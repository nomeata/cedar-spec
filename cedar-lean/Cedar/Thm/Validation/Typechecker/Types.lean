/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.Util.Std

/-!
This file contains useful definitions and lemmas about Cedar types.

todo: fill in `sorry`s.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

----- Definitions -----

def InstanceOfBoolType : Bool → BoolType → Prop
  | true,  .tt      => True
  | false, .ff      => True
  | _,     .anyBool => True
  | _, _            => False

def InstanceOfEntityType (e : EntityUID) (ety: EntityType) : Prop :=
  ety = e.ty

def InstanceOfExtType : Ext → ExtType → Prop
  | .decimal _, .decimal => True
  | .ipaddr _,  .ipAddr  => True
  | _, _                 => False

inductive InstanceOfType : Value → CedarType → Prop :=
  | instance_of_bool (b : Bool) (bty : BoolType)
      (h₁ : InstanceOfBoolType b bty) :
      InstanceOfType (.prim (.bool b)) (.bool bty)
  | instance_of_int :
      InstanceOfType (.prim (.int _)) .int
  | instance_of_string :
      InstanceOfType (.prim (.string _)) .string
  | instance_of_entity (e : EntityUID) (ety: EntityType)
      (h₁ : InstanceOfEntityType e ety) :
      InstanceOfType (.prim (.entityUID e)) (.entity ety)
  | instance_of_set (s : Set Value) (ty : CedarType)
      (h₁ : forall v, v ∈ s → InstanceOfType v ty) :
      InstanceOfType (.set s) (.set ty)
  | instance_of_record (r : Map Attr Value) (rty : RecordType)
      -- if an attribute is present in the record, then it is present in the type
      (h₁ : ∀ (k : Attr), r.contains k → rty.contains k)
      -- if an attribute is present, then it has the expected type
      (h₂ : ∀ (k : Attr) (v : Value) (qty : QualifiedType),
        r.find? k = some v → rty.find? k = some qty → InstanceOfType v qty.getType)
      -- required attributes are present
      (h₃ : ∀ (k : Attr) (qty : QualifiedType), rty.find? k = some qty → qty.isRequired → r.contains k) :
      InstanceOfType (.record r) (.record rty)
  | instance_of_ext (x : Ext) (xty : ExtType)
      (h₁ : InstanceOfExtType x xty) :
      InstanceOfType (.ext x) (.ext xty)

def InstanceOfRequestType (request : Request) (reqty : RequestType) : Prop :=
  InstanceOfEntityType request.principal reqty.principal ∧
  request.action = reqty.action ∧
  InstanceOfEntityType request.resource reqty.resource ∧
  InstanceOfType request.context (.record reqty.context)

/--
For every entity in the store,
1. The entity's type is defined in the type store.
2. The entity's attributes match the attribute types indicated in the type store.
3. The entity's ancestors' types are consistent with the ancestor information
   in the type store.
-/
def InstanceOfEntityTypeStore (entities : Entities) (ets: EntityTypeStore) : Prop :=
  ∀ uid data, entities.find? uid = some data →
    ∃ attrTys ancestorTys, ets.find? uid.ty = some (attrTys, ancestorTys) ∧
      InstanceOfType data.attrs (.record attrTys) ∧
      ∀ ancestor, ancestor ∈ data.ancestors → ancestor.ty ∈ ancestorTys

/--
For every action in the entity store, the action's ancestors are consistent
with the ancestor information in the action store.
-/
def InstanceOfActionStore (entities : Entities) (as: ActionStore) : Prop :=
  ∀ uid data, entities.find? uid = some data → as.contains uid →
    ∃ ancestors, as.find? uid = some ancestors →
      ∀ ancestor, ancestor ∈ data.ancestors → ancestor ∈ ancestors

def RequestAndEntitiesMatchEnvironment (env : Environment) (request : Request) (entities : Entities) : Prop :=
  InstanceOfRequestType request env.reqty ∧
  InstanceOfEntityTypeStore entities env.ets ∧
  InstanceOfActionStore entities env.acts

----- Theorems -----

theorem false_is_instance_of_ff :
  InstanceOfType (Value.prim (Prim.bool false)) (CedarType.bool BoolType.ff)
:= by
  apply InstanceOfType.instance_of_bool
  simp [InstanceOfBoolType]

theorem true_is_instance_of_tt :
  InstanceOfType (Value.prim (Prim.bool true)) (CedarType.bool BoolType.tt)
:= by
  apply InstanceOfType.instance_of_bool
  simp [InstanceOfBoolType]

theorem bool_is_instance_of_anyBool (b : Bool) :
  InstanceOfType (Value.prim (Prim.bool b)) (CedarType.bool BoolType.anyBool)
:= by
  apply InstanceOfType.instance_of_bool
  simp [InstanceOfBoolType]

theorem instance_of_bool_is_bool {v₁ : Value} {bty : BoolType} :
  InstanceOfType v₁ (CedarType.bool bty) →
  ∃ b, v₁ = .prim (.bool b)
:= by
  intro h₁
  rcases h₁ with ⟨b, _, _⟩
  exists b

theorem instance_of_ff_is_false {v₁ : Value} :
  InstanceOfType v₁ (CedarType.bool BoolType.ff) →
  v₁ = .prim (.bool false)
:= by
  intro h₁
  cases h₁ with
  | instance_of_bool b _ h₁ =>
    simp [InstanceOfBoolType] at h₁
    cases b <;> simp at h₁
    rfl

theorem instance_of_tt_is_true {v₁ : Value} :
  InstanceOfType v₁ (CedarType.bool BoolType.tt) →
  v₁ = .prim (.bool true)
:= by
  intro h₁
  cases h₁ with
  | instance_of_bool b _ h₁ =>
    simp [InstanceOfBoolType] at h₁
    cases b <;> simp at h₁
    rfl

theorem instance_of_anyBool_is_bool {v₁ : Value} :
  InstanceOfType v₁ (CedarType.bool BoolType.anyBool) →
  ∃ b, v₁ = .prim (.bool b)
:= by exact instance_of_bool_is_bool

theorem instance_of_lubBool {v : Value} {bty₁ bty₂ : BoolType} :
  (InstanceOfType v (CedarType.bool bty₁) ∨ InstanceOfType v (CedarType.bool bty₂)) →
  InstanceOfType v (CedarType.bool (lubBool bty₁ bty₂))
:= by
  intro h₁ ; cases h₁ <;> simp [lubBool] <;> split <;>
  try { assumption } <;>
  rename_i h₂ h₃ <;>
  rcases (instance_of_bool_is_bool h₂) with ⟨b, h₂⟩ <;>
  subst h₂ <;>
  try { try exact bool_is_instance_of_anyBool b }
  subst h₃ ; exact h₂

theorem instance_of_lub {v : Value} {ty ty₁ ty₂ : CedarType}
  (h₁ : (ty₁ ⊔ ty₂) = .some ty)
  (h₂ : InstanceOfType v ty₁ ∨ InstanceOfType v ty₂) :
  InstanceOfType v ty
:= by
  unfold lub? at h₁
  -- Generalizing here is a hack to let us retain hypthoses of the form ty₁ =
  -- CedarType.set s₁ after the split.  We need these for the termination proof.
  generalize hty₁ : ty₁ = vty₁
  generalize hty₂ : ty₂ = vty₂
  simp [hty₁, hty₂] at h₂
  split at h₁
  case h_1 =>
    simp at h₁ ; subst h₁ hty₁ hty₂
    exact instance_of_lubBool h₂
  case h_2 _ _ sty₁ sty₂ =>
    cases h₃ : sty₁ ⊔ sty₂ <;> simp [h₃] at h₁
    rename_i sty
    subst h₁ ; simp [←hty₁, ←hty₂] at h₂
    cases h₂ <;> rename_i h₄
    all_goals {
      cases h₄ ; rename_i s h₄
      apply InstanceOfType.instance_of_set
      intro w h₅
      specialize h₄ w h₅
      apply instance_of_lub h₃ (by simp [h₄])
    }
  case h_3 =>
    -- TODO: record case. Needs mutual recursion with proof for lubRecordType,
    -- and likely hairy termination lemmas. Alternatively, we could rewrite
    -- lub? to avoid mutual recursion (using the same trick as for `evaluate`).
    -- That may make this proof easier.
    sorry
  case h_4 =>
    split at h₁ <;> simp at h₁
    rename_i h₃
    subst h₁ h₃ hty₁ hty₂
    simp at h₂
    exact h₂
termination_by instance_of_lub _ _ ty₁ ty₂ _ _ => (sizeOf ty₁, sizeOf ty₂)

theorem instance_of_int_is_int {v₁ : Value} :
  InstanceOfType v₁ CedarType.int →
  ∃ i, v₁ = .prim (.int i)
:= by
  intro h₁
  cases h₁
  rename_i y
  exists y

theorem instance_of_string_is_string {v₁ : Value} :
  InstanceOfType v₁ CedarType.string →
  ∃ s, v₁ = .prim (.string s)
:= by
  intro h₁
  cases h₁
  rename_i y
  exists y

theorem instance_of_entity_type_is_entity {ety : EntityType} :
  InstanceOfType v₁ (.entity ety) →
  ∃ euid, euid.ty = ety ∧ v₁ = .prim (.entityUID euid)
:= by
  intro h₁
  cases h₁
  rename_i euid h₁
  simp [InstanceOfEntityType] at h₁
  exists euid
  simp [h₁]

theorem instance_of_record_type_is_record {rty : RecordType} :
  InstanceOfType v₁ (.record rty) →
  ∃ r, v₁ = .record r
:= by
  intro h₁
  cases h₁
  rename_i r _ _ _
  exists r

theorem instance_of_attribute_type {r : Map Attr Value} {v : Value} {rty : RecordType} {a : Attr} {aty : CedarType} {qaty : QualifiedType}
  (h₁ : InstanceOfType (.record r) (.record rty))
  (h₂ : rty.find? a = .some qaty)
  (h₃ : qaty.getType = aty)
  (h₄ : r.find? a = .some v) :
  InstanceOfType v aty
:= by
  cases h₁
  rename_i _ h₅ _
  rw [←h₃]
  apply h₅ a v qaty h₄ h₂

theorem absent_attribute_is_absent {r : Map Attr Value} {rty : RecordType} {a : Attr}
  (h₁ : InstanceOfType (.record r) (.record rty))
  (h₂ : rty.find? a = .none) :
  r.find? a = .none
:= by
  cases h₁
  case instance_of_record h₃ _ _ =>
    by_contra h₄
    simp [Option.ne_none_iff_exists', ←Map.contains_iff_some_find?] at h₄
    specialize h₃ a h₄
    simp [Map.contains_iff_some_find?, h₂] at h₃

theorem required_attribute_is_present {r : Map Attr Value} {rty : RecordType} {a : Attr} {aty : CedarType}
  (h₁ : InstanceOfType (.record r) (.record rty))
  (h₂ : rty.find? a = .some (Qualified.required aty)) :
  ∃ v, r.find? a = .some v
:= by
  cases h₁
  rename_i h₃
  rw [←Map.contains_iff_some_find?]
  apply h₃ _ _ h₂
  simp [Qualified.isRequired]

theorem well_typed_entity_attributes {env : Environment} {request : Request} {entities : Entities} {uid: EntityUID} {d: EntityData} {rty : RecordType}
  (h₁ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₂ : Map.find? entities uid = some d)
  (h₃ : EntityTypeStore.attrs? env.ets uid.ty = some rty) :
  InstanceOfType d.attrs (.record rty)
:= by
  rcases h₁ with ⟨_, h₁, _⟩
  simp [InstanceOfEntityTypeStore] at h₁
  specialize h₁ uid d h₂
  rcases h₁ with ⟨rty', _, h₁₂, h₁, _⟩
  unfold EntityTypeStore.attrs? at h₃
  simp [h₁₂] at h₃
  subst h₃
  exact h₁

theorem instance_of_type_bool_is_bool (v : Value) (ty : CedarType) :
  InstanceOfType v ty →
  ty ⊑ .bool .anyBool →
  ∃ b, v = .prim (.bool b)
:= by
  intro h₀ h₁
  cases v <;> cases ty <;> try cases h₀ <;>
  try simp [subty, lub?] at h₁
  case instance_of_bool b bty =>
    exists b

theorem bool_type_is_inhabited (bty : BoolType) :
  ∃ b, InstanceOfBoolType b bty
:= by
  simp [InstanceOfBoolType]
  cases bty
  case tt => exists true
  all_goals { exists false }

theorem entity_type_is_inhabited (ety : EntityType) :
  ∃ euid, InstanceOfEntityType euid ety
:= by
  simp [InstanceOfEntityType]
  exists (EntityUID.mk ety default)

theorem ext_type_is_inhabited (xty : ExtType) :
  ∃ x, InstanceOfExtType x xty
:= by
  simp [InstanceOfExtType]
  cases xty
  case ipAddr  => exists (Ext.ipaddr (default : IPAddr))
  case decimal => exists (Ext.decimal (default : Ext.Decimal))


mutual
theorem type_is_inhabited (ty : CedarType) :
  ∃ v, InstanceOfType v ty
:= by
  match ty with
  | .bool bty =>
    rcases (bool_type_is_inhabited bty) with ⟨b, h₁⟩
    exists (.prim (.bool b))
    apply InstanceOfType.instance_of_bool _ _ h₁
  | .int =>
    exists (.prim (.int default))
    apply InstanceOfType.instance_of_int
  | .string =>
    exists (.prim (.string default))
    apply InstanceOfType.instance_of_string
  | .entity ety =>
    rcases (entity_type_is_inhabited ety) with ⟨euid, h₁⟩
    exists (.prim (.entityUID euid))
    apply InstanceOfType.instance_of_entity _ _ h₁
  | .set ty₁ =>
    exists (.set Set.empty)
    apply InstanceOfType.instance_of_set
    intro v₁ h₁
    rcases (Set.in_set_means_list_non_empty v₁ Set.empty h₁) with h₂
    simp [Set.empty] at h₂
  | .ext xty =>
    rcases (ext_type_is_inhabited xty) with ⟨x, h₁⟩
    exists (.ext x)
    apply InstanceOfType.instance_of_ext _ _ h₁
  | .record rty =>
    rcases (record_type_is_inhabited rty) with ⟨r, h₁, h₂, h₃⟩
    exists (.record r)
    apply InstanceOfType.instance_of_record _ _ h₁ h₂ h₃

theorem record_type_is_inhabited (rty : RecordType) :
  ∃ (r : Map Attr Value),
    (∀ (k : Attr), r.contains k → rty.contains k) ∧
    (∀ (k : Attr) (v : Value) (qty : QualifiedType),
      r.find? k = some v → rty.find? k = some qty → InstanceOfType v qty.getType) ∧
    (∀ (k : Attr) (qty : QualifiedType), rty.find? k = some qty → qty.isRequired → r.contains k)
:= by sorry

end

end Cedar.Thm
