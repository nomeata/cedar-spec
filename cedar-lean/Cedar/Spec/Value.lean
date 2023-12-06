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

import Cedar.Data
import Cedar.Spec.Ext

/-! This file defines Cedar values and results. -/

namespace Cedar.Spec

open Cedar.Data
open Cedar.Spec.Ext
open Except

----- Definitions -----

inductive Error where
  | entityDoesNotExist
  | attrDoesNotExist
  | typeError
  | arithBoundsError
  | extensionError

abbrev Result (α) := Except Error α

abbrev Id := String

structure Name where
  id : Id
  path : List Id

abbrev EntityType := Name

structure EntityUID where
  ty : EntityType
  eid : String

inductive Prim where
  | bool (b : Bool)
  | int (i : Int64)
  | string (s : String)
  | entityUID (uid : EntityUID)

abbrev Attr := String

inductive Value where
  | prim (p : Prim)
  | set (s : Set Value)
  | record (m : Map Attr Value)
  | ext (x : Ext)

----- Coercions -----

def Value.asEntityUID : Value → Result EntityUID
  | .prim (.entityUID uid) => ok uid
  | _ => error Error.typeError

def Value.asSet : Value → Result (Data.Set Value)
  | .set s => ok s
  | _ => error Error.typeError

def Value.asBool : Value → Result Bool
  | .prim (.bool b) => ok b
  | _ => error Error.typeError

def Value.asString : Value →  Result String
  | .prim (.string s) => ok s
  | _ => error Error.typeError

def Value.asInt : Value →  Result Int64
  | .prim (.int i) => ok i
  | _ => error Error.typeError

def Result.as {α} (β) [Coe α (Result β)] : Result α → Result β
  | ok v    => v
  | error e => error e

instance : Coe Bool Value where
  coe b := .prim (.bool b)

instance : Coe Int64 Value where
  coe i := .prim (.int i)

instance : Coe String Value where
  coe s := .prim (.string s)

instance : Coe EntityUID Value where
  coe e := .prim (.entityUID e)

instance : Coe Prim Value where
  coe p := .prim p

instance : Coe Ext Value where
  coe x := .ext x

instance : Coe (Data.Set Value) Value where
  coe s := .set s

instance : Coe (Map Attr Value) Value where
  coe r := .record r

instance : Coe Value (Result Bool) where
  coe v := v.asBool

instance : Coe Value (Result Int64) where
  coe v := v.asInt

instance : Coe Value (Result String) where
  coe v := v.asString

instance : Coe Value (Result EntityUID) where
  coe v := v.asEntityUID

instance : Coe Value (Result (Data.Set Value)) where
  coe v := v.asSet

----- Derivations -----

deriving instance Repr, DecidableEq, BEq for Except
deriving instance Repr, DecidableEq for Error
deriving instance Repr, DecidableEq, Inhabited for Name
deriving instance Repr, DecidableEq, Inhabited for EntityType
deriving instance Repr, DecidableEq, Inhabited for EntityUID
deriving instance Repr, DecidableEq, Inhabited for Prim
deriving instance Repr for Value

mutual

def decValue (a b : Value) : Decidable (a = b) := by
  cases a <;> cases b
  case prim.prim pa pb => exact match decEq pa pb with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case set.set sa sb => exact match decValueSet sa sb with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case record.record ra rb => exact match decValueRecord ra rb with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case ext.ext xa xb => exact match decEq xa xb with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  all_goals {
    apply isFalse
    intro h
    injection h
  }

def decValueList (as bs : List Value) : Decidable (as = bs) :=
  match as, bs with
  | [], [] => isTrue rfl
  | _::_, [] => isFalse (by intro; contradiction)
  | [], _::_ => isFalse (by intro; contradiction)
  | a::as, b::bs =>
    match decValue a b with
    | isTrue h₁ => match decValueList as bs with
      | isTrue h₂ => isTrue (by rw [h₁, h₂])
      | isFalse _ => isFalse (by intro h; injection h; contradiction)
    | isFalse _ => isFalse (by intro h; injection h; contradiction)

def decProdAttrValue (as bs : Attr × Value) : Decidable (as = bs) :=
  match as, bs with
  | (a1, a2), (b1, b2) => match decEq a1 b1 with
    | isTrue h₀ => match decValue a2 b2 with
      | isTrue h₁ => isTrue (by rw [h₀, h₁])
      | isFalse _ => isFalse (by intro h; injection h; contradiction)
    | isFalse _ => isFalse (by intro h; injection h; contradiction)

def decProdAttrValueList (as bs : List (Attr × Value)) : Decidable (as = bs) :=
  match as, bs with
  | [], [] => isTrue rfl
  | _::_, [] => isFalse (by intro; contradiction)
  | [], _::_ => isFalse (by intro; contradiction)
  | a::as, b::bs =>
    match decProdAttrValue a b with
    | isTrue h₁ => match decProdAttrValueList as bs with
      | isTrue h₂ => isTrue (by rw [h₁, h₂])
      | isFalse _ => isFalse (by intro h; injection h; contradiction)
    | isFalse _ => isFalse (by intro h; injection h; contradiction)

def decValueSet (a b : Set Value) : Decidable (a = b) := by
  match a, b with
  | .mk la, .mk lb => exact match decValueList la lb with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  done

def decValueRecord (as bs : Map Attr Value) : Decidable (as = bs) := by
  match as, bs with
  | .mk ma, .mk mb => exact match decProdAttrValueList ma mb with
  | isTrue h => isTrue (by rw [h])
  | isFalse _ => isFalse (by intro h; injection h; contradiction)
end

instance : DecidableEq Value :=
  decValue

def Name.lt (a b : Name) : Bool :=
  (a.id :: a.path) < (b.id :: b.path)

instance : LT Name where
  lt a b := Name.lt a b

instance Name.decLt (a b : Name) : Decidable (a < b) :=
  if h : Name.lt a b then isTrue h else isFalse h

instance listOfIdDecLt (as bs : List Id) : Decidable (List.lt as bs) := by
  apply List.hasDecidableLt

instance Name.strictLT : StrictLT Name where
  asymmetric a b   := by
    simp only [LT.lt, lt, decide_eq_true_eq]
    apply List.lt_asymm
  transitive a b c := by
    simp only [LT.lt, lt, decide_eq_true_eq]
    apply List.lt_trans
  connected  a b   := by
    simp only [LT.lt, lt, decide_eq_true_eq]
    intro h₁
    apply List.lt_conn
    by_contra h₂
    simp at h₂
    cases a; cases b
    simp at *
    simp [h₂] at h₁

def EntityUID.lt (a b : EntityUID) : Bool :=
  (a.ty < b.ty) ∨ (a.ty = b.ty ∧ a.eid < b.eid)

instance : LT EntityUID where
  lt a b := EntityUID.lt a b

instance EntityUID.decLt (a b : EntityUID) : Decidable (a < b) :=
  if h : EntityUID.lt a b then isTrue h else isFalse h

theorem EntityUID.lt_asymm {a b : EntityUID} :
  a < b → ¬ b < a
:= by
  cases a ; cases b ; rename_i ty₁ eid₁ ty₂ eid₂
  simp [LT.lt] ; rw [EntityUID.lt, EntityUID.lt]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  intro h₁
  by_contra h₂
  rcases (Name.strictLT.asymmetric ty₁ ty₂) with h₃
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> try simp [h₁, h₂] at h₃
  case inl.inr =>
    rcases h₂ with ⟨h₂, _⟩
    subst h₂
    contradiction
  case inr.inl =>
    rcases (StrictLT.not_eq ty₂ ty₁ h₂) with h₄
    simp [h₁] at h₄
  case inr.inr =>
    rcases (String.strictLT.asymmetric eid₁ eid₂) with h₄
    simp [h₁] at h₄
    simp [h₄] at h₂

theorem EntityUID.lt_trans {a b c : EntityUID} :
  a < b → b < c → a < c
:= by
  cases a ; cases b ; cases c ; rename_i ty₁ eid₁ ty₂ eid₂ ty₃ eid₃
  simp [LT.lt] ; rw [EntityUID.lt, EntityUID.lt, EntityUID.lt]
  simp only [decide_eq_true_eq]
  intro h₁ h₂
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  case inl.inl =>
    rcases (Name.strictLT.transitive ty₁ ty₂ ty₃ h₁ h₂) with h₃
    simp [h₃]
  case inl.inr =>
    rcases h₂ with ⟨h₂, _⟩ ; subst h₂
    simp [h₁]
  case inr.inl =>
    rcases h₁ with ⟨h₁, _⟩ ; subst h₁
    simp [h₂]
  case inr.inr =>
    rcases h₁ with ⟨hl₁, hr₁⟩
    rcases h₂ with ⟨hl₂, hr₂⟩
    subst hl₁ hl₂ ; simp only [true_and]
    rcases (String.strictLT.transitive eid₁ eid₂ eid₃ hr₁ hr₂) with h₃
    simp [h₃]

theorem EntityUID.lt_conn {a b : EntityUID} :
  a ≠ b → (a < b ∨ b < a)
:= by
  cases a ; cases b ; rename_i ty₁ eid₁ ty₂ eid₂
  simp [LT.lt]
  intro h₁
  simp [EntityUID.lt]
  by_cases (ty₁ = ty₂)
  case pos h₂ =>
    subst h₂ ; simp only [forall_const, true_and] at *
    simp [StrictLT.irreflexive ty₁]
    apply String.strictLT.connected
    simp [h₁]
  case neg h₂ =>
    rcases (Name.strictLT.connected ty₁ ty₂ h₂) with h₃
    rcases h₃ with h₃ | h₃ <;> simp [h₃]

instance EntityUID.strictLT : StrictLT EntityUID where
  asymmetric a b   := by exact EntityUID.lt_asymm
  transitive a b c := by exact EntityUID.lt_trans
  connected a b    := by exact EntityUID.lt_conn

def Bool.lt (a b : Bool) : Bool := match a,b with
| false, true => true
| _, _ => false

instance : LT Bool where
  lt a b := Bool.lt a b

instance Bool.decLt (a b : Bool) : Decidable (a < b) :=
  if h : Bool.lt a b then isTrue h else isFalse h

instance Bool.strictLT : StrictLT Bool where
  asymmetric a b   := by
    simp [LT.lt, Bool.lt]
    split <;> simp
  transitive a b c := by
    simp [LT.lt, Bool.lt]
    split <;> simp
  connected  a b   := by
    simp [LT.lt, Bool.lt]
    split <;> simp
    split <;> simp
    cases a <;> cases b <;> simp at *

def Prim.lt : Prim → Prim → Bool
  | .bool nb, .bool mb => nb < mb
  | .int ni, .int mi => ni < mi
  | .string ns, .string ms => ns < ms
  | .entityUID nuid, .entityUID muid => nuid < muid
  | .bool _, .int _ => true
  | .bool _, .string _ => true
  | .bool _, .entityUID _ => true
  | .int _, .string _ => true
  | .int _, .entityUID _ => true
  | .string _, .entityUID _ => true
  | _,_ => false

instance : LT Prim where
lt := fun x y => Prim.lt x y

instance Prim.decLt (a b : Prim) : Decidable (a < b) :=
if  h : Prim.lt a b then isTrue h else isFalse h

theorem Prim.lt_asymm {a b : Prim} :
  a < b → ¬ b < a
:= by
  cases a <;> cases b <;> simp [LT.lt] <;>
  simp only [Prim.lt, lt, decide_eq_true_eq, decide_eq_false_iff_not]
  case bool b₁ b₂ =>
    rcases (Bool.strictLT.asymmetric b₁ b₂) with h₂
    exact h₂
  case int i₁ i₂ =>
    rcases (Int64.strictLT.asymmetric i₁ i₂) with h₂
    exact h₂
  case string s₁ s₂ =>
    rcases (String.strictLT.asymmetric s₁ s₂) with h₂
    exact h₂
  case entityUID uid₁ uid₂ =>
    rcases (EntityUID.strictLT.asymmetric uid₁ uid₂) with h₂
    exact h₂

theorem Prim.lt_trans {a b c : Prim} :
  a < b → b < c → a < c
:= by
  cases a <;> cases b <;> cases c <;> simp [LT.lt] <;>
  simp only [Prim.lt, decide_eq_true_eq, imp_self, implies_true, false_implies]
  case bool b₁ b₂ b₃ =>
    rcases (Bool.strictLT.transitive b₁ b₂ b₃) with h₂
    exact h₂
  case int i₁ i₂ i₃ =>
    rcases (Int64.strictLT.transitive i₁ i₂ i₃) with h₂
    exact h₂
  case string s₁ s₂ s₃ =>
    rcases (String.strictLT.transitive s₁ s₂ s₃) with h₂
    exact h₂
  case entityUID uid₁ uid₂ uid₃ =>
    rcases (EntityUID.strictLT.transitive uid₁ uid₂ uid₃) with h₂
    exact h₂

theorem Prim.lt_conn {a b : Prim} :
  a ≠ b → (a < b ∨ b < a)
:= by
  cases a <;> cases b <;> simp [LT.lt] <;>
  simp only [Prim.lt, lt, decide_eq_true_eq, decide_eq_false_iff_not]
  case bool b₁ b₂ =>
    rcases (Bool.strictLT.connected b₁ b₂) with h₂
    exact h₂
  case int i₁ i₂ =>
    rcases (Int64.strictLT.connected i₁ i₂) with h₂
    exact h₂
  case string s₁ s₂ =>
    rcases (String.strictLT.connected s₁ s₂) with h₂
    exact h₂
  case entityUID uid₁ uid₂ =>
    rcases (EntityUID.strictLT.connected uid₁ uid₂) with h₂
    exact h₂

instance Prim.strictLT : StrictLT Prim where
  asymmetric a b   := by exact Prim.lt_asymm
  transitive a b c := by exact Prim.lt_trans
  connected  a b   := by exact Prim.lt_conn

mutual
def Value.lt : Value → Value → Bool
  | .prim x, .prim y => x < y
  | .set (.mk lx), .set (.mk ly) => Values.lt lx ly lx.length
  | .record (.mk lx), .record (.mk ly) => ValueAttrs.lt lx ly lx.length
  | .ext x, .ext y => x < y
  | .prim _, .set _ => true
  | .prim _, .record _ => true
  | .prim _, .ext _ => true
  | .set _, .record _ => true
  | .set _, .ext _ => true
  | .set _, .prim _ => false
  | .record _, .ext _ => true
  | .record _, .prim _ => false
  | .record _, .set _ => false
  | .ext _, .prim _ => false
  | .ext _, .set _ => false
  | .ext _, .record _ => false

def Values.lt (n m : List Value) (i : Nat): Bool :=
  match n, m with
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | n::ns, m::ms => Value.lt n m || (n = m && Values.lt ns ms (i-1))

def ValueAttrs.lt (n m : List (Attr × Value)) (i : Nat) : Bool :=
  match n, m with
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | (na, nv)::ns, (ma, mv)::ms =>
    na < ma || (na = ma && Value.lt nv mv) ||
    (na = ma && nv = mv && ValueAttrs.lt ns ms (i-1))
end
termination_by
Value.lt as₁ as₂ => (sizeOf as₁, 0)
Values.lt as₁ as₂ i => (sizeOf as₁, as₁.length - i)
ValueAttrs.lt as₁ as₂ i => (sizeOf as₁, as₁.length - i)

instance : LT Value where
  lt := fun x y => Value.lt x y

instance Value.decLt (n m : Value) : Decidable (n < m) :=
if h : Value.lt n m then isTrue h else isFalse h

mutual
theorem Value.lt_irrefl (v : Value) :
  ¬ Value.lt v v
:= by
  cases v <;> simp [Value.lt] <;> rename_i w
  case prim => exact StrictLT.irreflexive w
  case set =>
    cases w ; rename_i ws ; simp [Value.lt]
    rcases (Values.lt_irrefl ws) with h₁
    simp [h₁]
  case record =>
    cases w ; rename_i ws ; simp [Value.lt]
    rcases (ValueAttrs.lt_irrefl ws) with h₁
    simp [h₁]
  case ext => exact StrictLT.irreflexive w

theorem Values.lt_irrefl (vs : List Value) :
  ¬ Values.lt vs vs vs.length
:= by
  cases vs ; simp [Values.lt] ; rename_i hd tl ; simp [Values.lt]
  by_contra h₁
  rcases h₁ with h₁ | h₁
  case inl =>
    rcases (Value.lt_irrefl hd) with h₂
    simp [h₁] at h₂
  case inr =>
    rcases (Values.lt_irrefl tl) with h₂
    simp [h₁] at h₂

theorem ValueAttrs.lt_irrefl (vs : List (Attr × Value)) :
  ¬ ValueAttrs.lt vs vs vs.length
:= by
  cases vs ; simp [ValueAttrs.lt] ; rename_i hd tl
  cases hd ; rename_i a v ; simp [ValueAttrs.lt]
  by_contra h₁
  rcases h₁ with h₁ | h₁
  case inl =>
    rcases h₁ with h₁ | h₁
    case inl =>
      rcases (StrictLT.irreflexive a) with h₂
      contradiction
    case inr =>
      rcases (Value.lt_irrefl v) with h₂
      contradiction
  case inr =>
    rcases (ValueAttrs.lt_irrefl tl) with h₂
    contradiction

end

theorem Value.lt_not_eq {x y : Value} :
  x < y → ¬ x = y
:= by
  intro h₁
  by_contra h₂
  subst h₂
  rcases (Value.lt_irrefl x) with h₃
  contradiction

mutual
theorem Value.lt_asymm {a b : Value} :
  a < b → ¬ b < a
:= by
  cases a <;> cases b <;> simp [LT.lt] <;> try simp [Value.lt]
  case prim p₁ p₂ => apply Prim.strictLT.asymmetric p₁ p₂
  case set s₁ s₂ =>
    cases s₁ ; cases s₂ ; rename_i vs₁ vs₂
    simp [Value.lt]
    intro h₁
    rcases (Values.lt_asym h₁) with h₂
    simp [h₂]
  case record r₁ r₂ =>
    cases r₁ ; cases r₂ ; rename_i avs₁ avs₂
    simp [Value.lt]
    intro h₁
    rcases (ValueAttrs.lt_asym h₁) with h₂
    simp [h₂]
  case ext x₁ x₂ => apply Ext.strictLT.asymmetric x₁ x₂

theorem Values.lt_asym {vs₁ vs₂: List Value} :
  Values.lt vs₁ vs₂ vs₁.length → ¬ Values.lt vs₂ vs₁ vs₂.length
:= by
  cases vs₁ <;> cases vs₂ <;> simp [Values.lt]
  rename_i hd₁ tl₁ hd₂ tl₂
  intro h₁ ; rcases h₁ with h₁ | h₁
  case inl =>
    rcases (Value.lt_asymm h₁) with h₂
    simp [LT.lt] at h₂
    simp [h₂] ; intro h₃ ; subst h₃
    simp [h₁] at h₂
  case inr =>
    rcases h₁ with ⟨hl₁, h₁⟩
    subst hl₁ ; simp only [true_and]
    rcases (Values.lt_asym h₁) with h₂
    simp [h₂, Value.lt_irrefl hd₁]

theorem ValueAttrs.lt_asym {vs₁ vs₂: List (Attr × Value)} :
  ValueAttrs.lt vs₁ vs₂ vs₁.length → ¬ ValueAttrs.lt vs₂ vs₁ vs₂.length
:= by
  cases vs₁ <;> cases vs₂ <;> simp [ValueAttrs.lt]
  rename_i hd₁ tl₁ hd₂ tl₂
  cases hd₁ ; cases hd₂ ; simp [ValueAttrs.lt]
  rename_i a₁ v₁ a₂ v₂
  intro h₁ ; rcases h₁ with h₁ | h₁
  case inl =>
    rcases h₁ with h₁ | h₁
    case inl =>
      rcases (String.strictLT.asymmetric a₁ a₂ h₁) with h₂
      rcases (StrictLT.not_eq a₁ a₂ h₁) with h₃
      rw [eq_comm] at h₃
      simp [h₂, h₃]
    case inr =>
      rcases h₁ with ⟨hl₁, h₁⟩ ; subst hl₁
      simp only [decide_True, Bool.true_and]
      rcases (Value.lt_asymm h₁) with h₂
      simp [LT.lt] at h₂ ; simp [h₂]
      rcases (StrictLT.irreflexive a₁) with h₃
      rcases (Value.lt_not_eq h₁) with h₄
      rw [eq_comm] at h₄
      simp [h₃, h₄]
  case inr =>
    rcases h₁ with ⟨h₂, h₁⟩
    rcases h₂ with ⟨hl₂, hr₂⟩ ; subst hl₂ hr₂
    simp only [decide_True, Bool.true_and, Bool.and_self]
    rcases (ValueAttrs.lt_asym h₁) with h₂
    rcases (StrictLT.irreflexive a₁) with h₃
    rcases (Value.lt_irrefl v₁) with h₄
    simp [h₂, h₃, h₄]

end

mutual
theorem Value.lt_trans {a b c : Value} :
  a < b → b < c → a < c
:= by
  cases a <;> cases b <;> cases c <;> simp [LT.lt] <;> try simp [Value.lt]
  case prim p₁ p₂ p₃ => apply Prim.strictLT.transitive p₁ p₂ p₃
  case set s₁ s₂ s₃ =>
    cases s₁ ; cases s₂ ; cases s₃ ; rename_i vs₁ vs₂ vs₃
    simp [Value.lt]
    intro h₁ h₂
    apply Values.lt_trans h₁ h₂
  case record r₁ r₂ r₃ =>
    cases r₁ ; cases r₂ ; cases r₃ ; rename_i vs₁ vs₂ vs₃
    simp [Value.lt]
    intro h₁ h₂
    apply ValueAttrs.lt_trans h₁ h₂
  case ext x₁ x₂ x₃ => apply Ext.strictLT.transitive x₁ x₂ x₃


theorem Values.lt_trans {vs₁ vs₂ vs₃: List Value}
  (h₁ : Values.lt vs₁ vs₂ vs₁.length)
  (h₂ : Values.lt vs₂ vs₃ vs₂.length ) :
  Values.lt vs₁ vs₃ vs₁.length
:= by
  cases vs₁ <;> cases vs₂ <;> cases vs₃ <;> simp [Values.lt] at *
  rename_i hd₁ tl₁ hd₂ tl₂ hd₃ tl₃
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  case inl.inl =>
    rcases (Value.lt_trans h₁ h₂) with h₃
    simp [LT.lt] at h₃ ; simp [h₃]
  case inl.inr =>
    rcases h₂ with ⟨h₂, _⟩ ; subst h₂ ; simp [h₁]
  case inr.inl =>
    rcases h₁ with ⟨h₁, _⟩ ; subst h₁ ; simp [h₂]
  case inr.inr =>
    rcases h₁ with ⟨hl₁, h₁⟩ ; subst hl₁
    rcases h₂ with ⟨hl₂, h₂⟩ ; subst hl₂
    rcases (Values.lt_trans h₁ h₂) with h₃
    simp [h₃]

theorem ValueAttrs.lt_trans {vs₁ vs₂ vs₃: List (Attr × Value)}
  (h₁ : ValueAttrs.lt vs₁ vs₂ vs₁.length)
  (h₂ : ValueAttrs.lt vs₂ vs₃ vs₂.length) :
  ValueAttrs.lt vs₁ vs₃ vs₁.length
:= by
  cases vs₁ <;> cases vs₂ <;> cases vs₃ <;> simp [ValueAttrs.lt] at *
  rename_i hd₁ tl₁ hd₂ tl₂ hd₃ tl₃
  cases hd₁ ; cases hd₂ ; cases hd₃ ; simp [ValueAttrs.lt] at *
  rename_i a₁ v₁ a₂ v₂ a₃ v₃
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  case inl.inl =>
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    case inl.inl =>
      rcases (String.strictLT.transitive a₁ a₂ a₃ h₁ h₂) with h₃
      simp [h₃]
    case inl.inr =>
      rcases h₂ with ⟨h₂, _⟩ ; subst h₂ ; simp [h₁]
    case inr.inl =>
      rcases h₁ with ⟨h₁, _⟩ ; subst h₁ ; simp [h₂]
    case inr.inr =>
      rcases h₁ with ⟨hl₁, h₁⟩ ; subst hl₁
      rcases h₂ with ⟨hl₂, h₂⟩ ; subst hl₂
      rcases (Value.lt_trans h₁ h₂) with h₃
      simp [LT.lt] at h₃ ; simp [h₃]
  case inl.inr =>
    rcases h₂ with ⟨h₂, _⟩
    rcases h₂ with ⟨hl₂, hr₂⟩ ; subst hl₂ hr₂
    simp [h₁]
  case inr.inl =>
    rcases h₁ with ⟨h₁, _⟩
    rcases h₁ with ⟨hl₁, hr₁⟩ ; subst hl₁ hr₁
    simp [h₂]
  case inr.inr =>
    rcases h₁ with ⟨h₁, h₃⟩
    rcases h₁ with ⟨hl₁, hr₁⟩ ; subst hl₁ hr₁
    rcases h₂ with ⟨h₂, h₄⟩
    rcases h₂ with ⟨hl₂, hr₂⟩ ; subst hl₂ hr₂
    rcases (ValueAttrs.lt_trans h₃ h₄) with h₅
    simp [h₅]
end

mutual
theorem Value.lt_conn {a b : Value} :
  a ≠ b → (a < b ∨ b < a)
:= by
  cases a <;> cases b <;> simp [LT.lt] <;> try simp [Value.lt]
  case prim p₁ p₂ => apply Prim.strictLT.connected p₁ p₂
  case set s₁ s₂ =>
    cases s₁ ; cases s₂ ; rename_i vs₁ vs₂
    simp [Value.lt]
    intro h₁
    apply Values.lt_conn h₁
  case record r₁ r₂ =>
    cases r₁ ; cases r₂ ; rename_i vs₁ vs₂
    simp [Value.lt]
    intro h₁
    apply ValueAttrs.lt_conn h₁
  case ext x₁ x₂ => apply Ext.strictLT.connected x₁ x₂


theorem Values.lt_conn {vs₁ vs₂ : List Value}
  (h₁ : ¬vs₁ = vs₂) :
  Values.lt vs₁ vs₂ vs₁.length ∨ Values.lt vs₂ vs₁ vs₂.length
:= by
  cases vs₁ <;> cases vs₂ <;> simp [Values.lt] <;> try contradiction
  rename_i hd₁ tl₁ hd₂ tl₂
  simp only [List.cons.injEq, not_and] at h₁
  by_cases h₂ : (hd₁ = hd₂)
  case pos =>
    simp [h₂] at *
    rcases (Values.lt_conn h₁) with h₃
    rcases h₃ with h₃ | h₃ <;> simp [h₃]
  case neg =>
    rcases (Value.lt_conn h₂) with h₃
    simp [LT.lt] at h₃
    rcases h₃ with h₃ | h₃ <;> simp [h₃]

theorem ValueAttrs.lt_conn {vs₁ vs₂ : List (Attr × Value)}
  (h₁ : ¬vs₁ = vs₂) :
  ValueAttrs.lt vs₁ vs₂ vs₁.length ∨ ValueAttrs.lt vs₂ vs₁ vs₂.length
:= by
  cases vs₁ <;> cases vs₂ <;> simp [ValueAttrs.lt] <;> try contradiction
  rename_i hd₁ tl₁ hd₂ tl₂
  cases hd₁ ; cases hd₂ ; simp [ValueAttrs.lt]
  rename_i a₁ v₁ a₂ v₂
  simp only [List.cons.injEq, Prod.mk.injEq, not_and, and_imp] at h₁
  by_cases h₂ : (a₁ = a₂)
  case pos =>
    subst h₂ ; simp only [forall_const, true_and] at *
    by_cases h₃ : (v₁ = v₂)
    case pos =>
      subst h₃ ; simp only [forall_const, true_and] at *
      rcases (ValueAttrs.lt_conn h₁) with h₂
      rcases h₂ with h₂ | h₂ <;> simp [h₂]
    case neg =>
      rcases (Value.lt_conn h₃) with h₄
      simp [LT.lt] at h₄
      rcases h₄ with h₄ | h₄ <;> simp [h₄]
  case neg =>
    rcases (String.strictLT.connected a₁ a₂) with h₃
    simp [h₂] at h₃
    rcases h₃ with h₃ | h₃ <;> simp [h₃]

end

instance Value.strictLT : StrictLT Value where
  asymmetric a b   := by exact Value.lt_asymm
  transitive a b c := by exact Value.lt_trans
  connected  a b   := by exact Value.lt_conn


deriving instance Inhabited for Value

end Cedar.Spec
