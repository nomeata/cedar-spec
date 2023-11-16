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
import Cedar.Thm.Lemmas.Std
import Cedar.Thm.Lemmas.Types
import Cedar.Thm.Lemmas.TypecheckerInversion
import Cedar.Validation

/-!
This file contains useful definitions and lemmas about the `Typechecker` functions.

todo: fill in `sorry`s. Some invariants may need to be adjusted. The current
definitions are an informed guess based on the corresponding Dafny proof.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
The type soundness property says that if the typechecker assigns a type to an
expression, then it must be the case that the expression `EvaluatesTo` a value
of that type. The `EvaluatesTo` predicate covers the (obvious) case where
evaluation has no errors, but it also allows for errors of type
`entityDoesNotExist`, `extensionError`, and `arithBoundsError`.

The typechecker cannot protect against these errors because they depend on
runtime information (i.e., the entities passed into the authorization request,
extension function applications on authorization-time data, and arithmetic
overflow errors). All other errors (`attrDoesNotExist` and `typeError`) can be
prevented statically.

_Note_: Currently, `extensionError`s can also be ruled out at validation time
because the only extension functions that can error are constructors, and all
constructors are required to be applied to string literals, meaning that they
can be fully evaluated during validation. This is not guaranteed to be the case
in the future.

_Note_: We plan to implement a range analysis that will be able to rule out
`arithBoundsError`s.
-/
def EvaluatesTo (e: Expr) (request : Request) (entities : Entities) (v : Value) : Prop :=
  evaluate e request entities = .error .entityDoesNotExist ∨
  evaluate e request entities = .error .extensionError ∨
  evaluate e request entities = .error .arithBoundsError ∨
  evaluate e request entities = .ok v

/--
On input to the typechecking function, for any (e,k) in the Capabilities,
e is a record- or entity-typed expression that has key k.
-/
def CapabilitiesInvariant (c : Capabilities) (request : Request) (entities : Entities) : Prop :=
  ∀ (e : Expr) (k : Attr), (e, k) ∈ c → EvaluatesTo (.hasAttr e k) request entities true

/--
The Capabilities output by the typechecking function will satisfy
`CapabilitiesInvariant` provided that the input expression evaluates to true.
-/
def GuardedCapabilitiesInvariant (e: Expr) (c: Capabilities) (request : Request) (entities : Entities) : Prop :=
  evaluate e request entities = .ok true →
  CapabilitiesInvariant c request entities

----- Capability lemmas -----

theorem empty_capabilities_invariant (request : Request) (entities : Entities) :
  CapabilitiesInvariant ∅ request entities
:= by
  intro e k h
  contradiction

theorem empty_guarded_capabilities_invariant {e: Expr} {request : Request} {entities : Entities} :
  GuardedCapabilitiesInvariant e ∅ request entities
:= by
  intro _
  exact empty_capabilities_invariant request entities

theorem capability_implies_record_attribute {x₁ : Expr} {a : Attr} {c₁ : Capabilities} {request : Request} {entities : Entities} {r : Map Attr Value}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : evaluate x₁ request entities = Except.ok (Value.record r))
  (h₃ : (x₁, a) ∈ c₁) :
  ∃ vₐ, r.find? a = some vₐ
:= by
  simp [CapabilitiesInvariant] at h₁
  specialize h₁ x₁ a h₃
  simp [EvaluatesTo, evaluate, h₂, hasAttr, attrsOf, Map.contains_iff_some_find?] at h₁
  exact h₁

theorem capability_implies_entity_attribute {x₁ : Expr} {a : Attr} {c₁ : Capabilities} {request : Request} {entities : Entities} {uid: EntityUID} {d: EntityData}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : evaluate x₁ request entities = Except.ok (Value.prim (Prim.entityUID uid)))
  (h₃ : Map.find? entities uid = some d)
  (h₄ : (x₁, a) ∈ c₁) :
  ∃ vₐ, d.attrs.find? a = some vₐ
:= by
  simp [CapabilitiesInvariant] at h₁
  specialize h₁ x₁ a h₄
  simp [EvaluatesTo, evaluate, h₂, hasAttr, attrsOf, Entities.attrsOrEmpty, h₃, Map.contains_iff_some_find?] at h₁
  exact h₁

theorem capability_union_invariant {c₁ c₂ : Capabilities} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : CapabilitiesInvariant c₂ request entities) :
  CapabilitiesInvariant (c₁ ∪ c₂) request entities
:= by
  simp [CapabilitiesInvariant] at *
  intro x a h₃
  specialize h₁ x a ; specialize h₂ x a
  cases h₃ <;> rename_i h₃ <;> simp [h₃] at * <;> assumption

theorem capability_intersection_invariant {c₁ c₂ : Capabilities} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities ∨ CapabilitiesInvariant c₂ request entities) :
  CapabilitiesInvariant (c₁ ∩ c₂) request entities
:= by
  simp [CapabilitiesInvariant] at *
  intro x a h₃ h₄
  cases h₁ <;> rename_i h₁ <;> apply h₁ x a <;> assumption

----- Lemmas showing that typechecking of individual expressions is sound -----

theorem type_of_lit_is_sound {l : Prim} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₃ : typeOf (Expr.lit l) c₁ env = Except.ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (Expr.lit l) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.lit l) request entities v ∧ InstanceOfType v ty
:= by
  simp [EvaluatesTo, evaluate]
  simp [typeOf, typeOfLit] at h₃
  split at h₃ <;> simp [ok] at h₃
  case h_5;
  split at h₃ <;> try { simp [err] at h₃ }
  simp at h₃
  all_goals {
    rcases h₃ with ⟨h₃, h₄⟩; rw [←h₃, ←h₄]; constructor
    case left => exact empty_guarded_capabilities_invariant
    case right => first |
      exact true_is_instance_of_tt |
      exact false_is_instance_of_ff |
      apply InstanceOfType.instance_of_int |
      apply InstanceOfType.instance_of_string |
      apply InstanceOfType.instance_of_entity; simp [InstanceOfEntityType]
  }

theorem type_of_var_is_sound {var : Var} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.var var) c₁ env = Except.ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (Expr.var var) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.var var) request entities v ∧ InstanceOfType v ty
:= by
  simp [EvaluatesTo, evaluate]
  simp [typeOf, typeOfVar] at h₃
  rcases h₂ with ⟨h₂, _⟩
  simp [InstanceOfRequestType] at h₂
  split at h₃ <;> simp <;> simp [ok] at h₃ <;>
  rcases h₃ with ⟨h₃, h₄⟩ <;> rw [←h₃, ←h₄] <;> constructor <;>
  try { exact empty_guarded_capabilities_invariant }
  case intro.h_1.intro.right =>
    apply InstanceOfType.instance_of_entity; simp [h₂]
  case intro.h_2.intro.right =>
    apply InstanceOfType.instance_of_entity
    simp [h₂, InstanceOfEntityType]
  case intro.h_3.intro.right =>
    apply InstanceOfType.instance_of_entity; simp [h₂]
  case intro.h_4.intro.right =>
    simp [h₂]

theorem type_of_not_is_sound {x₁ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.unaryApp .not x₁) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities},
      CapabilitiesInvariant c₁ request entities →
      RequestAndEntitiesMatchEnvironment env request entities →
      typeOf x₁ c₁ env = Except.ok (ty, c₂) →
      GuardedCapabilitiesInvariant x₁ c₂ request entities ∧
      ∃ v, EvaluatesTo x₁ request entities v ∧ InstanceOfType v ty) :
  GuardedCapabilitiesInvariant (Expr.unaryApp .not x₁) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.unaryApp .not x₁) request entities v ∧ InstanceOfType v ty
:= by
  rcases (type_of_not_inversion h₃) with ⟨h₅, bty, c₁', h₆, h₄⟩
  subst h₅; subst h₆
  apply And.intro
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    rcases (ih h₁ h₂ h₄) with ⟨_, v₁, h₆, h₇⟩ -- IH
    simp [EvaluatesTo] at h₆
    simp [EvaluatesTo, evaluate]
    rcases h₆ with h₆ | h₆ | h₆ | h₆ <;> simp [h₆]
    case intro.intro.intro.inr.inr.inr =>
      cases bty
      case anyBool =>
        rcases (instance_of_anyBool_is_bool h₇) with ⟨b, h₈⟩
        cases b <;>
        subst h₈ <;>
        simp [apply₁] <;>
        apply bool_is_instance_of_anyBool
      case tt =>
        rcases (instance_of_tt_is_true h₇) with h₈
        subst h₈
        simp [apply₁, BoolType.not]
        exact false_is_instance_of_ff
      case ff =>
        rcases (instance_of_ff_is_false h₇) with h₈
        subst h₈
        simp [apply₁, BoolType.not]
        exact true_is_instance_of_tt
    all_goals {
      exact type_is_inhabited (CedarType.bool (BoolType.not bty))
    }

theorem type_of_neg_is_sound {x₁ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.unaryApp .neg x₁) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities},
      CapabilitiesInvariant c₁ request entities →
      RequestAndEntitiesMatchEnvironment env request entities →
      typeOf x₁ c₁ env = Except.ok (ty, c₂) →
      GuardedCapabilitiesInvariant x₁ c₂ request entities ∧
      ∃ v, EvaluatesTo x₁ request entities v ∧ InstanceOfType v ty) :
  GuardedCapabilitiesInvariant (Expr.unaryApp .neg x₁) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.unaryApp .neg x₁) request entities v ∧ InstanceOfType v ty
:= by
  rcases (type_of_neg_inversion h₃) with ⟨h₅, h₆, c₁', h₄⟩
  subst h₅; subst h₆
  apply And.intro
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    rcases (ih h₁ h₂ h₄) with ⟨_, v₁, h₆, h₇⟩ -- IH
    simp [EvaluatesTo] at h₆
    simp [EvaluatesTo, evaluate]
    rcases h₆ with h₆ | h₆ | h₆ | h₆ <;> simp [h₆]
    case intro.intro.intro.inr.inr.inr =>
      rcases (instance_of_int_is_int h₇) with ⟨i, h₈⟩
      subst h₈
      simp [apply₁, intOrErr]
      cases h₉ : i.neg?
      case intro.none =>
        simp only [or_false, or_true, true_and]
        exact type_is_inhabited CedarType.int
      case intro.some i' =>
        simp only [Except.ok.injEq, false_or, exists_eq_left']
        apply InstanceOfType.instance_of_int
    all_goals {
      exact type_is_inhabited CedarType.int
    }

theorem type_of_mulBy_is_sound {x₁ : Expr} {k : Int64} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.unaryApp (.mulBy k) x₁) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities},
      CapabilitiesInvariant c₁ request entities →
      RequestAndEntitiesMatchEnvironment env request entities →
      typeOf x₁ c₁ env = Except.ok (ty, c₂) →
      GuardedCapabilitiesInvariant x₁ c₂ request entities ∧
      ∃ v, EvaluatesTo x₁ request entities v ∧ InstanceOfType v ty) :
  GuardedCapabilitiesInvariant (Expr.unaryApp (.mulBy k) x₁) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.unaryApp (.mulBy k) x₁) request entities v ∧ InstanceOfType v ty
:= by
  rcases (type_of_mulBy_inversion h₃) with ⟨h₅, h₆, c₁', h₄⟩
  subst h₅; subst h₆
  apply And.intro
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    rcases (ih h₁ h₂ h₄) with ⟨_, v₁, h₆, h₇⟩ -- IH
    simp [EvaluatesTo] at h₆
    simp [EvaluatesTo, evaluate]
    rcases h₆ with h₆ | h₆ | h₆ | h₆ <;> simp [h₆]
    case intro.intro.intro.inr.inr.inr =>
      rcases (instance_of_int_is_int h₇) with ⟨i, h₈⟩
      subst h₈
      simp [apply₁, intOrErr]
      cases h₉ : k.mul? i
      case intro.none =>
        simp only [or_false, or_true, true_and]
        exact type_is_inhabited CedarType.int
      case intro.some i' =>
        simp only [Except.ok.injEq, false_or, exists_eq_left']
        apply InstanceOfType.instance_of_int
    all_goals {
      exact type_is_inhabited CedarType.int
    }

theorem type_of_like_is_sound {x₁ : Expr} {p : Pattern} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.unaryApp (.like p) x₁) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities},
      CapabilitiesInvariant c₁ request entities →
      RequestAndEntitiesMatchEnvironment env request entities →
      typeOf x₁ c₁ env = Except.ok (ty, c₂) →
      GuardedCapabilitiesInvariant x₁ c₂ request entities ∧
      ∃ v, EvaluatesTo x₁ request entities v ∧ InstanceOfType v ty) :
  GuardedCapabilitiesInvariant (Expr.unaryApp (.like p) x₁) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.unaryApp (.like p) x₁) request entities v ∧ InstanceOfType v ty
:= by
  rcases (type_of_like_inversion h₃) with ⟨h₅, h₆, c₁', h₄⟩
  subst h₅; subst h₆
  apply And.intro
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    rcases (ih h₁ h₂ h₄) with ⟨_, v₁, h₆, h₇⟩ -- IH
    simp [EvaluatesTo] at h₆
    simp [EvaluatesTo, evaluate]
    rcases h₆ with h₆ | h₆ | h₆ | h₆ <;> simp [h₆]
    case intro.intro.intro.inr.inr.inr =>
      rcases (instance_of_string_is_string h₇) with ⟨s, h₈⟩
      subst h₈
      simp [apply₁]
      exact bool_is_instance_of_anyBool (wildcardMatch s p)
    all_goals {
      exact type_is_inhabited (.bool .anyBool)
    }

theorem type_of_is_is_sound {x₁ : Expr} {ety : EntityType} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.unaryApp (.is ety) x₁) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities},
      CapabilitiesInvariant c₁ request entities →
      RequestAndEntitiesMatchEnvironment env request entities →
      typeOf x₁ c₁ env = Except.ok (ty, c₂) →
      GuardedCapabilitiesInvariant x₁ c₂ request entities ∧
      ∃ v, EvaluatesTo x₁ request entities v ∧ InstanceOfType v ty) :
  GuardedCapabilitiesInvariant (Expr.unaryApp (.is ety) x₁) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.unaryApp (.is ety) x₁) request entities v ∧ InstanceOfType v ty
:= by
  rcases (type_of_is_inversion h₃) with ⟨h₅, ety', c₁', h₆, h₄⟩
  subst h₅; subst h₆
  apply And.intro
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    rcases (ih h₁ h₂ h₄) with ⟨_, v₁, h₆, h₇⟩ -- IH
    simp [EvaluatesTo] at h₆
    simp [EvaluatesTo, evaluate]
    rcases h₆ with h₆ | h₆ | h₆ | h₆ <;> simp [h₆]
    case intro.intro.intro.inr.inr.inr =>
      rcases (instance_of_entity_type_is_entity h₇) with ⟨uid, h₈, h₉⟩
      simp [apply₁, h₉, h₈]
      cases h₁₀ : ety == ety' <;>
      simp at h₁₀ <;>
      simp [h₁₀]
      case intro.intro.false => exact false_is_instance_of_ff
      case intro.intro.true => exact true_is_instance_of_tt
    all_goals {
      apply type_is_inhabited
    }

theorem type_of_getAttr_is_sound_for_records {x₁ : Expr} {a : Attr} {c₁ c₁' : Capabilities} {env : Environment} {rty : RecordType} {request : Request} {entities : Entities} {v₁ : Value}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : typeOf (Expr.getAttr x₁ a) c₁ env = Except.ok (ty, ∅))
  (h₃ : typeOf x₁ c₁ env = Except.ok (CedarType.record rty, c₁'))
  (h₄ : evaluate x₁ request entities = Except.ok v₁)
  (h₅ : InstanceOfType v₁ (CedarType.record rty)) :
  ∃ v,
  (getAttr v₁ a entities = Except.error Error.entityDoesNotExist ∨
   getAttr v₁ a entities = Except.error Error.extensionError ∨
   getAttr v₁ a entities = Except.error Error.arithBoundsError ∨
   getAttr v₁ a entities = Except.ok v) ∧
   InstanceOfType v ty
:= by
  rcases (instance_of_record_type_is_record h₅) with ⟨r, h₆⟩
  subst h₆
  simp [getAttr, attrsOf, Map.findOrErr]
  cases h₈ : Map.find? r a
  case intro.none =>
    simp only [or_self, false_and, exists_const]
    simp [typeOf, h₃, typeOfGetAttr, getAttrInRecord] at h₂
    split at h₂ <;> simp [ok, err] at h₂
    case h_1 _ _ h₉ =>
      subst h₂
      rcases (required_attribute_is_present h₅ h₉) with ⟨_, h₁₀⟩
      simp [h₈] at h₁₀
    case h_2 =>
      split at h₂ <;> simp at h₂
      subst h₂ ; rename_i h₁₀
      rcases (capability_implies_record_attribute h₁ h₄ h₁₀) with ⟨_, h₁₁⟩
      simp [h₈] at h₁₁
  case intro.some vₐ =>
    simp only [Except.ok.injEq, false_or, exists_eq_left']
    simp [typeOf, h₃, typeOfGetAttr, getAttrInRecord] at h₂
    split at h₂ <;> simp [ok, err] at h₂
    case h_1 _ _ h₉ =>
      subst h₂
      apply instance_of_attribute_type h₅ h₉ (by simp [Qualified.getType]) h₈
    case h_2 _ _ h₉ =>
      split at h₂ <;> simp at h₂
      subst h₂
      apply instance_of_attribute_type h₅ h₉ (by simp [Qualified.getType]) h₈

theorem type_of_getAttr_is_sound_for_entities {x₁ : Expr} {a : Attr} {c₁ c₁' : Capabilities} {env : Environment} {ety : EntityType} {request : Request} {entities : Entities} {v₁ : Value}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.getAttr x₁ a) c₁ env = Except.ok (ty, ∅))
  (h₄ : typeOf x₁ c₁ env = Except.ok (CedarType.entity ety, c₁'))
  (h₅ : evaluate x₁ request entities = Except.ok v₁)
  (h₆ : InstanceOfType v₁ (CedarType.entity ety)) :
  ∃ v,
  (getAttr v₁ a entities = Except.error Error.entityDoesNotExist ∨
   getAttr v₁ a entities = Except.error Error.extensionError ∨
   getAttr v₁ a entities = Except.error Error.arithBoundsError ∨
   getAttr v₁ a entities = Except.ok v) ∧
   InstanceOfType v ty
:= by
  rcases (instance_of_entity_type_is_entity h₆) with ⟨uid, h₇, h₈⟩
  subst h₈
  simp [getAttr, attrsOf, Entities.attrs, Map.findOrErr]
  cases h₈ : Map.find? entities uid
  case intro.intro.none =>
    simp only [Except.bind_err, Except.error.injEq, or_self, or_false, true_and]
    exact type_is_inhabited ty
  case intro.intro.some d =>
    subst h₇
    simp only [Except.bind_ok]
    cases h₉ : Map.find? d.attrs a
    case none =>
      simp
      simp [typeOf, h₄, typeOfGetAttr, getAttrInRecord] at h₃
      split at h₃ <;> simp [ok, err] at h₃
      split at h₃ <;> try simp at h₃
      case h_1.h_1 _ _ h₁₀ _ _ h₁₁ =>
        subst h₃
        rcases (well_typed_entity_attributes h₂ h₈ h₁₀) with h₁₂
        rcases (required_attribute_is_present h₁₂ h₁₁) with ⟨aᵥ, h₁₃⟩
        simp [h₉] at h₁₃
      case h_1.h_2 =>
        split at h₃ <;> simp at h₃
        subst h₃ ; rename_i h₁₃
        rcases (capability_implies_entity_attribute h₁ h₅ h₈ h₁₃) with ⟨_, h₁₄⟩
        simp [h₉] at h₁₄
    case some vₐ =>
      simp only [Except.ok.injEq, false_or, exists_eq_left']
      simp [typeOf, h₄, typeOfGetAttr, getAttrInRecord] at h₃
      split at h₃ <;> simp [ok, err] at h₃
      split at h₃ <;> try simp at h₃
      case h_1.h_1 _ _ h₁₀ _ _ h₁₁ =>
        subst h₃
        apply instance_of_attribute_type _ h₁₁ (by simp [Qualified.getType]) h₉
        apply well_typed_entity_attributes h₂ h₈ h₁₀
      case h_1.h_2 _ _ h₁₀ _ _ h₁₁ =>
        split at h₃ <;> simp at h₃
        subst h₃
        apply instance_of_attribute_type _ h₁₁ (by simp [Qualified.getType]) h₉
        apply well_typed_entity_attributes h₂ h₈ h₁₀

theorem type_of_getAttr_is_sound {x₁ : Expr} {a : Attr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.getAttr x₁ a) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities},
      CapabilitiesInvariant c₁ request entities →
      RequestAndEntitiesMatchEnvironment env request entities →
      typeOf x₁ c₁ env = Except.ok (ty, c₂) →
      GuardedCapabilitiesInvariant x₁ c₂ request entities ∧
      ∃ v, EvaluatesTo x₁ request entities v ∧ InstanceOfType v ty) :
  GuardedCapabilitiesInvariant (Expr.getAttr x₁ a) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.getAttr x₁ a) request entities v ∧ InstanceOfType v ty
:= by
  rcases (type_of_getAttr_inversion h₃) with ⟨h₅, c₁', h₄⟩
  subst h₅
  apply And.intro
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    rcases h₄ with ⟨ety, h₄⟩ | ⟨rty, h₄⟩ <;>
    rcases (ih h₁ h₂ h₄) with ⟨_, v₁, h₆, h₇⟩ <;>
    simp [EvaluatesTo] at h₆ <;>
    simp [EvaluatesTo, evaluate] <;>
    rcases h₆ with h₆ | h₆ | h₆ | h₆ <;> simp [h₆]
    case inl.intro.intro.intro.intro.inr.inr.inr =>
      exact type_of_getAttr_is_sound_for_entities h₁ h₂ h₃ h₄ h₆ h₇
    case inr.intro.intro.intro.intro.inr.inr.inr =>
      exact type_of_getAttr_is_sound_for_records h₁ h₃ h₄ h₆ h₇
    all_goals {
      exact type_is_inhabited ty
    }

theorem type_of_hasAttr_is_sound_for_records {x₁ : Expr} {a : Attr} {c₁ c₁' : Capabilities} {env : Environment} {rty : RecordType} {request : Request} {entities : Entities} {v₁ : Value}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : typeOf (Expr.hasAttr x₁ a) c₁ env = Except.ok (ty, c₂))
  (h₃ : typeOf x₁ c₁ env = Except.ok (CedarType.record rty, c₁'))
  (h₄ : evaluate x₁ request entities = Except.ok v₁)
  (h₅ : InstanceOfType v₁ (CedarType.record rty)) :
  ∃ v,
  (hasAttr v₁ a entities = Except.error Error.entityDoesNotExist ∨
   hasAttr v₁ a entities = Except.error Error.extensionError ∨
   hasAttr v₁ a entities = Except.error Error.arithBoundsError ∨
   hasAttr v₁ a entities = Except.ok v) ∧
  InstanceOfType v ty
:= by
  rcases (instance_of_record_type_is_record h₅) with ⟨r, h₅⟩
  subst h₅
  simp [hasAttr, attrsOf]
  simp [typeOf, h₃, typeOfHasAttr, hasAttrInRecord] at h₂
  split at h₂
  case intro.h_1 =>
    split at h₂ <;> simp [ok] at h₂ <;> rcases h₂ with ⟨h₂, _⟩ <;>
    simp [←h₂] <;>
    apply InstanceOfType.instance_of_bool <;>
    simp [InstanceOfBoolType]
    cases h₆ : (Map.contains r a) <;> simp
    rename_i h₇ _
    cases h₇
    case inl.intro.h₁.false.inl _ h₇ =>
      simp [CapabilitiesInvariant] at h₁
      specialize h₁ x₁ a h₇
      simp [EvaluatesTo, evaluate, h₄, hasAttr, attrsOf, h₆] at h₁
    case inl.intro.h₁.false.inr h₇ _ h₈ =>
      simp [Qualified.isRequired] at h₈
      split at h₈ <;> simp at h₈
      rcases (required_attribute_is_present h₅ h₇) with h₉
      simp [←Map.contains_iff_some_find?, h₆] at h₉
  case intro.h_2 =>
    simp [ok] at h₂
    rcases h₂ with ⟨h₂, _⟩
    simp [←h₂]
    apply InstanceOfType.instance_of_bool
    simp [InstanceOfBoolType]
    cases h₆ : (Map.contains r a) <;> simp
    rename_i _ h₇ _
    rcases (absent_attribute_is_absent h₅ h₇) with h₇
    simp [Map.contains_iff_some_find?, h₇] at h₆

theorem type_of_hasAttr_is_sound_for_entities {x₁ : Expr} {a : Attr} {c₁ c₁' : Capabilities} {env : Environment} {ety : EntityType} {request : Request} {entities : Entities} {v₁ : Value}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.hasAttr x₁ a) c₁ env = Except.ok (ty, c₂))
  (h₄ : typeOf x₁ c₁ env = Except.ok (CedarType.entity ety, c₁'))
  (h₅ : evaluate x₁ request entities = Except.ok v₁)
  (h₆ : InstanceOfType v₁ (CedarType.entity ety)) :
  ∃ v,
  (hasAttr v₁ a entities = Except.error Error.entityDoesNotExist ∨
   hasAttr v₁ a entities = Except.error Error.extensionError ∨
   hasAttr v₁ a entities = Except.error Error.arithBoundsError ∨
   hasAttr v₁ a entities = Except.ok v) ∧
   InstanceOfType v ty
:= by
  rcases (instance_of_entity_type_is_entity h₆) with ⟨uid, h₆, h₇⟩
  subst h₆ h₇
  simp [hasAttr, attrsOf]
  simp [typeOf, h₄, typeOfHasAttr] at h₃
  split at h₃ <;> try simp [err, hasAttrInRecord] at h₃
  rename_i _ rty h₇
  split at h₃
  case intro.intro.h_1.h_1 =>
    split at h₃ <;> rcases h₃ with ⟨h₃, _⟩ <;>
    apply InstanceOfType.instance_of_bool <;>
    simp [InstanceOfBoolType]
    cases h₈ : Map.contains (Entities.attrsOrEmpty entities uid) a <;> simp
    rename_i _ _ _ _  h₉
    simp [CapabilitiesInvariant] at h₁
    specialize h₁ x₁ a h₉
    simp [EvaluatesTo, evaluate, h₅, hasAttr, attrsOf, h₈] at h₁
  case intro.intro.h_1.h_2 =>
    simp [ok] at h₃
    rcases h₃ with ⟨h₃, _⟩
    simp [←h₃]
    apply InstanceOfType.instance_of_bool
    simp [InstanceOfBoolType]
    cases h₈ : Map.contains (Entities.attrsOrEmpty entities uid) a <;> simp
    rename_i _ _ h₉ _
    simp [Entities.attrsOrEmpty] at h₈
    split at h₈
    case intro.h₁.true.h_1 _ _ _ _ _ h₁₀ =>
      rcases (well_typed_entity_attributes h₂ h₁₀ h₇) with h₁₁
      rcases (absent_attribute_is_absent h₁₁ h₉) with h₁₂
      simp [Map.contains_iff_some_find?, h₁₂] at h₈
    case intro.h₁.true.h_2 =>
      rcases (Map.not_contains_of_empty a) with _
      contradiction

theorem type_of_hasAttr_is_sound {x₁ : Expr} {a : Attr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.hasAttr x₁ a) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities},
        CapabilitiesInvariant c₁ request entities →
        RequestAndEntitiesMatchEnvironment env request entities →
        typeOf x₁ c₁ env = Except.ok (ty, c₂) →
        GuardedCapabilitiesInvariant x₁ c₂ request entities ∧
        ∃ v, EvaluatesTo x₁ request entities v ∧ InstanceOfType v ty) :
  GuardedCapabilitiesInvariant (Expr.hasAttr x₁ a) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.hasAttr x₁ a) request entities v ∧ InstanceOfType v ty
:= by
  rcases (type_of_hasAttr_inversion h₃) with ⟨h₅, c₁', h₄⟩
  apply And.intro
  case left =>
    simp [GuardedCapabilitiesInvariant, CapabilitiesInvariant]
    intro h₆ x aₓ h₇
    cases h₅ <;> rename_i h₈ <;> subst h₈ <;> simp [Capabilities.singleton] at h₇
    rcases h₇ with ⟨h₇, h₈⟩
    subst h₇; subst h₈
    simp [EvaluatesTo, h₆]
  case right =>
    rcases h₄ with ⟨ety, h₄⟩ | ⟨rty, h₄⟩ <;>
    rcases (ih h₁ h₂ h₄) with ⟨_, v₁, h₆, h₇⟩ <;>
    simp [EvaluatesTo] at h₆ <;>
    simp [EvaluatesTo, evaluate] <;>
    rcases h₆ with h₆ | h₆ | h₆ | h₆ <;> simp [h₆]
    case inl.intro.intro.intro.intro.inr.inr.inr =>
      exact type_of_hasAttr_is_sound_for_entities h₁ h₂ h₃ h₄ h₆ h₇
    case inr.intro.intro.intro.intro.inr.inr.inr =>
      exact type_of_hasAttr_is_sound_for_records h₁ h₃ h₄ h₆ h₇
    all_goals {
      exact type_is_inhabited ty
    }

theorem type_of_and_is_sound {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.and x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : ∀ {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities},
    CapabilitiesInvariant c₁ request entities →
    RequestAndEntitiesMatchEnvironment env request entities →
    typeOf x₁ c₁ env = Except.ok (ty, c₂) →
    GuardedCapabilitiesInvariant x₁ c₂ request entities ∧
    ∃ v, EvaluatesTo x₁ request entities v ∧ InstanceOfType v ty)
  (ih₂ : ∀ {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities},
    CapabilitiesInvariant c₁ request entities →
    RequestAndEntitiesMatchEnvironment env request entities →
    typeOf x₂ c₁ env = Except.ok (ty, c₂) →
    GuardedCapabilitiesInvariant x₂ c₂ request entities ∧
    ∃ v, EvaluatesTo x₂ request entities v ∧ InstanceOfType v ty) :
  GuardedCapabilitiesInvariant (Expr.and x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.and x₁ x₂) request entities v ∧ InstanceOfType v ty
:= by
  rcases (type_of_and_inversion h₃) with ⟨bty₁, rc₁, h₄, h₅⟩
  specialize ih₁ h₁ h₂ h₄
  rcases ih₁ with ⟨ih₁₁, v₁, ih₁₂, ih₁₃⟩
  rcases (instance_of_bool_is_bool ih₁₃) with ⟨b₁, hb₁⟩ ; subst hb₁
  split at h₅
  case inl h₆ =>
    subst h₆
    rcases h₅ with ⟨hty, hc⟩ ; subst hty hc
    apply And.intro
    case left => exact empty_guarded_capabilities_invariant
    case right =>
      rcases (instance_of_ff_is_false ih₁₃) with h₇
      simp at h₇ ; subst h₇
      simp [EvaluatesTo] at ih₁₂
      rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
      simp [EvaluatesTo, evaluate, Result.as, ih₁₂, Coe.coe, Value.asBool] <;>
      try exact type_is_inhabited (CedarType.bool BoolType.ff)
      exact false_is_instance_of_ff
  case inr h₆ =>
    rcases h₅ with ⟨bty₂, rc₂, h₅, h₇⟩
    split at h₇ <;> rcases h₇ with ⟨hty, hc⟩ <;> subst hty hc
    case inl.intro h₈ =>
      subst h₈
      apply And.intro
      case left => exact empty_guarded_capabilities_invariant
      case right =>
        exists false ; simp [false_is_instance_of_ff]
        cases b₁
        case false =>
          rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
          simp [EvaluatesTo, evaluate, Result.as, ih₁₂, Coe.coe, Value.asBool]
        case true =>
          rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
          simp [EvaluatesTo, evaluate, Result.as, ih₁₂, Coe.coe, Value.asBool]
          simp [GuardedCapabilitiesInvariant] at ih₁₁
          specialize ih₁₁ ih₁₂
          rcases (capability_union_invariant h₁ ih₁₁) with h₇
          specialize ih₂ h₇ h₂ h₅
          rcases ih₂ with ⟨_, v₂, ih₂₂, ih₂₃⟩
          simp [EvaluatesTo] at ih₂₂
          rcases ih₂₂ with ih₂₂ | ih₂₂ | ih₂₂ | ih₂₂ <;>
          simp [EvaluatesTo, evaluate, Result.as, ih₂₂, Coe.coe, Value.asBool]
          rcases (instance_of_ff_is_false ih₂₃) with h₈
          subst h₈ ; simp only
    case inr.intro h₈ =>
      cases b₁
      case false =>
        rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
        simp [EvaluatesTo, evaluate, Result.as, ih₁₂, Coe.coe, Value.asBool, GuardedCapabilitiesInvariant] <;>
        try exact type_is_inhabited (CedarType.bool (lubBool bty₁ bty₂))
        apply instance_of_lubBool ; simp [ih₁₃]
      case true =>
        rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
        simp [EvaluatesTo, evaluate, Result.as, ih₁₂, Coe.coe, Value.asBool, GuardedCapabilitiesInvariant] <;>
        try exact type_is_inhabited (CedarType.bool (lubBool bty₁ bty₂))
        simp [GuardedCapabilitiesInvariant] at ih₁₁
        specialize ih₁₁ ih₁₂
        rcases (capability_union_invariant h₁ ih₁₁) with h₇
        specialize ih₂ h₇ h₂ h₅
        rcases ih₂ with ⟨ih₂₁, v₂, ih₂₂, ih₂₃⟩
        simp [EvaluatesTo] at ih₂₂
        rcases ih₂₂ with ih₂₂ | ih₂₂ | ih₂₂ | ih₂₂ <;>
        simp [EvaluatesTo, evaluate, Result.as, ih₂₂, Coe.coe, Value.asBool] <;>
        try exact type_is_inhabited (CedarType.bool (lubBool bty₁ bty₂))
        rcases (instance_of_bool_is_bool ih₂₃) with ⟨b₂, hb₂⟩ ; subst hb₂
        cases b₂ <;> simp
        case false =>
          exists false ; simp only [true_and]
          apply instance_of_lubBool ; simp [ih₂₃]
        case true =>
          apply And.intro
          case left =>
            simp [GuardedCapabilitiesInvariant] at ih₂₁
            specialize ih₂₁ ih₂₂
            exact capability_union_invariant ih₁₁ ih₂₁
          case right =>
            exists true ; simp only [true_and]
            apply instance_of_lubBool ; simp [ih₁₃]

theorem type_of_or_is_sound {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.or x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : ∀ {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities},
    CapabilitiesInvariant c₁ request entities →
    RequestAndEntitiesMatchEnvironment env request entities →
    typeOf x₁ c₁ env = Except.ok (ty, c₂) →
    GuardedCapabilitiesInvariant x₁ c₂ request entities ∧
    ∃ v, EvaluatesTo x₁ request entities v ∧ InstanceOfType v ty)
  (ih₂ : ∀ {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities},
    CapabilitiesInvariant c₁ request entities →
    RequestAndEntitiesMatchEnvironment env request entities →
    typeOf x₂ c₁ env = Except.ok (ty, c₂) →
    GuardedCapabilitiesInvariant x₂ c₂ request entities ∧
    ∃ v, EvaluatesTo x₂ request entities v ∧ InstanceOfType v ty) :
  GuardedCapabilitiesInvariant (Expr.or x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.or x₁ x₂) request entities v ∧ InstanceOfType v ty
:= by
  rcases (type_of_or_inversion h₃) with ⟨bty₁, rc₁, h₄, h₅⟩
  specialize ih₁ h₁ h₂ h₄
  rcases ih₁ with ⟨ih₁₁, v₁, ih₁₂, ih₁₃⟩
  rcases (instance_of_bool_is_bool ih₁₃) with ⟨b₁, hb₁⟩ ; subst hb₁
  split at h₅
  case inl h₆ =>
    subst h₆
    rcases h₅ with ⟨hty, hc⟩ ; subst hty hc
    apply And.intro
    case left => exact empty_guarded_capabilities_invariant
    case right =>
      rcases (instance_of_tt_is_true ih₁₃) with h₇
      simp at h₇ ; subst h₇
      simp [EvaluatesTo] at ih₁₂
      rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
      simp [EvaluatesTo, evaluate, Result.as, ih₁₂, Coe.coe, Value.asBool] <;>
      try exact type_is_inhabited (CedarType.bool BoolType.tt)
      exact true_is_instance_of_tt
  case inr =>
    rcases h₅ with ⟨bty₂, rc₂, h₅, h₇⟩
    specialize ih₂ h₁ h₂ h₅
    rcases ih₂ with ⟨ih₂₁, v₂, ih₂₂, ih₂₃⟩
    rcases (instance_of_bool_is_bool ih₂₃) with ⟨b₂, hb₂⟩ ; subst hb₂
    simp [EvaluatesTo]
    cases b₁ <;>
    rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
    rcases ih₂₂ with ih₂₂ | ih₂₂ | ih₂₂ | ih₂₂ <;>
    simp [evaluate, Result.as, Coe.coe, Value.asBool, ih₁₂, ih₂₂, GuardedCapabilitiesInvariant] <;>
    try exact type_is_inhabited ty
    case false.inr.inr.inr.inr.inr.inr =>
      cases b₂ <;> simp
      case false h₆ =>
        exists false ; simp only [true_and]
        cases bty₁ <;> simp at h₆ h₇
        case anyBool =>
          cases bty₂ <;> simp at h₇ <;>
          rcases h₇ with ⟨h₇, _⟩ <;> subst h₇ <;>
          try exact bool_is_instance_of_anyBool false
          exact ih₂₃
        case ff => rcases h₇ with ⟨h₇, _⟩ ; subst h₇ ; exact ih₂₃
      case true h₆ =>
        cases bty₁ <;> cases bty₂ <;> simp at h₆ h₇ <;>
        rcases h₇ with ⟨hty, hc⟩ <;> simp [hty, hc] at *
        case ff.ff.intro => rcases ih₂₃ with ⟨_, _, ih₂₃⟩ ; simp [InstanceOfBoolType] at ih₂₃
        case anyBool.ff.intro => rcases ih₂₃ with ⟨_, _, ih₂₃⟩ ; simp [InstanceOfBoolType] at ih₂₃
        case anyBool.tt.intro =>
          apply And.intro
          case left => apply empty_capabilities_invariant
          case right => exists true
        case anyBool.anyBool.intro =>
          apply And.intro
          case left =>
            simp [GuardedCapabilitiesInvariant, ih₂₂] at ih₂₁
            apply capability_intersection_invariant
            simp [ih₂₁]
          case right => exists true
        all_goals {
          simp [GuardedCapabilitiesInvariant, ih₂₂] at ih₂₁
          simp [ih₂₁]
          exists true
        }
    all_goals {
      simp [GuardedCapabilitiesInvariant] at ih₁₁ ih₂₁
      simp [ih₁₂] at ih₁₁ ; simp [ih₂₂] at ih₂₁
      rename_i h₆
      rcases ih₁₃ with ⟨_, _, ih₁₃⟩ ; simp [InstanceOfBoolType] at ih₁₃
      cases bty₁ <;> simp at h₆ ih₁₃ h₇
      cases bty₂ <;> simp at h₇ <;>
      rcases h₇ with ⟨ht, hc⟩ <;> simp [ht, hc] at * <;>
      simp [true_is_instance_of_tt, bool_is_instance_of_anyBool] <;>
      try { apply empty_capabilities_invariant } <;>
      try { assumption }
      apply capability_intersection_invariant
      simp [ih₁₁, ih₂₁]
    }

/--
If an expression is well-typed according to the typechecker, and the input
environment and capabilities satisfy some invariants, then either (1) evaluation
produces a value of the returned type or (2) it returns an error of type
`entityDoesNotExist`, `extensionError`, or `arithBoundsError`. Both options are
encoded in the `EvaluatesTo` predicate.
-/
theorem type_of_is_sound {e : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} :
  CapabilitiesInvariant c₁ request entities →
  RequestAndEntitiesMatchEnvironment env request entities →
  typeOf e c₁ env = .ok (ty, c₂) →
  GuardedCapabilitiesInvariant e c₂ request entities ∧
  ∃ (v : Value), EvaluatesTo e request entities v ∧ InstanceOfType v ty
:= by
  intro h₁ h₂ h₃
  match e with
  | .lit l => exact type_of_lit_is_sound h₃
  | .var var => exact type_of_var_is_sound h₂ h₃
  | .ite x₁ x₂ x₃ => sorry
  | .and x₁ x₂ =>
    rcases (@type_of_is_sound x₁) with ih₁
    rcases (@type_of_is_sound x₂) with ih₂
    exact type_of_and_is_sound h₁ h₂ h₃ ih₁ ih₂
  | .or x₁ x₂ =>
    rcases (@type_of_is_sound x₁) with ih₁
    rcases (@type_of_is_sound x₂) with ih₂
    exact type_of_or_is_sound h₁ h₂ h₃ ih₁ ih₂
  | .unaryApp op₁ x₁ =>
    rcases (@type_of_is_sound x₁) with ih
    match op₁ with
    | .not     => exact type_of_not_is_sound h₁ h₂ h₃ ih
    | .neg     => exact type_of_neg_is_sound h₁ h₂ h₃ ih
    | .mulBy k => exact type_of_mulBy_is_sound h₁ h₂ h₃ ih
    | .like p  => exact type_of_like_is_sound h₁ h₂ h₃ ih
    | .is ety  => exact type_of_is_is_sound h₁ h₂ h₃ ih
  | .binaryApp op₂ x₁ x₂ => sorry
  | .hasAttr x₁ a =>
    rcases (@type_of_is_sound x₁) with ih
    exact type_of_hasAttr_is_sound h₁ h₂ h₃ ih
  | .getAttr x₁ a =>
    rcases (@type_of_is_sound x₁) with ih
    exact type_of_getAttr_is_sound h₁ h₂ h₃ ih
  | .set xs => sorry
  | .record axs => sorry
  | .call xfn xs => sorry
