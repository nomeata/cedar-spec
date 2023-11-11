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
  simp [EvaluatesTo, evaluate, h₂, hasAttr, attrsOf] at h₁
  exact Map.contains_implies_some_find? h₁

theorem capability_implies_entity_attribute {x₁ : Expr} {a : Attr} {c₁ : Capabilities} {request : Request} {entities : Entities} {uid: EntityUID} {d: EntityData}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : evaluate x₁ request entities = Except.ok (Value.prim (Prim.entityUID uid)))
  (h₃ : Map.find? entities uid = some d)
  (h₄ : (x₁, a) ∈ c₁) :
  ∃ vₐ, d.attrs.find? a = some vₐ
:= by
  simp [CapabilitiesInvariant] at h₁
  specialize h₁ x₁ a h₄
  simp [EvaluatesTo, evaluate, h₂, hasAttr, attrsOf, Entities.attrsOrEmpty, h₃] at h₁
  exact Map.contains_implies_some_find? h₁

----- Base typechecking soundness lemmas -----

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

mutual

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
  match e with -- We do the proof using mutually inductive theorems.
  | .lit l => exact type_of_lit_is_sound h₃
  | .var var => exact type_of_var_is_sound h₂ h₃
  | .ite x₁ x₂ x₃ => sorry
  | .and x₁ x₂ => sorry
  | .or x₁ x₂ => sorry
  | .unaryApp op₁ x₁ =>
    match op₁ with
    | .not     => exact type_of_not_is_sound h₁ h₂ h₃
    | .neg     => exact type_of_neg_is_sound h₁ h₂ h₃
    | .mulBy k => exact type_of_mulBy_is_sound h₁ h₂ h₃
    | .like p  => exact type_of_like_is_sound h₁ h₂ h₃
    | .is ety  => exact type_of_is_is_sound h₁ h₂ h₃
  | .binaryApp op₂ x₁ x₂ => sorry
  | .hasAttr x₁ a => sorry
  | .getAttr x₁ a => exact type_of_getAttr_is_sound h₁ h₂ h₃
  | .set xs => sorry
  | .record axs => sorry
  | .call xfn xs => sorry

----- Unary op lemmas -----

theorem type_of_not_is_sound {x₁ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.unaryApp .not x₁) c₁ env = Except.ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (Expr.unaryApp .not x₁) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.unaryApp .not x₁) request entities v ∧ InstanceOfType v ty
:= by
  rcases (type_of_not_inversion h₃) with ⟨h₅, bty, c₁', h₆, h₄⟩
  subst h₅; subst h₆
  apply And.intro
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    rcases (type_of_is_sound h₁ h₂ h₄) with ⟨h₅, v₁, h₆, h₇⟩ -- IH
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
  (h₃ : typeOf (Expr.unaryApp .neg x₁) c₁ env = Except.ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (Expr.unaryApp .neg x₁) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.unaryApp .neg x₁) request entities v ∧ InstanceOfType v ty
:= by
  rcases (type_of_neg_inversion h₃) with ⟨h₅, h₆, c₁', h₄⟩
  subst h₅; subst h₆
  apply And.intro
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    rcases (type_of_is_sound h₁ h₂ h₄) with ⟨h₅, v₁, h₆, h₇⟩ -- IH
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
  (h₃ : typeOf (Expr.unaryApp (.mulBy k) x₁) c₁ env = Except.ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (Expr.unaryApp (.mulBy k) x₁) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.unaryApp (.mulBy k) x₁) request entities v ∧ InstanceOfType v ty
:= by
  rcases (type_of_mulBy_inversion h₃) with ⟨h₅, h₆, c₁', h₄⟩
  subst h₅; subst h₆
  apply And.intro
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    rcases (type_of_is_sound h₁ h₂ h₄) with ⟨h₅, v₁, h₆, h₇⟩ -- IH
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
  (h₃ : typeOf (Expr.unaryApp (.like p) x₁) c₁ env = Except.ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (Expr.unaryApp (.like p) x₁) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.unaryApp (.like p) x₁) request entities v ∧ InstanceOfType v ty
:= by
  rcases (type_of_like_inversion h₃) with ⟨h₅, h₆, c₁', h₄⟩
  subst h₅; subst h₆
  apply And.intro
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    rcases (type_of_is_sound h₁ h₂ h₄) with ⟨h₅, v₁, h₆, h₇⟩ -- IH
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
  (h₃ : typeOf (Expr.unaryApp (.is ety) x₁) c₁ env = Except.ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (Expr.unaryApp (.is ety) x₁) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.unaryApp (.is ety) x₁) request entities v ∧ InstanceOfType v ty
:= by
  rcases (type_of_is_inversion h₃) with ⟨h₅, ety', c₁', h₆, h₄⟩
  subst h₅; subst h₆
  apply And.intro
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    rcases (type_of_is_sound h₁ h₂ h₄) with ⟨h₅, v₁, h₆, h₇⟩ -- IH
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

----- getAttr lemma -----

theorem type_of_getAttr_is_sound {x₁ : Expr} {a : Attr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.getAttr x₁ a) c₁ env = Except.ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (Expr.getAttr x₁ a) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.getAttr x₁ a) request entities v ∧ InstanceOfType v ty
:= by
  rcases (type_of_getAttr_inversion h₃) with ⟨h₅, c₁', h₄⟩
  subst h₅
  apply And.intro
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    rcases h₄ with ⟨ety, h₄⟩ | ⟨rty, h₄⟩ <;>
    rcases (type_of_is_sound h₁ h₂ h₄) with ⟨_, v₁, h₆, h₇⟩ <;> -- IH
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

end
