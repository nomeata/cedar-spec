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

-- Easy property: the empty capability set satisifies the invariant
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
  | .lit l => exact type_of_lit_is_sound h₁ h₂ h₃
  | .var var => exact type_of_var_is_sound h₁ h₂ h₃
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
  | .getAttr x₁ a => sorry
  | .set xs => sorry
  | .record axs => sorry
  | .call xfn xs => sorry

----- Lit and var lemmas -----

theorem type_of_lit_is_sound {l : Prim} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
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
  (h₁ : CapabilitiesInvariant c₁ request entities)
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

end
