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

import Cedar.Thm.Validation.Typechecker.Basic
import Cedar.Thm.Validation.Typechecker.Types


/-!
This file proves that typechecking of `.unaryApp` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem type_of_not_inversion {x₁ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.unaryApp .not x₁) c₁ env = Except.ok (ty, c₂)) :
  c₂ = ∅ ∧
  ∃ bty c₁',
    ty = .bool bty.not ∧
    typeOf x₁ c₁ env = Except.ok (.bool bty, c₁')
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    rcases res with ⟨ty₁, c₁'⟩
    simp [typeOfUnaryApp] at h₁
    split at h₁ <;> try contradiction
    case mk.h_1 _ ty₁ bty _ =>
      simp [ok] at h₁
      apply And.intro
      case left => simp [h₁]
      case right =>
        exists bty, c₁'
        simp only [and_true, h₁]

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

theorem type_of_neg_inversion {x₁ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.unaryApp .neg x₁) c₁ env = Except.ok (ty, c₂)) :
  c₂ = ∅ ∧
  ty = .int ∧
  ∃ c₁', typeOf x₁ c₁ env = Except.ok (.int, c₁')
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    rcases res with ⟨ty₁, c₁'⟩
    simp [typeOfUnaryApp] at h₁
    split at h₁ <;> try contradiction
    simp [ok] at h₁
    simp [h₁]

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

theorem type_of_mulBy_inversion {x₁ : Expr} {k : Int64} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.unaryApp (.mulBy k) x₁) c₁ env = Except.ok (ty, c₂)) :
  c₂ = ∅ ∧
  ty = .int ∧
  ∃ c₁', typeOf x₁ c₁ env = Except.ok (.int, c₁')
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    rcases res with ⟨ty₁, c₁'⟩
    simp [typeOfUnaryApp] at h₁
    split at h₁ <;> try contradiction
    simp [ok] at h₁
    simp [h₁]

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

theorem type_of_like_inversion {x₁ : Expr} {p : Pattern} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.unaryApp (.like p) x₁) c₁ env = Except.ok (ty, c₂)) :
  c₂ = ∅ ∧
  ty = .bool .anyBool ∧
  ∃ c₁', typeOf x₁ c₁ env = Except.ok (.string, c₁')
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    rcases res with ⟨ty₁, c₁'⟩
    simp [typeOfUnaryApp] at h₁
    split at h₁ <;> try contradiction
    simp [ok] at h₁
    simp [h₁]

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

theorem type_of_is_inversion {x₁ : Expr} {ety : EntityType} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.unaryApp (.is ety) x₁) c₁ env = Except.ok (ty, c₂)) :
  c₂ = ∅ ∧
  ∃ ety' c₁',
    ty = (.bool (if ety = ety' then .tt else .ff)) ∧
    typeOf x₁ c₁ env = Except.ok (.entity ety', c₁')
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    rcases res with ⟨ty₁, c₁'⟩
    simp [typeOfUnaryApp] at h₁
    split at h₁ <;> try contradiction
    case mk.h_5 _ _ ety' h₃ =>
      simp only [UnaryOp.is.injEq] at h₃
      subst h₃
      simp [ok] at h₁
      apply And.intro
      case left => simp [h₁]
      case right =>
        exists ety', c₁'
        simp only [h₁, and_self]

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

end Cedar.Thm
