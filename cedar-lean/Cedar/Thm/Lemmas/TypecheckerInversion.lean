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
import Cedar.Validation

/-!
This file contains type checker inversion lemmas.
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

theorem getAttrInRecord_has_empty_capabilities {x₁ : Expr} {a : Attr} {c₁ c₂ : Capabilities} {rty : RecordType} {ty ty₁ : CedarType} :
  getAttrInRecord ty rty x₁ a c₁ = Except.ok (ty₁, c₂) →
  c₂ = ∅
:= by
  intro h₁
  simp [getAttrInRecord] at h₁
  split at h₁ <;> simp [ok, err] at h₁
  simp [h₁]
  split at h₁ <;> simp at h₁
  simp [h₁]

theorem type_of_getAttr_inversion {x₁ : Expr} {a : Attr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.getAttr x₁ a) c₁ env = Except.ok (ty, c₂)) :
  c₂ = ∅ ∧
  ∃ c₁',
    (∃ ety, typeOf x₁ c₁ env = Except.ok (.entity ety, c₁')) ∨
    (∃ rty, typeOf x₁ c₁ env = Except.ok (.record rty, c₁'))
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    rcases res with ⟨ty₁, c₁'⟩
    simp [typeOfGetAttr] at h₁
    split at h₁ <;> try contradiction
    case mk.h_1 =>
      simp
      apply getAttrInRecord_has_empty_capabilities h₁
    case mk.h_2 =>
      simp
      split at h₁ <;> try simp [err] at h₁
      apply getAttrInRecord_has_empty_capabilities h₁

theorem type_of_hasAttr_inversion {x₁ : Expr} {a : Attr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.hasAttr x₁ a) c₁ env = Except.ok (ty, c₂)) :
  (c₂ = ∅ ∨ c₂ = Capabilities.singleton x₁ a) ∧
  ∃ c₁',
    (∃ ety, typeOf x₁ c₁ env = Except.ok (.entity ety, c₁')) ∨
    (∃ rty, typeOf x₁ c₁ env = Except.ok (.record rty, c₁'))
:= by
  simp [typeOf, typeOfHasAttr] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    rcases res with ⟨ty₁, c₁'⟩
    simp at h₁
    split at h₁ <;> try simp [err, ok, hasAttrInRecord] at h₁
    case mk.h_1 _ _ =>
      split at h₁ <;> try split at h₁
      all_goals {
        simp [ok] at h₁
        simp [h₁]
      }
    case mk.h_2 _ _ =>
      split at h₁
      split at h₁ <;> try split at h₁
      all_goals {
        simp [ok] at h₁
        try simp [h₁]
      }


theorem type_of_and_inversion {x₁ x₂ : Expr} {c c' : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.and x₁ x₂) c env = Except.ok (ty, c')) :
  ∃ bty₁ c₁,
    typeOf x₁ c env = .ok (.bool bty₁, c₁) ∧
    if bty₁ = BoolType.ff
    then ty = .bool BoolType.ff ∧ c' = ∅
    else ∃ bty₂ c₂,
      typeOf x₂ (c ∪ c₁) env = .ok (.bool bty₂, c₂) ∧
      if bty₂ = BoolType.ff
      then ty = .bool BoolType.ff ∧ c' = ∅
      else ty = .bool (lubBool bty₁ bty₂) ∧ c' = c₁ ∪ c₂
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c env <;> simp [h₂] at *
  rename_i res₁
  simp [typeOfAnd] at h₁
  split at h₁ <;> simp [ok, err] at h₁
  case ok.h_1 h₃ =>
    exists BoolType.ff, res₁.snd ; simp [h₁]
    simp at h₃
    rcases h₁ with ⟨h₁, _⟩ ; subst h₁
    rcases h₃ with ⟨h₃, _⟩
    simp [←h₃]
  case ok.h_2 bty₁ c₁ h₃ h₄ =>
    exists bty₁, c₁
    simp at h₄ ; rcases h₄ with ⟨hty₁, hc₁⟩ ; simp [←hty₁, ←hc₁]
    split ; contradiction
    cases h₄ : typeOf x₂ (c ∪ res₁.snd) env <;> simp [h₄] at *
    rename_i res₂
    split at h₁ <;> simp at h₁ <;>
    rcases h₁ with ⟨hty, hc⟩ <;> subst hty hc
    case h_1.intro hty₂ =>
      exists BoolType.ff, res₂.snd ; simp [←hty₂]
    case h_2.intro hty₂ =>
      exists BoolType.tt, res₂.snd ; simp [←hty₂, hc₁]
      cases bty₁ <;> simp at h₃ <;> simp [lubBool]
    case h_3.intro bty₂ h₄ h₅ hty₂ =>
      exists BoolType.anyBool, res₂.snd
      cases bty₂ <;> simp at *
      simp [←hty₂, hc₁, lubBool]
      split
      case inl h₆ => simp [h₆]
      case inr => rfl

end Cedar.Thm
