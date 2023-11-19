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
This file contains useful definitions and lemmas about the
least upper bound (LUB) functions on Cedar types.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

inductive IsLubOfRecordTypes : List (Attr × Qualified CedarType) → List (Attr × Qualified CedarType) → List (Attr × Qualified CedarType) → Prop :=
  | nil : IsLubOfRecordTypes [] [] []
  | cons {a : Attr} {qty qty₁ qty₂ : Qualified CedarType} {rty rty₁ rty₂ : List (Attr × Qualified CedarType)}
    (h₁ : lubQualifiedType qty₁ qty₂ = .some qty)
    (h₂ : IsLubOfRecordTypes rty rty₁ rty₂) :
    IsLubOfRecordTypes ((a, qty) :: rty) ((a, qty₁) :: rty₁) ((a, qty₂) :: rty₂)

theorem lubRecordType_is_lub_of_record_types {rty rty₁ rty₂ : List (Attr × Qualified CedarType)} :
  lubRecordType rty₁ rty₂ = .some rty →
  IsLubOfRecordTypes rty rty₁ rty₂
:= by
  intro h₁
  unfold lubRecordType at h₁
  split at h₁ <;> try simp at h₁
  case h_1 => subst h₁ ; exact IsLubOfRecordTypes.nil
  case h_2 a hd₁ tl₁ a' hd₂ tl₂ =>
    split at h₁ <;> try contradiction
    rename_i h₂ ; subst h₂
    cases h₂ : lubQualifiedType hd₁ hd₂ <;> simp [h₂] at h₁
    cases h₃ : lubRecordType tl₁ tl₂ <;> simp [h₃] at h₁
    rename_i hd tl ; subst h₁
    apply IsLubOfRecordTypes.cons h₂
    apply lubRecordType_is_lub_of_record_types h₃

theorem lubRecord_find_implies_find {a : Attr} {qty : QualifiedType} {rty rty₁ rty₂ : List (Attr × Qualified CedarType)}
  (h₁ : IsLubOfRecordTypes rty rty₁ rty₂)
  (h₂ : Map.find? (Map.mk rty) a = .some qty) :
  (∃ qty₁ qty₂,
    Map.find? (Map.mk rty₁) a = .some qty₁ ∧
    Map.find? (Map.mk rty₂) a = .some qty₂ ∧
    lubQualifiedType qty₁ qty₂ = .some qty)
:= by
  simp [Map.find?, Map.kvs] at *
  induction h₁
  case nil => simp [List.find?] at h₂
  case cons a' hd hd₁ hd₂ tl tl₁ tl₂ h₃ _ ih =>
    simp [Map.find?, Map.kvs] at *
    cases h₅ : a' == a
    case false =>
      simp [List.find?, h₅] at *
      apply ih h₂
    case true =>
      simp [List.find?, h₅] at *
      simp [h₂, h₃]

theorem lubRecord_find_implied_by_find_left {a : Attr} {qty₁ : QualifiedType} {rty rty₁ rty₂ : List (Attr × Qualified CedarType)}
  (h₁ : IsLubOfRecordTypes rty rty₁ rty₂)
  (h₂ : Map.find? (Map.mk rty₁) a = .some qty₁) :
  (∃ qty qty₂,
    Map.find? (Map.mk rty₂) a = .some qty₂ ∧
    Map.find? (Map.mk rty) a = .some qty ∧
    lubQualifiedType qty₁ qty₂ = .some qty)
:= by
  simp [Map.find?, Map.kvs] at *
  induction h₁
  case nil => simp [List.find?] at h₂
  case cons a' hd hd₁ hd₂ tl tl₁ tl₂ h₃ _ ih =>
    simp [Map.find?, Map.kvs] at *
    cases h₅ : a' == a
    case false =>
      simp [List.find?, h₅] at *
      apply ih h₂
    case true =>
      simp [List.find?, h₅] at *
      simp [←h₂, h₃]

theorem lubRecord_contains_left {a : Attr} {rty rty₁ rty₂ : List (Attr × Qualified CedarType)}
  (h₁ : IsLubOfRecordTypes rty rty₁ rty₂)
  (h₂ : Map.contains (Map.mk rty₁) a = true) :
  Map.contains (Map.mk rty) a = true
:= by
  simp [Map.contains_iff_some_find?] at *
  rcases h₂ with ⟨qty₁, h₂⟩
  rcases (lubRecord_find_implied_by_find_left h₁ h₂) with ⟨qty, qty₂, h₃⟩
  exists qty ; simp [h₃]

theorem lubRecord_find_implies_find_left {a : Attr} {qty : QualifiedType} {rty rty₁ rty₂ : List (Attr × Qualified CedarType)}
  (h₁ : IsLubOfRecordTypes rty rty₁ rty₂)
  (h₂ : Map.find? (Map.mk rty) a = some qty) :
  ∃ qty₁,
    Map.find? (Map.mk rty₁) a = some qty₁ ∧
    Qualified.isRequired qty₁ = Qualified.isRequired qty
:= by
  rcases (lubRecord_find_implies_find h₁ h₂) with ⟨qty₁, qty₂, h₃, h₄, h₅⟩
  exists qty₁ ; simp [h₃]
  unfold lubQualifiedType at h₅
  split at h₅ <;> try simp at h₅
  all_goals {
    rename_i ty₁ ty₂
    cases h₆ : ty₁ ⊔ ty₂ <;> simp [h₆] at h₅
    subst h₅
    simp [Qualified.isRequired]
  }

theorem lubBool_comm {bty₁ bty₂ : BoolType} :
  lubBool bty₁ bty₂ = lubBool bty₂ bty₁
:= by
  simp [lubBool] ; split <;> rename_i h <;>
  rw [eq_comm] at h <;> simp [h]

mutual
theorem lubQualified_comm {qty₁ qty₂ : Qualified CedarType} :
  lubQualifiedType qty₁ qty₂ = lubQualifiedType qty₂ qty₁
:= by
  unfold lubQualifiedType
  split
  case h_1 | h_2 =>
    rename_i ty₁ ty₂
    rcases (@lub_comm ty₁ ty₂) with h
    simp [h]
  case h_3 =>
    rename_i h₁ h₂
    split <;> try { rfl } <;>
    rename_i ty₁ ty₂ <;> by_contra
    apply h₁ ty₂ ty₁ <;> rfl
    apply h₂ ty₂ ty₁ <;> rfl

theorem lubRecord_comm {rty₁ rty₂ : List (Attr × Qualified CedarType)} :
  lubRecordType rty₁ rty₂ = lubRecordType rty₂ rty₁
:= by
  unfold lubRecordType
  split <;> simp
  case h_2 =>
    rename_i a₁ hd₁ tl₁ a₂ hd₂ tl₂
    split <;> rename_i h₃ <;> rw [eq_comm] at h₃ <;> simp [h₃]
    subst h₃
    rcases (@lubQualified_comm hd₁ hd₂) with h₄
    rcases (@lubRecord_comm tl₁ tl₂) with h₅
    simp [h₄, h₅]
  case h_3 =>
    rename_i h₁ h₂
    split <;> try { contradiction } <;> try rfl
    split <;> try rfl
    rename_i a₁ hd₁ tl₁ a₂ hd₂ tl₂ h₃ ; subst h₃
    by_contra
    apply h₂ a₁ hd₂ tl₂ a₁ hd₁ tl₁ <;> rfl

theorem lub_comm {ty₁ ty₂ : CedarType} :
  (ty₁ ⊔ ty₂) = (ty₂ ⊔ ty₁)
:= by
  unfold lub?
  split
  case h_1 => simp [lubBool_comm]
  case h_2 =>
    rename_i s₁ s₂
    rcases (@lub_comm s₁ s₂) with h
    simp [h]
  case h_3 =>
    rename_i rty₁ rty₂
    rcases (@lubRecord_comm rty₁ rty₂) with h
    simp [h]
  case h_4 =>
    rename_i h₁ h₂ h₃
    split <;> split <;> rename_i h₄
    case inl.h_4 | inr.h_4 =>
      rename_i _ _ h₅ _ _ _ _
      rw [eq_comm] at h₅
      simp [h₅]
    all_goals {
      rename_i v₁ v₂
      by_contra
      try { apply h₁ v₂ v₁ <;> rfl  }
      try { apply h₂ v₂ v₁ <;> rfl  }
      try { apply h₃ v₂ v₁ <;> rfl  }
    }
end


theorem lubQualified_is_lub_of_getType {qty qty₁ qty₂: Qualified CedarType}
  (h₁ : lubQualifiedType qty₁ qty₂ = .some qty) :
  (qty₁.getType ⊔ qty₂.getType) = .some qty.getType
:= by
  unfold lubQualifiedType at h₁
  split at h₁ <;> try simp at h₁
  all_goals {
    rename_i aty₁ aty₂
    cases h₂ : (aty₁ ⊔ aty₂) <;> simp [h₂] at h₁
    rename_i aty
    simp [Qualified.getType, ←h₁]
  }




end Cedar.Thm
