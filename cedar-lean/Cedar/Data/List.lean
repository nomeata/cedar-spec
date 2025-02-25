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

import Cedar.Data.LT
import Std.Data.List.Basic
import Std.Data.List.Lemmas

/-!
This file contains utilities for working with lists that are canonical or
equivalent modulo ordering and duplicates.  A canonical list is sorted and
duplicate-free according to a strict total order <.
-/

namespace List

open Cedar.Data

----- Definitions -----

def insertCanonical [LT β] [DecidableLT β] (f : α → β) (x : α) (xs : List α) : List α :=
  match xs with
  | [] => [x]
  | hd :: tl =>
    let fh := f hd
    let fx := f x
    if fx < fh
    then x :: xs
    else if fx > fh
    then hd :: insertCanonical f x tl
    else x :: tl

/--
If the ordering relation < on β is strict, then `canonicalize` returns a
canonical representation of the input list, which is sorted and free of
duplicates.
-/
def canonicalize [LT β] [DecidableLT β] (f : α → β) : List α → List α
  | [] => []
  | hd :: tl => insertCanonical f hd (canonicalize f tl)

def Equiv {α} (a b : List α) : Prop :=
  a ⊆ b ∧ b ⊆ a

infix:50 " ≡ " => Equiv

inductive Sorted [LT α] : List α → Prop where
  | nil : Sorted []
  | cons_nil {x} : Sorted (x :: nil)
  | cons_cons {x y ys} :
      x < y →
      Sorted (y :: ys) →
      Sorted (x :: y :: ys)


theorem sizeOf_snd_lt_sizeOf_list {α : Type u} {β : Type v} [SizeOf α] [SizeOf β] {x : α × β} {xs : List (α × β)} :
  x ∈ xs → sizeOf x.snd < 1 + sizeOf xs
:= by
  intro h
  have := List.sizeOf_lt_of_mem h
  have : sizeOf x = 1 + sizeOf x.1 + sizeOf x.2 := rfl
  omega

def attach₂ {α : Type u} {β : Type v} [SizeOf α] [SizeOf β] (xs : List (α × β)) :
List { x : α × β // sizeOf x.snd < 1 + sizeOf xs } :=
  xs.pmap Subtype.mk
  (λ _ => sizeOf_snd_lt_sizeOf_list)

def mapM₁ {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u}
  (xs : List α) (f : {x : α // x ∈ xs} → m β) : m (List β) :=
  xs.attach.mapM f

def mapM₂ {m : Type u → Type v} [Monad m] {γ : Type u} [SizeOf α] [SizeOf β]
  (xs : List (α × β)) (f : {x : α × β // sizeOf x.snd < 1 + sizeOf xs} → m γ) : m (List γ) :=
  xs.attach₂.mapM f

----- Theorems -----

theorem mapM_pmap_subtype [Monad m] [LawfulMonad m]
  {p : α → Prop}
  (f : α → m β)
  (as : List α)
  (h : ∀ a, a ∈ as → p a)
  : List.mapM (fun x : { a : α // p a } => f x.val) (List.pmap Subtype.mk as h)
    =
    List.mapM f as
:= by
  rw [←List.mapM'_eq_mapM]
  induction as <;> simp [*]

theorem mapM₁_eq_mapM [Monad m] [LawfulMonad m]
  (f : α → m β)
  (as : List α) :
  List.mapM₁ as (fun x : { x // x ∈ as } => f x.val) =
  List.mapM f as
:= by
  simp [mapM₁, attach, mapM_pmap_subtype]

theorem Equiv.refl {a : List α} :
  a ≡ a
:= by unfold List.Equiv; simp

theorem Equiv.symm {a b : List α} :
  a ≡ b → b ≡ a
:= by unfold List.Equiv; simp; intro h₁ h₂; simp [h₁, h₂]

theorem Equiv.trans {a b c : List α} :
  a ≡ b → b ≡ c → a ≡ c
:= by
  unfold List.Equiv
  simp
  intro h₁ h₂ h₃ h₄
  apply And.intro
  exact List.Subset.trans h₁ h₃
  exact List.Subset.trans h₄ h₂

theorem cons_equiv_cons (x : α) (xs ys : List α) :
  xs ≡ ys → x :: xs ≡ x :: ys
:= by
  unfold List.Equiv
  intro h₁
  have ⟨h₁, h₂⟩ := h₁
  apply And.intro
  all_goals {
    apply List.cons_subset_cons; assumption
  }

theorem dup_head_equiv (x : α) (xs : List α) :
  x :: x :: xs ≡ x :: xs
:= by unfold List.Equiv; simp [List.subset_def]

theorem swap_cons_cons_equiv (x₁ x₂ : α) (xs : List α) :
  x₁ :: x₂ :: xs ≡ x₂ :: x₁ :: xs
:= by
  unfold List.Equiv
  simp [List.subset_def]
  apply And.intro
  all_goals { intro a h₁; simp [h₁] }

theorem filter_equiv (f : α -> Bool) (xs ys : List α) :
  xs ≡ ys → xs.filter f ≡ ys.filter f
:= by
  simp [List.Equiv, List.subset_def]
  intros h₁ h₂
  apply And.intro <;>
  intro a h₃ <;>
  simp [List.mem_filter] <;>
  rw [List.mem_filter] at h₃
  exact And.intro (h₁ h₃.left) h₃.right
  exact And.intro (h₂ h₃.left) h₃.right

theorem map_equiv (f : α → β) (xs ys : List α) :
  xs ≡ ys → xs.map f ≡ ys.map f
:= by
  intro h
  have ⟨a, b⟩ := h
  apply And.intro <;> simp [List.subset_def] <;>
  intro p h <;>
  exists p <;>
  rw [List.subset_def] at a b <;>
  simp
  exact a h
  exact b h

theorem filterMap_equiv (f : α → Option β) (xs ys : List α) :
  xs ≡ ys → xs.filterMap f ≡ ys.filterMap f
:= by
  simp [List.Equiv, List.subset_def]
  intros h₁ h₂
  apply And.intro <;>
  intro b a h₃ h₄ <;>
  exists a <;>
  simp [h₄]
  exact h₁ h₃
  exact h₂ h₃

theorem tail_of_sorted_is_sorted {x : α} {xs : List α} [LT α] :
  Sorted (x :: xs) → Sorted xs
:= by
  intro h₁; cases h₁
  exact Sorted.nil
  assumption

theorem if_strictly_sorted_then_head_lt_tail [LT α] [StrictLT α] (x : α) (xs : List α) :
  Sorted (x :: xs) → ∀ y, y ∈ xs → x < y
:= by
  intro h₁ y h₂
  induction xs generalizing y
  case nil => contradiction
  case cons _ _ hd tl ih =>
    cases h₂
    case head => cases h₁; assumption
    case tail h₂ =>
      apply ih
      case _ =>
        cases h₁
        case cons_cons h₃ h₄ =>
          cases h₄
          case _ => exact Sorted.cons_nil
          case cons_cons _ _ hd' tl' h₅ h₆ =>
            apply Sorted.cons_cons _ h₅
            apply StrictLT.transitive x hd hd' h₃ h₆
      case _ => assumption

theorem if_strictly_sorted_equiv_then_head_eq [LT α] [StrictLT α] (x y : α) (xs ys : List α) :
  Sorted (x :: xs) →
  Sorted (y :: ys) →
  (x :: xs) ≡ (y :: ys) →
  x = y
:= by
  intro h₁ h₂
  unfold List.Equiv; intro h₃
  replace ⟨h₃, h₄⟩ := h₃
  simp at h₃; simp at h₄
  replace ⟨h₃, _⟩ := h₃
  replace ⟨h₄, _⟩ := h₄
  cases h₃ <;> cases h₄ <;> try { assumption }
  case _ _ h₅ => simp [h₅]
  case _ h₅ h₆ =>
    have hc₁ := if_strictly_sorted_then_head_lt_tail x xs h₁ y h₆
    have hc₂ := if_strictly_sorted_then_head_lt_tail y ys h₂ x h₅
    have hc₃ := StrictLT.asymmetric x y hc₁
    contradiction

theorem if_strictly_sorted_equiv_then_tail_subset [LT α] [StrictLT α] (x : α) (xs ys : List α) :
  Sorted (x :: xs) →
  Sorted (x :: ys) →
  (x :: xs) ⊆ (x :: ys) →
  xs ⊆ ys
:= by
  intro h₁ h₂ h₃
  simp at h₃
  simp [List.subset_def]
  intro y h₄
  simp [List.subset_def] at h₃
  specialize h₃ h₄
  cases h₃
  case inr => assumption
  case inl _ h₅ =>
    subst h₅
    have h₆ := if_strictly_sorted_then_head_lt_tail y xs h₁ y h₄
    have h₇ := StrictLT.irreflexive y
    contradiction

theorem if_strictly_sorted_equiv_then_tail_equiv [LT α] [StrictLT α] (x : α) (xs ys : List α) :
  Sorted (x :: xs) →
  Sorted (x :: ys) →
  (x :: xs) ≡ (x :: ys) →
  xs ≡ ys
:= by
  unfold List.Equiv
  intro h₁ h₂ h₃
  replace ⟨h₃, h₄⟩ := h₃
  apply And.intro
  exact if_strictly_sorted_equiv_then_tail_subset x xs ys h₁ h₂ h₃
  exact if_strictly_sorted_equiv_then_tail_subset x ys xs h₂ h₁ h₄

theorem if_strictly_sorted_equiv_then_eq [LT α] [StrictLT α] (xs ys : List α) :
  Sorted xs → Sorted ys → xs ≡ ys → xs = ys
:= by
  intro h₁ h₂ h₃
  induction xs generalizing ys
  case nil =>
    apply Eq.symm
    rw [←List.subset_nil]
    unfold List.Equiv at h₃
    exact h₃.right
  case cons xhd xtl ih =>
    cases ys
    case nil =>
      unfold List.Equiv at h₃
      rw [←List.subset_nil]
      exact h₃.left
    case cons yhd ytl =>
      simp
      have h₅ : xhd = yhd := if_strictly_sorted_equiv_then_head_eq xhd yhd xtl ytl h₁ h₂ h₃
      simp [h₅]
      subst h₅
      apply ih
      exact (tail_of_sorted_is_sorted h₁)
      exact (tail_of_sorted_is_sorted h₂)
      exact (if_strictly_sorted_equiv_then_tail_equiv xhd xtl ytl h₁ h₂ h₃)

theorem insertCanonical_singleton [LT β] [DecidableLT β] (f : α → β)  (x : α) :
  insertCanonical f x [] = [x]
:= by unfold insertCanonical; rfl

theorem insertCanonical_not_nil [DecidableEq β] [LT β] [DecidableRel (α := β) (· < ·)] (f : α → β) (x : α) (xs : List α) :
  insertCanonical f x xs ≠ []
:= by
  unfold insertCanonical
  cases xs with
  | nil => simp
  | cons hd tl =>
    simp
    by_cases h₁ : (f x) < (f hd) <;> simp [h₁]
    by_cases h₂ : (f x) > (f hd) <;> simp [h₂]

theorem insertCanonical_cases [LT α] [DecidableLT α] (x y : α) (ys : List α) :
  (x < y ∧ insertCanonical id x (y :: ys) = x :: y :: ys) ∨
  (¬ x < y ∧ x > y ∧ insertCanonical id x (y :: ys) = y :: insertCanonical id x ys) ∨
  (¬ x < y ∧ ¬ x > y ∧ insertCanonical id x (y :: ys) = x :: ys)
:= by
  generalize h₁ : insertCanonical id x ys = xys
  unfold insertCanonical; simp
  by_cases (x < y)
  case pos _ _ h₂ => simp [h₂]
  case neg _ _ h₂ =>
    simp [h₂]
    by_cases (x > y)
    case pos _ _ h₃ => simp [h₃, h₁]
    case neg _ _ h₃ => simp [h₃]

theorem insertCanonical_sorted [LT α] [StrictLT α] [DecidableLT α] (x : α) (xs : List α) :
  Sorted xs → Sorted (insertCanonical id x xs)
:= by
  intro h₁
  unfold insertCanonical
  induction xs <;> simp
  case nil => exact Sorted.cons_nil
  case cons _ _ hd tl ih =>
    specialize ih (tail_of_sorted_is_sorted h₁)
    split
    case inl _ _ h₂ => exact Sorted.cons_cons h₂ h₁
    case inr _ _ h₂ =>
      by_cases (x > hd)
      case neg _ _ h₃ =>
        simp [h₃]
        unfold GT.gt at h₃
        have h₄ := StrictLT.if_not_lt_gt_then_eq x hd h₂ h₃
        subst h₄
        exact h₁
      case pos _ _ h₃ =>
        simp [h₃]
        cases tl
        case nil =>
          have h₄ := insertCanonical_singleton id x
          simp [h₄]
          apply Sorted.cons_cons (by apply h₃) Sorted.cons_nil
        case cons _ _ hd' tl' =>
          simp at ih
          have h₄ := insertCanonical_cases x hd' tl'
          cases h₄
          case inl _ _ _ h₄ =>
            replace ⟨h₄, h₅⟩ := h₄
            simp [h₅]
            apply Sorted.cons_cons (by apply h₃)
            apply Sorted.cons_cons h₄ (tail_of_sorted_is_sorted h₁)
          case inr _ _ _ h₄ =>
            cases h₄
            case inl _ _ _ h₄ =>
              replace ⟨h₄, h₅, h₆⟩ := h₄
              simp [h₆]
              simp [h₄, h₅] at ih
              apply Sorted.cons_cons _ ih
              apply if_strictly_sorted_then_head_lt_tail hd (hd' :: tl') h₁
              simp only [find?, mem_cons, true_or]
            case inr _ _ _ h₄ =>
              replace ⟨h₄, h₅, h₆⟩ := h₄
              simp [h₆]
              unfold GT.gt at h₅
              have h₇ := StrictLT.if_not_lt_gt_then_eq x hd' h₄ h₅
              subst h₇
              exact h₁

theorem insertCanonical_equiv [LT α] [StrictLT α] [DecidableLT α] (x : α) (xs : List α) :
  x :: xs ≡ insertCanonical id x xs
:= by
  unfold insertCanonical
  induction xs
  case nil => simp; exact Equiv.refl
  case cons _ _ hd tl ih =>
    simp
    split
    case inl => exact Equiv.refl
    case inr _ _ h₁ =>
      split
      case inr _ _ h₂ =>
        have h₃ := StrictLT.if_not_lt_gt_then_eq x hd h₁ h₂
        subst h₃
        exact dup_head_equiv x tl
      case inl _ _ h₂ =>
        cases tl
        case nil =>
          have h₃ := insertCanonical_singleton id x
          simp [h₃]
          apply swap_cons_cons_equiv
        case cons _ _ _ hd' tl' =>
          simp at ih
          have h₃ := insertCanonical_cases x hd' tl'
          cases h₃
          case inl _ _ _ h₃ =>
            simp [h₃]
            unfold List.Equiv
            simp only [cons_subset, mem_cons, true_or, or_true, true_and]
            apply And.intro
            all_goals {
              simp [List.subset_def]
              intro a h₄; simp [h₄]
            }
          case inr _ _ _ h₃ =>
            cases h₃
            case inr _ _ _ h₃ =>
              replace ⟨h₃, h₄, h₅⟩ := h₃
              simp [h₅]
              unfold GT.gt at h₄
              have h₆ := StrictLT.if_not_lt_gt_then_eq x hd' h₃ h₄
              subst h₆
              unfold List.Equiv
              simp only [cons_subset, mem_cons, true_or, or_true, Subset.refl, and_self, subset_cons]
            case inl _ _ _ h₃ =>
              replace ⟨h₃, h₄, h₅⟩ := h₃
              simp [h₅]
              simp [h₃, h₄] at ih
              have h₆ := swap_cons_cons_equiv x hd (hd' :: tl')
              apply Equiv.trans h₆
              apply cons_equiv_cons
              exact ih

theorem canonicalize_nil [LT β] [DecidableLT β] (f : α → β) :
  canonicalize f [] = []
:= by unfold canonicalize; rfl

theorem canonicalize_not_nil [DecidableEq β] [LT β] [DecidableLT β] (f : α → β) (xs : List α) :
  xs ≠ [] ↔ (canonicalize f xs) ≠ []
:= by
  apply Iff.intro
  case _ =>
    intro h₀
    cases xs with
    | nil => contradiction
    | cons hd tl =>
      unfold canonicalize
      apply insertCanonical_not_nil
  case _ =>
    unfold canonicalize
    intro h₀
    cases xs <;> simp at h₀; simp

theorem canonicalize_equiv [LT α] [StrictLT α] [DecidableLT α] (xs : List α) :
  xs ≡ canonicalize id xs
:= by
  induction xs
  case nil => simp [canonicalize_nil, Equiv.refl]
  case cons _ _ hd tl ih =>
    unfold canonicalize
    generalize h₁ : canonicalize id tl = ys
    simp [h₁] at ih
    have h₂ := insertCanonical_equiv hd ys
    apply Equiv.trans _ h₂
    apply cons_equiv_cons
    exact ih

theorem canonicalize_sorted [LT α] [StrictLT α] [DecidableLT α] (xs : List α) :
  Sorted (canonicalize id xs)
:= by
  induction xs
  case nil => simp [canonicalize_nil, Sorted.nil]
  case cons _ _ hd tl ih =>
    unfold canonicalize
    apply insertCanonical_sorted
    exact ih

theorem if_equiv_strictLT_then_canonical [LT α] [StrictLT α] [DecidableLT α] (xs ys : List α) :
  xs ≡ ys → (canonicalize id xs) = (canonicalize id ys)
:= by
  intro h₁
  apply if_strictly_sorted_equiv_then_eq
  exact (canonicalize_sorted xs)
  exact (canonicalize_sorted ys)
  have h₂ := Equiv.symm (canonicalize_equiv xs)
  have h₃ := Equiv.symm (canonicalize_equiv ys)
  apply Equiv.trans h₂
  apply Equiv.symm
  apply Equiv.trans h₃
  apply Equiv.symm
  exact h₁

theorem canonicalize_id_idempotent [LT α] [StrictLT α] [DecidableLT α] (xs : List α) :
  canonicalize id (canonicalize id xs) = canonicalize id xs
:= by
  apply if_equiv_strictLT_then_canonical
  apply List.Equiv.symm
  apply canonicalize_equiv

def Forallᵥ {α β γ} (p : β → γ → Prop) (kvs₁ : List (α × β)) (kvs₂ : List (α × γ)) : Prop :=
  List.Forall₂ (fun kv₁ kv₂ => kv₁.fst = kv₂.fst ∧ p kv₁.snd kv₂.snd) kvs₁ kvs₂

theorem insertCanonical_preserves_forallᵥ {α β γ} [LT α] [StrictLT α] [DecidableLT α] {p : β → γ → Prop}
  {kv₁ : α × β} {kv₂ : α × γ} {kvs₁ : List (α × β)} {kvs₂ : List (α × γ)}
  (h₁ : kv₁.fst = kv₂.fst ∧ p kv₁.snd kv₂.snd)
  (h₂ : Forallᵥ p kvs₁ kvs₂) :
  Forallᵥ p (insertCanonical Prod.fst kv₁ kvs₁) (insertCanonical Prod.fst kv₂ kvs₂)
:= by
  simp [Forallᵥ] at *
  cases h₂
  case nil =>
    simp [insertCanonical_singleton]
    apply Forall₂.cons (by exact h₁) (by simp only [Forall₂.nil])
  case cons hd₁ hd₂ tl₁ tl₂ h₃ h₄ =>
    simp [insertCanonical]
    split <;> split
    case inl.inl =>
      apply Forall₂.cons (by exact h₁)
      apply Forall₂.cons (by exact h₃) (by exact h₄)
    case inl.inr h₅ h₆ =>
      simp [h₁, h₃] at h₅
      have _ := StrictLT.asymmetric kv₂.fst hd₂.fst h₅
      split <;> contradiction
    case inr.inl h₅ h₆ =>
      simp [h₁, h₃] at h₅ h₆
      split
      case inl => contradiction
      case inr =>
        apply Forall₂.cons (by exact h₃)
        apply insertCanonical_preserves_forallᵥ h₁ h₄
    case inr.inr h₅ h₆ =>
      simp [h₁, h₃] at h₅ h₆
      split
      case inl => contradiction
      case inr => apply Forall₂.cons (by exact h₁) (by exact h₄)

theorem canonicalize_preserves_forallᵥ {α β γ} [LT α] [StrictLT α] [DecidableLT α] (p : β → γ → Prop) (kvs₁ : List (α × β)) (kvs₂ : List (α × γ)) :
  List.Forallᵥ p kvs₁ kvs₂ →
  List.Forallᵥ p (List.canonicalize Prod.fst kvs₁) (List.canonicalize Prod.fst kvs₂)
:= by
  simp [Forallᵥ]
  intro h₁
  cases h₁
  case nil => simp [canonicalize_nil]
  case cons hd₁ hd₂ tl₁ tl₂ h₂ h₃ =>
    simp [canonicalize]
    have h₄ := canonicalize_preserves_forallᵥ p tl₁ tl₂ h₃
    apply insertCanonical_preserves_forallᵥ h₂ h₄

theorem any_of_mem {f : α → Bool} {x : α} {xs : List α}
  (h₁ : x ∈ xs)
  (h₂ : f x) :
  any xs f = true
:= by
  cases xs <;> simp at h₁
  case cons hd tl =>
    simp [List.any_cons]
    rcases h₁ with h₁ | h₁
    subst h₁ ; simp [h₂]
    apply Or.inr ; exists x

end List
