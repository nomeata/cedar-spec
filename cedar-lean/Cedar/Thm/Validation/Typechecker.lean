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

import Cedar.Thm.Validation.Typechecker.And
import Cedar.Thm.Validation.Typechecker.GetAttr
import Cedar.Thm.Validation.Typechecker.HasAttr
import Cedar.Thm.Validation.Typechecker.IfThenElse
import Cedar.Thm.Validation.Typechecker.LitVar
import Cedar.Thm.Validation.Typechecker.Or
import Cedar.Thm.Validation.Typechecker.UnaryApp

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
  | .ite x₁ x₂ x₃ =>
    rcases (@type_of_is_sound x₁) with ih₁
    rcases (@type_of_is_sound x₂) with ih₂
    rcases (@type_of_is_sound x₃) with ih₃
    exact type_of_ite_is_sound h₁ h₂ h₃ ih₁ ih₂ ih₃
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
