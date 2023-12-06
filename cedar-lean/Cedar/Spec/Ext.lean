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

import Cedar.Spec.Ext.Decimal
import Cedar.Spec.Ext.IPAddr

/-! This file defines Cedar extension values. -/

namespace Cedar.Spec

open Cedar.Data
open Cedar.Spec.Ext

----- Definitions -----

abbrev IPAddr := IPAddr.IPNet

inductive Ext where
  | decimal (d : Decimal)
  | ipaddr (ip : IPAddr)

def Ext.lt : Ext → Ext → Bool
  | .decimal d₁, .decimal d₂ => d₁ < d₂
  | .ipaddr ip₁, .ipaddr ip₂ => ip₁ < ip₂
  | .decimal  _, .ipaddr _   => true
  | .ipaddr   _, .decimal _  => false

----- Derivations -----

deriving instance Repr, DecidableEq for Ext

instance : LT Ext where
lt := fun x y => Ext.lt x y

instance Ext.decLt (x y : Ext) : Decidable (x < y) :=
if  h : Ext.lt x y then isTrue h else isFalse h

instance : Coe Decimal Ext where
  coe d := .decimal d

instance : Coe IPAddr Ext where
  coe a := .ipaddr a


instance Ext.strictLT : StrictLT Ext where
  asymmetric a b   := by
    cases a <;> cases b <;> simp [LT.lt, Ext.lt] <;>
    rename_i x₁ x₂ <;> intro h₁
    case decimal =>
      rcases (Decimal.strictLT.asymmetric x₁ x₂) with h₂
      simp [LT.lt] at h₂
      cases h₃ : Decimal.lt x₁ x₂ <;>
      simp [h₃] at h₁ h₂ ; simp [h₂]
    case ipaddr =>
      rcases (Cedar.Spec.Ext.IPAddr.IPNet.strictLT.asymmetric x₁ x₂) with h₂
      simp [LT.lt] at h₂
      cases h₃ : Cedar.Spec.Ext.IPAddr.IPNet.lt x₁ x₂ <;>
      simp [h₃] at h₁ h₂ ; simp [h₂]
  transitive a b c := by
    cases a <;> cases b <;> cases c <;> simp [LT.lt, Ext.lt] <;>
    rename_i x₁ x₂ x₃ <;> intro h₁ h₂
    case decimal =>
      rcases (Decimal.strictLT.transitive x₁ x₂ x₃) with h₃
      simp [LT.lt] at h₃
      cases h₄ : Decimal.lt x₁ x₂ <;> simp [h₄] at *
      cases h₅ : Decimal.lt x₂ x₃ <;> simp [h₅] at *
      simp [h₃]
    case ipaddr =>
      rcases (Cedar.Spec.Ext.IPAddr.IPNet.strictLT.transitive x₁ x₂ x₃) with h₃
      simp [LT.lt] at h₃
      cases h₄ : Cedar.Spec.Ext.IPAddr.IPNet.lt x₁ x₂ <;> simp [h₄] at *
      cases h₅ : Cedar.Spec.Ext.IPAddr.IPNet.lt x₂ x₃ <;> simp [h₅] at *
      simp [h₃]
  connected  a b   := by
    cases a <;> cases b <;> simp [LT.lt, Ext.lt] <;>
    rename_i x₁ x₂ <;> intro h₁
    case decimal =>
      rcases (Decimal.strictLT.connected x₁ x₂) with h₂
      simp [LT.lt, h₁] at h₂
      rcases h₂ with h₂ | h₂ <;> simp [h₂]
    case ipaddr =>
      rcases (Cedar.Spec.Ext.IPAddr.IPNet.strictLT.connected x₁ x₂) with h₂
      simp [LT.lt, h₁] at h₂
      rcases h₂ with h₂ | h₂ <;> simp [h₂]


end Cedar.Spec
