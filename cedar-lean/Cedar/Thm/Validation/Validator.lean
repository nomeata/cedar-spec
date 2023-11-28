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
import Cedar.Thm.Validation.Typechecker

/-!
This file defines the top-level soundness property for the validator.

todo: fill in `sorry`s. Some invariants may need to be adjusted. The current
definitions are an informed guess based on the corresponding Dafny proof.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

def EvaluatesToBool (policy : Policy) (request : Request) (entities : Entities) : Prop :=
  ∃ (b : Bool), EvaluatesTo policy.toExpr request entities b

/--
If a policy successfully validates, then evaluating that policy with any request
will either (1) return a Boolean value or (2) return an error of type `entityDoesNotExist`
or `extensionError`. Both options are encoded in the `EvaluatesToBool` predicate.
The validator cannot protect against `entityDoesNotExist` and `extensionError`
errors because it has no knowledge of the entities/context that will be provided
at authorization time.
-/
theorem typecheck_policy_is_sound (policy : Policy) (env : Environment) (t : CedarType) (request : Request) (entities : Entities) :
  RequestAndEntitiesMatchEnvironment env request entities →
  typecheckPolicy policy env = .ok t →
  EvaluatesToBool policy request entities
:= by
  sorry

def RequestMatchesSchema (schema : Schema) (request : Request) : Prop :=
  match schema.acts.find? request.action with
  | some entry =>
      request.principal.ty ∈ entry.appliesToPrincipal ∧
      request.resource.ty ∈ entry.appliesToResource ∧
      InstanceOfType request.context (.record entry.context)
  | _ => False

def RequestAndEntitiesMatchSchema (schema : Schema) (request : Request) (entities : Entities) : Prop :=
  RequestMatchesSchema schema request ∧
  InstanceOfEntityTypeStore entities schema.ets ∧
  InstanceOfActionStore entities (schema.acts.mapOnValues (fun entry => { ancestors := entry.ancestors }))

theorem match_schema_implies_match_environments (schema : Schema) (request : Request) (entities : Entities) :
  RequestAndEntitiesMatchSchema schema request entities →
  ∀ env, env ∈ schema.toEnvironments →
  RequestAndEntitiesMatchEnvironment env request entities
:= by
  sorry

theorem typecheck_policy_with_environments_is_sound (policy : Policy) (envs : List Environment) (request : Request) (entities : Entities) :
  (∀ env, env ∈ envs → RequestAndEntitiesMatchEnvironment env request entities) →
  typecheckPolicyWithEnvironments policy envs = .ok () →
  EvaluatesToBool policy request entities
:= by
  sorry

theorem forM_all_ok {α ε} (l : List α) (f : α → Except ε Unit) :
  l.forM f = .ok () →
  ∀ x, x ∈ l → f x = .ok ()
:= by
  intro h₀ x hₓ
  induction l
  case nil => cases hₓ
  case cons hd tl ih =>
    simp at h₀
    simp [bind, Except.bind] at h₀
    cases hₓ
    -- x == hd
    case head =>
      generalize h : f x = fx
      cases fx <;> rewrite [h] at h₀ <;> simp at h₀
      case ok =>
        rfl
    -- x ∈ tl
    case tail =>
      generalize h : f hd = fhd
      cases fhd <;> rewrite [h] at h₀ <;> simp at h₀
      case ok =>
        apply ih <;> assumption
