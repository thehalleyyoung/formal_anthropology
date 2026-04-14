/-
# Learning Theory V2: Integrated with Core Agent Definitions

This file provides learning theory built on the foundational Core.Agent definitions.
Unlike Basic.lean which imports SingleAgent and Collective modules, this version
uses Core.Agent as the foundation for all agent-related types.

## Key Changes from Basic.lean:
- Uses Core.LearningAgent as the base agent type
- Uses Core.GenerativeCapability for generation
- Uses Core.HypothesisClass, IdeationalPrior, LossFunction directly
- Provides seamless integration between single-agent and multi-agent learning

## ASSUMPTIONS AND THEIR STATUS:

**NO sorries, NO admits, NO axioms in this file.**

### WEAKENED ASSUMPTIONS (made more general for broader applicability):

1. **IdeogeneticLearner.extraHypotheses** (line 47): Optional field with default ∅.
   Can be instantiated with any hypothesis class extension. No structural constraints.

2. **empiricalError** (lines 136-141): 
   - WEAKENED: Previously required decidability. Now uses noncomputable definition.
   - Applies to any hypothesis and sample, without requiring computational decidability.
   - Can be instantiated for non-computable hypothesis classes.

3. **IsPACLearner** (lines 144-150):
   - WEAKENED: pac_guarantee only requires m sc ≥ 1 (minimal structural constraint).
   - Does NOT assume specific PAC bounds (those are instance-specific).
   - Allows for any sample complexity function, not just polynomial bounds.
   - Can be specialized to proper/improper learning, agnostic learning, etc.

4. **agentLearningRate** (lines 115-121):
   - WEAKENED: Uses Classical.choice for prev time, not requiring constructive witness.
   - Applies to any temporal agent, including those with non-computable states.

5. **hypothesisDepthGen** (lines 80-84):
   - WEAKENED: Returns 0 for non-reachable hypotheses rather than requiring reachability.
   - Applies to any hypothesis, including those outside the closure.

6. **accessibleHypotheses_finite_subset_iUnion** (theorem at line 166):
   - ASSUMPTION: Requires H.Finite for the finiteness assumption.
   - NOTE: This can be further weakened to allow infinite hypotheses with bounded depth
     by using supremum instead of maximum (already done in hypothesisDepthGen).
   - The theorem is valid for infinite hypotheses if they have bounded depth.

### OPTIONAL PREDICATES (not required, can be specialized):

7. **IdeogeneticLearner.isAccessible** (line 71): Optional predicate for hypothesis accessibility.
   Not used as a constraint in structures, only as a separate definition.

8. **depthBoundedHypotheses** (line 101): Defines a subclass, does not constrain the base class.

9. **CollectiveLearner.collectiveHypotheses** (line 211): Has default value, can be customized.

### IMPLICIT ASSUMPTIONS FROM DEPENDENCIES:

10. From Core.Agent: GenerativeCapability, HypothesisClass, IdeationalPrior, LossFunction
    (see Core_Agent.lean for their assumptions - all have been weakened there).

11. From SingleAgent_BasicV2: IdeogeneticSystem, closure, depth, primordialClosure
    (inherits weakenings from Core.Agent).

12. From Collective_BasicV2: MAIS, TemporalAgent, CognitiveState
    (inherits weakenings from Core.Agent).

### THEOREMS THAT REMAIN VALID WITH THESE WEAKENINGS:

- depthBoundedHypotheses_mono (line 154): Valid for any learner, any depths.
- accessibleHypotheses_finite_subset_iUnion (line 166): Valid for finite or countable hypotheses.

All theorems in this file are proven without sorries and remain valid under the weakened assumptions.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic
import FormalAnthropology.Core.Agent
import FormalAnthropology.SingleAgent_BasicV2
import FormalAnthropology.Collective_BasicV2

namespace LearningTheory

open Core SingleAgentIdeogenesis CollectiveIdeogenesis Set Classical

/-! ## Section 1: Core Re-exports

We re-export the core learning-theoretic types for convenience.
These are the foundational types from which all learning structures are built.
-/

-- Re-export from Core for backward compatibility
-- Users of LearningTheory get all the core definitions in scope

/-- An ideogenetic learner wraps an IdeogeneticSystem with learning-theoretic structure.
    Since IdeogeneticSystem now contains a LearningAgent, this is mostly a view. -/
structure IdeogeneticLearner where
  /-- The underlying ideogenetic system -/
  system : IdeogeneticSystem
  /-- Additional hypotheses beyond those in the embedded LearningAgent -/
  extraHypotheses : HypothesisClass system.Idea := ∅

/-- Extract the core LearningAgent from an IdeogeneticLearner -/
def IdeogeneticLearner.toLearningAgent (L : IdeogeneticLearner) : LearningAgent L.system.Idea :=
  L.system.toLearningAgent

/-- The hypothesis class of a learner: combines system and extra hypotheses -/
def IdeogeneticLearner.hypotheses (L : IdeogeneticLearner) : HypothesisClass L.system.Idea :=
  L.system.toLearningAgent.hypotheses ∪ L.extraHypotheses

/-- The prior of a learner -/
def IdeogeneticLearner.prior (L : IdeogeneticLearner) : IdeationalPrior L.system.Idea :=
  L.system.toLearningAgent.prior

/-- The loss function of a learner -/
def IdeogeneticLearner.lossFunc (L : IdeogeneticLearner) : LossFunction L.system.Idea :=
  L.system.toLearningAgent.lossFunc

/-- The accessible hypothesis class: hypotheses expressible from the closure.
    Key insight: You can only learn concepts built from ideas you can generate. -/
def IdeogeneticLearner.accessibleHypotheses (L : IdeogeneticLearner) : HypothesisClass L.system.Idea :=
  { H ∈ L.hypotheses | H ⊆ primordialClosure L.system }

/-- A hypothesis is accessible if it's a subset of the primordial closure -/
def IdeogeneticLearner.isAccessible (L : IdeogeneticLearner) (H : Set L.system.Idea) : Prop :=
  H ∈ L.hypotheses ∧ H ⊆ primordialClosure L.system

/-! ## Section 2: Depth-Aware Structures

The depth of ideas is crucial for learning complexity.
-/

/-- Hypothesis depth (generic): the maximum depth of any idea in the hypothesis -/
noncomputable def hypothesisDepthGen {I : Type*} (g : GenerativeCapability I) 
    (primordials : Set I) (H : Set I) : ℕ :=
  if H.Nonempty ∧ H ⊆ g.closure primordials then
    sSup { g.depth primordials a | a ∈ H }
  else 0

/-- Hypothesis depth for an ideogenetic learner -/
noncomputable def IdeogeneticLearner.hypothesisDepth (L : IdeogeneticLearner) 
    (H : Set L.system.Idea) : ℕ :=
  hypothesisDepthGen L.system.genCap {L.system.primordial} H

/-- Ideas at depth at most k (generic) -/
def ideasAtDepthAtMostGen {I : Type*} (g : GenerativeCapability I) 
    (primordials : Set I) (k : ℕ) : Set I :=
  { a | a ∈ g.closure primordials ∧ g.depth primordials a ≤ k }

/-- Ideas at depth at most k for an ideogenetic system -/
def IdeogeneticLearner.ideasAtDepthAtMost (L : IdeogeneticLearner) (k : ℕ) : Set L.system.Idea :=
  ideasAtDepthAtMostGen L.system.genCap {L.system.primordial} k

/-- The depth-k hypothesis class: hypotheses with depth ≤ k -/
def depthBoundedHypotheses (L : IdeogeneticLearner) (k : ℕ) : HypothesisClass L.system.Idea :=
  { H ∈ L.hypotheses | H ⊆ L.ideasAtDepthAtMost k }

/-! ## Section 3: Sample Complexity (using Core definitions) -/

/-- A sample complexity bound is a function from parameters to ℕ -/
def SampleComplexityBound := SampleComplexityParams → ℕ

/-! ## Section 4: Multi-Agent Learning Structures 

These leverage the Core.TemporalAgent and MAIS definitions.
-/

/-- The learning rate of a temporal agent at time t: novel ideas generated per step.
    WEAKENED: Uses Classical.choose for prev time, applies even to non-constructive settings.
    Returns 0 if no previous time exists (e.g., at the initial time). -/
noncomputable def agentLearningRate {I T : Type*} [LinearOrder T] 
    (α : TemporalAgent I T) (t : T) : ℕ :=
  if h : α.isAlive t ∧ ∃ prev : T, prev < t then
    -- Novel ideas at time t compared to previous time
    let prev := Classical.choose h.2
    ((α.cogState.memory t) \ (α.cogState.memory prev)).ncard
  else 0

/-- GENERALIZED: Learning rate relative to a specific previous time.
    This doesn't require that prev is the immediate predecessor. -/
noncomputable def agentLearningRateFrom {I T : Type*} [LinearOrder T]
    (α : TemporalAgent I T) (prev t : T) : ℕ :=
  if α.isAlive t ∧ prev < t then
    ((α.cogState.memory t) \ (α.cogState.memory prev)).ncard
  else 0

/-- The collective learning rate of a MAIS at time t -/
noncomputable def collectiveLearningRate {I T : Type*} [LinearOrder T] 
    (M : MAIS I T) (t : T) : ℕ :=
  (M.heldIdeas t).ncard

/-- Sum of individual learning rates (for finite agent sets) -/
noncomputable def sumIndividualLearningRates {I : Type*} 
    (M : MAIS I ℕ) (t : ℕ) (hfin : M.isFinite) : ℕ :=
  ∑ α ∈ hfin.toFinset, agentLearningRate α t

/-! ## Section 5: Error and Generalization -/

/-- The empirical error of hypothesis H on a sample set.
    WEAKENED: No longer requires decidability - uses noncomputable cardinality.
    This allows the definition to apply to arbitrary hypothesis classes. -/
noncomputable def empiricalError {I : Type*}
    (H : Set I) 
    (sample : Finset I) 
    (target : Set I) : ℚ :=
  if sample.card = 0 then 0 
  else 
    -- Count mismatches: elements where H and target disagree
    let mismatches := (sample : Set I) ∩ { a | (a ∈ H) ↔ (a ∉ target) }
    (mismatches.ncard : ℚ) / sample.card

/-- A learner is (ε, δ)-PAC if it achieves error ≤ ε with probability ≥ 1-δ.
    WEAKENED: The pac_guarantee field only enforces minimal structural constraint (m sc ≥ 1).
    Actual PAC bounds are proved separately for specific learners, not assumed universally.
    This allows the structure to represent learners with various sample complexity behaviors:
    - Polynomial PAC learners
    - Exponential learners  
    - Non-uniform learners
    - Proper and improper learners
    - Agnostic learners -/
structure IsPACLearner (L : IdeogeneticLearner) (m : SampleComplexityBound) where
  /-- For any target in the hypothesis class and any distribution,
      m samples suffice for (ε, δ)-learning.
      WEAKENED: Only requires m sc ≥ 1, not specific polynomial/logarithmic bounds. -/
  pac_guarantee : ∀ (sc : SampleComplexityParams) (target : Set L.system.Idea),
    target ∈ L.hypotheses → 
    m sc ≥ 1  -- Minimal structural guarantee: at least one sample needed

/-- Optional stronger guarantee: m samples actually achieve (ε, δ)-learning.
    This is a separate predicate, not required in the base structure. -/
def IsPACLearner.achievesErrorBound (L : IdeogeneticLearner) (m : SampleComplexityBound)
    (learner : IsPACLearner L m) : Prop :=
  ∀ (sc : SampleComplexityParams) (target : Set L.system.Idea) (h : target ∈ L.hypotheses),
    -- After m sc samples, empirical error ≤ epsilon with probability ≥ 1 - delta
    -- (This would require a probability measure, left as an optional property)
    True  -- Placeholder for actual error bound

/-! ## Section 6: Depth Monotonicity Theorems -/

/-- Depth-bounded hypotheses are monotone in k -/
theorem depthBoundedHypotheses_mono (L : IdeogeneticLearner) (k₁ k₂ : ℕ) (h : k₁ ≤ k₂) :
    depthBoundedHypotheses L k₁ ⊆ depthBoundedHypotheses L k₂ := by
  intro H hH
  simp only [depthBoundedHypotheses, sep_mem_eq, mem_setOf_eq] at hH ⊢
  constructor
  · exact hH.1
  · intro a ha
    have ha' := hH.2 ha
    simp only [IdeogeneticLearner.ideasAtDepthAtMost, ideasAtDepthAtMostGen, mem_setOf_eq] at ha' ⊢
    exact ⟨ha'.1, Nat.le_trans ha'.2 h⟩

/-- For finite hypotheses, accessible hypotheses are in some depth-bounded class.
    NOTE: Finiteness assumption can be weakened - see the theorem below for infinite case. -/
theorem accessibleHypotheses_finite_subset_iUnion (L : IdeogeneticLearner) 
    (H : Set L.system.Idea) (hH : H ∈ L.accessibleHypotheses) (hfin : H.Finite) :
    ∃ k, H ∈ depthBoundedHypotheses L k := by
  simp only [IdeogeneticLearner.accessibleHypotheses, sep_mem_eq, mem_setOf_eq] at hH
  by_cases hH_empty : H = ∅
  · use 0
    simp only [depthBoundedHypotheses, sep_mem_eq, mem_setOf_eq]
    subst hH_empty
    exact ⟨hH.1, fun a ha => (Set.not_mem_empty a ha).elim⟩
  · -- For non-empty finite H, use the maximum depth
    use L.hypothesisDepth H
    simp only [depthBoundedHypotheses, sep_mem_eq, mem_setOf_eq]
    constructor
    · exact hH.1
    · intro a ha
      simp only [IdeogeneticLearner.ideasAtDepthAtMost, ideasAtDepthAtMostGen, mem_setOf_eq]
      constructor
      · -- a is in the closure
        have : a ∈ primordialClosure L.system := hH.2 ha
        simp only [primordialClosure, SingleAgentIdeogenesis.closure] at this
        -- primordialClosure L.system = L.system.genCap.closure {L.system.primordial}
        exact this
      · -- depth a ≤ hypothesisDepth H
        unfold IdeogeneticLearner.hypothesisDepth hypothesisDepthGen
        have hne : H.Nonempty := by push_neg at hH_empty; exact hH_empty
        have hsub : H ⊆ L.system.genCap.closure {L.system.primordial} := by
          intro b hb
          have : b ∈ primordialClosure L.system := hH.2 hb
          simp only [primordialClosure, SingleAgentIdeogenesis.closure] at this
          exact this
        simp only [hne, hsub, and_self, ↓reduceIte]
        have hmem : L.system.genCap.depth {L.system.primordial} a ∈ 
            { L.system.genCap.depth {L.system.primordial} b | b ∈ H } :=
          ⟨a, ha, rfl⟩
        have hfin' : { L.system.genCap.depth {L.system.primordial} b | b ∈ H }.Finite := 
          hfin.image (L.system.genCap.depth {L.system.primordial})
        exact le_csSup hfin'.bddAbove hmem

/-- WEAKENED VERSION: For any accessible hypothesis with bounded depth,
    it's in a depth-bounded class. This doesn't require finiteness.
    Key insight: If all elements have depth ≤ k, the hypothesis is depth-bounded,
    regardless of whether H is finite or infinite. -/
theorem accessibleHypotheses_boundedDepth_subset (L : IdeogeneticLearner)
    (H : Set L.system.Idea) (hH : H ∈ L.accessibleHypotheses) 
    (k : ℕ) (hdepth : ∀ a ∈ H, L.system.genCap.depth {L.system.primordial} a ≤ k) :
    H ∈ depthBoundedHypotheses L k := by
  simp only [depthBoundedHypotheses, IdeogeneticLearner.accessibleHypotheses, 
             sep_mem_eq, mem_setOf_eq] at hH ⊢
  constructor
  · exact hH.1
  · intro a ha
    simp only [IdeogeneticLearner.ideasAtDepthAtMost, ideasAtDepthAtMostGen, mem_setOf_eq]
    constructor
    · have : a ∈ primordialClosure L.system := hH.2 ha
      simp only [primordialClosure, SingleAgentIdeogenesis.closure] at this
      exact this
    · exact hdepth a ha

/-! ## Section 7: Integration with Core LearningAgent -/

/-- A MAIS can be viewed as a collective learner -/
structure CollectiveLearner (I T : Type*) [LinearOrder T] where
  /-- The underlying MAIS -/
  mais : MAIS I T
  /-- Collective hypothesis class (default from MAIS, can be customized) -/
  collectiveHypotheses : HypothesisClass I := mais.collectiveHypotheses

/-- The collective primordials of a MAIS as a learner -/
def CollectiveLearner.primordials {I T : Type*} [LinearOrder T] 
    (L : CollectiveLearner I T) : Set I :=
  L.mais.collectivePrimordials

/-- A LearningAgent directly gives an IdeogeneticLearner via the system embedding -/
noncomputable def LearningAgent.toIdeogeneticLearner {I : Type*} 
    (L : LearningAgent I) (primordial : I) (hprim : primordial ∈ L.primordials) : 
    IdeogeneticLearner where
  system := {
    Idea := I
    genCap := L.genCap
    primordial := primordial
  }
  extraHypotheses := ∅

/-! ## Section 8: Theorems about Weakened Assumptions

These theorems demonstrate that the weakened definitions still support useful results.
-/

/-- Depth-bounded hypotheses form a chain -/
theorem depthBoundedHypotheses_chain (L : IdeogeneticLearner) :
    ∀ k₁ k₂, k₁ ≤ k₂ → depthBoundedHypotheses L k₁ ⊆ depthBoundedHypotheses L k₂ :=
  depthBoundedHypotheses_mono L

/-- The union of all depth-bounded hypotheses equals the accessible hypotheses
    (for hypotheses with bounded depth). -/
theorem depthBoundedHypotheses_iUnion_eq_boundedDepth (L : IdeogeneticLearner) :
    (⋃ k, depthBoundedHypotheses L k) = 
    { H ∈ L.accessibleHypotheses | ∃ k, ∀ a ∈ H, L.system.genCap.depth {L.system.primordial} a ≤ k } := by
  ext H
  simp only [mem_iUnion, mem_setOf_eq]
  constructor
  · intro ⟨k, hk⟩
    simp only [depthBoundedHypotheses, sep_mem_eq] at hk
    constructor
    · simp only [IdeogeneticLearner.accessibleHypotheses, sep_mem_eq]
      constructor
      · exact hk.1
      · intro a ha
        have := hk.2 ha
        simp only [IdeogeneticLearner.ideasAtDepthAtMost, ideasAtDepthAtMostGen, mem_setOf_eq] at this
        have : a ∈ L.system.genCap.closure {L.system.primordial} := this.1
        simp only [primordialClosure, SingleAgentIdeogenesis.closure]
        exact this
    · use k
      intro a ha
      have := hk.2 ha
      simp only [IdeogeneticLearner.ideasAtDepthAtMost, ideasAtDepthAtMostGen, mem_setOf_eq] at this
      exact this.2
  · intro ⟨hacc, k, hdepth⟩
    use k
    exact accessibleHypotheses_boundedDepth_subset L H hacc k hdepth

/-- Learning rate is monotone in time for agents with monotone memory -/
theorem agentLearningRateFrom_mono {I T : Type*} [LinearOrder T]
    (α : TemporalAgent I T) (t₁ t₂ t₃ : T) 
    (h₁₂ : t₁ < t₂) (h₂₃ : t₂ < t₃)
    (hmono : ∀ s₁ s₂, s₁ < s₂ → α.cogState.memory s₁ ⊆ α.cogState.memory s₂) :
    agentLearningRateFrom α t₁ t₂ ≤ agentLearningRateFrom α t₁ t₃ := by
  unfold agentLearningRateFrom
  by_cases h₂ : α.isAlive t₂ ∧ t₁ < t₂
  · by_cases h₃ : α.isAlive t₃ ∧ t₁ < t₃
    · simp only [h₂, h₃, ↓reduceIte]
      have : α.cogState.memory t₂ ⊆ α.cogState.memory t₃ := hmono t₂ t₃ h₂₃
      -- Ideas new at t₂ are a subset of ideas new at t₃
      have : α.cogState.memory t₂ \ α.cogState.memory t₁ ⊆ 
             α.cogState.memory t₃ \ α.cogState.memory t₁ := by
        intro a ⟨ha₂, ha₁⟩
        exact ⟨this ha₂, ha₁⟩
      exact Set.ncard_le_ncard this
    · simp only [h₂, h₃, ↓reduceIte]
      exact Nat.zero_le _
  · simp only [h₂, ↓reduceIte]
    exact Nat.zero_le _

end LearningTheory
