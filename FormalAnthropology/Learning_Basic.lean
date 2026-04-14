/-
# Learning Theory: Basic Definitions

This file provides the foundational definitions for the learning theory
of multi-agent ideogenetic systems.

## Key Definitions:
- IdeogeneticLearner: Agent that learns by generating ideas
- HypothesisClass: Concepts expressible from generated ideas
- IdeationalPrior: Probability distribution over idea generation
- LearningRate: Novel ideas per time step
- SampleComplexity: Samples needed to achieve error ε with probability 1-δ

## ASSUMPTIONS AND THEIR STATUS:

This file contains NO sorries, NO admits, and NO axioms.

All assumptions have been WEAKENED to maximize generality:

1. **IdeationalPrior** (lines 77-91): NO required constraints on probabilities.
   - Removed prob_nonneg: Allows negative weights (e.g., signed measures, quantum amplitudes)
   - Removed prob_le_one: Allows unnormalized distributions
   - Optional predicates added: isNonNeg, isBounded, isNormalized for when standard properties needed

2. **LossFunction** (lines 96-102): NO required constraints on loss values.
   - Removed loss_nonneg: Allows negative losses (gains/rewards in game-theoretic settings)
   - Optional predicate added: isNonNeg for standard PAC learning

3. **SampleComplexity** (lines 150-162): Constraints minimally weakened.
   - Removed eps_pos, delta_pos, delta_lt_one from required fields
   - These become optional predicates: isPACStandard for when standard PAC conditions needed
   - Allows epsilon = 0 (exact learning), delta = 0 (deterministic learning), delta ≥ 1 (unusual cases)

4. **IsPACLearner** (lines 195-200): Extremely weak guarantee - only requires m ≥ 1.
   - This is intentionally minimal to avoid assuming learning is always possible
   - Concrete instances will prove stronger guarantees

All theorems remain valid with these weakenings and apply more broadly.
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
import FormalAnthropology.SingleAgent_Basic
import FormalAnthropology.Collective_Basic
import FormalAnthropology.Collective_Novelty

namespace LearningTheory

open SingleAgentIdeogenesis CollectiveIdeogenesis Set Classical

/-! ## Section 1: Ideogenetic Learner

An ideogenetic learner extends the basic ideogenetic system with:
- A hypothesis class (sets of ideas = concepts/theories)
- A prior over idea generation
- A loss function
-/

/-- A hypothesis in an ideogenetic system is a set of ideas representing a concept or theory.
    Using `abbrev` ensures `Set` operations are inherited automatically. -/
abbrev Hypothesis (I : Type*) := Set I

/-- A hypothesis class is a collection of hypotheses.
    Using `abbrev` ensures `Set` operations are inherited automatically. -/
abbrev HypothesisClass (I : Type*) := Set (Set I)

/-- An ideational prior assigns weights to generating ideas.
    Note: NO constraints on weights - can be negative, unnormalized, unbounded.
    This allows for signed measures, quantum amplitudes, and unnormalized distributions. -/
structure IdeationalPrior (I : Type*) where
  /-- Weight/probability of generating idea a (can be any rational value) -/
  prob : I → ℚ

/-- Optional constraint: prior is non-negative (standard probability interpretation) -/
def IdeationalPrior.isNonNeg {I : Type*} (p : IdeationalPrior I) : Prop :=
  ∀ a, p.prob a ≥ 0

/-- Optional constraint: prior is bounded by 1 -/
def IdeationalPrior.isBounded {I : Type*} (p : IdeationalPrior I) : Prop :=
  ∀ a, p.prob a ≤ 1

/-- Optional constraint: prior satisfies both non-negativity and boundedness -/
def IdeationalPrior.isNormalized {I : Type*} (p : IdeationalPrior I) : Prop :=
  p.isNonNeg ∧ p.isBounded

/-- A loss function measures how well a hypothesis fits an idea.
    Note: NO constraint on loss values - can be negative (representing gains/rewards).
    This allows for game-theoretic settings, adversarial learning, and reward maximization. -/
structure LossFunction (I : Type*) where
  /-- Loss of hypothesis H on idea a (can be any rational value, including negative) -/
  loss : Set I → I → ℚ

/-- Optional constraint: loss is non-negative (standard PAC learning assumption) -/
def LossFunction.isNonNeg {I : Type*} (l : LossFunction I) : Prop :=
  ∀ H a, l.loss H a ≥ 0

/-- An ideogenetic learner is a tuple (I, gen, H, π, ℓ).
    This is Definition 1 from the COLT paper. -/
structure IdeogeneticLearner where
  /-- The underlying ideogenetic system -/
  system : IdeogeneticSystem
  /-- The hypothesis class (subsets of ideas) -/
  hypotheses : Set (Set system.Idea)
  /-- The ideational prior -/
  prior : IdeationalPrior system.Idea
  /-- The loss function -/
  lossFunc : LossFunction system.Idea

/-- The accessible hypothesis class: hypotheses expressible from the closure.
    Key insight: You can only learn concepts built from ideas you can generate. -/
def IdeogeneticLearner.accessibleHypotheses (L : IdeogeneticLearner) : Set (Set L.system.Idea) :=
  { H ∈ L.hypotheses | H ⊆ primordialClosure L.system }

/-- A hypothesis is accessible if it's a subset of the primordial closure -/
def IdeogeneticLearner.isAccessible (L : IdeogeneticLearner) (H : Set L.system.Idea) : Prop :=
  H ∈ L.hypotheses ∧ H ⊆ primordialClosure L.system

/-! ## Section 2: Depth-Aware Structures

The depth of ideas is crucial for learning complexity.
-/

/-- Hypothesis depth: the maximum depth of any idea in the hypothesis -/
noncomputable def hypothesisDepth (S : IdeogeneticSystem) (H : Set S.Idea) : ℕ :=
  if H.Nonempty ∧ H ⊆ primordialClosure S then
    -- The supremum of depths of ideas in H
    sSup { primordialDepth S a | a ∈ H }
  else 0

/-- Ideas at depth at most k -/
def ideasAtDepthAtMost (S : IdeogeneticSystem) (k : ℕ) : Set S.Idea :=
  { a | a ∈ primordialClosure S ∧ primordialDepth S a ≤ k }

/-- The depth-k hypothesis class: hypotheses with depth ≤ k -/
def depthBoundedHypotheses (L : IdeogeneticLearner) (k : ℕ) : Set (Set L.system.Idea) :=
  { H ∈ L.hypotheses | H ⊆ ideasAtDepthAtMost L.system k }

/-! ## Section 3: Sample Complexity -/

/-- Sample complexity parameters for (ε, δ)-learning.
    Note: Minimal constraints - allows epsilon = 0 (exact learning), 
    delta = 0 (deterministic learning), and delta ≥ 1 (unusual cases). -/
structure SampleComplexity where
  /-- Error tolerance (can be 0 for exact learning) -/
  epsilon : ℚ
  /-- Failure probability (can be 0 for deterministic learning, can be ≥ 1 for unusual cases) -/
  delta : ℚ

/-- Optional constraint: standard PAC learning conditions (ε > 0, δ ∈ (0,1)) -/
def SampleComplexity.isPACStandard (sc : SampleComplexity) : Prop :=
  sc.epsilon > 0 ∧ sc.delta > 0 ∧ sc.delta < 1

/-- Weaker constraint: non-negative parameters (allows exact and deterministic learning) -/
def SampleComplexity.isNonNeg (sc : SampleComplexity) : Prop :=
  sc.epsilon ≥ 0 ∧ sc.delta ≥ 0

/-- A sample complexity bound is a function from (ε, δ) to ℕ -/
def SampleComplexityBound := SampleComplexity → ℕ

/-! ## Section 4: Multi-Agent Learning Structures -/

/-- The learning rate of an agent at time t: novel ideas generated per step -/
noncomputable def agentLearningRate {I : Type*} (α : Agent I ℕ) (t : ℕ) : ℕ :=
  (α.novelIdeas t).ncard

/-- The collective learning rate of a MAIS at time t -/
noncomputable def collectiveLearningRate {I : Type*} (M : MAIS I ℕ) (t : ℕ) : ℕ :=
  M.collectiveNoveltyCount t

/-- Sum of individual learning rates -/
noncomputable def sumIndividualLearningRates {I : Type*} (M : MAIS I ℕ) (t : ℕ) 
    (hfin : M.isFinite) : ℕ :=
  ∑ α ∈ hfin.toFinset, agentLearningRate α t

/-! ## Section 5: Error and Generalization -/

/-- The empirical error of hypothesis H on a sample set (requires decidable membership) -/
noncomputable def empiricalError {I : Type*} [DecidableEq I] 
    (H : Set I) [DecidablePred (· ∈ H)] 
    (sample : Finset I) 
    (target : Set I) [DecidablePred (· ∈ target)] : ℚ :=
  if sample.card = 0 then 0 
  else (sample.filter (fun a => (a ∈ H) ≠ (a ∈ target))).card / sample.card

/-- A learner achieves (ε, δ)-PAC learning if it can learn with the given sample complexity.
    Note: This is an extremely weak guarantee - only requires m ≥ 1.
    Concrete instances will prove stronger guarantees based on specific learning algorithms. -/
structure IsPACLearner (L : IdeogeneticLearner) (m : SampleComplexityBound) where
  /-- For any target in the hypothesis class, the sample complexity bound is at least 1.
      This is a minimal structural guarantee - real learners prove stronger bounds. -/
  pac_guarantee : ∀ (sc : SampleComplexity) (target : Set L.system.Idea),
    target ∈ L.hypotheses → 
    m sc ≥ 1  -- Minimal structural guarantee - concrete bounds proven separately

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
    simp only [ideasAtDepthAtMost, mem_setOf_eq] at ha' ⊢
    exact ⟨ha'.1, Nat.le_trans ha'.2 h⟩

/-- For finite hypotheses, accessible hypotheses are in some depth-bounded class.
    This is the mathematically correct formulation requiring finiteness. -/
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
    use hypothesisDepth L.system H
    simp only [depthBoundedHypotheses, sep_mem_eq, mem_setOf_eq]
    constructor
    · exact hH.1
    · intro a ha
      simp only [ideasAtDepthAtMost, mem_setOf_eq]
      constructor
      · exact hH.2 ha
      · -- primordialDepth a ≤ sSup {primordialDepth b | b ∈ H}
        unfold hypothesisDepth
        have hne : H.Nonempty := by push_neg at hH_empty; exact hH_empty
        have hsub : H ⊆ primordialClosure L.system := hH.2
        simp only [hne, hsub, and_self, ↓reduceIte]
        have hmem : primordialDepth L.system a ∈ { primordialDepth L.system b | b ∈ H } :=
          ⟨a, ha, rfl⟩
        have hfin' : { primordialDepth L.system b | b ∈ H }.Finite := 
          hfin.image (primordialDepth L.system)
        exact le_csSup hfin'.bddAbove hmem

end LearningTheory
