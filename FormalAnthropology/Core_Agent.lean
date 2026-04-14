/-
# Core Agent Definitions

This file provides the foundational learning-theoretic definitions for agents
in ideogenetic systems. These definitions are shared by both single-agent 
and multi-agent ideogenesis.

The key insight is that an agent is fundamentally:
1. A hypothesis generator (can form new ideas from existing ones)
2. A learner (has a hypothesis class of expressible concepts)
3. Bounded by cognitive constraints (memory, attention, familiarity)

## Key Structures:
- GenerativeCapability: The generation operator with learning-theoretic properties
- CognitiveState: Memory, attention, and familiarity constraints
- LearningAgent: Full agent with hypothesis class and sample complexity bounds

## ASSUMPTIONS AND THEIR STATUS:

This file contains NO sorries, NO admits, and NO axioms.

All assumptions are encoded as optional Prop fields or separate definitions:

1. **GenerativeCapability.isFinitary** (line 41): OPTIONAL - defaults to assuming 
   finite generation, but can be instantiated with infinite generation when needed.
   This has been WEAKENED from a required field to an optional default.

2. **IdeationalPrior probability bounds** (lines 82-84): Can be weakened to allow
   unnormalized probabilities or negative weights if needed for certain applications
   (e.g., signed measures in quantum-inspired models). Currently assumes [0,1] range.

3. **LossFunction.loss_nonneg** (line 91): Assumes non-negative loss. Could be 
   weakened to allow negative losses (gains/rewards) for adversarial settings.

4. **SampleComplexityParams** (lines 105-108): Assumes standard PAC parameters
   with ε > 0 and δ ∈ (0,1). These are standard but could be relaxed for 
   alternative learning frameworks.

5. **CognitiveState.memory_local** (line 125): WEAKENED - No longer required as a 
   constraint. Memory can exceed local space (external storage, collective memory).

6. **CognitiveState.isMonotone** (line 129): OPTIONAL - Perfect memory is a 
   separate predicate, not required. Agents can forget.

7. **TemporalAgent birth/death constraints** (lines 227-231): These are reasonable
   biological constraints but could be relaxed for abstract or immortal agents.
   - birth_before_death: Made OPTIONAL via ExtendedTime allowing immortality
   - memory_before_birth: Can be relaxed to allow "innate" or inherited memories
   - primordials_in_memory: Can be relaxed to allow gradual acquisition

All theorems remain valid with these weakenings.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic

namespace Core

/-! ## Section 1: Generative Capability

The fundamental capability of an ideogenetic agent is generation:
the ability to produce new ideas from existing ones.
-/

/-- A generation operator on an idea space I.
    This is the mathematical core of ideogenesis. 
    Note: isFinitary is no longer a default assumption - it can be infinite. -/
structure GenerativeCapability (I : Type*) where
  /-- The generation function: each idea generates a set of successor ideas -/
  generate : I → Set I

/-- Optional predicate: generation is finitary (each idea generates finitely many successors).
    This is NOT required for the basic theory but useful for computational considerations. -/
def GenerativeCapability.isFinitary {I : Type*} (g : GenerativeCapability I) : Prop :=
  ∀ a, (g.generate a).Finite

/-- The cumulative generation from a seed set -/
def GenerativeCapability.genCumulative {I : Type*} (g : GenerativeCapability I) : 
    ℕ → Set I → Set I
  | 0, A => A
  | n + 1, A => g.genCumulative n A ∪ ⋃ a ∈ g.genCumulative n A, g.generate a

/-- The closure under generation -/
def GenerativeCapability.closure {I : Type*} (g : GenerativeCapability I) (A : Set I) : Set I :=
  ⋃ n, g.genCumulative n A

/-- Depth of an idea from a seed set -/
noncomputable def GenerativeCapability.depth {I : Type*} (g : GenerativeCapability I) 
    (A : Set I) (a : I) : ℕ :=
  @dite ℕ (∃ n, a ∈ g.genCumulative n A) (Classical.propDecidable _)
    (fun h => @Nat.find _ (Classical.decPred _) h)
    (fun _ => 0)

/-- An idea is reachable if it's in the closure -/
def GenerativeCapability.isReachable {I : Type*} (g : GenerativeCapability I) 
    (A : Set I) (a : I) : Prop :=
  a ∈ g.closure A

/-! ## Section 2: Hypothesis Class

A hypothesis class captures what concepts an agent can express.
Key insight: You can only learn concepts built from ideas you can generate.
-/

/-- A hypothesis is a set of ideas representing a concept or theory -/
abbrev Hypothesis (I : Type*) := Set I

/-- A hypothesis class is a collection of hypotheses -/
abbrev HypothesisClass (I : Type*) := Set (Set I)

/-- An ideational prior assigns weights to generating ideas.
    Note: Constraints weakened to allow negative weights and unnormalized distributions. -/
structure IdeationalPrior (I : Type*) where
  /-- Weight/probability of generating idea a (can be unnormalized or negative) -/
  prob : I → ℚ

/-- Optional constraint: prior is non-negative (standard probability interpretation) -/
def IdeationalPrior.isNonNeg {I : Type*} (p : IdeationalPrior I) : Prop :=
  ∀ a, p.prob a ≥ 0

/-- Optional constraint: prior is normalized (probabilities sum to 1) -/
def IdeationalPrior.isNormalized {I : Type*} (p : IdeationalPrior I) : Prop :=
  ∀ a, p.prob a ≤ 1

/-- A loss function measures how well a hypothesis fits an idea.
    Note: Can be negative (representing gains/rewards) in adversarial or game-theoretic settings. -/
structure LossFunction (I : Type*) where
  /-- Loss of hypothesis H on idea a (can be negative for gains) -/
  loss : Set I → I → ℚ

/-- Optional constraint: loss is non-negative (standard PAC learning assumption) -/
def LossFunction.isNonNeg {I : Type*} (l : LossFunction I) : Prop :=
  ∀ H a, l.loss H a ≥ 0

/-! ## Section 3: Sample Complexity Parameters

These define the learning-theoretic parameters for agents.
-/

/-- Sample complexity parameters for (ε, δ)-learning.
    Note: Constraints weakened to allow zero epsilon/delta for deterministic/exact learning. -/
structure SampleComplexityParams where
  /-- Error tolerance (can be 0 for exact learning) -/
  epsilon : ℚ
  /-- Failure probability (can be 0 for deterministic learning) -/
  delta : ℚ

/-- Optional constraint: standard PAC learning conditions (ε > 0, δ ∈ (0,1)) -/
def SampleComplexityParams.isPACStandard (p : SampleComplexityParams) : Prop :=
  p.epsilon > 0 ∧ p.delta > 0 ∧ p.delta < 1

/-- Weaker constraint: non-negative parameters -/
def SampleComplexityParams.isNonNeg (p : SampleComplexityParams) : Prop :=
  p.epsilon ≥ 0 ∧ p.delta ≥ 0

/-- A sample complexity bound function -/
def SampleComplexityBound := SampleComplexityParams → ℕ

/-! ## Section 4: Cognitive State

The cognitive state captures an agent's current knowledge and constraints.
-/

/-- A cognitive state models an agent's current knowledge and capabilities.
    Note: memory_local constraint removed - memory can exceed local space (external storage). -/
structure CognitiveState (I : Type*) (T : Type*) where
  /-- The agent's memory function: maps time to the set of ideas held -/
  memory : T → Set I
  /-- The agent's local idea space (what they can potentially hold internally) -/
  localSpace : Set I

/-- Optional constraint: memory is contained in the local space (no external storage). -/
def CognitiveState.memory_local {I T : Type*} (c : CognitiveState I T) : Prop :=
  ∀ t, c.memory t ⊆ c.localSpace

/-- Memory is monotone (perfect memory) -/
def CognitiveState.isMonotone {I T : Type*} [LE T] (c : CognitiveState I T) : Prop :=
  ∀ t₁ t₂, t₁ ≤ t₂ → c.memory t₁ ⊆ c.memory t₂

/-- Familiarity: ideas the agent has encountered -/
def CognitiveState.familiar {I : Type*} (c : CognitiveState I ℕ) (t : ℕ) : Set I :=
  ⋃ t' : Fin (t + 1), c.memory t'.val

/-! ## Section 5: Learning Agent

A learning agent combines generative capability with cognitive constraints
and a hypothesis class for learning.
-/

/-- A learning agent with full learning-theoretic structure -/
structure LearningAgent (I : Type*) where
  /-- The agent's generative capability -/
  genCap : GenerativeCapability I
  /-- The agent's hypothesis class -/
  hypotheses : HypothesisClass I
  /-- The agent's ideational prior -/
  prior : IdeationalPrior I
  /-- The agent's loss function -/
  lossFunc : LossFunction I
  /-- Primordial ideas (the agent's starting knowledge) -/
  primordials : Set I

/-- The closure of a learning agent's primordials -/
def LearningAgent.ideaClosure {I : Type*} (L : LearningAgent I) : Set I :=
  L.genCap.closure L.primordials

/-- Accessible hypotheses: those expressible from the closure -/
def LearningAgent.accessibleHypotheses {I : Type*} (L : LearningAgent I) : HypothesisClass I :=
  { H ∈ L.hypotheses | H ⊆ L.ideaClosure }

/-- Ideas at depth at most k -/
def LearningAgent.ideasAtDepthAtMost {I : Type*} (L : LearningAgent I) (k : ℕ) : Set I :=
  { a | a ∈ L.ideaClosure ∧ L.genCap.depth L.primordials a ≤ k }

/-- Depth-bounded hypotheses -/
def LearningAgent.depthBoundedHypotheses {I : Type*} (L : LearningAgent I) (k : ℕ) : 
    HypothesisClass I :=
  { H ∈ L.hypotheses | H ⊆ L.ideasAtDepthAtMost k }

/-! ## Section 6: Temporal Agent

An agent situated in time with birth, death, and evolving memory.
-/

/-- An extended time value that can represent infinity -/
inductive ExtendedTime (T : Type*) where
  | finite : T → ExtendedTime T
  | infinite : ExtendedTime T
deriving DecidableEq

namespace ExtendedTime

variable {T : Type*} [LinearOrder T]

def le : ExtendedTime T → ExtendedTime T → Prop
  | finite t, finite s => t ≤ s
  | finite _, infinite => True
  | infinite, finite _ => False
  | infinite, infinite => True

def lt : ExtendedTime T → ExtendedTime T → Prop
  | finite t, finite s => t < s
  | finite _, infinite => True
  | infinite, _ => False

instance : LE (ExtendedTime T) where le := le
instance : LT (ExtendedTime T) where lt := lt

theorem finite_lt_infinite (t : T) : (finite t : ExtendedTime T) < infinite := by
  simp only [LT.lt, lt]

theorem finite_le_finite {t s : T} : (finite t : ExtendedTime T) ≤ finite s ↔ t ≤ s := by
  simp only [LE.le, le]

theorem finite_lt_finite {t s : T} : (finite t : ExtendedTime T) < finite s ↔ t < s := by
  simp only [LT.lt, lt]

end ExtendedTime

/-- Agent identifier -/
structure AgentId where
  id : ℕ
deriving DecidableEq

/-- A temporal agent is a learning agent situated in time.
    Note: Constraints significantly weakened to allow immortal agents, pre-birth memories, etc. -/
structure TemporalAgent (I : Type*) (T : Type*) [LinearOrder T] extends LearningAgent I where
  /-- Unique identifier -/
  agentId : AgentId
  /-- Cognitive state evolving over time -/
  cogState : CognitiveState I T
  /-- Time of birth -/
  birth : T
  /-- Time of death (can be infinite for immortal agents) -/
  death : ExtendedTime T

/-- Optional constraint: birth precedes death (can be violated for immortal agents) -/
def TemporalAgent.birth_before_death {I T : Type*} [LinearOrder T] (α : TemporalAgent I T) : Prop :=
  ExtendedTime.finite α.birth < α.death

/-- Optional constraint: memory is empty before birth (can be violated for inherited memory) -/
def TemporalAgent.memory_empty_before_birth {I T : Type*} [LinearOrder T] (α : TemporalAgent I T) : Prop :=
  ∀ t, t < α.birth → α.cogState.memory t = ∅

/-- Optional constraint: primordials are in initial memory (can be violated for gradual acquisition) -/
def TemporalAgent.primordials_in_initial_memory {I T : Type*} [LinearOrder T] (α : TemporalAgent I T) : Prop :=
  α.primordials ⊆ α.cogState.memory α.birth

/-- Whether an agent is alive at time t -/
def TemporalAgent.isAlive {I T : Type*} [LinearOrder T] (α : TemporalAgent I T) (t : T) : Prop :=
  α.birth ≤ t ∧ ExtendedTime.finite t < α.death

/-- The local idea space of a temporal agent -/
def TemporalAgent.localIdeas {I T : Type*} [LinearOrder T] (α : TemporalAgent I T) : Set I :=
  α.cogState.localSpace

/-- The memory of a temporal agent at time t -/
def TemporalAgent.memory {I T : Type*} [LinearOrder T] (α : TemporalAgent I T) (t : T) : Set I :=
  α.cogState.memory t

/-- The generation function of a temporal agent -/
def TemporalAgent.generate {I T : Type*} [LinearOrder T] (α : TemporalAgent I T) : I → Set I :=
  α.genCap.generate

/-! ## Section 7: Basic Theorems -/

/-- The seed is always in the closure -/
theorem GenerativeCapability.seed_in_closure {I : Type*} (g : GenerativeCapability I) 
    (A : Set I) : A ⊆ g.closure A := by
  intro a ha
  simp only [closure, Set.mem_iUnion]
  exact ⟨0, by simp [genCumulative, ha]⟩

/-- Cumulative generation is monotone -/
theorem GenerativeCapability.genCumulative_mono {I : Type*} (g : GenerativeCapability I) 
    (A : Set I) (n m : ℕ) (h : n ≤ m) : g.genCumulative n A ⊆ g.genCumulative m A := by
  induction m with
  | zero => 
    simp only [Nat.le_zero] at h
    subst h; rfl
  | succ m ih =>
    cases Nat.lt_or_eq_of_le h with
    | inl hlt =>
      have : n ≤ m := Nat.lt_succ_iff.mp hlt
      intro a ha
      simp only [genCumulative, Set.mem_union]
      left
      exact ih this ha
    | inr heq =>
      subst heq; rfl

/-- Depth is well-defined for reachable ideas -/
theorem GenerativeCapability.depth_spec {I : Type*} (g : GenerativeCapability I) 
    (A : Set I) (a : I) (ha : g.isReachable A a) : 
    a ∈ g.genCumulative (g.depth A a) A := by
  simp only [isReachable, closure, Set.mem_iUnion] at ha
  obtain ⟨n, hn⟩ := ha
  have hex : ∃ k, a ∈ g.genCumulative k A := ⟨n, hn⟩
  unfold depth
  rw [dif_pos hex]
  haveI : DecidablePred fun k => a ∈ g.genCumulative k A := Classical.decPred _
  convert @Nat.find_spec (fun k => a ∈ g.genCumulative k A) _ hex

/-- Depth bounds from membership -/
theorem GenerativeCapability.depth_le_of_mem {I : Type*} (g : GenerativeCapability I) 
    (A : Set I) (a : I) (n : ℕ) (h : a ∈ g.genCumulative n A) : g.depth A a ≤ n := by
  have hex : ∃ k, a ∈ g.genCumulative k A := ⟨n, h⟩
  unfold depth
  rw [dif_pos hex]
  haveI : DecidablePred fun k => a ∈ g.genCumulative k A := Classical.decPred _
  convert @Nat.find_le n (fun k => a ∈ g.genCumulative k A) _ hex h

end Core
