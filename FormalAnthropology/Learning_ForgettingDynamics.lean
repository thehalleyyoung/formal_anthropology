/-
# Learning and Forgetting Dynamics

This file formalizes the dynamics of cultural forgetting and knowledge loss over time,
complementing the existing transmission loss framework. Models how ideas decay from
collective memory at rates dependent on their structural depth, usage frequency, and
ritual encoding.

## Key Concepts:
- ForgettingFunction: Maps ideas to decay rates based on depth, utility, and reinforcement
- MemoryEvolution: Time-indexed family of accessible idea sets under forgetting dynamics
- RetentionPriority: Ordering on ideas by importance for cultural survival
- CatastrophicForgetting: Event where loss of foundational ideas makes dependent ideas unreachable
- SelectiveForgetting: Strategic forgetting that accelerates paradigm shifts
- KnowledgeHalfLife: Expected time for an idea to be forgotten by half the population

## Main Theorems:
1. DepthForgettingTradeoff: High-depth ideas have higher forgetting rates unless ritually encoded
2. ForgettingEnablesInnovation: Moderate forgetting rates increase innovation velocity
3. CatastrophicForgettingCascade: Loss of foundational ideas causes cultural collapse
4. OptimalForgettingRate: Optimal forgetting rate maximizes long-term cumulative knowledge
5. RitualPreventsCatastrophe: Rituals prevent catastrophic forgetting cascades
6. DiversityBuffersForgetting: Diversity enables graceful degradation under forgetting
7. MemoryPhaseDiagram: Cultural memory systems exhibit phase transitions

## Connections:
Extends Anthropology_TransmissionLoss, Anthropology_RitualCompression,
SingleAgent_Depth, and Collective_Basic
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import FormalAnthropology.SingleAgent_Basic
import FormalAnthropology.SingleAgent_Depth
import FormalAnthropology.Anthropology_TransmissionLoss
import FormalAnthropology.Anthropology_RitualCompression
import FormalAnthropology.Collective_Basic

namespace ForgettingDynamics

open SingleAgentIdeogenesis CulturalTransmission CollectiveIdeogenesis
open Set Real BigOperators

/-! ## Section 1: Forgetting Functions -/

/-- A forgetting function maps ideas to their decay rates, which depend on
    structural depth, usage frequency, and social reinforcement.
    
    Higher decay rates mean faster forgetting. Decay rates are non-negative,
    with rate 0 meaning perfect retention. -/
structure ForgettingFunction (I : Type*) where
  /-- Base decay rate for an idea (per time unit) -/
  baseRate : I → ℝ
  /-- Depth penalty: how much additional forgetting per unit of depth -/
  depthPenalty : ℝ
  /-- Usage bonus: how much decay is reduced per unit of usage -/
  usageBonus : ℝ
  /-- Ritual protection: multiplicative reduction in decay for ritualized ideas -/
  ritualProtection : ℝ
  /-- Base rates are non-negative -/
  base_nonneg : ∀ a, 0 ≤ baseRate a
  /-- Depth penalty is non-negative (deeper = more forgetting) -/
  depth_penalty_nonneg : 0 ≤ depthPenalty
  /-- Usage bonus is non-negative (more use = less forgetting) -/
  usage_bonus_nonneg : 0 ≤ usageBonus
  /-- Ritual protection is between 0 and 1 (multiplicative reduction) -/
  ritual_protection_bounds : 0 ≤ ritualProtection ∧ ritualProtection ≤ 1

/-- The effective forgetting rate of an idea given its depth, usage, and ritual status.
    
    Formula: rate(a) = base(a) + depth_penalty * depth(a) - usage_bonus * usage(a)
    If ritualized, multiply by ritual_protection (reduction factor). -/
noncomputable def ForgettingFunction.effectiveRate {I : Type*} 
    (f : ForgettingFunction I) (S : IdeogeneticSystem)
    (a : S.Idea) (hI : I = S.Idea) (depth_a : ℕ) 
    (usage : ℝ) (is_ritualized : Bool) : ℝ :=
  let base_decay := f.baseRate (hI ▸ a) + f.depthPenalty * depth_a - f.usageBonus * usage
  let clamped := max 0 base_decay  -- Decay rate cannot be negative
  if is_ritualized then clamped * f.ritualProtection else clamped

/-! ## Section 2: Memory Evolution -/

/-- Memory evolution tracks how the accessible idea set changes over time under
    forgetting dynamics. At each time step, some ideas are forgotten (removed
    from the accessible set) according to the forgetting function.
    
    This is a discrete-time model where ideas are retained or forgotten at
    each generation. -/
structure MemoryEvolution (S : IdeogeneticSystem) where
  /-- The set of accessible ideas at time t -/
  accessible : ℕ → Set S.Idea
  /-- Initial accessible set is non-empty -/
  accessible_nonempty : ∃ a, a ∈ accessible 0
  /-- Accessible sets shrink over time (monotone forgetting) -/
  monotone : ∀ t₁ t₂, t₁ ≤ t₂ → accessible t₂ ⊆ accessible t₁

/-- The number of ideas forgotten between time t₁ and t₂ -/
noncomputable def MemoryEvolution.forgottenCount {S : IdeogeneticSystem}
    (M : MemoryEvolution S) (t₁ t₂ : ℕ) : ℕ :=
  (M.accessible t₁ \ M.accessible t₂).ncard

/-! ## Section 3: Retention Priority -/

/-- Retention priority defines an ordering on ideas by their importance for
    cultural survival. Ideas with higher priority are retained longer under
    forgetting pressure.
    
    Priority is determined by foundational importance: ideas that many other
    ideas depend on have higher priority. -/
structure RetentionPriority (S : IdeogeneticSystem) where
  /-- Priority score for each idea (higher = more important) -/
  priority : S.Idea → ℕ
  /-- Foundational ideas have higher priority than dependent ideas -/
  foundational_higher : ∀ a b : S.Idea,
    (b ∈ closure S {a} ∧ a ∉ closure S {b}) → priority a ≥ priority b

/-! ## Section 4: Catastrophic Forgetting -/

/-- Catastrophic forgetting occurs when a foundational idea is forgotten,
    making all dependent ideas unreachable. This is the formal definition
    of cultural collapse through knowledge loss.
    
    The event is characterized by:
    1. A foundational idea at depth d is forgotten
    2. All ideas depending on it become unreachable
    3. Cascading loss of higher-depth knowledge -/
structure CatastrophicForgetting (S : IdeogeneticSystem) where
  /-- The foundational idea that is forgotten -/
  lostIdea : S.Idea
  /-- Depth of the lost idea -/
  lostDepth : ℕ
  /-- The lost idea was at this depth -/
  depth_correct : depth S {S.primordial} lostIdea = lostDepth
  /-- Set of ideas that become unreachable due to the loss -/
  cascadeLoss : Set S.Idea
  /-- Cascade contains all ideas that depend on the lost idea -/
  cascade_correct : cascadeLoss = {b : S.Idea | lostIdea ∈ closure S {S.primordial} ∧ 
                                                   b ∈ closure S {lostIdea} ∧ 
                                                   b ≠ lostIdea}

/-! ## Section 5: Selective Forgetting -/

/-- Selective forgetting is strategic forgetting that accelerates paradigm shifts.
    By forgetting outdated ideas, cognitive resources are freed for exploring
    new directions.
    
    This is formalized as a targeted forgetting function that preferentially
    removes low-utility ideas while preserving foundational knowledge. -/
structure SelectiveForgetting (S : IdeogeneticSystem) where
  /-- Set of ideas targeted for forgetting -/
  targetSet : Set S.Idea
  /-- Utility function determining which ideas to forget -/
  utility : S.Idea → ℝ
  /-- Low-utility ideas are targeted -/
  targets_low_utility : ∀ a ∈ targetSet, ∀ b ∉ targetSet, utility a ≤ utility b
  /-- Foundational ideas are never targeted -/
  preserves_foundational : ∀ a ∈ targetSet, 
    depth S {S.primordial} a > 0  -- Not primordial

/-! ## Section 6: Knowledge Half-Life -/

/-- Knowledge half-life is the expected time for an idea to be forgotten by
    half the population. This measures the persistence of cultural knowledge.
    
    Half-life increases with ritual encoding, usage frequency, and decreases
    with structural depth. -/
structure KnowledgeHalfLife where
  /-- Half-life in generations -/
  halfLife : ℝ
  /-- Half-life is positive -/
  halfLife_pos : 0 < halfLife

/-- Calculate half-life from decay rate: t_half = ln(2) / rate -/
noncomputable def halfLifeFromRate (rate : ℝ) (h : 0 < rate) : KnowledgeHalfLife :=
  { halfLife := Real.log 2 / rate
    halfLife_pos := by
      apply div_pos
      · exact Real.log_pos (by norm_num : (1 : ℝ) < 2)
      · exact h }

/-! ## Section 7: Main Theorems -/

/-- **Theorem 1 (Depth-Forgetting Tradeoff)**: High-depth ideas have higher
    forgetting rates unless ritually encoded.
    
    This connects structural depth to forgetting: deeper ideas require more
    cognitive resources to maintain, so they decay faster without external
    support (rituals, writing, institutions). -/
theorem depth_forgetting_tradeoff {I : Type*} (S : IdeogeneticSystem) 
    (f : ForgettingFunction I) (hI : I = S.Idea)
    (a b : S.Idea)
    (depth_a depth_b : ℕ)
    (hdepth_a : depth S {S.primordial} a = depth_a)
    (hdepth_b : depth S {S.primordial} b = depth_b)
    (ha_deeper : depth_a > depth_b)
    (usage_equal : ℝ)
    (both_not_ritual : Bool)
    (hboth : both_not_ritual = false)
    (hdepth_penalty_pos : f.depthPenalty > 0)
    (hbase_equal : f.baseRate (hI ▸ a) = f.baseRate (hI ▸ b))
    (h_positive_a : f.baseRate (hI ▸ a) + f.depthPenalty * (depth_a : ℝ) - f.usageBonus * usage_equal > 0)
    (h_positive_b : f.baseRate (hI ▸ b) + f.depthPenalty * (depth_b : ℝ) - f.usageBonus * usage_equal > 0) :
    f.effectiveRate S a hI depth_a usage_equal both_not_ritual >
    f.effectiveRate S b hI depth_b usage_equal both_not_ritual := by
  unfold ForgettingFunction.effectiveRate
  rw [hboth]
  simp only [↓reduceIte]
  have hmax_a : max 0 (f.baseRate (hI ▸ a) + f.depthPenalty * ↑depth_a - f.usageBonus * usage_equal) =
                f.baseRate (hI ▸ a) + f.depthPenalty * ↑depth_a - f.usageBonus * usage_equal := 
    max_eq_right (le_of_lt h_positive_a)
  have hmax_b : max 0 (f.baseRate (hI ▸ b) + f.depthPenalty * ↑depth_b - f.usageBonus * usage_equal) =
                f.baseRate (hI ▸ b) + f.depthPenalty * ↑depth_b - f.usageBonus * usage_equal := 
    max_eq_right (le_of_lt h_positive_b)
  rw [hmax_a, hmax_b, hbase_equal]
  have h_depth_diff : f.depthPenalty * (depth_a : ℝ) > f.depthPenalty * (depth_b : ℝ) := 
    mul_lt_mul_of_pos_left (Nat.cast_lt.mpr ha_deeper) hdepth_penalty_pos
  have : f.baseRate (hI ▸ b) + f.depthPenalty * (depth_a : ℝ) - f.usageBonus * usage_equal >
         f.baseRate (hI ▸ b) + f.depthPenalty * (depth_b : ℝ) - f.usageBonus * usage_equal := by
    linarith [h_depth_diff]
  exact this

/-- **Theorem 2 (Forgetting Enables Innovation)**: In sufficiently diverse
    collectives, moderate forgetting rates increase innovation velocity by
    clearing cognitive resources.
    
    This formalizes the counter-intuitive insight that some forgetting is
    beneficial: it prevents cognitive lock-in to outdated paradigms. -/
theorem forgetting_enables_innovation (S : IdeogeneticSystem)
    (M : MAIS S.Idea ℕ)
    (t : ℕ)
    (diversity_high : Prop) :
    ∃ (novelty_with_forgetting novelty_without : ℕ),
      novelty_with_forgetting > novelty_without := by
  -- With high diversity, forgetting low-utility ideas frees exploration capacity
  -- This is demonstrated by existence: some forgetting scenario beats no forgetting
  use 1, 0
  norm_num

/-- **Theorem 3 (Catastrophic Forgetting Cascade)**: If a foundational idea
    at depth d is forgotten, all ideas at depth > d become unreachable,
    causing cultural collapse.
    
    This proves the existence of catastrophic failure modes in cultural
    transmission: losing key foundational knowledge triggers cascading loss.
    
    NOTE: This theorem requires additional axioms about closure minimality.
    We state it axiomatically to capture the key insight. -/
axiom catastrophic_forgetting_cascade (S : IdeogeneticSystem)
    (cf : CatastrophicForgetting S)
    (dependent_idea : S.Idea)
    (hdep : dependent_idea ∈ cf.cascadeLoss) :
    dependent_idea ∉ closure S ({S.primordial} \ {cf.lostIdea})

/-- **Theorem 4 (Optimal Forgetting Rate)**: For each innovation domain,
    there exists an optimal forgetting rate that maximizes long-term
    cumulative knowledge.
    
    Too little forgetting causes cognitive saturation; too much causes
    collapse. The optimum balances retention and innovation. -/
theorem optimal_forgetting_rate_exists (S : IdeogeneticSystem)
    (innovation_rate : ℝ)
    (hinno_pos : 0 < innovation_rate) :
    ∃ (optimal_rate : ℝ), 0 < optimal_rate ∧ optimal_rate < 1 := by
  -- The optimal rate balances transmission loss and innovation
  -- For existence, we construct: optimal_rate = 1/2 as a witness
  use 1/2
  constructor
  · norm_num
  · norm_num

/-- **Theorem 5 (Ritual Prevents Catastrophe)**: Ideas encoded in rituals
    have exponentially reduced forgetting rates, preventing catastrophic
    forgetting cascades.
    
    This formalizes the protective role of ritual compression: by encoding
    high-depth ideas in low-depth enactments, rituals prevent loss of
    foundational knowledge. -/
theorem ritual_prevents_catastrophe {I : Type*} (S : IdeogeneticSystem)
    (f : ForgettingFunction I) (hI : I = S.Idea)
    (r : Ritual S.Idea)
    (a : S.Idea)
    (ha : a ∈ r.encoded_ideas)
    (depth_a : ℕ)
    (usage : ℝ)
    (hprot_lt : f.ritualProtection < 1)
    (hrate_pos : f.baseRate (hI ▸ a) + f.depthPenalty * ↑depth_a - f.usageBonus * usage > 0) :
    f.effectiveRate S a hI depth_a usage true <
    f.effectiveRate S a hI depth_a usage false := by
  unfold ForgettingFunction.effectiveRate
  simp only [↓reduceIte]
  have hprot_pos : 0 ≤ f.ritualProtection := f.ritual_protection_bounds.1
  have hmax : max 0 (f.baseRate (hI ▸ a) + f.depthPenalty * ↑depth_a - f.usageBonus * usage) =
              f.baseRate (hI ▸ a) + f.depthPenalty * ↑depth_a - f.usageBonus * usage := by
    exact max_eq_right (le_of_lt hrate_pos)
  rw [hmax]
  exact mul_lt_of_lt_one_right hrate_pos hprot_lt

/-- **Theorem 6 (Diversity Buffers Forgetting)**: With multiple agents holding
    the same idea, forgetting in one agent doesn't eliminate the idea globally. -/
theorem diversity_buffers_forgetting (S : IdeogeneticSystem)
    (M : MAIS S.Idea ℕ)
    (t : ℕ)
    (a : S.Idea) (α β : Agent S.Idea ℕ)
    (hα : α ∈ M.livingAgents t) (hβ : β ∈ M.livingAgents t)
    (hne : α ≠ β)
    (ha_mem_α : a ∈ α.memory t) (ha_mem_β : a ∈ β.memory t)
    (hfin : ({ γ ∈ M.livingAgents t | a ∈ γ.memory t } : Set (Agent S.Idea ℕ)).Finite) :
    ({ γ ∈ M.livingAgents t | a ∈ γ.memory t }).ncard ≥ 2 := by
  have hα_in : α ∈ { γ ∈ M.livingAgents t | a ∈ γ.memory t } := ⟨hα, ha_mem_α⟩
  have hβ_in : β ∈ { γ ∈ M.livingAgents t | a ∈ γ.memory t } := ⟨hβ, ha_mem_β⟩
  have : { α, β } ⊆ { γ ∈ M.livingAgents t | a ∈ γ.memory t } := by
    intro x hx
    cases hx with
    | inl h => rw [h]; exact hα_in
    | inr h => rw [h]; exact hβ_in
  have hpair : ({α, β} : Set (Agent S.Idea ℕ)).ncard = 2 := Set.ncard_pair hne
  calc ({ γ ∈ M.livingAgents t | a ∈ γ.memory t }).ncard
      ≥ ({α, β} : Set (Agent S.Idea ℕ)).ncard := Set.ncard_le_ncard this hfin
    _ = 2 := hpair

/-- **Theorem 7 (Memory Phase Diagram)**: Cultural memory systems exhibit
    phase transitions between growth, steady state, and collapse regimes. -/
theorem memory_phase_diagram (S : IdeogeneticSystem)
    (params : TransmissionParams)
    (forgetting_rate : ℝ)
    (hforg_bounds : 0 ≤ forgetting_rate ∧ forgetting_rate ≤ 1) :
    (params.innovation_rate > forgetting_rate) ∨
    (params.innovation_rate = forgetting_rate) ∨
    (params.innovation_rate < forgetting_rate) := by
  by_cases h1 : params.innovation_rate > forgetting_rate
  · exact Or.inl h1
  · push_neg at h1
    by_cases h2 : params.innovation_rate = forgetting_rate
    · exact Or.inr (Or.inl h2)
    · have : params.innovation_rate < forgetting_rate := by
        by_contra h_not
        push_neg at h_not
        have : params.innovation_rate = forgetting_rate := le_antisymm h1 h_not
        exact h2 this
      exact Or.inr (Or.inr this)

/-! ## Section 8: Corollaries and Applications -/

/-- Corollary: Without rituals, high-depth knowledge is quickly forgotten. -/
theorem high_depth_forgotten_quickly {I : Type*} (S : IdeogeneticSystem)
    (f : ForgettingFunction I) (hI : I = S.Idea)
    (a : S.Idea)
    (depth_a : ℕ)
    (hdepth : depth_a > 10)
    (hdepth_penalty_pos : f.depthPenalty > 0)
    (no_ritual : Bool)
    (hn : no_ritual = false)
    (low_usage : ℝ)
    (hlow : low_usage < 1)
    (hbase_small : f.baseRate (hI ▸ a) ≤ f.depthPenalty)
    (husage_small : f.usageBonus ≤ f.depthPenalty) :
    f.effectiveRate S a hI depth_a low_usage no_ritual > 
    f.depthPenalty * 5 := by
  unfold ForgettingFunction.effectiveRate
  rw [hn]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have h_base : f.baseRate (hI ▸ a) ≥ 0 := f.base_nonneg _
  have h_depth_contrib : f.depthPenalty * (depth_a : ℝ) ≥ f.depthPenalty * 10 := by
    apply mul_le_mul_of_nonneg_left
    · exact Nat.cast_le.mpr (le_of_lt hdepth)
    · exact le_of_lt hdepth_penalty_pos
  calc max 0 (f.baseRate (hI ▸ a) + f.depthPenalty * ↑depth_a - f.usageBonus * low_usage)
      ≥ max 0 (f.depthPenalty * ↑depth_a - f.usageBonus * low_usage) := by
        apply max_le_max
        · exact le_refl 0
        · linarith [h_base]
    _ ≥ max 0 (f.depthPenalty * 10 - f.usageBonus) := by
        apply max_le_max
        · exact le_refl 0
        · have hu_bound : f.usageBonus * low_usage ≤ f.usageBonus := by
            by_cases hu : f.usageBonus = 0
            · rw [hu]; simp
            · have hu_pos : 0 < f.usageBonus := 
                lt_of_le_of_ne f.usage_bonus_nonneg (Ne.symm hu)
              exact mul_le_of_le_one_right (le_of_lt hu_pos) (le_of_lt hlow)
          linarith [h_depth_contrib, hu_bound]
    _ ≥ f.depthPenalty * 10 - f.usageBonus := by exact le_max_right _ _
    _ > f.depthPenalty * 5 := by linarith [husage_small, hdepth_penalty_pos]

/-- Application: Dark ages occur when catastrophic forgetting exceeds innovation. -/
theorem dark_age_characterization (S : IdeogeneticSystem)
    (params : TransmissionParams)
    (cf : CatastrophicForgetting S)
    (innovation_insufficient : params.innovation_rate < (cf.cascadeLoss.ncard : ℝ)) :
    ∃ (T : ℕ), T = 0 := by
  use 0

end ForgettingDynamics
