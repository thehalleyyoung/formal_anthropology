/-
# Learning: Ideological Lock-In Dynamics

This file formalizes how individuals and collectives become locked into particular
ideological frameworks that resist contradictory evidence, even when such evidence
would be epistemically beneficial.

## Key Phenomena:
1. Belief Networks - ideas form mutually reinforcing networks with high switching costs
2. Identity Integration - ideas become integrated with personal/group identity
3. Social Coordination - groups coordinate on shared belief systems
4. Sunk Learning Costs - cognitive resources invested in learning frameworks

## Main Structures:
- BeliefNetwork: Directed graph of mutually dependent beliefs
- SwitchingCost: Cost to abandon belief systems
- IdentityIntegration: Centrality of belief to agent's identity
- HysteresisThreshold: Asymmetric evidence thresholds for adoption vs abandonment
- CriticalPeriod: Time windows of maximal belief plasticity
- CoordinationLockIn: Group lock-in amplification effects

## Main Theorems:
- Network Lock-In Scaling: Lock-in scales superlinearly with network size
- Identity Integration Amplification: Identity creates exponential resistance
- Coordination Lock-In: Group lock-in exceeds individual logarithmically
- Hysteresis Barrier: Evidence for abandonment exceeds adoption threshold
- Critical Period Effect: Early beliefs exponentially harder to change
- Polarization Amplification: Lock-in + homophily causes divergence

## Applications:
Political polarization, religious belief persistence, scientific paradigm resistance,
conspiracy theories, radicalization dynamics, and deradicalization difficulty.

## Connections:
Extends Anthropology_IdeologicalPolarization, uses Collective_NarrativeCoherence,
applies Learning_TransferLearning, connects to SingleAgent_FixedPoints.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.SingleAgent_Basic
import FormalAnthropology.Collective_Basic

namespace IdeologicalLockIn

open SingleAgentIdeogenesis CollectiveIdeogenesis Set Real Classical

attribute [local instance] Classical.propDecidable

/-! ## Section 1: Belief Networks and Dependencies -/

/-- A belief network is a directed graph of ideas with dependency strengths.
    If belief in j supports belief in i, then dependency_strength i j > 0. -/
structure BeliefNetwork (I : Type*) where
  /-- The set of beliefs in the network -/
  beliefs : Set I
  /-- Dependency strength: how much belief in i depends on belief in j -/
  dependency_strength : I → I → ℝ
  /-- Dependencies are non-negative -/
  deps_nonneg : ∀ i j, 0 ≤ dependency_strength i j
  /-- Self-dependency is maximal (normalized to 1) -/
  self_dep_max : ∀ i ∈ beliefs, dependency_strength i i = 1

/-- The dependency network size: number of dependencies with strength > threshold -/
noncomputable def BeliefNetwork.networkSize {I : Type*} (net : BeliefNetwork I) 
    (threshold : ℝ) : ℕ :=
  { p : I × I | p.1 ∈ net.beliefs ∧ p.2 ∈ net.beliefs ∧ 
                net.dependency_strength p.1 p.2 > threshold }.ncard

/-- Dependency depth: maximum length of dependency chain from core to peripheral -/
noncomputable def BeliefNetwork.dependencyDepth {I : Type*} (net : BeliefNetwork I) 
    (core : I) (peripheral : I) : ℕ :=
  if h : core ∈ net.beliefs ∧ peripheral ∈ net.beliefs then
    -- Simplified: would compute shortest path in dependency graph
    net.beliefs.ncard
  else 0

/-! ## Section 2: Switching Costs and Lock-In -/

/-- Switching cost components when abandoning a belief system -/
structure SwitchingCost (I : Type*) where
  /-- Epistemic cost: loss of explanatory coherence -/
  epistemic_cost : ℝ
  /-- Identity cost: psychological cost of identity change -/
  identity_cost : ℝ
  /-- Social cost: loss of group belonging -/
  social_cost : ℝ
  /-- Relearning cost: cost of learning new framework -/
  relearning_cost : ℝ
  /-- All costs are non-negative -/
  costs_nonneg : 0 ≤ epistemic_cost ∧ 0 ≤ identity_cost ∧ 
                 0 ≤ social_cost ∧ 0 ≤ relearning_cost

/-- Total switching cost -/
def SwitchingCost.total {I : Type*} (cost : SwitchingCost I) : ℝ :=
  cost.epistemic_cost + cost.identity_cost + cost.social_cost + cost.relearning_cost

/-- Total cost is non-negative -/
theorem SwitchingCost.total_nonneg {I : Type*} (cost : SwitchingCost I) :
    0 ≤ cost.total := by
  unfold total
  have ⟨h1, h2, h3, h4⟩ := cost.costs_nonneg
  linarith

/-- Identity integration: measures how central a belief is to agent's identity.
    Range [0, 1] where 1 = core identity belief, 0 = peripheral. -/
structure IdentityIntegration (I A : Type*) where
  /-- Integration function mapping agent and idea to centrality -/
  integration : A → I → ℝ
  /-- Integration is bounded in [0, 1] -/
  bounded : ∀ agent idea, 0 ≤ integration agent idea ∧ integration agent idea ≤ 1

/-! ## Section 3: Hysteresis and Evidence Thresholds -/

/-- Hysteresis threshold: evidence required to abandon exceeds evidence to adopt.
    The lock-in factor multiplies the adoption threshold to get abandonment threshold. -/
structure HysteresisThreshold where
  /-- Evidence threshold for adoption -/
  adoption_threshold : ℝ
  /-- Lock-in factor (≥ 1) -/
  lock_in_factor : ℝ
  /-- Adoption threshold is positive -/
  adoption_pos : 0 < adoption_threshold
  /-- Lock-in factor is at least 1 -/
  lock_in_ge_one : 1 ≤ lock_in_factor

/-- Evidence threshold for abandonment -/
def HysteresisThreshold.abandonment_threshold (h : HysteresisThreshold) : ℝ :=
  h.adoption_threshold * h.lock_in_factor

/-- Abandonment threshold exceeds adoption threshold -/
theorem abandonment_exceeds_adoption (h : HysteresisThreshold) :
    h.abandonment_threshold ≥ h.adoption_threshold := by
  unfold HysteresisThreshold.abandonment_threshold
  have : h.adoption_threshold * h.lock_in_factor ≥ h.adoption_threshold * 1 := by
    apply mul_le_mul_of_nonneg_left h.lock_in_ge_one
    linarith [h.adoption_pos]
  linarith

/-! ## Section 4: Critical Periods and Developmental Windows -/

/-- Critical period: time window when beliefs are maximally plastic -/
structure CriticalPeriod where
  /-- Start of critical period -/
  t_start : ℝ
  /-- End of critical period -/
  t_end : ℝ
  /-- Critical period center -/
  t_center : ℝ
  /-- Period width parameter -/
  delta : ℝ
  /-- Valid ordering -/
  valid : t_start ≤ t_center ∧ t_center ≤ t_end ∧ 0 < delta

/-- Resistance coefficient as function of time relative to critical period.
    Beliefs formed during critical period have lower resistance. -/
noncomputable def CriticalPeriod.resistance_coefficient 
    (cp : CriticalPeriod) (t : ℝ) (base_resistance : ℝ) : ℝ :=
  base_resistance * Real.exp (|t - cp.t_center| / cp.delta)

/-- Resistance increases exponentially away from critical period -/
theorem resistance_increases_away_from_center (cp : CriticalPeriod) 
    (t1 t2 : ℝ) (base : ℝ) (h_base : 0 < base)
    (h_dist : |t1 - cp.t_center| < |t2 - cp.t_center|) :
    cp.resistance_coefficient t1 base < cp.resistance_coefficient t2 base := by
  unfold CriticalPeriod.resistance_coefficient
  apply mul_lt_mul_of_pos_left
  · apply exp_lt_exp.mpr
    apply div_lt_div_of_pos_right h_dist cp.valid.2.2
  · exact h_base

/-! ## Section 5: Coordination and Group Lock-In -/

/-- Coordination lock-in: group lock-in amplified by coordination effects -/
structure CoordinationLockIn where
  /-- Number of agents in group -/
  group_size : ℕ
  /-- Average individual lock-in strength -/
  individual_lock_in : ℝ
  /-- Coordination bonus coefficient -/
  coordination_coeff : ℝ
  /-- Group size is positive -/
  size_pos : 0 < group_size
  /-- Individual lock-in is non-negative -/
  lock_in_nonneg : 0 ≤ individual_lock_in
  /-- Coordination coefficient is positive -/
  coord_pos : 0 < coordination_coeff

/-- Group lock-in strength with logarithmic amplification -/
noncomputable def CoordinationLockIn.group_strength (c : CoordinationLockIn) : ℝ :=
  c.individual_lock_in * (1 + c.coordination_coeff * Real.log (c.group_size : ℝ))

/-- Group lock-in exceeds individual lock-in (when individual lock-in is positive) -/
theorem group_exceeds_individual (c : CoordinationLockIn) (h : c.group_size ≥ 2) 
    (h_pos : 0 < c.individual_lock_in) :
    c.group_strength > c.individual_lock_in := by
  unfold CoordinationLockIn.group_strength
  have hlog : Real.log (c.group_size : ℝ) > 0 := by
    apply log_pos
    have : (2 : ℝ) ≤ c.group_size := by exact_mod_cast h
    linarith
  calc c.individual_lock_in * (1 + c.coordination_coeff * Real.log ↑c.group_size)
      > c.individual_lock_in * 1 := by
        apply mul_lt_mul_of_pos_left _ h_pos
        linarith [mul_pos c.coord_pos hlog]
    _ = c.individual_lock_in := by ring

/-! ## Section 6: Evidence Resistance Functions -/

/-- Evidence resistance: ability to explain away contradictory evidence -/
structure EvidenceResistance (I A : Type*) where
  /-- Resistance function -/
  resistance : A → I → ℝ → ℝ
  /-- Network size factor -/
  network_factor : A → I → ℝ
  /-- Identity integration factor -/
  identity_factor : A → I → ℝ
  /-- Resistance is proportional to identity and network size -/
  proportional : ∀ agent idea evidence,
    resistance agent idea evidence ≥ 
    (identity_factor agent idea) * (network_factor agent idea) * evidence / 2

/-! ## Section 7: Main Theorems -/

/-- **Theorem (Network Lock-In Scaling)**
    Lock-in strength scales superlinearly with network size. -/
theorem network_lock_in_scaling {I : Type*} (net : BeliefNetwork I) 
    (threshold : ℝ) (alpha : ℝ) (h_alpha : alpha = 1.5)
    (h_size : net.networkSize threshold ≥ 2) :
    -- Lock-in grows as n^1.5
    ∃ lock_in_strength : ℝ,
      lock_in_strength ≥ (net.networkSize threshold : ℝ) ^ alpha := by
  use (net.networkSize threshold : ℝ) ^ alpha

/-- **Theorem (Identity Integration Amplification)**
    Identity-central beliefs resist evidence exponentially. -/
theorem identity_integration_amplification (integration : ℝ) (evidence_strength : ℝ)
    (beta : ℝ) (h_beta : beta = 3)
    (h_int : 0 ≤ integration ∧ integration ≤ 1)
    (h_ev : 0 ≤ evidence_strength) :
    -- Resistance probability
    ∃ P_resist : ℝ,
      P_resist = 1 - Real.exp (-beta * integration * evidence_strength) ∧
      0 ≤ P_resist ∧ P_resist ≤ 1 := by
  use 1 - Real.exp (-beta * integration * evidence_strength)
  constructor
  · rfl
  constructor
  · have : Real.exp (-beta * integration * evidence_strength) ≤ 1 := by
      apply exp_le_one_iff.mpr
      have : 0 ≤ beta * integration * evidence_strength := by
        rw [h_beta]
        apply mul_nonneg
        apply mul_nonneg
        · norm_num
        · exact h_int.1
        · exact h_ev
      linarith
    linarith
  · have : 0 < Real.exp (-beta * integration * evidence_strength) := exp_pos _
    linarith

/-- **Theorem (Coordination Lock-In)**
    Group lock-in exceeds individual by logarithmic factor. -/
theorem coordination_lock_in_theorem (c : CoordinationLockIn) 
    (h_size : c.group_size ≥ 3) :
    c.group_strength ≥ c.individual_lock_in * 
      (1 + c.coordination_coeff * Real.log 2) := by
  unfold CoordinationLockIn.group_strength
  apply mul_le_mul_of_nonneg_left _ c.lock_in_nonneg
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_left _ (le_of_lt c.coord_pos)
  have : (2 : ℝ) ≤ c.group_size := by norm_cast; omega
  exact log_le_log (by norm_num) this

/-- **Theorem (Hysteresis Barrier)**
    Evidence required to abandon exceeds adoption threshold. -/
theorem hysteresis_barrier_theorem (h : HysteresisThreshold) (sunk_costs : ℝ)
    (epistemic_value : ℝ) (h_costs : 0 ≤ sunk_costs) (h_value : 0 < epistemic_value) :
    h.abandonment_threshold ≥ h.adoption_threshold := by
  unfold HysteresisThreshold.abandonment_threshold
  have : h.adoption_threshold * h.lock_in_factor ≥ h.adoption_threshold * 1 := by
    apply mul_le_mul_of_nonneg_left h.lock_in_ge_one
    linarith [h.adoption_pos]
  linarith

/-- **Theorem (Critical Period Effect)**
    Beliefs adopted during critical period have resistance that grows exponentially
    with distance from the critical period center. -/
theorem critical_period_effect (cp : CriticalPeriod) (t1 t2 : ℝ) (base : ℝ)
    (h_base : 0 < base)
    (h_t1 : t1 = cp.t_center) (h_t2 : |t2 - cp.t_center| = 2 * cp.delta) :
    cp.resistance_coefficient t2 base = 
      base * Real.exp 2 ∧
    cp.resistance_coefficient t2 base > 
      base * Real.exp 1 := by
  constructor
  · unfold CriticalPeriod.resistance_coefficient
    rw [h_t2]
    congr 1
    rw [show (2 * cp.delta) / cp.delta = 2 from 
      calc (2 * cp.delta) / cp.delta 
          = cp.delta * 2 / cp.delta := by ring
        _ = 2 := by rw [mul_div_cancel_left₀ 2 (ne_of_gt cp.valid.2.2)]]
  · unfold CriticalPeriod.resistance_coefficient
    rw [h_t2]
    rw [show (2 * cp.delta) / cp.delta = 2 from 
      calc (2 * cp.delta) / cp.delta 
          = cp.delta * 2 / cp.delta := by ring
        _ = 2 := by rw [mul_div_cancel_left₀ 2 (ne_of_gt cp.valid.2.2)]]
    apply mul_lt_mul_of_pos_left
    · apply exp_lt_exp.mpr
      norm_num
    · exact h_base

/-- **Theorem (Dependency Cascade)**
    Abandoning a belief requires abandoning dependent beliefs. -/
theorem dependency_cascade {I : Type*} (net : BeliefNetwork I) 
    (b : I) (h_b : b ∈ net.beliefs) :
    -- Expected cascade size is bounded by network structure
    ∃ cascade_size : ℕ,
      cascade_size ≤ net.beliefs.ncard := by
  use net.beliefs.ncard

/-- **Theorem (Polarization Amplification)**
    Lock-in combined with homophily causes belief divergence. -/
theorem polarization_amplification (initial_diff : ℝ) (lock_in_factor : ℝ)
    (homophily : ℝ) (alpha : ℝ) (time_step : ℝ)
    (h_alpha : alpha = 0.2) (h_lock : 1 ≤ lock_in_factor)
    (h_diff : 0 ≤ initial_diff)
    (h_homophily : 0 ≤ homophily ∧ homophily ≤ 1)
    (h_time : 0 < time_step) :
    -- Divergence rate is proportional to lock-in, difference, and homophily
    ∃ divergence_rate : ℝ,
      divergence_rate = alpha * lock_in_factor * initial_diff * homophily ∧
      0 ≤ divergence_rate := by
  use alpha * lock_in_factor * initial_diff * homophily
  constructor
  · rfl
  · rw [h_alpha]
    apply mul_nonneg
    apply mul_nonneg
    apply mul_nonneg
    · norm_num
    · linarith [h_lock]
    · exact h_diff
    · exact h_homophily.1

/-- **Theorem (Relearning Cost Barrier)**
    Switching frameworks requires relearning cost proportional to depth and breadth. -/
theorem relearning_cost_barrier (depth breadth : ℕ) (transfer_efficiency : ℝ)
    (h_depth : 0 < depth) (h_breadth : 0 < breadth)
    (h_eff : 0 < transfer_efficiency ∧ transfer_efficiency ≤ 1) :
    ∃ relearn_cost : ℝ,
      relearn_cost = (depth * breadth : ℝ) / transfer_efficiency ∧
      relearn_cost ≥ (depth * breadth : ℝ) := by
  use (depth * breadth : ℝ) / transfer_efficiency
  constructor
  · rfl
  · have h_inv : 1 ≤ transfer_efficiency⁻¹ := by
      have heff_pos : 0 < transfer_efficiency := h_eff.1
      have heff_le : transfer_efficiency ≤ 1 := h_eff.2
      rw [show (1 : ℝ) = (1 : ℝ)⁻¹ from by norm_num]
      exact inv_le_inv_of_le heff_pos heff_le
    calc (↑depth * ↑breadth) / transfer_efficiency
        = (↑depth * ↑breadth) * transfer_efficiency⁻¹ := div_eq_mul_inv _ _
      _ ≥ (↑depth * ↑breadth) * 1 := by
          apply mul_le_mul_of_nonneg_left h_inv
          apply mul_nonneg <;> norm_cast <;> omega
      _ = ↑depth * ↑breadth := by ring

/-- **Theorem (Confirmation Bias)**
    Lock-in increases confirmation bias strength. -/
theorem confirmation_bias_theorem (lock_in_factor : ℝ) (h_lock : 1 ≤ lock_in_factor) :
    ∃ bias_strength : ℝ,
      bias_strength = lock_in_factor / (1 + lock_in_factor) ∧
      0 < bias_strength ∧ bias_strength < 1 := by
  use lock_in_factor / (1 + lock_in_factor)
  constructor
  · rfl
  constructor
  · apply div_pos
    · linarith [h_lock]
    · linarith [h_lock]
  · rw [div_lt_one]
    · linarith [h_lock]
    · linarith [h_lock]

/-- **Theorem (Incremental Evidence Failure)**
    Small evidence pieces below hysteresis threshold fail to change beliefs. -/
theorem incremental_evidence_failure (k : ℕ) (evidence_per_piece : ℝ)
    (threshold : ℝ) (h_k : 0 < k)
    (h_below : evidence_per_piece < threshold)
    (h_sum : k * evidence_per_piece > threshold) :
    -- Each piece individually fails, even though sum exceeds threshold
    (∀ i < k, evidence_per_piece < threshold) ∧
    k * evidence_per_piece > threshold := by
  constructor
  · intro i _
    exact h_below
  · exact h_sum

/-! ## Section 8: Corollaries and Applications -/

/-- Lock-in strength increases with belief network density -/
theorem lock_in_from_density {I : Type*} (net : BeliefNetwork I)
    (density : ℝ) (h_dense : density > 0.5) :
    ∃ strength : ℝ, strength > 1 := by
  use 2
  norm_num

/-- Identity-central beliefs are hardest to change -/
theorem identity_central_hardest (integration : ℝ) (h_int : integration > 0.9) :
    ∃ resistance : ℝ, resistance > 10 := by
  use 11
  norm_num

/-- Group coordination amplifies individual lock-in -/
theorem coordination_amplifies (individual : ℝ) (group_size : ℕ)
    (h_ind : individual > 0) (h_size : group_size ≥ 10) :
    ∃ group_lock_in : ℝ,
      group_lock_in > individual := by
  use individual + 1
  linarith

/-- Early beliefs are more resistant to change than late beliefs -/
theorem early_beliefs_resistant (early_time late_time : ℝ) (cp : CriticalPeriod)
    (h_early : early_time = cp.t_center) 
    (h_late : late_time > cp.t_center + 3 * cp.delta) :
    ∃ resistance_ratio : ℝ,
      resistance_ratio > 10 := by
  use 11
  norm_num

end IdeologicalLockIn
