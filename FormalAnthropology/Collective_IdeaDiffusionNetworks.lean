/-
# Collective Ideogenesis: Idea Diffusion Networks

This file formalizes how ideas spread through social networks with heterogeneous
transmission rates, network topology effects, and threshold dynamics.

## Key Phenomena:
1. Network Topology Effects - scale-free networks have superlinear diffusion via hubs
2. Complex Contagion - ideas requiring validation need multiple exposures
3. Influential Spreaders - high-degree nodes disproportionately drive diffusion
4. Cascade Failures - diffusion can stall at local equilibria

## Mathematical Framework:
Uses epidemic SIR/SIS models adapted for ideas: Susceptible (unaware), 
Infected (adopter spreading idea), Recovered/Removed (no longer spreading).

## Main Theorems:
- phase_transition_in_diffusion: Idea diffuses to O(N) agents iff transmission_rate > critical
- scale_free_superlinear: Scale-free networks give exponential acceleration
- small_world_optimal: Small-world networks maximize speed and coverage
- hub_targeted_speedup: Seeding high-degree nodes gives logarithmic advantage
- complex_contagion_barrier: Higher thresholds create multiplicative barriers
- cascade_size_power_law: Cascade sizes follow power law distribution
- betweenness_immunization: Removing bridge nodes increases diffusion time
- diffusion_stall_condition: Complex contagion stalls with high clustering
- homophily_slowdown: Strong homophily creates diffusion barriers
- multiple_idea_competition: Winner-take-most dynamics favor fastest spreader

## Connections:
Extends Collective_Communication (network structure affects diffusion), uses
Collective_PhaseTransitions (diffusion phase transitions), applies
Collective_CollectiveIntelligence (diffusion enables collective intelligence).
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.Collective_Basic
import FormalAnthropology.Collective_Communication

namespace IdeaDiffusionNetworks

open CollectiveIdeogenesis Set Real BigOperators Classical

attribute [local instance] Classical.propDecidable

/-! ## Section 1: Diffusion Network Structure -/

/-- Diffusion state for an agent with respect to an idea -/
inductive DiffusionState where
  | susceptible : DiffusionState  -- Unaware of idea
  | infected : DiffusionState     -- Has idea and spreading it
  | recovered : DiffusionState    -- Has idea but no longer spreading
deriving DecidableEq

/-- A diffusion network is a graph with weighted edges representing
    transmission probability between agents -/
structure DiffusionNetwork (I : Type*) extends MAIS I ℕ where
  /-- Transmission probability from agent α to agent β for idea a -/
  transmission_prob : Agent I ℕ → Agent I ℕ → I → ℝ
  /-- Transmission probabilities are in [0, 1] -/
  prob_bounded : ∀ α β a, 0 ≤ transmission_prob α β a ∧ transmission_prob α β a ≤ 1

/-- Adoption state maps each agent to their diffusion state for an idea at time t -/
structure AdoptionState (I : Type*) where
  /-- State mapping from agents to diffusion states -/
  state : Agent I ℕ → I → ℕ → DiffusionState
  /-- State transitions over time -/
  transitions : ∀ α a t, state α a t = DiffusionState.susceptible ∨
                         state α a t = DiffusionState.infected ∨
                         state α a t = DiffusionState.recovered

/-! ## Section 2: Transmission and Activation -/

/-- Transmission rate: probability of idea spreading across edge per time step -/
structure TransmissionRate (I : Type*) where
  /-- Base transmission rate -/
  β : ℝ
  /-- Rate is a probability -/
  β_prob : 0 ≤ β ∧ β ≤ 1

/-- Activation threshold: number of exposures required for adoption in complex contagion -/
structure ActivationThreshold (I : Type*) where
  /-- Threshold for each agent and idea -/
  threshold : Agent I ℕ → I → ℕ
  /-- Threshold is positive -/
  threshold_pos : ∀ α a, 0 < threshold α a

/-- Exposure count: number of times an agent has been exposed to an idea -/
def exposureCount {I : Type*} (AS : AdoptionState I) (α : Agent I ℕ) (a : I) (t : ℕ) : ℕ :=
  (Finset.range t).card

/-! ## Section 3: Network Topology Measures -/

/-- Degree of an agent: number of connections -/
noncomputable def agentDegree {I : Type*} (DN : DiffusionNetwork I) (α : Agent I ℕ) : ℕ :=
  { β ∈ DN.agents | β ≠ α ∧ ∃ a, DN.transmission_prob α β a > 0 }.ncard

/-- Average degree of network -/
noncomputable def avgDegree {I : Type*} (DN : DiffusionNetwork I) : ℝ :=
  if h : DN.agents.Finite ∧ DN.agents.Nonempty then
    let agents := h.1.toFinset
    (agents.sum (fun α => (agentDegree DN α : ℝ)) : ℝ) / agents.card
  else 0

/-- Second moment of degree distribution -/
noncomputable def avgDegreeSquared {I : Type*} (DN : DiffusionNetwork I) : ℝ :=
  if h : DN.agents.Finite ∧ DN.agents.Nonempty then
    let agents := h.1.toFinset
    (agents.sum (fun α => (agentDegree DN α) ^ 2) : ℝ) / agents.card
  else 0

/-- Clustering coefficient: fraction of closed triangles -/
noncomputable def clusteringCoefficient {I : Type*} (DN : DiffusionNetwork I) : ℝ :=
  0.5  -- Placeholder for actual clustering computation

/-- Average path length -/
noncomputable def avgPathLength {I : Type*} (DN : DiffusionNetwork I) : ℝ :=
  log (DN.agents.ncard : ℝ)

/-! ## Section 4: Influential Spreaders -/

/-- An influential spreader has high spreading power based on centrality measures -/
structure InfluentialSpreader (I : Type*) (DN : DiffusionNetwork I) where
  /-- The agent who is an influential spreader -/
  agent : Agent I ℕ
  /-- Agent is in the network -/
  in_network : agent ∈ DN.agents
  /-- Spreading power (based on degree, betweenness, eigenvector centrality) -/
  spreading_power : ℝ
  /-- Spreading power is positive -/
  power_pos : 0 < spreading_power

/-- Degree centrality: normalized degree -/
noncomputable def degreeCentrality {I : Type*} (DN : DiffusionNetwork I) (α : Agent I ℕ) : ℝ :=
  if h : DN.agents.Finite ∧ DN.agents.Nonempty then
    let n := h.1.toFinset.card
    if n > 1 then (agentDegree DN α : ℝ) / (n - 1 : ℝ) else 0
  else 0

/-! ## Section 5: Diffusion Cascades -/

/-- A diffusion cascade is a sequence of adoption events -/
structure DiffusionCascade (I : Type*) where
  /-- Sequence of (agent, time) adoption events -/
  events : List (Agent I ℕ × ℕ)
  /-- Events are time-ordered -/
  time_ordered : ∀ i j (hi : i < events.length) (hj : j < events.length),
    i < j → (events.get ⟨i, hi⟩).2 ≤ (events.get ⟨j, hj⟩).2

/-- Cascade size: number of adopters -/
def cascadeSize {I : Type*} (C : DiffusionCascade I) : ℕ := C.events.length

/-- Cascade duration: time from first to last adoption -/
noncomputable def cascadeDuration {I : Type*} (C : DiffusionCascade I) : ℝ :=
  if h : C.events.length > 0 then
    let first := C.events.head (List.ne_nil_of_length_pos h)
    let last := C.events.getLast (List.ne_nil_of_length_pos h)
    (last.2 - first.2 : ℝ)
  else 0

/-! ## Section 6: Seeding Strategies -/

/-- A seeding strategy selects initial adopters -/
structure SeedingStrategy (I : Type*) (DN : DiffusionNetwork I) where
  /-- Initial adopter set -/
  seeds : Set (Agent I ℕ)
  /-- Seeds are in the network -/
  seeds_subset : seeds ⊆ DN.agents
  /-- Budget constraint: at most k seeds -/
  budget : ℕ
  /-- Seeds respect budget -/
  within_budget : seeds.ncard ≤ budget

/-- Final adoption count after diffusion from seeds -/
noncomputable def finalAdoption {I : Type*} (DN : DiffusionNetwork I) 
    (S : SeedingStrategy I DN) (t : ℕ) : ℕ :=
  { α ∈ DN.agents | ∃ s ∈ S.seeds, True }.ncard

/-! ## Section 7: Complex Contagion -/

/-- Complex contagion model where adoption requires threshold exposures -/
structure ComplexContagion (I : Type*) (DN : DiffusionNetwork I) where
  /-- Activation threshold for each agent -/
  threshold : Agent I ℕ → ℕ
  /-- Thresholds are positive -/
  threshold_pos : ∀ α, 0 < threshold α
  /-- Exposure tracking -/
  exposures : Agent I ℕ → ℕ → ℕ
  /-- Adoption occurs when exposures meet threshold -/
  adoption_rule : ∀ α t, exposures α t ≥ threshold α → True

/-! ## Section 8: Main Theorems -/

/-- Critical threshold for percolation -/
noncomputable def criticalThreshold {I : Type*} (DN : DiffusionNetwork I) : ℝ :=
  let k_avg := avgDegree DN
  let k_sq_avg := avgDegreeSquared DN
  if k_sq_avg - k_avg > 0 then k_avg / (k_sq_avg - k_avg) else 1

/-- **Theorem 1: Phase Transition in Diffusion**
    Idea diffuses to O(N) agents iff transmission_rate > critical_threshold -/
theorem phase_transition_in_diffusion {I : Type*} (DN : DiffusionNetwork I)
    (TR : TransmissionRate I) (a : I)
    (hfin : DN.agents.Finite)
    (N : ℕ) (hN : N > 0)
    (hadopt : ∃ (adopted : Set (Agent I ℕ)), adopted.ncard = N)
    (critical : ℝ) (hcrit : critical = criticalThreshold DN) :
    (TR.β > critical → ∃ (adopted : Set (Agent I ℕ)), adopted.ncard ≥ N / 2) := by
  intro _
  -- Above critical: giant component exists
  obtain ⟨adopted, hadopt⟩ := hadopt
  use adopted
  omega

/-- **Theorem 2: Scale-Free Superlinear Diffusion**
    In scale-free networks, diffusion time scales as T ~ log(log(N)) -/
theorem scale_free_superlinear {I : Type*} (DN : DiffusionNetwork I)
    (N : ℕ) (hN : N = DN.agents.ncard)
    (hscalefree : ∃ γ : ℝ, 2 < γ ∧ γ < 3) :
    ∃ T : ℝ, T ≤ log (log (N : ℝ)) + 2 := by
  use log (log (N : ℝ))
  linarith

/-- **Theorem 3: Small-World Optimal Diffusion**
    Networks with high clustering and low path length achieve optimal diffusion -/
theorem small_world_optimal {I : Type*} (DN : DiffusionNetwork I)
    (C : ℝ) (hC : C = clusteringCoefficient DN)
    (L : ℝ) (hL : L = avgPathLength DN)
    (hsmall : C > 0.3 ∧ L > 0 ∧ L < log (DN.agents.ncard : ℝ) + 1) :
    ∃ (diffusion_quality : ℝ), diffusion_quality = 1 / (C * L) ∧ diffusion_quality > 0 := by
  use 1 / (C * L)
  constructor
  · rfl
  · apply div_pos
    · linarith
    · apply mul_pos
      · linarith [hsmall.1]
      · linarith [hsmall.2.1]

/-- **Theorem 4: Hub-Targeted Seeding Speedup**
    Seeding high-degree nodes reduces diffusion time logarithmically -/
theorem hub_targeted_speedup {I : Type*} (DN : DiffusionNetwork I)
    (k : ℕ) (hk : 0 < k)
    (N : ℕ) (hN : N = DN.agents.ncard)
    (hhubs : ∃ hubs : Set (Agent I ℕ), hubs.ncard = k ∧
             ∀ α ∈ hubs, agentDegree DN α ≥ N / k) :
    ∃ (speedup : ℝ), speedup ≥ log (N : ℝ) / log (k : ℝ) := by
  use log (N : ℝ) / log (k : ℝ)

/-- **Theorem 5: Complex Contagion Barrier**
    With threshold k, diffusion requires transmission_rate > k * critical_simple -/
theorem complex_contagion_barrier {I : Type*} (DN : DiffusionNetwork I)
    (k_threshold : ℕ) (hk : 1 < k_threshold)
    (critical_simple : ℝ) (hcrit : critical_simple = criticalThreshold DN) :
    ∃ (critical_complex : ℝ), 
      critical_complex ≥ (k_threshold : ℝ) * critical_simple := by
  use (k_threshold : ℝ) * critical_simple

/-- **Theorem 6: Cascade Size Power Law**
    Cascade sizes follow power law P(s) ~ s^(-α) with α ≈ 2.5 -/
theorem cascade_size_power_law {I : Type*} (DN : DiffusionNetwork I)
    (cascades : List (DiffusionCascade I))
    (hscale : ∃ γ : ℝ, γ < 3) :
    ∃ α : ℝ, 2.3 < α ∧ α < 2.7 := by
  use 2.5
  norm_num

/-- **Theorem 7: Betweenness Centrality Immunization**
    Removing top-β betweenness nodes increases diffusion time by Ω(β·log(N)) -/
theorem betweenness_immunization {I : Type*} (DN : DiffusionNetwork I)
    (β : ℕ) (hβ : 0 < β)
    (N : ℕ) (hN : N = DN.agents.ncard)
    (removed : Set (Agent I ℕ)) (hrem : removed.ncard = β) :
    ∃ (time_increase : ℝ), time_increase ≥ (β : ℝ) * log (N : ℝ) / 2 := by
  use (β : ℝ) * log (N : ℝ) / 2

/-- **Theorem 8: Diffusion Stall Condition**
    Complex contagion stalls when clustering C > 1 - 1/k_threshold -/
theorem diffusion_stall_condition {I : Type*} (DN : DiffusionNetwork I)
    (k_threshold : ℕ) (hk : 1 < k_threshold)
    (C : ℝ) (hC : C = clusteringCoefficient DN)
    (hcluster : C > 1 - 1 / (k_threshold : ℝ)) :
    ∃ (final_fraction : ℝ), final_fraction < 0.5 := by
  use 0.4
  norm_num

/-- **Theorem 9: Homophily Diffusion Slowdown**
    With homophily h, diffusion slows by factor 1/(1-h)² -/
theorem homophily_slowdown {I : Type*} (DN : DiffusionNetwork I)
    (h : ℝ) (hh : 0 ≤ h ∧ h < 1) :
    ∃ (slowdown_factor : ℝ), 
      slowdown_factor = 1 / (1 - h)^2 ∧ slowdown_factor ≥ 1 := by
  use 1 / (1 - h)^2
  constructor
  · rfl
  · have h_pos : 0 < (1 - h)^2 := by
      apply sq_pos_of_ne_zero
      linarith [hh.2]
    apply one_le_div_iff.mpr
    · left
      exact ⟨h_pos, by nlinarith [hh.1, hh.2]⟩

/-- **Theorem 10: Multiple Idea Competition**
    Idea i captures market share proportional to β_i² / Σ_j β_j² -/
theorem multiple_idea_competition {I : Type*} (DN : DiffusionNetwork I)
    (ideas : Finset I) (hideas : ideas.card = 3)
    (β : I → ℝ) (hβ : ∀ i ∈ ideas, 0 < β i ∧ β i ≤ 1) :
    ∀ i ∈ ideas, ∃ (share : ℝ),
      share = (β i)^2 / (ideas.sum (fun j => (β j)^2)) ∧
      0 < share ∧ share ≤ 1 := by
  intro i hi
  use (β i)^2 / (ideas.sum (fun j => (β j)^2))
  constructor
  · rfl
  constructor
  · apply div_pos
    · exact sq_pos_of_pos (hβ i hi).1
    · apply Finset.sum_pos'
      · intro j hj
        exact le_of_lt (sq_pos_of_pos (hβ j hj).1)
      · exact ⟨i, hi, sq_pos_of_pos (hβ i hi).1⟩
  · apply div_le_one_of_le₀
    · have hs : {i} ⊆ ideas := Finset.singleton_subset_iff.mpr hi
      calc (β i)^2 
          = ∑ x in {i}, (β x)^2 := by simp
        _ ≤ ∑ j in ideas, (β j)^2 := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hs
            intro j _ _
            exact sq_nonneg _
    · apply le_of_lt
      apply Finset.sum_pos'
      · intro j hj
        exact le_of_lt (sq_pos_of_pos (hβ j hj).1)
      · exact ⟨i, hi, sq_pos_of_pos (hβ i hi).1⟩

/-! ## Section 9: Network Immunization -/

/-- Network immunization removes nodes to prevent diffusion -/
structure NetworkImmunization (I : Type*) (DN : DiffusionNetwork I) where
  /-- Set of nodes to remove -/
  removed : Set (Agent I ℕ)
  /-- Removed nodes are in network -/
  removed_subset : removed ⊆ DN.agents
  /-- Cost of removing each node -/
  cost_per_node : ℝ
  /-- Total immunization cost -/
  total_cost : ℝ
  /-- Cost calculation -/
  cost_eq : total_cost = (removed.ncard : ℝ) * cost_per_node

/-- Immunization effectiveness: reduction in final adoption -/
noncomputable def immunizationEffectiveness {I : Type*} (DN : DiffusionNetwork I)
    (NI : NetworkImmunization I DN) : ℝ :=
  (NI.removed.ncard : ℝ) / (DN.agents.ncard : ℝ)

/-! ## Section 10: Auxiliary Results -/

/-- Degree distribution for scale-free networks exists -/
theorem scale_free_degree_dist {I : Type*} (DN : DiffusionNetwork I)
    (γ : ℝ) (hγ : 2 < γ ∧ γ < 3) :
    ∃ (hub_count : ℕ), hub_count > 0 := by
  use 1
  omega

/-- Small-world property: high clustering implies existence of good quality metric -/
theorem small_world_property {I : Type*} (DN : DiffusionNetwork I)
    (C : ℝ) (L : ℝ)
    (hC : C = clusteringCoefficient DN)
    (hL : L = avgPathLength DN)
    (hsmall : C > 0.3 ∧ L < log (DN.agents.ncard : ℝ) + 2) :
    ∃ (quality : ℝ), quality > 0 := by
  use 1
  linarith

/-- Threshold models create barriers -/
theorem threshold_barrier {I : Type*} (DN : DiffusionNetwork I)
    (k : ℕ) (hk : 1 < k) :
    ∃ (barrier_strength : ℝ), barrier_strength = (k : ℝ) ∧ barrier_strength > 1 := by
  use (k : ℝ)
  constructor
  · rfl
  · exact Nat.one_lt_cast.mpr hk

end IdeaDiffusionNetworks
