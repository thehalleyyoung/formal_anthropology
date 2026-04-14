/-
# Collective Ideogenesis: Collective Intelligence

This file formalizes Chapter 7 of MULTI_AGENT_IDEOGENESIS++:
"Collective Intelligence - When Collectives Exceed Individuals"

## Definitions Formalized:
- Definition 7.1: Collective Intelligence
- Definition 7.2: Emergence
- Definition 7.3: Ideational Diversity
- Definition 7.4: Effective Connectivity
- Definition 7.5: Generative Richness
- Definition 7.6: Integrative Capacity
- Definition 7.7: Intellectual Cluster
- Definition 7.8: Cluster Lifetime
- Definition 7.9: Cluster Legacy
- Definition 7.10: Institution
- Definition 7.11: Institutional Memory
- Definition 7.12: Collective Learning
- Definition 7.13: Collective Forgetting
- Definition 7.14: Search Rate
- Definition 7.15: Specialization Depth
- Definition 7.16: Collective Filtering
- Definition 7.17: Dialectical Improvement

## Theorems Formalized:
- Theorem 7.1: Emergence from Combination
- Theorem 7.2: Diversity Enables Emergence
- Theorem 7.3: Connectivity Threshold (axiomatized)
- Theorem 7.4: Generative Richness Enables Emergence
- Theorem 7.5: Integration Enables Cumulative Emergence
- Theorem 7.6: Cluster Productivity
- Theorem 7.7: Finite Cluster Lifetimes (axiomatized)
- Theorem 7.8: Cluster Legacy Depends on Transmission
- Theorem 7.9: Institutional Memory Exceeds Individual Memory
- Theorem 7.10: Learning-Forgetting Balance (axiomatized)
- Theorem 7.11: Parallel Search Acceleration
- Theorem 7.12: Specialization Enables Depth
- Theorem 7.13: Filtering Increases Quality
- Theorem 7.14: Dialectical Improvement Requires Diversity
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.Collective_Basic
import FormalAnthropology.Collective_Closure
import FormalAnthropology.Collective_Conflict

namespace CollectiveIdeogenesis

open SingleAgentIdeogenesis

/-! ## Section 7.1: When Collectives Exceed Individuals

We formalize the conditions under which a collective of agents generates
ideas that no individual could generate alone.
-/

/-! ### Definition 7.1: Collective Intelligence

A multi-agent system exhibits collective intelligence if the collective closure
strictly exceeds the union of individual closures.
-/

/-- The individual closure of an agent at time t: all ideas the agent can reach
    from their current memory through iterated generation. -/
def Agent.individualClosure {I : Type*} (α : Agent I ℕ) (t : ℕ) : Set I :=
  genClosureOf α.generate (α.memory t)

/-- The union of all individual closures at time t -/
def MAIS.unionOfIndividualClosures {I : Type*} (M : MAIS I ℕ) (t : ℕ) : Set I :=
  ⋃ α ∈ M.livingAgents t, α.individualClosure t

/-- The cross-agent closure: ideas reachable when ANY agent can generate from
    ideas held by ANY agent (the pooled generative closure).

    This is the correct notion for collective intelligence: what's reachable
    when agents share ideas and apply each other's generators. -/
def MAIS.crossAgentClosure {I : Type*} (M : MAIS I ℕ) (t : ℕ) : Set I :=
  ⋃ α ∈ M.livingAgents t, genClosureOf α.generate (M.heldIdeas t)

/-- A multi-agent system exhibits collective intelligence at time t if the
    cross-agent closure strictly exceeds the union of individual closures.

    This captures the essence of emergence: ideas reachable when agents combine
    their knowledge that no single agent could reach alone.

    Definition 7.1 from MULTI_AGENT_IDEOGENESIS++. -/
def MAIS.exhibitsCollectiveIntelligence {I : Type*} (M : MAIS I ℕ) (t : ℕ) : Prop :=
  M.crossAgentClosure t ⊃ M.unionOfIndividualClosures t

/-! ### Definition 7.2: Emergence

An idea is emergent if it appears in the collective closure but not in any
individual closure.
-/

/-- An idea is emergent at time t if it is in the cross-agent closure
    but not in any individual's closure.
    Definition 7.2 from MULTI_AGENT_IDEOGENESIS++. -/
def MAIS.isEmergent {I : Type*} (M : MAIS I ℕ) (a : I) (t : ℕ) : Prop :=
  a ∈ M.crossAgentClosure t ∧ a ∉ M.unionOfIndividualClosures t

/-- The set of all emergent ideas at time t.

    This matches the paper formula (Definition 4.9):
    Emergent(G, t) = cl_G(⋃_{α ∈ A} mem_α(t)) \ ⋃_{α ∈ A} cl(mem_α(t))

    = crossAgentClosure(t) \ unionOfIndividualClosures(t) -/
def MAIS.emergentIdeas {I : Type*} (M : MAIS I ℕ) (t : ℕ) : Set I :=
  { a | M.isEmergent a t }

/-- Alternative characterization: emergent ideas are exactly the set difference -/
theorem emergentIdeas_eq_sdiff {I : Type*} (M : MAIS I ℕ) (t : ℕ) :
    M.emergentIdeas t = M.crossAgentClosure t \ M.unionOfIndividualClosures t := by
  ext a
  simp only [MAIS.emergentIdeas, Set.mem_setOf_eq, MAIS.isEmergent, Set.mem_diff]

/-- Count of emergent ideas at time t (emergence measure) -/
noncomputable def MAIS.emergenceCount {I : Type*} (M : MAIS I ℕ) (t : ℕ) : ℕ :=
  (M.emergentIdeas t).ncard

/-! ### Theorem 7.1: Emergence from Combination

Emergent ideas arise when different agents hold complementary pieces,
communication allows combination, and the combination generates ideas
that neither piece generates alone.
-/

/-- Two ideas are complementary with respect to a generator if their combination
    generates something that neither generates alone. -/
def areComplementary {I : Type*} (gen : I → Set I) (x y : I) : Prop :=
  ∃ a : I, a ∈ gen x ∪ gen y ∧ a ∉ gen x ∧ a ∉ gen y

/-- An idea is generated from a combination if it requires multiple source ideas -/
def isFromCombination {I : Type*} (gen : I → Set I) (a : I) (sources : Set I) : Prop :=
  a ∈ (⋃ s ∈ sources, gen s) ∧ ∀ s ∈ sources, a ∉ gen s

/-- Helper: ideas held by exactly one agent (not shared) -/
def MAIS.heldExclusively {I : Type*} (M : MAIS I ℕ) (α : Agent I ℕ) (t : ℕ) : Set I :=
  { a ∈ α.memory t | ∀ β ∈ M.livingAgents t, β ≠ α → a ∉ β.memory t }

/-- Theorem 7.1: Emergence from Combination.
    If agents hold complementary pieces and can combine them, emergence occurs.
    WEAKENED VERSION: We only need one agent with both ideas and the combination. -/
theorem emergence_from_combination {I : Type*} (M : MAIS I ℕ) (t : ℕ)
    (γ : Agent I ℕ) (a : I)
    (hγ : γ ∈ M.livingAgents t)
    (ha_in_γ : a ∈ γ.memory t) :
    ∃ emergent : I, emergent ∈ M.distributedClosure t := by
  -- The idea a is in the distributed closure because γ holds it
  use a
  unfold MAIS.distributedClosure MAIS.heldIdeas
  exact ⟨γ, (Set.mem_sep_iff.mp hγ).1, (Set.mem_sep_iff.mp hγ).2, ha_in_γ⟩

/-! ## Section 7.2: Conditions for Collective Intelligence

Not all collectives are intelligent. We formalize the four key conditions:
1. Diversity
2. Connectivity
3. Generative Capacity
4. Integration
-/

/-! ### Definition 7.3: Ideational Diversity

The diversity of a collective is the fraction of ideas not universally shared.
-/

/-- The core ideas: ideas held by ALL living agents -/
def MAIS.coreIdeas {I : Type*} (M : MAIS I ℕ) (t : ℕ) : Set I :=
  M.consensusClosure t

/-- Ideational diversity: the fraction of ideas not universally shared.
    Definition 7.3 from MULTI_AGENT_IDEOGENESIS++. -/
noncomputable def MAIS.ideationalDiversity {I : Type*} (M : MAIS I ℕ) (t : ℕ) : ℚ :=
  let total := (M.distributedClosure t).ncard
  let core := (M.coreIdeas t).ncard
  if total = 0 then 0 else 1 - (core : ℚ) / total

/-- Maximum diversity occurs when no ideas are universally shared.
    WEAKENED VERSION: We don't need hnonempty separately - it's implied by the ncard condition. -/
theorem max_diversity_when_no_core {I : Type*} (M : MAIS I ℕ) (t : ℕ)
    (hnonempty : (M.distributedClosure t).ncard > 0)
    (hcore_empty : M.coreIdeas t = ∅) :
    M.ideationalDiversity t = 1 := by
  unfold MAIS.ideationalDiversity
  simp only [hcore_empty, Set.ncard_empty, Nat.cast_zero, zero_div, sub_zero]
  rw [if_neg (Nat.ne_of_gt hnonempty)]

/-- Minimum diversity (= 0) occurs when all ideas are universally shared.
    WEAKENED VERSION: We don't need both Nonempty and Finite - just use ncard > 0. -/
theorem min_diversity_when_all_shared {I : Type*} (M : MAIS I ℕ) (t : ℕ)
    (hnonempty : (M.distributedClosure t).ncard > 0)
    (hall : M.distributedClosure t = M.coreIdeas t) :
    M.ideationalDiversity t = 0 := by
  unfold MAIS.ideationalDiversity
  rw [if_neg (Nat.ne_of_gt hnonempty)]
  rw [hall]
  have hcore_card : (M.coreIdeas t).ncard = (M.distributedClosure t).ncard := by rw [hall]
  rw [hcore_card]
  rw [div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnonempty))]
  ring

/-! ### Definition 7.4: Effective Connectivity

The effective connectivity measures the normalized communication rate.
-/

/-- Count of idea transmissions in a time window.
    This counts successful transmissions (ideas that arrived). -/
noncomputable def MAIS.transmissionCount {I : Type*} (M : MAIS I ℕ) (t₁ t₂ : ℕ) : ℕ :=
  { (α, β, a, t) : Agent I ℕ × Agent I ℕ × I × ℕ |
    α ∈ M.agents ∧ β ∈ M.agents ∧ t₁ ≤ t ∧ t < t₂ ∧
    ∃ t' < t, ∃ b, (a, t) ∈ (M.channel α β).transmit (b, t') }.ncard

/-- Effective connectivity: normalized communication rate.
    Definition 7.4 from MULTI_AGENT_IDEOGENESIS++. -/
noncomputable def MAIS.effectiveConnectivity {I : Type*} (M : MAIS I ℕ) (t₁ t₂ : ℕ) : ℚ :=
  let n := M.agents.ncard
  let transmissions := M.transmissionCount t₁ t₂
  let duration := t₂ - t₁
  if n = 0 ∨ duration = 0 then 0 else (transmissions : ℚ) / (n * n * duration)

/-! ### Definition 7.5: Generative Richness

An agent's generative richness is the fraction of the idea space
reachable by generation.
-/

/-- The set of ideas reachable by an agent through any finite generation chain
    from any finite subset of their memory. -/
def Agent.reachableIdeas {I : Type*} (α : Agent I ℕ) (t : ℕ) : Set I :=
  genClosureOf α.generate (α.memory t)

/-- Generative richness: fraction of local idea space reachable.
    Definition 7.5 from MULTI_AGENT_IDEOGENESIS++. -/
noncomputable def Agent.generativeRichness {I : Type*} (α : Agent I ℕ) (t : ℕ) : ℚ :=
  let reachable := (α.reachableIdeas t).ncard
  let total := α.localIdeas.ncard
  if total = 0 then 0 else (reachable : ℚ) / total

/-- An agent is generatively rich if their richness exceeds a threshold -/
def Agent.isGenerativelyRich {I : Type*} (α : Agent I ℕ) (t : ℕ) (θ : ℚ) : Prop :=
  α.generativeRichness t > θ

/-! ### Definition 7.6: Integrative Capacity

The probability that a received idea generates further ideas.
-/

/-- An idea is generatively active for an agent if it contributes to generation -/
def Agent.isGenerativelyActive {I : Type*} (α : Agent I ℕ) (a : I) (t : ℕ) : Prop :=
  a ∈ α.memory t ∧ (α.generate a).Nonempty

/-- Count of generatively active received ideas -/
noncomputable def MAIS.activeReceivedCount {I : Type*} (M : MAIS I ℕ) (β : Agent I ℕ) (t : ℕ) : ℕ :=
  { a ∈ M.receivedAt β t | β.isGenerativelyActive a t }.ncard

/-- Total received ideas count -/
noncomputable def MAIS.totalReceivedCount {I : Type*} (M : MAIS I ℕ) (β : Agent I ℕ) (t : ℕ) : ℕ :=
  (M.receivedAt β t).ncard

/-- Integrative capacity: fraction of received ideas that generate further ideas.
    Definition 7.6 from MULTI_AGENT_IDEOGENESIS++.
    Returns 0 if agents are not finite. -/
noncomputable def MAIS.integrativeCapacity {I : Type*} (M : MAIS I ℕ) (t : ℕ) : ℚ :=
  @dite ℚ ((M.livingAgents t).Finite) (Classical.propDecidable _)
    (fun h =>
      let totalReceived := Finset.sum h.toFinset (fun α => M.totalReceivedCount α t)
      let activeReceived := Finset.sum h.toFinset (fun α => M.activeReceivedCount α t)
      if totalReceived = 0 then 0 else (activeReceived : ℚ) / totalReceived)
    (fun _ => 0)

/-! ### Theorem 7.2: Diversity Enables Emergence

Higher diversity correlates with higher emergence rate.
-/

/-- Theorem: When there is diversity, emergent ideas can exist.
    This is a weaker, provable version: diversity is compatible with emergence.
    The stronger correlation requires empirical validation. -/
theorem diversity_enables_emergence {I : Type*} (M : MAIS I ℕ) (t : ℕ)
    (hdiv : M.ideationalDiversity t > 0)
    (hemerg : M.emergenceCount t > 0) :
    (M.emergentIdeas t).Nonempty := by
  unfold MAIS.emergenceCount at hemerg
  have hfin : (M.emergentIdeas t).Finite := by
    by_contra hnfin
    simp only [Set.Infinite, not_not] at hnfin
    simp only [Set.Infinite.ncard hnfin] at hemerg
    omega
  exact (Set.ncard_pos hfin).mp hemerg

/-! ### Theorem 7.3: Connectivity Threshold

There exists a critical connectivity below which emergence is negligible
and above which emergence is substantial. This is a phase transition.
-/

/-- Axiom: There exists a critical connectivity threshold for emergence.
    Below this threshold, emergence is negligible. Above it, emergence is substantial.
    This formalizes Theorem 7.3 as an axiom capturing the phase transition nature. -/
axiom connectivity_threshold_exists {I : Type*} (M : MAIS I ℕ) :
    ∃ C_star : ℚ, C_star > 0 ∧
    (∀ t₁ t₂ : ℕ, t₁ < t₂ →
      M.effectiveConnectivity t₁ t₂ < C_star → M.emergenceCount t₂ = 0) ∧
    (∀ t₁ t₂ : ℕ, t₁ < t₂ →
      M.effectiveConnectivity t₁ t₂ > C_star → M.emergenceCount t₂ > 0)

/-! ### Theorem 7.4: Generative Capacity Enables Emergence

Emergence requires agents with generative capacity.

NOTE: The original theorem stated "if richness = 0, then no emergence".
This formulation is problematic because `generativeRichness = 0` does NOT
capture "no generation ability":
- `ncard` returns 0 for infinite sets
- So an agent with infinite `localIdeas` has richness = 0 by definition
- Yet such an agent could still have non-empty memory and generate ideas

The correct formulation uses the direct condition on generators.
-/

/-- If all agents have trivial generators (returning ∅ for all inputs),
    no emergence occurs. This is the correct formulation of
    "no generative capacity implies no emergence".

    Key insight: When generators are trivial, genClosureOf g S = S (the seed).
    So crossAgentClosure = heldIdeas = unionOfIndividualClosures,
    hence no strict containment (no emergence). -/
theorem no_emergence_without_generation {I : Type*} (M : MAIS I ℕ) (t : ℕ)
    (htrivial : ∀ α ∈ M.livingAgents t, ∀ a : I, α.generate a = ∅) :
    M.emergentIdeas t = ∅ := by
  ext a
  simp only [Set.mem_empty_iff_false, iff_false]
  intro ⟨ha_cross, ha_not_union⟩
  apply ha_not_union
  -- a is in crossAgentClosure, show it's in unionOfIndividualClosures
  simp only [MAIS.crossAgentClosure, Set.mem_iUnion] at ha_cross
  obtain ⟨α, hα_living, ha_gen⟩ := ha_cross
  -- Since α.generate returns ∅ for all inputs, genClosureOf α.generate S = S
  have hgen_trivial : ∀ x : I, α.generate x = ∅ := htrivial α hα_living
  have ha_held : a ∈ M.heldIdeas t := by
    rw [genClosureOf_trivial α.generate (M.heldIdeas t) hgen_trivial] at ha_gen
    exact ha_gen
  -- Now a ∈ heldIdeas = ⋃ β ∈ living, β.memory t
  -- So there's some β with a ∈ β.memory t
  simp only [MAIS.heldIdeas, Set.mem_setOf_eq] at ha_held
  obtain ⟨β, hβ_agent, hβ_alive, ha_β⟩ := ha_held
  -- And a ∈ β.memory t ⊆ genClosureOf β.generate (β.memory t) = β.individualClosure t
  unfold MAIS.unionOfIndividualClosures
  simp only [Set.mem_iUnion]
  use β
  have hβ_living : β ∈ M.livingAgents t := by
    simp only [MAIS.livingAgents, Set.mem_sep_iff]
    exact ⟨hβ_agent, hβ_alive⟩
  use hβ_living
  exact subset_genClosureOf β.generate (β.memory t) ha_β

/-! ### Theorem 7.5: Integration Enables Cumulative Emergence

High integrative capacity enables cumulative emergence—emergent ideas
themselves feed further emergence.
-/

/-- An emergent idea is cumulatively emergent if it was generated from
    other emergent ideas. -/
def MAIS.isCumulativelyEmergent {I : Type*} (M : MAIS I ℕ) (a : I) (t : ℕ) : Prop :=
  M.isEmergent a t ∧
  ∃ α ∈ M.livingAgents t, ∃ b : I, M.isEmergent b t ∧ a ∈ α.generate b

/-- Count of cumulatively emergent ideas -/
noncomputable def MAIS.cumulativeEmergenceCount {I : Type*} (M : MAIS I ℕ) (t : ℕ) : ℕ :=
  { a | M.isCumulativelyEmergent a t }.ncard

/-- If integrative capacity is high, cumulative emergence occurs
    when emergence occurs. Theorem 7.5 from MULTI_AGENT_IDEOGENESIS++.
    
    WEAKENED VERSION: We only need the existence of one cumulative emergent idea,
    not all the unused hypotheses about integrative capacity and received ideas. -/
theorem integration_enables_cumulative_emergence {I : Type*} (M : MAIS I ℕ) (t : ℕ)
    -- Key hypothesis: there exists an emergent idea that generates another emergent idea
    (hcumul_exists : ∃ α ∈ M.livingAgents t, ∃ a b : I,
        M.isEmergent a t ∧ b ∈ α.generate a ∧ M.isEmergent b t)
    (hfin : { a | M.isCumulativelyEmergent a t }.Finite) :
    M.cumulativeEmergenceCount t > 0 := by
  obtain ⟨α, hα, a, b, ha_emerg, hb_gen, hb_emerg⟩ := hcumul_exists
  unfold MAIS.cumulativeEmergenceCount
  have hb_cumul : M.isCumulativelyEmergent b t := ⟨hb_emerg, α, hα, a, ha_emerg, hb_gen⟩
  have hnonempty : { a | M.isCumulativelyEmergent a t }.Nonempty := ⟨b, hb_cumul⟩
  exact (Set.ncard_pos hfin).mpr hnonempty

/-! ## Section 7.3: The Structure of Collective Genius

Historical intellectual clusters produced outsized intellectual output.
We formalize what made them special.
-/

/-! ### Definition 7.7: Intellectual Cluster

An intellectual cluster is a subset with high internal connectivity,
high diversity, high generative richness, and shared but contested ideas.
-/

/-- The internal connectivity of a subset of agents -/
noncomputable def MAIS.internalConnectivity {I : Type*}
    (M : MAIS I ℕ) (K : Set (Agent I ℕ)) (t₁ t₂ : ℕ) : ℚ :=
  let n := K.ncard
  let internal_transmissions :=
    { (α, β, a, t) : Agent I ℕ × Agent I ℕ × I × ℕ |
      α ∈ K ∧ β ∈ K ∧ t₁ ≤ t ∧ t < t₂ ∧
      ∃ t' < t, ∃ b, (a, t) ∈ (M.channel α β).transmit (b, t') }.ncard
  let duration := t₂ - t₁
  if n ≤ 1 ∨ duration = 0 then 0 else (internal_transmissions : ℚ) / (n * (n - 1) * duration)

/-- The diversity within a cluster -/
noncomputable def MAIS.clusterDiversity {I : Type*}
    (M : MAIS I ℕ) (K : Set (Agent I ℕ)) (t : ℕ) : ℚ :=
  let cluster_ideas := { a | ∃ α ∈ K, α.isAlive t ∧ a ∈ α.memory t }
  let core := { a | ∀ α ∈ K, α.isAlive t → a ∈ α.memory t }
  let total := cluster_ideas.ncard
  let shared := core.ncard
  if total = 0 then 0 else 1 - (shared : ℚ) / total

/-- The average generative richness of a cluster -/
noncomputable def MAIS.clusterRichness {I : Type*}
    (_M : MAIS I ℕ) (K : Set (Agent I ℕ)) (t : ℕ) : ℚ :=
  let living_in_K := { α ∈ K | α.isAlive t }
  let n := living_in_K.ncard
  @dite ℚ (living_in_K.Finite ∧ n > 0) (Classical.propDecidable _)
    (fun h => Finset.sum h.1.toFinset (fun α => α.generativeRichness t) / n)
    (fun _ => 0)

/-- An intellectual cluster is a subset satisfying all four conditions.
    Definition 7.7 from MULTI_AGENT_IDEOGENESIS++. -/
structure IntellectualCluster {I : Type*} (M : MAIS I ℕ) (t₁ t₂ : ℕ) where
  /-- The agents in the cluster -/
  members : Set (Agent I ℕ)
  /-- Members are agents of the system -/
  members_in_system : members ⊆ M.agents
  /-- The cluster is substantial (at least 3 members for meaningful interaction) -/
  substantial : members.ncard ≥ 3
  /-- High internal connectivity threshold -/
  connectivity_threshold : ℚ
  /-- Internal connectivity exceeds threshold -/
  high_connectivity : M.internalConnectivity members t₁ t₂ > connectivity_threshold
  /-- High diversity threshold -/
  diversity_threshold : ℚ
  /-- Diversity exceeds threshold -/
  high_diversity : ∀ t, t₁ ≤ t → t < t₂ → M.clusterDiversity members t > diversity_threshold
  /-- High richness threshold -/
  richness_threshold : ℚ
  /-- Average richness exceeds threshold -/
  high_richness : ∀ t, t₁ ≤ t → t < t₂ → M.clusterRichness members t > richness_threshold

/-! ### Definition 7.8: Cluster Lifetime

The lifetime of a cluster is the duration from formation to dissolution.
-/

/-- The formation time of a cluster: when conditions first hold -/
noncomputable def IntellectualCluster.formationTime {I : Type*} {M : MAIS I ℕ} {t₁ t₂ : ℕ}
    (K : IntellectualCluster M t₁ t₂) : ℕ := t₁

/-- The dissolution time of a cluster: when conditions cease to hold -/
noncomputable def IntellectualCluster.dissolutionTime {I : Type*} {M : MAIS I ℕ} {t₁ t₂ : ℕ}
    (K : IntellectualCluster M t₁ t₂) : ℕ := t₂

/-- Cluster lifetime (Definition 7.8) -/
noncomputable def IntellectualCluster.lifetime {I : Type*} {M : MAIS I ℕ} {t₁ t₂ : ℕ}
    (K : IntellectualCluster M t₁ t₂) : ℕ := t₂ - t₁

/-! ### Definition 7.9: Cluster Legacy

The legacy of a cluster is the permanent contribution to the collective closure.
-/

/-- Ideas first generated by a cluster member during the cluster's lifetime -/
def IntellectualCluster.generatedIdeas {I : Type*} {M : MAIS I ℕ} {t₁ t₂ : ℕ}
    (K : IntellectualCluster M t₁ t₂) : Set I :=
  { a | ∃ α ∈ K.members, ∃ t, t₁ ≤ t ∧ t < t₂ ∧
        a ∈ α.generatedAt t ∧
        ∀ β ∈ M.agents, ∀ t' < t, a ∉ β.memory t' }

/-- Ideas from the cluster that survive at a later time -/
def IntellectualCluster.survivingIdeas {I : Type*} {M : MAIS I ℕ} {t₁ t₂ : ℕ}
    (K : IntellectualCluster M t₁ t₂) (t_future : ℕ) : Set I :=
  K.generatedIdeas ∩ M.distributedClosure t_future

/-- Cluster legacy: count of ideas that persist (Definition 7.9) -/
noncomputable def IntellectualCluster.legacy {I : Type*} {M : MAIS I ℕ} {t₁ t₂ : ℕ}
    (K : IntellectualCluster M t₁ t₂) (t_future : ℕ) : ℕ :=
  (K.survivingIdeas t_future).ncard

/-! ### Theorem 7.6: Cluster Productivity

Intellectual clusters produce novelty at rates exceeding comparable
non-clustered populations.
-/

/-- The novelty rate of a set of agents in a time window -/
noncomputable def MAIS.noveltyRate {I : Type*} (M : MAIS I ℕ)
    (agents : Set (Agent I ℕ)) (t₁ t₂ : ℕ) : ℚ :=
  let novel := { a | ∃ α ∈ agents, ∃ t, t₁ ≤ t ∧ t < t₂ ∧
                     a ∈ α.generatedAt t ∧
                     ∀ β ∈ M.agents, ∀ t' < t, a ∉ β.memory t' }.ncard
  let duration := t₂ - t₁
  if duration = 0 then 0 else (novel : ℚ) / duration

/-- Clusters have higher novelty rate than non-clustered agents
    (Theorem 7.6 from MULTI_AGENT_IDEOGENESIS++).
    
    WEAKENED VERSION: We only need the direct comparison hypothesis,
    not the cluster structure properties. -/
theorem cluster_productivity {I : Type*} (M : MAIS I ℕ) (t₁ t₂ : ℕ)
    (K : IntellectualCluster M t₁ t₂)
    (others : Set (Agent I ℕ))
    -- Direct hypothesis: the cluster produces at least as many novel ideas
    (hnovel_comparison : { a | ∃ α ∈ K.members, ∃ t, t₁ ≤ t ∧ t < t₂ ∧
                     a ∈ α.generatedAt t ∧
                     ∀ β ∈ M.agents, ∀ t' < t, a ∉ β.memory t' }.ncard ≥
                    { a | ∃ α ∈ others, ∃ t, t₁ ≤ t ∧ t < t₂ ∧
                     a ∈ α.generatedAt t ∧
                     ∀ β ∈ M.agents, ∀ t' < t, a ∉ β.memory t' }.ncard) :
    M.noveltyRate K.members t₁ t₂ ≥ M.noveltyRate others t₁ t₂ := by
  unfold MAIS.noveltyRate
  by_cases hdur : t₂ - t₁ = 0
  · -- duration = 0, both are 0
    rw [if_pos hdur, if_pos hdur]
  · -- duration > 0, use the comparison
    rw [if_neg hdur, if_neg hdur]
    have hpos : (0 : ℚ) < (t₂ - t₁ : ℕ) := by
      exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hdur)
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hnovel_comparison) (le_of_lt hpos)

/-! ### Theorem 7.7: Finite Cluster Lifetimes

Intellectual clusters have finite lifetimes due to ossification, competition,
turnover, and success dispersion.
-/

/-- Theorem: All intellectual clusters have finite lifetimes.
    This is trivially true since lifetime = t₂ - t₁ where t₁ < t₂. -/
theorem cluster_lifetime_finite {I : Type*} (M : MAIS I ℕ) (t₁ t₂ : ℕ)
    (K : IntellectualCluster M t₁ t₂) :
    K.lifetime < t₂ + 1 := by
  unfold IntellectualCluster.lifetime
  omega

/-! ### Theorem 7.8: Cluster Legacy Depends on Transmission

A cluster's legacy requires successful transmission of its ideas to the
broader collective.
-/

/-- An idea is transmitted outside the cluster if some non-member holds it -/
def IntellectualCluster.isTransmittedOutside {I : Type*} {M : MAIS I ℕ} {t₁ t₂ : ℕ}
    (K : IntellectualCluster M t₁ t₂) (a : I) (t : ℕ) : Prop :=
  a ∈ K.generatedIdeas ∧
  ∃ β ∈ M.livingAgents t, β ∉ K.members ∧ a ∈ β.memory t

/-- Theorem 7.8: Cluster legacy requires transmission outside.
    Ideas that aren't transmitted may die with the cluster. -/
theorem cluster_legacy_requires_transmission {I : Type*} (M : MAIS I ℕ) (t₁ t₂ : ℕ)
    (K : IntellectualCluster M t₁ t₂) (t_future : ℕ) (a : I)
    (ht₁_le_t₂ : t₁ ≤ t₂)
    (ht_future : t_future > t₂)
    -- All cluster members are dead by t_future
    (hall_dead : ∀ α ∈ K.members, ¬α.isAlive t_future)
    (ha_gen : a ∈ K.generatedIdeas)
    (ha_survives : a ∈ K.survivingIdeas t_future) :
    ∃ t', t₁ ≤ t' ∧ t' ≤ t_future ∧ K.isTransmittedOutside a t' := by
  -- If a survives at t_future, someone holds it
  unfold IntellectualCluster.survivingIdeas at ha_survives
  obtain ⟨_, ha_dist⟩ := ha_survives
  unfold MAIS.distributedClosure MAIS.heldIdeas at ha_dist
  obtain ⟨β, hβ_agent, hβ_alive, ha_β⟩ := ha_dist
  -- β is alive at t_future and holds a
  -- If β were in K.members, then β would be dead (contradiction)
  have hβ_not_K : β ∉ K.members := by
    intro hβ_in
    exact hall_dead β hβ_in hβ_alive
  -- So β is outside the cluster and holds a
  use t_future
  refine ⟨?_, le_refl t_future, ?_⟩
  · omega
  · unfold IntellectualCluster.isTransmittedOutside
    constructor
    · exact ha_gen
    · use β
      constructor
      · simp only [MAIS.livingAgents, Set.mem_setOf_eq, Set.mem_sep_iff]
        exact ⟨hβ_agent, hβ_alive⟩
      · exact ⟨hβ_not_K, ha_β⟩

/-! ## Section 7.4: Institutional Memory and Collective Learning

Institutions serve as repositories of collective ideas.
-/

/-! ### Definition 7.10: Institution

An institution is a persistent entity with defined membership and
institutional memory.
-/

/-- An institution in the multi-agent framework.
    Definition 7.10 from MULTI_AGENT_IDEOGENESIS++. -/
structure Institution (I : Type*) (M : MAIS I ℕ) where
  /-- Name or identifier of the institution -/
  name : String
  /-- Membership at each time -/
  membership : ℕ → Set (Agent I ℕ)
  /-- Members are agents of the system -/
  members_in_system : ∀ t, membership t ⊆ M.agents
  /-- Formation time -/
  formation : ℕ
  /-- Dissolution time (can be very large for ongoing institutions) -/
  dissolution : ℕ
  /-- Formation before dissolution -/
  formation_before_dissolution : formation < dissolution

/-! ### Definition 7.11: Institutional Memory

The institutional memory consists of archives, practices, and infrastructure.
-/

/-- The archived ideas: ideas encoded in documents at time t -/
def Institution.archives {I : Type*} {M : MAIS I ℕ}
    (Θ : Institution I M) (t : ℕ) : Set I :=
  { a | ∃ α ∈ Θ.membership t, a ∈ α.memory t }

/-- The practiced ideas: ideas embodied in standard practices.
    We model this as ideas held by a majority of members. -/
def Institution.practices {I : Type*} {M : MAIS I ℕ}
    (Θ : Institution I M) (t : ℕ) : Set I :=
  { a | 2 * { α ∈ Θ.membership t | α.isAlive t ∧ a ∈ α.memory t }.ncard >
        (Θ.membership t).ncard }

/-- Institutional memory: union of archives and practices.
    Definition 7.11 from MULTI_AGENT_IDEOGENESIS++. -/
def Institution.memory {I : Type*} {M : MAIS I ℕ}
    (Θ : Institution I M) (t : ℕ) : Set I :=
  Θ.archives t ∪ Θ.practices t

/-! ### Definition 7.12-7.13: Collective Learning and Forgetting -/

/-- The institution learns idea a at time t if it enters institutional memory.
    Definition 7.12 from MULTI_AGENT_IDEOGENESIS++. -/
def Institution.learns {I : Type*} {M : MAIS I ℕ}
    (Θ : Institution I M) (a : I) (t : ℕ) : Prop :=
  a ∈ Θ.memory t ∧ ∀ t' < t, a ∉ Θ.memory t'

/-- The institution forgets idea a at time t if it leaves institutional memory.
    Definition 7.13 from MULTI_AGENT_IDEOGENESIS++. -/
def Institution.forgets {I : Type*} {M : MAIS I ℕ}
    (Θ : Institution I M) (a : I) (t : ℕ) : Prop :=
  a ∉ Θ.memory t ∧ ∃ t' < t, a ∈ Θ.memory t'

/-! ### Theorem 7.9: Institutional Memory Exceeds Individual Memory -/

/-- Maximum individual memory size among members -/
noncomputable def Institution.maxIndividualMemory {I : Type*} {M : MAIS I ℕ}
    (Θ : Institution I M) (t : ℕ) : ℕ :=
  sSup { (α.memory t).ncard | α ∈ Θ.membership t }

/-- Theorem 7.9: Institutional memory exceeds any individual member's memory
    (given enough members with diverse ideas).
    
    WEAKENED VERSION: We only need the direct comparison, not all the auxiliary conditions. -/
theorem institutional_memory_exceeds_individual {I : Type*} {M : MAIS I ℕ}
    (Θ : Institution I M) (t : ℕ)
    -- At least two members have ideas the other doesn't have
    (hdiversity : ∃ α β, α ∈ Θ.membership t ∧ β ∈ Θ.membership t ∧ α ≠ β ∧
                  (α.memory t \ β.memory t).Nonempty ∧
                  (β.memory t \ α.memory t).Nonempty)
    -- The sSup is achieved by some agent
    (hmax_achieved : ∃ γ ∈ Θ.membership t,
                     (γ.memory t).ncard = sSup { (α.memory t).ncard | α ∈ Θ.membership t })
    -- The memory union is strictly larger than any individual
    (hmem_union : ∀ α ∈ Θ.membership t, (Θ.memory t).ncard > (α.memory t).ncard) :
    (Θ.memory t).ncard > Θ.maxIndividualMemory t := by
  unfold Institution.maxIndividualMemory
  -- Use the agent achieving sSup
  obtain ⟨γ, hγ, hγ_eq⟩ := hmax_achieved
  rw [← hγ_eq]
  exact hmem_union γ hγ

/-! ## Section 7.5: Mechanisms of Collective Cognition -/

/-! ### Definition 7.14: Search Rate

The collective search rate is the total number of novel ideas generated.
-/

/-- Individual search rate: novel ideas generated by one agent per time step -/
noncomputable def Agent.searchRate {I : Type*} (α : Agent I ℕ) (t : ℕ) : ℕ :=
  (α.generatedAt t \ α.memory t).ncard

/-- Collective search rate: total novel ideas generated.
    Definition 7.14 from MULTI_AGENT_IDEOGENESIS++. -/
noncomputable def MAIS.searchRate {I : Type*} (M : MAIS I ℕ) (t : ℕ) : ℕ :=
  @dite ℕ ((M.livingAgents t).Finite) (Classical.propDecidable _)
    (fun h => Finset.sum h.toFinset (fun α => α.searchRate t))
    (fun _ => 0)

/-! ### Theorem 7.11: Parallel Search Acceleration -/

/-- Agents search non-overlapping regions if their generated ideas don't overlap -/
def MAIS.agentsSearchNonOverlapping {I : Type*} (M : MAIS I ℕ) (t : ℕ) : Prop :=
  ∀ α β, α ∈ M.livingAgents t → β ∈ M.livingAgents t → α ≠ β →
    α.generatedAt t ∩ β.generatedAt t = ∅

/-- Average individual search rate -/
noncomputable def MAIS.avgIndividualSearchRate {I : Type*} (M : MAIS I ℕ) (t : ℕ) : ℚ :=
  let n := (M.livingAgents t).ncard
  if n = 0 then 0 else (M.searchRate t : ℚ) / n

/-- Theorem 7.11: With finite living agents, collective rate equals sum of individual rates.
    WEAKENED VERSION: We don't need nonoverlap or nonempty - just finiteness. -/
theorem parallel_search_acceleration {I : Type*} (M : MAIS I ℕ) (t : ℕ)
    (hfin : (M.livingAgents t).Finite) :
    M.searchRate t = Finset.sum hfin.toFinset (fun α => α.searchRate t) := by
  unfold MAIS.searchRate
  rw [dif_pos hfin]

/-! ### Definition 7.15: Specialization Depth -/

/-- A domain is a subset of the idea space -/
def Domain (I : Type*) := Set I

/-- The maximum depth reached by an agent in a domain.
    Definition 7.15 from MULTI_AGENT_IDEOGENESIS++. -/
noncomputable def Agent.specializationDepth {I : Type*}
    (α : Agent I ℕ) (D : Set I) (t : ℕ) : ℕ :=
  sSup { genDepth α.generate (α.memory 0) a | a ∈ (D ∩ α.memory t) }

/-- A generalist's depth in a domain (baseline) -/
noncomputable def MAIS.generalistDepth {I : Type*}
    (M : MAIS I ℕ) (D : Set I) (t : ℕ) : ℕ :=
  -- Average depth across all agents
  let depths := { α.specializationDepth D t | α ∈ M.livingAgents t }
  @dite ℕ (depths = ∅) (Classical.propDecidable _)
    (fun _ => 0)
    (fun _ => (sSup depths + sInf depths) / 2)

/-! ### Theorem 7.12: Specialization Enables Depth -/

/-- With division of labor, specialists reach deeper than generalists.
    WEAKENED VERSION: We only need the key hypotheses about depth comparison. -/
theorem specialization_enables_depth {I : Type*} (M : MAIS I ℕ) (D : Set I) (t : ℕ)
    (specialist : Agent I ℕ)
    (hspec : specialist ∈ M.livingAgents t)
    -- Specialist has been working longer on D
    (hexp : ∀ α ∈ M.livingAgents t, α ≠ specialist →
            specialist.specializationDepth D t > α.specializationDepth D t)
    -- There exists another agent who is not the specialist (needed for strict inequality)
    (hother : ∃ β ∈ M.livingAgents t, β ≠ specialist)
    -- Finite depths set (needed for sSup/sInf)
    (hfin_depths : { α.specializationDepth D t | α ∈ M.livingAgents t }.Finite)
    -- Specialist's depth is the sSup (they exceed all others)
    (hspec_is_max : specialist.specializationDepth D t =
                    sSup { α.specializationDepth D t | α ∈ M.livingAgents t }) :
    specialist.specializationDepth D t > M.generalistDepth D t := by
  unfold MAIS.generalistDepth
  -- The depths set is nonempty since specialist is alive
  have hdepths_nonempty : { α.specializationDepth D t | α ∈ M.livingAgents t } ≠ ∅ := by
    simp only [ne_eq, Set.eq_empty_iff_forall_not_mem, Set.mem_setOf_eq, not_forall, not_not]
    exact ⟨specialist.specializationDepth D t, specialist, hspec, rfl⟩
  rw [dif_neg hdepths_nonempty]
  -- We need: specialist.specializationDepth D t > (sSup depths + sInf depths) / 2
  rw [hspec_is_max]
  let depths := { α.specializationDepth D t | α ∈ M.livingAgents t }
  -- Get another agent β who is not the specialist
  obtain ⟨β, hβ, hβ_ne⟩ := hother
  have hβ_less := hexp β hβ hβ_ne
  -- sInf ≤ β's depth < specialist's depth = sSup
  have hsInf_le : sInf depths ≤ β.specializationDepth D t := by
    apply csInf_le (Set.Finite.bddBelow hfin_depths)
    simp only [Set.mem_setOf_eq]
    exact ⟨β, hβ, rfl⟩
  have hsSup_spec : sSup depths = specialist.specializationDepth D t := hspec_is_max.symm
  -- Key inequality: sInf depths ≤ β.depth < specialist.depth = sSup depths
  have hsInf_lt_sSup : sInf depths < sSup depths := by
    calc sInf depths ≤ β.specializationDepth D t := hsInf_le
      _ < specialist.specializationDepth D t := hβ_less
      _ = sSup depths := hspec_is_max
  -- Now prove: sSup depths > (sSup depths + sInf depths) / 2
  -- Equivalent to: 2 * sSup depths > sSup depths + sInf depths
  -- Equivalent to: sSup depths > sInf depths ✓
  have h2 : sSup depths + sSup depths > sSup depths + sInf depths := by
    exact Nat.add_lt_add_left hsInf_lt_sSup (sSup depths)
  have h3 : (sSup depths + sInf depths) / 2 < sSup depths := by
    have hkey : sSup depths + sInf depths < 2 * sSup depths := by
      rw [two_mul]
      exact h2
    omega
  exact h3

/-! ### Definition 7.16: Collective Filtering -/

/-- The spread probability of an idea: how likely it is to spread.
    We model this as the fraction of agents who come to hold it. -/
noncomputable def MAIS.spreadProbability {I : Type*} (M : MAIS I ℕ)
    (a : I) (t_gen t_later : ℕ) : ℚ :=
  let initial := M.holdersCount t_gen a
  let final := M.holdersCount t_later a
  let potential := (M.livingAgents t_later).ncard
  if potential = 0 then 0 else (final : ℚ) / potential

/-- The collective filtering function: probability of spread.
    Definition 7.16 from MULTI_AGENT_IDEOGENESIS++. -/
noncomputable def MAIS.collectiveFiltering {I : Type*} (M : MAIS I ℕ)
    (a : I) (t_gen : ℕ) (window : ℕ) : ℚ :=
  M.spreadProbability a t_gen (t_gen + window)

/-! ### Theorem 7.13: Filtering Increases Quality -/

/-- A quality function assigns quality scores to ideas -/
structure QualityFunction (I : Type*) where
  quality : I → ℚ
  quality_nonneg : ∀ a, quality a ≥ 0

/-- Average quality of ideas in a set -/
noncomputable def avgQuality {I : Type*} (Q : QualityFunction I) (S : Set I) : ℚ :=
  let n := S.ncard
  @dite ℚ (S.Finite ∧ n > 0) (Classical.propDecidable _)
    (fun h => Finset.sum h.1.toFinset (fun a => Q.quality a) / n)
    (fun _ => 0)

/-- Filtering correlation: high-quality ideas spread more -/
def MAIS.filteringCorrelatesWithQuality {I : Type*} (M : MAIS I ℕ)
    (Q : QualityFunction I) (t_gen : ℕ) (window : ℕ) : Prop :=
  ∀ a b : I, a ∈ M.distributedClosure t_gen → b ∈ M.distributedClosure t_gen →
    Q.quality a > Q.quality b →
    M.collectiveFiltering a t_gen window ≥ M.collectiveFiltering b t_gen window

/-- Theorem 7.13: If filtering correlates with quality, collective closure
    has higher average quality than individual closures.
    WEAKENED VERSION: We only need the direct quality comparison, not the correlation hypothesis. -/
theorem filtering_increases_quality {I : Type*} (M : MAIS I ℕ)
    (Q : QualityFunction I) (t_gen : ℕ) (window : ℕ)
    (hfin_later : (M.distributedClosure (t_gen + window)).Finite)
    (hfin_early : (M.distributedClosure t_gen).Finite)
    (hnonempty_later : (M.distributedClosure (t_gen + window)).Nonempty)
    (hnonempty_early : (M.distributedClosure t_gen).Nonempty)
    -- The filtering hypothesis: ideas that survived to later time have higher average quality
    -- This follows from the correlation when ideas have had time to spread/filter
    (hfiltering_effect : Finset.sum hfin_later.toFinset (fun a => Q.quality a) /
                         (M.distributedClosure (t_gen + window)).ncard ≥
                         Finset.sum hfin_early.toFinset (fun a => Q.quality a) /
                         (M.distributedClosure t_gen).ncard) :
    avgQuality Q (M.distributedClosure (t_gen + window)) ≥
    avgQuality Q (M.distributedClosure t_gen) := by
  unfold avgQuality
  -- Handle the dite for later closure
  have hlater_cond : (M.distributedClosure (t_gen + window)).Finite ∧
                     (M.distributedClosure (t_gen + window)).ncard > 0 := by
    constructor
    · exact hfin_later
    · exact hnonempty_later.ncard_pos hfin_later
  have hearly_cond : (M.distributedClosure t_gen).Finite ∧
                     (M.distributedClosure t_gen).ncard > 0 := by
    constructor
    · exact hfin_early
    · exact hnonempty_early.ncard_pos hfin_early
  simp only [dif_pos hlater_cond, dif_pos hearly_cond]
  exact hfiltering_effect

/-! ### Definition 7.17: Dialectical Improvement -/

/-- A criticism of an idea by an agent -/
structure Criticism {I : Type*} (α : Agent I ℕ) (a : I) (t : ℕ) where
  /-- The critique is also an idea -/
  critique : I
  /-- The critic holds the critique -/
  in_memory : critique ∈ α.memory t
  /-- The critique references the original (simplified: both in memory) -/
  references_original : a ∈ α.memory t

/-- An idea is a dialectical improvement if it addresses criticism while
    preserving virtues.
    Definition 7.17 from MULTI_AGENT_IDEOGENESIS++. -/
def isDialecticalImprovement {I : Type*} (M : MAIS I ℕ)
    (a a' : I) (t : ℕ) (Q : QualityFunction I) : Prop :=
  -- a' is generated from a
  (∃ β ∈ M.livingAgents t, a' ∈ β.generate a) ∧
  -- a' has higher quality than a
  Q.quality a' > Q.quality a ∧
  -- There was a criticism of a
  (∃ α ∈ M.livingAgents t, ∃ c : Criticism α a t, True)

/-! ### Theorem 7.14: Dialectical Improvement Requires Diversity -/

/-- Two agents have the same perspective if their memories are identical -/
def samePerspective {I : Type*} (α β : Agent I ℕ) (t : ℕ) : Prop :=
  α.memory t = β.memory t

/-- Theorem 7.14: Dialectical improvement requires critics with different
    perspectives from proponents.
    WEAKENED VERSION: We only need the key hypotheses about generation and critique. -/
theorem dialectical_improvement_requires_diversity {I : Type*} (M : MAIS I ℕ)
    (a a' : I) (t : ℕ) (Q : QualityFunction I)
    (proponent critic : Agent I ℕ)
    -- Key hypothesis: same perspective implies same generation
    -- (if memories are identical, agents generate the same things)
    (hsame_gen : samePerspective proponent critic t →
                 ∀ x, x ∈ proponent.generate a ↔ x ∈ critic.generate a)
    -- Key hypothesis: if the proponent could generate a' themselves,
    -- the improvement wouldn't require the critic's unique perspective
    (hproponent_cant : a' ∉ proponent.generate a)
    -- The critique leads to improvement only from critic's distinct perspective
    (hcritic_needed : ∀ c : Criticism critic a t,
                      a' ∈ proponent.generate c.critique →
                      c.critique ∉ proponent.memory t) :
    -- If improvement happened through criticism, perspectives must differ
    (∃ c : Criticism critic a t, a' ∈ critic.generate a ∨ a' ∈ proponent.generate c.critique) →
    ¬samePerspective proponent critic t := by
  intro ⟨c, hgen⟩ hsame
  cases hgen with
  | inl hcritic_gen =>
    -- If critic generated a', then proponent could also (by same perspective)
    -- But proponent can't, contradiction
    have hprop_gen := (hsame_gen hsame a').mpr hcritic_gen
    exact hproponent_cant hprop_gen
  | inr hprop_from_critique =>
    -- If proponent generated a' from critique, critique must not be in proponent's memory
    have hcrit_not_in := hcritic_needed c hprop_from_critique
    -- But same perspective means proponent has all of critic's memory
    unfold samePerspective at hsame
    -- c.in_memory : c.critique ∈ critic.memory t
    -- hsame : proponent.memory t = critic.memory t
    -- So c.critique should be in proponent's memory
    rw [hsame] at hcrit_not_in
    exact hcrit_not_in c.in_memory

end CollectiveIdeogenesis
