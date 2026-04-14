/-
# Collective Ideogenesis: Distributed Closure

This file contains definitions and theorems about closure in multi-agent systems
from MULTI_AGENT_IDEOGENESIS++ Chapter 2.4 and 8.3:

- Definition 2.13: Naive Collective Closure
- Definition 2.14: Distributed Closure at Time t
- Definition 2.15: Consensus Closure at Time t
- Definition 2.16: Majority Closure
- Definition 2.17: Closure Divergence
- Theorem 2.1: Closure Inclusions
- Theorem 8.4: Distributed Closure Monotonicity
- Theorem 8.5: Closure Non-Monotonicity with Forgetting
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.Collective_Basic

namespace CollectiveIdeogenesis

/-! ## Definition 2.13: Naive Collective Closure

The naive closure is the union of all ideas ever held by any agent at any time.
-/

/-- The naive collective closure: all ideas ever held by any agent (Definition 2.13).
    Warning: This may not be well-defined (could be a proper class). -/
def MAIS.naiveClosure {I T : Type*} [LinearOrder T] (M : MAIS I T) : Set I :=
  { a | ∃ t : T, ∃ α ∈ M.agents, a ∈ α.memory t }

/-! ## Definition 2.14: Distributed Closure at Time t

The distributed closure at time t is the set of ideas currently held by someone.
-/

/-- The distributed closure at time t (Definition 2.14).
    This is the set of all ideas held by at least one living agent. -/
def MAIS.distributedClosure {I T : Type*} [LinearOrder T] (M : MAIS I T) (t : T) : Set I :=
  M.heldIdeas t

/-- Notation: cl(t) for distributed closure -/
notation "cl(" M "," t ")" => MAIS.distributedClosure M t

/-! ## Definition 2.15: Consensus Closure at Time t

The consensus closure is the set of ideas held by ALL agents.
-/

/-- The consensus closure at time t: ideas held by all living agents (Definition 2.15). -/
def MAIS.consensusClosure {I T : Type*} [LinearOrder T] (M : MAIS I T) (t : T) : Set I :=
  { a | ∀ α ∈ M.livingAgents t, a ∈ α.memory t }

/-- Notation: cl_∩(t) for consensus closure -/
notation "cl_∩(" M "," t ")" => MAIS.consensusClosure M t

/-! ## Definition 2.16: Majority Closure

The majority closure is the set of ideas held by more than half the agents.
-/

/-- Count how many living agents hold an idea -/
noncomputable def MAIS.holdersCount {I T : Type*} [LinearOrder T] 
    (M : MAIS I T) (t : T) (a : I) : ℕ :=
  { α ∈ M.livingAgents t | a ∈ α.memory t }.ncard

/-- The majority closure at time t: ideas held by majority (Definition 2.16). -/
def MAIS.majorityClosure {I T : Type*} [LinearOrder T] (M : MAIS I T) (t : T) : Set I :=
  { a | 2 * M.holdersCount t a > (M.livingAgents t).ncard }

/-- Notation: cl_maj(t) for majority closure -/
notation "cl_maj(" M "," t ")" => MAIS.majorityClosure M t

/-! ## Definition 2.17: Closure Divergence

The divergence measures the fraction of ideas not universally held.
-/

/-- The closure divergence at time t (Definition 2.17).
    This is the fraction of distributed closure not in consensus closure. -/
noncomputable def MAIS.closureDivergence {I T : Type*} [LinearOrder T] 
    (M : MAIS I T) (t : T) : ℚ :=
  let distributed := (M.distributedClosure t).ncard
  let consensus := (M.consensusClosure t).ncard
  if distributed = 0 then 0 else (distributed - consensus : ℤ) / distributed

/-! ## Theorem 2.1: Closure Inclusions

For any time t: cl_∩(t) ⊆ cl_maj(t) ⊆ cl(t) ⊆ cl_naive
-/

/-- Consensus closure is contained in distributed closure 
    (requires at least one living agent for non-vacuous statement) -/
theorem MAIS.consensus_subset_distributed {I T : Type*} [LinearOrder T] 
    (M : MAIS I T) (t : T) (hnonempty : (M.livingAgents t).Nonempty) : 
    M.consensusClosure t ⊆ M.distributedClosure t := by
  intro a ha
  simp only [consensusClosure, Set.mem_setOf_eq] at ha
  simp only [distributedClosure, heldIdeas, Set.mem_setOf_eq]
  obtain ⟨α, hα⟩ := hnonempty
  simp only [livingAgents, Set.mem_sep_iff] at hα
  exact ⟨α, hα.1, hα.2, ha α ⟨hα.1, hα.2⟩⟩

/-- Distributed closure is contained in naive closure -/
theorem MAIS.distributed_subset_naive {I T : Type*} [LinearOrder T] 
    (M : MAIS I T) (t : T) : M.distributedClosure t ⊆ M.naiveClosure := by
  intro a ha
  simp only [distributedClosure, heldIdeas, Set.mem_setOf_eq] at ha
  simp only [naiveClosure, Set.mem_setOf_eq]
  obtain ⟨α, hα, halive, ha⟩ := ha
  exact ⟨t, α, hα, ha⟩

/-- Majority closure is contained in distributed closure -/
theorem MAIS.majority_subset_distributed {I T : Type*} [LinearOrder T] 
    (M : MAIS I T) (t : T) : M.majorityClosure t ⊆ M.distributedClosure t := by
  intro a ha
  simp only [majorityClosure, Set.mem_setOf_eq] at ha
  simp only [distributedClosure, heldIdeas, Set.mem_setOf_eq]
  -- If majority holds a, then at least one agent holds a
  have hpos : M.holdersCount t a > 0 := by
    by_contra hzero
    push_neg at hzero
    simp only [Nat.le_zero] at hzero
    rw [hzero] at ha
    omega
  simp only [holdersCount] at hpos
  have hne : { α ∈ M.livingAgents t | a ∈ α.memory t }.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have : Set.ncard { α ∈ M.livingAgents t | a ∈ α.memory t } = 0 := by
      rw [hemp]; simp
    omega
  obtain ⟨α, hα⟩ := hne
  simp only [Set.mem_sep_iff, livingAgents, Set.mem_sep_iff] at hα
  exact ⟨α, hα.1.1, hα.1.2, hα.2⟩

/-- Consensus closure is contained in majority closure (when there are agents) -/
theorem MAIS.consensus_subset_majority {I T : Type*} [LinearOrder T] 
    (M : MAIS I T) (t : T) (hnonempty : (M.livingAgents t).Nonempty) 
    (hfinite : (M.livingAgents t).Finite) : 
    M.consensusClosure t ⊆ M.majorityClosure t := by
  intro a ha
  simp only [consensusClosure, Set.mem_setOf_eq] at ha
  simp only [majorityClosure, Set.mem_setOf_eq]
  -- If all agents hold a, then holdersCount = livingAgents.ncard
  have heq : { α ∈ M.livingAgents t | a ∈ α.memory t } = M.livingAgents t := by
    ext α
    simp only [Set.mem_sep_iff, and_iff_left_iff_imp]
    intro hα
    exact ha α hα
  simp only [holdersCount, heq]
  have hpos : 0 < (M.livingAgents t).ncard := by
    rw [Set.ncard_pos hfinite]
    exact hnonempty
  omega

/-- Full chain of closure inclusions (Theorem 2.1) -/
theorem MAIS.closure_chain {I T : Type*} [LinearOrder T] 
    (M : MAIS I T) (t : T) (hnonempty : (M.livingAgents t).Nonempty)
    (hfinite : (M.livingAgents t).Finite) :
    M.consensusClosure t ⊆ M.majorityClosure t ∧
    M.majorityClosure t ⊆ M.distributedClosure t ∧
    M.distributedClosure t ⊆ M.naiveClosure :=
  ⟨consensus_subset_majority M t hnonempty hfinite, 
   majority_subset_distributed M t, 
   distributed_subset_naive M t⟩

/-! ## Theorem 8.4: Distributed Closure Monotonicity (without forgetting)

If there is no forgetting, the distributed closure grows monotonically.
-/

/-- A MAIS has no forgetting if all agents have perfect memory -/
def MAIS.hasNoForgetting {I T : Type*} [LinearOrder T] (M : MAIS I T) : Prop :=
  M.hasPerfectMemory

/-- The distributed closure grows monotonically when there's no forgetting 
    and agents are immortal (Theorem 8.4). -/
theorem MAIS.distributed_closure_monotone {I : Type*} (M : MAIS I ℕ) 
    (hperfect : M.hasPerfectMemory) (himmortal : M.isImmortal) (t₁ t₂ : ℕ) (h : t₁ ≤ t₂) :
    M.distributedClosure t₁ ⊆ M.distributedClosure t₂ := by
  intro a ha
  simp only [distributedClosure, heldIdeas, Set.mem_setOf_eq] at ha ⊢
  obtain ⟨α, hα, halive₁, ha⟩ := ha
  -- α is also alive at t₂ since immortal
  have halive₂ : α.isAlive t₂ := by
    simp only [Agent.isAlive] at halive₁ ⊢
    constructor
    · exact le_trans halive₁.1 h
    · rw [himmortal α hα]
      exact ExtendedTime.finite_lt_infinite t₂
  -- α still has the idea due to perfect memory
  have hmem : a ∈ α.memory t₂ := by
    apply hperfect α hα t₁ t₂ h halive₁ halive₂
    exact ha
  exact ⟨α, hα, halive₂, hmem⟩

/-! ## Theorem 8.5: Closure Non-Monotonicity with Forgetting

With forgetting, closure can decrease.
-/

/-- A forgetful raw agent: the raw data for an agent that holds an idea at time 0 but not at time 1 -/
def forgetfulRawAgent : RawAgent Unit ℕ where
  agentId := ⟨0⟩
  localIdeas := Set.univ
  generate := fun _ => ∅
  memory := fun t => if t = 0 then {()} else ∅
  birth := 0
  death := ExtendedTime.infinite

/-- A forgetful agent: an agent that holds an idea at time 0 but not at time 1 -/
def forgetfulAgent : Agent Unit ℕ where
  toRawAgent := forgetfulRawAgent
  birth_before_death := ExtendedTime.finite_lt_infinite 0
  memory_in_lifetime := fun _ => Set.subset_univ _
  memory_before_birth := fun t ht => by
    simp only [forgetfulRawAgent]
    have : t < 0 := ht
    omega

/-- The forgetful agent is alive at any time -/
theorem forgetfulAgent_alive (t : ℕ) : forgetfulAgent.isAlive t := by
  simp only [Agent.isAlive, forgetfulAgent]
  exact ⟨Nat.zero_le t, ExtendedTime.finite_lt_infinite t⟩

/-- A RawMAIS with one forgetful agent -/
def forgetfulRawMAIS : RawMAIS Unit ℕ where
  agents := {forgetfulAgent}
  channel := fun _ _ => trivialChannel Unit
  primordials := fun _ => {()}

/-- A MAIS with one forgetful agent -/
def forgetfulMAIS : MAIS Unit ℕ where
  toRawMAIS := forgetfulRawMAIS
  agents_distinct := fun α hα β hβ _ => by
    have hα' : α ∈ ({forgetfulAgent} : Set (Agent Unit ℕ)) := hα
    have hβ' : β ∈ ({forgetfulAgent} : Set (Agent Unit ℕ)) := hβ
    simp only [Set.mem_singleton_iff] at hα' hβ'
    rw [hα', hβ']
  primordials_local := fun α hα => by
    have hα' : α ∈ ({forgetfulAgent} : Set (Agent Unit ℕ)) := hα
    simp only [Set.mem_singleton_iff] at hα'
    subst hα'
    exact Set.subset_univ _
  primordials_in_memory := fun α hα => by
    have hα' : α ∈ ({forgetfulAgent} : Set (Agent Unit ℕ)) := hα
    simp only [Set.mem_singleton_iff] at hα'
    subst hα'
    intro x hx
    have hx' : x ∈ ({()} : Set Unit) := hx
    simp only [Set.mem_singleton_iff] at hx'
    simp only [forgetfulAgent, forgetfulRawAgent, hx', ↓reduceIte, Set.mem_singleton_iff]

/-- The forgetful MAIS holds the unit at time 0 -/
theorem forgetfulMAIS_holds_at_zero : () ∈ forgetfulMAIS.distributedClosure 0 := by
  simp only [MAIS.distributedClosure, MAIS.heldIdeas, RawMAIS.heldIdeas, Set.mem_setOf_eq]
  refine ⟨forgetfulAgent, ?_, forgetfulAgent_alive 0, ?_⟩
  · rfl
  · simp only [forgetfulAgent, forgetfulRawAgent, ↓reduceIte, Set.mem_singleton_iff]

/-- The forgetful MAIS does NOT hold the unit at time 1 -/
theorem forgetfulMAIS_not_holds_at_one : () ∉ forgetfulMAIS.distributedClosure 1 := by
  simp only [MAIS.distributedClosure, MAIS.heldIdeas, RawMAIS.heldIdeas, Set.mem_setOf_eq, not_exists, not_and]
  intro α hα halive
  have hα' : α ∈ ({forgetfulAgent} : Set (Agent Unit ℕ)) := hα
  simp only [Set.mem_singleton_iff] at hα'
  rw [hα']
  simp only [forgetfulAgent, forgetfulRawAgent]
  -- 1 = 0 is false, so memory is ∅
  have : (1 : ℕ) ≠ 0 := Nat.one_ne_zero
  simp only [this, ↓reduceIte, Set.mem_empty_iff_false, not_false_eq_true]

/-- Forgetting can cause closure to shrink (Theorem 8.5).
    This is an existence statement showing non-monotonicity is possible. -/
theorem MAIS.closure_can_shrink_with_forgetting :
    ∃ (I : Type) (M : MAIS I ℕ) (t₁ t₂ : ℕ), t₁ < t₂ ∧ 
      ¬(M.distributedClosure t₁ ⊆ M.distributedClosure t₂) := by
  use Unit, forgetfulMAIS, 0, 1
  constructor
  · exact Nat.zero_lt_one
  · intro h
    have h1 := h forgetfulMAIS_holds_at_zero
    exact forgetfulMAIS_not_holds_at_one h1

/-! ## Theorem 8.6: Eventual Closure Bound

In a finite-agent system with bounded memory and eventual stagnation,
the eventual closure is bounded.
-/

/-- All agents have bounded memory: memory is finite with at most `bound` elements.
    Note: We require explicit finiteness because Set.ncard returns 0 for infinite sets. -/
def MAIS.hasBoundedMemory {I T : Type*} [LinearOrder T] 
    (M : MAIS I T) (bound : ℕ) : Prop :=
  ∀ α ∈ M.agents, ∀ t, (α.memory t).Finite ∧ (α.memory t).ncard ≤ bound

/-- Eventually stagnating: no new ideas after some time -/
def MAIS.eventuallyStagnates {I : Type*} (M : MAIS I ℕ) : Prop :=
  ∃ t₀, ∀ t ≥ t₀, M.distributedClosure t = M.distributedClosure t₀

/-- The distributed closure is contained in the union of agent memories -/
theorem MAIS.distributed_subset_union_memories {I T : Type*} [LinearOrder T]
    (M : MAIS I T) (t : T) : 
    M.distributedClosure t ⊆ ⋃ α ∈ M.agents, α.memory t := by
  intro a ha
  simp only [distributedClosure, heldIdeas, Set.mem_setOf_eq] at ha
  simp only [Set.mem_iUnion]
  obtain ⟨α, hα, _, hmem⟩ := ha
  exact ⟨α, hα, hmem⟩

/-- Bounded memory implies finite memory at each time -/
theorem MAIS.memory_finite_of_bounded {I T : Type*} [LinearOrder T]
    (M : MAIS I T) (bound : ℕ) (hb : M.hasBoundedMemory bound) 
    (α : Agent I T) (hα : α ∈ M.agents) (t : T) : (α.memory t).Finite :=
  (hb α hα t).1

/-- Bounded memory gives the ncard bound -/
theorem MAIS.memory_ncard_of_bounded {I T : Type*} [LinearOrder T]
    (M : MAIS I T) (bound : ℕ) (hb : M.hasBoundedMemory bound) 
    (α : Agent I T) (hα : α ∈ M.agents) (t : T) : (α.memory t).ncard ≤ bound :=
  (hb α hα t).2

/-! ### Helper lemma: ncard of biUnion is bounded by sum of ncards -/

/-- Helper for biUnion bound: version with explicit Finset -/
theorem Set.ncard_biUnion_le_finset {α β : Type*} [DecidableEq α] (s : Finset α) (f : α → Set β)
    (hf : ∀ a ∈ s, (f a).Finite) :
    (⋃ a ∈ (s : Set α), f a).ncard ≤ ∑ a ∈ s, (f a).ncard := by
  induction s using Finset.induction_on with
  | empty => 
    simp only [Finset.coe_empty, Set.biUnion_empty, Set.ncard_empty, Finset.sum_empty, le_refl]
  | @insert x s hxs ih =>
    have hf' : ∀ a ∈ s, (f a).Finite := fun a ha => hf a (Finset.mem_insert_of_mem ha)
    have hfx : (f x).Finite := hf x (Finset.mem_insert_self x s)
    simp only [Finset.coe_insert, Set.biUnion_insert]
    calc (f x ∪ ⋃ a ∈ (s : Set α), f a).ncard 
        ≤ (f x).ncard + (⋃ a ∈ (s : Set α), f a).ncard := Set.ncard_union_le _ _
      _ ≤ (f x).ncard + ∑ a ∈ s, (f a).ncard := Nat.add_le_add_left (ih hf') _
      _ = ∑ a ∈ insert x s, (f a).ncard := by rw [Finset.sum_insert hxs]

/-- The ncard of a biUnion over a finite index set is bounded by the sum of ncards.
    This is a general lemma that Mathlib doesn't have directly for Set.ncard. -/
theorem Set.ncard_biUnion_le {α β : Type*} {s : Set α} {f : α → Set β}
    (hs : s.Finite) (hf : ∀ a ∈ s, (f a).Finite) :
    (⋃ a ∈ s, f a).ncard ≤ ∑ a ∈ hs.toFinset, (f a).ncard := by
  classical
  have h := ncard_biUnion_le_finset hs.toFinset f (fun a ha => hf a (hs.mem_toFinset.mp ha))
  convert h using 2
  ext x
  simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, Finset.mem_coe]

/-- Eventual closure bound (Theorem 8.6).
    In a finite-agent system with bounded memory, the distributed closure 
    at any time is bounded by |agents| * memory_bound. -/
theorem MAIS.eventual_closure_bound {I : Type*} (M : MAIS I ℕ) 
    (hfinite : M.isFinite) (hbound : ∃ b, M.hasBoundedMemory b) :
    ∃ bound, ∀ t, (M.distributedClosure t).ncard ≤ bound := by
  obtain ⟨b, hb⟩ := hbound
  -- The bound is |agents| * b
  use M.agents.ncard * b
  intro t
  -- The distributed closure is contained in the union of agent memories
  have hsub : M.distributedClosure t ⊆ ⋃ α ∈ M.agents, α.memory t := 
    distributed_subset_union_memories M t
  -- Each agent memory is finite
  have hmem_fin : ∀ α ∈ M.agents, (α.memory t).Finite := 
    fun α hα => memory_finite_of_bounded M b hb α hα t
  -- The union has bounded cardinality
  have hfin_union : (⋃ α ∈ M.agents, α.memory t).Finite := 
    Set.Finite.biUnion hfinite hmem_fin
  -- Distributed closure is also finite (subset of finite)
  have hfin_dist : (M.distributedClosure t).Finite := Set.Finite.subset hfin_union hsub
  -- Use subset monotonicity for ncard
  have h1 : (M.distributedClosure t).ncard ≤ (⋃ α ∈ M.agents, α.memory t).ncard := 
    Set.ncard_le_ncard hsub hfin_union
  -- Bound the union's cardinality using the standard inequality for unions
  have h2 : (⋃ α ∈ M.agents, α.memory t).ncard ≤ M.agents.ncard * b := by
    -- We proceed by using Set.ncard_biUnion_le and then bounding the sum
    have hle : (⋃ α ∈ M.agents, α.memory t).ncard ≤ 
               ∑ α ∈ hfinite.toFinset, (α.memory t).ncard := 
      Set.ncard_biUnion_le hfinite hmem_fin
    have hsum_le : ∑ α ∈ hfinite.toFinset, (α.memory t).ncard ≤ 
                   hfinite.toFinset.card * b := by
      apply Finset.sum_le_card_nsmul
      intro α hα
      exact (hb α (hfinite.mem_toFinset.mp hα) t).2
    have hcard : hfinite.toFinset.card = M.agents.ncard := 
      (Set.ncard_eq_toFinset_card M.agents hfinite).symm
    calc (⋃ α ∈ M.agents, α.memory t).ncard 
        ≤ ∑ α ∈ hfinite.toFinset, (α.memory t).ncard := hle
      _ ≤ hfinite.toFinset.card * b := hsum_le
      _ = M.agents.ncard * b := by rw [hcard]
  exact le_trans h1 h2

/-! ## Additional Closure Properties -/

/-- Ideas in the distributed closure at t are held by some agent at t -/
theorem MAIS.mem_distributed_iff {I T : Type*} [LinearOrder T] 
    (M : MAIS I T) (t : T) (a : I) :
    a ∈ M.distributedClosure t ↔ ∃ α ∈ M.agents, α.isAlive t ∧ a ∈ α.memory t := by
  rfl

/-- If no agent is alive, the distributed closure is empty -/
theorem MAIS.distributed_empty_of_no_living {I T : Type*} [LinearOrder T] 
    (M : MAIS I T) (t : T) (h : M.livingAgents t = ∅) :
    M.distributedClosure t = ∅ := by
  ext a
  simp only [distributedClosure, heldIdeas, RawMAIS.heldIdeas, Set.mem_setOf_eq, Set.mem_empty_iff_false,
             iff_false, not_exists, not_and]
  intro α hα halive hmem
  have : α ∈ M.livingAgents t := ⟨hα, halive⟩
  rw [h] at this
  exact Set.not_mem_empty α this

/-- The distributed closure at origin contains all primordials -/
theorem MAIS.primordials_in_initial_closure {I : Type*} (M : MAIS I ℕ) :
    ∀ α ∈ M.agents, α.birth = 0 → M.primordials α ⊆ M.distributedClosure 0 := by
  intro α hα hbirth a ha
  simp only [distributedClosure, heldIdeas, Set.mem_setOf_eq]
  have hmem : a ∈ α.memory α.birth := M.primordials_in_memory α hα ha
  rw [hbirth] at hmem
  have halive : α.isAlive 0 := by
    simp only [Agent.isAlive]
    constructor
    · rw [← hbirth]
    · rw [← hbirth]; exact α.birth_before_death
  exact ⟨α, hα, halive, hmem⟩

end CollectiveIdeogenesis
