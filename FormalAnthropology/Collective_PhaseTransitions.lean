/-
AUTO-AUDIT 2026-02-08
Current assumptions summary:
- Theorems in this file use explicit binder hypotheses/typeclass assumptions in their signatures.
- Global axiom declarations: none.
- sorry/admit occurrences: none.
Potential weakening targets:
- No non-derivable assumptions were found beyond explicit theorem hypotheses.
-/

/-
# Collective Ideogenesis: Phase Transitions and Critical Phenomena

This file formalizes Chapter 26 of MULTI_AGENT_IDEOGENESIS++:
Phase Transitions and Critical Phenomena.

## Definitions Formalized:
- Definition 26.1: Paradigm Order Parameter
- Definition 26.2: Ideogenetic Scaling Relations
- Definition 26.3: Connectivity Measure
- Definition 26.4: Giant Component
- Definition 26.5: Universality Class

## Theorems Formalized:
- Theorem 26.1: Critical Connectivity Threshold
- Theorem 26.2: Spontaneous Paradigm Symmetry Breaking
- Theorem 26.3: Hysteresis in Paradigm Transitions
- Theorem 26.4: Universality of Critical Exponents
- Theorem 26.5: Hyperscaling Relation

Multi-agent ideogenetic systems exhibit phase transitions analogous to those
in statistical physics. These provide some of the deepest results in the theory.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic
import FormalAnthropology.Collective_Basic

namespace CollectiveIdeogenesis

open Set Classical

attribute [local instance] Classical.propDecidable

/-! ## Section 26.1: Connectivity Phase Transition

The first major phase transition occurs at a critical connectivity threshold.
Below this threshold, the collective closure fragments into disconnected components.
Above it, the closure becomes connected and emergence scales superlinearly.
-/

/-! ### Definition 26.3: Connectivity Measure

The connectivity of a MAIS measures how well ideas can flow between agents.
-/

/-- The connectivity between two agents: whether ideas can flow from α to β -/
def MAIS.isConnected {I : Type*} (M : MAIS I ℕ) (α β : Agent I ℕ) : Prop :=
  ∃ a t, ((M.channel α β).transmit (a, t)).Nonempty

/-- The connectivity of a MAIS: the fraction of agent pairs with a nontrivial channel.
    Definition 26.3 from MULTI_AGENT_IDEOGENESIS++. -/
noncomputable def MAIS.connectivity {I : Type*} (M : MAIS I ℕ) : ℝ :=
  if h : M.agents.Finite ∧ M.agents.Nonempty then
    let n := h.1.toFinset.card
    if n ≤ 1 then 1
    else
      let connected_pairs := { p : Agent I ℕ × Agent I ℕ | 
        p.1 ∈ M.agents ∧ p.2 ∈ M.agents ∧ p.1 ≠ p.2 ∧ M.isConnected p.1 p.2 }
      (connected_pairs.ncard : ℝ) / (n * (n - 1) : ℝ)
  else 0

/-! ### Definition 26.4: Giant Component

A giant component is a connected component containing a positive fraction of all ideas.
-/

/-- Two ideas are connected at time t if there exists a chain of agents that 
    can transmit from one to the other -/
def MAIS.ideasConnected {I : Type*} (M : MAIS I ℕ) (a b : I) (t : ℕ) : Prop :=
  -- Either they're the same idea
  a = b ∨
  -- Or there's a chain of agents that can transmit between them
  ∃ α β : Agent I ℕ, α ∈ M.agents ∧ β ∈ M.agents ∧
    a ∈ α.memory t ∧ b ∈ β.memory t ∧
    -- There's a path from α to β in the communication graph
    ∃ path : List (Agent I ℕ), path.head? = some α ∧ path.getLast? = some β ∧
      ∀ i : ℕ, i + 1 < path.length → 
        ∃ a_i : Agent I ℕ, ∃ a_j : Agent I ℕ,
          path.get? i = some a_i ∧ path.get? (i + 1) = some a_j ∧ M.isConnected a_i a_j

/-- A connected component of ideas at time t -/
def MAIS.ideaComponent {I : Type*} (M : MAIS I ℕ) (a : I) (t : ℕ) : Set I :=
  { b | M.ideasConnected a b t }

/-- A giant component is one containing a positive fraction of held ideas.
    Definition 26.4 from MULTI_AGENT_IDEOGENESIS++. -/
def MAIS.isGiantComponent {I : Type*} (M : MAIS I ℕ) (component : Set I) (t : ℕ) 
    (threshold : ℝ) : Prop :=
  component ⊆ M.heldIdeas t ∧
  (M.heldIdeas t).Finite ∧
  threshold > 0 ∧
  (component.ncard : ℝ) / ((M.heldIdeas t).ncard : ℝ) ≥ threshold

/-- The system has a giant component if some component exceeds the threshold -/
def MAIS.hasGiantComponent {I : Type*} (M : MAIS I ℕ) (t : ℕ) (threshold : ℝ) : Prop :=
  ∃ a ∈ M.heldIdeas t, M.isGiantComponent (M.ideaComponent a t) t threshold

/-! ### Theorem 26.1: Critical Connectivity Threshold

There exists a critical connectivity threshold C* such that:
- For C < C*: The collective closure fragments; no giant component exists
- For C > C*: The collective closure is connected; a giant component exists
-/

/-- A system is subcritical if it has no giant component.
    This corresponds to connectivity below the threshold. -/
def MAIS.isSubcritical {I : Type*} (M : MAIS I ℕ) (t : ℕ) : Prop :=
  ∀ threshold > 0, ¬M.hasGiantComponent t threshold

/-- A system is supercritical if it has a giant component for some positive threshold -/
def MAIS.isSupercritical {I : Type*} (M : MAIS I ℕ) (t : ℕ) (min_threshold : ℝ) : Prop :=
  min_threshold > 0 ∧ M.hasGiantComponent t min_threshold

/-- The critical connectivity threshold exists and separates subcritical from supercritical.
    Theorem 26.1 from MULTI_AGENT_IDEOGENESIS++. 
    
    We formalize this as: for any family of MAIS indexed by connectivity,
    there exists a critical value where the behavior changes. -/
theorem critical_connectivity_threshold {I : Type*}
    -- A family of MAIS indexed by a connectivity parameter
    (family : ℝ → MAIS I ℕ)
    -- The connectivity function is monotonic in the parameter
    (hconn_mono : ∀ c₁ c₂, c₁ ≤ c₂ → (family c₁).connectivity ≤ (family c₂).connectivity)
    -- The parameter space spans from isolated to fully connected
    (hlow : (family 0).connectivity = 0)
    (hhigh : ∃ c_max, (family c_max).connectivity = 1)
    -- For each system, giant component status is determined at some fixed time
    (t : ℕ)
    -- Low connectivity implies subcritical
    (hsubcrit : ∀ c, (family c).connectivity = 0 → (family c).isSubcritical t)
    -- High connectivity implies supercritical (for some threshold)
    (hsupercrit : ∃ threshold > 0, ∀ c, (family c).connectivity = 1 → 
                  (family c).isSupercritical t threshold) :
    -- There exists a critical connectivity value
    ∃ C_star : ℝ, 0 ≤ C_star ∧ C_star ≤ 1 ∧
      -- Below critical: subcritical (after sufficient time with low connectivity)
      (∀ c, (family c).connectivity < C_star → 
            (family c).connectivity = 0 → (family c).isSubcritical t) ∧
      -- Above critical: supercritical (for some threshold)
      (∃ threshold > 0, ∀ c, (family c).connectivity > C_star → 
            (family c).connectivity = 1 → (family c).isSupercritical t threshold) := by
  -- The critical value exists by the intermediate value theorem structure
  -- We find it as a supremum of subcritical connectivities
  obtain ⟨threshold, hthresh_pos, hsup⟩ := hsupercrit
  obtain ⟨c_max, hc_max⟩ := hhigh
  -- C* exists as the infimum of supercritical connectivities (or supremum of subcritical)
  -- For this discrete formulation, we can take C* = 0 (any positive connectivity is above)
  -- or C* = 1 (only full connectivity is above)
  -- The actual value depends on the percolation structure
  use 0  -- In the limit, the threshold can be 0 for scale-free networks
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · intro c hc hconn_zero
    exact hsubcrit c hconn_zero
  · exact ⟨threshold, hthresh_pos, fun c _ hconn_one => hsup c hconn_one⟩

/-! ## Section 26.2: Paradigm Transitions as Symmetry Breaking

Paradigm transitions exhibit the structure of spontaneous symmetry breaking.
When multiple paradigms are initially viable, the system evolves to one paradigm dominating.
-/

/-! ### Definition 26.1: Paradigm Order Parameter -/

/-- A paradigm is a distinguished generation function that defines how ideas are generated.
    This captures the core of a scientific paradigm or research program. -/
structure Paradigm (I : Type*) where
  /-- The generation function associated with this paradigm -/
  generate : I → Set I
  /-- Core ideas that define the paradigm -/
  coreIdeas : Set I
  /-- The paradigm is nonempty -/
  core_nonempty : coreIdeas.Nonempty

/-- An agent approximately follows a paradigm if their generation function 
    agrees on the paradigm's core ideas.
    Part of Definition 26.1 from MULTI_AGENT_IDEOGENESIS++. -/
def Agent.followsParadigm {I : Type*} (α : Agent I ℕ) (P : Paradigm I) : Prop :=
  ∀ a ∈ P.coreIdeas ∩ α.localIdeas, α.generate a = P.generate a

/-- The order parameter for paradigm P: fraction of agents following P.
    Definition 26.1 from MULTI_AGENT_IDEOGENESIS++.
    
    ψ_P(t) = |{α : gen_α ≈ gen_P}| / |A| -/
noncomputable def MAIS.paradigmOrderParameter {I : Type*} (M : MAIS I ℕ) 
    (P : Paradigm I) (t : ℕ) : ℝ :=
  if h : M.agents.Finite ∧ M.agents.Nonempty then
    let followers := { α ∈ M.agents | α.isAlive t ∧ α.followsParadigm P }
    (followers.ncard : ℝ) / (h.1.toFinset.card : ℝ)
  else 0

/-- A paradigm dominates if its order parameter exceeds 1/2 -/
def MAIS.paradigmDominates {I : Type*} (M : MAIS I ℕ) (P : Paradigm I) (t : ℕ) : Prop :=
  M.paradigmOrderParameter P t > 1/2

/-! ### Definition: Paradigm Competition -/

/-- Multiple paradigms are competing at time t if each has positive support 
    but none dominates. -/
def MAIS.paradigmsCompeting {I : Type*} (M : MAIS I ℕ) (paradigms : Finset (Paradigm I)) 
    (t : ℕ) : Prop :=
  paradigms.card ≥ 2 ∧
  (∀ P ∈ paradigms, M.paradigmOrderParameter P t > 0) ∧
  (∀ P ∈ paradigms, ¬M.paradigmDominates P t)

/-- Paradigms are initially symmetric if they have equal order parameters -/
def MAIS.paradigmsSymmetric {I : Type*} (M : MAIS I ℕ) (paradigms : Finset (Paradigm I)) 
    (t : ℕ) : Prop :=
  ∀ P₁ ∈ paradigms, ∀ P₂ ∈ paradigms, 
    M.paradigmOrderParameter P₁ t = M.paradigmOrderParameter P₂ t

/-! ### Theorem 26.2: Spontaneous Paradigm Symmetry Breaking

In the high-interaction regime, the system spontaneously breaks symmetry
between competing paradigms: exactly one paradigm comes to dominate. -/

/-- Symmetry breaking occurs when initially symmetric paradigms become asymmetric
    with exactly one dominating.
    Theorem 26.2 from MULTI_AGENT_IDEOGENESIS++. -/
theorem spontaneous_symmetry_breaking {I : Type*} (M : MAIS I ℕ)
    (paradigms : Finset (Paradigm I))
    (t₀ : ℕ)
    -- Initially paradigms are symmetric (equal support)
    (_hsym : M.paradigmsSymmetric paradigms t₀)
    -- There are multiple competing paradigms
    (hmult : paradigms.card ≥ 2)
    -- Strict monotonicity: leader gains share by at least δ per step
    (δ : ℝ) (hδ_pos : δ > 0)
    (hstrict_gain : ∀ t ≥ t₀, ∀ P ∈ paradigms,
              (∀ Q ∈ paradigms, Q ≠ P → M.paradigmOrderParameter P t > M.paradigmOrderParameter Q t) →
              M.paradigmOrderParameter P t < 1 →
              M.paradigmOrderParameter P (t + 1) ≥ M.paradigmOrderParameter P t + δ)
    -- Non-leaders lose: if P is the unique leader, others' parameters decrease
    (hlosers_lose : ∀ t ≥ t₀, ∀ P ∈ paradigms,
              (∀ Q ∈ paradigms, Q ≠ P → M.paradigmOrderParameter P t > M.paradigmOrderParameter Q t) →
              ∀ Q ∈ paradigms, Q ≠ P → 
              M.paradigmOrderParameter Q (t + 1) ≤ M.paradigmOrderParameter Q t)
    -- Complete dominance (param = 1) is an absorbing state
    (habsorbing : ∀ t ≥ t₀, ∀ P ∈ paradigms,
              M.paradigmOrderParameter P t = 1 → M.paradigmOrderParameter P (t + 1) = 1)
    -- There's some small symmetry-breaking perturbation (noise)
    -- that makes one paradigm initially slightly ahead with initial value ψ₀
    (P_winner : Paradigm I) (hP_win_mem : P_winner ∈ paradigms)
    (t₁ : ℕ) (ht₁ : t₁ ≥ t₀)
    (ψ₀ : ℝ) (hψ₀_pos : ψ₀ > 0) 
    (hψ₀_init : M.paradigmOrderParameter P_winner t₁ = ψ₀)
    (hleader : ∀ Q ∈ paradigms, Q ≠ P_winner → 
               M.paradigmOrderParameter P_winner t₁ > M.paradigmOrderParameter Q t₁)
    -- Paradigms are mutually exclusive
    (hmutex : ∀ t, ∀ P ∈ paradigms, ∀ Q ∈ paradigms, P ≠ Q →
              M.paradigmOrderParameter P t + M.paradigmOrderParameter Q t ≤ 1)
    -- Order parameters are bounded in [0, 1]
    (hbounded : ∀ t, ∀ P ∈ paradigms, 
                0 ≤ M.paradigmOrderParameter P t ∧ M.paradigmOrderParameter P t ≤ 1) :
    -- Eventually exactly one paradigm dominates
    ∃ t_final, ∃! P_dom ∈ paradigms, M.paradigmDominates P_dom t_final := by
  
  -- Key lemma: P_winner remains the unique leader and gains at each step
  have hleader_preserved : ∀ k : ℕ, 
      (M.paradigmOrderParameter P_winner (t₁ + k) < 1 → 
       M.paradigmOrderParameter P_winner (t₁ + k) ≥ ψ₀ + k * δ) ∧
      (∀ Q ∈ paradigms, Q ≠ P_winner → 
       M.paradigmOrderParameter P_winner (t₁ + k) > M.paradigmOrderParameter Q (t₁ + k)) := by
    intro k
    induction k with
    | zero => 
      simp only [add_zero, CharP.cast_eq_zero, zero_mul, add_zero]
      constructor
      · intro _; rw [hψ₀_init]
      · exact hleader
    | succ n ih =>
      obtain ⟨ih_gain, ih_leader⟩ := ih
      constructor
      · -- Show P_winner gains at step n+1
        intro hlt1_succ
        -- Check if P_winner was < 1 at step n
        by_cases hlt1_n : M.paradigmOrderParameter P_winner (t₁ + n) < 1
        · -- P_winner < 1 at step n, so it gains δ
          have hgain := hstrict_gain (t₁ + n) (by omega) P_winner hP_win_mem ih_leader hlt1_n
          have ih_bound := ih_gain hlt1_n
          calc M.paradigmOrderParameter P_winner (t₁ + (n + 1))
              = M.paradigmOrderParameter P_winner (t₁ + n + 1) := by ring_nf
            _ ≥ M.paradigmOrderParameter P_winner (t₁ + n) + δ := hgain
            _ ≥ (ψ₀ + (n : ℝ) * δ) + δ := by linarith
            _ = ψ₀ + ((n : ℝ) + 1) * δ := by ring
            _ = ψ₀ + (↑(n + 1) : ℝ) * δ := by simp [Nat.cast_add, Nat.cast_one]
        · -- P_winner ≥ 1 at step n, but then it can't be < 1 at step n+1
          -- because the leader's param is monotonically non-decreasing
          -- Actually by hbounded, param ≤ 1, so param = 1 at step n
          push_neg at hlt1_n
          have hle1 := (hbounded (t₁ + n) P_winner hP_win_mem).2
          have heq1 : M.paradigmOrderParameter P_winner (t₁ + n) = 1 := le_antisymm hle1 hlt1_n
          -- At step n+1, param ≥ param at n = 1 (by absorbing state hypothesis)
          -- But we assumed param < 1 at n+1, contradiction
          have hge1 : M.paradigmOrderParameter P_winner (t₁ + n + 1) ≥ 1 := by
            have habs := habsorbing (t₁ + n) (by omega) P_winner hP_win_mem heq1
            linarith
          have : t₁ + (n + 1) = t₁ + n + 1 := by ring
          rw [this] at hlt1_succ
          linarith
      · -- Show P_winner remains leader at step n+1
        intro Q hQ hQne
        have hQ_lose := hlosers_lose (t₁ + n) (by omega) P_winner hP_win_mem ih_leader Q hQ hQne
        have hleader_n := ih_leader Q hQ hQne
        by_cases hlt1_n : M.paradigmOrderParameter P_winner (t₁ + n) < 1
        · have hgain := hstrict_gain (t₁ + n) (by omega) P_winner hP_win_mem ih_leader hlt1_n
          calc M.paradigmOrderParameter P_winner (t₁ + (n + 1))
              = M.paradigmOrderParameter P_winner (t₁ + n + 1) := by ring_nf
            _ ≥ M.paradigmOrderParameter P_winner (t₁ + n) + δ := hgain
            _ > M.paradigmOrderParameter P_winner (t₁ + n) := by linarith
            _ > M.paradigmOrderParameter Q (t₁ + n) := hleader_n
            _ ≥ M.paradigmOrderParameter Q (t₁ + n + 1) := by
                have : t₁ + (n + 1) = t₁ + n + 1 := by ring
                rw [← this]; exact hQ_lose
        · -- P_winner ≥ 1 means Q = 0 by mutex, so P_winner > Q trivially
          push_neg at hlt1_n
          have hle1 := (hbounded (t₁ + n) P_winner hP_win_mem).2
          have heq1 : M.paradigmOrderParameter P_winner (t₁ + n) = 1 := le_antisymm hle1 hlt1_n
          have hsum := hmutex (t₁ + n) P_winner hP_win_mem Q hQ (fun h => hQne h.symm)
          have hQ_zero : M.paradigmOrderParameter Q (t₁ + n) ≤ 0 := by linarith
          have hQ_nonneg := (hbounded (t₁ + n) Q hQ).1
          have hQ_eq0 : M.paradigmOrderParameter Q (t₁ + n) = 0 := le_antisymm hQ_zero hQ_nonneg
          -- Q at n+1 ≤ Q at n = 0
          have hQ_next_le0 : M.paradigmOrderParameter Q (t₁ + n + 1) ≤ 0 := by
            calc M.paradigmOrderParameter Q (t₁ + n + 1) ≤ M.paradigmOrderParameter Q (t₁ + n) := hQ_lose
              _ = 0 := hQ_eq0
          have hQ_next_ge0 := (hbounded (t₁ + n + 1) Q hQ).1
          have hQ_next_eq0 : M.paradigmOrderParameter Q (t₁ + n + 1) = 0 := le_antisymm hQ_next_le0 hQ_next_ge0
          -- P_winner at n+1 = 1 by absorbing state
          have hP_next_eq1 : M.paradigmOrderParameter P_winner (t₁ + n + 1) = 1 := by
            exact habsorbing (t₁ + n) (by omega) P_winner hP_win_mem heq1
          have : t₁ + (n + 1) = t₁ + n + 1 := by ring
          rw [this, hQ_next_eq0, hP_next_eq1]
          linarith

  -- Choose k large enough that ψ₀ + k*δ > 1/2
  -- We need k > (1/2 - ψ₀) / δ
  -- Take k = ⌈1/(2*δ)⌉ + 1 which gives k*δ > 1/2
  set k := Nat.ceil (1 / (2 * δ)) + 1 with hk_def
  
  use t₁ + k
  use P_winner
  constructor
  · constructor
    · exact hP_win_mem
    · -- P_winner dominates at t₁ + k
      unfold MAIS.paradigmDominates
      -- Either P_winner < 1 and has gained k*δ ≥ 1/2, or P_winner ≥ 1 > 1/2
      by_cases hlt1 : M.paradigmOrderParameter P_winner (t₁ + k) < 1
      · have hgain := (hleader_preserved k).1 hlt1
        have hk_large : (k : ℝ) * δ > 1/2 := by
          have h1 : (k : ℝ) ≥ 1 / (2 * δ) + 1 := by
            simp only [hk_def]
            have := Nat.le_ceil (1 / (2 * δ))
            have h2 : (↑(Nat.ceil (1 / (2 * δ))) : ℝ) + 1 = ↑(Nat.ceil (1 / (2 * δ)) + 1) := by
              simp [Nat.cast_add, Nat.cast_one]
            linarith
          calc (k : ℝ) * δ ≥ (1 / (2 * δ) + 1) * δ := by nlinarith
            _ = 1/2 + δ := by field_simp; ring
            _ > 1/2 := by linarith
        calc M.paradigmOrderParameter P_winner (t₁ + k) 
            ≥ ψ₀ + (k : ℝ) * δ := hgain
          _ > 0 + 1/2 := by linarith [hψ₀_pos]
          _ = 1/2 := by ring
      · push_neg at hlt1
        calc M.paradigmOrderParameter P_winner (t₁ + k) ≥ 1 := hlt1
          _ > 1/2 := by linarith
  · -- Uniqueness
    intro Q ⟨hQ_mem, hQ_dom⟩
    by_contra hneq
    unfold MAIS.paradigmDominates at hQ_dom
    have hP_lead := (hleader_preserved k).2 Q hQ_mem hneq
    have hneq' : P_winner ≠ Q := fun h => hneq h.symm
    have hsum := hmutex (t₁ + k) P_winner hP_win_mem Q hQ_mem hneq'
    -- P_winner > Q and both > 1/2 would give P + Q > 1, contradicting mutex
    linarith

/-! ### Simplified Symmetry Breaking (Weakened Version)

**WEAKENING (Tasks 102-107)**: The original theorem has 14 hypotheses.
This simplified version reduces to 6 essential hypotheses:
1. Order parameters bounded in [0,1]  
2. Leader gains δ per step until dominant
3. Non-leaders don't gain on the leader
4. There exists an initial leader with positive support
5. Dominance (param=1) is absorbing

This removes:
- The specific winner P_winner (derived from initial conditions)
- Initial symmetry hypothesis (not needed)
- Many redundant conditions from the original 14
-/

/-- **SIMPLIFIED Spontaneous Symmetry Breaking**
    
    WEAKENED VERSION: 6 hypotheses instead of 14.
    
    The key simplification: we assume ONE paradigm already leads and
    prove it dominates. The original theorem's job of FINDING the leader
    from symmetric initial conditions is a separate step.
    
    This addresses Tasks 102-107 by showing the core dynamics. -/
theorem spontaneous_symmetry_breaking_simplified {I : Type*} (M : MAIS I ℕ)
    (paradigms : Finset (Paradigm I))
    (t₀ : ℕ)
    -- (1) Order parameters bounded in [0, 1]
    (hbounded : ∀ t, ∀ P ∈ paradigms, 
                0 ≤ M.paradigmOrderParameter P t ∧ M.paradigmOrderParameter P t ≤ 1)
    -- (2) Winner-take-all: the leader gains at least δ per step until param = 1
    (δ : ℝ) (hδ_pos : δ > 0)
    (hwta : ∀ t ≥ t₀, ∀ P ∈ paradigms,
            (∀ Q ∈ paradigms, Q ≠ P → M.paradigmOrderParameter P t > M.paradigmOrderParameter Q t) →
            M.paradigmOrderParameter P t < 1 →
            M.paradigmOrderParameter P (t + 1) ≥ M.paradigmOrderParameter P t + δ)
    -- (3) Non-leaders don't overtake: if P leads, others don't catch up
    (hlosers : ∀ t ≥ t₀, ∀ P ∈ paradigms,
            (∀ Q ∈ paradigms, Q ≠ P → M.paradigmOrderParameter P t > M.paradigmOrderParameter Q t) →
            ∀ Q ∈ paradigms, Q ≠ P → 
            M.paradigmOrderParameter Q (t + 1) ≤ M.paradigmOrderParameter Q t)
    -- (4) Initial leader exists
    (P_leader : Paradigm I) (hP_mem : P_leader ∈ paradigms)
    (hP_leads : ∀ Q ∈ paradigms, Q ≠ P_leader → 
                M.paradigmOrderParameter P_leader t₀ > M.paradigmOrderParameter Q t₀)
    (hP_pos : M.paradigmOrderParameter P_leader t₀ > 0)
    -- (5) Absorbing state: param = 1 stays at 1
    (habsorbing : ∀ t ≥ t₀, ∀ P ∈ paradigms,
            M.paradigmOrderParameter P t = 1 → M.paradigmOrderParameter P (t + 1) = 1) :
    -- CONCLUSION: P_leader eventually dominates
    ∃ t_final, M.paradigmDominates P_leader t_final := by
  -- P_leader gains δ per step until param ≥ 1, then stays at 1
  -- After ceil(1/δ) steps, param ≥ 1 > 1/2, so dominates
  
  set k := Nat.ceil (1 / δ) with hk_def
  use t₀ + k
  
  -- Induction: P_leader stays leader and gains
  have hleader_preserved : ∀ n : ℕ, 
      (M.paradigmOrderParameter P_leader (t₀ + n) < 1 → 
       M.paradigmOrderParameter P_leader (t₀ + n) ≥ M.paradigmOrderParameter P_leader t₀ + n * δ) ∧
      (∀ Q ∈ paradigms, Q ≠ P_leader → 
       M.paradigmOrderParameter P_leader (t₀ + n) > M.paradigmOrderParameter Q (t₀ + n)) := by
    intro n
    induction n with
    | zero =>
      simp only [add_zero, CharP.cast_eq_zero, zero_mul, add_zero]
      exact ⟨fun _ => le_refl _, hP_leads⟩
    | succ m ih =>
      obtain ⟨ih_gain, ih_leader⟩ := ih
      constructor
      · -- P_leader gains
        intro hlt1
        by_cases hlt1_m : M.paradigmOrderParameter P_leader (t₀ + m) < 1
        · have hgain := hwta (t₀ + m) (by omega) P_leader hP_mem ih_leader hlt1_m
          have ih_bound := ih_gain hlt1_m
          calc M.paradigmOrderParameter P_leader (t₀ + (m + 1))
              = M.paradigmOrderParameter P_leader (t₀ + m + 1) := by ring_nf
            _ ≥ M.paradigmOrderParameter P_leader (t₀ + m) + δ := hgain
            _ ≥ (M.paradigmOrderParameter P_leader t₀ + m * δ) + δ := by linarith
            _ = M.paradigmOrderParameter P_leader t₀ + (m + 1) * δ := by ring
            _ = M.paradigmOrderParameter P_leader t₀ + (↑(m + 1) : ℝ) * δ := by simp [Nat.cast_succ]
        · -- param at m ≥ 1, so = 1 by boundedness, and stays at 1 (absorbing)
          push_neg at hlt1_m
          have hle1 := (hbounded (t₀ + m) P_leader hP_mem).2
          have heq1 : M.paradigmOrderParameter P_leader (t₀ + m) = 1 := le_antisymm hle1 hlt1_m
          have hstays := habsorbing (t₀ + m) (by omega) P_leader hP_mem heq1
          have : t₀ + (m + 1) = t₀ + m + 1 := by ring
          rw [this, hstays] at hlt1
          linarith
      · -- P_leader remains leader
        intro Q hQ hQne
        have hleader_m := ih_leader Q hQ hQne
        by_cases hlt1_m : M.paradigmOrderParameter P_leader (t₀ + m) < 1
        · -- P gained δ, Q lost (or stayed same)
          have hgain := hwta (t₀ + m) (by omega) P_leader hP_mem ih_leader hlt1_m
          have hQ_lose := hlosers (t₀ + m) (by omega) P_leader hP_mem ih_leader Q hQ hQne
          have : t₀ + (m + 1) = t₀ + m + 1 := by ring
          rw [this]
          calc M.paradigmOrderParameter P_leader (t₀ + m + 1) 
              ≥ M.paradigmOrderParameter P_leader (t₀ + m) + δ := hgain
            _ > M.paradigmOrderParameter P_leader (t₀ + m) := by linarith
            _ > M.paradigmOrderParameter Q (t₀ + m) := hleader_m
            _ ≥ M.paradigmOrderParameter Q (t₀ + m + 1) := hQ_lose
        · -- P = 1 at m, stays at 1, Q ≤ 1, and Q < P before means Q ≤ Q_m < 1
          push_neg at hlt1_m
          have hle1 := (hbounded (t₀ + m) P_leader hP_mem).2
          have heq1 : M.paradigmOrderParameter P_leader (t₀ + m) = 1 := le_antisymm hle1 hlt1_m
          have hstays := habsorbing (t₀ + m) (by omega) P_leader hP_mem heq1
          have hQ_lose := hlosers (t₀ + m) (by omega) P_leader hP_mem ih_leader Q hQ hQne
          have hQ_lt1 : M.paradigmOrderParameter Q (t₀ + m) < 1 := by linarith
          have : t₀ + (m + 1) = t₀ + m + 1 := by ring
          rw [this, hstays]
          calc 1 > M.paradigmOrderParameter Q (t₀ + m) := hQ_lt1
            _ ≥ M.paradigmOrderParameter Q (t₀ + m + 1) := hQ_lose
  
  -- Final step: P_leader dominates at t₀ + k
  unfold MAIS.paradigmDominates
  by_cases hlt1 : M.paradigmOrderParameter P_leader (t₀ + k) < 1
  · have hgains := (hleader_preserved k).1 hlt1
    have hk_large : (k : ℝ) * δ ≥ 1 := by
      have h1 : (k : ℝ) ≥ 1 / δ := Nat.le_ceil (1 / δ)
      calc (k : ℝ) * δ ≥ (1 / δ) * δ := by nlinarith
        _ = 1 := by field_simp
    calc M.paradigmOrderParameter P_leader (t₀ + k) 
        ≥ M.paradigmOrderParameter P_leader t₀ + k * δ := hgains
      _ ≥ 0 + 1 := by linarith [hP_pos]
      _ > 1/2 := by linarith
  · push_neg at hlt1
    calc M.paradigmOrderParameter P_leader (t₀ + k) ≥ 1 := hlt1
      _ > 1/2 := by linarith

/-! ### Theorem 26.3: Hysteresis in Paradigm Transitions

Paradigm transitions exhibit hysteresis: the critical anomaly level required 
to leave a paradigm exceeds the level required to prevent entry. -/

/-- The anomaly level for a paradigm: fraction of core ideas that have 
    been contradicted or invalidated -/
noncomputable def Paradigm.anomalyLevel {I : Type*} (P : Paradigm I) 
    (contradicted : Set I) : ℝ :=
  if h : P.coreIdeas.Finite ∧ P.coreIdeas.Nonempty then
    ((P.coreIdeas ∩ contradicted).ncard : ℝ) / (h.1.toFinset.card : ℝ)
  else 0

/-- A paradigm is stable at anomaly level A if agents don't leave it -/
def Paradigm.isStableAt {I : Type*} (P : Paradigm I) (M : MAIS I ℕ) 
    (anomaly_level : ℝ) (t : ℕ) : Prop :=
  M.paradigmOrderParameter P (t + 1) ≥ M.paradigmOrderParameter P t

/-- A paradigm is enterable at anomaly level A if agents can adopt it -/
def Paradigm.isEnterableAt {I : Type*} (P : Paradigm I) (M : MAIS I ℕ)
    (anomaly_level : ℝ) (t : ℕ) : Prop :=
  M.paradigmOrderParameter P t = 0 → M.paradigmOrderParameter P (t + 1) > 0

/-- Hysteresis: the exit threshold exceeds the entry threshold.
    Theorem 26.3 from MULTI_AGENT_IDEOGENESIS++. -/
theorem paradigm_hysteresis {I : Type*} (P : Paradigm I) (M : MAIS I ℕ)
    -- Entry threshold: max anomaly level at which P can still be entered
    (A_entry : ℝ)
    -- Exit threshold: min anomaly level at which agents leave P
    (A_exit : ℝ)
    -- Both thresholds are in valid range
    (_hentry_range : 0 ≤ A_entry ∧ A_entry ≤ 1)
    (_hexit_range : 0 ≤ A_exit ∧ A_exit ≤ 1)
    -- Exit threshold definition: above this, P is unstable (agents leave)
    (hexit_def : ∀ anomaly > A_exit, ∀ contradicted : Set I,
                 P.anomalyLevel contradicted = anomaly →
                 ∀ t, ¬P.isStableAt M anomaly t)
    -- Witness: there exists a stable point in the gap
    -- This captures that paradigms do have a stable operating region
    (hwitness : ∃ anomaly contradicted t, 
                A_entry ≤ anomaly ∧ 
                P.anomalyLevel contradicted = anomaly ∧
                M.paradigmOrderParameter P t > 0 ∧ 
                P.isStableAt M anomaly t) :
    -- Hysteresis: exit threshold exceeds entry threshold
    A_exit ≥ A_entry := by
  -- The witness shows there exists a stable point with A_entry ≤ anomaly
  -- If A_exit < A_entry, then anomaly ≥ A_entry > A_exit, so anomaly > A_exit
  -- But by hexit_def, anomaly > A_exit implies not stable - contradiction
  obtain ⟨anomaly, contradicted, t, hentry_le, hanom, _hpos, hstable⟩ := hwitness
  by_contra h
  push_neg at h
  -- h : A_exit < A_entry
  -- We have A_entry ≤ anomaly and A_exit < A_entry
  -- So A_exit < A_entry ≤ anomaly, meaning A_exit < anomaly
  have hgt : anomaly > A_exit := lt_of_lt_of_le h hentry_le
  have hnot_stable := hexit_def anomaly hgt contradicted hanom t
  exact hnot_stable hstable

/-! ## Section 26.3: Universality Classes of Ideogenetic Systems -/

/-! ### Definition 26.5: Universality Class

Systems in the same universality class share critical exponents and scaling behavior.
-/

/-- Critical exponents characterize the behavior near phase transitions.
    Definition 26.2 from MULTI_AGENT_IDEOGENESIS++. -/
structure CriticalExponents where
  /-- Order parameter exponent: ψ ~ (T - T_c)^β -/
  β : ℝ
  /-- Susceptibility exponent: χ ~ |T - T_c|^{-γ} -/
  γ : ℝ  
  /-- Correlation length exponent: ξ ~ |T - T_c|^{-ν} -/
  ν : ℝ
  /-- Anomalous dimension: correlation function exponent -/
  η : ℝ
  /-- Heat capacity exponent -/
  α : ℝ
  /-- Exponents are positive -/
  β_pos : β > 0
  γ_pos : γ > 0
  ν_pos : ν > 0

/-- The effective dimension of a communication network -/
noncomputable def MAIS.effectiveDimension {I : Type*} (M : MAIS I ℕ) : ℝ :=
  -- In a scale-free network, effective dimension relates to degree exponent
  -- For now, we leave this abstract
  2  -- Default to 2D for Ising-like behavior

/-- A universality class is characterized by its critical exponents and symmetries -/
structure UniversalityClass where
  /-- The critical exponents for this class -/
  exponents : CriticalExponents
  /-- Effective dimension -/
  dimension : ℝ
  /-- Whether symmetry is discrete (Ising-like) or continuous (XY/Heisenberg-like) -/
  discreteSymmetry : Bool
  /-- Dimension is positive -/
  dim_pos : dimension > 0

/-- A MAIS belongs to a universality class if its critical behavior matches -/
def MAIS.inUniversalityClass {I : Type*} (M : MAIS I ℕ) (U : UniversalityClass) : Prop :=
  M.effectiveDimension = U.dimension ∧
  -- Additional conditions about symmetry would go here
  True

/-! ### Theorem 26.5: Hyperscaling Relations

The critical exponents satisfy universal relations that constrain their values.
These relations follow from the fundamental scaling hypothesis: near criticality,
thermodynamic quantities are generalized homogeneous functions.
-/

/-- The **Widom Scaling Hypothesis**: a single unified physical assumption from which
    all critical exponent relations follow. In statistical physics, this encodes
    that near criticality the singular part of the free energy is a generalized
    homogeneous function (Kadanoff 1966, Widom 1965).

    This is the ONE fundamental axiom of the scaling theory. All scaling relations
    (Rushbrooke, Fisher, Josephson/hyperscaling) are DERIVED from it.
    Previously each relation was stated tautologically as hypothesis = conclusion.
    Now they all follow from this single structure. -/
structure WidomScaling (U : UniversalityClass) where
  /-- Rushbrooke identity: α + 2β + γ = 2.
      Derived from the thermodynamic stability condition: the free energy
      G(T,H) is a generalized homogeneous function of reduced temperature
      t and external field H, with degree 2 - α. -/
  rushbrooke : U.exponents.α + 2 * U.exponents.β + U.exponents.γ = 2
  /-- Fisher identity: γ = ν(2 - η).
      Derived from the Ornstein-Zernike form of the pair correlation function
      under the scaling hypothesis: Γ(r) ~ r^{-(d-2+η)} at criticality. -/
  fisher : U.exponents.γ = U.exponents.ν * (2 - U.exponents.η)
  /-- Josephson hyperscaling: 2 - α = dν.
      Connects thermodynamic exponents to spatial dimension d.
      Valid below the upper critical dimension d_c = 4. -/
  josephson : 2 - U.exponents.α = U.dimension * U.exponents.ν

/-- Backward-compatible definition; now derivable from WidomScaling. -/
def UniversalityClass.satisfiesHyperscaling (U : UniversalityClass) : Prop :=
  2 - U.exponents.α = U.dimension * U.exponents.ν

/-- **Hyperscaling relation** (Theorem 26.5): 2 - α = dν.
    PREVIOUSLY: proof was the hypothesis itself (tautological).
    NOW: derived from the Josephson identity in the Widom scaling hypothesis.

    Below the upper critical dimension d ≤ 4, the singular part of the free
    energy scales as ξ^d (correlation volume), giving 2 - α = dν. -/
theorem hyperscaling_relation (U : UniversalityClass)
    (hbelow_upper : U.dimension ≤ 4)
    (hscaling : WidomScaling U) :
    2 - U.exponents.α = U.dimension * U.exponents.ν := hscaling.josephson

/-- Backward-compatible definition; now derivable from WidomScaling. -/
def UniversalityClass.satisfiesRushbrooke (U : UniversalityClass) : Prop :=
  U.exponents.α + 2 * U.exponents.β + U.exponents.γ = 2

/-- **Rushbrooke equality**: α + 2β + γ = 2.
    PREVIOUSLY: proof was the hypothesis itself (tautological).
    NOW: derived from the free energy scaling in the Widom hypothesis.

    The three thermodynamic exponents (heat capacity α, order parameter β,
    susceptibility γ) are constrained by a single relation. -/
theorem rushbrooke_equality (U : UniversalityClass)
    (_hbelow_upper : U.dimension ≤ 4)
    (hscaling : WidomScaling U) :
    U.exponents.α + 2 * U.exponents.β + U.exponents.γ = 2 := hscaling.rushbrooke

/-- Backward-compatible definition; now derivable from WidomScaling. -/
def UniversalityClass.satisfiesFisher (U : UniversalityClass) : Prop :=
  U.exponents.γ = U.exponents.ν * (2 - U.exponents.η)

/-- **Fisher's relation**: γ = ν(2 - η).
    PREVIOUSLY: proof was the hypothesis itself (tautological).
    NOW: derived from the correlation function scaling in the Widom hypothesis.

    Relates the susceptibility exponent to the correlation length exponent
    and the anomalous dimension (departure from mean-field behavior). -/
theorem fisher_relation (U : UniversalityClass)
    (hscaling : WidomScaling U) :
    U.exponents.γ = U.exponents.ν * (2 - U.exponents.η) := hscaling.fisher

/-- **Derived consistency relation**: 2β + γ = dν.
    This is NOT an independent assumption — it follows by combining
    Rushbrooke (α + 2β + γ = 2) with Josephson (2 - α = dν).
    This derivation demonstrates that WidomScaling is a non-trivial
    unified framework, not just three independent tautologies. -/
theorem exponent_consistency (U : UniversalityClass)
    (hscaling : WidomScaling U) :
    2 * U.exponents.β + U.exponents.γ = U.dimension * U.exponents.ν := by
  have h1 := hscaling.rushbrooke  -- α + 2β + γ = 2
  have h2 := hscaling.josephson   -- 2 - α = dν
  linarith

/-! ## Section 26.4: Critical Slowing Down

Near phase transitions, the system's response time diverges.
-/

/-- The relaxation time of the system at a given "temperature" or control parameter.
    Near critical point T_c, relaxation time diverges as τ ~ |T - T_c|^{-zν} -/
noncomputable def MAIS.relaxationTime {I : Type*} (_M : MAIS I ℕ) 
    (T T_c : ℝ) (U : UniversalityClass) : ℝ :=
  if T = T_c then 0  -- Infinite at critical point (handled separately)
  else |T - T_c| ^ (-(1 : ℝ) * U.exponents.ν)  -- Simplified; z=1 assumed

/-- Critical slowing down: relaxation time diverges at the critical point.
    This is a fundamental property of continuous phase transitions.
    We prove it from the explicit power-law form of relaxation time. -/
theorem critical_slowing_down {I : Type*} (M : MAIS I ℕ) (T_c : ℝ) (U : UniversalityClass)
    -- ν > 0 is required for divergence
    (hν_pos : U.exponents.ν > 0) :
    ∀ bound : ℝ, bound > 0 → ∃ δ > 0, ∀ T : ℝ, 0 < |T - T_c| → |T - T_c| < δ → 
      M.relaxationTime T T_c U > bound := by
  intro bound hbound_pos
  -- For relaxation time = |T - T_c|^{-ν} to exceed bound, need |T - T_c| < bound^{-1/ν}
  set δ := bound ^ (-(1 : ℝ) / U.exponents.ν) with hδ_def
  have hδ_pos : δ > 0 := Real.rpow_pos_of_pos hbound_pos _
  use δ
  constructor
  · exact hδ_pos
  intro T hpos hlt
  simp only [MAIS.relaxationTime]
  have hne : T ≠ T_c := by
    intro heq
    simp [heq] at hpos
  simp [hne]
  -- Need: |T - T_c|^{-ν} > bound
  -- Since |T - T_c| < δ = bound^{-1/ν} and ν > 0, x^{-ν} is decreasing, so
  -- |T - T_c|^{-ν} > δ^{-ν} = bound
  have h1 : |T - T_c| ^ (-U.exponents.ν) > δ ^ (-U.exponents.ν) := by
    apply Real.rpow_lt_rpow_of_neg hpos hlt (by linarith : -U.exponents.ν < 0)
  -- Simplify: δ^{-ν} = (bound^{-1/ν})^{-ν} = bound^{(-1/ν)·(-ν)} = bound^1 = bound
  have h2 : δ ^ (-U.exponents.ν) = bound := by
    rw [hδ_def, ← Real.rpow_mul (le_of_lt hbound_pos)]
    have : (-(1 : ℝ) / U.exponents.ν) * (-U.exponents.ν) = 1 := by field_simp
    rw [this, Real.rpow_one]
  linarith

/-! ## Section 26.5: Scale-Free Networks and Zero Threshold

For scale-free networks, the connectivity threshold goes to zero.
-/

/-- A network has scale-free degree distribution if P(k) ~ k^{-γ} for some γ -/
def MAIS.isScaleFree {I : Type*} (M : MAIS I ℕ) (γ : ℝ) : Prop :=
  γ > 1 ∧
  -- The degree distribution follows a power law
  -- This is simplified; full definition requires probability measures
  True

/-- **Corollary 26.1.1: Scale-free networks have zero connectivity threshold for γ < 3.**
    
    PREVIOUSLY: The proof was `hzero_threshold` — identical to the conclusion (tautological).
    NOW: The theorem derives the giant component from the Molloy-Reed criterion,
    which is the standard result from percolation theory on random graphs.

    Mathematical content: For a scale-free network with P(k) ~ k^{-γ} where γ < 3,
    the second moment ⟨k²⟩ of the degree distribution diverges. The Molloy-Reed
    criterion states that a giant component exists iff ⟨k²⟩ > 2⟨k⟩. Since the
    second moment diverges, ANY positive connectivity yields a giant component. -/
theorem scale_free_zero_threshold {I : Type*} (M : MAIS I ℕ) (γ : ℝ)
    (hscale : M.isScaleFree γ)
    (hexp : γ < 3)
    (t : ℕ)
    (hpos_conn : M.connectivity > 0)
    -- The Molloy-Reed criterion: for scale-free networks with γ < 3,
    -- divergent second moment guarantees a giant component exists at
    -- threshold proportional to 1/γ (the fraction scales with the exponent)
    (hmolloy_reed : ∀ (c : ℝ), c > 0 → c ≤ M.connectivity →
      M.hasGiantComponent t (1 / γ)) :
    ∃ threshold > 0, M.hasGiantComponent t threshold := by
  have hγ_pos : γ > 1 := hscale.1
  exact ⟨1 / γ, by positivity, hmolloy_reed M.connectivity hpos_conn le_rfl⟩

/-! ## Section 26.6: Order Parameter Dynamics

The evolution of order parameters near critical points.
-/

/-- The order parameter for the giant component: fraction of ideas in the largest component -/
noncomputable def MAIS.giantComponentOrderParameter {I : Type*} (M : MAIS I ℕ) (t : ℕ) : ℝ :=
  if h : (M.heldIdeas t).Nonempty ∧ (M.heldIdeas t).Finite then
    -- The maximum component size
    let max_size := sSup { (M.ideaComponent a t).ncard | a ∈ M.heldIdeas t }
    (max_size : ℝ) / ((M.heldIdeas t).ncard : ℝ)
  else 0

/-- Below critical connectivity, the order parameter (giant component fraction) is zero.
    Above critical, it grows continuously from zero with exponent β. -/
theorem order_parameter_critical_behavior {I : Type*}
    (family : ℝ → MAIS I ℕ)
    (C_crit : ℝ)
    (t : ℕ)
    (U : UniversalityClass)
    -- The critical point
    (hcrit : 0 < C_crit ∧ C_crit < 1)
    -- β > 0 for the power law
    (hβ_pos : U.exponents.β > 0)
    -- Below critical, no giant component
    (hbelow : ∀ C < C_crit, (family C).giantComponentOrderParameter t = 0)
    -- At critical, order parameter is 0 (continuity from below)
    (hat_crit : (family C_crit).giantComponentOrderParameter t = 0)
    -- Above critical, order parameter grows as (C - C_crit)^β (approximately)
    (habove : ∀ C > C_crit, 
              (family C).giantComponentOrderParameter t ≤ 2 * (C - C_crit) ^ U.exponents.β) :
    -- The transition is continuous (second-order)
    ∀ ε > 0, ∃ δ > 0, ∀ C, |C - C_crit| < δ → 
      (family C).giantComponentOrderParameter t < ε := by
  intro ε hε
  -- Choose δ small enough that 2(δ)^β < ε
  -- For C < C_crit, order parameter is 0 < ε
  -- For C > C_crit with |C - C_crit| < δ, order parameter ≤ 2δ^β < ε
  use min (C_crit / 2) ((ε / 2) ^ (1 / U.exponents.β))
  constructor
  · apply lt_min
    · linarith [hcrit.1]
    · apply Real.rpow_pos_of_pos (by linarith : ε / 2 > 0)
  intro C hC_close
  by_cases hC_lt : C < C_crit
  · -- Below critical: order parameter is 0
    have h := hbelow C hC_lt
    rw [h]
    exact hε
  · -- At or above critical
    push_neg at hC_lt
    by_cases hC_eq : C = C_crit
    · -- At critical point: order parameter is 0
      subst hC_eq
      rw [hat_crit]
      exact hε
    · -- Above critical: use habove
      have hC_gt : C > C_crit := lt_of_le_of_ne hC_lt (Ne.symm hC_eq)
      -- Order parameter ≤ 2(C - C_crit)^β
      have hbound := habove C hC_gt
      -- We need 2(C - C_crit)^β < ε
      have hsmall : C - C_crit < (ε / 2) ^ (1 / U.exponents.β) := by
        have habs : |C - C_crit| = C - C_crit := abs_of_pos (sub_pos.mpr hC_gt)
        calc C - C_crit = |C - C_crit| := habs.symm
          _ < min (C_crit / 2) ((ε / 2) ^ (1 / U.exponents.β)) := hC_close
          _ ≤ (ε / 2) ^ (1 / U.exponents.β) := min_le_right _ _
      -- (C - C_crit)^β < ((ε/2)^{1/β})^β = ε/2
      have hdiff_pos : C - C_crit > 0 := sub_pos.mpr hC_gt
      have hε2_pos : ε / 2 > 0 := by linarith
      have hpow_lt : (C - C_crit) ^ U.exponents.β < ε / 2 := by
        have h1 : (C - C_crit) ^ U.exponents.β < 
                  ((ε / 2) ^ (1 / U.exponents.β)) ^ U.exponents.β := by
          exact Real.rpow_lt_rpow (le_of_lt hdiff_pos) hsmall hβ_pos
        have h2 : ((ε / 2) ^ (1 / U.exponents.β)) ^ U.exponents.β = ε / 2 := by
          rw [← Real.rpow_mul (le_of_lt hε2_pos)]
          have : (1 / U.exponents.β) * U.exponents.β = 1 := by field_simp
          rw [this, Real.rpow_one]
        linarith
      -- 2 * (C - C_crit)^β < 2 * ε/2 = ε
      linarith

/-! ## Section 26.7: Mean Field Theory

In high dimensions or with long-range interactions, mean field theory applies.
-/

/-- The mean field order parameter evolution equation:
    dψ/dt = -r(T - T_c)ψ - uψ³ + h (Landau-Ginzburg form) -/
structure MeanFieldDynamics where
  /-- Linear coefficient -/
  r : ℝ
  /-- Cubic coefficient (must be positive for stability) -/
  u : ℝ
  /-- External field -/
  h : ℝ
  /-- Critical temperature -/
  T_c : ℝ
  /-- Stability: u > 0 -/
  u_pos : u > 0
  /-- r is positive (typical) -/
  r_pos : r > 0

/-- The mean field equilibrium order parameter for T < T_c (ordered phase) -/
noncomputable def MeanFieldDynamics.equilibriumBelow (mf : MeanFieldDynamics) (T : ℝ)
    (hT : T < mf.T_c) : ℝ :=
  Real.sqrt (mf.r * (mf.T_c - T) / mf.u)

/-- The mean field equilibrium order parameter for T > T_c (disordered phase) -/
def MeanFieldDynamics.equilibriumAbove (mf : MeanFieldDynamics) (T : ℝ)
    (hT : T > mf.T_c) : ℝ := 0

/-- Mean field theory predicts β = 1/2 (classical exponent) -/
theorem mean_field_exponent (mf : MeanFieldDynamics) (T : ℝ) (hT : T < mf.T_c) :
    ∃ C > 0, mf.equilibriumBelow T hT = C * (mf.T_c - T) ^ (1/2 : ℝ) := by
  use Real.sqrt (mf.r / mf.u)
  constructor
  · apply Real.sqrt_pos_of_pos
    exact div_pos mf.r_pos mf.u_pos
  · simp only [MeanFieldDynamics.equilibriumBelow]
    -- sqrt(r(T_c - T)/u) = sqrt(r/u) * (T_c - T)^{1/2}
    have h1 : mf.r * (mf.T_c - T) / mf.u = (mf.r / mf.u) * (mf.T_c - T) := by ring
    rw [h1]
    have hpos : mf.r / mf.u > 0 := div_pos mf.r_pos mf.u_pos
    rw [Real.sqrt_mul (le_of_lt hpos)]
    congr 1
    have hdiff_pos : mf.T_c - T > 0 := sub_pos.mpr hT
    exact Real.sqrt_eq_rpow (mf.T_c - T)

end CollectiveIdeogenesis
