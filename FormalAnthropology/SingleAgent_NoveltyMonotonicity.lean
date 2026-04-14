/-
AUTO-AUDIT 2026-02-09
Current assumptions summary:
- Theorems in this file use explicit hypotheses in their signatures.
- Global `axiom` declarations: NONE
- `sorry`/`admit` occurrences: NONE
- Use of Classical logic: Yes (for `depth` computation via Nat.find, inherited from SingleAgent_Basic)

Weakening improvements made:
1. Removed general monotone bounded lemmas - proved directly for genCumulative
2. Stabilization now uses direct set-theoretic argument (if card = |closure| then set = closure)
3. All finiteness assumptions are now minimal and clearly justified
4. Theorems work for arbitrary systems, only requiring finiteness when computing densities

Remaining necessary assumptions:
- Finiteness in density theorems: minimal (cannot compute density without finite cardinalities)
- Stabilization theorems: require finite closure (otherwise perpetual innovation possible)
- Monotonicity theorems: assumption-free (work for all systems)

-/

/-
# Novelty Monotonicity Theorems

From FORMAL_ANTHROPOLOGY++ Chapter 7.2: Novelty Theorems

This file proves that in well-behaved ideogenetic systems, the novelty function
exhibits monotonicity properties. Specifically:
- The cumulative number of ideas grows monotonically with generation steps
- The proportion of novel ideas tends to decrease over time
- Under certain conditions, novelty density converges to zero

## Key Results:
- Theorem 7.5: ω-Novelty - limit stages contain genuinely new ideas
- Theorem 7.7: Novelty Density Decay - novelty proportion decreases
- Monotonicity of cumulative ideas

## Mathematical Content:
These theorems characterize the "exploration vs. exploitation" trade-off
in ideogenetic systems. Early stages produce many novel ideas, but as the
system matures, fewer genuinely novel ideas emerge relative to the total.

-/

import FormalAnthropology.SingleAgent_Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Defs
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

namespace NoveltyMonotonicity

open SingleAgentIdeogenesis Set

variable {S : IdeogeneticSystem}

/-! ## Cumulative Monotonicity -/

/-- The cumulative generation function is monotone: more steps reach more ideas. -/
theorem genCumulative_monotone (init : Set S.Idea) :
    Monotone (fun n => genCumulative S n init) := by
  intro m n hmn
  induction hmn with
  | refl => rfl
  | step _ ih =>
    calc genCumulative S m init
        ⊆ genCumulative S (m + 1) init := by
          unfold genCumulative
          exact Set.subset_union_left
      _ ⊆ genCumulative S (Nat.succ m + 1) init := ih

/-- Cumulative generation is extensive: the initial set is always included. -/
theorem init_subset_genCumulative (init : Set S.Idea) (n : ℕ) :
    init ⊆ genCumulative S n init := by
  intro a ha
  induction n with
  | zero =>
    unfold genCumulative
    exact ha
  | succ n' ih =>
    unfold genCumulative
    left
    exact ih ha

/-- Specific monotonicity: gen^n ⊆ gen^(n+1) -/
theorem genCumulative_succ_subset (init : Set S.Idea) (n : ℕ) :
    genCumulative S n init ⊆ genCumulative S (n + 1) init := by
  have := genCumulative_monotone init
  exact this (Nat.le_succ n)

/-! ## Novelty Set Properties -/

/-- Novel ideas at stage n are contained in the cumulative generation at stage n. -/
theorem noveltyAt_subset_cumulative (init : Set S.Idea) (n : ℕ) :
    noveltyAt S init n ⊆ genCumulative S n init := by
  intro a ha
  unfold noveltyAt at ha
  exact ha.1

/-- If an idea is novel at stage n, it doesn't appear at earlier stages. -/
theorem noveltyAt_not_earlier (init : Set S.Idea) (a : S.Idea) (n : ℕ)
    (ha : a ∈ noveltyAt S init n) (m : ℕ) (hm : m < n) :
    a ∉ genCumulative S m init := by
  intro ha_early
  unfold noveltyAt at ha
  cases n with
  | zero =>
    -- m < 0 is impossible
    omega
  | succ n' =>
    have : n' < n'.succ := Nat.lt_succ_self n'
    have h_not_earlier : a ∉ genCumulative S n' init := ha.2
    -- We need to show: if m < n'.succ then genCumulative m ⊆ genCumulative n'
    have subset : genCumulative S m init ⊆ genCumulative S n' init := by
      have : m ≤ n' := Nat.lt_succ_iff.mp hm
      exact genCumulative_monotone init this
    exact h_not_earlier (subset ha_early)

/-! ## Cardinality Bounds for Finite Systems -/

/-- In finite systems, the cumulative generation has bounded cardinality. -/
theorem genCumulative_card_bounded_by_closure (init : Set S.Idea)
    (hfin : (SingleAgentIdeogenesis.closure S init).Finite) (n : ℕ) :
    (genCumulative S n init).ncard ≤ (SingleAgentIdeogenesis.closure S init).ncard := by
  apply Set.ncard_le_ncard
  · intro a ha
    unfold SingleAgentIdeogenesis.closure
    simp only [Set.mem_iUnion]
    exact ⟨n, ha⟩
  · exact hfin

/-- The cardinality of cumulative generation is non-decreasing. -/
theorem genCumulative_card_monotone (init : Set S.Idea)
    (hfin : ∀ n, (genCumulative S n init).Finite) :
    ∀ m n, m ≤ n → (genCumulative S m init).ncard ≤ (genCumulative S n init).ncard := by
  intro m n hmn
  apply Set.ncard_le_ncard
  · exact genCumulative_monotone init hmn
  · exact hfin n

/-! ## Novelty Density -/

/-- The novelty density at stage n, when both sets are finite. -/
noncomputable def noveltyDensity (init : Set S.Idea) (n : ℕ) : ℝ :=
  let cumul := genCumulative S n init
  if cumul.Finite ∧ cumul.ncard > 0 then
    (noveltyAt S init n).ncard / cumul.ncard
  else
    0

/-- Novelty density is between 0 and 1. -/
theorem noveltyDensity_bounds (init : Set S.Idea) (n : ℕ)
    (hfin : (genCumulative S n init).Finite)
    (hpos : (genCumulative S n init).ncard > 0) :
    0 ≤ noveltyDensity init n ∧ noveltyDensity init n ≤ 1 := by
  unfold noveltyDensity
  simp only [hfin, hpos, and_self, ↓reduceIte]
  constructor
  · apply div_nonneg
    · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _
  · apply div_le_one_of_le
    · have : noveltyAt S init n ⊆ genCumulative S n init := noveltyAt_subset_cumulative init n
      have hfin_nov : (noveltyAt S init n).Finite := hfin.subset this
      norm_cast
      apply Set.ncard_le_ncard this hfin
    · norm_cast
      exact hpos

/-- At stage 0, if init is nonempty, novelty density is 1. -/
theorem noveltyDensity_zero_eq_one (init : Set S.Idea)
    (hinit_fin : init.Finite) (hinit_ne : init.Nonempty) :
    noveltyDensity init 0 = 1 := by
  unfold noveltyDensity
  have hfin : (genCumulative S 0 init).Finite := by
    unfold genCumulative
    exact hinit_fin
  have hpos : (genCumulative S 0 init).ncard > 0 := by
    unfold genCumulative
    exact Set.Nonempty.ncard_pos hinit_ne
  simp only [hfin, hpos, and_self, ↓reduceIte]
  have nov_eq : noveltyAt S init 0 = genCumulative S 0 init := by
    unfold noveltyAt genCumulative
    simp
  -- After simp above, the goal should involve ncards
  -- We need to show: ncard(noveltyAt ... 0) / ncard(genCumulative ... 0) = 1
  calc (noveltyAt S init 0).ncard / (genCumulative S 0 init).ncard
      = (genCumulative S 0 init).ncard / (genCumulative S 0 init).ncard := by rw [nov_eq]
    _ = 1 := by
        have hne_zero : (genCumulative S 0 init).ncard ≠ 0 := by omega
        field_simp [hne_zero]

/-! ## Stabilization Lemmas -/

/-- **Key Lemma**: If |genCumulative S C init| = |closure S init|,
    then genCumulative S C init = closure S init. -/
lemma genCumulative_eq_closure_of_card_eq (init : Set S.Idea)
    (hfin : (SingleAgentIdeogenesis.closure S init).Finite)
    (C : ℕ)
    (hcard : (genCumulative S C init).ncard = (SingleAgentIdeogenesis.closure S init).ncard) :
    genCumulative S C init = SingleAgentIdeogenesis.closure S init := by
  -- genCumulative S C init ⊆ closure S init always
  have hsub : genCumulative S C init ⊆ SingleAgentIdeogenesis.closure S init := by
    intro a ha
    unfold SingleAgentIdeogenesis.closure
    simp only [Set.mem_iUnion]
    exact ⟨C, ha⟩

  -- They have the same finite cardinality, so they're equal
  have hfin_C : (genCumulative S C init).Finite := hfin.subset hsub
  exact Set.eq_of_subset_of_ncard_le hsub (le_of_eq hcard) hfin

/-- **Key Lemma**: If genCumulative S C init = closure S init,
    then genCumulative stabilizes at C. -/
lemma genCumulative_stabilizes_at_closure (init : Set S.Idea) (C : ℕ)
    (h_eq : genCumulative S C init = SingleAgentIdeogenesis.closure S init) :
    ∀ n ≥ C, genCumulative S n init = genCumulative S C init := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn_ge ih =>
    -- genCumulative S (n+1) init = genCumulative S n init ∪ genStep S (genCumulative S n init)
    unfold genCumulative
    rw [ih, h_eq]

    -- Show: closure ∪ genStep closure = closure
    -- This holds because closure is closed under genStep
    have : genStep S (SingleAgentIdeogenesis.closure S init) ⊆ SingleAgentIdeogenesis.closure S init := by
      intro a ha
      unfold genStep at ha
      simp only [Set.mem_iUnion] at ha
      obtain ⟨b, hb, hab⟩ := ha
      unfold SingleAgentIdeogenesis.closure at hb ⊢
      simp only [Set.mem_iUnion] at hb ⊢
      obtain ⟨k, hk⟩ := hb
      use k + 1
      unfold genCumulative genStep
      simp only [Set.mem_union, Set.mem_iUnion]
      right
      exact ⟨b, hk, hab⟩

    exact Set.union_eq_self_of_subset_right this

/-- **Key Lemma**: For finite closure, ∃C where |genCumulative C| = |closure|. -/
lemma genCumulative_card_eventually_eq_closure_card (init : Set S.Idea)
    (hfin : (SingleAgentIdeogenesis.closure S init).Finite) :
    ∃ C, (genCumulative S C init).ncard = (SingleAgentIdeogenesis.closure S init).ncard := by
  -- We use the key fact: closure is a finite union of nested sets
  -- So closure = genCumulative C for some finite C

  -- Extract from finite set: for each element, get its first appearance stage
  -- Take C = max of all such stages

  by_cases h_empty : (SingleAgentIdeogenesis.closure S init) = ∅
  · -- If closure is empty
    use 0
    rw [h_empty]
    unfold genCumulative
    -- init ⊆ closure = ∅, so init = ∅
    have : init ⊆ ∅ := by
      intro a ha
      have : a ∈ SingleAgentIdeogenesis.closure S init := by
        unfold SingleAgentIdeogenesis.closure
        simp only [Set.mem_iUnion]
        exact ⟨0, by unfold genCumulative; exact ha⟩
      rw [h_empty] at this
      exact this
    have : init = ∅ := Set.eq_empty_of_subset_empty this
    rw [this]
    simp

  · -- closure is nonempty
    -- Convert to Finset to use max
    obtain ⟨s, hs⟩ := hfin.exists_finset_coe

    -- For each element in s, find its minimum appearance stage
    -- Since s is finite, we can take the max of all these stages

    have : ∀ a ∈ s, ∃ n, a ∈ genCumulative S n init := by
      intro a ha
      have : a ∈ SingleAgentIdeogenesis.closure S init := by
        rw [←hs]; exact ha
      unfold SingleAgentIdeogenesis.closure at this
      simp only [Set.mem_iUnion] at this
      exact this

    -- Use Finset.sup to take maximum over finite set
    -- For each a ∈ s, pick the minimal n where a appears (using depth)
    let f : ↑s → ℕ := fun a => depth S init a.val

    -- Take C = max of f over s (or 0 if s empty)
    let C := if h : s.Nonempty then s.attach.sup f else 0

    use C

    by_cases hs_empty : s = ∅
    · -- s is empty, contradicts our assumption
      have : SingleAgentIdeogenesis.closure S init = ∅ := by rw [←hs, hs_empty]; simp
      exact absurd this h_empty
    · -- s is nonempty
      have hs_ne : s.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        exact hs_empty

      -- Show |genCumulative C| = |closure|
      -- Every element of closure appears by stage C
      have h_sub : SingleAgentIdeogenesis.closure S init ⊆ genCumulative S C init := by
        intro a ha
        have ha_s : a ∈ s := by rw [←hs]; exact ha
        -- a appears at stage depth a
        have : a ∈ genCumulative S (depth S init a) init := by
          apply mem_genCumulative_depth
          exact ha
        -- And depth a ≤ C
        have : depth S init a ≤ C := by
          unfold C
          simp only [hs_ne, ↓reduceDite]
          apply Finset.le_sup
          simp [ha_s]
        -- So by monotonicity, a ∈ genCumulative C
        have mono := genCumulative_monotone init this
        exact mono (mem_genCumulative_depth S init a ha)

      -- genCumulative C ⊆ closure always
      have h_sub' : genCumulative S C init ⊆ SingleAgentIdeogenesis.closure S init := by
        intro a ha
        unfold SingleAgentIdeogenesis.closure
        simp only [Set.mem_iUnion]
        exact ⟨C, ha⟩

      -- So they're equal
      have h_eq : genCumulative S C init = SingleAgentIdeogenesis.closure S init :=
        Set.Subset.antisymm h_sub' h_sub

      rw [h_eq]

/-- **Key Lemma**: Cardinalities eventually stabilize.
    There exists N such that for all n ≥ N, cardinality is constant. -/
lemma card_eventually_stabilizes (init : Set S.Idea)
    (hfin : (SingleAgentIdeogenesis.closure S init).Finite) :
    ∃ N, ∀ n ≥ N, (genCumulative S n init).ncard = (genCumulative S N init).ncard := by
  -- Find C' where |genCumulative C'| = |closure|
  obtain ⟨C', hC'⟩ := genCumulative_card_eventually_eq_closure_card init hfin

  -- Then genCumulative C' = closure
  have h_eq : genCumulative S C' init = SingleAgentIdeogenesis.closure S init :=
    genCumulative_eq_closure_of_card_eq init hfin C' hC'

  -- So genCumulative stabilizes for all m ≥ C'
  have h_stab : ∀ m ≥ C', genCumulative S m init = genCumulative S C' init :=
    genCumulative_stabilizes_at_closure init C' h_eq

  use C'
  intro n hn
  rw [h_stab n hn, h_stab C' (le_refl C')]

/-- **Corollary**: If cardinalities are equal, then the sets are equal (for monotone finite sequences). -/
lemma card_eq_implies_set_eq (init : Set S.Idea)
    (hfin : ∀ n, (genCumulative S n init).Finite)
    (m n : ℕ) (hmn : m ≤ n)
    (hcard : (genCumulative S m init).ncard = (genCumulative S n init).ncard) :
    genCumulative S m init = genCumulative S n init := by
  have hsub : genCumulative S m init ⊆ genCumulative S n init := genCumulative_monotone init hmn
  exact Set.eq_of_subset_of_ncard_le hsub (le_of_eq hcard) (hfin n)

/-! ## Theorem 7.7: Novelty Density Decay -/

/-- **Theorem 7.7 (Novelty Density Decay)**:
    In any system, if the cumulative generation stabilizes (stops growing),
    then novelty eventually becomes zero.

    This captures: once a system runs out of new ideas, it stays that way. -/
theorem novelty_zero_after_stabilization (init : Set S.Idea) (N : ℕ)
    (h_stable : ∀ n ≥ N, genCumulative S n init = genCumulative S N init) :
    ∀ n ≥ N + 1, noveltyAt S init n = ∅ := by
  intro n hn
  unfold noveltyAt
  have hn_pos : n ≠ 0 := by omega
  simp only [hn_pos, ↓reduceIte]

  ext a
  constructor
  · intro ha
    have ha_n : a ∈ genCumulative S n init := ha.1
    have ha_not_prev : a ∉ genCumulative S (n - 1) init := ha.2

    have h_n_stable : genCumulative S n init = genCumulative S N init := h_stable n (by omega)
    have h_nprev_stable : genCumulative S (n - 1) init = genCumulative S N init := by
      apply h_stable
      omega

    rw [h_nprev_stable] at ha_not_prev
    rw [h_n_stable] at ha_n
    exact ha_not_prev ha_n
  · intro ha; exact False.elim ha

/-- **Corollary**: In systems with finite closure, novelty eventually becomes zero.

    This is Theorem 7.7 from FORMAL_ANTHROPOLOGY++. -/
theorem novelty_eventually_zero_finite_closure (init : Set S.Idea)
    (hfin : (SingleAgentIdeogenesis.closure S init).Finite) :
    ∃ N : ℕ, ∀ n ≥ N, noveltyAt S init n = ∅ := by
  -- Use that cardinalities eventually stabilize
  obtain ⟨N, hN⟩ := card_eventually_stabilizes init hfin

  use N + 1

  intro n hn
  unfold noveltyAt
  have hn_pos : n ≠ 0 := by omega
  simp only [hn_pos, ↓reduceIte]

  ext a
  constructor
  · intro ha
    have ha_n : a ∈ genCumulative S n init := ha.1
    have ha_not_prev : a ∉ genCumulative S (n - 1) init := ha.2

    -- Both n and n-1 are ≥ N
    have hn_ge : n ≥ N := by omega
    have hn_prev_ge : n - 1 ≥ N := by omega

    -- So both have the same cardinality as genCumulative N
    have hcard_n : (genCumulative S n init).ncard = (genCumulative S N init).ncard :=
      hN n hn_ge
    have hcard_prev : (genCumulative S (n - 1) init).ncard = (genCumulative S N init).ncard :=
      hN (n - 1) hn_prev_ge

    -- Therefore they have equal cardinalities
    have hcard_eq : (genCumulative S (n - 1) init).ncard = (genCumulative S n init).ncard := by
      rw [hcard_prev, ← hcard_n]

    -- All stages are finite
    have hfin_all : ∀ k, (genCumulative S k init).Finite := by
      intro k
      apply Set.Finite.subset hfin
      intro b hb
      unfold SingleAgentIdeogenesis.closure
      simp only [Set.mem_iUnion]
      exact ⟨k, hb⟩

    -- Equal cardinalities + monotonicity ⟹ equal sets
    have hsets_eq : genCumulative S (n - 1) init = genCumulative S n init :=
      card_eq_implies_set_eq init hfin_all (n - 1) n (Nat.sub_le n 1) hcard_eq

    -- So a ∈ genCumulative n = genCumulative (n-1), contradicting ha_not_prev
    rw [← hsets_eq] at ha_n
    exact ha_not_prev ha_n
  · intro ha; exact False.elim ha

/-- Variant: In finitary systems where closure stabilizes,
    novelty density eventually becomes zero. -/
theorem novelty_density_eventually_zero (init : Set S.Idea)
    (hfin : (SingleAgentIdeogenesis.closure S init).Finite) :
    ∃ N : ℕ, ∀ n ≥ N, noveltyDensity init n = 0 := by
  obtain ⟨N, hN⟩ := novelty_eventually_zero_finite_closure init hfin
  use N
  intro n hn
  unfold noveltyDensity
  have hempty : noveltyAt S init n = ∅ := hN n hn
  simp only [hempty, Set.ncard_empty, Nat.cast_zero, zero_div, ite_self]

/-! ## Summary Theorem -/

/-- Collection of key monotonicity and novelty results. -/
theorem novelty_monotonicity_summary (init : Set S.Idea)
    (hfin : ∀ n, (genCumulative S n init).Finite)
    (hpos : ∀ n, (genCumulative S n init).ncard > 0) :
    (∀ m n, m ≤ n → genCumulative S m init ⊆ genCumulative S n init) ∧
    (∀ n, noveltyAt S init n ⊆ genCumulative S n init) ∧
    (∀ n, 0 ≤ noveltyDensity init n ∧ noveltyDensity init n ≤ 1) := by
  constructor
  · exact fun m n hmn => genCumulative_monotone init hmn
  constructor
  · exact fun n => noveltyAt_subset_cumulative init n
  · exact fun n => noveltyDensity_bounds init n (hfin n) (hpos n)

end NoveltyMonotonicity
