/-
# Novelty Density Decay Theorem

From FORMAL_ANTHROPOLOGY++ Chapter 7.2: Novelty Theorems

This file proves fundamental theorems about novelty density in ideogenetic systems.
The key result is Theorem 7.7: in finitary systems with finite closures, novelty
density eventually decays to zero.

## Key Results:
- Theorem 7.7: Novelty Density Decay - ρ(n) → 0 in finite finitary systems
- Corollary: Eventually no new ideas appear (eventual stagnation)
- Lemma: Cardinality growth bounds in finitary systems

## Mathematical Content:
Novelty density ρ(n) = |Nov(n)| / |gen^n({ι})| measures what fraction of ideas
at stage n are genuinely new. In finite finitary systems, as the closure fills in,
fewer new ideas appear relative to total ideas, so ρ(n) → 0.

## Dependencies:
- SingleAgent_Basic: IdeogeneticSystem, depth, noveltyAt
-/

import FormalAnthropology.SingleAgent_Basic
import FormalAnthropology.SingleAgent_Depth
import FormalAnthropology.SingleAgent_NoveltyMonotonicity
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace NoveltyDensityDecay

open SingleAgentIdeogenesis Set

variable {S : IdeogeneticSystem}

/-! ## Section 1: Novelty Density Definition -/

/-- Novelty density at stage n: the fraction of ideas that are new at stage n.
    
    ρ(n) = |Nov(n)| / |gen^n({ι})|
    
    This measures how "productive" stage n is relative to the total accumulated ideas. -/
noncomputable def noveltyDensity (init : Set S.Idea) (n : ℕ) : ℚ :=
  let nov := noveltyAt S init n
  let total := genCumulative S n init
  if h : total.Finite ∧ total.ncard ≠ 0 then
    (nov.ncard : ℚ) / (total.ncard : ℚ)
  else 0

/-- Novelty density is between 0 and 1 -/
theorem noveltyDensity_bounded (init : Set S.Idea) (n : ℕ) :
    0 ≤ noveltyDensity init n ∧ noveltyDensity init n ≤ 1 := by
  unfold noveltyDensity
  split_ifs with h
  · constructor
    · apply div_nonneg
      · exact Nat.cast_nonneg _
      · exact Nat.cast_nonneg _
    · apply div_le_one_of_le
      · have hfin := h.1
        have : noveltyAt S init n ⊆ genCumulative S n init := noveltyAt_subset_cumulative init n
        have hfin_nov : (noveltyAt S init n).Finite := hfin.subset this
        have hcard : (noveltyAt S init n).ncard ≤ (genCumulative S n init).ncard := 
          Set.ncard_le_ncard this hfin
        exact Nat.cast_le.mpr hcard
      · have hpos : 0 < (genCumulative S n init).ncard := Nat.pos_of_ne_zero h.2
        exact Nat.cast_pos.mpr hpos
  · constructor <;> norm_num

/-! ## Section 2: Finiteness Lemmas -/

/-- In a finitary system with finite initial set, each stage is finite -/
theorem genCumulative_finite_of_finitary_init 
    (hfin_gen : ∀ a : S.Idea, (S.generate a).Finite)
    (init : Set S.Idea) (hfin_init : init.Finite) (n : ℕ) :
    (genCumulative S n init).Finite := by
  induction n with
  | zero =>
    unfold genCumulative
    exact hfin_init
  | succ k ih =>
    unfold genCumulative
    apply Finite.union ih
    apply Finite.biUnion ih
    intro a _
    exact hfin_gen a

/-- If the closure is finite and generation is finitary, then all stages are finite -/
theorem stages_finite_of_finite_closure
    (init : Set S.Idea) 
    (hfin : (SingleAgentIdeogenesis.closure S init).Finite) (n : ℕ) :
    (genCumulative S n init).Finite := by
  have : genCumulative S n init ⊆ closure S init := by
    unfold closure
    exact Set.subset_iUnion (fun k => genCumulative S k init) n
  exact hfin.subset this

/-! ## Section 3: Cardinality Growth Bounds -/

/-- The cardinality of gen^n is bounded by the closure cardinality -/
theorem genCumulative_ncard_bounded 
    (init : Set S.Idea)
    (hfin : (SingleAgentIdeogenesis.closure S init).Finite) (n : ℕ) :
    (genCumulative S n init).ncard ≤ (SingleAgentIdeogenesis.closure S init).ncard := by
  have hfin_n := stages_finite_of_finite_closure init hfin n
  have : genCumulative S n init ⊆ SingleAgentIdeogenesis.closure S init := by
    unfold SingleAgentIdeogenesis.closure
    exact Set.subset_iUnion (fun k => genCumulative S k init) n
  exact Set.ncard_le_ncard this hfin

/-- Cardinality is monotone in stages -/
theorem genCumulative_ncard_monotone (init : Set S.Idea)
    (hfin : ∀ n, (genCumulative S n init).Finite)
    (m n : ℕ) (h : m ≤ n) :
    (genCumulative S m init).ncard ≤ (genCumulative S n init).ncard := by
  have hsub := genCumulative_mono S init m n h
  have hfin_n := hfin n
  exact Set.ncard_le_ncard hsub hfin_n

/-! ## Section 4: Eventual Stabilization -/

/-- A bounded monotone sequence of natural numbers eventually stabilizes.
    
    This is a fundamental fact: a monotone sequence with values in a finite range
    must eventually become constant.
    
    **Proof**: By contradiction. If f never stabilizes, then for all N there exists 
    n ≥ N with f n > f N (by monotonicity). Building an infinite strictly increasing 
    sequence of values all ≤ bound leads to a contradiction. -/
theorem bounded_monotone_nat_stabilizes (f : ℕ → ℕ) (bound : ℕ)
    (hmono : ∀ m n, m ≤ n → f m ≤ f n)
    (hbound : ∀ n, f n ≤ bound) :
    ∃ N : ℕ, ∀ n ≥ N, f n = f N := by
  by_contra h
  push_neg at h
  -- h : ∀ N, ∃ n ≥ N, f n ≠ f N
  -- Since f is monotone and f n ≠ f N for n ≥ N, we have f n > f N
  have h' : ∀ N, ∃ n ≥ N, f n > f N := by
    intro N
    obtain ⟨n, hn_ge, hne⟩ := h N
    use n, hn_ge
    have hle := hmono N n hn_ge
    omega
  -- Build strictly increasing sequence of f values: f(N₀) < f(N₁) < ... all ≤ bound
  have step : ∀ k : ℕ, ∃ N : ℕ, f N ≥ f 0 + k := by
    intro k
    induction k with
    | zero => exact ⟨0, le_refl _⟩
    | succ k ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨M, _, hfM⟩ := h' N
      use M
      calc f M > f N := hfM
           _ ≥ f 0 + k := hN
  -- Take k = bound + 1 for contradiction
  obtain ⟨N, hN⟩ := step (bound + 1)
  have hcontra := hbound N
  omega

/-- If the closure is finite, then the sequence of cardinalities eventually stabilizes.
    
    This is because cardinality can increase at most C times (where C is closure size),
    and at each step it either increases or stays the same. -/
theorem eventually_stabilizes (init : Set S.Idea)
    (hfin : (SingleAgentIdeogenesis.closure S init).Finite) :
    ∃ N : ℕ, ∀ n ≥ N, (genCumulative S n init).ncard = (genCumulative S N init).ncard := by
  -- Apply the bounded monotone lemma
  let f := fun n => (genCumulative S n init).ncard
  let C := (SingleAgentIdeogenesis.closure S init).ncard
  have hmono : ∀ m n, m ≤ n → f m ≤ f n := by
    intro m n hmn
    exact genCumulative_ncard_monotone init (fun k => stages_finite_of_finite_closure init hfin k) m n hmn
  have hbound : ∀ n, f n ≤ C := by
    intro n
    exact genCumulative_ncard_bounded init hfin n
  exact bounded_monotone_nat_stabilizes f C hmono hbound

/-- Corollary: Once stabilized, novelty is empty -/
theorem novelty_empty_after_stabilization (init : Set S.Idea)
    (hfin : (SingleAgentIdeogenesis.closure S init).Finite) :
    ∃ N : ℕ, ∀ n > N, noveltyAt S init n = ∅ := by
  obtain ⟨N, hstab⟩ := eventually_stabilizes init hfin
  use N
  intro n hn
  -- noveltyAt n = gen^n \ gen^(n-1)
  -- If cardinalities are equal for n-1 and n, then no new elements
  have hn_ge : n ≥ N := by omega
  have hn_pred : n - 1 ≥ N := by omega
  have heq_n := hstab n hn_ge
  have heq_pred := hstab (n - 1) hn_pred
  -- |gen^n| = |gen^(n-1)| and gen^(n-1) ⊆ gen^n
  have hsub : genCumulative S (n - 1) init ⊆ genCumulative S n init := by
    apply genCumulative_mono
    omega
  have hfin_n := stages_finite_of_finite_closure init hfin n
  have hfin_pred := stages_finite_of_finite_closure init hfin (n - 1)
  -- Equal cardinality + subset = equality
  have heq_set : genCumulative S (n - 1) init = genCumulative S n init := by
    apply Set.eq_of_subset_of_ncard_le hsub
    omega
    exact hfin_n
  -- noveltyAt n = gen^n \ gen^(n-1) = ∅
  unfold noveltyAt
  ext a
  constructor
  · intro ⟨ha_n, ha_pred⟩
    rw [heq_set] at ha_pred
    exact ha_pred ha_n
  · intro ha
    exact absurd ha (Set.not_mem_empty a)

/-! ## Section 5: Main Theorem - Novelty Density Decay -/

/-- **Theorem 7.7: Novelty Density Decay**
    
    In finitary systems with finite closures, novelty density eventually becomes zero.
    
    ρ(n) → 0 as n → ∞
    
    More precisely: there exists N such that for all n > N, ρ(n) = 0. -/
theorem novelty_density_eventually_zero (init : Set S.Idea)
    (hfin : (SingleAgentIdeogenesis.closure S init).Finite) :
    ∃ N : ℕ, ∀ n > N, noveltyDensity init n = 0 := by
  obtain ⟨N, hempty⟩ := novelty_empty_after_stabilization init hfin
  use N
  intro n hn
  unfold noveltyDensity
  split_ifs
  · -- Novelty is empty, so ncard = 0
    have : noveltyAt S init n = ∅ := hempty n hn
    simp [this, Set.ncard_empty]
  · have : noveltyAt S init n = ∅ := hempty n hn
    simp [this, Set.ncard_empty]
  · rfl
  · rfl

/-- Corollary: Eventually the system stagnates (no new ideas) -/
theorem eventual_stagnation (init : Set S.Idea)
    (hfin : (SingleAgentIdeogenesis.closure S init).Finite) :
    ∃ N : ℕ, ∀ n > N, 
      genCumulative S n init = genCumulative S N init := by
  obtain ⟨N, hstab⟩ := eventually_stabilizes init hfin
  use N
  intro n hn
  -- We need gen^n = gen^N
  have hn_ge : n ≥ N := by omega
  -- From stabilization: |gen^n| = |gen^N|
  have heq_card := hstab n hn_ge
  -- And gen^N ⊆ gen^n
  have hsub : genCumulative S N init ⊆ genCumulative S n init := by
    apply genCumulative_mono
    exact hn_ge
  -- Equal cardinality + subset = equality
  have hfin_n := stages_finite_of_finite_closure init hfin n
  have hfin_N := stages_finite_of_finite_closure init hfin N
  apply Set.eq_of_subset_of_ncard_le hsub
  · omega
  · exact hfin_n

/-! ## Section 6: Rate of Decay -/

/-- The sum of all novelty densities is bounded by the closure size.
    
    ∑_{n=0}^∞ |Nov(n)| = |closure| < ∞
    
    This implies that ρ(n) cannot stay bounded away from 0. -/
theorem sum_novelty_sizes_bounded (init : Set S.Idea)
    (hfin : (SingleAgentIdeogenesis.closure S init).Finite) :
    ∃ M : ℕ, ∀ N : ℕ, 
      (∑ n in Finset.range N, (noveltyAt S init n).ncard) ≤ M := by
  use (SingleAgentIdeogenesis.closure S init).ncard
  intro N
  -- The novelty sets partition the closure (disjoint union)
  -- So their sum equals the closure cardinality
  -- We have: ⋃_{n < N} Nov(n) ⊆ closure, and they're disjoint
  have hpartition : (⋃ n ∈ Finset.range N, noveltyAt S init n) ⊆ closure S init := by
    intro a ha
    simp only [Set.mem_iUnion] at ha
    obtain ⟨n, hn, ha_nov⟩ := ha
    have : noveltyAt S init n ⊆ genCumulative S n init := noveltyAt_subset S init n
    have : a ∈ genCumulative S n init := this ha_nov
    unfold closure
    exact Set.mem_iUnion.mpr ⟨n, this⟩
  -- The union has cardinality ≤ closure cardinality
  have hfin_union : (⋃ n ∈ Finset.range N, noveltyAt S init n).Finite := 
    hfin.subset hpartition
  have hcard_bound : (⋃ n ∈ Finset.range N, noveltyAt S init n).ncard ≤ (SingleAgentIdeogenesis.closure S init).ncard :=
    Set.ncard_le_ncard hpartition hfin
  -- The novelty sets are pairwise disjoint
  have hdisjoint : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n → 
      Disjoint (noveltyAt S init m) (noveltyAt S init n) := by
    intro m _ n _ hmn
    exact novelty_disjoint init m n hmn
  -- Sum of disjoint finite sets' cardinalities equals union cardinality
  calc (∑ n in Finset.range N, (noveltyAt S init n).ncard)
      = (⋃ n ∈ Finset.range N, noveltyAt S init n).ncard := by
        apply Finset.ncard_biUnion_eq
        intro m hm n hn hmn
        exact hdisjoint m hm n hn hmn
    _ ≤ (SingleAgentIdeogenesis.closure S init).ncard := hcard_bound

/-- Alternative formulation: average novelty density over first N stages → 0 -/
theorem average_novelty_density_vanishes (init : Set S.Idea)
    (hfin : (SingleAgentIdeogenesis.closure S init).Finite)
    (hinit_ne : init.Nonempty) :
    ∀ ε > 0, ∃ N : ℕ, ∀ M ≥ N,
      (∑ n in Finset.range M, (noveltyAt S init n).ncard : ℚ) / M < ε := by
  intro ε hε
  -- Total novelty is bounded by closure size C
  obtain ⟨C, hbound⟩ := sum_novelty_sizes_bounded init hfin
  -- Choose N > C/ε
  use Nat.ceil (C / ε) + 1
  intro M hM
  -- Sum of novelties ≤ C
  have hsum_bound : (∑ n in Finset.range M, (noveltyAt S init n).ncard) ≤ C := hbound M
  -- So (sum / M) ≤ C / M < C / N ≤ ε
  have hM_pos : (M : ℚ) > 0 := by
    have : M > 0 := by omega
    exact Nat.cast_pos.mpr this
  calc (∑ n in Finset.range M, (noveltyAt S init n).ncard : ℚ) / M
      ≤ (C : ℚ) / M := by
        apply div_le_div_of_nonneg_right
        · exact Nat.cast_le.mpr hsum_bound
        · exact le_of_lt hM_pos
    _ < ε := by
        apply div_lt_iff_lt_mul hM_pos |>.mpr
        have hM_ge : (M : ℚ) ≥ Nat.ceil (C / ε) + 1 := by
          exact Nat.cast_le.mpr hM
        calc (C : ℚ) 
            = (C : ℚ) * 1 := by ring
          _ < (C / ε) * ε := by
              rw [div_mul_cancel₀]
              · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega : C ≠ 0))
              · exact ne_of_gt hε
          _ ≤ (Nat.ceil (C / ε) : ℚ) * ε := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt hε)
              exact Nat.le_ceil (C / ε)
          _ < (Nat.ceil (C / ε) + 1 : ℚ) * ε := by
              apply mul_lt_mul_of_pos_right _ hε
              norm_cast
              omega
          _ ≤ (M : ℚ) * ε := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt hε)
              exact hM_ge

end NoveltyDensityDecay
