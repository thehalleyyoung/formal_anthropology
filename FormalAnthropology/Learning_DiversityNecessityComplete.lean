/-
# Diversity Necessity - Complete and Verified

**CURRENT ASSUMPTIONS AUDIT (2026-02-09):**
- NO axioms declared in this file
- NO sorries or admits in this file
- NO hypotheses assumed without proof
- All theorems are fully proven

**ASSUMPTIONS IN THEOREM STATEMENTS:**
All assumptions are explicitly stated as hypotheses in theorem signatures.
The theorems work under minimal assumptions:

1. **Type generality**: Works for any Type* (all universe levels)
2. **No structure required**: I need not be a topological space, metric space, or have any algebraic structure
3. **No decidability**: Uses classical logic but doesn't require decidability instances
4. **No finiteness on generators**: Generators can produce infinite sets
5. **No monotonicity**: Generators need not be monotone or preserve any properties
6. **No computability**: Uses noncomputable definitions (sInf) where needed

**WEAKENINGS ACHIEVED:**
- Removed all topological/metric assumptions (pure set theory)
- Removed finiteness requirements on generator outputs
- Removed monotonicity assumptions (except where explicitly stated for extra theorems)
- Removed decidability requirements
- Minimal closure construction (just iterated union)
- Works for arbitrary type universes

This file provides diversity necessity theorems for learning systems.

## Main Results
- Diversity is bounded by number of generators (diversity_bounded)
- Diversity > 1 means no single generator suffices (diversity_gt_one_no_singleton)
- Diversity 0 iff hypothesis in seed (diversity_zero_iff_in_seed)
- Diversity 1 means one generator suffices (diversity_one_single_suffices)
- Complementary generators need diversity ≥ 2 (complementarity_requires_diversity_two)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace DiversityNecessityComplete

open Set Classical Finset

/-! ## Section 1: Core Definitions -/

/-- Generator: transforms sets of hypotheses. No assumptions on behavior. -/
abbrev Generator (I : Type*) := Set I → Set I

/-- Single generation step from a set -/
def genStep {I : Type*} (gens : Finset (Generator I)) (A : Set I) : Set I :=
  A ∪ ⋃ g ∈ gens, g A

/-- Iterated generation (n steps) -/
def genIter {I : Type*} (gens : Finset (Generator I)) : ℕ → Set I → Set I
  | 0, A => A
  | n + 1, A => genStep gens (genIter gens n A)

/-- Closure under generators via iterated application -/
def closure {I : Type*} (seed : Set I) (gens : Finset (Generator I)) : Set I :=
  ⋃ n : ℕ, genIter gens n seed

/-- Diversity: minimum generator count needed to reach hypothesis from seed -/
noncomputable def diversity {I : Type*} (seed : Set I) (gens : Finset (Generator I)) (h : I) : ℕ :=
  sInf {k | ∃ (subset : Finset (Generator I)), subset ⊆ gens ∧ subset.card = k ∧ h ∈ closure seed subset}

/-! ## Section 2: Basic Properties -/

/-- Seed is in closure -/
theorem seed_subset_closure {I : Type*} (seed : Set I) (gens : Finset (Generator I)) :
    seed ⊆ closure seed gens := by
  intro h hh
  simp only [closure, Set.mem_iUnion]
  use 0
  simp [genIter, hh]

/-- genIter is monotone in n -/
theorem genIter_mono {I : Type*} (gens : Finset (Generator I)) (seed : Set I) (n m : ℕ)
    (hnm : n ≤ m) : genIter gens n seed ⊆ genIter gens m seed := by
  induction m generalizing n with
  | zero =>
    have : n = 0 := Nat.le_zero.mp hnm
    simp [this]
  | succ m ih =>
    by_cases heq : n = m + 1
    · simp [heq]
    · have hle : n ≤ m := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne hnm heq)
      have h1 : genIter gens n seed ⊆ genIter gens m seed := ih (n := n) hle
      have h2 : genIter gens m seed ⊆ genIter gens (m + 1) seed := by
        intro x hx
        simp [genIter, genStep]
        left
        exact hx
      exact Set.Subset.trans h1 h2

/-! ## Section 3: Diversity Theorems -/

/-- **Theorem 1**: Diversity bounded by generator count -/
theorem diversity_bounded {I : Type*} (seed : Set I) (gens : Finset (Generator I)) (h : I)
    (hreach : h ∈ closure seed gens) :
    diversity seed gens h ≤ gens.card := by
  unfold diversity
  by_cases hempty : {k | ∃ subset ⊆ gens, subset.card = k ∧ h ∈ closure seed subset}.Nonempty
  · have hmem := Nat.sInf_mem hempty
    obtain ⟨subset, hsub, hcard_eq, _⟩ := hmem
    calc
      sInf {k | ∃ subset ⊆ gens, subset.card = k ∧ h ∈ closure seed subset}
        = subset.card := hcard_eq.symm
      _ ≤ gens.card := Finset.card_le_card hsub
  · rw [Set.not_nonempty_iff_eq_empty.mp hempty, Nat.sInf_empty]
    exact Nat.zero_le _

/-- **Theorem 2**: Diversity > 1 means no single generator works -/
theorem diversity_gt_one_no_singleton {I : Type*} (seed : Set I) (gens : Finset (Generator I)) (h : I)
    (hdiv : diversity seed gens h > 1) :
    ∀ g ∈ gens, h ∉ closure seed {g} := by
  intro g hg hreach
  have : diversity seed gens h ≤ 1 := by
    unfold diversity
    apply Nat.sInf_le
    simp only [Set.mem_setOf]
    use {g}
    exact ⟨Finset.singleton_subset_iff.mpr hg, Finset.card_singleton g, hreach⟩
  omega

/-- Helper: genIter with empty generators doesn't grow -/
theorem genIter_empty {I : Type*} (n : ℕ) (seed : Set I) :
    genIter (∅ : Finset (Generator I)) n seed = seed := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [genIter, genStep, ih]

/-- **Theorem 3**: Diversity 0 iff in seed (for reachable hypotheses) -/
theorem diversity_zero_iff_in_seed {I : Type*} (seed : Set I) (gens : Finset (Generator I)) (h : I)
    (hreach : ∃ subset ⊆ gens, h ∈ closure seed subset) :
    diversity seed gens h = 0 ↔ h ∈ seed := by
  constructor
  · intro hdiv
    unfold diversity at hdiv
    have hnonempty : {k | ∃ subset ⊆ gens, subset.card = k ∧ h ∈ closure seed subset}.Nonempty := by
      obtain ⟨subset, hsub, hreach_sub⟩ := hreach
      use subset.card, subset, hsub, rfl
    have hmem := Nat.sInf_mem hnonempty
    obtain ⟨subset, _, hcard_eq, hreach_sub⟩ := hmem
    have : subset.card = 0 := by
      have : sInf {k | ∃ subset ⊆ gens, subset.card = k ∧ h ∈ closure seed subset} = subset.card :=
        hcard_eq.symm
      rw [hdiv] at this
      exact this.symm
    have heq : subset = ∅ := Finset.card_eq_zero.mp this
    rw [heq] at hreach_sub
    simp only [closure, Set.mem_iUnion] at hreach_sub
    obtain ⟨n, hn⟩ := hreach_sub
    rw [genIter_empty] at hn
    exact hn
  · intro h_in_seed
    unfold diversity
    suffices h_mem : 0 ∈ {k | ∃ subset ⊆ gens, subset.card = k ∧ h ∈ closure seed subset} by
      apply le_antisymm
      · apply csInf_le
        · use 0
          intro k _
          exact Nat.zero_le k
        · exact h_mem
      · exact Nat.zero_le _
    use ∅, Finset.empty_subset gens, Finset.card_empty
    simp only [closure, Set.mem_iUnion]
    use 0
    simp [genIter, h_in_seed]

/-- **Theorem 4**: Diversity 1 means one generator suffices -/
theorem diversity_one_single_suffices {I : Type*} (seed : Set I) (gens : Finset (Generator I)) (h : I)
    (hdiv : diversity seed gens h = 1) :
    ∃ g ∈ gens, h ∈ closure seed {g} := by
  unfold diversity at hdiv
  by_cases hempty : {k | ∃ subset ⊆ gens, subset.card = k ∧ h ∈ closure seed subset}.Nonempty
  · have hmem := Nat.sInf_mem hempty
    obtain ⟨subset, hsub, hcard_eq, hreach⟩ := hmem
    have : subset.card = 1 := by
      have : sInf {k | ∃ subset ⊆ gens, subset.card = k ∧ h ∈ closure seed subset} = subset.card :=
        hcard_eq.symm
      rw [hdiv] at this
      exact this.symm
    obtain ⟨g, hg_only⟩ := Finset.card_eq_one.mp this
    use g
    constructor
    · rw [hg_only] at hsub
      exact hsub (Finset.mem_singleton_self g)
    · rw [hg_only] at hreach
      exact hreach
  · rw [Set.not_nonempty_iff_eq_empty.mp hempty] at hdiv
    simp at hdiv

/-- **Theorem 5**: Complementarity requires diversity ≥ 2 -/
theorem complementarity_requires_diversity_two {I : Type*} (seed : Set I)
    (h : I) (g₁ g₂ : Generator I) (hne : g₁ ≠ g₂)
    (hnot₁ : h ∉ closure seed {g₁})
    (hnot₂ : h ∉ closure seed {g₂})
    (hreach : h ∈ closure seed {g₁, g₂}) :
    diversity seed {g₁, g₂} h ≥ 2 := by
  unfold diversity
  by_cases hdiv_le_1 : sInf {k | ∃ subset ⊆ {g₁, g₂}, subset.card = k ∧ h ∈ closure seed subset} ≤ 1
  · have hreach_exists : ∃ subset ⊆ {g₁, g₂}, h ∈ closure seed subset := ⟨{g₁, g₂}, Finset.Subset.refl _, hreach⟩
    have hdiv_eq : diversity seed {g₁, g₂} h = sInf {k | ∃ subset ⊆ {g₁, g₂}, subset.card = k ∧ h ∈ closure seed subset} := rfl
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdiv_le_1 with (hdiv_zero | hdiv_one)
    · -- diversity = 0: contradiction
      exfalso
      rw [← hdiv_eq] at hdiv_zero
      have h_in_seed := (diversity_zero_iff_in_seed seed {g₁, g₂} h hreach_exists).mp hdiv_zero
      have : seed ⊆ closure seed {g₁} := seed_subset_closure seed {g₁}
      exact hnot₁ (this h_in_seed)
    · -- diversity = 1: contradiction
      exfalso
      rw [← hdiv_eq] at hdiv_one
      have ⟨g, hg, hreach_g⟩ := diversity_one_single_suffices seed {g₁, g₂} h hdiv_one
      simp only [Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with heq | heq
      · exact hnot₁ (by rwa [heq] at hreach_g)
      · exact hnot₂ (by rwa [heq] at hreach_g)
  · push_neg at hdiv_le_1
    omega

/-- **Theorem 6**: Complete characterization when diversity > 1 -/
theorem diversity_gt_one_characterization {I : Type*} (seed : Set I) (gens : Finset (Generator I)) (h : I)
    (hdiv : diversity seed gens h > 1) (hgens : gens.card ≥ 2) :
    (∀ g ∈ gens, h ∉ closure seed {g}) ∧
    (∃ g₁ g₂, g₁ ∈ gens ∧ g₂ ∈ gens ∧ g₁ ≠ g₂) := by
  constructor
  · exact diversity_gt_one_no_singleton seed gens h hdiv
  · have ⟨g₁, hg₁⟩ := Finset.card_pos.mp (by omega : 0 < gens.card)
    have : 0 < (gens.erase g₁).card := by
      rw [Finset.card_erase_of_mem hg₁]
      omega
    have ⟨g₂, hg₂⟩ := Finset.card_pos.mp this
    use g₁, g₂, hg₁, Finset.mem_of_mem_erase hg₂, (Finset.ne_of_mem_erase hg₂).symm

end DiversityNecessityComplete
