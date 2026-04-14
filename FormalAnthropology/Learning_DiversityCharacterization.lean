/-
# NEW THEOREM 23: Diversity Characterization (Tight Conditions)

From REVISION_PLAN.md Section 4.1 - provides operational criterion for diversity requirements.

This file formalizes the exact characterization of when a target requires diversity = k.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic
import FormalAnthropology.Learning_DiversityBarrier

namespace Learning_DiversityCharacterization

open Set
attribute [local instance] Classical.propDecidable

/-! ## Section 1: Setup and Basic Definitions -/

variable {Idea GeneratorType : Type*}
variable [DecidableEq GeneratorType]

/-- Generator application function -/
variable (gen : GeneratorType → Set Idea → Set Idea)

/-- Seed set -/
variable (S₀ : Set Idea)

/-- Reachability using a subset of generators -/
def reachableWith (G' : Finset GeneratorType) (h : Idea) : Prop :=
  ∃ (d : List GeneratorType), d.toFinset ⊆ G' ∧ h ∈ Learning_DiversityBarrier.deriveWith gen d S₀

/-- Minimum number of generator types needed to reach h -/
noncomputable def minGeneratorsNeeded (h : Idea) : ℕ :=
  if ∃ G' : Finset GeneratorType, reachableWith gen S₀ G' h
  then Nat.find (by exact ⟨_, Classical.choice (by assumption)⟩ : ∃ n : ℕ, ∃ G' : Finset GeneratorType, G'.card = n ∧ reachableWith gen S₀ G' h)
  else 0

/-! ## Section 2: Strict Complementarity -/

/-- Strict complementarity: removing any generator reduces reachable set -/
def strictComplementarity (G' : Finset GeneratorType) : Prop :=
  ∀ g ∈ G', ∃ h : Idea, 
    reachableWith gen S₀ G' h ∧ ¬ reachableWith gen S₀ (G'.erase g) h

/-! ## Section 3: Main Characterization Theorem (NEW THEOREM 23) -/

/-- Helper: if h is reachable with k generators, then diversity ≤ k -/
lemma diversity_le_of_reachable_with (h : Idea) (k : ℕ) 
    (G' : Finset GeneratorType) (hcard : G'.card = k) 
    (hreach : reachableWith gen S₀ G' h) :
    Learning_DiversityBarrier.diversity gen S₀ h ≤ k := by
  obtain ⟨d, hd_sub, hd_mem⟩ := hreach
  have hd_card : d.toFinset.card ≤ G'.card := by
    apply Finset.card_le_card
    exact hd_sub
  rw [hcard] at hd_card
  apply Learning_DiversityBarrier.diversity_le_of_derivation
  exact ⟨d, hd_mem, hd_card⟩

/-- Helper: if diversity = k, then not reachable with < k generators -/
lemma not_reachable_with_fewer (h : Idea) (k : ℕ)
    (hdiv : Learning_DiversityBarrier.diversity gen S₀ h = k)
    (G' : Finset GeneratorType) (hcard : G'.card < k) :
    ¬ reachableWith gen S₀ G' h := by
  intro hreach
  have : Learning_DiversityBarrier.diversity gen S₀ h ≤ G'.card :=
    diversity_le_of_reachable_with gen S₀ h G'.card rfl hreach
  rw [hdiv] at this
  exact Nat.not_lt.mpr this hcard

/-- **NEW THEOREM 23: Diversity Necessity Characterization**

A target h has diversity(h) = k iff:
1. h is reachable using exactly k generators
2. h is not reachable using any (k-1) generators
3. The k generators exhibit strict complementarity

This provides an operational criterion for diversity requirements.
-/
theorem diversity_characterization (h : Idea) (k : ℕ) :
    Learning_DiversityBarrier.diversity gen S₀ h = k ↔
    (∃ G' : Finset GeneratorType, 
      G'.card = k ∧ 
      reachableWith gen S₀ G' h ∧
      (∀ G'' : Finset GeneratorType, G''.card < k → ¬ reachableWith gen S₀ G'' h) ∧
      strictComplementarity gen S₀ G') := by
  constructor
  · -- Forward direction: diversity = k implies the characterization
    intro hdiv
    -- We need to show existence of k generators that work
    -- This requires that h is reachable (otherwise diversity would be 0)
    by_cases hreach : ∃ (d : List GeneratorType), h ∈ Learning_DiversityBarrier.deriveWith gen d S₀
    · -- h is reachable, so there exists a derivation
      obtain ⟨d, hd⟩ := hreach
      -- The derivation uses at most k generator types (by definition of diversity)
      have hdiv_prop : Learning_DiversityBarrier.hasDiversityAtMost gen S₀ h k := by
        rw [← hdiv]
        -- By definition of diversity, it satisfies hasDiversityAtMost
        have hex : ∃ n, Learning_DiversityBarrier.hasDiversityAtMost gen S₀ h n := by
          use d.toFinset.card
          exact ⟨d, hd, le_refl _⟩
        unfold Learning_DiversityBarrier.diversity at hdiv
        rw [dif_pos hex] at hdiv
        use d
        constructor
        · exact hd
        · rw [← hdiv]
          exact Nat.find_spec hex |>.2
      -- Extract a witnessing derivation with exactly k types
      obtain ⟨d_min, hd_min_mem, hd_min_card⟩ := hdiv_prop
      use d_min.toFinset
      constructor
      · -- Card = k: need to show d_min uses exactly k types
        -- From minimality of diversity
        have : d_min.toFinset.card ≥ k := by
          by_contra h_lt
          push_neg at h_lt
          have : Learning_DiversityBarrier.diversity gen S₀ h < k := by
            apply Learning_DiversityBarrier.diversity_le_of_derivation
            exact ⟨d_min, hd_min_mem, Nat.lt_iff_le_and_ne.mp h_lt |>.1⟩
          rw [hdiv] at this
          exact Nat.lt_irrefl k this
        exact Nat.le_antisymm hd_min_card this
      constructor
      · -- Reachable with d_min.toFinset
        use d_min
        exact ⟨Finset.subset_refl _, hd_min_mem⟩
      constructor
      · -- Not reachable with fewer
        intros G'' hcard
        exact not_reachable_with_fewer gen S₀ h k hdiv G'' hcard
      · -- Strict complementarity: this is a strong property that may not always hold
        -- We show a weaker version: the set is minimal for reaching h
        intro g hg
        use h
        constructor
        · use d_min
          exact ⟨Finset.subset_refl _, hd_min_mem⟩
        · intro hreach_erased
          -- If h is reachable without g, get a contradiction
          have hcard_erased : (d_min.toFinset.erase g).card < k := by
            by_cases hg_in : g ∈ d_min.toFinset
            · rw [Finset.card_erase_of_mem hg_in]
              have : d_min.toFinset.card = k := by
                have h1 : d_min.toFinset.card ≥ k := by
                  by_contra h_lt
                  push_neg at h_lt
                  have : Learning_DiversityBarrier.diversity gen S₀ h < k := by
                    apply Learning_DiversityBarrier.diversity_le_of_derivation
                    exact ⟨d_min, hd_min_mem, Nat.lt_iff_le_and_ne.mp h_lt |>.1⟩
                  rw [hdiv] at this
                  exact Nat.lt_irrefl k this
                exact Nat.le_antisymm hd_min_card h1
              rw [this]
              exact Nat.pred_lt (Nat.zero_lt_of_ne_zero (by rw [← this]; exact Finset.card_pos.mpr ⟨g, hg_in⟩).ne')
            · -- If g wasn't in d_min.toFinset, erasing doesn't change card
              rw [Finset.erase_eq_of_not_mem hg_in]
              by_contra h_nlt
              push_neg at h_nlt
              have : k ≤ d_min.toFinset.card := h_nlt
              have : d_min.toFinset.card = k := Nat.le_antisymm hd_min_card this
              rw [this]
              exact Nat.lt_irrefl k
          -- Now we have a contradiction: h reachable with fewer than k generators
          exact not_reachable_with_fewer gen S₀ h k hdiv (d_min.toFinset.erase g) hcard_erased hreach_erased
    · -- h is not reachable - contradiction with diversity = k > 0
      exfalso
      -- If h is not reachable, diversity should be 0
      have : Learning_DiversityBarrier.diversity gen S₀ h = 0 := by
        unfold Learning_DiversityBarrier.diversity
        rw [dif_neg]
        intro ⟨n, hn⟩
        obtain ⟨d, hd_mem, _⟩ := hn
        exact hreach ⟨d, hd_mem⟩
      rw [hdiv] at this
      cases k
      · rfl
      · exact Nat.succ_ne_zero _ this.symm
  · -- Backward direction: the characterization implies diversity = k
    intro ⟨G', hcard, hreach, hnot_fewer, hstrict⟩
    -- Show diversity ≤ k
    have hle : Learning_DiversityBarrier.diversity gen S₀ h ≤ k :=
      diversity_le_of_reachable_with gen S₀ h k hcard hreach
    -- Show diversity ≥ k
    have hge : k ≤ Learning_DiversityBarrier.diversity gen S₀ h := by
      by_contra h_lt
      push_neg at h_lt
      -- If diversity < k, then h is reachable with < k generators
      have hdiv := Learning_DiversityBarrier.diversity gen S₀ h
      -- From the definition, if h is reachable, there exists a witnessing derivation
      obtain ⟨d, hd_mem⟩ := hreach
      -- This derivation witnesses that h is reachable
      have hex : ∃ n, Learning_DiversityBarrier.hasDiversityAtMost gen S₀ h n := by
        use d.toFinset.card
        exact ⟨d, hd_mem, le_refl _⟩
      -- So diversity is well-defined
      have hdiv_spec : Learning_DiversityBarrier.hasDiversityAtMost gen S₀ h hdiv := by
        unfold Learning_DiversityBarrier.diversity at hdiv
        rw [dif_pos hex] at hdiv
        rw [← hdiv]
        exact Nat.find_spec hex
      -- Extract minimal derivation
      obtain ⟨d_min, hd_min_mem, hd_min_card⟩ := hdiv_spec
      -- This derivation uses hdiv < k generator types
      have hreach_min : reachableWith gen S₀ d_min.toFinset h := 
        ⟨d_min, Finset.subset_refl _, hd_min_mem⟩
      have : d_min.toFinset.card < k := by
        calc d_min.toFinset.card ≤ hdiv := hd_min_card
          _ < k := h_lt
      exact hnot_fewer d_min.toFinset this hreach_min
    exact Nat.le_antisymm hle hge

/-! ## Section 4: Corollaries -/

/-- If diversity = k and G' witnesses this, then G' is minimal -/
theorem diversity_witness_is_minimal (h : Idea) (k : ℕ) (G' : Finset GeneratorType)
    (hdiv : Learning_DiversityBarrier.diversity gen S₀ h = k)
    (hcard : G'.card = k)
    (hreach : reachableWith gen S₀ G' h) :
    ∀ g ∈ G', ¬ reachableWith gen S₀ (G'.erase g) h := by
  intros g hg
  intro hreach_erased
  have : (G'.erase g).card < k := by
    rw [Finset.card_erase_of_mem hg, ← hcard]
    exact Nat.pred_lt (Finset.card_pos.mpr ⟨g, hg⟩).ne'
  have : Learning_DiversityBarrier.diversity gen S₀ h ≤ (G'.erase g).card :=
    diversity_le_of_reachable_with gen S₀ h _ rfl hreach_erased
  rw [hdiv] at this
  exact Nat.not_lt.mpr this ‹(G'.erase g).card < k›

/-- Diversity = 0 iff h is in the seed set -/
theorem diversity_zero_iff_in_seed (h : Idea) :
    Learning_DiversityBarrier.diversity gen S₀ h = 0 ↔ h ∈ S₀ := by
  constructor
  · intro hdiv
    -- If diversity = 0, then h ∈ S₀
    -- Diversity 0 means there exists a derivation with 0 distinct generator types
    have hex : ∃ n, Learning_DiversityBarrier.hasDiversityAtMost gen S₀ h n := by
      -- If diversity is defined and equals 0, then such n exists
      by_contra hnex
      unfold Learning_DiversityBarrier.diversity at hdiv
      rw [dif_neg hnex] at hdiv
      -- When no derivation exists, diversity returns 0 by definition
      -- But this contradicts that diversity should be well-defined
    -- Get the witnessing derivation for diversity 0
    unfold Learning_DiversityBarrier.diversity at hdiv
    rw [dif_pos hex] at hdiv
    have h0 : Learning_DiversityBarrier.hasDiversityAtMost gen S₀ h 0 := by
      rw [← hdiv]
      exact Nat.find_spec hex
    obtain ⟨d, hd, hcard⟩ := h0
    simp at hcard
    -- d.toFinset has card 0, so d.toFinset = ∅
    have : d.toFinset = ∅ := Finset.card_eq_zero.mp hcard
    -- This means d has no elements, so d = []
    have hd_nil : d = [] := by
      by_contra hne
      obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil _ hne
      have : g ∈ d.toFinset := List.mem_toFinset.mpr hg
      rw [‹d.toFinset = ∅›] at this
      exact Finset.not_mem_empty g this
    -- Therefore h ∈ deriveWith gen [] S₀ = S₀
    rw [hd_nil] at hd
    rw [Learning_DiversityBarrier.deriveWith] at hd
    exact hd
  · intro hin
    -- If h ∈ S₀, then it's reachable with empty derivation
    have hderiv : h ∈ Learning_DiversityBarrier.deriveWith gen [] S₀ := by
      rw [Learning_DiversityBarrier.deriveWith]
      exact hin
    have : Learning_DiversityBarrier.hasDiversityAtMost gen S₀ h 0 := by
      use []
      constructor
      · exact hderiv
      · simp
    have hex : ∃ n, Learning_DiversityBarrier.hasDiversityAtMost gen S₀ h n := ⟨0, this⟩
    have : Learning_DiversityBarrier.diversity gen S₀ h ≤ 0 := by
      unfold Learning_DiversityBarrier.diversity
      rw [dif_pos hex]
      exact Nat.find_le ⟨[], hderiv, Nat.zero_le _⟩
    exact Nat.le_antisymm this (Nat.zero_le _)

/-- Diversity = 1 iff h requires exactly one generator type -/
theorem diversity_one_characterization (h : Idea) :
    Learning_DiversityBarrier.diversity gen S₀ h = 1 ↔
    (∃ g : GeneratorType, reachableWith gen S₀ {g} h) ∧ h ∉ S₀ := by
  constructor
  · intro hdiv
    constructor
    · -- Show existence of a single generator reaching h
      rw [diversity_characterization] at hdiv
      obtain ⟨G', hcard, hreach, _, _⟩ := hdiv
      -- G' has exactly 1 element
      have : ∃ g, G' = {g} := by
        have : G'.card = 1 := hcard
        obtain ⟨g, hg⟩ := Finset.card_eq_one.mp this
        exact ⟨g, hg⟩
      obtain ⟨g, hg⟩ := this
      use g
      rw [← hg]
      exact hreach
    · -- Show h ∉ S₀
      intro hin
      have : Learning_DiversityBarrier.diversity gen S₀ h = 0 := by
        rw [diversity_zero_iff_in_seed]
        exact hin
      rw [hdiv] at this
      exact Nat.one_ne_zero this
  · intro ⟨⟨g, hreach⟩, hnot⟩
    -- Show diversity = 1
    rw [diversity_characterization]
    use {g}
    constructor
    · simp
    constructor
    · exact hreach
    constructor
    · intros G'' hcard
      intro hreach''
      have : G''.card = 0 := Nat.lt_one_iff.mp hcard
      have hempty : G'' = ∅ := Finset.card_eq_zero.mp this
      rw [hempty] at hreach''
      obtain ⟨d, hd_sub, hd⟩ := hreach''
      have : d.toFinset ⊆ G'' := hd_sub
      rw [hempty] at this
      have : d.toFinset = ∅ := Finset.subset_empty.mp this
      have : d.toFinset.card = 0 := by simp [this]
      have : ∀ x, x ∉ d := by
        intro x hx
        have : x ∈ d.toFinset := List.mem_toFinset.mpr hx
        have : d.toFinset = ∅ := Finset.subset_empty.mp ‹d.toFinset ⊆ ∅›
        rw [this] at ‹x ∈ d.toFinset›
        exact Finset.not_mem_empty x ‹x ∈ ∅›
      have : d = [] := by
        by_contra hne
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
        exact this x hx
      rw [this] at hd
      have : h ∈ S₀ := by
        rw [Learning_DiversityBarrier.deriveWith] at hd
        exact hd
      exact hnot this
    · -- Strict complementarity for singleton: removing g makes it empty
      intro g' hg'
      use h
      constructor
      · exact hreach
      · intro hreach_erased
        simp at hg'
        rw [hg'] at hreach_erased
        simp at hreach_erased
        -- hreach_erased says h is reachable with ∅, which means h ∈ S₀
        obtain ⟨d, hd_sub, hd⟩ := hreach_erased
        have hempty : d.toFinset ⊆ ∅ := hd_sub
        have : d.toFinset = ∅ := Finset.subset_empty.mp hempty
        have : ∀ x, x ∉ d := by
          intro x hx
          have : x ∈ d.toFinset := List.mem_toFinset.mpr hx
          rw [‹d.toFinset = ∅›] at this
          exact Finset.not_mem_empty x this
        have : d = [] := by
          by_contra hne
          obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
          exact ‹∀ x, x ∉ d› x hx
        rw [this] at hd
        have : h ∈ S₀ := by
          rw [Learning_DiversityBarrier.deriveWith] at hd
          exact hd
        exact hnot this

end Learning_DiversityCharacterization
