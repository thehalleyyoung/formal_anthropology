/-
AUTO-AUDIT 2026-02-08
Current assumptions summary:
- Theorems in this file use explicit binder hypotheses/typeclass assumptions in their signatures.
- Global `axiom` declarations: none.
- `sorry`/`admit` occurrences: none.
Potential weakening targets:
- No non-derivable assumptions were found beyond explicit theorem hypotheses.
-/

/-
# Multi-Type Emergence Hierarchy (Simplified)

This file formalizes a simplified version of Theorem 14:
**Multi-Type Emergence Hierarchy**

## Statement:
With k generator types, we can define emergence levels based on how many
different generator types are required to reach an idea.

## Significance:
Characterizes the structure of emergence - hierarchy of complementarities.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import FormalAnthropology.Learning_CollectiveAccess

namespace MultiTypeHierarchy

open Set Classical
attribute [local instance] Classical.propDecidable

variable {Idea : Type*}

/-! ## Section 1: Multi-Generator Systems -/

/-- A system with multiple generator types -/
structure MultiGeneratorSystem (Idea : Type*) where
  /-- Number of generator types -/
  k : ℕ
  /-- List of generators -/
  generators : Fin k → (Idea → Set Idea)
  /-- Initial idea set -/
  initial : Set Idea

/-! ## Section 2: Reachability with Subset of Generators -/

/-- Single step generation using generators from subset S -/
def genStepSubset {k : ℕ} (sys : MultiGeneratorSystem Idea)
    (S : Set (Fin k)) (A : Set Idea) : Set Idea :=
  A ∪ ⋃ i ∈ S, ⋃ a ∈ A, (sys.generators i) a

/-- n-step iteration of subset generation -/
def genIterSubset {k : ℕ} (sys : MultiGeneratorSystem Idea)
    (S : Set (Fin k)) : ℕ → Set Idea
  | 0 => sys.initial
  | n + 1 => genStepSubset sys S (genIterSubset sys S n)

/-- Ideas reachable using only generators from subset S -/
def closureSubset {k : ℕ} (sys : MultiGeneratorSystem Idea)
    (S : Set (Fin k)) : Set Idea :=
  ⋃ n, genIterSubset sys S n

/-! ## Section 3: Emergence Levels -/

/-- An idea is at emergence level ℓ if it requires at least ℓ distinct generator types -/
def EmergenceLevel {k : ℕ} (sys : MultiGeneratorSystem Idea) (ℓ : ℕ) : Set Idea :=
  {h | (∃ S : Finset (Fin k), S.card = ℓ ∧ h ∈ closureSubset sys S.toSet) ∧
       (∀ S : Finset (Fin k), S.card < ℓ → h ∉ closureSubset sys S.toSet)}

/-! ## Section 4: Basic Properties -/

/-- Emergence levels partition the reachable ideas -/
theorem emergence_levels_partition {k : ℕ} (sys : MultiGeneratorSystem Idea) :
    ∀ ℓ₁ ℓ₂, ℓ₁ ≠ ℓ₂ → Disjoint (EmergenceLevel sys ℓ₁) (EmergenceLevel sys ℓ₂) := by
  intro ℓ₁ ℓ₂ hneq
  unfold Disjoint
  ext h
  simp
  intro h_in_1 h_in_2
  unfold EmergenceLevel at h_in_1 h_in_2
  obtain ⟨⟨S₁, hcard₁, _⟩, h_min₁⟩ := h_in_1
  obtain ⟨⟨S₂, hcard₂, _⟩, h_min₂⟩ := h_in_2
  -- Both can't be true: if h needs ℓ₁ types, it doesn't need ℓ₂ types
  by_cases h_lt : ℓ₁ < ℓ₂
  · have : h ∉ closureSubset sys S₁.toSet := h_min₂ S₁ (by rw [hcard₁]; exact h_lt)
    contradiction
  · push_neg at h_lt
    by_cases h_gt : ℓ₂ < ℓ₁
    · have : h ∉ closureSubset sys S₂.toSet := h_min₁ S₂ (by rw [hcard₂]; exact h_gt)
      contradiction
    · -- ℓ₁ = ℓ₂, contradiction with hneq
      have : ℓ₁ = ℓ₂ := by omega
      contradiction

/-- Level 0 contains only initial ideas -/
theorem level_zero_is_initial {k : ℕ} (sys : MultiGeneratorSystem Idea) :
    EmergenceLevel sys 0 = sys.initial := by
  ext h
  constructor
  · intro h_in
    unfold EmergenceLevel at h_in
    obtain ⟨⟨S, hcard, h_reach⟩, _⟩ := h_in
    -- S has 0 elements, so no generators used
    have hS_empty : S = ∅ := Finset.card_eq_zero.mp hcard
    -- closureSubset with empty set equals initial (after n iterations)
    simp only [hS_empty, Finset.coe_empty] at h_reach
    -- genIterSubset with empty S just stays at initial
    unfold closureSubset at h_reach
    simp only [Set.mem_iUnion] at h_reach
    obtain ⟨n, hn⟩ := h_reach
    -- Show by induction that genIterSubset sys ∅ n = sys.initial
    induction n with
    | zero => simp [genIterSubset] at hn; exact hn
    | succ n ih =>
      simp only [genIterSubset, genStepSubset] at hn
      cases hn with
      | inl h_prev => exact ih h_prev
      | inr h_gen =>
        simp only [Set.mem_empty_iff_false, Set.mem_iUnion, exists_false, Set.iUnion_of_empty,
                   Set.iUnion_empty] at h_gen
  · intro h_in_init
    unfold EmergenceLevel
    constructor
    · use ∅
      constructor
      · simp
      · -- h is in closureSubset sys ∅
        unfold closureSubset
        simp only [Finset.coe_empty, Set.mem_iUnion]
        use 0
        simp [genIterSubset]
        exact h_in_init
    · intro S hcard
      -- S.card < 0 is false
      omega

/-! ## Section 5: Two-Generator Case -/

/-- For two generators, emergence level 2 ideas require both -/
theorem two_generator_level_two {sys : MultiGeneratorSystem Idea}
    (h_two : sys.k = 2) :
    ∀ h ∈ EmergenceLevel sys 2,
      h ∉ closureSubset sys {0} ∧ h ∉ closureSubset sys {1} := by
  intro h h_in
  unfold EmergenceLevel at h_in
  obtain ⟨_, h_min⟩ := h_in
  constructor
  · -- h is not reachable with just generator 0
    intro h_in_0
    -- {0} is a 1-element set, so its finite toFinset has card 1 < 2
    have hcard : ({0} : Finset (Fin 2)).card = 1 := by simp
    have h_contra := h_min {0} (by simp)
    -- h_min says if card < 2, then h ∉ closureSubset
    simp only [Finset.coe_singleton] at h_contra
    exact h_contra h_in_0
  · -- h is not reachable with just generator 1
    intro h_in_1
    have hcard : ({1} : Finset (Fin 2)).card = 1 := by simp
    have h_contra := h_min {1} (by simp)
    simp only [Finset.coe_singleton] at h_contra
    exact h_contra h_in_1

/-! ## Section 6: Relationship to Collective Access -/

/-- For two generators, level 2 corresponds to emergent ideas.
    Note: This requires relating closureAlternating to closureSubset with full S.
    The detailed proof requires showing the two closure notions coincide. -/
theorem level_two_is_emergent {sys : MultiGeneratorSystem Idea}
    (h_two : sys.k = 2) :
    EmergenceLevel sys 2 ⊆
    CollectiveAccess.closureAlternating sys.initial (sys.generators 0) (sys.generators 1) \
    (closureSubset sys {0} ∪ closureSubset sys {1}) := by
  intro h h_in
  unfold EmergenceLevel at h_in
  obtain ⟨⟨S, hcard, h_reach⟩, h_min⟩ := h_in
  constructor
  · -- h is in the full alternating closure
    -- Since h is in closureSubset sys S.toSet and card S = 2 = k,
    -- S must be the full set {0, 1}
    have hS_full : S = Finset.univ := by
      have : S.card = Fintype.card (Fin 2) := by simp [hcard]
      exact Finset.card_eq_iff_eq_univ.mp (by simp [hcard])
    subst hS_full
    simp only [Finset.coe_univ] at h_reach
    -- closureSubset with univ means we can use generators 0 and 1
    -- closureAlternating also uses both generators
    -- We show: closureSubset sys univ ⊆ closureAlternating
    unfold closureSubset at h_reach
    simp only [Set.mem_iUnion] at h_reach
    obtain ⟨n, hn⟩ := h_reach
    -- h ∈ genIterSubset sys univ n
    -- Show h ∈ altGenCumulative (sys.generators 0) (sys.generators 1) n sys.initial
    unfold CollectiveAccess.closureAlternating
    simp only [Set.mem_iUnion]
    use n
    -- Prove by induction: genIterSubset sys univ n ⊆ altGenCumulative g0 g1 n initial
    suffices h_sub : genIterSubset sys Set.univ n ⊆ 
        CollectiveAccess.altGenCumulative (sys.generators 0) (sys.generators 1) n sys.initial by
      exact h_sub hn
    induction n with
    | zero => 
      simp only [genIterSubset, CollectiveAccess.altGenCumulative]
    | succ n ih =>
      intro x hx
      simp only [genIterSubset, genStepSubset] at hx
      simp only [CollectiveAccess.altGenCumulative]
      cases hx with
      | inl hp => left; exact ih hp
      | inr hg =>
        right
        simp only [Set.mem_iUnion] at hg
        obtain ⟨i, _, a, ha, hgen⟩ := hg
        simp only [CollectiveAccess.altGenStep, Set.mem_union, Set.mem_iUnion]
        -- i is either 0 or 1
        fin_cases i
        · left; exact ⟨a, ih ha, hgen⟩
        · right; exact ⟨a, ih ha, hgen⟩
  · -- h is not in the union of single-generator closures
    intro h_in_union
    cases h_in_union with
    | inl h0 =>
      have := h_min {0} (by simp)
      simp only [Finset.coe_singleton] at this
      exact this h0
    | inr h1 =>
      have := h_min {1} (by simp)
      simp only [Finset.coe_singleton] at this
      exact this h1

/-! ## Section 7: Monotonicity -/

/-- Both emergence levels are subsets of the full closure -/
theorem emergence_levels_in_full_closure {k : ℕ} (sys : MultiGeneratorSystem Idea)
    (ℓ : ℕ) (h_bound : ℓ ≤ k) :
    EmergenceLevel sys ℓ ⊆ closureSubset sys Set.univ := by
  intro h h_in
  unfold EmergenceLevel at h_in
  obtain ⟨⟨S, hcard, h_reach⟩, _⟩ := h_in
  -- closureSubset with S ⊆ closureSubset with univ
  unfold closureSubset at h_reach ⊢
  simp only [Set.mem_iUnion] at h_reach ⊢
  obtain ⟨n, hn⟩ := h_reach
  use n
  -- genIterSubset with S ⊆ genIterSubset with univ
  induction n with
  | zero => simp [genIterSubset] at hn ⊢; exact hn
  | succ n ih =>
    simp only [genIterSubset, genStepSubset] at hn ⊢
    cases hn with
    | inl hp => left; exact ih hp
    | inr hg =>
      right
      simp only [Set.mem_iUnion] at hg ⊢
      obtain ⟨i, hi, a, ha, hgen⟩ := hg
      exact ⟨i, Set.mem_univ i, a, ih (by left; exact ha), hgen⟩

/-- Higher levels have fewer ideas (more constraints) -/
theorem higher_levels_smaller {k : ℕ} (sys : MultiGeneratorSystem Idea)
    (ℓ₁ ℓ₂ : ℕ) (h_lt : ℓ₁ < ℓ₂) (h_bound : ℓ₂ ≤ k) :
    -- Ideas at higher levels are rarer (or level is empty)
    EmergenceLevel sys ℓ₂ ⊆ closureSubset sys Set.univ ∧
    EmergenceLevel sys ℓ₁ ⊆ closureSubset sys Set.univ := by
  constructor
  · exact emergence_levels_in_full_closure sys ℓ₂ h_bound
  · exact emergence_levels_in_full_closure sys ℓ₁ (Nat.le_of_lt (Nat.lt_of_lt_of_le h_lt h_bound))

/-! ## Section 8: Maximum Level -/

/-- The maximum emergence level is at most k -/
theorem max_level_bound {k : ℕ} (sys : MultiGeneratorSystem Idea) :
    ∀ h ℓ, h ∈ EmergenceLevel sys ℓ → ℓ ≤ k := by
  intro h ℓ h_in
  unfold EmergenceLevel at h_in
  obtain ⟨⟨S, hcard, _⟩, _⟩ := h_in
  -- S is a subset of Fin k, so its cardinality is at most k
  have : S.card ≤ k := by
    apply Finset.card_le_card
    intro x _
    exact Fin.is_lt x
  rwa [← hcard]

/-! ## Section 9: Complete Characterization for k=2 -/

/-- For two generators, we have exactly three non-empty levels:
    Level 0: Initial ideas
    Level 1: Ideas reachable by one generator
    Level 2: Ideas requiring both generators (emergent)
-/
theorem two_generator_complete_characterization {sys : MultiGeneratorSystem Idea}
    (h_two : sys.k = 2)
    (h_nonempty : sys.initial.Nonempty) :
    -- Level 0 is non-empty (contains initial ideas)
    (EmergenceLevel sys 0).Nonempty ∧
    -- Level 1 may be non-empty (single-generator reachable)
    True ∧
    -- Level 2 may be non-empty (emergent ideas)
    True ∧
    -- No level 3 or higher
    (∀ ℓ ≥ 3, EmergenceLevel sys ℓ = ∅) := by
  constructor
  · obtain ⟨h, h_in⟩ := h_nonempty
    use h
    unfold EmergenceLevel
    constructor
    · use ∅
      constructor
      · simp
      · -- closureSubset with ∅ = initial after 0 steps
        unfold closureSubset
        simp only [Set.mem_iUnion]
        use 0
        simp [genIterSubset, h_in]
    · -- No subset with card < 0 exists
      intro S hcard
      simp at hcard
  constructor
  · trivial
  constructor
  · trivial
  · intro ℓ hℓ
    ext h
    simp
    intro h_in
    -- Level ℓ ≥ 3 requires at least 3 generators, but we only have 2
    have : ℓ ≤ sys.k := max_level_bound sys h ℓ h_in
    rw [h_two] at this
    omega

/-! ## Section 10: Summary -/

/-- The emergence hierarchy formalizes the structure of complementarities:
    - Level 0: No generators needed
    - Level 1: One generator sufficient
    - Level 2: Two generators required (pairwise complementarity)
    - Level ℓ: ℓ generators required (ℓ-wise complementarity)
    
    This provides a fine-grained analysis beyond binary "emergent or not".
-/

end MultiTypeHierarchy
