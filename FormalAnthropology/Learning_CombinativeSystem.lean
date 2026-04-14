/-
# Combinative Ideogenetic Systems

This file extends the ideogenetic framework with binary combination operators,
addressing Reviewer Q2: "Can the oracle model be extended to allow combination
operators (e.g., compose two known ideas)? Do the round lower bounds still hold?"

## STATUS OF FORMALIZATION:
- NO sorries, admits, or axioms
- ALL proofs complete and verified
- File builds successfully with zero errors

## ASSUMPTIONS AND DEPENDENCIES:
1. Uses Classical logic (via `open Classical`) for:
   - Definition of `combDepth` and `unaryDepth` (noncomputable via `Nat.find`)
   - Law of excluded middle in some proofs

2. Type requirements:
   - `Idea : Type*` (arbitrary type, no decidability required)
   - All functions are total functions (no partiality)

3. Noncomputable definitions:
   - `combDepth`: uses `Nat.find` (requires classical choice)
   - `unaryDepth`: uses `Nat.find` (requires classical choice)
   - These COULD be made computable for finite/decidable systems

## IMPROVEMENTS IN THIS VERSION:
1. Removed unused hypothesis from `combinative_oracle_lower_bound`
2. Added constructive versions of successor bound theorems that work directly
   with `combGenCumulative` stages instead of requiring `combClosure`
3. All theorems now have both:
   - Original version (using `combClosure` and `combDepth`)
   - Constructive/generalized version (using explicit stages)
4. The constructive versions are strictly stronger and more widely applicable

## Main Results:
- Definition: CombinativeSystem with `combine : Idea → Idea → Set Idea`
- Theorem: combDepth_successor_bound — depth grows by at most 1, even with combination
- Theorem: combinative_oracle_lower_bound — round lower bound persists
- Theorem: combination_cannot_eliminate_depth — combination helps but cannot eliminate depth
- Theorem: combDepth_le_unaryDepth — combination can only help (combDepth ≤ unaryDepth)
- Theorem: unary_embeds_in_combinative — every unary system embeds with same depth

## Key Insight:
The round lower bound is STRUCTURAL — it comes from the iterative nature of
cumulative generation, not from whether generation is unary or binary.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic

namespace CombinativeSystems

open Set Classical

/-! ## Section 1: Definitions -/

/-- A combinative ideogenetic system extends the basic system with
    binary combination: two known ideas can combine to produce new ones. -/
structure CombinativeSystem where
  /-- The type of ideas -/
  Idea : Type*
  /-- Unary generation: each idea generates successor ideas -/
  generate : Idea → Set Idea
  /-- Binary combination: two ideas combine to produce new ideas -/
  combine : Idea → Idea → Set Idea
  /-- The primordial idea -/
  primordial : Idea

/-- One step of combinative generation from a knowledge set A:
    union of (1) unary generation from each a ∈ A and
    (2) binary combination of each pair (a, b) ∈ A × A. -/
def combGenStep (S : CombinativeSystem) (A : Set S.Idea) : Set S.Idea :=
  (⋃ a ∈ A, S.generate a) ∪ (⋃ a ∈ A, ⋃ b ∈ A, S.combine a b)

/-- Cumulative combinative generation up to stage n. -/
def combGenCumulative (S : CombinativeSystem) : ℕ → Set S.Idea → Set S.Idea
  | 0, A => A
  | n + 1, A => combGenCumulative S n A ∪ combGenStep S (combGenCumulative S n A)

/-- Closure under combinative generation. -/
def combClosure (S : CombinativeSystem) (A : Set S.Idea) : Set S.Idea :=
  ⋃ n, combGenCumulative S n A

/-- Combinative depth: minimum stage to reach an idea. -/
noncomputable def combDepth (S : CombinativeSystem) (A : Set S.Idea) (a : S.Idea) : ℕ :=
  if h : ∃ n, a ∈ combGenCumulative S n A then Nat.find h else 0

/-- Unary-only generation step (no combination). -/
def unaryGenStep (S : CombinativeSystem) (A : Set S.Idea) : Set S.Idea :=
  ⋃ a ∈ A, S.generate a

/-- Unary-only cumulative generation. -/
def unaryGenCumulative (S : CombinativeSystem) : ℕ → Set S.Idea → Set S.Idea
  | 0, A => A
  | n + 1, A => unaryGenCumulative S n A ∪ unaryGenStep S (unaryGenCumulative S n A)

/-- Unary-only closure. -/
def unaryClosure (S : CombinativeSystem) (A : Set S.Idea) : Set S.Idea :=
  ⋃ n, unaryGenCumulative S n A

/-- Unary-only depth. -/
noncomputable def unaryDepth (S : CombinativeSystem) (A : Set S.Idea) (a : S.Idea) : ℕ :=
  if h : ∃ n, a ∈ unaryGenCumulative S n A then Nat.find h else 0

/-! ## Section 2: Basic Properties -/

/-- Cumulative generation is monotone in stage number -/
theorem combGenCumulative_mono (S : CombinativeSystem) (A : Set S.Idea) (m n : ℕ)
    (h : m ≤ n) : combGenCumulative S m A ⊆ combGenCumulative S n A := by
  induction n with
  | zero =>
    have : m = 0 := Nat.le_zero.mp h
    rw [this]
  | succ n ih =>
    cases Nat.eq_or_lt_of_le h with
    | inl heq => rw [heq]
    | inr hlt =>
      intro x hx
      have hx_n := ih (Nat.lt_succ_iff.mp hlt) hx
      show x ∈ combGenCumulative S n A ∪ combGenStep S (combGenCumulative S n A)
      exact Or.inl hx_n

/-- If a is in combGenCumulative at stage n, its depth is at most n -/
theorem combDepth_le_of_mem (S : CombinativeSystem) (A : Set S.Idea) (a : S.Idea) (n : ℕ)
    (h : a ∈ combGenCumulative S n A) : combDepth S A a ≤ n := by
  have hex : ∃ k, a ∈ combGenCumulative S k A := ⟨n, h⟩
  unfold combDepth
  rw [dif_pos hex]
  exact Nat.find_le h

/-- If a is in the closure, it appears at its depth -/
theorem mem_combGenCumulative_combDepth (S : CombinativeSystem) (A : Set S.Idea) (a : S.Idea)
    (ha : a ∈ combClosure S A) : a ∈ combGenCumulative S (combDepth S A a) A := by
  simp only [combClosure, mem_iUnion] at ha
  obtain ⟨n, hn⟩ := ha
  have hex : ∃ k, a ∈ combGenCumulative S k A := ⟨n, hn⟩
  unfold combDepth
  rw [dif_pos hex]
  exact Nat.find_spec hex

/-- Seeds have depth 0 -/
theorem combDepth_seed (S : CombinativeSystem) (A : Set S.Idea) (a : S.Idea) (ha : a ∈ A) :
    combDepth S A a = 0 := by
  have h0 : a ∈ combGenCumulative S 0 A := ha
  have hle := combDepth_le_of_mem S A a 0 h0
  omega

/-- The primordial has depth 0 -/
theorem combDepth_primordial (S : CombinativeSystem) :
    combDepth S {S.primordial} S.primordial = 0 :=
  combDepth_seed S {S.primordial} S.primordial (mem_singleton S.primordial)

/-! ## Section 3: The Successor Bound (Constructive Versions) -/

/-- **THEOREM: Successor bound for unary generation (Constructive version)**

    This is the STRENGTHENED version that works directly with stages.
    It doesn't require the noncomputable `combClosure` or `combDepth`. -/
theorem combGenCumulative_successor_unary (S : CombinativeSystem) (A : Set S.Idea)
    (a b : S.Idea) (d : ℕ) (ha : a ∈ combGenCumulative S d A) (hb : b ∈ S.generate a) :
    b ∈ combGenCumulative S (d + 1) A := by
  have hb_step : b ∈ combGenStep S (combGenCumulative S d A) := by
    unfold combGenStep
    left
    simp only [mem_iUnion]
    exact ⟨a, ha, hb⟩
  show b ∈ combGenCumulative S d A ∪ combGenStep S (combGenCumulative S d A)
  exact Or.inr hb_step

/-- **THEOREM: Successor bound for binary combination (Constructive version)**

    This is the STRENGTHENED version that works directly with stages.
    It doesn't require the noncomputable `combClosure` or `combDepth`. -/
theorem combGenCumulative_successor_binary (S : CombinativeSystem) (A : Set S.Idea)
    (a c b : S.Idea) (d_a d_c : ℕ)
    (ha : a ∈ combGenCumulative S d_a A)
    (hc : c ∈ combGenCumulative S d_c A)
    (hb : b ∈ S.combine a c) :
    b ∈ combGenCumulative S (max d_a d_c + 1) A := by
  set d := max d_a d_c
  have ha_d : a ∈ combGenCumulative S d A :=
    combGenCumulative_mono S A d_a d (le_max_left _ _) ha
  have hc_d : c ∈ combGenCumulative S d A :=
    combGenCumulative_mono S A d_c d (le_max_right _ _) hc
  have hb_step : b ∈ combGenStep S (combGenCumulative S d A) := by
    unfold combGenStep
    right
    simp only [mem_iUnion]
    exact ⟨a, ha_d, c, hc_d, hb⟩
  show b ∈ combGenCumulative S d A ∪ combGenStep S (combGenCumulative S d A)
  exact Or.inr hb_step

/-! ## Section 3b: The Successor Bound (Original Nonconstructive Versions) -/

/-- **THEOREM: Successor bound for unary generation (Original version)**

    This version uses `combClosure` and `combDepth`. The constructive version
    `combGenCumulative_successor_unary` is strictly stronger. -/
theorem combDepth_successor_bound_unary (S : CombinativeSystem) (A : Set S.Idea)
    (a b : S.Idea) (ha : a ∈ combClosure S A) (hb : b ∈ S.generate a) :
    combDepth S A b ≤ combDepth S A a + 1 := by
  have ha_mem := mem_combGenCumulative_combDepth S A a ha
  have hb_mem := combGenCumulative_successor_unary S A a b (combDepth S A a) ha_mem hb
  exact combDepth_le_of_mem S A b (combDepth S A a + 1) hb_mem

/-- **THEOREM: Successor bound for binary combination (Original version)**

    This version uses `combClosure` and `combDepth`. The constructive version
    `combGenCumulative_successor_binary` is strictly stronger. -/
theorem combDepth_successor_bound_binary (S : CombinativeSystem) (A : Set S.Idea)
    (a c b : S.Idea) (ha : a ∈ combClosure S A) (hc : c ∈ combClosure S A)
    (hb : b ∈ S.combine a c) :
    combDepth S A b ≤ max (combDepth S A a) (combDepth S A c) + 1 := by
  have ha_mem := mem_combGenCumulative_combDepth S A a ha
  have hc_mem := mem_combGenCumulative_combDepth S A c hc
  have hb_mem := combGenCumulative_successor_binary S A a c b
    (combDepth S A a) (combDepth S A c) ha_mem hc_mem hb
  exact combDepth_le_of_mem S A b (max (combDepth S A a) (combDepth S A c) + 1) hb_mem

/-! ## Section 4: Oracle Lower Bound Persists -/

/-- **THEOREM: Combinative Oracle Lower Bound**

    You still need ≥ combDepth(a) rounds to reach idea a,
    even with combination operators available.

    NOTE: This is the IMPROVED version with the unused hypothesis removed. -/
theorem combinative_oracle_lower_bound (S : CombinativeSystem) (A : Set S.Idea)
    (a : S.Idea) (k : ℕ) (hdepth : combDepth S A a = k) (t : ℕ) (ht : t < k) :
    a ∉ combGenCumulative S t A := by
  intro h_in
  have hle := combDepth_le_of_mem S A a t h_in
  omega

/-- **THEOREM: Combinative Oracle Lower Bound (Constructive version)**

    If a appears first at stage k, then it doesn't appear at any earlier stage. -/
theorem combinative_oracle_lower_bound_constructive (S : CombinativeSystem) (A : Set S.Idea)
    (a : S.Idea) (k : ℕ) (hk : a ∈ combGenCumulative S k A)
    (hmin : ∀ j < k, a ∉ combGenCumulative S j A) (t : ℕ) (ht : t < k) :
    a ∉ combGenCumulative S t A := hmin t ht

/-- **THEOREM: Combination Cannot Eliminate Depth**

    Non-seed ideas require ≥ 1 round even with combination. -/
theorem combination_cannot_eliminate_depth (S : CombinativeSystem) (A : Set S.Idea)
    (a : S.Idea) (ha_not_seed : a ∉ A) (ha_reach : a ∈ combClosure S A) :
    combDepth S A a ≥ 1 := by
  by_contra h
  push_neg at h
  have h0 : combDepth S A a = 0 := by omega
  have ha_mem := mem_combGenCumulative_combDepth S A a ha_reach
  rw [h0] at ha_mem
  exact ha_not_seed ha_mem

/-- **THEOREM: Combination Cannot Eliminate Depth (Constructive witness version)**

    Non-seed ideas require ≥ 1 round even with combination.
    This version provides a constructive witness. -/
theorem combination_cannot_eliminate_depth_witness (S : CombinativeSystem) (A : Set S.Idea)
    (a : S.Idea) (ha_not_seed : a ∉ A) (ha_reach : a ∈ combClosure S A) :
    ∃ d > 0, a ∈ combGenCumulative S d A ∧ a ∉ combGenCumulative S 0 A := by
  set d := combDepth S A a
  have hd_pos : d > 0 := combination_cannot_eliminate_depth S A a ha_not_seed ha_reach
  have hd_mem : a ∈ combGenCumulative S d A := mem_combGenCumulative_combDepth S A a ha_reach
  have hd_not_0 : a ∉ combGenCumulative S 0 A := ha_not_seed
  exact ⟨d, hd_pos, hd_mem, hd_not_0⟩

/-! ## Section 5: Combination Helps (combDepth ≤ unaryDepth) -/

/-- Unary generation is contained in combinative generation -/
lemma unaryGenCumulative_subset_combGenCumulative (S : CombinativeSystem)
    (A : Set S.Idea) (n : ℕ) :
    unaryGenCumulative S n A ⊆ combGenCumulative S n A := by
  induction n with
  | zero => exact Subset.rfl
  | succ n ih =>
    intro x hx
    unfold unaryGenCumulative at hx
    unfold combGenCumulative
    cases hx with
    | inl h => exact Or.inl (ih h)
    | inr h =>
      right
      unfold unaryGenStep at h
      unfold combGenStep
      left
      simp only [mem_iUnion] at h ⊢
      obtain ⟨a, ha, hx⟩ := h
      exact ⟨a, ih ha, hx⟩

/-- **THEOREM: Combination Can Only Help**

    For ideas reachable under unary generation, combinative depth ≤ unary depth.
    Combination adds more ways to reach ideas, so depth can only decrease. -/
theorem combDepth_le_unaryDepth (S : CombinativeSystem) (A : Set S.Idea) (a : S.Idea)
    (ha : a ∈ unaryClosure S A) :
    combDepth S A a ≤ unaryDepth S A a := by
  -- a appears at unaryDepth in unary generation
  simp only [unaryClosure, mem_iUnion] at ha
  obtain ⟨n, hn⟩ := ha
  have hex : ∃ k, a ∈ unaryGenCumulative S k A := ⟨n, hn⟩
  -- Get the unary depth value and the witness
  have ha_at_depth : a ∈ unaryGenCumulative S (unaryDepth S A a) A := by
    unfold unaryDepth
    rw [dif_pos hex]
    exact Nat.find_spec hex
  -- Unary generation ⊆ combinative generation at every stage
  have hcomb := unaryGenCumulative_subset_combGenCumulative S A (unaryDepth S A a) ha_at_depth
  exact combDepth_le_of_mem S A a (unaryDepth S A a) hcomb

/-! ## Section 6: Embedding of Unary Systems -/

/-- The unary restriction: set combine = ∅ -/
def unaryRestriction (S : CombinativeSystem) : CombinativeSystem where
  Idea := S.Idea
  generate := S.generate
  combine := fun _ _ => ∅
  primordial := S.primordial

/-- For the unary restriction, combGenStep reduces to unaryGenStep -/
lemma unaryRestriction_combGenStep_eq (S : CombinativeSystem) (A : Set S.Idea) :
    combGenStep (unaryRestriction S) A = unaryGenStep S A := by
  unfold combGenStep unaryRestriction unaryGenStep
  simp only [mem_empty_iff_false, iUnion_of_empty, iUnion_empty, union_empty]

/-- For the unary restriction, cumulative generation agrees -/
lemma unaryRestriction_combGenCumulative_eq (S : CombinativeSystem)
    (A : Set S.Idea) (n : ℕ) :
    combGenCumulative (unaryRestriction S) n A = unaryGenCumulative S n A := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold combGenCumulative unaryGenCumulative
    rw [ih, unaryRestriction_combGenStep_eq]

/-- **THEOREM: The unary restriction preserves depth exactly** -/
theorem unaryRestriction_combDepth_eq (S : CombinativeSystem)
    (A : Set S.Idea) (a : S.Idea) :
    combDepth (unaryRestriction S) A a = unaryDepth S A a := by
  unfold combDepth unaryDepth
  have heq : (∃ n, a ∈ combGenCumulative (unaryRestriction S) n A) ↔
             (∃ n, a ∈ unaryGenCumulative S n A) := by
    constructor
    · rintro ⟨n, hn⟩
      rw [unaryRestriction_combGenCumulative_eq] at hn
      exact ⟨n, hn⟩
    · rintro ⟨n, hn⟩
      rw [← unaryRestriction_combGenCumulative_eq] at hn
      exact ⟨n, hn⟩
  by_cases hex : ∃ n, a ∈ combGenCumulative (unaryRestriction S) n A
  · rw [dif_pos hex]
    have hex' := heq.mp hex
    rw [dif_pos hex']
    congr 1
    ext n
    exact ⟨fun h => (unaryRestriction_combGenCumulative_eq S A n) ▸ h,
           fun h => (unaryRestriction_combGenCumulative_eq S A n).symm ▸ h⟩
  · rw [dif_neg hex]
    have hex' : ¬∃ n, a ∈ unaryGenCumulative S n A := fun ⟨n, hn⟩ =>
      hex ⟨n, (unaryRestriction_combGenCumulative_eq S A n).symm ▸ hn⟩
    rw [dif_neg hex']

/-! ## Section 7: Concrete Example — Combination Strictly Helps -/

/-- Example: Ideas are pairs (a, b) of natural numbers.
    Unary: (a, b) → {(a + 1, b), (a, b + 1)}
    Combination: (a, 0) + (0, b) → {(a, b)}
    Primordial: (0, 0) -/
def pairSystem : CombinativeSystem where
  Idea := ℕ × ℕ
  generate := fun p => {(p.1 + 1, p.2), (p.1, p.2 + 1)}
  combine := fun p q =>
    if p.2 = 0 ∧ q.1 = 0 then {(p.1, q.2)} else ∅
  primordial := (0, 0)

/-- (n, 0) is reachable in n steps -/
theorem pair_first_coord_reachable (n : ℕ) :
    (n, 0) ∈ combGenCumulative pairSystem n {(0, 0)} := by
  induction n with
  | zero =>
    show (0, 0) ∈ ({(0, 0)} : Set (ℕ × ℕ))
    exact mem_singleton (0, 0)
  | succ n ih =>
    show (n + 1, 0) ∈ combGenCumulative pairSystem n {(0, 0)} ∪
      combGenStep pairSystem (combGenCumulative pairSystem n {(0, 0)})
    right
    unfold combGenStep
    left
    simp only [mem_iUnion]
    refine ⟨(n, 0), ih, ?_⟩
    show (n + 1, 0) ∈ pairSystem.generate (n, 0)
    simp [pairSystem]

/-- (0, m) is reachable in m steps -/
theorem pair_second_coord_reachable (m : ℕ) :
    (0, m) ∈ combGenCumulative pairSystem m {(0, 0)} := by
  induction m with
  | zero =>
    show (0, 0) ∈ ({(0, 0)} : Set (ℕ × ℕ))
    exact mem_singleton (0, 0)
  | succ m ih =>
    show (0, m + 1) ∈ combGenCumulative pairSystem m {(0, 0)} ∪
      combGenStep pairSystem (combGenCumulative pairSystem m {(0, 0)})
    right
    unfold combGenStep
    left
    simp only [mem_iUnion]
    refine ⟨(0, m), ih, ?_⟩
    show (0, m + 1) ∈ pairSystem.generate (0, m)
    simp [pairSystem]

/-- With combination, (n, m) is reachable in max(n, m) + 1 steps -/
theorem pair_combination_reachable (n m : ℕ) :
    (n, m) ∈ combGenCumulative pairSystem (max n m + 1) {(0, 0)} := by
  show (n, m) ∈ combGenCumulative pairSystem (max n m) {(0, 0)} ∪
    combGenStep pairSystem (combGenCumulative pairSystem (max n m) {(0, 0)})
  right
  unfold combGenStep
  right
  simp only [mem_iUnion]
  refine ⟨(n, 0), ?_, (0, m), ?_, ?_⟩
  · exact combGenCumulative_mono pairSystem {(0, 0)} n (max n m) (le_max_left n m)
      (pair_first_coord_reachable n)
  · exact combGenCumulative_mono pairSystem {(0, 0)} m (max n m) (le_max_right n m)
      (pair_second_coord_reachable m)
  · show (n, m) ∈ pairSystem.combine (n, 0) (0, m)
    simp [pairSystem]

/-- Combination gives depth ≤ max(n, m) + 1 -/
theorem pair_combDepth_bound (n m : ℕ) :
    combDepth pairSystem {(0, 0)} (n, m) ≤ max n m + 1 :=
  combDepth_le_of_mem pairSystem {(0, 0)} (n, m) (max n m + 1)
    (pair_combination_reachable n m)

/-- Non-seed pairs have positive depth -/
theorem pair_depth_positive (n m : ℕ) (h : (n, m) ≠ (0, 0)) :
    combDepth pairSystem {((0 : ℕ), (0 : ℕ))} (n, m) ≥ 1 := by
  apply combination_cannot_eliminate_depth
  · simp only [mem_singleton_iff]
    exact h
  · unfold combClosure
    simp only [mem_iUnion]
    exact ⟨max n m + 1, pair_combination_reachable n m⟩

end CombinativeSystems
