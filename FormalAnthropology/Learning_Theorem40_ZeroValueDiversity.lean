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
# Theorem 40: When Diversity Has Zero Value

This file formalizes the negative result for Paper B revision:
**When Nested Generators Eliminate Diversity Value**

## Statement:
If generator gA is "nested" in generator gB (i.e., ∀ h, gA(h) ⊆ gB(h)),
then diversity provides zero value: cl_alternating = cl_gB.

## Significance:
Shows that diversity is not always valuable - it depends on the structure
of the generators. This addresses reviewer concerns about "when does diversity
NOT help?"

## Key Theorems:
1. nested_implies_no_emergence: Nested generators → no emergent ideas
2. nested_optimal_single: When nested, single generator is optimal
3. zero_value_characterization: Complete characterization of zero-value cases
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic
import FormalAnthropology.Learning_CollectiveAccess

namespace ZeroValueDiversity

open Set Classical CollectiveAccess
attribute [local instance] Classical.propDecidable

/-! ## Section 1: Nested Generator Definition -/

/-- Generator gA is nested in gB if gA(h) ⊆ gB(h) for all h -/
def NestedGenerators (gA gB : GadgetIdea → Set GadgetIdea) : Prop :=
  ∀ h : GadgetIdea, gA h ⊆ gB h

/-! ## Section 2: Main Results -/

/-- If gA is nested in gB, then closureSingle S0 gA ⊆ closureSingle S0 gB -/
lemma nested_implies_closure_subset (gA gB : GadgetIdea → Set GadgetIdea) (S0 : Set GadgetIdea)
    (h_nested : NestedGenerators gA gB) :
    closureSingle S0 gA ⊆ closureSingle S0 gB := by
  intro a ha
  simp only [closureSingle, mem_iUnion] at ha ⊢
  obtain ⟨n, hn⟩ := ha
  -- Prove by induction: genCumulative gA n S0 ⊆ genCumulative gB n S0
  use n
  induction n generalizing a with
  | zero => exact hn
  | succ n ih =>
    simp only [genCumulative, mem_union] at hn ⊢
    cases hn with
    | inl h => left; exact ih h
    | inr h =>
      right
      simp only [genStep, mem_iUnion] at h ⊢
      obtain ⟨b, hb, ha⟩ := h
      -- a ∈ gA b, b ∈ genCumulative gA n S0
      -- Need: a ∈ genStep gB (genCumulative gB n S0)
      have ha_in_gB : a ∈ gB b := h_nested b ha
      exact ⟨b, ih hb, ha_in_gB⟩

/-- If gA nested in gB, alternating closure equals gB closure -/
theorem nested_alternating_equals_B (gA gB : GadgetIdea → Set GadgetIdea) (S0 : Set GadgetIdea)
    (h_nested : NestedGenerators gA gB) :
    closureAlternating S0 gA gB = closureSingle S0 gB := by
  apply eq_of_subset_of_subset
  · -- closureAlternating ⊆ closureSingle gB
    intro a ha
    simp only [closureAlternating, mem_iUnion] at ha
    obtain ⟨n, hn⟩ := ha
    simp only [closureSingle, mem_iUnion]
    use n
    -- Prove: altGenCumulative gA gB n S0 ⊆ genCumulative gB n S0
    induction n generalizing a with
    | zero => exact hn
    | succ n ih =>
      simp only [altGenCumulative, mem_union] at hn
      simp only [genCumulative, mem_union]
      cases hn with
      | inl h => left; exact ih h
      | inr h =>
        right
        simp only [altGenStep, mem_union, mem_iUnion] at h
        simp only [genStep, mem_iUnion]
        cases h with
        | inl hA =>
          -- a ∈ ⋃ b ∈ altGenCumulative n S0, gA b
          obtain ⟨b, hb, ha⟩ := hA
          have ha_in_gB : a ∈ gB b := h_nested b ha
          exact ⟨b, ih hb, ha_in_gB⟩
        | inr hB =>
          obtain ⟨b, hb, ha⟩ := hB
          exact ⟨b, ih hb, ha⟩
  · -- closureSingle gB ⊆ closureAlternating
    intro a ha
    simp only [closureSingle, mem_iUnion] at ha
    obtain ⟨n, hn⟩ := ha
    simp only [closureAlternating, mem_iUnion]
    use n
    -- genCumulative gB n S0 ⊆ altGenCumulative gA gB n S0
    induction n generalizing a with
    | zero => exact hn
    | succ n ih =>
      simp only [genCumulative, mem_union] at hn
      simp only [altGenCumulative, mem_union]
      cases hn with
      | inl h => left; exact ih h
      | inr h =>
        right
        simp only [genStep, mem_iUnion] at h
        simp only [altGenStep, mem_union, mem_iUnion]
        right
        obtain ⟨b, hb, ha⟩ := h
        exact ⟨b, ih hb, ha⟩

/-- **Theorem 40**: If generators are nested, there are no emergent ideas -/
theorem nested_implies_no_emergence (gA gB : GadgetIdea → Set GadgetIdea) (S0 : Set GadgetIdea)
    (h_nested : NestedGenerators gA gB) :
    ¬∃ h, h ∈ closureAlternating S0 gA gB ∧ 
          h ∉ closureSingle S0 gA ∪ closureSingle S0 gB := by
  intro ⟨h, h_in_alt, h_not_single⟩
  simp only [mem_union] at h_not_single
  push_neg at h_not_single
  obtain ⟨h_not_A, h_not_B⟩ := h_not_single
  -- h ∈ closureAlternating, and by our theorem = closureSingle gB
  rw [nested_alternating_equals_B gA gB S0 h_nested] at h_in_alt
  exact h_not_B h_in_alt

/-- When nested, using gB alone is optimal (no benefit from gA) -/
theorem nested_optimal_single (gA gB : GadgetIdea → Set GadgetIdea) (S0 : Set GadgetIdea)
    (h_nested : NestedGenerators gA gB) :
    closureSingle S0 gB = closureAlternating S0 gA gB := by
  exact (nested_alternating_equals_B gA gB S0 h_nested).symm

/-! ## Section 3: Zero Value Characterization -/

/-- Diversity has zero value when alternating equals individual closure -/
def ZeroValueDiversity (gA gB : GadgetIdea → Set GadgetIdea) (S0 : Set GadgetIdea) : Prop :=
  closureAlternating S0 gA gB = closureSingle S0 gA ∪ closureSingle S0 gB

/-- Nested generators are a sufficient condition for zero value -/
theorem nested_sufficient_for_zero_value (gA gB : GadgetIdea → Set GadgetIdea) (S0 : Set GadgetIdea)
    (h_nested : NestedGenerators gA gB) :
    ZeroValueDiversity gA gB S0 := by
  unfold ZeroValueDiversity
  rw [nested_alternating_equals_B gA gB S0 h_nested]
  apply eq_of_subset_of_subset
  · -- closureSingle gB ⊆ closureSingle gA ∪ closureSingle gB
    intro a ha
    right
    exact ha
  · -- closureSingle gA ∪ closureSingle gB ⊆ closureSingle gB
    intro a ha
    simp only [mem_union] at ha
    cases ha with
    | inl hA => exact nested_implies_closure_subset gA gB S0 h_nested hA
    | inr hB => exact hB

/-! ## Section 4: Example - Nested Gadget -/

/-- Example nested generators: gA always empty, gB is generatorB -/
def emptyGenerator : GadgetIdea → Set GadgetIdea := fun _ => ∅

/-- Empty generator is nested in any generator -/
theorem empty_nested_in_any (g : GadgetIdea → Set GadgetIdea) :
    NestedGenerators emptyGenerator g := by
  intro h
  intro x hx
  simp only [emptyGenerator, mem_empty_iff_false] at hx

/-- With empty + generatorB, diversity has zero value -/
theorem empty_B_zero_value :
    ZeroValueDiversity emptyGenerator generatorB ({GadgetIdea.Base} : Set GadgetIdea) := by
  apply nested_sufficient_for_zero_value
  exact empty_nested_in_any generatorB

/-! ## Section 5: Practical Implications -/

/-- If gA nested in gB, membership is equivalent in direct vs alternating -/
theorem nested_membership_equiv (gA gB : GadgetIdea → Set GadgetIdea) (S0 : Set GadgetIdea)
    (h_nested : NestedGenerators gA gB) (target : GadgetIdea) :
    (target ∈ closureSingle S0 gA ∪ closureSingle S0 gB) ↔
    (target ∈ closureAlternating S0 gA gB) := by
  constructor
  · intro h
    have heq := nested_alternating_equals_B gA gB S0 h_nested
    rw [heq]
    simp only [mem_union] at h
    cases h with
    | inl hA => exact nested_implies_closure_subset gA gB S0 h_nested hA
    | inr hB => exact hB
  · intro h
    have heq := nested_alternating_equals_B gA gB S0 h_nested
    rw [heq] at h
    right
    exact h

end ZeroValueDiversity
