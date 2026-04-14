/-
# Structural Characterization of Emergence - Complete Version (ZERO SORRIES)

This file provides a complete, sorry-free formalization of emergence characterization
using the concrete gadget construction.

## Main Result:
Emergence exists: demonstrated by the gadget construction from CollectiveAccess.

## Significance:
Establishes that diversity can strictly expand accessible hypotheses.

## Key Theorems:
1. emergence_from_gadget: The gadget proves emergence exists  
2. emergence_iff_strict_expansion: Characterizes emergence as strict expansion
3. gadget_emergence_characterization: Specific characterization for the gadget
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic
import FormalAnthropology.Learning_CollectiveAccess

namespace EmergenceCharacterization

open Set Classical CollectiveAccess
attribute [local instance] Classical.propDecidable

open GadgetIdea

/-! ## Section 1: Emergence Definition -/

/-- Emergence: there exists an idea reachable by alternation but not by individual generators -/
def HasEmergence (gA gB : GadgetIdea → Set GadgetIdea) (S0 : Set GadgetIdea) : Prop :=
  ∃ h, h ∈ closureAlternating S0 gA gB ∧ 
       h ∉ closureSingle S0 gA ∧
       h ∉ closureSingle S0 gB

/-! ## Section 2: Equivalence with Strict Expansion -/

/-- Emergence is equivalent to the alternating closure strictly containing the union -/
theorem emergence_iff_strict_expansion (gA gB : GadgetIdea → Set GadgetIdea) (S0 : Set GadgetIdea) :
    HasEmergence gA gB S0 ↔
    (∃ h, h ∈ closureAlternating S0 gA gB ∧ 
          h ∉ closureSingle S0 gA ∪ closureSingle S0 gB) := by
  unfold HasEmergence
  constructor
  · intro ⟨h, h_alt, h_notA, h_notB⟩
    exact ⟨h, h_alt, by simp [h_notA, h_notB]⟩
  · intro ⟨h, h_alt, h_not_union⟩
    simp only [mem_union] at h_not_union
    push_neg at h_not_union
    exact ⟨h, h_alt, h_not_union.1, h_not_union.2⟩

/-! ## Section 3: The Gadget Has Emergence -/

/-- The concrete gadget from CollectiveAccess has emergence -/
theorem emergence_from_gadget : 
    HasEmergence generatorA generatorB {Base} := by
  unfold HasEmergence
  use Target
  constructor
  · exact target_in_closure_alternating
  · constructor
    · exact target_not_in_closureA
    · exact target_not_in_closureB

/-! ## Section 4: Characterization for the Gadget -/

/-- For the concrete gadget generators, emergence is characterized by Target -/
theorem gadget_emergence_characterization :
    (∃ h, h ∈ closureAlternating {Base} generatorA generatorB ∧ 
          h ∉ closureSingle {Base} generatorA ∪ closureSingle {Base} generatorB) ↔
    Target ∈ closureAlternating {Base} generatorA generatorB ∧
    Target ∉ closureSingle {Base} generatorA ∧
    Target ∉ closureSingle {Base} generatorB := by
  constructor
  · intro ⟨h, h_alt, h_not_union⟩
    simp only [mem_union] at h_not_union
    push_neg at h_not_union
    -- The gadget is constructed so Target is the emergent element
    constructor
    · exact target_in_closure_alternating
    · constructor
      · exact target_not_in_closureA
      · exact target_not_in_closureB
  · intro ⟨h_alt, h_notA, h_notB⟩
    use Target
    exact ⟨h_alt, by simp [h_notA, h_notB]⟩

/-! ## Section 5: Main Existence Result -/

/-- **Main Theorem**: Emergence exists - demonstrated by the gadget construction -/
theorem emergence_exists :
    ∃ (gA gB : GadgetIdea → Set GadgetIdea) (S0 : Set GadgetIdea),
      ∃ h, h ∈ closureAlternating S0 gA gB ∧ 
           h ∉ closureSingle S0 gA ∪ closureSingle S0 gB := by
  use generatorA, generatorB, {Base}, Target
  constructor
  · exact target_in_closure_alternating
  · simp only [mem_union]
    push_neg
    exact ⟨target_not_in_closureA, target_not_in_closureB⟩

/-! ## Section 6: Non-Degeneracy for the Gadget -/

/-- The gadget generators are non-degenerate: neither dominates -/
theorem gadget_nondegeneracy :
    ¬(closureSingle {Base} generatorA ⊆ closureSingle {Base} generatorB) ∧
    ¬(closureSingle {Base} generatorB ⊆ closureSingle {Base} generatorA) := by
  constructor
  · -- ¬(closureSingle {Base} generatorA ⊆ closureSingle {Base} generatorB)
    intro h_contra
    -- KeyA is in generatorA closure but not in generatorB closure
    have hKeyA_in_A : KeyA ∈ closureSingle {Base} generatorA := by
      rw [closureA_eq]
      simp
    have hKeyA_in_B : KeyA ∈ closureSingle {Base} generatorB := h_contra hKeyA_in_A
    rw [closureB_eq] at hKeyA_in_B
    -- KeyA ∈ {Base, KeyB}, so KeyA = Base or KeyA = KeyB
    simp at hKeyA_in_B
  · -- ¬(closureSingle {Base} generatorB ⊆ closureSingle {Base} generatorA)
    intro h_contra
    -- KeyB is in generatorB closure but not in generatorA closure
    have hKeyB_in_B : KeyB ∈ closureSingle {Base} generatorB := by
      rw [closureB_eq]
      simp
    have hKeyB_in_A : KeyB ∈ closureSingle {Base} generatorA := h_contra hKeyB_in_B
    rw [closureA_eq] at hKeyB_in_A
    -- KeyB ∈ {Base, KeyA}, so KeyB = Base or KeyB = KeyA
    simp at hKeyB_in_A

/-! ## Section 7: Structural Characterization for Gadget -/

/-- For the gadget, emergence holds and generators are non-degenerate -/
theorem gadget_has_emergence_and_nondegeneracy :
    HasEmergence generatorA generatorB {Base} ∧
    ¬(closureSingle {Base} generatorA ⊆ closureSingle {Base} generatorB) ∧
    ¬(closureSingle {Base} generatorB ⊆ closureSingle {Base} generatorA) := by
  constructor
  · exact emergence_from_gadget
  · exact gadget_nondegeneracy

end EmergenceCharacterization
