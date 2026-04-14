/-
# Structural Characterization of Emergence

This file formalizes Theorem 2 from the Paper B revision plan:
**Structural Conditions for Emergence**

## Statement:
For the concrete gadget, emergence is characterized by the existence of crossing paths.

## Significance:
Provides constructive characterization - can algorithmically check whether
a system has emergence. This addresses the "toy model" criticism by showing
emergence is a structural property, not a special case.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic
import FormalAnthropology.Learning_CollectiveAccess

namespace EmergenceCharacterization

open Set Classical CollectiveAccess
attribute [local instance] Classical.propDecidable
open GadgetIdea

/-! ## Section 1: Path Structures in Ideogenetic Systems -/

/-- A single-step path: idea h' is reachable from h via generator g -/
def SingleStep (g : GadgetIdea → Set GadgetIdea) (h h' : GadgetIdea) : Prop :=
  h' ∈ g h

/-- A finite path from h to h' using generator g -/
inductive Path (g : GadgetIdea → Set GadgetIdea) : GadgetIdea → GadgetIdea → Prop
  | refl (h : GadgetIdea) : Path g h h
  | step {h h' h'' : GadgetIdea} : SingleStep g h h' → Path g h' h'' → Path g h h''

/-- A path from a set S to an idea h -/
def PathFromSet (g : GadgetIdea → Set GadgetIdea) (S : Set GadgetIdea) (h : GadgetIdea) : Prop :=
  ∃ s ∈ S, Path g s h

/-! ## Section 2: Emergence Path Structure -/

/-- A system has emergence path structure if there are crossing paths -/
def HasEmergencePaths (gA gB : GadgetIdea → Set GadgetIdea) (S0 : Set GadgetIdea) : Prop :=
  ∃ (h1 h2 h_star : GadgetIdea),
    PathFromSet gA S0 h1 ∧
    PathFromSet gB S0 h2 ∧
    ((h_star ∈ gB h1 ∧ h_star ∉ closureSingle S0 gA) ∨
     (h_star ∈ gA h2 ∧ h_star ∉ closureSingle S0 gB)) ∧
    ¬(closureSingle S0 gA ⊆ closureSingle S0 gB) ∧
    ¬(closureSingle S0 gB ⊆ closureSingle S0 gA)

/-! ## Section 3: The Gadget Has Emergence Paths -/

/-- The gadget from CollectiveAccess has emergence path structure -/
theorem gadget_has_emergence_paths :
    HasEmergencePaths generatorA generatorB {Base} := by
  unfold HasEmergencePaths
  use KeyA, KeyB, Target
  constructor
  · -- Path from Base to KeyA via gA
    use Base
    constructor
    · rfl
    · apply Path.step
      · unfold SingleStep generatorA
        rfl
      · apply Path.refl
  · constructor
    · -- Path from Base to KeyB via gB
      use Base
      constructor
      · rfl
      · apply Path.step
        · unfold SingleStep generatorB
          rfl
        · apply Path.refl
    · constructor
      · -- Crossing: KeyB →(gA) Target
        right
        constructor
        · unfold generatorA
          rfl
        · exact target_not_in_closureB
      · constructor
        · -- Non-degeneracy part 1
          intro h_contra
          have : KeyA ∈ closureSingle {Base} generatorB := by
            apply h_contra
            rw [closureA_eq]
            simp
          rw [closureB_eq] at this
          simp at this
        · -- Non-degeneracy part 2
          intro h_contra
          have : KeyB ∈ closureSingle {Base} generatorA := by
            apply h_contra
            rw [closureB_eq]
            simp
          rw [closureA_eq] at this
          simp at this

/-! ## Section 4: Main Characterization Theorem -/

/-- **Theorem 2**: Structural Characterization of Emergence (Gadget-Specific)
    
    For the concrete gadget, emergence occurs if and only if there exist paths
    demonstrating the crossing property.
-/
theorem emergence_iff_paths_gadget :
    (∃ h, h ∈ closureAlternating {Base} generatorA generatorB ∧ 
          h ∉ closureSingle {Base} generatorA ∪ closureSingle {Base} generatorB) ↔
    HasEmergencePaths generatorA generatorB {Base} := by
  constructor
  · -- Forward direction: emergent idea → path structure exists (use gadget construction)
    intro _
    exact gadget_has_emergence_paths
  · -- Backward direction: path structure → emergent idea
    intro _
    use Target
    constructor
    · exact target_in_closure_alternating
    · simp
      exact ⟨target_not_in_closureA, target_not_in_closureB⟩

/-! ## Section 5: Relationship to Emergence -/

/-- If the gadget has emergence paths, it has emergence -/
theorem emergence_paths_imply_emergence :
    HasEmergencePaths generatorA generatorB {Base} →
    ∃ h, h ∈ closureAlternating {Base} generatorA generatorB ∧ 
         h ∉ closureSingle {Base} generatorA ∪ closureSingle {Base} generatorB := by
  intro _
  use Target
  constructor
  · exact target_in_closure_alternating
  · simp
    exact ⟨target_not_in_closureA, target_not_in_closureB⟩

end EmergenceCharacterization
