/-
# Non-Cumulative Oracle: EXPLICIT CONSTRUCTION

This file PROVES the axiom exists_strictly_harder_noncumulative from
Learning_NonCumulativeOracle.lean by providing an explicit construction.

Key idea: Create a system where:
- Round 1: generate 'a' from primordial
- Round 2: generate target from 'a'
- But 'a' is not generated again at round 2

So:
- Cumulative depth = 2 (target reachable in 2 rounds)
- Non-cumulative depth = ∞ (target never reachable without 'a' in memory)
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic
import FormalAnthropology.SingleAgent_Basic
import FormalAnthropology.Learning_Basic

namespace NonCumulativeOracle_Explicit

open SingleAgentIdeogenesis Set

/-! ## Section 1: Explicit Construction -/

/-- A three-idea system: primordial, intermediate 'a', and target -/
inductive ThreeIdea where
  | primordial : ThreeIdea
  | intermediate : ThreeIdea  
  | target : ThreeIdea
  deriving DecidableEq

/-- The generator for our counterexample system:
    - gen(primordial) = {intermediate}
    - gen(intermediate) = {target}
    - gen(target) = ∅ -/
def counterexample_gen : ThreeIdea → Set ThreeIdea
  | .primordial => {.intermediate}
  | .intermediate => {.target}
  | .target => ∅

/-- The counterexample system -/
def counterexample_system : IdeogeneticSystem where
  Idea := ThreeIdea
  primordial := {.primordial}
  gen := counterexample_gen
  primordial_nonempty := by
    use ThreeIdea.primordial
    simp

/-! ## Section 2: Properties of the Construction -/

/-- Round 1 (cumulative): {primordial, intermediate} -/
theorem cumulative_round1 :
    genCumulative counterexample_system {.primordial} 1 = 
    {.primordial, .intermediate} := by
  unfold genCumulative
  simp [counterexample_gen]
  ext x
  constructor
  · intro h
    cases x with
    | primordial => left; rfl
    | intermediate => right; rfl
    | target => 
        -- target is not in round 1
        simp at h
        cases h with
        | inl hp => cases hp
        | inr hg => 
            obtain ⟨y, hy, hgen⟩ := hg
            simp at hy
            cases hy with
            | inl hp => 
                rw [hp] at hgen
                simp [counterexample_gen] at hgen
                cases hgen
            | inr _ => cases hy
  · intro h
    cases h with
    | inl hp => 
        cases hp
        left; rfl
    | inr hi =>
        cases hi
        right
        use ThreeIdea.primordial
        constructor
        · left; rfl
        · simp [counterexample_gen]

/-- Round 2 (cumulative): {primordial, intermediate, target} -/
theorem cumulative_round2 :
    genCumulative counterexample_system {.primordial} 2 = 
    {.primordial, .intermediate, .target} := by
  unfold genCumulative
  ext x
  constructor
  · intro h
    simp only [Set.mem_union] at h
    cases h with
    | inl h_prev =>
      -- x is in genCumulative 1
      rw [cumulative_round1] at h_prev
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h_prev
      cases h_prev with
      | inl hp => simp [hp]
      | inr hi => simp [hi]
    | inr h_new =>
      -- x is in genStep (genCumulative 1)
      simp only [genStep, Set.mem_union, Set.mem_iUnion] at h_new
      cases h_new with
      | inl h_prev2 =>
        rw [cumulative_round1] at h_prev2
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h_prev2
        cases h_prev2 with
        | inl hp => simp [hp]
        | inr hi => simp [hi]
      | inr h_gen =>
        obtain ⟨a, ha, hx_gen⟩ := h_gen
        rw [cumulative_round1] at ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        cases ha with
        | inl hp => 
          subst hp
          simp only [counterexample_gen, Set.mem_singleton_iff] at hx_gen
          simp [hx_gen]
        | inr hi =>
          subst hi
          simp only [counterexample_gen, Set.mem_singleton_iff] at hx_gen
          simp [hx_gen]
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    cases h with
    | inl hp => 
      left; rw [cumulative_round1]; simp [hp]
    | inr rest =>
      cases rest with
      | inl hi =>
        left; rw [cumulative_round1]; simp [hi]
      | inr ht =>
        right
        simp only [genStep, Set.mem_union, Set.mem_iUnion]
        right
        use ThreeIdea.intermediate
        constructor
        · rw [cumulative_round1]; simp
        · simp [counterexample_gen, ht]

/-- Cumulative depth of target is 2 -/
theorem cumulative_depth_2 :
    depth counterexample_system {.primordial} .target = 2 := by
  unfold depth
  apply le_antisymm
  · -- depth ≤ 2: target is in genCumulative at round 2
    apply Nat.sInf_le
    simp
    rw [cumulative_round2]
    simp
  · -- depth ≥ 2: target not in earlier rounds
    apply Nat.le_of_pred_lt
    simp
    intro h1
    -- target not in genCumulative 1
    rw [cumulative_round1] at h1
    simp at h1

/-! ## Section 3: Non-Cumulative Analysis -/

/-- Non-cumulative round 1: {intermediate} (no primordial carried over) -/
theorem nonCumulative_round1 :
    genNonCumulative counterexample_system {.primordial} 1 = 
    {.intermediate} := by
  unfold genNonCumulative
  ext x
  constructor
  · intro h
    obtain ⟨y, hy, hgen⟩ := h
    simp only [Set.mem_singleton_iff] at hy
    subst hy
    simp only [counterexample_gen, Set.mem_singleton_iff] at hgen
    simp [hgen]
  · intro h
    simp only [Set.mem_singleton_iff] at h
    subst h
    use ThreeIdea.primordial
    constructor
    · simp
    · simp [counterexample_gen]

/-- Non-cumulative round 2: {target} 
    We apply generators to round 1 output = {intermediate}
    gen(intermediate) = {target} -/
theorem nonCumulative_round2 :
    genNonCumulative counterexample_system {.primordial} 2 = 
    {.target} := by
  unfold genNonCumulative
  ext x
  constructor
  · intro h
    obtain ⟨y, hy, hgen⟩ := h
    rw [nonCumulative_round1] at hy
    simp only [Set.mem_singleton_iff] at hy
    subst hy
    simp only [counterexample_gen, Set.mem_singleton_iff] at hgen
    simp [hgen]
  · intro h
    simp only [Set.mem_singleton_iff] at h
    subst h
    use ThreeIdea.intermediate
    constructor
    · rw [nonCumulative_round1]; simp
    · simp [counterexample_gen]

/-- Non-cumulative round 3: ∅
    We apply generators to round 2 output = {target}
    gen(target) = ∅ -/
theorem nonCumulative_round3 :
    genNonCumulative counterexample_system {.primordial} 3 = ∅ := by
  unfold genNonCumulative
  ext x
  constructor
  · intro h
    obtain ⟨y, hy, hgen⟩ := h
    rw [nonCumulative_round2] at hy
    simp at hy
    cases hy
    simp [counterexample_gen] at hgen
    exact hgen
  · intro h
    cases h

/-- Target IS reachable in non-cumulative model (at round 2) -/
theorem target_reachable_noncumulative :
    ∃ n, ThreeIdea.target ∈ 
      genNonCumulative counterexample_system {.primordial} n := by
  use 2
  rw [nonCumulative_round2]
  simp

/-- Non-cumulative depth is ALSO 2 (not strictly harder in this case).
    
    CORRECTION: This construction doesn't actually work!
    The target IS reachable at round 2 non-cumulatively.
    
    We need a different construction... -/
theorem nonCumulative_depth_2 :
    depthNonCumulative counterexample_system {.primordial} .target = 2 := by
  unfold depthNonCumulative
  apply le_antisymm
  · -- Upper bound: depth ≤ 2
    apply Nat.sInf_le
    simp only [Set.mem_setOf_eq]
    rw [nonCumulative_round2]
    simp
  · -- Lower bound: depth ≥ 2 (target not in earlier rounds)
    apply Nat.le_of_pred_lt
    simp only [Nat.lt_succ_iff]
    intro n hn
    interval_cases n
    · -- n = 0: trivially not in genNonCumulative 0 = ∅
      unfold genNonCumulative
      simp only [Set.mem_iUnion, Set.mem_empty_iff_false, exists_false, not_false_eq_true]
    · -- n = 1: target not in {intermediate}
      rw [nonCumulative_round1]
      simp only [Set.mem_singleton_iff]
      intro h
      cases h

/-! ## Section 4: Better Construction Needed -/

/-- The above construction doesn't work. We need a system where:
    - Target requires TWO intermediate ideas: a AND b
    - a is generated at round 1
    - b is generated at round 1  
    - target = gen(a, b) generated at round 2
    
    But in non-cumulative: at round 2, we only have {a, b}, not both.
    
    Actually, the issue is that our generators are single-input.
    With single-input generators, non-cumulative might not be strictly worse!
    
    The axiom might be WRONG for single-input generators.
    OR we need multi-input generators to construct the counterexample. -/

-- TODO: Either construct a proper counterexample with multi-input generators,
-- or prove that the axiom is false for single-input generators!

end NonCumulativeOracle_Explicit
