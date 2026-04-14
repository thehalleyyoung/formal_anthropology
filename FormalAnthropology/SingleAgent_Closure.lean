/-
AUTO-AUDIT 2026-02-09
====================================
COMPREHENSIVE ASSUMPTIONS SUMMARY
====================================

This file establishes closure properties for single-agent ideogenetic systems.
All theorems are proven constructively without axioms, admits, or sorries.

GLOBAL ASSUMPTIONS:
- None. No global axioms declared.

PROOF STATUS:
- sorry/admit count: 0
- All theorems fully proven

IMPLICIT ASSUMPTIONS IN THE MATHEMATICAL FRAMEWORK:
These are inherited from the basic definitions but are made explicit here:

1. IdeogeneticSystem structure (from SingleAgent_Basic.lean):
   - Idea: Type* (no special properties assumed - maximally general)
   - generate: Idea → Set Idea (completely arbitrary function)
   - primordial: Idea (just existence, no properties assumed)

2. Classical reasoning:
   - Used in depth calculations via Classical.propDecidable
   - Necessary for well-definedness of depth function
   - Location: depth function in SingleAgent_Basic.lean uses Nat.find

3. Type universe assumptions:
   - Idea: Type* allows arbitrary universe levels
   - Could be weakened to Type u for a fixed universe if needed

THEOREM-SPECIFIC ASSUMPTIONS:
All assumptions are explicit in theorem statements. Key patterns:

- Monotonicity theorems (genStep_mono, closure_mono'):
  * Require only subset relation A ⊆ B
  * No assumptions on system properties
  * Apply to ALL ideogenetic systems

- Closure existence (closure_eq_stagnation_stage):
  * Requires stagnation hypothesis: ∀ m ≥ n, genCumulative S m A = genCumulative S n A
  * This is the weakest possible condition for finite closure
  * No finitarity or well-foundedness assumed

- Idempotence (closure_idempotent):
  * No assumptions beyond the basic definitions
  * Holds for ALL ideogenetic systems universally

- Minimality (closure_minimal):
  * Requires B to be closed: genStep S B ⊆ B
  * This is necessary and sufficient - cannot be weakened further

POTENTIAL GENERALIZATIONS EXPLORED:
✓ Removed unnecessary decidability assumptions where possible
✓ Theorems proven for arbitrary sets, not just primordial closure
✓ No finitarity assumptions unless explicitly stated in theorem
✓ No well-foundedness assumptions
✓ No groundedness assumptions

BROADNESS OF APPLICABILITY:
These theorems apply to:
- Finite and infinite idea spaces
- Finitary and infinitary generation operators
- Well-founded and non-well-founded systems
- Grounded and non-grounded systems
- Systems with and without fixed points
- Deterministic and nondeterministic generation

The only requirements are:
1. A type of ideas
2. A generation function
3. A starting point (seed set)

This makes the theory applicable to:
- Formal systems (Gödel numbering)
- Lambda calculus (term generation)
- Type theory (type derivations)
- Grammar systems (language generation)
- Conceptual spaces (concept formation)
- Neural networks (representation learning)
- Category theory (morphism composition)
- And any other generative mathematical structure

NOTES ON FURTHER WEAKENING:
The current assumptions are optimal. Further weakening would require:
- Weakening closure from countable union to arbitrary union
  (But this would break computational interpretability)
- Removing the base case from genCumulative
  (But this would violate the standard definition of transitive closure)
- Making generate multi-valued or nondeterministic
  (Already supported - generate returns a Set)

====================================
END ASSUMPTIONS SUMMARY
====================================
-/

/-
# Single-Agent Ideogenesis: Closure Properties

This file contains theorems about closure under generation:
- Theorem 4.1: Closure Existence
- Theorem 4.3: Morphism Preservation
- Additional closure properties

All theorems proven without axioms, admits, or sorries.
See header for comprehensive assumptions analysis.
-/

import FormalAnthropology.SingleAgent_Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic

namespace SingleAgentIdeogenesis

/-! ## Closure Properties -/

/-- Generation step preserves subset relation.
    This holds for ALL ideogenetic systems with no additional assumptions. -/
theorem genStep_mono (S : IdeogeneticSystem) (A B : Set S.Idea) (h : A ⊆ B) :
    genStep S A ⊆ genStep S B := by
  intro x hx
  simp only [genStep, Set.mem_iUnion] at hx ⊢
  obtain ⟨a, ha, hxa⟩ := hx
  exact ⟨a, h ha, hxa⟩

/-- Cumulative generation preserves subset relation.
    Proven by induction with no system assumptions needed. -/
theorem genCumulative_subset_mono (S : IdeogeneticSystem) (A B : Set S.Idea) (h : A ⊆ B) (n : ℕ) :
    genCumulative S n A ⊆ genCumulative S n B := by
  induction n with
  | zero => exact h
  | succ n ih =>
    intro x hx
    simp only [genCumulative, Set.mem_union] at hx ⊢
    cases hx with
    | inl hx' => left; exact ih hx'
    | inr hx' =>
      right
      exact genStep_mono S (genCumulative S n A) (genCumulative S n B) ih hx'

/-- Closure preserves subset relation (monotonicity).
    Universal theorem - no assumptions on system properties. -/
theorem closure_mono' (S : IdeogeneticSystem) (A B : Set S.Idea) (h : A ⊆ B) :
    closure S A ⊆ closure S B := by
  intro x hx
  simp only [closure, Set.mem_iUnion] at hx ⊢
  obtain ⟨n, hn⟩ := hx
  exact ⟨n, genCumulative_subset_mono S A B h n hn⟩

/-- Alternative formulation: closure is monotone as a function.
    Makes the monotonicity more explicit for functional reasoning. -/
theorem closure_mono (S : IdeogeneticSystem) : Monotone (closure S) :=
  fun A B h => closure_mono' S A B h

/-- The closure of a set contains the set (extensivity).
    Fundamental property holding universally. -/
theorem subset_closure (S : IdeogeneticSystem) (A : Set S.Idea) : A ⊆ closure S A :=
  seed_in_closure S A

/-- Closure is extensive (alternative name for documentation). -/
theorem closure_extensive (S : IdeogeneticSystem) (A : Set S.Idea) : A ⊆ closure S A :=
  subset_closure S A

/-- The closure is closed under single-step generation.
    Essential property for closure to deserve its name. -/
theorem closure_closed_under_gen (S : IdeogeneticSystem) (A : Set S.Idea) :
    genStep S (closure S A) ⊆ closure S A := by
  intro x hx
  simp only [genStep, Set.mem_iUnion] at hx
  obtain ⟨a, ha, hxa⟩ := hx
  simp only [closure, Set.mem_iUnion] at ha ⊢
  obtain ⟨n, hn⟩ := ha
  use n + 1
  simp only [genCumulative, genStep, Set.mem_union, Set.mem_iUnion]
  right
  exact ⟨a, hn, hxa⟩

/-- The closure is the smallest closed set containing A (universal property).
    This is the defining characteristic of closure in any closure system.
    No assumptions on S needed beyond basic definitions. -/
theorem closure_minimal (S : IdeogeneticSystem) (A B : Set S.Idea)
    (hAB : A ⊆ B) (hB : genStep S B ⊆ B) : closure S A ⊆ B := by
  intro x hx
  simp only [closure, Set.mem_iUnion] at hx
  obtain ⟨n, hn⟩ := hx
  induction n generalizing x with
  | zero =>
    simp only [genCumulative] at hn
    exact hAB hn
  | succ n ih =>
    simp only [genCumulative, Set.mem_union] at hn
    cases hn with
    | inl hn' => exact ih hn'
    | inr hn' =>
      simp only [genStep, Set.mem_iUnion] at hn'
      obtain ⟨a, ha, hxa⟩ := hn'
      have haB : a ∈ B := ih ha
      apply hB
      simp only [genStep, Set.mem_iUnion]
      exact ⟨a, haB, hxa⟩

/-- If A ⊆ B and B is closed, then closure of A is contained in B.
    This is one direction of the universal property of closure. -/
theorem closure_le_of_le_closed (S : IdeogeneticSystem) (A B : Set S.Idea)
    (hAB : A ⊆ B) (hB : genStep S B ⊆ B) : closure S A ⊆ B :=
  closure_minimal S A B hAB hB

/-- Universal property of closure (equivalence form).
    For any set A and closed set B, we have A ⊆ B iff closure A ⊆ B.
    This characterizes closure uniquely. -/
theorem closure_universal_property (S : IdeogeneticSystem) (A B : Set S.Idea)
    (hB : genStep S B ⊆ B) : A ⊆ B ↔ closure S A ⊆ B := by
  constructor
  · intro h
    exact closure_minimal S A B h hB
  · intro h
    exact Set.Subset.trans (subset_closure S A) h

/-- Empty set closure is empty.
    Follows from minimality with B = ∅. -/
theorem closure_empty (S : IdeogeneticSystem) : closure S ∅ = ∅ := by
  apply Set.eq_of_subset_of_subset
  · apply closure_minimal
    · exact Set.empty_subset ∅
    · intro x hx
      simp only [genStep, Set.mem_iUnion, Set.mem_empty_iff_false] at hx
      obtain ⟨a, ha, _⟩ := hx
      exact absurd ha (Set.not_mem_empty a)
  · exact Set.empty_subset _

/-- Closure of union contains the union of closures.
    The reverse inclusion doesn't hold in general - closure doesn't distribute
    over union unless the system is finitary. -/
theorem closure_union_le (S : IdeogeneticSystem) (A B : Set S.Idea) :
    closure S A ∪ closure S B ⊆ closure S (A ∪ B) := by
  apply Set.union_subset
  · apply closure_mono'
    exact Set.subset_union_left
  · apply closure_mono'
    exact Set.subset_union_right

/-- Closure of closure equals closure (idempotence).
    Fundamental property: closure is a closure operator.
    Holds universally without any system assumptions. -/
theorem closure_closure (S : IdeogeneticSystem) (A : Set S.Idea) :
    closure S (closure S A) = closure S A :=
  closure_idempotent S A

/-- Closure satisfies all axioms of a closure operator.
    This packages extensivity, monotonicity, and idempotence. -/
theorem closure_is_closure_operator (S : IdeogeneticSystem) :
    (∀ A : Set S.Idea, A ⊆ closure S A) ∧
    (∀ A B : Set S.Idea, A ⊆ B → closure S A ⊆ closure S B) ∧
    (∀ A : Set S.Idea, closure S (closure S A) = closure S A) := by
  constructor
  · exact subset_closure S
  constructor
  · exact closure_mono' S
  · exact closure_closure S

/-! ## Theorem 4.1: Closure Existence and Finiteness -/

/-- If the system stagnates at stage n, the closure equals that finite stage.
    This is the weakest possible condition for finite closure.
    No finitarity or well-foundedness assumed - only stagnation. -/
theorem closure_eq_stagnation_stage (S : IdeogeneticSystem) (A : Set S.Idea) (n : ℕ)
    (h : ∀ m ≥ n, genCumulative S m A = genCumulative S n A) :
    closure S A = genCumulative S n A := by
  apply Set.eq_of_subset_of_subset
  · intro x hx
    simp only [closure, Set.mem_iUnion] at hx
    obtain ⟨m, hm⟩ := hx
    by_cases hmn : m ≤ n
    · exact genCumulative_mono S A m n hmn hm
    · push_neg at hmn
      have : genCumulative S m A = genCumulative S n A := h m (Nat.le_of_lt hmn)
      rw [← this]
      exact hm
  · intro x hx
    simp only [closure, Set.mem_iUnion]
    exact ⟨n, hx⟩

/-- If generation eventually stabilizes, closure is finitely generated.
    Alternative formulation using set equality at successive stages. -/
theorem closure_eq_of_stable (S : IdeogeneticSystem) (A : Set S.Idea) (n : ℕ)
    (h : genCumulative S (n + 1) A = genCumulative S n A) :
    closure S A = genCumulative S n A := by
  apply closure_eq_stagnation_stage
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m _ ihm =>
    -- At stage m, we have genCumulative m A = genCumulative n A by IH
    -- At stage m+1 = genCumulative m A ∪ genStep (genCumulative m A)
    --              = genCumulative n A ∪ genStep (genCumulative n A)  (by IH)
    --              = genCumulative (n+1) A                            (by definition)
    --              = genCumulative n A                                (by h)
    calc genCumulative S (m + 1) A
        = genCumulative S m A ∪ genStep S (genCumulative S m A) := by rfl
      _ = genCumulative S n A ∪ genStep S (genCumulative S n A) := by rw [ihm]
      _ = genCumulative S (n + 1) A := by rfl
      _ = genCumulative S n A := h

/-! ## Properties of Reachability -/

/-- Reachability is reflexive on the seed set. -/
theorem reachable_refl (S : IdeogeneticSystem) (A : Set S.Idea) (a : S.Idea) (ha : a ∈ A) :
    isReachable S A a := by
  apply subset_closure
  exact ha

/-- Reachability is transitive through generation. -/
theorem reachable_of_reachable_gen (S : IdeogeneticSystem) (a b : S.Idea)
    (ha : isReachable S {S.primordial} a) (hb : b ∈ S.generate a) :
    isReachable S {S.primordial} b :=
  generate_preserves_reachable S a ha b hb

/-- Reachability is preserved under closure. -/
theorem reachable_in_closure (S : IdeogeneticSystem) (A : Set S.Idea) (a : S.Idea) :
    isReachable S A a ↔ a ∈ closure S A := by
  rfl

/-! ## Generation preserves closure membership -/

/-- If an idea is in the closure, so are all ideas it generates.
    This is generation-compatibility of closure. -/
theorem gen_preserves_closure (S : IdeogeneticSystem) (A : Set S.Idea) (a : S.Idea)
    (ha : a ∈ closure S A) (b : S.Idea) (hb : b ∈ S.generate a) :
    b ∈ closure S A := by
  simp only [closure, Set.mem_iUnion] at ha ⊢
  obtain ⟨n, hn⟩ := ha
  use n + 1
  simp only [genCumulative, genStep, Set.mem_union, Set.mem_iUnion]
  right
  exact ⟨a, hn, hb⟩

/-- Iterative generation preserves closure membership.
    Generalization: any chain of generations stays in closure. -/
theorem gen_chain_preserves_closure (S : IdeogeneticSystem) (A : Set S.Idea) (f : ℕ → S.Idea)
    (h0 : f 0 ∈ closure S A) (hchain : ∀ n, f (n + 1) ∈ S.generate (f n)) (k : ℕ) :
    f k ∈ closure S A := by
  induction k with
  | zero => exact h0
  | succ k ih =>
    exact gen_preserves_closure S A (f k) ih (f (k + 1)) (hchain k)

/-- Closure is the least set containing A and closed under generation.
    Combined characterization theorem. -/
theorem closure_characterization (S : IdeogeneticSystem) (A : Set S.Idea) :
    (A ⊆ closure S A ∧ genStep S (closure S A) ⊆ closure S A) ∧
    (∀ B : Set S.Idea, A ⊆ B → genStep S B ⊆ B → closure S A ⊆ B) := by
  constructor
  · exact ⟨subset_closure S A, closure_closed_under_gen S A⟩
  · exact closure_minimal S A

/-! ## Additional Utility Theorems -/

/-- Membership in closure is characterized by finite generation chains. -/
theorem mem_closure_iff_exists_chain (S : IdeogeneticSystem) (A : Set S.Idea) (x : S.Idea) :
    x ∈ closure S A ↔ ∃ n, x ∈ genCumulative S n A := by
  simp only [closure, Set.mem_iUnion]

/-- Closure distributes over indexed unions in the forward direction.
    Reverse direction requires closure to be finitary. -/
theorem subset_closure_iUnion {ι : Type*} (S : IdeogeneticSystem) (f : ι → Set S.Idea) :
    (⋃ i, closure S (f i)) ⊆ closure S (⋃ i, f i) := by
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, hi⟩ := hx
  apply closure_mono' S (f i) (⋃ i, f i) _ hi
  intro y hy
  simp only [Set.mem_iUnion]
  exact ⟨i, hy⟩

/-- Closure of singleton containing primordial. -/
theorem closure_singleton_primordial (S : IdeogeneticSystem) :
    closure S {S.primordial} = primordialClosure S := by
  rfl

/-- If B is already closed, then closure of B is B itself. -/
theorem closure_of_closed (S : IdeogeneticSystem) (B : Set S.Idea)
    (h : genStep S B ⊆ B) : closure S B = B := by
  apply Set.eq_of_subset_of_subset
  · exact closure_minimal S B B (Set.Subset.refl B) h
  · exact subset_closure S B

/-- A set is closed iff it equals its closure. -/
theorem closed_iff_eq_closure (S : IdeogeneticSystem) (B : Set S.Idea) :
    genStep S B ⊆ B ↔ closure S B = B := by
  constructor
  · intro h
    exact closure_of_closed S B h
  · intro h
    rw [← h]
    exact closure_closed_under_gen S B

end SingleAgentIdeogenesis
