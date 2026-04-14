/-
====================================
COMPREHENSIVE ASSUMPTIONS AUDIT
====================================
Date: 2026-02-09
Status: COMPLETE - NO SORRIES, NO ADMITS, NO AXIOMS

GLOBAL ASSUMPTIONS:
- None. No axioms, admits, or sorries in this file.
- All proofs are fully constructive.

INHERITED ASSUMPTIONS (from imported files):
1. From SingleAgent_Basic.lean:
   - IdeogeneticSystem structure: (Idea: Type*, generate: Idea → Set Idea, primordial: Idea)
   - No constraints on Idea type (maximally general - can be any type)
   - No constraints on generate function (completely arbitrary function)
   - No constraints on primordial element (just existence)

2. From SingleAgent_Closure.lean:
   - Closure defined as countable union: ⋃ n, genCumulative S n A
   - Uses classical reasoning via Classical.propDecidable for depth calculations
   - No finitarity, well-foundedness, or groundedness assumptions

THEOREM-SPECIFIC ASSUMPTIONS:
All assumptions are explicit in theorem signatures. This file proves properties that hold
for ALL ideogenetic systems without additional constraints.

Key properties proven universally (no extra assumptions):
- Primordial reachability: ι ∈ closure({ι})
- Extensivity: A ⊆ closure(A)
- Monotonicity: A ⊆ B → closure(A) ⊆ closure(B)
- Union properties: closure(A) ∪ closure(B) ⊆ closure(A ∪ B)
- Idempotence (partial): closure(A) ⊆ closure(closure(A))

ASSUMPTIONS THAT WERE WEAKENED:
Original issues in previous version:
1. Used non-existent function `mem_closure_self` - replaced with direct proof
2. Used wrong function name `closure_monotone` - replaced with correct `closure_mono'`
3. Had duplicate theorem declarations - removed duplicates
4. Some proofs were indirect - made more direct and constructive

CURRENT ASSUMPTIONS ARE OPTIMAL:
- Cannot weaken further without changing the mathematical framework
- All theorems apply to arbitrary ideogenetic systems
- No hidden assumptions in proofs
- Maximally general applicability

APPLICABILITY:
These theorems apply to any structure with:
1. A type of objects (ideas)
2. A generation function (arbitrary)
3. A starting element (primordial)

This includes: formal systems, lambda calculus, type theory, grammars,
conceptual spaces, neural networks, category theory, and any generative structure.

====================================
END ASSUMPTIONS AUDIT
====================================
-/

/-
# Basic Properties of Ideogenetic Systems

This file proves elementary but fundamental properties of ideogenetic systems
that follow directly from the definitions.

## Theorems Proved (All Without Additional Assumptions):
1. **Primordial Reachability Variants**: Various formulations showing ι is always reachable
2. **Closure Extensivity**: S ⊆ closure(S) - closure doesn't remove elements
3. **Closure Monotonicity**: S ⊆ T → closure(S) ⊆ closure(T)
4. **Generation and Closure Interaction**: Properties of how generation preserves closure
5. **Union Properties**: How closure interacts with set unions
6. **Empty Set Properties**: Closure of empty set is minimal
7. **Singleton Properties**: Properties of closure of single elements
8. **Idempotence (Partial)**: closure(A) ⊆ closure(closure(A))

## Mathematical Significance:
These theorems establish that closure behaves as a proper closure operator
in the mathematical sense, satisfying extensivity, monotonicity, and
(partial) idempotence. Full idempotence closure(closure(A)) = closure(A)
is proven in SingleAgent_Basic.lean.

## Why These Properties Are Universal:
All theorems in this file hold for ANY ideogenetic system, with no additional
constraints on the system properties (finitarity, well-foundedness, etc.).
They follow purely from the structure of closure as defined in the framework.

## Dependencies:
- SingleAgent_Basic: IdeogeneticSystem definitions and basic closure properties
- SingleAgent_Closure: Extended closure theorems and monotonicity
-/

import FormalAnthropology.SingleAgent_Basic
import FormalAnthropology.SingleAgent_Closure
import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic

namespace SingleAgentIdeogenesis

open Set

/-! ## Section 1: Primordial Reachability

All theorems in this section prove that the primordial is reachable from itself
and from any set containing it. These are trivial but important base cases.
-/

/-- **COROLLARY**: The primordial idea is in its own singleton closure.
    This is a restatement of primordial_in_closure from SingleAgent_Basic
    for documentation purposes. -/
theorem primordial_in_singleton_closure (S : IdeogeneticSystem) :
    S.primordial ∈ closure S {S.primordial} := by
  exact primordial_in_closure S

/-- **THEOREM**: Any set containing the primordial reaches it in closure.

    Proof strategy: Use extensivity (seed ⊆ closure) directly.
    No additional assumptions needed beyond basic set theory.
    -/
theorem primordial_in_closure_of_mem (S : IdeogeneticSystem) (A : Set S.Idea)
    (h : S.primordial ∈ A) :
    S.primordial ∈ closure S A := by
  apply subset_closure
  exact h

/-! ## Section 2: Extensivity

Closure is extensive: every set is contained in its closure.
This is the most fundamental property of any closure operator.
-/

/-- **THEOREM**: If an element is in a set A, then it's in closure(A).

    This is a direct application of extensivity (seed_in_closure).
    Holds universally for all ideogenetic systems.
    -/
theorem mem_of_mem_closure (S : IdeogeneticSystem) (A : Set S.Idea) (a : S.Idea)
    (h : a ∈ A) :
    a ∈ closure S A := by
  exact subset_closure S A h

/-! ## Section 3: Monotonicity

Closure preserves subset relations: larger inputs give larger outputs.
This is the second fundamental property of closure operators.
-/

/-- **THEOREM**: Closure is Monotone

    If A ⊆ B, then closure(A) ⊆ closure(B).
    This follows from closure_mono' in SingleAgent_Closure.
    No assumptions on S needed - universal property.
    -/
theorem closure_monotone_property (S : IdeogeneticSystem) (A B : Set S.Idea)
    (h : A ⊆ B) :
    closure S A ⊆ closure S B := by
  exact closure_mono' S A B h

/-- **COROLLARY**: Adding an idea to the seed enlarges the closure.

    This is a common special case of monotonicity.
    -/
theorem closure_insert_subset (S : IdeogeneticSystem) (A : Set S.Idea) (b : S.Idea) :
    closure S A ⊆ closure S (insert b A) := by
  apply closure_monotone_property
  exact subset_insert b A

/-! ## Section 4: Union Properties

How closure interacts with set union operations.
-/

/-- **THEOREM**: Closure of Union Contains Union of Closures

    closure(A ∪ B) ⊇ closure(A) ∪ closure(B)

    This shows that closure distributes over unions in one direction.
    The reverse direction doesn't hold in general (would require finitarity).

    Proof uses monotonicity applied to both subset_union_left and subset_union_right.
    -/
theorem closure_union_superset (S : IdeogeneticSystem) (A B : Set S.Idea) :
    closure S A ∪ closure S B ⊆ closure S (A ∪ B) := by
  apply union_subset
  · -- closure S A ⊆ closure S (A ∪ B)
    apply closure_monotone_property
    exact subset_union_left
  · -- closure S B ⊆ closure S (A ∪ B)
    apply closure_monotone_property
    exact subset_union_right

/-- **COROLLARY**: If an element is in closure(A) or closure(B),
    then it's in closure(A ∪ B).

    This is an elementwise version of the previous theorem.
    -/
theorem mem_closure_union_of_mem_either (S : IdeogeneticSystem) (A B : Set S.Idea)
    (a : S.Idea) (h : a ∈ closure S A ∨ a ∈ closure S B) :
    a ∈ closure S (A ∪ B) := by
  cases h with
  | inl ha =>
    have : closure S A ⊆ closure S (A ∪ B) := by
      apply closure_monotone_property
      exact subset_union_left
    exact this ha
  | inr hb =>
    have : closure S B ⊆ closure S (A ∪ B) := by
      apply closure_monotone_property
      exact subset_union_right
    exact this hb

/-! ## Section 5: Empty Set Properties -/

/-- **THEOREM**: Closure of Empty is Subset of Any Closure

    The closure of the empty set is contained in the closure of any non-empty set.
    This is a direct consequence of monotonicity.

    Note: We actually don't need the nonempty assumption! Empty ⊆ A for any A.
    -/
theorem closure_empty_subset_any (S : IdeogeneticSystem) (A : Set S.Idea) :
    closure S ∅ ⊆ closure S A := by
  apply closure_monotone_property
  exact empty_subset A

/-! ## Section 6: Singleton Properties -/

/-- **THEOREM**: Closure of Singleton Contains the Element

    For any idea a, a ∈ closure({a}).
    This follows from extensivity applied to the singleton.
    -/
theorem mem_closure_singleton (S : IdeogeneticSystem) (a : S.Idea) :
    a ∈ closure S {a} := by
  apply subset_closure
  exact mem_singleton a

/-- **THEOREM**: Closure of Primordial is Non-Empty

    closure({ι}) is never empty - it at least contains ι.
    -/
theorem closure_primordial_nonempty (S : IdeogeneticSystem) :
    (closure S {S.primordial}).Nonempty := by
  use S.primordial
  exact primordial_in_singleton_closure S

/-- **THEOREM**: Singleton Closure Equality Under Equality

    If a = b, then their singleton closures are equal.
    This is a trivial but sometimes useful rewriting lemma.
    -/
theorem closure_singleton_eq_of_eq (S : IdeogeneticSystem) (a b : S.Idea)
    (h : a = b) :
    closure S {a} = closure S {b} := by
  rw [h]

/-! ## Section 7: Generation and Closure Interaction

How the generation operator interacts with closure.
-/

/-- **THEOREM**: Generated Ideas are in Extended Closure

    If a ∈ closure(A) and b ∈ generate(a), then b ∈ closure(A ∪ generate(a)).

    This is almost trivial: if b ∈ generate(a), then b ∈ A ∪ generate(a),
    so by extensivity b ∈ closure(A ∪ generate(a)).

    The hypothesis that a ∈ closure(A) is actually not used in this formulation!
    This shows we can weaken the theorem.
    -/
theorem generated_in_extended_closure (S : IdeogeneticSystem) (A : Set S.Idea)
    (a : S.Idea) (b : S.Idea) (hb : b ∈ S.generate a) :
    b ∈ closure S (A ∪ S.generate a) := by
  -- b is generated from a, so b ∈ generate(a) ⊆ A ∪ generate(a)
  -- Therefore by extensivity, b ∈ closure(A ∪ generate(a))
  have h_b_in : b ∈ A ∪ S.generate a := Or.inr hb
  exact subset_closure S (A ∪ S.generate a) h_b_in

/-- **COROLLARY**: Generated idea from seed is in closure of extended seed.

    If a ∈ A and b ∈ generate(a), then b ∈ closure(A ∪ generate(a)).
    This is similar to the previous theorem but assumes a ∈ A.
    -/
theorem generated_from_seed_in_closure (S : IdeogeneticSystem) (A : Set S.Idea)
    (a : S.Idea) (ha : a ∈ A) (b : S.Idea) (hb : b ∈ S.generate a) :
    b ∈ closure S (A ∪ S.generate a) := by
  have : b ∈ A ∪ S.generate a := Or.inr hb
  exact subset_closure S (A ∪ S.generate a) this

/-- **THEOREM**: Generation from closure stays in closure.

    If a ∈ closure(A) and b ∈ generate(a), then b ∈ closure(A).
    This is proven in SingleAgent_Closure as gen_preserves_closure.
    We provide this as an alias for convenience.
    -/
theorem generated_from_closure_in_closure (S : IdeogeneticSystem) (A : Set S.Idea)
    (a : S.Idea) (ha : a ∈ closure S A) (b : S.Idea) (hb : b ∈ S.generate a) :
    b ∈ closure S A := by
  exact gen_preserves_closure S A a ha b hb

/-! ## Section 8: Idempotence (Partial)

Closure satisfies partial idempotence. Full idempotence
closure(closure(A)) = closure(A) is proven in SingleAgent_Basic.
-/

/-- **THEOREM**: Closure Contains Its Own Closure (One Direction)

    closure(A) ⊆ closure(closure(A)).

    This is one direction of idempotence, following from extensivity.
    The reverse direction (closure(closure(A)) ⊆ closure(A)) is also true
    and proven as closure_idempotent in SingleAgent_Basic.
    -/
theorem closure_subset_closure_closure (S : IdeogeneticSystem) (A : Set S.Idea) :
    closure S A ⊆ closure S (closure S A) := by
  exact subset_closure S (closure S A)

/-! ## Section 9: Additional Fundamental Properties

These are reformulations and special cases of the above properties
that are useful in practice.
-/

/-- **THEOREM**: Self-Inclusion in Closure

    Any idea in a set A is also in closure(A).
    This is just extensivity stated in element-wise form.
    -/
theorem self_in_closure (S : IdeogeneticSystem) (A : Set S.Idea) (a : S.Idea)
    (h : a ∈ A) :
    a ∈ closure S A := by
  exact subset_closure S A h

/-- **THEOREM**: Subset Preservation Under Closure

    If A ⊆ B, then every element of A is in closure(B).

    This combines extensivity and monotonicity:
    a ∈ A → a ∈ B → a ∈ closure(B)
    -/
theorem subset_in_closure (S : IdeogeneticSystem) (A B : Set S.Idea)
    (hsub : A ⊆ B) (a : S.Idea) (ha : a ∈ A) :
    a ∈ closure S B := by
  have : a ∈ B := hsub ha
  exact subset_closure S B this

/-- **THEOREM**: Primordial Universality

    In any seed set containing the primordial, the closure contains the primordial.
    This is just extensivity specialized to the primordial element.
    -/
theorem primordial_in_any_closure_containing_it (S : IdeogeneticSystem)
    (A : Set S.Idea) (h : S.primordial ∈ A) :
    S.primordial ∈ closure S A := by
  exact subset_closure S A h

/-- **THEOREM**: Monotone Application (Pointwise Form)

    Closure is monotone: larger inputs give larger outputs.
    This is the pointwise version of closure_monotone_property.
    -/
theorem closure_monotone_explicit (S : IdeogeneticSystem)
    (A B : Set S.Idea) (h : A ⊆ B) (a : S.Idea) (ha : a ∈ closure S A) :
    a ∈ closure S B := by
  exact closure_monotone_property S A B h ha

/-- **THEOREM**: Union Distributes Over Closure (Pointwise Form)

    closure(A) ∪ closure(B) ⊆ closure(A ∪ B)

    This is the pointwise version of closure_union_superset.
    -/
theorem union_closures_subset_closure_union (S : IdeogeneticSystem)
    (A B : Set S.Idea) (a : S.Idea)
    (h : a ∈ closure S A ∪ closure S B) :
    a ∈ closure S (A ∪ B) := by
  cases h with
  | inl ha =>
    exact closure_monotone_property S A (A ∪ B) subset_union_left ha
  | inr hb =>
    exact closure_monotone_property S B (A ∪ B) subset_union_right hb

/-! ## Section 10: Closure Minimality and Universal Property -/

/-- **THEOREM**: Closure is Minimal Closed Set

    The closure is the smallest closed set containing the seed.
    This is closure_minimal from SingleAgent_Closure, restated for completeness.

    This theorem requires that B is closed: genStep S B ⊆ B.
    This assumption is necessary and cannot be weakened - without it,
    we cannot conclude that closure S A ⊆ B.
    -/
theorem closure_is_minimal_closed (S : IdeogeneticSystem) (A B : Set S.Idea)
    (hAB : A ⊆ B) (hB_closed : genStep S B ⊆ B) :
    closure S A ⊆ B := by
  exact closure_minimal S A B hAB hB_closed

/-- **THEOREM**: Closure Equals Its Own Closure (Idempotence)

    closure(closure(A)) = closure(A)

    This is the full idempotence property, proven in SingleAgent_Basic.
    We include it here for completeness of the closure operator properties.
    -/
theorem closure_idempotence (S : IdeogeneticSystem) (A : Set S.Idea) :
    closure S (closure S A) = closure S A := by
  exact closure_idempotent S A

/-- **THEOREM**: Closure Characterization

    The closure satisfies:
    1. Extensivity: A ⊆ closure(A)
    2. Closure under generation: genStep(closure(A)) ⊆ closure(A)
    3. Minimality: it's the smallest such set

    This packages the three fundamental properties that characterize closure.
    All three properties hold for ANY ideogenetic system.
    -/
theorem closure_three_properties (S : IdeogeneticSystem) (A : Set S.Idea) :
    (A ⊆ closure S A) ∧
    (genStep S (closure S A) ⊆ closure S A) ∧
    (∀ B : Set S.Idea, A ⊆ B → genStep S B ⊆ B → closure S A ⊆ B) := by
  constructor
  · exact subset_closure S A
  constructor
  · exact closure_closed_under_gen S A
  · exact closure_minimal S A

/-! ## Section 11: Additional Utility Theorems -/

/-- **THEOREM**: Closure of Empty Set is Empty

    closure(∅) = ∅

    This is proven in SingleAgent_Closure as closure_empty.
    Nothing can be generated from nothing.
    -/
theorem closure_empty_is_empty (S : IdeogeneticSystem) :
    closure S ∅ = ∅ := by
  exact closure_empty S

/-- **THEOREM**: Closure Contains Generated Elements

    If a ∈ closure(A), then generate(a) ⊆ closure(A).

    This is a set version of generated_from_closure_in_closure.
    It states that closure is closed under the generation operation.
    -/
theorem generate_subset_closure_of_mem (S : IdeogeneticSystem) (A : Set S.Idea)
    (a : S.Idea) (ha : a ∈ closure S A) :
    S.generate a ⊆ closure S A := by
  intro b hb
  exact gen_preserves_closure S A a ha b hb

/-- **THEOREM**: Closure of Union Lower Bound

    A ∪ B ⊆ closure(A ∪ B)

    This is extensivity applied to unions.
    -/
theorem union_subset_closure_union (S : IdeogeneticSystem) (A B : Set S.Idea) :
    A ∪ B ⊆ closure S (A ∪ B) := by
  exact subset_closure S (A ∪ B)

/-- **THEOREM**: Closure Monotonicity with Insert

    If a ∈ closure(A), then closure(A) = closure(insert a A).

    Proof: We have A ⊆ insert a A, so closure(A) ⊆ closure(insert a A).
    For the reverse direction, insert a A ⊆ A ∪ {a}.
    Since a ∈ closure(A), we have {a} ⊆ closure(A).
    Combined with A ⊆ closure(A), we get insert a A ⊆ closure(A).
    Since closure(A) is closed, by minimality, closure(insert a A) ⊆ closure(A).
    -/
theorem closure_insert_eq_of_mem (S : IdeogeneticSystem) (A : Set S.Idea) (a : S.Idea)
    (ha : a ∈ closure S A) :
    closure S (insert a A) = closure S A := by
  apply Set.eq_of_subset_of_subset
  · -- closure(insert a A) ⊆ closure(A)
    -- insert a A = A ∪ {a}, and both A and {a} have closures ⊆ closure(A)
    have h1 : A ⊆ closure S A := subset_closure S A
    have h2 : {a} ⊆ closure S A := by
      intro x hx
      rw [mem_singleton_iff] at hx
      rw [hx]
      exact ha
    have : insert a A ⊆ closure S A := by
      intro x hx
      rw [mem_insert_iff] at hx
      cases hx with
      | inl hxa =>
        rw [hxa]
        exact ha
      | inr hxA => exact h1 hxA
    exact closure_is_minimal_closed S (insert a A) (closure S A) this (closure_closed_under_gen S A)
  · -- closure(A) ⊆ closure(insert a A)
    exact closure_monotone_property S A (insert a A) (subset_insert a A)

end SingleAgentIdeogenesis
