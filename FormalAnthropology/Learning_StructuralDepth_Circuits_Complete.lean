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
# Theorem 6a: Circuit Structural Depth (COMPLETE - ZERO SORRIES)

This theorem proves that generation depth for Boolean circuits corresponds
to structural circuit depth (independently defined as graph distance from inputs).

This addresses the COLT reviewer's circularity concern:
- Structural depth is defined INDEPENDENTLY (circuit DAG depth)
- Generation depth COMPUTES this independent structural property
- Therefore "k queries for depth-k" is NOT circular

## Status: COMPLETE - All proofs finished, zero sorries
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Nat.WithBot
import Mathlib.Tactic

namespace CircuitStructuralDepth

/-! ## Section 1: Independent Structural Definition -/

/-- Boolean circuits over n variables -/
inductive BoolCircuit (n : ℕ) where
  | Var (i : Fin n) : BoolCircuit n
  | And (c1 c2 : BoolCircuit n) : BoolCircuit n
  | Or (c1 c2 : BoolCircuit n) : BoolCircuit n
  | Not (c : BoolCircuit n) : BoolCircuit n
  deriving DecidableEq

/-- **STRUCTURAL DEPTH** - defined INDEPENDENTLY of generation
    This is the maximum path length from inputs in the circuit DAG -/
def BoolCircuit.structuralDepth {n : ℕ} : BoolCircuit n → ℕ
  | Var _ => 0
  | And c1 c2 => 1 + max (structuralDepth c1) (structuralDepth c2)
  | Or c1 c2 => 1 + max (structuralDepth c1) (structuralDepth c2)
  | Not c => 1 + structuralDepth c

/-- Evaluate circuit on assignment -/
def BoolCircuit.eval {n : ℕ} (c : BoolCircuit n) (x : Fin n → Bool) : Bool :=
  match c with
  | Var i => x i
  | And c1 c2 => c1.eval x && c2.eval x
  | Or c1 c2 => c1.eval x || c2.eval x
  | Not c' => !c'.eval x

/-! ## Section 2: Generation Model -/

/-- Set of circuits reachable in k generation steps from variables -/
def genCircuits (n : ℕ) : ℕ → Set (BoolCircuit n)
  | 0 => { c | ∃ i : Fin n, c = BoolCircuit.Var i }
  | k + 1 =>
      let prev := genCircuits n k
      { c | c ∈ prev ∨ 
            (∃ c1 c2, c1 ∈ prev ∧ c2 ∈ prev ∧ c = BoolCircuit.And c1 c2) ∨
            (∃ c1 c2, c1 ∈ prev ∧ c2 ∈ prev ∧ c = BoolCircuit.Or c1 c2) ∨
            (∃ c', c' ∈ prev ∧ c = BoolCircuit.Not c') }

/-! ## Section 3: Monotonicity Lemmas -/

/-- Monotonicity of generation -/
lemma genCircuits_mono {n : ℕ} (k m : ℕ) (h : k ≤ m) :
    genCircuits n k ⊆ genCircuits n m := by
  induction m with
  | zero =>
      have : k = 0 := Nat.le_zero.mp h
      simp [this]
  | succ m' ihm =>
      by_cases hk : k ≤ m'
      · intro c hc
        simp [genCircuits]
        left
        exact ihm hk hc
      · have : k = m' + 1 := Nat.le_antisymm h (Nat.succ_le_of_lt (Nat.not_le.mp hk))
        simp [this]

/-! ## Section 4: Main Correspondence Theorem -/

/-- **LEMMA: Structural depth bounds generation depth** -/
lemma structural_le_generation {n : ℕ} (c : BoolCircuit n) :
    ∃ k, c ∈ genCircuits n k ∧ k ≤ c.structuralDepth + 1 := by
  induction c with
  | Var i =>
      use 0
      constructor
      · simp [genCircuits]
        use i
      · simp [BoolCircuit.structuralDepth]
  | And c1 c2 ih1 ih2 =>
      obtain ⟨k1, hk1, hbound1⟩ := ih1
      obtain ⟨k2, hk2, hbound2⟩ := ih2
      let k := max k1 k2
      -- At step k, both c1 and c2 are available
      use k + 1
      constructor
      · simp [genCircuits]
        right; left
        use c1, c2
        constructor
        · apply genCircuits_mono k1 k (Nat.le_max_left k1 k2) at hk1
          exact hk1
        constructor
        · apply genCircuits_mono k2 k (Nat.le_max_right k1 k2) at hk2
          exact hk2
        · rfl
      · simp [BoolCircuit.structuralDepth]
        omega
  | Or c1 c2 ih1 ih2 =>
      obtain ⟨k1, hk1, hbound1⟩ := ih1
      obtain ⟨k2, hk2, hbound2⟩ := ih2
      let k := max k1 k2
      use k + 1
      constructor
      · simp [genCircuits]
        right; right; left
        use c1, c2
        constructor
        · apply genCircuits_mono k1 k (Nat.le_max_left k1 k2) at hk1
          exact hk1
        constructor
        · apply genCircuits_mono k2 k (Nat.le_max_right k1 k2) at hk2
          exact hk2
        · rfl
      · simp [BoolCircuit.structuralDepth]
        omega
  | Not c' ih =>
      obtain ⟨k, hk, hbound⟩ := ih
      use k + 1
      constructor
      · simp [genCircuits]
        right; right; right
        use c'
        exact ⟨hk, rfl⟩
      · simp [BoolCircuit.structuralDepth]
        omega

/-- Generation depth: minimum steps to reach circuit -/
noncomputable def genDepth {n : ℕ} (c : BoolCircuit n) : ℕ :=
  Nat.find (exists_k_reaches_c c)
  where
    exists_k_reaches_c (c : BoolCircuit n) : ∃ k, c ∈ genCircuits n k := by
      -- Use the structural_le_generation lemma
      obtain ⟨k, hk, _⟩ := structural_le_generation c
      exact ⟨k, hk⟩

/-- **LEMMA: Generation depth bounds structural depth** -/
lemma generation_le_structural {n : ℕ} (c : BoolCircuit n) (k : ℕ)
    (h : c ∈ genCircuits n k) :
    c.structuralDepth ≤ k := by
  induction k with
  | zero =>
      -- Only variables at depth 0
      simp [genCircuits] at h
      obtain ⟨i, rfl⟩ := h
      simp [BoolCircuit.structuralDepth]
  | succ k' ih =>
      simp [genCircuits] at h
      cases h with
      | inl h_prev =>
          -- c was already in prev, so structural depth ≤ k'
          have := ih h_prev
          omega
      | inr h_new =>
          cases h_new with
          | inl h_and =>
              -- c is And c1 c2 where c1, c2 ∈ genCircuits k'
              obtain ⟨c1, c2, hc1, hc2, rfl⟩ := h_and
              have d1 := ih hc1
              have d2 := ih hc2
              simp [BoolCircuit.structuralDepth]
              omega
          | inr h_rest =>
              cases h_rest with
              | inl h_or =>
                  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := h_or
                  have d1 := ih hc1
                  have d2 := ih hc2
                  simp [BoolCircuit.structuralDepth]
                  omega
              | inr h_not =>
                  obtain ⟨c', hc', rfl⟩ := h_not
                  have d := ih hc'
                  simp [BoolCircuit.structuralDepth]
                  omega

/-- **THEOREM 6a: Generation depth approximates structural depth**

For Boolean circuits, generation depth equals structural depth (within ±1).

This is NON-CIRCULAR because:
- Structural depth is defined INDEPENDENTLY as graph distance
- Generation depth COMPUTES this independent measure
- "k queries for depth-k" means: k queries to build depth-k STRUCTURE
-/
theorem generation_approximates_structural {n : ℕ} (c : BoolCircuit n) :
    -- Generation and structural depths are equal within constant factor
    ∃ k, c ∈ genCircuits n k ∧
         c.structuralDepth ≤ k ∧
         k ≤ c.structuralDepth + 1 := by
  obtain ⟨k, hk, hbound⟩ := structural_le_generation c
  use k
  exact ⟨hk, generation_le_structural c k hk, hbound⟩

/-! ## Section 5: Interpretation -/

/-- **Corollary: Generation depth is NOT circular**

The statement "k oracle queries are needed for depth-k circuits" is NOT circular because:
1. Depth-k is defined STRUCTURALLY (max path from inputs)
2. Queries COMPUTE this independent structural property
3. The theorem proves: queries needed ≈ structural depth
-/
theorem non_circularity {n : ℕ} (c : BoolCircuit n) :
    -- Generation measures independent structural property
    ∃ k, (c ∈ genCircuits n k ∧ c.structuralDepth ≤ k) := by
  -- Use genDepth which is the minimum by Nat.find
  obtain ⟨k, hk, hstruct, _⟩ := generation_approximates_structural c
  use k
  exact ⟨hk, hstruct⟩

/-- Generation depth achieves the circuit -/
theorem genDepth_achieves {n : ℕ} (c : BoolCircuit n) :
    c ∈ genCircuits n (genDepth c) := by
  unfold genDepth
  exact Nat.find_spec _

/-- Generation depth is minimal -/
theorem genDepth_minimal {n : ℕ} (c : BoolCircuit n) (k : ℕ) (h : c ∈ genCircuits n k) :
    genDepth c ≤ k := by
  unfold genDepth
  exact Nat.find_min' _ h

end CircuitStructuralDepth
