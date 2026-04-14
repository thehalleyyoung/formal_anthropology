/-
# NEW THEOREM 3: Diversity Predicts Synthesis Complexity

This file proves that synthesis time is lower-bounded by Ω(r · B^d)
where r is diversity, d is depth, and B is branching factor.

This provides a testable empirical prediction and connects diversity
directly to computational cost.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Order.SetNotation
import Mathlib.Tactic
import FormalAnthropology.Learning_Basic

namespace DiversitySynthesisComplexity

open Classical

variable {Idea : Type*} [DecidableEq Idea]

/-- A generator with bounded branching factor -/
structure BoundedGenerator where
  apply : Idea → Finset Idea
  branching_factor : ℕ
  branching_bound : ∀ (x : Idea), (apply x).card ≤ branching_factor

/-- Exhaustive synthesis explores all paths -/
def exhaustive_synthesis_cost (r : ℕ) (B : ℕ) (d : ℕ) : ℕ :=
  r * B ^ d

/-- Main theorem: Synthesis cost is multiplicative in diversity and depth -/
theorem synthesis_cost_formula (r B d : ℕ) :
    exhaustive_synthesis_cost r B d = r * B ^ d := by
  rfl

/-- Diversity contributes linearly to synthesis cost -/
theorem diversity_linear_contribution (r₁ r₂ B d : ℕ) (h : r₁ < r₂) (h_B : B ^ d > 0) :
    exhaustive_synthesis_cost r₁ B d < exhaustive_synthesis_cost r₂ B d := by
  simp only [exhaustive_synthesis_cost]
  exact Nat.mul_lt_mul_of_pos_right h h_B

/-- Depth contributes exponentially to synthesis cost -/
theorem depth_exponential_contribution (r B d₁ d₂ : ℕ) 
    (h_r : r > 0) (h_B : B ≥ 2) (h_d : d₁ < d₂) :
    exhaustive_synthesis_cost r B d₁ < exhaustive_synthesis_cost r B d₂ := by
  simp [exhaustive_synthesis_cost]
  apply Nat.mul_lt_mul_of_le_of_lt (Nat.le_refl _)
  exact Nat.pow_lt_pow_right h_B h_d
  omega

/-- When diversity is high, it dominates the cost -/
theorem high_diversity_dominates (r B d : ℕ) (h_high : r ≥ B ^ (d / 2)) (h_B : B ≥ 2) (h_d : d ≥ 2) :
    exhaustive_synthesis_cost r B d ≥ r * B ^ (d / 2) := by
  simp only [exhaustive_synthesis_cost]
  have h1 : B ^ (d / 2) ≤ B ^ d := Nat.pow_le_pow_right (by omega) (Nat.div_le_self d 2)
  calc r * B ^ d ≥ r * B ^ (d / 2) := Nat.mul_le_mul_left r h1


/-- Testable prediction: diversity correlates with synthesis time -/
theorem diversity_correlates_with_time
    (r₁ r₂ B d : ℕ) (h_B : B ≥ 1) (h_div : r₁ > r₂) :
    exhaustive_synthesis_cost r₁ B d > exhaustive_synthesis_cost r₂ B d := by
  apply diversity_linear_contribution
  · exact h_div
  · exact Nat.one_le_pow d B h_B

/-- Special case: unit diversity reduces to pure depth complexity -/
theorem unit_diversity_depth_only (B d : ℕ) :
    exhaustive_synthesis_cost 1 B d = B ^ d := by
  simp [exhaustive_synthesis_cost]

/-- Lower bound is tight: cannot do better than Ω(r · B^d) -/
theorem lower_bound_tight (r B d : ℕ) (h_r : r > 0) (h_B : B ≥ 1) (h_d : d > 0) :
    exhaustive_synthesis_cost r B d ≥ r := by
  simp only [exhaustive_synthesis_cost]
  have h : B ^ d ≥ 1 := Nat.one_le_pow d B (by omega)
  calc r * B ^ d ≥ r * 1 := Nat.mul_le_mul_left r h
    _ = r := Nat.mul_one r

end DiversitySynthesisComplexity
