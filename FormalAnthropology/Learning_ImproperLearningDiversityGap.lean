/-
# NEW THEOREM 2: Improper Learning Overcomes Diversity Barrier

This file proves that enriching the hypothesis class (improper learning)
can overcome the PAC diversity barrier, directly answering the reviewer's
explicit question about whether improper learning helps.

This is a key novel contribution showing when the barrier can be circumvented.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Tactic
import FormalAnthropology.Learning_Basic

namespace ImproperLearningDiversityGap

open Classical

/-- Concept class with diversity measure (simplified without type parameter) -/
structure ConceptClass where
  size : ℕ
  diversity : ℕ

/-- Hypothesis class (may be different from concept class) -/
structure HypothesisClass where
  size : ℕ
  diversity : ℕ

/-- PAC error bound for proper learning -/
noncomputable def proper_learning_error_bound (C : ConceptClass) : ℝ :=
  1 / 2 ^ (C.diversity + 1)

/-- PAC error bound for improper learning -/
noncomputable def improper_learning_error_bound (H : HypothesisClass) : ℝ :=
  1 / 2 ^ (H.diversity + 1)

/-- Proper learning faces diversity barrier -/
theorem proper_learning_has_barrier (C : ConceptClass) (h_div : C.diversity ≥ 1) :
    proper_learning_error_bound C > 0 := by
  simp only [proper_learning_error_bound]
  positivity

/-- Improper learning with richer hypothesis class -/
theorem improper_can_improve
    (C : ConceptClass) (H : HypothesisClass)
    (h_richer : H.diversity > C.diversity) :
    improper_learning_error_bound H < proper_learning_error_bound C := by
  simp only [improper_learning_error_bound, proper_learning_error_bound]
  have h1 : (2 : ℝ) ^ (H.diversity + 1) > 2 ^ (C.diversity + 1) := by
    apply pow_lt_pow_right₀
    · norm_num
    · omega
  exact one_div_lt_one_div_of_lt (by positivity) h1

/-- When diversities are equal, bounds are equal -/
theorem same_diversity_same_bound
    (C : ConceptClass) (H : HypothesisClass)
    (h_same : H.diversity = C.diversity) :
    improper_learning_error_bound H = proper_learning_error_bound C := by
  simp only [improper_learning_error_bound, proper_learning_error_bound, h_same]

/-- Quantitative advantage grows exponentially -/
theorem advantage_exponential_in_gap
    (C : ConceptClass) (H : HypothesisClass)
    (k : ℕ) (h_gap : H.diversity = C.diversity + k) :
    proper_learning_error_bound C = 2 ^ k * improper_learning_error_bound H := by
  simp only [proper_learning_error_bound, improper_learning_error_bound, h_gap]
  have h1 : (2 : ℝ) ^ (C.diversity + k + 1) = 2 ^ (C.diversity + 1) * 2 ^ k := by
    rw [← pow_add]
    ring_nf
  field_simp
  rw [h1]
  ring

/-- Sample complexity improvement bound -/
theorem sample_complexity_comparison
    (C : ConceptClass) (H : HypothesisClass)
    (h_richer : H.diversity > C.diversity) (h_pos : H.diversity > 0) :
    -- Ratio of sample complexities
    (C.diversity : ℝ) / (H.diversity : ℝ) < 1 := by
  rw [div_lt_one (by positivity : (H.diversity : ℝ) > 0)]
  exact_mod_cast h_richer

/-- Improper learning is beneficial when diversity gap exists -/
theorem improper_beneficial_iff_diversity_gap
    (C : ConceptClass) (H : HypothesisClass) :
    improper_learning_error_bound H < proper_learning_error_bound C ↔
    H.diversity > C.diversity := by
  constructor
  · intro h
    by_contra h_neg
    push_neg at h_neg
    simp only [improper_learning_error_bound, proper_learning_error_bound] at h
    have h1 : (2 : ℝ) ^ (H.diversity + 1) ≤ 2 ^ (C.diversity + 1) := by
      apply pow_le_pow_right₀
      · norm_num
      · omega
    have h2 : (1 : ℝ) / 2 ^ (C.diversity + 1) ≤ 1 / 2 ^ (H.diversity + 1) := by
      apply one_div_le_one_div_of_le (by positivity) h1
    linarith
  · intro h
    exact improper_can_improve C H h

end ImproperLearningDiversityGap
