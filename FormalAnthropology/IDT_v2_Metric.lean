import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.IDT_Foundations_v2

/-!
# IDT v2: Metric and Geometric Structure

The real-valued resonance function induces a rich geometric structure.
d²(a,b) = rs(a,a) + rs(b,b) - 2·rs(a,b) gives an RKHS embedding.

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT2

section MetricStructure
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-! ## §1. Squared Distance — Core Properties -/

theorem sd_nonneg (a b : I) : squaredDistance a b ≥ 0 :=
  squaredDistance_nonneg a b

theorem sd_self_zero (a : I) : squaredDistance a a = 0 :=
  squaredDistance_self a

theorem sd_symm (a b : I) : squaredDistance a b = squaredDistance b a :=
  squaredDistance_symm a b

theorem sd_formula (a b : I) :
    squaredDistance a b =
    resonanceStrength a a + resonanceStrength b b - 2 * resonanceStrength a b := rfl

theorem sd_from_void (a : I) :
    squaredDistance (void : I) a =
    1 + resonanceStrength a a - 2 * resonanceStrength (void : I) a :=
  squaredDistance_void_left a

theorem sd_void_void : squaredDistance (void : I) (void : I) = 0 :=
  squaredDistance_self _

/-! ## §2. Resonance Similarity -/

/-- Resonance similarity: 2·rs(a,b) / (rs(a,a) + rs(b,b)) — analogous to cosine similarity -/
noncomputable def resonanceSimilarity (a b : I) : ℝ :=
  2 * resonanceStrength a b / (resonanceStrength a a + resonanceStrength b b)

theorem resonanceSimilarity_le_one (a b : I) :
    resonanceSimilarity a b ≤ 1 := by
  unfold resonanceSimilarity
  have ha := rs_self_pos' (I := I) a
  have hb := rs_self_pos' (I := I) b
  have hsum : resonanceStrength a a + resonanceStrength b b > 0 := by linarith
  rw [div_le_one hsum]
  nlinarith [sq_nonneg (resonanceStrength a a - resonanceStrength b b),
             sq_nonneg (resonanceStrength a b), IdeaticSpace2.rs_nonneg a b,
             IdeaticSpace2.rs_cauchy_schwarz a b]

theorem resonanceSimilarity_nonneg (a b : I) :
    resonanceSimilarity a b ≥ 0 := by
  unfold resonanceSimilarity
  have ha := rs_self_pos' (I := I) a
  have hb := rs_self_pos' (I := I) b
  exact div_nonneg (by linarith [IdeaticSpace2.rs_nonneg a b]) (by linarith)

theorem resonanceSimilarity_self (a : I) : resonanceSimilarity a a = 1 := by
  unfold resonanceSimilarity
  have ha := rs_self_pos' (I := I) a
  have hne : resonanceStrength a a + resonanceStrength a a ≠ 0 := by linarith
  field_simp; ring

theorem resonanceSimilarity_symm (a b : I) :
    resonanceSimilarity a b = resonanceSimilarity b a := by
  unfold resonanceSimilarity; rw [IdeaticSpace2.rs_symm a b, add_comm]

/-! ## §3. RKHS Structure -/

/-- RKHS norm squared = self-resonance -/
noncomputable def rkhs_norm_sq (a : I) : ℝ := resonanceStrength a a

theorem rkhs_norm_sq_ge_one (a : I) : rkhs_norm_sq a ≥ 1 := rs_self_ge_one a

theorem rkhs_norm_sq_pos (a : I) : rkhs_norm_sq a > 0 := rs_self_pos' a

/-- RKHS inner product = resonance strength -/
noncomputable def rkhs_inner (a b : I) : ℝ := resonanceStrength a b

theorem rkhs_inner_symm (a b : I) : rkhs_inner a b = rkhs_inner b a :=
  IdeaticSpace2.rs_symm a b

theorem rkhs_cauchy_schwarz (a b : I) :
    rkhs_inner a b * rkhs_inner a b ≤ rkhs_norm_sq a * rkhs_norm_sq b :=
  IdeaticSpace2.rs_cauchy_schwarz a b

/-- d²(a,b) = ‖a‖² + ‖b‖² - 2⟨a,b⟩ -/
theorem sd_from_inner (a b : I) :
    squaredDistance a b = rkhs_norm_sq a + rkhs_norm_sq b - 2 * rkhs_inner a b := rfl

/-! ## §4. Composition and Distance -/

theorem rs_shared_context_right (a b c : I) :
    resonanceStrength (compose a c) (compose b c) ≥ resonanceStrength a b :=
  IdeaticSpace2.rs_compose_right_mono a b c

theorem rs_shared_context_left (a b c : I) :
    resonanceStrength (compose c a) (compose c b) ≥ resonanceStrength a b :=
  IdeaticSpace2.rs_compose_left_mono a b c

theorem sd_void_compose_nonneg (a b : I) :
    squaredDistance (void : I) (compose a b) ≥ 0 :=
  squaredDistance_nonneg _ _

/-! ## §5. Cultural Distance -/

/-- Cultural distance: squared distance between ideas -/
noncomputable def culturalDistance (a b : I) : ℝ := squaredDistance a b

theorem culturalDistance_nonneg (a b : I) : culturalDistance a b ≥ 0 :=
  squaredDistance_nonneg a b

theorem culturalDistance_self (a : I) : culturalDistance a a = 0 :=
  squaredDistance_self a

theorem culturalDistance_symm (a b : I) :
    culturalDistance a b = culturalDistance b a :=
  squaredDistance_symm a b

/-- Adding shared context preserves or increases resonance -/
theorem shared_context_resonance_increase (a b c : I) :
    resonanceStrength (compose c a) (compose c b) ≥ resonanceStrength a b :=
  IdeaticSpace2.rs_compose_left_mono a b c

/-! ## §6. Norm Properties -/

theorem rs_mono_compose_right (a b : I) :
    rkhs_norm_sq (compose a b) ≥ rkhs_norm_sq a := rs_compose_self_right a b

theorem rs_mono_compose_left (a b : I) :
    rkhs_norm_sq (compose b a) ≥ rkhs_norm_sq a := rs_compose_self_left a b

theorem rkhs_norm_composeN_mono (a : I) (n : ℕ) :
    rkhs_norm_sq (composeN a (n + 1)) ≥ rkhs_norm_sq (composeN a n) :=
  rs_self_composeN_mono a n

theorem void_minimal_norm (a : I) : rkhs_norm_sq (void : I) ≤ rkhs_norm_sq a := by
  unfold rkhs_norm_sq; rw [IdeaticSpace2.rs_void_self]; exact rs_self_ge_one a

/-! ## §7. Depth-Distance Interaction -/

theorem deeper_composition_higher_norm (a b : I) :
    rkhs_norm_sq (compose a b) ≥ rkhs_norm_sq a := rs_compose_self_right a b

theorem atomic_norm_ge_one (a : I) (_ : atomic a) :
    rkhs_norm_sq a ≥ 1 := rs_self_ge_one a

theorem void_norm_eq_one : rkhs_norm_sq (void : I) = 1 := by
  unfold rkhs_norm_sq; exact IdeaticSpace2.rs_void_self

/-! ## §8. Normalized Distance -/

/-- Normalized squared distance: scales by sum of norms -/
noncomputable def normalizedSqDist (a b : I) : ℝ :=
  squaredDistance a b / (rkhs_norm_sq a + rkhs_norm_sq b)

theorem normalizedSqDist_nonneg (a b : I) : normalizedSqDist a b ≥ 0 := by
  unfold normalizedSqDist
  exact div_nonneg (squaredDistance_nonneg a b) (by
    unfold rkhs_norm_sq
    linarith [rs_self_pos' (I := I) a, rs_self_pos' (I := I) b])

theorem normalizedSqDist_self (a : I) : normalizedSqDist a a = 0 := by
  unfold normalizedSqDist; rw [squaredDistance_self]; simp

theorem normalizedSqDist_symm (a b : I) :
    normalizedSqDist a b = normalizedSqDist b a := by
  unfold normalizedSqDist rkhs_norm_sq; rw [squaredDistance_symm, add_comm]

theorem normalizedSqDist_le_one (a b : I) : normalizedSqDist a b ≤ 1 := by
  unfold normalizedSqDist
  have ha := rs_self_pos' (I := I) a
  have hb := rs_self_pos' (I := I) b
  have hsum : rkhs_norm_sq a + rkhs_norm_sq b > 0 := by
    unfold rkhs_norm_sq; linarith
  rw [div_le_one hsum]
  unfold squaredDistance rkhs_norm_sq
  linarith [IdeaticSpace2.rs_nonneg a b]

end MetricStructure
end IDT2
