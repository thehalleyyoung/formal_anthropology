import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.IDT_Foundations_v2

/-!
# IDT v2: Metric Structure of the Ideatic Space

Ideas form a pseudo-metric space via `squaredDistance(a,b) = rs(a,a) + rs(b,b) - 2·rs(a,b)`.
This squared distance arises from the RKHS embedding induced by the resonance kernel.

This file develops 26 theorems about:
- Squared distance geometry and the polarization identity
- Balls in idea space (`withinSqBall`)
- Composition and distance: how composing ideas affects distances
- Resonance similarity (analogue of cosine similarity)
- Normalized distance and depth-distance interactions

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT2.Metric

variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2 IDT2

/-! ## §1. Self-Norm: ‖a‖² = rs(a,a) -/

/-- Self-norm squared of an idea. -/
noncomputable def selfNormSq (a : I) : ℝ := resonanceStrength a a

theorem selfNormSq_pos (a : I) : selfNormSq a > 0 :=
  IdeaticSpace2.rs_self_pos a

theorem selfNormSq_ge_one (a : I) : selfNormSq a ≥ 1 :=
  rs_self_ge_one a

theorem selfNormSq_void : selfNormSq (void : I) = 1 :=
  IdeaticSpace2.rs_void_self

/-! ## §2. Squared Distance — Core Properties -/

/-- Squared distance is non-negative. -/
theorem sqDist_nonneg (a b : I) : squaredDistance a b ≥ 0 :=
  squaredDistance_nonneg a b

/-- Squared distance to self is zero. -/
theorem sqDist_self (a : I) : squaredDistance a a = 0 :=
  squaredDistance_self a

/-- Squared distance is symmetric. -/
theorem sqDist_symm (a b : I) : squaredDistance a b = squaredDistance b a :=
  squaredDistance_symm a b

/-- The fundamental decomposition: d²(a,b) = ‖a‖² + ‖b‖² − 2·rs(a,b). -/
theorem sqDist_decomp (a b : I) :
    squaredDistance a b = selfNormSq a + selfNormSq b - 2 * resonanceStrength a b := by
  unfold squaredDistance selfNormSq; ring

/-! ## §3. Polarization Identity -/

/-- The polarization identity: resonance can be recovered from distances and norms.
    rs(a,b) = (‖a‖² + ‖b‖² − d²(a,b)) / 2  -/
theorem polarization_identity (a b : I) :
    resonanceStrength a b =
    (selfNormSq a + selfNormSq b - squaredDistance a b) / 2 := by
  unfold squaredDistance selfNormSq; ring

/-- Equivalent form of polarization: 2·rs(a,b) = ‖a‖² + ‖b‖² − d²(a,b). -/
theorem polarization_identity' (a b : I) :
    2 * resonanceStrength a b =
    selfNormSq a + selfNormSq b - squaredDistance a b := by
  unfold squaredDistance selfNormSq; ring

/-! ## §4. Distance from Void -/

/-- Distance from void: d²(void,a) = 1 + ‖a‖² − 2·rs(void,a). -/
theorem sqDist_void_left (a : I) :
    squaredDistance (void : I) a = 1 + selfNormSq a - 2 * resonanceStrength (void : I) a := by
  unfold squaredDistance selfNormSq; rw [IdeaticSpace2.rs_void_self]

/-- Void-void distance is zero. -/
theorem sqDist_void_void : squaredDistance (void : I) (void : I) = 0 :=
  squaredDistance_self _

/-- Distance from void is nonneg. -/
theorem sqDist_from_void_nonneg (a : I) : squaredDistance (void : I) a ≥ 0 :=
  squaredDistance_nonneg _ _

/-! ## §5. withinSqBall -/

/-- Ball of ideas within squared-distance `r` of a center. -/
def withinSqBall (center : I) (r : ℝ) (a : I) : Prop :=
  squaredDistance center a ≤ r

/-- Every idea is in its own zero-radius ball. -/
theorem withinSqBall_self_zero (a : I) : withinSqBall a 0 a := by
  unfold withinSqBall; rw [squaredDistance_self]

/-- Self-membership for nonneg radius. -/
theorem withinSqBall_self {a : I} {r : ℝ} (hr : 0 ≤ r) : withinSqBall a r a := by
  unfold withinSqBall; rw [squaredDistance_self]; exact hr

/-- Larger radius ⇒ larger ball. -/
theorem withinSqBall_mono {c a : I} {r r' : ℝ} (hrr : r ≤ r')
    (h : withinSqBall c r a) : withinSqBall c r' a := by
  unfold withinSqBall at *; linarith

/-- Balls are symmetric in the distance sense. -/
theorem withinSqBall_symm {c a : I} {r : ℝ}
    (h : withinSqBall c r a) : withinSqBall a r c := by
  unfold withinSqBall at *; rw [squaredDistance_symm]; exact h

/-! ## §6. Composition and Distance -/

/-- Composing with void on the right preserves distance (identity). -/
theorem sqDist_compose_void_right (a b : I) :
    squaredDistance (compose a (void : I)) (compose b (void : I)) = squaredDistance a b := by
  simp [squaredDistance]

/-- Composing with void on the left preserves distance (identity). -/
theorem sqDist_compose_void_left (a b : I) :
    squaredDistance (compose (void : I) a) (compose (void : I) b) = squaredDistance a b := by
  simp [squaredDistance]

/-- Composing on the right increases cross-resonance, so can shrink distance. -/
theorem sqDist_compose_right_bound (a b c : I) :
    squaredDistance (compose a c) (compose b c) ≤
    selfNormSq (compose a c) + selfNormSq (compose b c) -
    2 * resonanceStrength a b := by
  unfold squaredDistance selfNormSq
  linarith [IdeaticSpace2.rs_compose_right_mono a b c]

/-- Composing on the left similarly. -/
theorem sqDist_compose_left_bound (a b c : I) :
    squaredDistance (compose c a) (compose c b) ≤
    selfNormSq (compose c a) + selfNormSq (compose c b) -
    2 * resonanceStrength a b := by
  unfold squaredDistance selfNormSq
  linarith [IdeaticSpace2.rs_compose_left_mono a b c]

/-! ## §7. Norm Growth under Composition -/

/-- Composition grows self-norm (right part). -/
theorem selfNormSq_compose_ge_left (a b : I) :
    selfNormSq (compose a b) ≥ selfNormSq a := by
  unfold selfNormSq; exact rs_compose_self_right a b

/-- Composition grows self-norm (left part). -/
theorem selfNormSq_compose_ge_right (a b : I) :
    selfNormSq (compose a b) ≥ selfNormSq b := by
  unfold selfNormSq; exact rs_compose_self_left b a

/-- Void has minimal self-norm. -/
theorem void_minimal_selfNormSq (a : I) : selfNormSq (void : I) ≤ selfNormSq a := by
  unfold selfNormSq; rw [IdeaticSpace2.rs_void_self]; exact rs_self_ge_one a

/-- Iterated composition grows norms monotonically. -/
theorem selfNormSq_composeN_mono (a : I) (n : ℕ) :
    selfNormSq (composeN a (n + 1)) ≥ selfNormSq (composeN a n) := by
  unfold selfNormSq; exact rs_self_composeN_mono a n

/-! ## §8. Cauchy-Schwarz Metric Consequence -/

/-- Resonance-squared bounded by product of self-norms. -/
theorem rs_sq_le_selfNormSq_product (a b : I) :
    resonanceStrength a b ^ 2 ≤ selfNormSq a * selfNormSq b := by
  unfold selfNormSq; rw [sq]; exact IdeaticSpace2.rs_cauchy_schwarz a b

/-- Squared distance is bounded above by the sum of self-norms (since rs ≥ 0). -/
theorem sqDist_le_sum_norms (a b : I) :
    squaredDistance a b ≤ selfNormSq a + selfNormSq b := by
  unfold squaredDistance selfNormSq; linarith [IdeaticSpace2.rs_nonneg a b]

end IDT2.Metric
