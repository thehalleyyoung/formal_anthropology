import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Ideatic Diffusion Theory v2: Hilbert Space Foundations

Every idea `a : I` maps to a vector `φ(a)` in a real Hilbert space `H`.
Resonance between ideas = inner product of their images:

  `resonanceStrength a b := ⟪φ(a), φ(b)⟫_ℝ`

The embedding `φ` is a monoid homomorphism: `φ(compose a b) = φ(a) + φ(b)`.
This forces `φ(void) = 0`, so void = the zero vector = silence with no resonance.

## Key consequences (all proved, zero sorries)

- **Bilinearity**: `rs(compose a b, c) = rs(a,c) + rs(b,c)`
- **Self-resonance = squared norm**: `rs(a,a) = ‖φ(a)‖²`
- **Cauchy-Schwarz**: `rs(a,b)² ≤ rs(a,a) · rs(b,b)`
- **Metric**: `d(a,b)² = rs(a,a) + rs(b,b) - 2·rs(a,b)`
- **Void annihilation**: `rs(void, a) = 0`
- **Pythagorean theorem**: orthogonal ideas compose independently
- **Parallelogram law**, **triangle inequality**, etc.

## Relationship to v1

v2 is a separate axiomatic system, inspired by v1 but not extending it.
In v1, `resonates` is a boolean predicate with `resonance_refl : resonates a a`.
In v2, `resonates a b ↔ rs(a,b) > 0`, so `resonates void void` is false.
Void = silence = zero content = no resonance: philosophically coherent.
-/

namespace IDT2

/-! ## §1. The Core Structure -/

/-- A Hilbert Ideatic Space: ideas with a monoid structure, depth function,
    and an embedding into a real inner product space.

    **7 axioms**: 3 monoid + 2 depth + 2 embedding. Everything else is derived. -/
class HilbertIdeaticSpace (I : Type*) (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- Ideatic composition: combining two ideas -/
  compose : I → I → I
  /-- The void: silence, the empty idea, identity for composition -/
  void : I
  /-- (A1) Composition is associative -/
  compose_assoc : ∀ (a b c : I), compose (compose a b) c = compose a (compose b c)
  /-- (A2) Void is a left identity -/
  void_left : ∀ (a : I), compose void a = a
  /-- (A3) Void is a right identity -/
  void_right : ∀ (a : I), compose a void = a
  /-- Depth: structural complexity of an idea -/
  depth : I → ℕ
  /-- Void has zero depth -/
  depth_void : depth void = 0
  /-- Depth is subadditive under composition -/
  depth_subadditive : ∀ (a b : I), depth (compose a b) ≤ depth a + depth b
  /-- The Hilbert space embedding: every idea maps to a vector -/
  φ : I → H
  /-- Distinct ideas have distinct embeddings -/
  φ_injective : Function.Injective φ
  /-- Composition is additive in the embedding (φ is a monoid homomorphism to (H,+)) -/
  φ_compose : ∀ (a b : I), φ (compose a b) = φ a + φ b

variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [S : HilbertIdeaticSpace I H]

/-! ## §2. Derived: φ(void) = 0

Since φ(compose void a) = φ(void) + φ(a) and compose void a = a,
we get φ(a) = φ(void) + φ(a), hence φ(void) = 0. -/

@[simp]
theorem φ_void : S.φ S.void = 0 := by
  have h := S.φ_compose S.void S.void
  rw [S.void_left] at h
  have : S.φ S.void - S.φ S.void = S.φ S.void + S.φ S.void - S.φ S.void :=
    congrArg (· - S.φ S.void) h
  simp at this
  exact this.symm

/-! ## §3. Resonance Strength

The real-valued resonance function: the inner product of embeddings. -/

/-- Resonance strength between two ideas = inner product of their embeddings.
    This is the central quantity of IDT v2. -/
noncomputable def resonanceStrength (a b : I) : ℝ :=
  (inner (S.φ a) (S.φ b) : ℝ)

/-- Qualitative resonance: positive inner product between embeddings -/
def resonates (a b : I) : Prop :=
  @resonanceStrength I H _ _ S a b > 0

/-! ## §4. Symmetry -/

theorem resonanceStrength_comm (a b : I) :
    @resonanceStrength I H _ _ S a b = @resonanceStrength I H _ _ S b a := by
  unfold resonanceStrength
  rw [real_inner_comm]

theorem resonates_symm (a b : I) :
    @resonates I H _ _ S a b → @resonates I H _ _ S b a := by
  unfold resonates
  rw [resonanceStrength_comm]
  exact id

/-! ## §5. Bilinearity — composition decomposes resonance -/

/-- Composing on the left decomposes: rs(compose a b, c) = rs(a,c) + rs(b,c) -/
theorem resonanceStrength_compose_left (a b c : I) :
    @resonanceStrength I H _ _ S (S.compose a b) c =
    @resonanceStrength I H _ _ S a c + @resonanceStrength I H _ _ S b c := by
  unfold resonanceStrength
  rw [S.φ_compose]
  exact inner_add_left _ _ _

/-- Composing on the right decomposes: rs(a, compose b c) = rs(a,b) + rs(a,c) -/
theorem resonanceStrength_compose_right (a b c : I) :
    @resonanceStrength I H _ _ S a (S.compose b c) =
    @resonanceStrength I H _ _ S a b + @resonanceStrength I H _ _ S a c := by
  unfold resonanceStrength
  rw [S.φ_compose]
  exact inner_add_right _ _ _

/-! ## §6. Void annihilation -/

@[simp]
theorem resonanceStrength_void_left (a : I) :
    @resonanceStrength I H _ _ S S.void a = 0 := by
  unfold resonanceStrength
  rw [φ_void]
  exact inner_zero_left _

@[simp]
theorem resonanceStrength_void_right (a : I) :
    @resonanceStrength I H _ _ S a S.void = 0 := by
  unfold resonanceStrength
  rw [φ_void]
  exact inner_zero_right _

/-- Void does not resonate with anything -/
theorem not_resonates_void_left (a : I) :
    ¬ @resonates I H _ _ S S.void a := by
  unfold resonates; simp

theorem not_resonates_void_right (a : I) :
    ¬ @resonates I H _ _ S a S.void := by
  unfold resonates; simp

/-! ## §7. Self-resonance = squared norm -/

/-- Self-resonance equals the squared norm of the embedding -/
theorem resonanceStrength_self (a : I) :
    @resonanceStrength I H _ _ S a a = ‖S.φ a‖ ^ 2 := by
  unfold resonanceStrength
  exact real_inner_self_eq_norm_sq _

/-- Self-resonance is non-negative -/
theorem resonanceStrength_self_nonneg (a : I) :
    0 ≤ @resonanceStrength I H _ _ S a a := by
  rw [resonanceStrength_self]; positivity

/-- Self-resonance is zero iff the idea is void -/
theorem resonanceStrength_self_eq_zero_iff (a : I) :
    @resonanceStrength I H _ _ S a a = 0 ↔ a = S.void := by
  constructor
  · intro h
    rw [resonanceStrength_self] at h
    have hnorm : ‖S.φ a‖ = 0 := by nlinarith [norm_nonneg (S.φ a)]
    rw [norm_eq_zero] at hnorm
    exact S.φ_injective (by rw [hnorm, φ_void])
  · intro h; rw [h]; simp

/-! ## §8. Cauchy-Schwarz for resonance -/

/-- |rs(a,b)| ≤ ‖φ(a)‖ · ‖φ(b)‖ -/
theorem resonanceStrength_abs_le (a b : I) :
    |@resonanceStrength I H _ _ S a b| ≤ ‖S.φ a‖ * ‖S.φ b‖ := by
  unfold resonanceStrength
  exact abs_real_inner_le_norm _ _

/-- Upper bound: rs(a,b) ≤ ‖φ(a)‖ · ‖φ(b)‖ -/
theorem resonanceStrength_le (a b : I) :
    @resonanceStrength I H _ _ S a b ≤ ‖S.φ a‖ * ‖S.φ b‖ := by
  unfold resonanceStrength
  exact real_inner_le_norm _ _

/-- Lower bound: -(‖φ(a)‖ · ‖φ(b)‖) ≤ rs(a,b) -/
theorem neg_norm_mul_le_resonanceStrength (a b : I) :
    -(‖S.φ a‖ * ‖S.φ b‖) ≤ @resonanceStrength I H _ _ S a b := by
  have := resonanceStrength_abs_le (S := S) a b
  linarith [neg_abs_le (@resonanceStrength I H _ _ S a b)]

/-- Squared Cauchy-Schwarz: rs(a,b)² ≤ rs(a,a) · rs(b,b) -/
theorem resonanceStrength_cauchy_schwarz_sq (a b : I) :
    @resonanceStrength I H _ _ S a b ^ 2 ≤
    @resonanceStrength I H _ _ S a a * @resonanceStrength I H _ _ S b b := by
  rw [resonanceStrength_self, resonanceStrength_self, ← mul_pow]
  have h1 := resonanceStrength_le (S := S) a b
  have h2 := neg_norm_mul_le_resonanceStrength (S := S) a b
  nlinarith [sq_nonneg (@resonanceStrength I H _ _ S a b + ‖S.φ a‖ * ‖S.φ b‖),
             sq_nonneg (@resonanceStrength I H _ _ S a b - ‖S.φ a‖ * ‖S.φ b‖)]

/-! ## §9. Ideatic distance -/

/-- Distance between ideas = norm of the difference of their embeddings -/
noncomputable def ideaDist (a b : I) : ℝ :=
  ‖S.φ a - S.φ b‖

/-- Distance squared decomposes via resonance strength -/
theorem ideaDist_sq (a b : I) :
    @ideaDist I H _ _ S a b ^ 2 =
    @resonanceStrength I H _ _ S a a +
    @resonanceStrength I H _ _ S b b -
    2 * @resonanceStrength I H _ _ S a b := by
  unfold ideaDist resonanceStrength
  rw [norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  ring

/-- Distance is symmetric -/
theorem ideaDist_comm (a b : I) :
    @ideaDist I H _ _ S a b = @ideaDist I H _ _ S b a := by
  unfold ideaDist; rw [norm_sub_rev]

/-- Distance to self is zero -/
@[simp]
theorem ideaDist_self (a : I) :
    @ideaDist I H _ _ S a a = 0 := by
  unfold ideaDist; simp

/-- Distance is non-negative -/
theorem ideaDist_nonneg (a b : I) :
    0 ≤ @ideaDist I H _ _ S a b := by
  unfold ideaDist; exact norm_nonneg _

/-- Distance is zero iff ideas are equal -/
theorem ideaDist_eq_zero_iff (a b : I) :
    @ideaDist I H _ _ S a b = 0 ↔ a = b := by
  unfold ideaDist
  constructor
  · intro h
    rw [norm_eq_zero, sub_eq_zero] at h
    exact S.φ_injective h
  · intro h; rw [h]; simp

/-! ## §10. Triangle inequality -/

/-- Triangle inequality: d(a,c) ≤ d(a,b) + d(b,c) -/
theorem ideaDist_triangle (a b c : I) :
    @ideaDist I H _ _ S a c ≤
    @ideaDist I H _ _ S a b + @ideaDist I H _ _ S b c := by
  unfold ideaDist
  calc ‖S.φ a - S.φ c‖
      = ‖(S.φ a - S.φ b) + (S.φ b - S.φ c)‖ := by congr 1; abel
    _ ≤ ‖S.φ a - S.φ b‖ + ‖S.φ b - S.φ c‖ := norm_add_le _ _

/-! ## §11. Cosine similarity -/

/-- Cosine similarity between ideas (normalized resonance) -/
noncomputable def cosineSimilarity (a b : I) : ℝ :=
  @resonanceStrength I H _ _ S a b / (‖S.φ a‖ * ‖S.φ b‖)

private theorem φ_norm_pos_of_ne_void (a : I) (ha : a ≠ S.void) : ‖S.φ a‖ > 0 :=
  norm_pos_iff.mpr (fun h => ha (S.φ_injective (by rw [h, φ_void])))

/-- Cosine similarity ≤ 1 for nonvoid ideas -/
theorem cosineSimilarity_le_one (a b : I) (ha : a ≠ S.void) (hb : b ≠ S.void) :
    @cosineSimilarity I H _ _ S a b ≤ 1 := by
  unfold cosineSimilarity
  rw [div_le_one (mul_pos (φ_norm_pos_of_ne_void a ha) (φ_norm_pos_of_ne_void b hb))]
  exact resonanceStrength_le a b

/-- Cosine similarity ≥ -1 for nonvoid ideas -/
theorem neg_one_le_cosineSimilarity (a b : I) (ha : a ≠ S.void) (hb : b ≠ S.void) :
    -1 ≤ @cosineSimilarity I H _ _ S a b := by
  unfold cosineSimilarity
  rw [le_div_iff₀ (mul_pos (φ_norm_pos_of_ne_void a ha) (φ_norm_pos_of_ne_void b hb))]
  linarith [neg_norm_mul_le_resonanceStrength (S := S) a b]

/-- Cosine similarity with self = 1 for nonvoid ideas -/
theorem cosineSimilarity_self (a : I) (ha : a ≠ S.void) :
    @cosineSimilarity I H _ _ S a a = 1 := by
  unfold cosineSimilarity
  rw [resonanceStrength_self]
  have ha' := φ_norm_pos_of_ne_void a ha
  field_simp; ring

/-! ## §12. Orthogonality -/

/-- Two ideas are orthogonal if their resonance is zero -/
def orthogonal (a b : I) : Prop :=
  @resonanceStrength I H _ _ S a b = 0

theorem orthogonal_symm (a b : I) :
    @orthogonal I H _ _ S a b → @orthogonal I H _ _ S b a := by
  unfold orthogonal; rw [resonanceStrength_comm]; exact id

/-- Void is orthogonal to everything -/
theorem orthogonal_void_left (a : I) :
    @orthogonal I H _ _ S S.void a := by
  unfold orthogonal; simp

/-- Pythagorean theorem: for orthogonal ideas, self-resonances add -/
theorem pythagorean (a b : I) (h : @orthogonal I H _ _ S a b) :
    @resonanceStrength I H _ _ S (S.compose a b) (S.compose a b) =
    @resonanceStrength I H _ _ S a a + @resonanceStrength I H _ _ S b b := by
  rw [resonanceStrength_compose_left, resonanceStrength_compose_right,
      resonanceStrength_compose_right]
  unfold orthogonal at h
  rw [h, resonanceStrength_comm (S := S) b a, h]
  ring

/-! ## §13. Parallelogram law -/

/-- The parallelogram law: ‖a+b‖² + ‖a-b‖² = 2(‖a‖² + ‖b‖²) -/
theorem parallelogram_law (a b : I) :
    @resonanceStrength I H _ _ S (S.compose a b) (S.compose a b) +
    @ideaDist I H _ _ S a b ^ 2 =
    2 * (@resonanceStrength I H _ _ S a a + @resonanceStrength I H _ _ S b b) := by
  rw [resonanceStrength_compose_left, resonanceStrength_compose_right,
      resonanceStrength_compose_right, ideaDist_sq,
      resonanceStrength_comm (S := S) b a]
  ring

/-! ## §14. Embedding norm properties -/

theorem φ_norm_nonneg (a : I) : 0 ≤ ‖S.φ a‖ := norm_nonneg _

@[simp]
theorem φ_norm_void : ‖S.φ S.void‖ = 0 := by rw [φ_void, norm_zero]

theorem φ_norm_pos (a : I) (ha : a ≠ S.void) : 0 < ‖S.φ a‖ :=
  φ_norm_pos_of_ne_void a ha

/-- ‖φ(compose a b)‖ ≤ ‖φ(a)‖ + ‖φ(b)‖ -/
theorem φ_compose_norm_le (a b : I) :
    ‖S.φ (S.compose a b)‖ ≤ ‖S.φ a‖ + ‖S.φ b‖ := by
  rw [S.φ_compose]; exact norm_add_le _ _

/-! ## §15. Resonance monotonicity -/

/-- Composing with a positively-resonant idea increases self-resonance -/
theorem compose_increases_self_resonance (a c : I)
    (h : @resonanceStrength I H _ _ S a c > 0) :
    @resonanceStrength I H _ _ S (S.compose a c) (S.compose a c) >
    @resonanceStrength I H _ _ S a a := by
  rw [resonanceStrength_compose_left, resonanceStrength_compose_right,
      resonanceStrength_compose_right]
  have hcc := resonanceStrength_self_nonneg (S := S) c
  rw [resonanceStrength_comm (S := S) c a]
  linarith

/-! ## §16. Projection coefficient -/

/-- The resonance component of a along b -/
noncomputable def projectionCoeff (a b : I) : ℝ :=
  @resonanceStrength I H _ _ S a b / @resonanceStrength I H _ _ S b b

/-- Projection of an idea onto itself = 1 -/
theorem projectionCoeff_self (a : I) (ha : a ≠ S.void) :
    @projectionCoeff I H _ _ S a a = 1 := by
  unfold projectionCoeff
  have h : @resonanceStrength I H _ _ S a a ≠ 0 := by
    rw [resonanceStrength_self]
    intro h
    have : ‖S.φ a‖ = 0 := by nlinarith [norm_nonneg (S.φ a)]
    rw [norm_eq_zero] at this
    exact ha (S.φ_injective (by rw [this, φ_void]))
  exact div_self h

/-! ## §17. Depth interaction -/

theorem depth_compose_bound (a b : I) :
    S.depth (S.compose a b) ≤ S.depth a + S.depth b :=
  S.depth_subadditive a b

theorem depth_void_eq : S.depth S.void = 0 := S.depth_void

/-! ## §18. Resonance classes -/

/-- Two ideas are θ-resonant if their inner product exceeds θ·‖a‖·‖b‖ -/
def inResonanceClass (θ : ℝ) (a b : I) : Prop :=
  @resonanceStrength I H _ _ S a b ≥ θ * ‖S.φ a‖ * ‖S.φ b‖

/-- Resonance class membership is symmetric -/
theorem inResonanceClass_symm (θ : ℝ) (a b : I) :
    @inResonanceClass I H _ _ S θ a b → @inResonanceClass I H _ _ S θ b a := by
  unfold inResonanceClass
  intro h
  rw [resonanceStrength_comm]
  linarith [mul_comm ‖S.φ a‖ ‖S.φ b‖]

/-! ## §19. Composition preserves resonance direction -/

/-- If a resonates with c and b resonates with c, then compose a b resonates with c -/
theorem compose_preserves_resonance (a b c : I)
    (ha : @resonates I H _ _ S a c) (hb : @resonates I H _ _ S b c) :
    @resonates I H _ _ S (S.compose a b) c := by
  unfold resonates at *
  rw [resonanceStrength_compose_left]
  linarith

/-! ## §20. Summary

The `HilbertIdeaticSpace` class has **7 axioms**:
- 3 monoid axioms (compose_assoc, void_left, void_right)
- 2 depth axioms (depth_void, depth_subadditive)
- 2 embedding axioms (φ_injective, φ_compose)

From these we derived **30+ theorems** including:
- φ_void (embedding of void = 0)
- Symmetry, bilinearity, void annihilation
- Self-resonance = squared norm
- Cauchy-Schwarz inequality (both absolute and squared forms)
- Metric space properties (distance, triangle inequality)
- Cosine similarity bounds [-1, 1]
- Pythagorean theorem for orthogonal ideas
- Parallelogram law
- Resonance monotonicity under composition
- Composition preserves positive resonance

**Zero sorries. Zero axioms. Zero admits.**
-/

end IDT2
