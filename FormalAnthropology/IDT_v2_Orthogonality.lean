import FormalAnthropology.IDT_Foundations_v2

/-!
# Orthogonality Theory for Ideatic Spaces v2

Two ideas are **orthogonal** when their resonance strength is zero — they inhabit
completely separate semantic domains (like "chess moves" and "cooking recipes").
**Aligned** ideas resonate positively. Because `rs_nonneg` forces all resonance ≥ 0,
**opposition** (negative resonance) is structurally impossible in `IdeaticSpace2`.

This file develops 24 theorems about the orthogonal / aligned partition of idea pairs,
their interaction with composition, and consequences of the Cauchy-Schwarz inequality.

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT2.Orthogonality

variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2 IDT2

/-! ## §1. Definitions -/

/-- Two ideas are orthogonal when their resonance is exactly zero. -/
def orthogonal (a b : I) : Prop := resonanceStrength a b = 0

/-- Two ideas are aligned when their resonance is strictly positive. -/
def aligned (a b : I) : Prop := resonanceStrength a b > 0

/-- Two ideas are opposed when their resonance is negative.
    In `IdeaticSpace2` this is vacuously impossible (`rs_nonneg`),
    but we define it for logical completeness. -/
def opposed (a b : I) : Prop := resonanceStrength a b < 0

/-! ## §2. Symmetry -/

/-- Orthogonality is symmetric. -/
theorem orthogonal_symm {a b : I} (h : orthogonal a b) : orthogonal b a := by
  unfold orthogonal at *; rwa [IdeaticSpace2.rs_symm]

/-- Alignment is symmetric. -/
theorem aligned_symm {a b : I} (h : aligned a b) : aligned b a := by
  unfold aligned at *; rwa [IdeaticSpace2.rs_symm]

/-- Opposition is symmetric (vacuously, since it never holds). -/
theorem opposed_symm {a b : I} (h : opposed a b) : opposed b a := by
  exact absurd h (by unfold opposed; linarith [IdeaticSpace2.rs_nonneg a b])

/-! ## §3. Opposition Is Impossible -/

/-- Opposition never holds: resonance is non-negative. -/
theorem not_opposed (a b : I) : ¬opposed a b := by
  unfold opposed; linarith [IdeaticSpace2.rs_nonneg a b]

/-- Self-opposition is impossible. -/
theorem not_opposed_self (a : I) : ¬opposed a a := not_opposed a a

/-! ## §4. Mutual Exclusion -/

/-- Orthogonal ideas are not aligned. -/
theorem orthogonal_not_aligned {a b : I} (h : orthogonal a b) : ¬aligned a b := by
  unfold orthogonal aligned at *; linarith

/-- Orthogonal ideas are not opposed. -/
theorem orthogonal_not_opposed {a b : I} (_h : orthogonal a b) : ¬opposed a b :=
  not_opposed a b

/-- Aligned ideas are not orthogonal. -/
theorem aligned_not_orthogonal {a b : I} (h : aligned a b) : ¬orthogonal a b := by
  unfold orthogonal aligned at *; linarith

/-- Aligned and opposed cannot both hold. -/
theorem not_aligned_and_opposed (a b : I) : ¬(aligned a b ∧ opposed a b) := by
  intro ⟨_, ho⟩; exact absurd ho (not_opposed a b)

/-! ## §5. The Dichotomy: Aligned or Orthogonal -/

/-- Every idea pair is either aligned or orthogonal (since opposed is impossible). -/
theorem aligned_or_orthogonal (a b : I) : aligned a b ∨ orthogonal a b := by
  unfold aligned orthogonal
  rcases lt_or_eq_of_le (IdeaticSpace2.rs_nonneg a b) with h | h
  · left; exact h
  · right; linarith

/-! ## §6. Self-Resonance Facts -/

/-- Every idea is aligned with itself. -/
theorem aligned_self (a : I) : aligned a a :=
  IdeaticSpace2.rs_self_pos a

/-- No idea is orthogonal to itself. -/
theorem not_orthogonal_self (a : I) : ¬orthogonal a a := by
  unfold orthogonal; linarith [IdeaticSpace2.rs_self_pos a]

/-- Self-alignment strength is at least 1. -/
theorem aligned_self_ge_one (a : I) : resonanceStrength a a ≥ 1 :=
  rs_self_ge_one a

/-! ## §7. Orthogonality and Squared Distance -/

/-- When ideas are orthogonal, squared distance equals the sum of self-resonances. -/
theorem orthogonal_squaredDistance {a b : I} (h : orthogonal a b) :
    squaredDistance a b = resonanceStrength a a + resonanceStrength b b := by
  unfold squaredDistance orthogonal at *; linarith

/-- Squared distance is bounded above by the sum of self-resonances (for any pair). -/
theorem squaredDistance_le_sum_self (a b : I) :
    squaredDistance a b ≤ resonanceStrength a a + resonanceStrength b b := by
  unfold squaredDistance; linarith [IdeaticSpace2.rs_nonneg a b]

/-- Orthogonal pairs achieve the maximum squared distance. -/
theorem orthogonal_maximizes_distance {a b : I} (h : orthogonal a b) :
    squaredDistance a b = resonanceStrength a a + resonanceStrength b b := by
  unfold squaredDistance orthogonal at *; linarith

/-- If squared distance equals the sum of self-resonances, ideas are orthogonal. -/
theorem squaredDistance_max_iff_orthogonal {a b : I}
    (h : squaredDistance a b = resonanceStrength a a + resonanceStrength b b) :
    orthogonal a b := by
  unfold squaredDistance orthogonal at *; linarith

/-! ## §8. Composition Preserves Alignment -/

/-- Composing aligned ideas on the right preserves alignment. -/
theorem compose_preserves_aligned_right {a b : I} (c : I) (h : aligned a b) :
    aligned (compose a c) (compose b c) := by
  unfold aligned at *
  linarith [IdeaticSpace2.rs_compose_right_mono a b c]

/-- Composing on the left preserves alignment. -/
theorem compose_preserves_aligned_left (c : I) {a b : I} (h : aligned a b) :
    aligned (compose c a) (compose c b) := by
  unfold aligned at *
  linarith [IdeaticSpace2.rs_compose_left_mono a b c]

/-- Composed ideas are always self-aligned. -/
theorem compose_self_aligned (a b : I) : aligned (compose a b) (compose a b) :=
  IdeaticSpace2.rs_self_pos _

/-! ## §9. Cauchy-Schwarz Consequences -/

/-- Resonance is bounded by the geometric mean of self-resonances. -/
theorem rs_sq_le_product (a b : I) :
    resonanceStrength a b ^ 2 ≤ resonanceStrength a a * resonanceStrength b b := by
  have h := IdeaticSpace2.rs_cauchy_schwarz a b
  rw [sq]; exact h

/-- Each resonance is ≤ the max of self-resonances. -/
theorem rs_le_max_self (a b : I) :
    resonanceStrength a b ≤ max (resonanceStrength a a) (resonanceStrength b b) := by
  rcases le_total (resonanceStrength a a) (resonanceStrength b b) with hab | hab
  · have := rs_le_self_when (I := I) b a (by rwa [IdeaticSpace2.rs_symm])
    rw [IdeaticSpace2.rs_symm] at this
    exact le_max_of_le_right this
  · exact le_max_of_le_left (rs_le_self_when a b hab)

/-- Aligned pair: resonance bounded by either self-resonance. -/
theorem aligned_le_self_or {a b : I} :
    resonanceStrength a b ≤ resonanceStrength a a ∨
    resonanceStrength a b ≤ resonanceStrength b b := by
  by_contra h
  push_neg at h
  have hcs := IdeaticSpace2.rs_cauchy_schwarz a b
  have ha := IdeaticSpace2.rs_self_pos a
  have hb := IdeaticSpace2.rs_self_pos b
  have hab := IdeaticSpace2.rs_nonneg a b
  -- rs(a,b) > rs(a,a) > 0 and rs(a,b) > rs(b,b) > 0
  -- So rs(a,b)² > rs(a,a) * rs(a,b) > rs(a,a) * rs(b,b), contradicting C-S
  nlinarith [mul_lt_mul_of_pos_left h.1 (by linarith : (0 : ℝ) < resonanceStrength a b)]

/-! ## §10. Normalized Resonance and Orthogonality -/

/-- Orthogonal ideas have zero normalized resonance. -/
theorem orthogonal_normalizedRS {a b : I} (h : orthogonal a b) :
    normalizedRS a b = 0 := by
  unfold normalizedRS orthogonal at *
  rw [h]; simp

/-- Aligned ideas have positive normalized resonance. -/
theorem aligned_normalizedRS_pos {a b : I} (h : aligned a b) :
    normalizedRS a b > 0 := by
  unfold normalizedRS aligned at *
  apply div_pos
  · exact mul_pos h h
  · exact mul_pos (IdeaticSpace2.rs_self_pos a) (IdeaticSpace2.rs_self_pos b)

end IDT2.Orthogonality
