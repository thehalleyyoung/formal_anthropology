import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.IDT_Foundations_v2

/-!
# IDT v2: Cooperation and Conflict Between Ideas

The resonance between idea-vectors determines whether interaction is
cooperative (positive resonance) or independent. In this non-negative
resonance model, "conflict" (negative resonance) is provably impossible —
a deep structural result showing that all ideas share some baseline
compatibility.

## Key Definitions
- `cooperates a b`: ideas positively resonate (rs > 0)
- `conflicts a b`: ideas negatively resonate (rs < 0) — provably empty
- `jointPayoff a b`: self-resonance of the composed idea
- `cooperationSurplus a b`: extra value from composition beyond sum of parts

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT2.Cooperation

variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-! ## §1. Core Definitions -/

/-- Two ideas cooperate if their resonance is strictly positive -/
def cooperates (a b : I) : Prop := resonanceStrength a b > 0

/-- Two ideas conflict if their resonance is negative -/
def conflicts (a b : I) : Prop := resonanceStrength a b < 0

/-- The cooperation surplus: extra self-resonance from composition beyond sum of parts -/
noncomputable def cooperationSurplus (a b : I) : ℝ :=
  resonanceStrength (compose a b) (compose a b) -
  (resonanceStrength a a + resonanceStrength b b)

/-- Joint payoff from cooperation: self-resonance of the composed idea -/
noncomputable def jointPayoff (a b : I) : ℝ :=
  resonanceStrength (compose a b) (compose a b)

/-- Cooperation ratio: pairwise resonance relative to self-resonance -/
noncomputable def cooperationRatio (a b : I) : ℝ :=
  resonanceStrength a b / resonanceStrength a a

/-! ## §2. Symmetry and Basic Properties -/

/-- Theorem 1: Cooperation is symmetric -/
theorem cooperates_symm (a b : I) : cooperates a b → cooperates b a := by
  unfold cooperates; rw [rs_symm']; exact id

/-- Theorem 2: Conflict is symmetric -/
theorem conflicts_symm (a b : I) : conflicts a b → conflicts b a := by
  unfold conflicts; rw [rs_symm']; exact id

/-- Theorem 3: Cooperation and conflict are mutually exclusive -/
theorem cooperates_not_conflicts (a b : I) : ¬(cooperates a b ∧ conflicts a b) := by
  unfold cooperates conflicts; intro ⟨h1, h2⟩; linarith

/-- Theorem 4: Every idea cooperates with itself -/
theorem self_cooperates (a : I) : cooperates a a := by
  unfold cooperates; exact rs_self_pos' a

/-- Theorem 5: Void cooperates with itself (rs = 1) -/
theorem void_cooperates_self : cooperates (void : I) (void : I) := by
  unfold cooperates; rw [rs_void_unit]; linarith

/-! ## §3. The Impossibility of Conflict -/

/-- Theorem 6: Conflicts are impossible — resonance is always non-negative -/
theorem no_conflicts (a b : I) : ¬conflicts a b := by
  unfold conflicts; linarith [rs_nonneg' a b]

/-- Theorem 7: Every pair either cooperates or has zero resonance -/
theorem cooperates_or_zero (a b : I) :
    cooperates a b ∨ resonanceStrength a b = 0 := by
  unfold cooperates
  rcases le_or_lt (resonanceStrength a b) 0 with h | h
  · right; linarith [rs_nonneg' a b]
  · left; exact h

/-- Theorem 8: Not cooperating iff resonance is exactly zero -/
theorem not_cooperates_iff_zero (a b : I) :
    ¬cooperates a b ↔ resonanceStrength a b = 0 := by
  unfold cooperates
  constructor
  · intro h; linarith [rs_nonneg' a b]
  · intro h; linarith

/-! ## §4. Joint Payoff Theory -/

/-- Theorem 9: Joint payoff exceeds left component's self-resonance -/
theorem jointPayoff_ge_left (a b : I) :
    jointPayoff a b ≥ resonanceStrength a a := by
  unfold jointPayoff; exact rs_compose_self_right a b

/-- Theorem 10: Joint payoff exceeds right component's self-resonance -/
theorem jointPayoff_ge_right (a b : I) :
    jointPayoff a b ≥ resonanceStrength b b := by
  unfold jointPayoff; exact rs_compose_self_left b a

/-- Theorem 11: Joint payoff is always at least 1 -/
theorem jointPayoff_ge_one (a b : I) : jointPayoff a b ≥ 1 := by
  unfold jointPayoff; exact rs_compose_ge_one a b

/-- Theorem 12: Joint payoff is strictly positive -/
theorem jointPayoff_pos (a b : I) : jointPayoff a b > 0 := by
  linarith [jointPayoff_ge_one (I := I) a b]

/-- Theorem 13: Joint payoff is non-negative -/
theorem jointPayoff_nonneg (a b : I) : jointPayoff a b ≥ 0 := by
  linarith [jointPayoff_ge_one (I := I) a b]

/-- Theorem 14: Joint payoff with void on left yields self-resonance -/
theorem jointPayoff_void_left (b : I) :
    jointPayoff (void : I) b = resonanceStrength b b := by
  unfold jointPayoff; rw [void_left]

/-- Theorem 15: Joint payoff with void on right yields self-resonance -/
theorem jointPayoff_void_right (a : I) :
    jointPayoff a (void : I) = resonanceStrength a a := by
  unfold jointPayoff; rw [void_right]

/-- Theorem 16: Joint payoff of void with void is 1 -/
theorem jointPayoff_void_void :
    jointPayoff (void : I) (void : I) = 1 := by
  unfold jointPayoff; rw [void_left]; exact rs_void_unit

/-- Theorem 17: Joint payoff exceeds the max of individual self-resonances -/
theorem jointPayoff_ge_max (a b : I) :
    jointPayoff a b ≥ max (resonanceStrength a a) (resonanceStrength b b) :=
  max_le (jointPayoff_ge_left a b) (jointPayoff_ge_right a b)

/-! ## §5. Cooperation Surplus -/

/-- Theorem 18: Surplus decomposes as joint payoff minus parts -/
theorem surplus_eq_jp_minus_parts (a b : I) :
    cooperationSurplus a b =
    jointPayoff a b - resonanceStrength a a - resonanceStrength b b := by
  unfold cooperationSurplus jointPayoff; ring

/-- Theorem 19: Joint payoff = sum of parts + surplus -/
theorem jointPayoff_from_parts (a b : I) :
    jointPayoff a b =
    resonanceStrength a a + resonanceStrength b b + cooperationSurplus a b := by
  unfold cooperationSurplus jointPayoff; ring

/-- Theorem 20: Surplus is bounded below by negative right self-resonance -/
theorem surplus_ge_neg_right (a b : I) :
    cooperationSurplus a b ≥ -resonanceStrength b b := by
  unfold cooperationSurplus
  linarith [rs_compose_self_right (I := I) a b]

/-- Theorem 21: Surplus is bounded below by negative left self-resonance -/
theorem surplus_ge_neg_left (a b : I) :
    cooperationSurplus a b ≥ -resonanceStrength a a := by
  unfold cooperationSurplus
  linarith [rs_compose_self_left (I := I) b a]

/-- Theorem 22: Composing with void gives surplus = -1 -/
theorem surplus_void_right (a : I) :
    cooperationSurplus a (void : I) = -1 := by
  unfold cooperationSurplus; rw [void_right, rs_void_unit]; ring

/-- Theorem 23: Void on left also gives surplus = -1 -/
theorem surplus_void_left (a : I) :
    cooperationSurplus (void : I) a = -1 := by
  unfold cooperationSurplus; rw [void_left, rs_void_unit]; ring

/-- Theorem 24: Surplus of void with void is -1 -/
theorem surplus_void_void :
    cooperationSurplus (void : I) (void : I) = -1 :=
  surplus_void_left _

/-! ## §6. Composition Preserves Cooperation -/

/-- Theorem 25: Cooperation is preserved under right composition -/
theorem cooperates_compose_right (a b c : I) :
    cooperates a b → cooperates (compose a c) (compose b c) := by
  unfold cooperates
  intro h; linarith [rs_compose_both_mono (I := I) a b c]

/-- Theorem 26: Cooperation is preserved under left composition -/
theorem cooperates_compose_left (a b c : I) :
    cooperates a b → cooperates (compose c a) (compose c b) := by
  unfold cooperates
  intro h; linarith [IdeaticSpace2.rs_compose_left_mono a b c]

/-- Theorem 27: Any composed idea cooperates with itself -/
theorem cooperates_compose_self (a b : I) :
    cooperates (compose a b) (compose a b) := by
  unfold cooperates; linarith [rs_compose_ge_one (I := I) a b]

/-! ## §7. Cooperation Ratio -/

/-- Theorem 28: Cooperation ratio with self is 1 -/
theorem cooperationRatio_self (a : I) : cooperationRatio a a = 1 := by
  unfold cooperationRatio; exact div_self (ne_of_gt (rs_self_pos' a))

/-- Theorem 29: Cooperation ratio is non-negative -/
theorem cooperationRatio_nonneg (a b : I) : cooperationRatio a b ≥ 0 := by
  unfold cooperationRatio
  have h1 : (0 : ℝ) ≤ resonanceStrength a b := rs_nonneg' a b
  have h2 : (0 : ℝ) < resonanceStrength a a := rs_self_pos' a
  exact div_nonneg h1 (le_of_lt h2)

/-- Theorem 30: Surplus is bounded above: at most jointPayoff - 2 -/
theorem surplus_le_jp_minus_two (a b : I) :
    cooperationSurplus a b ≤ jointPayoff a b - 2 := by
  unfold cooperationSurplus jointPayoff
  linarith [rs_self_ge_one (I := I) a, rs_self_ge_one (I := I) b]

/-- Theorem 31: When surplus is non-negative, joint payoff is super-additive -/
theorem positive_surplus_super_additive (a b : I)
    (h : cooperationSurplus a b ≥ 0) :
    jointPayoff a b ≥ resonanceStrength a a + resonanceStrength b b := by
  linarith [jointPayoff_from_parts (I := I) a b]

end IDT2.Cooperation
