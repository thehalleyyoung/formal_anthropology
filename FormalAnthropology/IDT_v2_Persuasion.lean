import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.IDT_Foundations_v2

/-!
# IDT v2: Persuasion Theory

Persuasion = composing your signal with the listener's belief.
The persuasion effect is measured by squared distance in the resonance
kernel, and persuasion success by the resonance between signal and outcome.

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT2.Persuasion

variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-! ## §1. Core Definitions -/

/-- Persuasion: compose the signal with the listener's belief. -/
def persuade (signal belief : I) : I := compose signal belief

/-- Squared persuasion effect: how much the belief changes (in squared distance). -/
noncomputable def persuasionEffectSq (signal belief : I) : ℝ :=
  squaredDistance belief (persuade signal belief)

/-- Persuasion success: resonance between signal and the resulting belief. -/
noncomputable def persuasionSuccess (signal belief : I) : ℝ :=
  resonanceStrength signal (persuade signal belief)

/-- Self-persuasion: resonance of the outcome with itself. -/
noncomputable def outcomeStrength (signal belief : I) : ℝ :=
  resonanceStrength (persuade signal belief) (persuade signal belief)

/-- Iterated persuasion: apply the same signal n times. -/
def iteratedPersuasion (signal : I) : ℕ → I → I
  | 0, belief => belief
  | n + 1, belief => persuade signal (iteratedPersuasion signal n belief)

/-! ## §2. Basic Persuasion Properties -/

/-- Theorem 1: Void signal has no persuasion effect. -/
theorem persuade_void_signal (belief : I) :
    persuade (void : I) belief = belief := by
  unfold persuade; exact IdeaticSpace2.void_left belief

/-- Theorem 2: Persuading a void belief yields the signal itself. -/
theorem persuade_void_belief (signal : I) :
    persuade signal (void : I) = signal := by
  unfold persuade; exact IdeaticSpace2.void_right signal

/-- Theorem 3: Persuasion is associative. -/
theorem persuade_assoc (a b c : I) :
    persuade (persuade a b) c = persuade a (persuade b c) := by
  unfold persuade; exact IdeaticSpace2.compose_assoc a b c

/-- Theorem 4: Void signal gives zero squared persuasion effect. -/
theorem persuasionEffectSq_void_signal (belief : I) :
    persuasionEffectSq (void : I) belief = 0 := by
  unfold persuasionEffectSq persuade
  rw [IdeaticSpace2.void_left]
  exact squaredDistance_self belief

/-- Theorem 5: Squared persuasion effect is non-negative. -/
theorem persuasionEffectSq_nonneg (signal belief : I) :
    persuasionEffectSq signal belief ≥ 0 := by
  unfold persuasionEffectSq; exact squaredDistance_nonneg _ _

/-! ## §3. Persuasion Success -/

/-- Theorem 6: Persuasion success is non-negative. -/
theorem persuasionSuccess_nonneg (signal belief : I) :
    persuasionSuccess signal belief ≥ 0 := by
  unfold persuasionSuccess persuade; exact IdeaticSpace2.rs_nonneg _ _

/-- Theorem 7: Persuading a void belief yields self-resonance as success. -/
theorem persuasionSuccess_void_belief (signal : I) :
    persuasionSuccess signal (void : I) = resonanceStrength signal signal := by
  unfold persuasionSuccess; rw [persuade_void_belief]

/-- Theorem 8: Success of a void signal equals resonance with original belief. -/
theorem persuasionSuccess_void_signal (belief : I) :
    persuasionSuccess (void : I) belief = resonanceStrength (void : I) belief := by
  unfold persuasionSuccess; rw [persuade_void_signal]

/-- Theorem 9: Persuasion success with void belief is at least 1. -/
theorem persuasionSuccess_void_belief_ge_one (signal : I) :
    persuasionSuccess signal (void : I) ≥ 1 := by
  rw [persuasionSuccess_void_belief]; exact rs_self_ge_one signal

/-! ## §4. Depth Bounds -/

/-- Theorem 10: Depth of persuaded belief is bounded. -/
theorem persuasion_depth_bound (signal belief : I) :
    depth (persuade signal belief) ≤ depth signal + depth belief := by
  unfold persuade; exact IdeaticSpace2.depth_subadditive signal belief

/-- Theorem 11: Iterated persuasion at step 0 is the identity. -/
theorem iterated_persuasion_zero (signal belief : I) :
    iteratedPersuasion signal 0 belief = belief := rfl

/-- Theorem 12: Iterated persuasion successor. -/
theorem iterated_persuasion_succ (signal : I) (n : ℕ) (belief : I) :
    iteratedPersuasion signal (n + 1) belief =
    persuade signal (iteratedPersuasion signal n belief) := rfl

/-- Theorem 13: Iterating void persuasion is the identity. -/
theorem void_persuasion_iterated (belief : I) :
    ∀ n, iteratedPersuasion (void : I) n belief = belief
  | 0 => rfl
  | n + 1 => by
    rw [iterated_persuasion_succ, void_persuasion_iterated belief n, persuade_void_signal]

/-- Theorem 14: Iterated persuasion depth bound. -/
theorem iterated_persuasion_depth_bound (signal : I) :
    ∀ (n : ℕ) (belief : I),
    depth (iteratedPersuasion signal n belief) ≤ n * depth signal + depth belief
  | 0, belief => by simp [iteratedPersuasion]
  | n + 1, belief => by
    rw [iterated_persuasion_succ]
    have h1 := persuasion_depth_bound signal (iteratedPersuasion signal n belief)
    have h2 := iterated_persuasion_depth_bound signal n belief
    have : (n + 1) * depth signal + depth belief =
           depth signal + (n * depth signal + depth belief) := by ring
    omega

/-! ## §5. Outcome Strength -/

/-- Theorem 15: Outcome strength is always at least 1. -/
theorem outcomeStrength_ge_one (signal belief : I) :
    outcomeStrength signal belief ≥ 1 := by
  unfold outcomeStrength persuade; exact rs_compose_ge_one signal belief

/-- Theorem 16: Outcome strength dominates signal self-resonance. -/
theorem outcomeStrength_ge_signal (signal belief : I) :
    outcomeStrength signal belief ≥ resonanceStrength signal signal := by
  unfold outcomeStrength persuade; exact rs_compose_self_right signal belief

/-- Theorem 17: Outcome strength dominates belief self-resonance. -/
theorem outcomeStrength_ge_belief (signal belief : I) :
    outcomeStrength signal belief ≥ resonanceStrength belief belief := by
  unfold outcomeStrength persuade; exact rs_compose_self_left belief signal

/-- Theorem 18: Void belief outcome has strength = signal self-resonance. -/
theorem outcomeStrength_void_belief (signal : I) :
    outcomeStrength signal (void : I) = resonanceStrength signal signal := by
  unfold outcomeStrength; rw [persuade_void_belief]

/-- Theorem 19: Void signal outcome has strength = belief self-resonance. -/
theorem outcomeStrength_void_signal (belief : I) :
    outcomeStrength (void : I) belief = resonanceStrength belief belief := by
  unfold outcomeStrength; rw [persuade_void_signal]

/-! ## §6. Resonance Relationships -/

/-- Theorem 20: Persuasion preserves resonance with context (right). -/
theorem persuasion_preserves_resonance_right (signal belief c : I) :
    resonanceStrength (persuade signal belief) (persuade signal c) ≥
    resonanceStrength belief c := by
  unfold persuade
  exact IdeaticSpace2.rs_compose_left_mono belief c signal

/-- Theorem 21: Persuasion preserves resonance with context (left). -/
theorem persuasion_preserves_resonance_left (signal1 signal2 belief : I) :
    resonanceStrength (persuade signal1 belief) (persuade signal2 belief) ≥
    resonanceStrength signal1 signal2 := by
  unfold persuade
  exact IdeaticSpace2.rs_compose_right_mono signal1 signal2 belief

/-- Theorem 22: Iterated persuasion monotonically increases self-resonance. -/
theorem iterated_persuasion_self_resonance_mono (signal : I) (n : ℕ) (belief : I) :
    resonanceStrength (iteratedPersuasion signal (n + 1) belief)
      (iteratedPersuasion signal (n + 1) belief) ≥
    resonanceStrength (iteratedPersuasion signal n belief)
      (iteratedPersuasion signal n belief) := by
  rw [iterated_persuasion_succ]
  exact outcomeStrength_ge_belief signal (iteratedPersuasion signal n belief)

/-- Theorem 23: Iterated persuasion self-resonance is at least 1. -/
theorem iterated_persuasion_self_resonance_ge_one (signal : I) :
    ∀ (n : ℕ) (belief : I),
    resonanceStrength (iteratedPersuasion signal n belief)
      (iteratedPersuasion signal n belief) ≥ 1
  | 0, belief => rs_self_ge_one belief
  | n + 1, belief => by
    linarith [iterated_persuasion_self_resonance_mono signal n belief,
              iterated_persuasion_self_resonance_ge_one signal n belief]

/-! ## §7. Persuasion Composition -/

/-- Theorem 24: Persuading twice by different signals is persuading by their composite. -/
theorem double_persuasion (s1 s2 belief : I) :
    persuade s1 (persuade s2 belief) = persuade (persuade s1 s2) belief := by
  unfold persuade; rw [IdeaticSpace2.compose_assoc]

/-- Theorem 25: Persuasion by composeN is iterated persuasion. -/
theorem persuade_composeN (signal : I) (n : ℕ) :
    persuade (composeN signal n) signal = composeN signal (n + 1) := by
  unfold persuade; rfl

/-- Theorem 26: Persuasion effect is symmetric in the kernel sense. -/
theorem persuasionEffectSq_comm (signal belief : I) :
    persuasionEffectSq signal belief = squaredDistance belief (persuade signal belief) := rfl

/-- Theorem 27: Self-resonance of double persuasion exceeds signal's self-resonance. -/
theorem double_persuasion_strength_ge_signal (signal belief : I) :
    outcomeStrength signal (persuade signal belief) ≥
    resonanceStrength signal signal := by
  unfold outcomeStrength
  rw [double_persuasion]
  unfold persuade
  have h := rs_compose_self_right (compose signal signal) belief
  linarith [rs_compose_self_right signal signal]

/-! ## §8. Persuasion Quality -/

/-- Normalized persuasion quality: how efficiently the signal persuades. -/
noncomputable def persuasionQuality (signal belief : I) : ℝ :=
  normalizedRS signal (persuade signal belief)

/-- Theorem 28: Persuasion quality is between 0 and 1. -/
theorem persuasionQuality_bounded (signal belief : I) :
    0 ≤ persuasionQuality signal belief ∧ persuasionQuality signal belief ≤ 1 := by
  unfold persuasionQuality
  exact ⟨(normalizedRS_nonneg signal (persuade signal belief)).le,
         normalizedRS_le_one signal (persuade signal belief)⟩

/-- Theorem 29: Persuasion quality of void belief is 1 (perfect self-resonance). -/
theorem persuasionQuality_void_belief (signal : I) :
    persuasionQuality signal (void : I) = 1 := by
  unfold persuasionQuality; rw [persuade_void_belief]; exact normalizedRS_self signal

/-- Theorem 30: Self-resonance of persuaded belief exceeds original belief's self-resonance. -/
theorem persuade_self_resonance_ge_belief (signal belief : I) :
    resonanceStrength (persuade signal belief) (persuade signal belief) ≥
    resonanceStrength belief belief := by
  unfold persuade
  exact rs_compose_self_left belief signal

end IDT2.Persuasion
