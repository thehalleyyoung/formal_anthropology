import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.IDT_Foundations_v2

/-!
# IDT v2: Narrative Theory

Stories as trajectories through meaning space. A narrative is a sequence of
episodes (ideas). The "story so far" at each point is the fold-composition
of all episodes. Coherence measures consecutive resonance; narrative weight
measures the self-resonance (semantic mass) of the full composed story.

Key results:
- Narrative weight is monotonically non-decreasing (adding episodes never
  reduces meaning)
- Narrative coherence is non-negative (all consecutive resonances are ≥ 0)
- Story composition is a monoid homomorphism (concatenation = composition)

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT2.Narrative

variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-! ## §1. Narrative Structure -/

/-- A narrative is a sequence of episodes (ideas). -/
abbrev Narrative' (I : Type*) := List I

/-- The cumulative story: right-fold compose of all episodes.
    storyAt [e₁, e₂, e₃] = compose e₁ (compose e₂ e₃). -/
def storyAt : List I → I
  | [] => (void : I)
  | a :: rest => compose a (storyAt rest)

/-- Consecutive resonance: sum of pairwise resonances between adjacent episodes.
    Measures how smoothly one episode flows into the next. -/
noncomputable def narrativeCoherence : List I → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => resonanceStrength a b + narrativeCoherence (b :: rest)

/-- Narrative weight: self-resonance of the full composed story.
    Measures the total semantic mass of the narrative. -/
noncomputable def narrativeWeight (n : List I) : ℝ :=
  resonanceStrength (storyAt n) (storyAt n)

/-- An episode advances the narrative if it contributes non-void content. -/
def advances (episode : I) : Prop := episode ≠ (void : I)

/-! ## §2. Story Composition -/

@[simp] theorem storyAt_nil : storyAt ([] : List I) = (void : I) := rfl

@[simp] theorem storyAt_cons (a : I) (rest : List I) :
    storyAt (a :: rest) = compose a (storyAt rest) := rfl

theorem storyAt_singleton (a : I) : storyAt [a] = a := by
  simp [IdeaticSpace2.void_right]

theorem storyAt_pair (a b : I) : storyAt [a, b] = compose a b := by
  simp [IdeaticSpace2.void_right]

/-- Inserting void at the front has no effect on the story. -/
theorem void_episode_identity (rest : List I) :
    storyAt ((void : I) :: rest) = storyAt rest := by
  simp [IdeaticSpace2.void_left]

/-- Story composition is a monoid homomorphism:
    the story of a concatenated narrative equals the composition of the two stories. -/
theorem narrative_is_monoid_fold (n1 n2 : List I) :
    storyAt (n1 ++ n2) = compose (storyAt (I := I) n1) (storyAt n2) := by
  induction n1 with
  | nil => simp [IdeaticSpace2.void_left]
  | cons a rest ih =>
    simp only [List.cons_append, storyAt_cons]
    rw [ih, ← IDT2.compose_assoc]

/-- Depth of the composed story is bounded by the sum of episode depths. -/
theorem storyAt_depth_bound (n : List I) :
    depth (storyAt n) ≤ (n.map depth).sum := by
  induction n with
  | nil => simp [depth_void']
  | cons a rest ih =>
    simp only [storyAt_cons, List.map_cons, List.sum_cons]
    have h := depth_subadditive' a (storyAt rest)
    omega

/-- Appending an empty narrative changes nothing. -/
theorem storyAt_append_nil (n : List I) :
    storyAt (n ++ []) = storyAt n := by
  simp

/-! ## §3. Coherence -/

@[simp] theorem narrativeCoherence_nil :
    narrativeCoherence ([] : List I) = 0 := rfl

@[simp] theorem narrativeCoherence_singleton (a : I) :
    narrativeCoherence [a] = 0 := rfl

theorem narrativeCoherence_cons (a b : I) (rest : List I) :
    narrativeCoherence (a :: b :: rest) =
    resonanceStrength a b + narrativeCoherence (b :: rest) := rfl

theorem narrativeCoherence_pair (a b : I) :
    narrativeCoherence [a, b] = resonanceStrength a b := by
  show resonanceStrength a b + (0 : ℝ) = resonanceStrength a b
  linarith

theorem narrativeCoherence_pair_nonneg (a b : I) :
    narrativeCoherence [a, b] ≥ 0 := by
  rw [narrativeCoherence_pair]
  exact IdeaticSpace2.rs_nonneg a b

/-- Every narrative has non-negative coherence because all pairwise resonances
    are non-negative. -/
theorem narrativeCoherence_nonneg (n : List I) :
    narrativeCoherence n ≥ 0 := by
  induction n with
  | nil => simp [narrativeCoherence]
  | cons a rest ih =>
    cases rest with
    | nil => simp [narrativeCoherence]
    | cons b rest' =>
      rw [narrativeCoherence_cons]
      linarith [IdeaticSpace2.rs_nonneg a b]

/-! ## §4. Narrative Weight and Arc -/

/-- The empty narrative has weight 1 (the void self-resonance). -/
theorem narrativeWeight_void :
    narrativeWeight ([] : List I) = 1 := by
  unfold narrativeWeight
  simp [rs_void_unit]

/-- Narrative weight is strictly positive. -/
theorem narrativeWeight_pos (n : List I) : narrativeWeight n > 0 := by
  unfold narrativeWeight; exact rs_self_pos' _

/-- Narrative weight is at least 1. -/
theorem narrativeWeight_ge_one (n : List I) : narrativeWeight n ≥ 1 := by
  unfold narrativeWeight; exact rs_self_ge_one _

/-- Singleton narrative weight equals self-resonance. -/
theorem narrativeWeight_singleton (a : I) :
    narrativeWeight [a] = resonanceStrength a a := by
  unfold narrativeWeight; rw [storyAt_singleton]

/-- **The narrative arc theorem**: adding an episode never decreases weight.
    Narratives accumulate meaning monotonically. -/
theorem narrativeWeight_monotone (a : I) (rest : List I) :
    narrativeWeight (a :: rest) ≥ narrativeWeight rest := by
  unfold narrativeWeight
  simp only [storyAt_cons]
  exact rs_compose_self_left (storyAt rest) a

/-- Weight of a concatenated narrative is at least the weight of the first part. -/
theorem narrativeWeight_append_ge_left (n1 n2 : List I) :
    narrativeWeight (n1 ++ n2) ≥ narrativeWeight n1 := by
  unfold narrativeWeight
  rw [narrative_is_monoid_fold]
  exact rs_compose_self_right (storyAt n1) (storyAt n2)

/-- Weight of a concatenated narrative is at least the weight of the second part. -/
theorem narrativeWeight_append_ge_right (n1 n2 : List I) :
    narrativeWeight (n1 ++ n2) ≥ narrativeWeight n2 := by
  unfold narrativeWeight
  rw [narrative_is_monoid_fold]
  exact rs_compose_self_left (storyAt n2) (storyAt n1)

/-- Pair narrative weight is the self-resonance of the composed pair. -/
theorem narrativeWeight_pair (a b : I) :
    narrativeWeight [a, b] = resonanceStrength (compose a b) (compose a b) := by
  unfold narrativeWeight; rw [storyAt_pair]

/-- Pair narrative weight is at least the singleton weight of the first episode. -/
theorem narrativeWeight_pair_ge_first (a b : I) :
    narrativeWeight [a, b] ≥ narrativeWeight [a] := by
  rw [narrativeWeight_pair, narrativeWeight_singleton]
  exact rs_compose_self_right a b

/-- Pair narrative weight is at least the singleton weight of the second episode. -/
theorem narrativeWeight_pair_ge_second (a b : I) :
    narrativeWeight [a, b] ≥ narrativeWeight [b] := by
  rw [narrativeWeight_pair, narrativeWeight_singleton]
  exact rs_compose_self_left b a

/-- A narrative of all void episodes composes to void. -/
theorem storyAt_void_list (n : ℕ) :
    storyAt (List.replicate n (void : I)) = (void : I) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show compose (void : I) (storyAt (List.replicate n (void : I))) = (void : I)
    rw [ih]; exact IdeaticSpace2.void_left _

/-- The coherence of a :: b :: rest is at least the resonance of the first pair. -/
theorem narrativeCoherence_ge_first_pair (a b : I) (rest : List I) :
    narrativeCoherence (a :: b :: rest) ≥ resonanceStrength a b := by
  rw [narrativeCoherence_cons]
  linarith [narrativeCoherence_nonneg (I := I) (b :: rest)]

/-- Void does not advance the narrative. -/
theorem void_not_advances : ¬ advances (I := I) (void : I) :=
  not_not.mpr rfl

end IDT2.Narrative
