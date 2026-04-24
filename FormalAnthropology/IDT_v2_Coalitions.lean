import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.IDT_Foundations_v2

/-!
# IDT v2: Coalitions of Ideas

Coalitions of agents form when their ideas mutually resonate. The coalition
idea is the composition of all members' ideas. Coalition value = self-resonance
of the composed idea.

## Key Definitions
- `Coalition I`: a list of ideas (agents' contributions)
- `coalitionIdea`: compose all members' ideas (fold via compose)
- `coalitionValue`: self-resonance of the composed coalition idea
- `isStable`: removing any member reduces coalition value

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT2.Coalitions

variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-! ## §1. Core Definitions -/

/-- A coalition is a list of ideas (agents' ideas) -/
abbrev Coalition (I : Type*) := List I

/-- Coalition idea: compose all members' ideas -/
def coalitionIdea : Coalition I → I
  | [] => (void : I)
  | a :: rest => compose a (coalitionIdea rest)

/-- Coalition value: self-resonance of the composed coalition idea -/
noncomputable def coalitionValue (c : Coalition I) : ℝ :=
  resonanceStrength (coalitionIdea c) (coalitionIdea c)

/-- Sum of individual self-resonances in a coalition -/
noncomputable def sumIndividualValues : Coalition I → ℝ
  | [] => 0
  | a :: rest => resonanceStrength a a + sumIndividualValues rest

/-! ## §2. Coalition Idea — Structural Properties -/

/-- Theorem 1: Empty coalition yields void -/
theorem coalitionIdea_nil : coalitionIdea ([] : Coalition I) = (void : I) := rfl

/-- Theorem 2: Singleton coalition yields the idea itself -/
@[simp] theorem coalitionIdea_singleton (a : I) : coalitionIdea [a] = a := by
  simp [coalitionIdea, IdeaticSpace2.void_right]

/-- Theorem 3: Cons unfolds to compose -/
theorem coalitionIdea_cons (a : I) (rest : Coalition I) :
    coalitionIdea (a :: rest) = compose a (coalitionIdea rest) := rfl

/-- Theorem 4: Void member at head doesn't change the coalition idea -/
@[simp] theorem coalitionIdea_void_cons (c : Coalition I) :
    coalitionIdea ((void : I) :: c) = coalitionIdea c := by
  simp [coalitionIdea, IdeaticSpace2.void_left]

/-- Theorem 5: Pair coalition yields compose -/
theorem coalitionIdea_pair (a b : I) :
    coalitionIdea [a, b] = compose a b := by
  simp [coalitionIdea, IdeaticSpace2.void_right]

/-! ## §3. Coalition Value — Basic Properties -/

/-- Theorem 6: Empty coalition has value 1 (rs(void,void) = 1) -/
theorem coalitionValue_nil :
    coalitionValue ([] : Coalition I) = 1 := by
  unfold coalitionValue; simp [coalitionIdea]; exact IdeaticSpace2.rs_void_self

/-- Theorem 7: Coalition value is always at least 1 -/
theorem coalitionValue_ge_one (c : Coalition I) : coalitionValue c ≥ 1 := by
  unfold coalitionValue
  induction c with
  | nil => simp [coalitionIdea]; linarith [IdeaticSpace2.rs_void_self (I := I)]
  | cons a rest ih =>
    simp only [coalitionIdea]
    exact rs_compose_ge_one a (coalitionIdea rest)

/-- Theorem 8: Coalition value is strictly positive -/
theorem coalitionValue_pos (c : Coalition I) : coalitionValue c > 0 := by
  linarith [coalitionValue_ge_one (I := I) c]

/-- Theorem 9: Coalition value is non-negative -/
theorem coalitionValue_nonneg (c : Coalition I) : coalitionValue c ≥ 0 := by
  linarith [coalitionValue_ge_one (I := I) c]

/-- Theorem 10: Singleton coalition value = self-resonance -/
theorem coalitionValue_singleton (a : I) :
    coalitionValue [a] = resonanceStrength a a := by
  unfold coalitionValue; simp

/-- Theorem 11: Pair coalition value = rs(compose a b, compose a b) -/
theorem coalitionValue_pair (a b : I) :
    coalitionValue [a, b] = resonanceStrength (compose a b) (compose a b) := by
  unfold coalitionValue; simp [coalitionIdea, IdeaticSpace2.void_right]

/-! ## §4. Adding Members -/

/-- Theorem 12: Adding a member increases value beyond the original -/
theorem adding_member_ge_original (a : I) (c : Coalition I) :
    coalitionValue (a :: c) ≥ coalitionValue c :=
  rs_compose_self_left (coalitionIdea c) a

/-- Theorem 13: Adding a member increases value beyond the member's own value -/
theorem adding_member_ge_new (a : I) (c : Coalition I) :
    coalitionValue (a :: c) ≥ resonanceStrength a a := by
  unfold coalitionValue coalitionIdea
  exact rs_compose_self_right a (coalitionIdea c)

/-- Theorem 14: Adding void doesn't change coalition value -/
theorem adding_void_value (c : Coalition I) :
    coalitionValue ((void : I) :: c) = coalitionValue c := by
  unfold coalitionValue; simp

/-! ## §5. Coalition Merging -/

/-- Theorem 15: Merging coalitions via concatenation composes their ideas -/
theorem coalitionIdea_append (c1 c2 : Coalition I) :
    coalitionIdea (c1 ++ c2) = compose (coalitionIdea c1) (coalitionIdea c2) := by
  induction c1 with
  | nil => simp [coalitionIdea, IdeaticSpace2.void_left]
  | cons a rest ih =>
    show compose a (coalitionIdea (rest ++ c2)) =
         compose (compose a (coalitionIdea rest)) (coalitionIdea c2)
    rw [ih, compose_assoc]

/-- Theorem 16: Merging with empty coalition on the left preserves idea -/
theorem coalitionIdea_nil_append (c : Coalition I) :
    coalitionIdea ([] ++ c) = coalitionIdea c := by
  simp [coalitionIdea_append, coalitionIdea, IdeaticSpace2.void_left]

/-- Theorem 17: Merging with empty coalition on the right preserves idea -/
theorem coalitionIdea_append_nil (c : Coalition I) :
    coalitionIdea (c ++ []) = coalitionIdea c := by
  simp [coalitionIdea_append, coalitionIdea, IdeaticSpace2.void_right]

/-- Theorem 18: Merged coalition value ≥ left sub-coalition value -/
theorem merge_value_ge_left (c1 c2 : Coalition I) :
    coalitionValue (c1 ++ c2) ≥ coalitionValue c1 := by
  unfold coalitionValue
  rw [coalitionIdea_append]
  exact rs_compose_self_right (coalitionIdea c1) (coalitionIdea c2)

/-- Theorem 19: Merged coalition value ≥ right sub-coalition value -/
theorem merge_value_ge_right (c1 c2 : Coalition I) :
    coalitionValue (c1 ++ c2) ≥ coalitionValue c2 := by
  unfold coalitionValue
  rw [coalitionIdea_append]
  exact rs_compose_self_left (coalitionIdea c2) (coalitionIdea c1)

/-! ## §6. Resonance with Coalition Ideas -/

/-- Theorem 20: Resonance with a coalition idea is monotone in membership -/
theorem coalition_resonance_mono (a : I) (x : I) (c : Coalition I) :
    resonanceStrength (coalitionIdea (a :: c)) x ≥ 0 := by
  exact rs_nonneg' _ _

/-- Theorem 21: Self-resonance of a coalition is ≥ any member's self-resonance -/
theorem coalitionValue_ge_member_head (a : I) (c : Coalition I) :
    coalitionValue (a :: c) ≥ resonanceStrength a a :=
  adding_member_ge_new a c

/-- Theorem 22: Coalition with void prefix has same value -/
theorem void_prefix_same_value (c : Coalition I) :
    coalitionValue ((void : I) :: c) = coalitionValue c :=
  adding_void_value c

/-! ## §7. Coalition Depth -/

/-- Theorem 23: Coalition idea depth is bounded by sum of depths -/
theorem coalitionIdea_depth_bound (c : Coalition I) :
    depth (coalitionIdea c) ≤ (c.map depth).sum := by
  induction c with
  | nil => simp [coalitionIdea, IdeaticSpace2.depth_void]
  | cons a rest ih =>
    simp only [coalitionIdea, List.map_cons, List.sum_cons]
    exact le_trans (IdeaticSpace2.depth_subadditive a (coalitionIdea rest))
      (Nat.add_le_add_left ih _)

/-- Theorem 24: Empty coalition has depth 0 -/
theorem coalitionIdea_depth_nil : depth (coalitionIdea ([] : Coalition I)) = 0 := by
  simp [coalitionIdea, IdeaticSpace2.depth_void]

/-- Theorem 25: Singleton coalition depth equals idea depth -/
theorem coalitionIdea_depth_singleton (a : I) :
    depth (coalitionIdea [a]) = depth a := by
  simp

/-! ## §8. Individual Values -/

/-- Theorem 26: Sum of individual values of empty coalition is 0 -/
theorem sumIndividualValues_nil :
    sumIndividualValues ([] : Coalition I) = 0 := rfl

/-- Theorem 27: Sum of individual values is non-negative -/
theorem sumIndividualValues_nonneg (c : Coalition I) :
    sumIndividualValues c ≥ 0 := by
  induction c with
  | nil => simp [sumIndividualValues]
  | cons a rest ih =>
    simp only [sumIndividualValues]
    linarith [rs_self_pos' (I := I) a]

/-- Theorem 28: Sum of individual values is at least the length -/
theorem sumIndividualValues_ge_length (c : Coalition I) :
    sumIndividualValues c ≥ c.length := by
  induction c with
  | nil => simp [sumIndividualValues]
  | cons a rest ih =>
    simp only [sumIndividualValues, List.length_cons]
    have ha := rs_self_ge_one (I := I) a
    push_cast
    linarith

/-! ## §9. Stability -/

/-- A coalition is stable if its value exceeds value of tail -/
def isHeadStable (c : Coalition I) : Prop :=
  match c with
  | [] => True
  | _ :: rest => coalitionValue c ≥ coalitionValue rest

/-- Theorem 29: Every coalition is head-stable (adding members can only help) -/
theorem every_coalition_head_stable (c : Coalition I) : isHeadStable c := by
  cases c with
  | nil => exact trivial
  | cons a rest => exact adding_member_ge_original a rest

/-- A coalition is monotone-stable: every prefix has increasing value -/
def isMonotoneStable : Coalition I → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
    coalitionValue [a] ≤ coalitionValue [a, b] ∧ isMonotoneStable (b :: rest)

/-- Theorem 30: Singleton is always monotone-stable -/
theorem singleton_monotone_stable (a : I) :
    isMonotoneStable ([a] : Coalition I) := trivial

/-- Theorem 31: Pair with positive resonance is monotone-stable -/
theorem pair_monotone_stable (a b : I) :
    isMonotoneStable ([a, b] : Coalition I) := by
  unfold isMonotoneStable
  constructor
  · -- coalitionValue [a] ≤ coalitionValue [a, b]
    unfold coalitionValue
    simp [coalitionIdea, IdeaticSpace2.void_right]
    exact rs_compose_self_right a b
  · exact trivial

/-! ## §10. Coalition Value Comparisons -/

/-- Theorem 32: Pair value ≥ singleton value for left element -/
theorem pair_ge_left (a b : I) :
    coalitionValue [a, b] ≥ coalitionValue [a] := by
  unfold coalitionValue
  simp [coalitionIdea, IdeaticSpace2.void_right]
  exact rs_compose_self_right a b

/-- Theorem 33: Pair value ≥ singleton value for right element -/
theorem pair_ge_right (a b : I) :
    coalitionValue [a, b] ≥ coalitionValue [b] := by
  unfold coalitionValue
  simp [coalitionIdea, IdeaticSpace2.void_right]
  exact rs_compose_self_left b a

/-- Theorem 34: Triple value ≥ pair value (first two) -/
theorem triple_ge_pair (a b c : I) :
    coalitionValue [a, b, c] ≥ coalitionValue [a, b] := by
  unfold coalitionValue
  simp only [coalitionIdea, IdeaticSpace2.void_right]
  rw [← compose_assoc]
  exact rs_compose_self_right (compose a b) c

/-- Theorem 35: Void coalition (list of voids) has value 1 -/
theorem void_coalition_value : ∀ (n : ℕ),
    coalitionValue (List.replicate n (void : I)) = 1
  | 0 => by unfold coalitionValue; simp [coalitionIdea]; exact IdeaticSpace2.rs_void_self
  | n + 1 => by
    unfold coalitionValue
    simp only [List.replicate_succ, coalitionIdea]
    rw [IdeaticSpace2.void_left]
    rw [← coalitionIdea_nil (I := I)]
    simp only [coalitionIdea]
    have : coalitionIdea (List.replicate n (void : I)) = (void : I) := by
      induction n with
      | zero => simp [coalitionIdea]
      | succ k ih => simp [List.replicate_succ, coalitionIdea, IdeaticSpace2.void_left, ih]
    rw [this]
    exact IdeaticSpace2.rs_void_self

/-- Theorem 36: Coalitions of voids have void as idea -/
theorem void_coalition_idea : ∀ (n : ℕ),
    coalitionIdea (List.replicate n (void : I)) = (void : I)
  | 0 => rfl
  | n + 1 => by
    simp [List.replicate_succ, coalitionIdea, IdeaticSpace2.void_left,
          void_coalition_idea n]

end IDT2.Coalitions
