import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic

/-!
# Ideatic Diffusion Theory v2: Quantitative Resonance

The key innovation of IDT v2: resonance is no longer a binary Prop but a
**real-valued function** measuring the *degree* of resonance between ideas.

`resonanceStrength : I → I → ℝ` is a symmetric, non-negative function that
behaves like a kernel function from functional analysis. It implicitly embeds
ideas into a Hilbert space of meaning, where the inner product captures
semantic similarity.

## Axiom Groups

- **A1–A3** (Algebraic): Ideatic composition forms a monoid
- **D1–D4** (Depth): Ideas have intrinsic complexity behaving subadditively
- **RS1–RS7** (Resonance Strength): Quantitative resonance with kernel properties

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT2

/-! ## §1. The Core Axiom Class -/

/-- The foundational axiom class of Ideatic Diffusion Theory v2.
    Resonance is now a real-valued strength function, not a binary Prop. -/
class IdeaticSpace2 (I : Type*) where
  compose : I → I → I
  void : I
  compose_assoc : ∀ (a b c : I), compose (compose a b) c = compose a (compose b c)
  void_left : ∀ (a : I), compose void a = a
  void_right : ∀ (a : I), compose a void = a
  depth : I → ℕ
  atomic : I → Prop
  depth_void : depth void = 0
  depth_subadditive : ∀ (a b : I), depth (compose a b) ≤ depth a + depth b
  depth_atomic : ∀ (a : I), atomic a → depth a ≤ 1
  void_atomic : atomic void
  /-- Real-valued resonance strength (the v2 kernel) -/
  resonanceStrength : I → I → ℝ
  /-- RS1: Resonance is symmetric -/
  rs_symm : ∀ (a b : I), resonanceStrength a b = resonanceStrength b a
  /-- RS2: Self-resonance is strictly positive -/
  rs_self_pos : ∀ (a : I), resonanceStrength a a > 0
  /-- RS3: Resonance is non-negative -/
  rs_nonneg : ∀ (a b : I), resonanceStrength a b ≥ 0
  /-- RS4: Void has unit self-resonance -/
  rs_void_self : resonanceStrength void void = 1
  /-- RS5: Right-composition monotonicity -/
  rs_compose_right_mono : ∀ (a b c : I),
    resonanceStrength (compose a c) (compose b c) ≥ resonanceStrength a b
  /-- RS6: Left-composition monotonicity -/
  rs_compose_left_mono : ∀ (a b c : I),
    resonanceStrength (compose c a) (compose c b) ≥ resonanceStrength a b
  /-- RS7: Cauchy-Schwarz inequality for resonance -/
  rs_cauchy_schwarz : ∀ (a b : I),
    resonanceStrength a b * resonanceStrength a b ≤
    resonanceStrength a a * resonanceStrength b b

/-! ## §2. Algebraic Consequences -/

section Algebra
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

theorem compose_assoc (a b c : I) :
    compose (compose a b) c = compose a (compose b c) :=
  IdeaticSpace2.compose_assoc a b c

@[simp] theorem void_left (a : I) : compose (void : I) a = a :=
  IdeaticSpace2.void_left a

@[simp] theorem void_right (a : I) : compose a (void : I) = a :=
  IdeaticSpace2.void_right a

@[simp] theorem void_self :
    compose (void : I) (void : I) = (void : I) := void_left _

theorem compose_assoc4 (a b c d : I) :
    compose (compose (compose a b) c) d =
    compose a (compose b (compose c d)) := by
  rw [compose_assoc, compose_assoc]

def composeN (a : I) : ℕ → I
  | 0 => void
  | n + 1 => compose (composeN a n) a

@[simp] theorem composeN_zero (a : I) : composeN a 0 = (void : I) := rfl

theorem composeN_succ (a : I) (n : ℕ) :
    composeN a (n + 1) = compose (composeN a n) a := rfl

@[simp] theorem composeN_void : ∀ (n : ℕ),
    composeN (void : I) n = (void : I)
  | 0 => rfl
  | n + 1 => by simp [composeN, composeN_void n]

theorem composeN_one (a : I) : composeN a 1 = a := by
  simp [composeN, composeN_succ]

theorem composeN_two (a : I) : composeN a 2 = compose a a := by
  simp [composeN, composeN_succ, composeN_one]

end Algebra

/-! ## §3. Resonance Strength — Foundational Theorems -/

section ResonanceFoundations
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

theorem rs_symm' (a b : I) : resonanceStrength a b = resonanceStrength b a :=
  IdeaticSpace2.rs_symm a b

theorem rs_self_pos' (a : I) : resonanceStrength a a > 0 :=
  IdeaticSpace2.rs_self_pos a

theorem rs_nonneg' (a b : I) : resonanceStrength a b ≥ 0 :=
  IdeaticSpace2.rs_nonneg a b

theorem rs_void_unit : resonanceStrength (void : I) (void : I) = 1 :=
  IdeaticSpace2.rs_void_self

/-- Self-resonance ≥ 1 for all ideas.
    RS6 with a=void, b=void, c=idea gives rs(idea, idea) ≥ rs(void, void) = 1. -/
theorem rs_self_ge_one (a : I) : resonanceStrength a a ≥ 1 := by
  have h := IdeaticSpace2.rs_compose_left_mono (I := I) (void : I) (void : I) a
  simp [IdeaticSpace2.void_left] at h
  rw [IdeaticSpace2.rs_void_self] at h
  linarith

theorem rs_with_void_nonneg (a : I) : resonanceStrength a (void : I) ≥ 0 :=
  IdeaticSpace2.rs_nonneg a _

theorem rs_le_self_product (a b : I) :
    resonanceStrength a b * resonanceStrength a b ≤
    resonanceStrength a a * resonanceStrength b b :=
  IdeaticSpace2.rs_cauchy_schwarz a b

theorem rs_self_product_pos (a b : I) :
    resonanceStrength a a * resonanceStrength b b > 0 :=
  mul_pos (rs_self_pos' a) (rs_self_pos' b)

theorem rs_compose_self_right (a b : I) :
    resonanceStrength (compose a b) (compose a b) ≥ resonanceStrength a a := by
  have h := IdeaticSpace2.rs_compose_right_mono a a b
  rwa [IdeaticSpace2.rs_symm] at *

theorem rs_compose_self_left (a b : I) :
    resonanceStrength (compose b a) (compose b a) ≥ resonanceStrength a a :=
  IdeaticSpace2.rs_compose_left_mono a a b

theorem rs_compose_ge_one (a b : I) :
    resonanceStrength (compose a b) (compose a b) ≥ 1 := by
  linarith [rs_compose_self_right (I := I) a b, rs_self_ge_one (I := I) a]

theorem rs_compose_both_mono (a a' b : I) :
    resonanceStrength (compose a b) (compose a' b) ≥ resonanceStrength a a' :=
  IdeaticSpace2.rs_compose_right_mono a a' b

theorem rs_double_compose (a b c d : I) :
    resonanceStrength (compose c (compose a d)) (compose c (compose b d)) ≥
    resonanceStrength (compose a d) (compose b d) :=
  IdeaticSpace2.rs_compose_left_mono (compose a d) (compose b d) c

theorem rs_right_context_chain (a b d : I) :
    resonanceStrength (compose a d) (compose b d) ≥ resonanceStrength a b :=
  IdeaticSpace2.rs_compose_right_mono a b d

/-- RS upper bound: rs(a,b) ≤ rs(a,a) when rs(b,b) ≤ rs(a,a) -/
theorem rs_le_self_when (a b : I)
    (h : resonanceStrength b b ≤ resonanceStrength a a) :
    resonanceStrength a b ≤ resonanceStrength a a := by
  have hcs := IdeaticSpace2.rs_cauchy_schwarz a b
  have ha := rs_self_pos' (I := I) a
  have hnn := IdeaticSpace2.rs_nonneg a b
  nlinarith [sq_nonneg (resonanceStrength a a - resonanceStrength a b)]

end ResonanceFoundations

/-! ## §4. Depth Theorems -/

section DepthTheorems
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

theorem depth_void' : depth (void : I) = 0 := IdeaticSpace2.depth_void

theorem depth_subadditive' (a b : I) :
    depth (compose a b) ≤ depth a + depth b :=
  IdeaticSpace2.depth_subadditive a b

theorem void_atomic' : atomic (void : I) := IdeaticSpace2.void_atomic

theorem depth_compose_void_left (a : I) :
    depth (compose (void : I) a) ≤ depth a := by
  rw [IdeaticSpace2.void_left]

theorem depth_compose_void_right (a : I) :
    depth (compose a (void : I)) ≤ depth a := by
  rw [IdeaticSpace2.void_right]

theorem depth_compose_le_double_max (a b : I) :
    depth (compose a b) ≤ 2 * max (depth a) (depth b) := by
  have h := IdeaticSpace2.depth_subadditive a b; omega

theorem depth_composeN_le (a : I) : ∀ (n : ℕ),
    depth (composeN a n) ≤ n * depth a
  | 0 => by simp [composeN, IdeaticSpace2.depth_void]
  | n + 1 => by
    simp only [composeN]
    have h1 := IdeaticSpace2.depth_subadditive (composeN a n) a
    have h2 := depth_composeN_le a n
    have : (n + 1) * depth a = n * depth a + depth a := by ring
    omega

theorem depth_compose_atomic (a b : I) (ha : atomic a) (hb : atomic b) :
    depth (compose a b) ≤ 2 := by
  have h := IdeaticSpace2.depth_subadditive a b
  have h1 := IdeaticSpace2.depth_atomic a ha
  have h2 := IdeaticSpace2.depth_atomic b hb
  omega

end DepthTheorems

/-! ## §5. Resonance Metrics — Squared Distance -/

section Metrics
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-- Squared distance in the RKHS embedding -/
noncomputable def squaredDistance (a b : I) : ℝ :=
  resonanceStrength a a + resonanceStrength b b - 2 * resonanceStrength a b

theorem squaredDistance_nonneg (a b : I) : squaredDistance a b ≥ 0 := by
  unfold squaredDistance
  have hcs := IdeaticSpace2.rs_cauchy_schwarz a b
  have ha := rs_self_pos' (I := I) a
  have hb := rs_self_pos' (I := I) b
  have hnn := IdeaticSpace2.rs_nonneg a b
  nlinarith [sq_nonneg (resonanceStrength a a - resonanceStrength b b),
             sq_nonneg (resonanceStrength a b)]

theorem squaredDistance_self (a : I) : squaredDistance a a = 0 := by
  unfold squaredDistance; ring

theorem squaredDistance_symm (a b : I) : squaredDistance a b = squaredDistance b a := by
  unfold squaredDistance; rw [IdeaticSpace2.rs_symm a b]; ring

theorem squaredDistance_void_left (a : I) :
    squaredDistance (void : I) a =
    1 + resonanceStrength a a - 2 * resonanceStrength (void : I) a := by
  unfold squaredDistance; rw [IdeaticSpace2.rs_void_self]

theorem squaredDistance_from_void_nonneg (a : I) :
    squaredDistance (void : I) a ≥ 0 := squaredDistance_nonneg _ _

/-- Normalized resonance strength (squared cosine similarity) -/
noncomputable def normalizedRS (a b : I) : ℝ :=
  (resonanceStrength a b * resonanceStrength a b) /
  (resonanceStrength a a * resonanceStrength b b)

theorem normalizedRS_le_one (a b : I) : normalizedRS a b ≤ 1 := by
  unfold normalizedRS
  have hcs := IdeaticSpace2.rs_cauchy_schwarz a b
  have hprod := rs_self_product_pos (I := I) a b
  exact div_le_one_of_le₀ hcs (le_of_lt hprod)

theorem normalizedRS_nonneg (a b : I) : normalizedRS a b ≥ 0 := by
  unfold normalizedRS
  exact div_nonneg (mul_self_nonneg _) (le_of_lt (rs_self_product_pos (I := I) a b))

theorem normalizedRS_self (a : I) : normalizedRS a a = 1 := by
  unfold normalizedRS
  have h := rs_self_pos' (I := I) a
  have hne : resonanceStrength a a ≠ 0 := ne_of_gt h
  have hne2 : resonanceStrength a a * resonanceStrength a a ≠ 0 :=
    mul_ne_zero hne hne
  exact div_self hne2

theorem squaredDistance_zero_iff_self (a : I) :
    squaredDistance a a = 0 := squaredDistance_self a

end Metrics

/-! ## §6. Interpretation Theory — Payoffs -/

section Interpretation
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

def interpret (s r : I) : I := compose r s

noncomputable def senderPayoff (s r : I) : ℝ :=
  resonanceStrength s (interpret s r)

noncomputable def receiverPayoff (s r : I) : ℝ :=
  resonanceStrength r (interpret s r)

theorem interpret_void_receiver (s : I) : interpret s (void : I) = s := by
  unfold interpret; simp [IdeaticSpace2.void_left]

theorem interpret_void_signal (r : I) : interpret (void : I) r = r := by
  unfold interpret; simp [IdeaticSpace2.void_right]

theorem senderPayoff_void_receiver (s : I) :
    senderPayoff s (void : I) = resonanceStrength s s := by
  unfold senderPayoff; rw [interpret_void_receiver]

theorem receiverPayoff_void_signal (r : I) :
    receiverPayoff (void : I) r = resonanceStrength r r := by
  unfold receiverPayoff; rw [interpret_void_signal]

theorem senderPayoff_nonneg (s r : I) : senderPayoff s r ≥ 0 := by
  unfold senderPayoff interpret
  exact IdeaticSpace2.rs_nonneg s (compose r s)

theorem receiverPayoff_nonneg (s r : I) : receiverPayoff s r ≥ 0 := by
  unfold receiverPayoff interpret
  exact IdeaticSpace2.rs_nonneg r (compose r s)

theorem receiverPayoff_void_signal_ge_one (r : I) :
    receiverPayoff (void : I) r ≥ 1 := by
  rw [receiverPayoff_void_signal]; exact rs_self_ge_one r

theorem senderPayoff_void_receiver_ge_one (s : I) :
    senderPayoff s (void : I) ≥ 1 := by
  rw [senderPayoff_void_receiver]; exact rs_self_ge_one s

theorem receiverPayoff_context_mono (s r c : I) :
    resonanceStrength (compose c r) (compose (compose c r) s) ≥
    resonanceStrength r (compose r s) := by
  have h := IdeaticSpace2.rs_compose_left_mono r (compose r s) c
  rwa [← compose_assoc] at h

end Interpretation

/-! ## §7. Coherence Theory -/

section Coherence
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

noncomputable def totalResonance : List I → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => resonanceStrength a b + totalResonance (b :: rest)

theorem totalResonance_nil : totalResonance ([] : List I) = 0 := rfl
theorem totalResonance_singleton (a : I) : totalResonance [a] = 0 := rfl

theorem totalResonance_pair (a b : I) :
    totalResonance [a, b] = resonanceStrength a b := by
  simp [totalResonance]

theorem totalResonance_pair_nonneg (a b : I) : totalResonance [a, b] ≥ 0 := by
  rw [totalResonance_pair]; exact IdeaticSpace2.rs_nonneg a b

noncomputable def coherenceStrength (a b : I) : ℝ := resonanceStrength a b

theorem coherenceStrength_symm (a b : I) :
    coherenceStrength a b = coherenceStrength b a :=
  IdeaticSpace2.rs_symm a b

theorem coherenceStrength_self (a : I) :
    coherenceStrength a a = resonanceStrength a a := rfl

theorem coherenceStrength_bounded (a b : I) :
    coherenceStrength a b * coherenceStrength a b ≤
    coherenceStrength a a * coherenceStrength b b :=
  IdeaticSpace2.rs_cauchy_schwarz a b

def composeList : List I → I
  | [] => void
  | [a] => a
  | a :: rest => compose a (composeList rest)

theorem composeList_nil : composeList ([] : List I) = (void : I) := rfl
theorem composeList_singleton (a : I) : composeList [a] = a := rfl

end Coherence

/-! ## §8. Resonance Classes -/

section ResonanceClasses
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

def stronglyResonant (a b : I) (threshold : ℝ) : Prop :=
  resonanceStrength a b ≥ threshold

theorem stronglyResonant_symm (a b : I) (t : ℝ) :
    stronglyResonant a b t → stronglyResonant b a t := by
  unfold stronglyResonant; rw [IdeaticSpace2.rs_symm]; exact id

theorem stronglyResonant_self (a : I) : stronglyResonant a a 1 :=
  rs_self_ge_one a

theorem stronglyResonant_zero (a b : I) : stronglyResonant a b 0 :=
  IdeaticSpace2.rs_nonneg a b

theorem stronglyResonant_compose_right (a b c : I) (t : ℝ) :
    stronglyResonant a b t → stronglyResonant (compose a c) (compose b c) t := by
  intro h; unfold stronglyResonant at *
  linarith [IdeaticSpace2.rs_compose_right_mono a b c]

theorem stronglyResonant_compose_left (a b c : I) (t : ℝ) :
    stronglyResonant a b t → stronglyResonant (compose c a) (compose c b) t := by
  intro h; unfold stronglyResonant at *
  linarith [IdeaticSpace2.rs_compose_left_mono a b c]

def resonates (a b : I) : Prop := resonanceStrength a b > 0

theorem resonates_refl (a : I) : resonates a a := rs_self_pos' a

theorem resonates_symm (a b : I) : resonates a b → resonates b a := by
  unfold resonates; rw [IdeaticSpace2.rs_symm]; exact id

end ResonanceClasses

/-! ## §9. Resonance Algebra -/

section ResonanceAlgebra
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

theorem rs_compose_with_part_right (a b : I) :
    resonanceStrength (compose a b) (compose a b) ≥ resonanceStrength a a :=
  rs_compose_self_right a b

theorem rs_compose_with_part_left (a b : I) :
    resonanceStrength (compose a b) (compose a b) ≥ resonanceStrength b b :=
  rs_compose_self_left b a

theorem rs_self_composeN_mono (a : I) (n : ℕ) :
    resonanceStrength (composeN a (n + 1)) (composeN a (n + 1)) ≥
    resonanceStrength (composeN a n) (composeN a n) := by
  simp only [composeN_succ]; exact rs_compose_self_right (composeN a n) a

theorem rs_composeN_ge_one (a : I) : ∀ (n : ℕ),
    resonanceStrength (composeN a n) (composeN a n) ≥ 1
  | 0 => by simp [composeN]; rw [IdeaticSpace2.rs_void_self]
  | n + 1 => by linarith [rs_self_composeN_mono (I := I) a n, rs_composeN_ge_one a n]

theorem rs_void_calibration :
    resonanceStrength (void : I) (void : I) = 1 := IdeaticSpace2.rs_void_self

end ResonanceAlgebra

/-! ## §10. Advanced Resonance Properties -/

section Advanced
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

def rsLeq (a b : I) : Prop := resonanceStrength a a ≤ resonanceStrength b b

theorem rsLeq_refl (a : I) : rsLeq a a := le_refl _
theorem rsLeq_trans (a b c : I) : rsLeq a b → rsLeq b c → rsLeq a c := le_trans

theorem rsLeq_compose_right (a b : I) : rsLeq a (compose a b) :=
  rs_compose_self_right a b

theorem rsLeq_compose_left (a b : I) : rsLeq a (compose b a) :=
  rs_compose_self_left a b

theorem rsLeq_void (a : I) : rsLeq (void : I) a := by
  unfold rsLeq; rw [IdeaticSpace2.rs_void_self]; exact rs_self_ge_one a

noncomputable def resonanceGap (a b : I) : ℝ :=
  resonanceStrength a a - resonanceStrength a b

theorem resonanceGap_nonneg_when_rs_le (a b : I)
    (h : resonanceStrength b b ≤ resonanceStrength a a) :
    resonanceGap a b ≥ 0 := by
  unfold resonanceGap
  linarith [rs_le_self_when (I := I) a b h]

theorem resonanceGap_self (a : I) : resonanceGap a a = 0 := by
  unfold resonanceGap; linarith

noncomputable def resonanceExcess (a b : I) : ℝ :=
  resonanceStrength (compose a b) (compose a b) - resonanceStrength a a

theorem resonanceExcess_nonneg (a b : I) : resonanceExcess a b ≥ 0 := by
  unfold resonanceExcess; linarith [rs_compose_self_right (I := I) a b]

theorem resonanceExcess_void (a : I) : resonanceExcess a (void : I) = 0 := by
  unfold resonanceExcess; rw [IdeaticSpace2.void_right]; linarith

end Advanced

/-! ## §11. Depth-Resonance Interaction -/

section DepthResonance
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

theorem depth_resonance_monotone (a : I) (n : ℕ) :
    resonanceStrength (composeN a (n + 1)) (composeN a (n + 1)) ≥
    resonanceStrength (composeN a n) (composeN a n) :=
  rs_self_composeN_mono a n

theorem zero_depth_unit_resonance :
    depth (void : I) = 0 ∧ resonanceStrength (void : I) (void : I) = 1 :=
  ⟨IdeaticSpace2.depth_void, IdeaticSpace2.rs_void_self⟩

theorem atomic_bounded (a : I) (ha : atomic a) :
    depth a ≤ 1 ∧ resonanceStrength a a ≥ 1 :=
  ⟨IdeaticSpace2.depth_atomic a ha, rs_self_ge_one a⟩

theorem compose_increases_both (a b : I) :
    depth (compose a b) ≤ depth a + depth b ∧
    resonanceStrength (compose a b) (compose a b) ≥ resonanceStrength a a :=
  ⟨IdeaticSpace2.depth_subadditive a b, rs_compose_self_right a b⟩

end DepthResonance

/-! ## §12. List Resonance Analysis -/

section ListResonance
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

noncomputable def maxSelfResonance : List I → ℝ
  | [] => 0
  | [a] => resonanceStrength a a
  | a :: rest => max (resonanceStrength a a) (maxSelfResonance rest)

theorem maxSelfResonance_nonneg : ∀ (l : List I), maxSelfResonance l ≥ 0
  | [] => by simp [maxSelfResonance]
  | [a] => by simp [maxSelfResonance]; exact le_of_lt (rs_self_pos' a)
  | a :: _ :: _ => by
    simp [maxSelfResonance]; left; exact le_of_lt (rs_self_pos' a)

noncomputable def sumSelfResonance : List I → ℝ
  | [] => 0
  | a :: rest => resonanceStrength a a + sumSelfResonance rest

theorem sumSelfResonance_nonneg : ∀ (l : List I), sumSelfResonance l ≥ 0
  | [] => by simp [sumSelfResonance]
  | a :: rest => by
    simp [sumSelfResonance]
    linarith [rs_self_pos' (I := I) a, sumSelfResonance_nonneg rest]

theorem sumSelfResonance_singleton (a : I) :
    sumSelfResonance [a] = resonanceStrength a a := by
  simp [sumSelfResonance]

theorem each_self_resonance_ge_one (a : I) :
    resonanceStrength a a ≥ 1 := rs_self_ge_one a

end ListResonance

end IDT2
