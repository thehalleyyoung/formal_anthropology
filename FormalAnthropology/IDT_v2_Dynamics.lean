import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.IDT_Foundations_v2

/-!
# IDT v2: Dynamics and Evolution

Dynamics and evolution in the real-valued resonance framework.
Transmission, mutation, selection, and convergence interact
with the quantitative resonance structure.

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT2

/-! ## §1. Transmission Dynamics -/

section Transmission
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-- A transmission function: how ideas propagate through a medium -/
structure TransmissionFn (I : Type*) [IdeaticSpace2 I] where
  transmit : I → I
  transmit_void : transmit void = void

/-- Transmission fidelity: resonance between original and transmitted idea -/
noncomputable def transmissionFidelity (T : TransmissionFn I) (a : I) : ℝ :=
  resonanceStrength a (T.transmit a)

theorem transmissionFidelity_nonneg (T : TransmissionFn I) (a : I) :
    transmissionFidelity T a ≥ 0 := by
  unfold transmissionFidelity; exact IdeaticSpace2.rs_nonneg a _

/-- Fidelity of void transmission = 1 -/
theorem transmissionFidelity_void (T : TransmissionFn I) :
    transmissionFidelity T (void : I) = 1 := by
  unfold transmissionFidelity; rw [T.transmit_void]; exact IdeaticSpace2.rs_void_self

/-- A faithful transmission preserves ideas exactly -/
structure FaithfulTransmission (I : Type*) [IdeaticSpace2 I] extends TransmissionFn I where
  faithful : ∀ (a : I), transmit a = a

/-- Faithful transmission has perfect fidelity -/
theorem faithful_fidelity (T : FaithfulTransmission I) (a : I) :
    transmissionFidelity T.toTransmissionFn a = resonanceStrength a a := by
  unfold transmissionFidelity; rw [T.faithful]

/-- Faithful fidelity is at least 1 -/
theorem faithful_fidelity_ge_one (T : FaithfulTransmission I) (a : I) :
    transmissionFidelity T.toTransmissionFn a ≥ 1 := by
  rw [faithful_fidelity]; exact rs_self_ge_one a

/-- Transmission loss: drop in fidelity -/
noncomputable def transmissionLoss (T : TransmissionFn I) (a : I) : ℝ :=
  resonanceStrength a a - transmissionFidelity T a

/-- Faithful transmission has zero loss -/
theorem faithful_zero_loss (T : FaithfulTransmission I) (a : I) :
    transmissionLoss T.toTransmissionFn a = 0 := by
  unfold transmissionLoss; rw [faithful_fidelity]; linarith

/-- Compositional transmission preserves the compose structure -/
structure CompositionalTransmission (I : Type*) [IdeaticSpace2 I]
    extends TransmissionFn I where
  compositionality : ∀ (a b : I),
    transmit (compose a b) = compose (transmit a) (transmit b)

/-- Compositional transmission is faithful on void -/
theorem compositional_void (T : CompositionalTransmission I) :
    T.transmit (void : I) = (void : I) := T.transmit_void

end Transmission

/-! ## §2. Mutagenic Diffusion -/

section Mutagenic
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-- Mutagenic transmission: ideas mutate, depth may decrease -/
structure MutagenicTransmission (I : Type*) [IdeaticSpace2 I]
    extends TransmissionFn I where
  depth_decay : ∀ (a : I), depth (transmit a) ≤ depth a

theorem mutagenic_void (T : MutagenicTransmission I) :
    T.transmit (void : I) = (void : I) := T.transmit_void

theorem mutagenic_depth_le (T : MutagenicTransmission I) (a : I) :
    depth (T.transmit a) ≤ depth a := T.depth_decay a

/-- Mutagenic fidelity of void is perfect -/
theorem mutagenic_void_fidelity (T : MutagenicTransmission I) :
    transmissionFidelity T.toTransmissionFn (void : I) = 1 :=
  transmissionFidelity_void T.toTransmissionFn

end Mutagenic

/-! ## §3. Selective Diffusion -/

section Selective
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-- Fitness of an idea in a context -/
noncomputable def fitness (context a : I) : ℝ := resonanceStrength context a

theorem fitness_nonneg (context a : I) : fitness context a ≥ 0 := by
  unfold fitness; exact IdeaticSpace2.rs_nonneg context a

theorem fitness_symm (a b : I) : fitness a b = fitness b a := by
  unfold fitness; exact IdeaticSpace2.rs_symm a b

theorem self_fitness_ge_one (a : I) : fitness a a ≥ 1 := rs_self_ge_one a

/-- Idea a is fitter than b in context c -/
def fitterThan (c a b : I) : Prop := fitness c a > fitness c b

theorem fitterThan_trans (c a b d : I) :
    fitterThan c a b → fitterThan c b d → fitterThan c a d := by
  unfold fitterThan; intro h1 h2; linarith

/-- Selection function: picks the fitter idea -/
noncomputable def selectFitter (context a b : I) : I :=
  if fitness context a ≥ fitness context b then a else b

/-- Selected idea is always one of the two candidates -/
theorem selectFitter_is_a_or_b (context a b : I) :
    selectFitter context a b = a ∨ selectFitter context a b = b := by
  unfold selectFitter
  by_cases h : fitness context a ≥ fitness context b
  · simp [h]
  · simp [h]

/-- Selective pressure: maximum fitness of pair -/
noncomputable def selectivePressure (context a b : I) : ℝ :=
  max (fitness context a) (fitness context b)

theorem selectivePressure_ge_left (context a b : I) :
    selectivePressure context a b ≥ fitness context a :=
  le_max_left _ _

theorem selectivePressure_ge_right (context a b : I) :
    selectivePressure context a b ≥ fitness context b :=
  le_max_right _ _

theorem selectivePressure_nonneg (context a b : I) :
    selectivePressure context a b ≥ 0 := by
  linarith [selectivePressure_ge_left (I := I) context a b,
            fitness_nonneg (I := I) context a]

end Selective

/-! ## §4. Convergence -/

section Convergence
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-- A sequence converges in self-resonance -/
def rsConverges (seq : ℕ → I) (limit : ℝ) : Prop :=
  ∀ (ε : ℝ), ε > 0 → ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N →
    |resonanceStrength (seq n) (seq n) - limit| < ε

/-- Constant sequences converge -/
theorem const_seq_converges (a : I) :
    rsConverges (fun _ => a) (resonanceStrength a a) := by
  intro ε hε; exact ⟨0, fun _ _ => by simp; exact hε⟩

/-- A sequence is resonance-bounded -/
def rsBounded (seq : ℕ → I) (B : ℝ) : Prop :=
  ∀ (n : ℕ), resonanceStrength (seq n) (seq n) ≤ B

theorem const_seq_bounded (a : I) :
    rsBounded (fun _ => a) (resonanceStrength a a) := fun _ => le_refl _

/-- Self-resonance is non-decreasing in a monotone sequence -/
def rsMonotone (seq : ℕ → I) : Prop :=
  ∀ (n : ℕ), resonanceStrength (seq (n + 1)) (seq (n + 1)) ≥
              resonanceStrength (seq n) (seq n)

/-- ComposeN sequence is monotone -/
theorem composeN_seq_monotone (a : I) :
    rsMonotone (fun n => composeN a n) := by
  intro n; exact rs_self_composeN_mono a n

/-- Monotone sequences are bounded below by initial value -/
theorem monotone_lower_bound (seq : ℕ → I) (hm : rsMonotone seq) (n : ℕ) :
    resonanceStrength (seq n) (seq n) ≥ resonanceStrength (seq 0) (seq 0) := by
  induction n with
  | zero => exact le_refl _
  | succ k ih => linarith [hm k]

/-- All elements in any sequence have self-resonance ≥ 1 -/
theorem monotone_seq_ge_one (seq : ℕ → I) (_ : rsMonotone seq) (n : ℕ) :
    resonanceStrength (seq n) (seq n) ≥ 1 := rs_self_ge_one _

end Convergence

/-! ## §5. Diffusion Networks -/

section Networks
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-- Total resonance energy in a network -/
noncomputable def networkEnergy (nodes : List I) : ℝ :=
  sumSelfResonance nodes

theorem networkEnergy_nonneg (nodes : List I) :
    networkEnergy nodes ≥ 0 := sumSelfResonance_nonneg nodes

theorem networkEnergy_singleton (a : I) :
    networkEnergy [a] = resonanceStrength a a :=
  sumSelfResonance_singleton a

theorem networkEnergy_per_node_ge_one (a : I) :
    networkEnergy [a] ≥ 1 := by
  rw [networkEnergy_singleton]; exact rs_self_ge_one a

end Networks

end IDT2
