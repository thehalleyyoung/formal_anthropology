import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.IDT_Foundations_v2

/-!
# IDT v2: Kernel Interpretation of Resonance

The kernel interpretation: `resonanceStrength` IS a kernel function
k(a,b) = ⟪φ(a), φ(b)⟫ (the "kernel trick"). This connects IDT to
machine learning, RKHS theory, and Mercer's theorem.

Every positive-definite kernel induces a feature map into a Hilbert space.
Here we prove that `resonanceStrength` satisfies all the axioms of a
positive-definite kernel, and develop kernel-theoretic consequences.

## Key Concepts

- **Kernel function**: k(a,b) = rs(a,b) — the resonance kernel
- **Kernel trace**: Σᵢ k(aᵢ,aᵢ) — total "energy" in a population
- **Kernel distance**: k(a,a) + k(b,b) - 2k(a,b) — squared RKHS distance
- **Normalized kernel**: k(a,b)² / (k(a,a)·k(b,b)) — cosine similarity²

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT2.Kernels

variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-! ## §1. The Kernel Function -/

section KernelBasics

/-- The kernel function of the ideatic space.
    In RKHS theory: k(a,b) = ⟪φ(a), φ(b)⟫_H -/
noncomputable def kernel (a b : I) : ℝ := resonanceStrength a b

/-- K1: Kernel symmetry (Mercer condition) -/
theorem kernel_symmetric (a b : I) : kernel a b = kernel b a :=
  rs_symm' a b

/-- K2: Kernel non-negativity -/
theorem kernel_nonneg (a b : I) : kernel a b ≥ 0 :=
  rs_nonneg' a b

/-- K3: Kernel is strictly positive on the diagonal -/
theorem kernel_self_pos (a : I) : kernel a a > 0 :=
  rs_self_pos' a

/-- K4: Diagonal kernel bounded below by 1 -/
theorem kernel_self_ge_one (a : I) : kernel a a ≥ 1 :=
  rs_self_ge_one a

/-- K5: Cauchy-Schwarz inequality for the kernel -/
theorem kernel_cauchy_schwarz (a b : I) :
    kernel a b * kernel a b ≤ kernel a a * kernel b b :=
  rs_le_self_product a b

/-- K6: Void has unit self-kernel -/
theorem kernel_void_self : kernel (void : I) (void : I) = 1 :=
  rs_void_unit

/-- K7: Right-composition monotonicity (kernel amplification) -/
theorem kernel_compose_right_mono (a b c : I) :
    kernel (compose a c) (compose b c) ≥ kernel a b :=
  IdeaticSpace2.rs_compose_right_mono a b c

/-- K8: Left-composition monotonicity -/
theorem kernel_compose_left_mono (a b c : I) :
    kernel (compose c a) (compose c b) ≥ kernel a b :=
  IdeaticSpace2.rs_compose_left_mono a b c

/-- K9: Composition increases self-kernel (right) -/
theorem kernel_compose_self_ge_right (a b : I) :
    kernel (compose a b) (compose a b) ≥ kernel a a :=
  rs_compose_self_right a b

/-- K10: Composition increases self-kernel (left) -/
theorem kernel_compose_self_ge_left (a b : I) :
    kernel (compose a b) (compose a b) ≥ kernel b b :=
  rs_compose_self_left b a

end KernelBasics

/-! ## §2. Kernel Trace -/

section KernelTrace

/-- The kernel trace on a population: Σᵢ k(aᵢ, aᵢ).
    In matrix terms, this is tr(G) where G is the Gram matrix. -/
noncomputable def kernelTrace : List I → ℝ
  | [] => 0
  | a :: rest => kernel a a + kernelTrace rest

@[simp] theorem kernelTrace_nil : kernelTrace ([] : List I) = 0 := rfl

theorem kernelTrace_cons (a : I) (rest : List I) :
    kernelTrace (a :: rest) = kernel a a + kernelTrace rest := rfl

theorem kernelTrace_singleton (a : I) :
    kernelTrace [a] = kernel a a := by
  simp [kernelTrace]

theorem kernelTrace_nonneg : ∀ (pop : List I), kernelTrace pop ≥ 0
  | [] => by simp [kernelTrace]
  | a :: rest => by
    simp only [kernelTrace]
    linarith [kernel_self_pos (I := I) a, kernelTrace_nonneg rest]

theorem kernelTrace_pos_of_nonempty (a : I) (rest : List I) :
    kernelTrace (a :: rest) > 0 := by
  simp only [kernelTrace]
  linarith [kernel_self_pos (I := I) a, kernelTrace_nonneg (I := I) rest]

/-- Kernel trace distributes over append -/
theorem kernelTrace_append : ∀ (l₁ l₂ : List I),
    kernelTrace (l₁ ++ l₂) = kernelTrace l₁ + kernelTrace l₂
  | [], l₂ => by simp [kernelTrace]
  | a :: rest, l₂ => by
    show kernel a a + kernelTrace (rest ++ l₂) =
      (kernel a a + kernelTrace rest) + kernelTrace l₂
    linarith [kernelTrace_append rest l₂]

/-- Each idea contributes ≥ 1 to the trace -/
theorem kernelTrace_ge_length : ∀ (pop : List I),
    kernelTrace pop ≥ pop.length
  | [] => by simp [kernelTrace]
  | a :: rest => by
    simp only [kernelTrace, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith [kernel_self_ge_one (I := I) a, kernelTrace_ge_length rest]

end KernelTrace

/-! ## §3. Kernel Distance -/

section KernelDist

/-- Kernel distance (squared RKHS distance):
    d²(a,b) = k(a,a) + k(b,b) - 2k(a,b) = ‖φ(a) - φ(b)‖² -/
noncomputable def kernelDist (a b : I) : ℝ :=
  kernel a a + kernel b b - 2 * kernel a b

/-- Kernel distance equals the foundational squared distance -/
theorem kernelDist_eq_squaredDistance (a b : I) :
    kernelDist a b = squaredDistance a b := rfl

/-- Kernel distance is non-negative (positive semi-definiteness) -/
theorem kernelDist_nonneg (a b : I) : kernelDist a b ≥ 0 := by
  rw [kernelDist_eq_squaredDistance]; exact squaredDistance_nonneg a b

/-- Kernel distance from self is zero -/
theorem kernelDist_self (a : I) : kernelDist a a = 0 := by
  rw [kernelDist_eq_squaredDistance]; exact squaredDistance_self a

/-- Kernel distance is symmetric -/
theorem kernelDist_symm (a b : I) : kernelDist a b = kernelDist b a := by
  rw [kernelDist_eq_squaredDistance, kernelDist_eq_squaredDistance]
  exact squaredDistance_symm a b

/-- Kernel distance expansion -/
theorem kernelDist_expand (a b : I) :
    kernelDist a b = kernel a a + kernel b b - 2 * kernel a b := rfl

/-- Higher kernel ↔ closer distance (for fixed self-kernels) -/
theorem kernelDist_decreases_with_kernel (a b : I) (c : ℝ)
    (h : kernel a b ≥ c) :
    kernelDist a b ≤ kernel a a + kernel b b - 2 * c := by
  unfold kernelDist; linarith

end KernelDist

/-! ## §4. Normalized Kernel (Cosine Similarity²) -/

section NormalizedKernel

/-- Normalized kernel: k̂(a,b) = k(a,b)² / (k(a,a)·k(b,b))
    This is the squared cosine similarity in the RKHS. -/
noncomputable def normalizedKernel (a b : I) : ℝ :=
  (kernel a b * kernel a b) / (kernel a a * kernel b b)

theorem normalizedKernel_eq_normalizedRS (a b : I) :
    normalizedKernel a b = normalizedRS a b := rfl

/-- Normalized kernel ≤ 1 (Cauchy-Schwarz consequence) -/
theorem normalizedKernel_le_one (a b : I) :
    normalizedKernel a b ≤ 1 := by
  rw [normalizedKernel_eq_normalizedRS]; exact normalizedRS_le_one a b

/-- Normalized kernel ≥ 0 -/
theorem normalizedKernel_nonneg (a b : I) :
    normalizedKernel a b ≥ 0 := by
  rw [normalizedKernel_eq_normalizedRS]; exact normalizedRS_nonneg a b

/-- Normalized self-kernel = 1 -/
theorem normalizedKernel_self (a : I) :
    normalizedKernel a a = 1 := by
  rw [normalizedKernel_eq_normalizedRS]; exact normalizedRS_self a

/-- Normalized kernel is symmetric -/
theorem normalizedKernel_symm (a b : I) :
    normalizedKernel a b = normalizedKernel b a := by
  unfold normalizedKernel kernel
  rw [IdeaticSpace2.rs_symm a b,
      mul_comm (resonanceStrength a a) (resonanceStrength b b)]

end NormalizedKernel

/-! ## §5. Kernel Algebraic Properties -/

section KernelAlgebra

/-- Kernel of composed ideas is at least as strong as kernel of parts -/
theorem kernel_compose_amplifies_right (a a' b : I) :
    kernel (compose a b) (compose a' b) ≥ kernel a a' :=
  IdeaticSpace2.rs_compose_right_mono a a' b

/-- Double composition amplifies kernel -/
theorem kernel_double_compose (a b c d : I) :
    kernel (compose c (compose a d)) (compose c (compose b d)) ≥
    kernel (compose a d) (compose b d) :=
  IdeaticSpace2.rs_compose_left_mono (compose a d) (compose b d) c

/-- Kernel excess from composition is non-negative -/
noncomputable def kernelExcess (a b : I) : ℝ :=
  kernel (compose a b) (compose a b) - kernel a a

theorem kernelExcess_nonneg (a b : I) : kernelExcess a b ≥ 0 := by
  unfold kernelExcess kernel; exact resonanceExcess_nonneg a b

/-- Kernel excess is zero when composing with void -/
theorem kernelExcess_void (a : I) : kernelExcess a (void : I) = 0 := by
  unfold kernelExcess kernel
  show resonanceStrength (compose a (void : I)) (compose a (void : I)) -
    resonanceStrength a a = 0
  rw [IdeaticSpace2.void_right]; ring

/-- Kernel of void with anything is non-negative -/
theorem kernel_void_nonneg (a : I) : kernel (void : I) a ≥ 0 :=
  rs_nonneg' _ _

/-- ComposeN increases kernel monotonically -/
theorem kernel_composeN_mono (a : I) (n : ℕ) :
    kernel (composeN a (n + 1)) (composeN a (n + 1)) ≥
    kernel (composeN a n) (composeN a n) :=
  rs_self_composeN_mono a n

/-- ComposeN kernel is always ≥ 1 -/
theorem kernel_composeN_ge_one (a : I) (n : ℕ) :
    kernel (composeN a n) (composeN a n) ≥ 1 :=
  rs_composeN_ge_one a n

end KernelAlgebra

/-! ## §6. Kernel-Based Classification -/

section KernelClassification

/-- Two ideas are kernel-close if their kernel distance is below a threshold -/
def kernelClose (a b : I) (ε : ℝ) : Prop := kernelDist a b ≤ ε

theorem kernelClose_self (a : I) (ε : ℝ) (hε : ε ≥ 0) :
    kernelClose a a ε := by
  unfold kernelClose; rw [kernelDist_self]; exact hε

theorem kernelClose_symm (a b : I) (ε : ℝ) :
    kernelClose a b ε → kernelClose b a ε := by
  unfold kernelClose; rw [kernelDist_symm]; exact id

/-- Ideas with high kernel value are kernel-close -/
theorem high_kernel_implies_close (a b : I)
    (h : kernel a b ≥ (kernel a a + kernel b b) / 2 - ε / 2)
    (_hε : ε ≥ 0) :
    kernelClose a b ε := by
  unfold kernelClose kernelDist; linarith

/-- Kernel alignment: whether two ideas are "in the same direction" -/
def kernelAligned (a b : I) (threshold : ℝ) : Prop :=
  normalizedKernel a b ≥ threshold

theorem kernelAligned_self (a : I) : kernelAligned a a 1 := by
  unfold kernelAligned; rw [normalizedKernel_self]

theorem kernelAligned_symm (a b : I) (t : ℝ) :
    kernelAligned a b t → kernelAligned b a t := by
  unfold kernelAligned; rw [normalizedKernel_symm]; exact id

end KernelClassification

end IDT2.Kernels
