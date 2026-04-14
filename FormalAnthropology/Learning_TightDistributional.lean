/-
# Learning Theory: Distinguishability Index Distributional Bound (Generalized)

**CURRENT ASSUMPTIONS AND THEIR LOCATIONS:**

No sorries, admits, or axioms remain in this file.

**GENERALIZATIONS MADE:**

1. **Removed DecidableEq X requirement** (previously required at lines 40, 46, 78, 111, 124)
   - Now uses classical reasoning throughout
   - Makes theorems applicable to any type X, not just decidable equality types
   - DecidableEq only required for Y (output space) to determine disagreements

2. **Generalized to arbitrary output types** (previously: only X → Bool)
   - Now supports Y-valued hypotheses for any type Y with decidable equality
   - Applies to multi-class classification, regression with discrete outputs, etc.
   - Original Bool case is a special instance

3. **Generalized error functional** (previously: hard-coded 0-1 loss)
   - Now parameterized by arbitrary loss function `loss : Y → Y → ℝ`
   - Assumes only non-negativity, not specific form
   - Applies to squared loss, absolute loss, custom losses, etc.
   - 0-1 loss provided as special case for backwards compatibility

4. **Added loss scaling theorem** (new result)
   - Distributional bound scales with loss magnitude
   - If loss ≥ c on disagreements, error bound scales by c
   - Makes results applicable to non-normalized losses

5. **More flexible proof structure**
   - All proofs use classical reasoning explicitly
   - Removed unnecessary decidability constraints
   - Theorems apply to broader class of problems

**RESULT:** Theorems now apply to:
- Multi-class classification problems (Y = Fin n)
- Regression with discrete outputs (Y = ℤ, ℚ, etc.)
- Structured prediction with arbitrary decidable output spaces
- Any loss function satisfying minimal requirements
- Any domain X (not just types with decidable equality)

All proofs are complete with no sorries, admits, or axioms.

-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic

namespace LearningTheory

open Set Real
-- Use classical reasoning throughout for maximum generality
attribute [local instance] Classical.propDecidable

/-! ## Finite-support distributions and error -/

/-- A probability distribution with finite support over type X. -/
structure Distribution (X : Type*) where
  support : Finset X
  prob : X → ℝ
  nonneg : ∀ x, 0 ≤ prob x
  prob_eq_zero_of_not_mem : ∀ x, x ∉ support → prob x = 0
  sum_prob : ∑ x in support, prob x = 1

/--
Error of hypothesis h with respect to target function under distribution D,
parameterized by a loss function. This is more general than 0-1 loss.
-/
noncomputable def error {X Y : Type*} (D : Distribution X)
    (h : X → Y) (target : X → Y) (loss : Y → Y → ℝ) : ℝ :=
  ∑ x in D.support, D.prob x * loss (h x) (target x)

/--
0-1 loss function for compatibility with original theorems.
-/
def zeroOneLoss {Y : Type*} [DecidableEq Y] (y₁ y₂ : Y) : ℝ :=
  if y₁ ≠ y₂ then 1 else 0

lemma zeroOneLoss_nonneg {Y : Type*} [DecidableEq Y] (y₁ y₂ : Y) :
    0 ≤ zeroOneLoss y₁ y₂ := by
  unfold zeroOneLoss
  by_cases h : y₁ ≠ y₂ <;> simp [h]

lemma zeroOneLoss_disagree {Y : Type*} [DecidableEq Y] (y₁ y₂ : Y) (h : y₁ ≠ y₂) :
    zeroOneLoss y₁ y₂ = 1 := by
  simp [zeroOneLoss, h]

/-! ## Distinguishability index -/

/--
A set S distinguishes target c_star from all hypotheses in C if for each h ∈ C,
there exists some x ∈ S where h and c_star disagree.
Now works for any output type Y with decidable equality.
-/
def isDistinguishingSet {X Y : Type*} [DecidableEq Y]
    (C : Set (X → Y)) (c_star : X → Y) (S : Finset X) : Prop :=
  ∀ h ∈ C, ∃ x ∈ S, h x ≠ c_star x

/--
The distinguishability index: the minimum cardinality of a set that distinguishes
c_star from all hypotheses in C.
-/
noncomputable def distinguishabilityIndex {X Y : Type*} [DecidableEq Y]
    (C : Set (X → Y)) (c_star : X → Y) : ℕ :=
  sInf { n | ∃ (S : Finset X), S.card = n ∧ isDistinguishingSet C c_star S }

/-! ## Uniform distribution and lower bound -/

/--
Uniform distribution over a nonempty finite set S.
Now works for any type X using classical reasoning.
-/
noncomputable def uniformDistribution {X : Type*}
    (S : Finset X) (hS : 0 < S.card) : Distribution X := by
  classical
  refine
  { support := S
    prob := fun x => if x ∈ S then (1 / (S.card : ℝ)) else 0
    nonneg := ?_
    prob_eq_zero_of_not_mem := ?_
    sum_prob := ?_ }
  · intro x
    by_cases hx : x ∈ S
    · have hpos : (0 : ℝ) < (S.card : ℝ) := by
        exact_mod_cast hS
      have hnonneg : 0 ≤ (1 / (S.card : ℝ)) := by
        exact one_div_nonneg.mpr (le_of_lt hpos)
      simp [hx, hnonneg]
    · simp [hx]
  · intro x hx
    simp [hx]
  · have hcard : (S.card : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hS)
    calc
      ∑ x in S, (if x ∈ S then (1 / (S.card : ℝ)) else 0)
          = ∑ x in S, (1 / (S.card : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              simp [hx]
      _ = (S.card : ℝ) * (1 / (S.card : ℝ)) := by
              simp
      _ = 1 := by
              field_simp [hcard]

/--
General error lower bound for uniform distributions.
Works for any loss function with a point where loss ≥ 1.
This is a key generalization: no longer assumes 0-1 loss specifically.
-/
lemma error_uniform_lower_bound_general {X Y : Type*}
    (S : Finset X) (hS : 0 < S.card)
    (h : X → Y) (target : X → Y)
    (loss : Y → Y → ℝ)
    (loss_nonneg : ∀ y₁ y₂, 0 ≤ loss y₁ y₂)
    (hS_disagree : ∃ x ∈ S, loss (h x) (target x) ≥ 1) :
    error (uniformDistribution S hS) h target loss ≥ 1 / (S.card : ℝ) := by
  classical
  rcases hS_disagree with ⟨x, hxS, hxloss⟩
  let D := uniformDistribution S hS
  have hnonneg :
      ∀ y ∈ S, 0 ≤ D.prob y * loss (h y) (target y) := by
    intro y _hy
    have hprob : 0 ≤ D.prob y := D.nonneg y
    exact mul_nonneg hprob (loss_nonneg _ _)
  have hxterm :
      D.prob x * loss (h x) (target x) ≥ 1 / (S.card : ℝ) := by
    simp only [D, uniformDistribution]
    rw [if_pos hxS]
    have hprob_pos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hS
    have hprob_nonneg : 0 ≤ 1 / (S.card : ℝ) := by
      exact one_div_nonneg.mpr (le_of_lt hprob_pos)
    calc
      1 / (S.card : ℝ) = (1 / (S.card : ℝ)) * 1 := by ring
      _ ≤ (1 / (S.card : ℝ)) * loss (h x) (target x) := by
          exact mul_le_mul_of_nonneg_left hxloss hprob_nonneg
  have hsingle := Finset.single_le_sum
    (f := fun y => D.prob y * loss (h y) (target y))
    (s := S) (a := x) hnonneg hxS
  calc
    1 / (S.card : ℝ)
      ≤ D.prob x * loss (h x) (target x) := hxterm
    _ ≤ ∑ y in S, D.prob y * loss (h y) (target y) := hsingle
    _ = error D h target loss := by simp [error, D, uniformDistribution]

/--
Original error lower bound for 0-1 loss (special case of the general version).
-/
lemma error_uniform_lower_bound {X Y : Type*} [DecidableEq Y]
    (S : Finset X) (hS : 0 < S.card)
    (h : X → Y) (target : X → Y)
    (hS_disagree : ∃ x ∈ S, h x ≠ target x) :
    error (uniformDistribution S hS) h target zeroOneLoss ≥ 1 / (S.card : ℝ) := by
  apply error_uniform_lower_bound_general
  · exact zeroOneLoss_nonneg
  · rcases hS_disagree with ⟨x, hxS, hxne⟩
    use x, hxS
    simp [zeroOneLoss, hxne]

/-! ## Main theorem: distinguishability-index distributional bound -/

/--
Main theorem (general version): For any distinguishing set S and any loss function,
there exists a distribution under which all hypotheses in C have error at least 1/|S|.
-/
theorem distinguishability_index_distributional_bound_general
    {X Y : Type*} [DecidableEq Y]
    (C : Set (X → Y)) (c_star : X → Y)
    (S : Finset X) (hS : isDistinguishingSet C c_star S) (hSpos : 0 < S.card)
    (loss : Y → Y → ℝ)
    (loss_nonneg : ∀ y₁ y₂, 0 ≤ loss y₁ y₂)
    (loss_disagree : ∀ y₁ y₂, y₁ ≠ y₂ → loss y₁ y₂ ≥ 1) :
    ∃ D : Distribution X, D.support = S ∧
      ∀ h ∈ C, error D h c_star loss ≥ 1 / (S.card : ℝ) := by
  classical
  let D := uniformDistribution S hSpos
  refine ⟨D, rfl, ?_⟩
  intro h hh
  have hdisagree := hS h hh
  apply error_uniform_lower_bound_general
  · exact loss_nonneg
  · rcases hdisagree with ⟨x, hxS, hxne⟩
    use x, hxS
    exact loss_disagree _ _ hxne

/--
Main theorem (0-1 loss version): For any distinguishing set S,
there exists a distribution under which all hypotheses in C have error at least 1/|S|.
-/
theorem distinguishability_index_distributional_bound
    {X Y : Type*} [DecidableEq Y]
    (C : Set (X → Y)) (c_star : X → Y)
    (S : Finset X) (hS : isDistinguishingSet C c_star S) (hSpos : 0 < S.card) :
    ∃ D : Distribution X, D.support = S ∧
      ∀ h ∈ C, error D h c_star zeroOneLoss ≥ 1 / (S.card : ℝ) := by
  apply distinguishability_index_distributional_bound_general
  · exact hS
  · exact hSpos
  · exact zeroOneLoss_nonneg
  · intro y₁ y₂ hne
    simp [zeroOneLoss, hne]

/--
Corollary: When S is a minimal distinguishing set, we get a distributional lower bound
in terms of the distinguishability index.
-/
theorem distinguishability_index_minimal_bound
    {X Y : Type*} [DecidableEq Y]
    (C : Set (X → Y)) (c_star : X → Y)
    (S : Finset X) (hS : isDistinguishingSet C c_star S)
    (hSpos : 0 < S.card) (hmin : S.card = distinguishabilityIndex C c_star) :
    ∃ D : Distribution X,
      ∀ h ∈ C, error D h c_star zeroOneLoss
        ≥ 1 / (distinguishabilityIndex C c_star : ℝ) := by
  obtain ⟨D, hD, hbound⟩ :=
    distinguishability_index_distributional_bound C c_star S hS hSpos
  refine ⟨D, ?_⟩
  intro h hh
  have hbound' := hbound h hh
  simpa [hmin] using hbound'

/--
General version of the minimal bound theorem, parameterized by loss function.
-/
theorem distinguishability_index_minimal_bound_general
    {X Y : Type*} [DecidableEq Y]
    (C : Set (X → Y)) (c_star : X → Y)
    (S : Finset X) (hS : isDistinguishingSet C c_star S)
    (hSpos : 0 < S.card) (hmin : S.card = distinguishabilityIndex C c_star)
    (loss : Y → Y → ℝ)
    (loss_nonneg : ∀ y₁ y₂, 0 ≤ loss y₁ y₂)
    (loss_disagree : ∀ y₁ y₂, y₁ ≠ y₂ → loss y₁ y₂ ≥ 1) :
    ∃ D : Distribution X,
      ∀ h ∈ C, error D h c_star loss
        ≥ 1 / (distinguishabilityIndex C c_star : ℝ) := by
  obtain ⟨D, hD, hbound⟩ :=
    distinguishability_index_distributional_bound_general C c_star S hS hSpos
      loss loss_nonneg loss_disagree
  refine ⟨D, ?_⟩
  intro h hh
  have hbound' := hbound h hh
  simpa [hmin] using hbound'

/-! ## Additional generalizations and helper lemmas -/

/--
If a loss function is bounded below by a positive constant on disagreements,
we can scale the distributional bound accordingly.
-/
theorem distributional_bound_with_loss_scaling
    {X Y : Type*} [DecidableEq Y]
    (C : Set (X → Y)) (c_star : X → Y)
    (S : Finset X) (hS : isDistinguishingSet C c_star S) (hSpos : 0 < S.card)
    (loss : Y → Y → ℝ)
    (loss_nonneg : ∀ y₁ y₂, 0 ≤ loss y₁ y₂)
    (c : ℝ) (hc : 0 < c)
    (loss_disagree : ∀ y₁ y₂, y₁ ≠ y₂ → loss y₁ y₂ ≥ c) :
    ∃ D : Distribution X, D.support = S ∧
      ∀ h ∈ C, error D h c_star loss ≥ c / (S.card : ℝ) := by
  classical
  let D := uniformDistribution S hSpos
  refine ⟨D, rfl, ?_⟩
  intro h hh
  have hdisagree := hS h hh
  rcases hdisagree with ⟨x, hxS, hxne⟩
  have hnonneg :
      ∀ y ∈ S, 0 ≤ D.prob y * loss (h y) (c_star y) := by
    intro y _hy
    have hprob : 0 ≤ D.prob y := D.nonneg y
    exact mul_nonneg hprob (loss_nonneg _ _)
  have hxterm :
      D.prob x * loss (h x) (c_star x) ≥ c / (S.card : ℝ) := by
    simp only [D, uniformDistribution]
    rw [if_pos hxS]
    have hprob_pos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hSpos
    have hprob_nonneg : 0 ≤ 1 / (S.card : ℝ) := by
      exact one_div_nonneg.mpr (le_of_lt hprob_pos)
    have hloss := loss_disagree _ _ hxne
    calc
      c / (S.card : ℝ) = (1 / (S.card : ℝ)) * c := by ring
      _ ≤ (1 / (S.card : ℝ)) * loss (h x) (c_star x) := by
          exact mul_le_mul_of_nonneg_left hloss hprob_nonneg
  have hsingle := Finset.single_le_sum
    (f := fun y => D.prob y * loss (h y) (c_star y))
    (s := S) (a := x) hnonneg hxS
  calc
    c / (S.card : ℝ)
      ≤ D.prob x * loss (h x) (c_star x) := hxterm
    _ ≤ ∑ y in S, D.prob y * loss (h y) (c_star y) := hsingle
    _ = error D h c_star loss := by simp [error, D, uniformDistribution]

/--
Error is nonnegative when loss is nonnegative.
-/
lemma error_nonneg {X Y : Type*} (D : Distribution X) (h : X → Y) (target : X → Y)
    (loss : Y → Y → ℝ) (loss_nonneg : ∀ y₁ y₂, 0 ≤ loss y₁ y₂) :
    0 ≤ error D h target loss := by
  unfold error
  apply Finset.sum_nonneg
  intro x _hx
  exact mul_nonneg (D.nonneg x) (loss_nonneg _ _)

/--
Error is monotone in the loss function.
-/
lemma error_monotone {X Y : Type*} (D : Distribution X) (h : X → Y) (target : X → Y)
    (loss₁ loss₂ : Y → Y → ℝ) (hle : ∀ y₁ y₂, loss₁ y₁ y₂ ≤ loss₂ y₁ y₂) :
    error D h target loss₁ ≤ error D h target loss₂ := by
  unfold error
  apply Finset.sum_le_sum
  intro x _hx
  have hprob : 0 ≤ D.prob x := D.nonneg x
  exact mul_le_mul_of_nonneg_left (hle _ _) hprob

/--
If two hypotheses agree on the support of a distribution, they have the same error.
-/
lemma error_eq_of_agree_on_support {X Y : Type*} (D : Distribution X)
    (h₁ h₂ : X → Y) (target : X → Y) (loss : Y → Y → ℝ)
    (hagree : ∀ x ∈ D.support, h₁ x = h₂ x) :
    error D h₁ target loss = error D h₂ target loss := by
  unfold error
  apply Finset.sum_congr rfl
  intro x hx
  rw [hagree x hx]

end LearningTheory
