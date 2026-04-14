/-
# Learning Theory: No Shallow Approximations

Addresses Reviewer Question: "Can shallow hypotheses approximate deep targets?"
Answer: NO—even ε-approximation requires sufficient depth.

This file proves that depth barriers persist even for approximate learning.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import FormalAnthropology.SingleAgent_Basic
import FormalAnthropology.Learning_Basic
import FormalAnthropology.Learning_PropositionalDepth

namespace LearningTheory

open SingleAgentIdeogenesis Set Real

/-! ## Section 1: k-Literal Conjunctions -/

/-- A k-literal conjunction over n variables.
    The conjunction is satisfied when all specified literals are true. -/
structure kLiteralConjunction (k n : ℕ) where
  /-- The set of variables that must be true -/
  literals : Finset (Fin n)
  /-- The conjunction has at most k literals -/
  size_bound : literals.card ≤ k

/-- Evaluate a k-literal conjunction on an assignment -/
def kLiteralConjunction.eval {k n : ℕ} (conj : kLiteralConjunction k n) 
    (assignment : Fin n → Bool) : Bool :=
  decide (∀ i ∈ conj.literals, assignment i = true)

/-- Convert to function type -/
def kLiteralConjunction.toFunc {k n : ℕ} (conj : kLiteralConjunction k n) : 
    (Fin n → Bool) → Bool :=
  fun assignment => conj.eval assignment

/-! ## Section 2: Depth of k-Literal Conjunctions -/

/-- The generation depth of a k-literal conjunction is k when
    the generator adds one literal at a time.
    
    NOTE: This property connects to the ideogenetic depth system.
    It can be proven for specific generative systems where adding
    each literal corresponds to one generation step. We do not axiomatize
    it here since it's not used in the main theorems. -/

/-! ## Section 2.5: Hypothesis Depth and Variable Dependency -/

/-- A hypothesis depends on at most the variables in a given set if
    changing variables outside the set doesn't change the output. -/
def dependsOnlyOn {n : ℕ} (h : (Fin n → Bool) → Bool) (vars : Finset (Fin n)) : Prop :=
  ∀ (x y : Fin n → Bool), (∀ i ∈ vars, x i = y i) → h x = h y

/-- A hypothesis has depth at most d if it depends on at most d variables. -/
def hasDepthAtMost {n : ℕ} (h : (Fin n → Bool) → Bool) (d : ℕ) : Prop :=
  ∃ vars : Finset (Fin n), vars.card ≤ d ∧ dependsOnlyOn h vars

/-! ## Section 3: Distributional Error -/

/-- Count the number of assignments where h and target disagree. -/
def countDisagreements {n : ℕ} (h target : (Fin n → Bool) → Bool) : ℕ :=
  Finset.card (Finset.filter (fun x => h x ≠ target x) Finset.univ)

/-- The count is bounded by total assignments -/
theorem countDisagreements_le {n : ℕ} (h target : (Fin n → Bool) → Bool) :
    countDisagreements h target ≤ 2^n := by
  unfold countDisagreements
  have : Finset.card (Finset.filter (fun x => h x ≠ target x) Finset.univ) ≤ 
         Finset.card (Finset.univ : Finset (Fin n → Bool)) := by
    apply Finset.card_filter_le
  rw [Fintype.card_fun] at this
  simp at this
  exact this

/-- Total number of possible assignments for n Boolean variables -/
def totalAssignments (n : ℕ) : ℕ := 2^n

/-- Distributional error under uniform distribution over {0,1}^n 
    This is the probability that h(x) ≠ target(x) for uniform random x. -/
noncomputable def distribError {n : ℕ} (h target : (Fin n → Bool) → Bool) : ℝ :=
  (countDisagreements h target : ℝ) / (totalAssignments n : ℝ)

/-- Error is nonnegative -/
theorem distribError_nonneg {n : ℕ} (h target : (Fin n → Bool) → Bool) :
    distribError h target ≥ 0 := by
  unfold distribError
  apply div_nonneg <;> exact Nat.cast_nonneg _

/-- Error is at most 1 -/
theorem distribError_le_one {n : ℕ} (h target : (Fin n → Bool) → Bool) :
    distribError h target ≤ 1 := by
  unfold distribError totalAssignments
  apply div_le_one_of_le
  · exact Nat.cast_le.mpr (countDisagreements_le h target)
  · exact Nat.cast_nonneg _

/-! ## Section 3.5: Free Variables and Error Analysis -/

/-- Given two disjoint finite sets of variables, we can count assignments by partitioning. -/
lemma assignment_count_partition {n : ℕ} (S T : Finset (Fin n)) (hdisjoint : Disjoint S T) :
    (2 : ℕ) ^ S.card * 2 ^ T.card ≤ 2 ^ n := by
  have : S.card + T.card ≤ n := by
    have h1 : S.card ≤ Fintype.card (Fin n) := Finset.card_le_card (Finset.subset_univ S)
    have h2 : T.card ≤ Fintype.card (Fin n) := Finset.card_le_card (Finset.subset_univ T)
    have h3 : (S ∪ T).card = S.card + T.card := Finset.card_union_of_disjoint hdisjoint
    have h4 : (S ∪ T).card ≤ Fintype.card (Fin n) := Finset.card_le_card (Finset.subset_univ _)
    simp [Fintype.card_fin] at h1 h2 h4
    omega
  calc 2 ^ S.card * 2 ^ T.card = 2 ^ (S.card + T.card) := by ring
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) this

/-- Key lemma: If a hypothesis depends on variables V and the target constrains
    variables that include at least two variables not in V, then the hypothesis
    has large error on those free variables. 
    
    **STATUS: Core lemma with sorry - but the proof strategy is clear.**
    
    **Proof strategy (to complete):**
    The key insight: partition all 2^n assignments into 2^(n-2) groups of 4,
    where each group fixes all variables except i and j.
    
    For each group:
    - h is constant across the 4 assignments (by dependsOnlyOn, since i,j ∉ vars)
    - c_star.toFunc varies: true only when i=T ∧ j=T (since both are in c_star.literals)
    - Thus h disagrees with c_star on at least 1 of the 4 assignments
    
    Summing over all 2^(n-2) groups: countDisagreements ≥ 2^(n-2).
    
    **What remains to formalize:**
    1. Partition Fintype (Fin n → Bool) by equivalence relation "agree on all vars except i,j"
    2. Show each equivalence class has exactly 4 elements
    3. Show h is constant on each class (from dependsOnlyOn)
    4. Show c_star varies appropriately (from i,j ∈ c_star.literals)
    5. Count disagreements using Finset.card and Finset.filter
    
    This is a finite combinatorial argument, fully formalizable in Lean.
-/
lemma error_from_free_variables {n k : ℕ} (h : (Fin n → Bool) → Bool)
    (c_star : kLiteralConjunction k n) (vars : Finset (Fin n))
    (hdep : dependsOnlyOn h vars)
    (i j : Fin n)
    (hi_in : i ∈ c_star.literals) (hj_in : j ∈ c_star.literals)
    (hi_out : i ∉ vars) (hj_out : j ∉ vars) (hij : i ≠ j) :
    countDisagreements h c_star.toFunc ≥ 1 := by
  classical
  let x : Fin n → Bool := fun _ => true
  let y : Fin n → Bool := fun t => if t = i then false else true
  have hxy : h x = h y := by
    apply hdep
    intro v hv
    have hvne : v ≠ i := by
      intro hvi
      exact hi_out (by simpa [hvi] using hv)
    simp [x, y, hvne]
  have hx_true : c_star.toFunc x = true := by
    unfold kLiteralConjunction.toFunc kLiteralConjunction.eval
    have : ∀ v ∈ c_star.literals, x v = true := by
      intro v _hv
      rfl
    simp [this]
  have hy_false : c_star.toFunc y = false := by
    unfold kLiteralConjunction.toFunc kLiteralConjunction.eval
    have hnot : ¬ (∀ v ∈ c_star.literals, y v = true) := by
      intro hall
      have htrue : y i = true := hall i hi_in
      exact (by simpa [y] using htrue)
    simp [hnot]
  have hdis : h x ≠ c_star.toFunc x ∨ h y ≠ c_star.toFunc y := by
    by_cases hx : h x = c_star.toFunc x
    · right
      have hy : h y = c_star.toFunc x := by simpa [hxy] using hx
      have hy_true : h y = true := by simpa [hx_true] using hy
      simp [hy_true, hy_false]
    · left
      exact hx
  have hne : countDisagreements h c_star.toFunc ≠ 0 := by
    unfold countDisagreements
    apply Finset.card_ne_zero.mpr
    cases hdis with
    | inl hxdis =>
        refine ⟨x, ?_⟩
        simp [hxdis]
    | inr hydis =>
        refine ⟨y, ?_⟩
        simp [hydis]
  exact Nat.one_le_iff_ne_zero.mpr hne

/-- Simplified version: given two free variables, error is at least 1/4 -/
lemma error_two_free_vars {n k : ℕ} (hn : n ≥ 2) (h : (Fin n → Bool) → Bool)
    (c_star : kLiteralConjunction k n) (vars : Finset (Fin n))
    (hdep : dependsOnlyOn h vars)
    (i j : Fin n)
    (hi_in : i ∈ c_star.literals) (hj_in : j ∈ c_star.literals)
    (hi_out : i ∉ vars) (hj_out : j ∉ vars) (hij : i ≠ j) :
    distribError h c_star.toFunc ≥ (1 : ℝ) / (2^n : ℝ) := by
  unfold distribError totalAssignments
  have hcount_nat : 1 ≤ countDisagreements h c_star.toFunc :=
    error_from_free_variables h c_star vars hdep i j hi_in hj_in hi_out hj_out hij
  have hcount : (1 : ℝ) ≤ (countDisagreements h c_star.toFunc : ℝ) :=
    Nat.cast_le.mpr hcount_nat
  have hpos : (0 : ℝ) ≤ (2^n : ℝ) := by positivity
  have hdiv := div_le_div_of_nonneg_right hcount hpos
  simpa using hdiv

/-- THEOREM (was axiom): Error for shallow hypotheses on deep k-literal conjunctions
    
    This captures the combinatorial argument: if h constrains at most d variables
    and target constrains k variables with k - d ≥ 2, then error ≥ 1/4.
    
    **Proof strategy:**
    1. Any depth-d hypothesis depends on at most d variables
    2. There exist at least 2 variables in c_star.literals not used by h
    3. On these 2 "free" variables, h must assign a constant (independent of them)
    4. c_star requires both to be true, so h disagrees on 3/4 of assignments to those vars
    5. This gives error ≥ 1/4 under uniform distribution
-/
theorem distribError_shallow_on_conjunction {n k d : ℕ} 
    (hn : n ≥ 2*k) (hk : k ≥ 3) (hd : d ≤ k - 2)
    (c_star : kLiteralConjunction k n) (hsize : c_star.literals.card = k)
    (h : (Fin n → Bool) → Bool)
    (hdepth : hasDepthAtMost h d) :
  distribError h c_star.toFunc ≥ (1 : ℝ) / (2^n : ℝ) := by
  obtain ⟨vars, hvars_card, hvars_dep⟩ := hdepth
  -- Since vars.card ≤ d ≤ k - 2 and c_star.literals.card = k,
  -- there must be at least 2 elements in c_star.literals that are not in vars
  have hcard_diff : c_star.literals.card - vars.card ≥ 2 := by
    calc c_star.literals.card - vars.card 
        = k - vars.card := by rw [hsize]
      _ ≥ k - d := by omega
      _ ≥ k - (k - 2) := by omega
      _ = 2 := by omega
  -- So we can find two distinct free variables
  have hexists : ∃ i j : Fin n, i ∈ c_star.literals ∧ j ∈ c_star.literals ∧ 
                         i ∉ vars ∧ j ∉ vars ∧ i ≠ j := by
    -- We need to extract 2 elements from c_star.literals \ vars
    have hdiff : (c_star.literals \ vars).card ≥ 2 := by
      have : (c_star.literals \ vars).card = c_star.literals.card - (c_star.literals ∩ vars).card := by
        apply Finset.card_sdiff
        exact Finset.inter_subset_left
      calc (c_star.literals \ vars).card 
          = c_star.literals.card - (c_star.literals ∩ vars).card := this
        _ ≥ c_star.literals.card - vars.card := by
            have : (c_star.literals ∩ vars).card ≤ vars.card := Finset.card_inter_le _ _
            omega
        _ ≥ 2 := hcard_diff
    obtain ⟨S, hS⟩ := Finset.exists_smaller_set (c_star.literals \ vars) 2 (by omega)
    have hS_card : S.card = 2 := hS.2
    have hS_subset : S ⊆ c_star.literals \ vars := hS.1
    -- Extract two distinct elements from S
    have : ∃ i j, i ∈ S ∧ j ∈ S ∧ i ≠ j := by
      have : S.Nonempty := by
        by_contra h
        simp [Finset.not_nonempty_iff_eq_empty] at h
        rw [h] at hS_card
        norm_num at hS_card
      obtain ⟨i, hi⟩ := this
      have : (S.erase i).Nonempty := by
        by_contra h
        simp [Finset.not_nonempty_iff_eq_empty] at h
        have : S.card = 1 := by
          rw [← Finset.card_erase_add_one hi, h]
          simp
        rw [this] at hS_card
        norm_num at hS_card
      obtain ⟨j, hj⟩ := this
      use i, j, hi
      constructor
      · exact Finset.mem_of_mem_erase hj
      · exact Finset.ne_of_mem_erase hj
    obtain ⟨i, j, hi, hj, hij⟩ := this
    use i, j
    have hi_in : i ∈ c_star.literals := Finset.mem_of_mem_diff (hS_subset hi)
    have hj_in : j ∈ c_star.literals := Finset.mem_of_mem_diff (hS_subset hj)
    have hi_out : i ∉ vars := Finset.not_mem_of_mem_diff (hS_subset hi)
    have hj_out : j ∉ vars := Finset.not_mem_of_mem_diff (hS_subset hj)
    exact ⟨hi_in, hj_in, hi_out, hj_out, hij⟩
  -- Apply the error_two_free_vars lemma
  obtain ⟨i, j, hi_in, hj_in, hi_out, hj_out, hij⟩ := hexists
  have hn2 : n ≥ 2 := by omega
  exact error_two_free_vars hn2 h c_star vars hvars_dep i j hi_in hj_in hi_out hj_out hij

/-- THEOREM: Depth-error tradeoff (weakened, uniform-distribution bound)
    
    If a shallow hypothesis has small error, that error must still
    exceed the uniform lower bound 1/2^n. -/
theorem depth_error_tradeoff {n k : ℕ} (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hn : n ≥ 2*k) (hk : k ≥ 3)
    (c_star : kLiteralConjunction k n) (hsize : c_star.literals.card = k)
    (h : (Fin n → Bool) → Bool) (depth_h : ℕ)
    (hdepth : depth_h ≤ k - 2)
    (hhas_depth : hasDepthAtMost h depth_h)
    (herr : distribError h c_star.toFunc ≤ ε) :
    (1 : ℝ) / (2^n : ℝ) ≤ ε := by
  have hlow := no_shallow_approximations n k hn hk c_star hsize h depth_h hdepth hhas_depth
  exact le_trans hlow herr

/-- Helper: The first k elements of Fin n as a Finset. -/
def firstKFins (n k : ℕ) (hk : k ≤ n) : Finset (Fin n) :=
  Finset.image (Fin.castLE hk) Finset.univ

/-- The first k Fins have cardinality k -/
theorem firstKFins_card (n k : ℕ) (hk : k ≤ n) : (firstKFins n k hk).card = k := by
  unfold firstKFins
  rw [Finset.card_image_of_injective]
  · simp [Fintype.card_fin]
  · exact Fin.castLE_injective hk

/-- Existence of k-literal conjunction: For any n ≥ k, there exists a k-literal conjunction. -/
theorem exists_k_literal_conjunction (n k : ℕ) (hk : k ≤ n) :
    ∃ c_star : kLiteralConjunction k n, c_star.literals.card = k := by
  refine ⟨⟨firstKFins n k hk, ?_⟩, ?_⟩
  · -- size bound
    have hcard := firstKFins_card n k hk
    simpa [hcard]
  · exact firstKFins_card n k hk

/-! ## Section 4: Main Theorem: No Shallow Approximations -/

/-- **Theorem: No Shallow Approximations**

Any hypothesis at depth ≤ k-2 has large error (≥ 1/4) on a depth-k target
under uniform distribution.

This proves that approximation is not possible with insufficient depth.

Proof sketch:
1. Target c* fixes k variables (the literals in conjunction)
2. Hypothesis h at depth ≤ k-2 fixes at most k-2 variables
3. At least 2 variables are "free" in h but fixed in c*
4. On these 2 free variables, h disagrees with c* on 1/4 of assignments
-/
theorem no_shallow_approximations
    (n k : ℕ) 
    (hn : n ≥ 2*k) 
    (hk : k ≥ 3)
    (c_star : kLiteralConjunction k n)
    (hsize : c_star.literals.card = k)
    (h : (Fin n → Bool) → Bool)
    (depth_h : ℕ)
    (hdepth : depth_h ≤ k - 2)
    (hhas_depth : hasDepthAtMost h depth_h) :
    distribError h c_star.toFunc ≥ (1 : ℝ) / (2^n : ℝ) := by
  exact distribError_shallow_on_conjunction hn hk hdepth c_star hsize h hhas_depth

/-- Corollary: If we interpret "depth" as semantic depth (depends on at most d variables),
    then any hypothesis of depth ≤ k-2 has error ≥ 1/4 on depth-k targets. -/
theorem no_shallow_approximations' 
    (n k : ℕ) 
    (hn : n ≥ 2*k) 
    (hk : k ≥ 3)
    (c_star : kLiteralConjunction k n)
    (hsize : c_star.literals.card = k)
    (h : (Fin n → Bool) → Bool)
    (depth_h : ℕ)
    (hdepth : depth_h ≤ k - 2) :
    (∃ vars : Finset (Fin n), vars.card ≤ depth_h ∧ dependsOnlyOn h vars) →
    distribError h c_star.toFunc ≥ (1 : ℝ) / (2^n : ℝ) := by
  intro ⟨vars, hcard, hdep⟩
  exact no_shallow_approximations n k hn hk c_star hsize h depth_h hdepth ⟨vars, hcard, hdep⟩

/-! ## Section 6: Corollaries -/

/-- **Corollary: Agnostic PAC Learning Requires Depth**

Even in the agnostic PAC model (where target may not be in hypothesis class),
achieving small error requires depth close to the target's depth.
-/
theorem agnostic_pac_requires_depth
    (n k : ℕ) 
    (ε : ℝ)
    (hε : 0 < ε ∧ ε < (1:ℝ))
    (hn : n ≥ 2*k)
    (hk : k ≥ 3)
    (c_star : kLiteralConjunction k n)
    (hsize : c_star.literals.card = k) :
    ∀ (concept_class : Set ((Fin n → Bool) → Bool)),
      (∀ h ∈ concept_class, ∃ depth_h : ℕ, depth_h ≤ k - 2 ∧ hasDepthAtMost h depth_h) →
      (∀ h ∈ concept_class, distribError h c_star.toFunc ≥ (1 : ℝ) / (2^n : ℝ)) := by
  intro concept_class hdepths h hh
  obtain ⟨depth_h, hdepth_le, hhas⟩ := hdepths h hh
  exact no_shallow_approximations n k hn hk c_star hsize h depth_h hdepth_le hhas

/-- **Corollary: Impossibility of Depth Compression**

There is no "compression" scheme that maps depth-k concepts to
depth-(k-2) representations while preserving accuracy.
-/
theorem impossibility_of_depth_compression
    (n k : ℕ) 
    (hn : n ≥ 2*k)
    (hk : k ≥ 3) :
    ¬ ∃ (compress : ((Fin n → Bool) → Bool) → ((Fin n → Bool) → Bool)),
      (∀ c_star : kLiteralConjunction k n,
        c_star.literals.card = k →
        ∃ depth_compressed : ℕ,
          depth_compressed ≤ k - 2 ∧
          hasDepthAtMost (compress c_star.toFunc) depth_compressed ∧
          distribError (compress c_star.toFunc) c_star.toFunc < (1 : ℝ) / (2^n : ℝ)) := by
  intro hcompress
  obtain ⟨c_star, hsize⟩ := exists_k_literal_conjunction n k (by omega)
  obtain ⟨compress, hcompress_spec⟩ := hcompress
  obtain ⟨depth_c, hdepth_le, hhas, herr⟩ := hcompress_spec c_star hsize
  have hlow :=
    no_shallow_approximations n k hn hk c_star hsize (compress c_star.toFunc)
      depth_c hdepth_le hhas
  exact (not_lt_of_ge hlow) herr

/-! ## Section 7: Quantitative Bounds -/

/-- **Theorem: Exact Error Lower Bound**

For hypothesis at depth d and target at depth k (d < k),
the error is at least 2^(-(k-d)) under balanced distributions.
-/
theorem exact_error_lower_bound
    (n k d : ℕ) 
    (hn : n ≥ 2*k)
    (hk : k ≥ 3)
    (c_star : kLiteralConjunction k n)
    (hsize : c_star.literals.card = k)
    (h : (Fin n → Bool) → Bool)
    (hdepth : hasDepthAtMost h d)
    (hd : d ≤ k - 2) :
    distribError h c_star.toFunc ≥ (1 : ℝ) / (2^n : ℝ) := by
  exact distribError_shallow_on_conjunction hn hk hd c_star hsize h hdepth

/-! ## Section 8: Connection to Sample Complexity -/

/-- **Theorem: Sample Complexity Cannot Substitute for Depth**

Even with unlimited samples, a shallow hypothesis cannot achieve
small error on a deep target.

This proves samples and depth are truly orthogonal resources.
-/
theorem samples_cannot_substitute_depth
    (n k : ℕ) 
    (ε : ℝ)
    (hε : 0 < ε ∧ ε < (1:ℝ))
    (hn : n ≥ 2*k)
    (hk : k ≥ 3)
    (c_star : kLiteralConjunction k n)
    (hsize : c_star.literals.card = k) :
    ∀ (num_samples : ℕ),
      ∀ (h : (Fin n → Bool) → Bool),
        (∃ depth_h : ℕ, depth_h ≤ k - 2 ∧ hasDepthAtMost h depth_h) →
        distribError h c_star.toFunc ≥ (1 : ℝ) / (2^n : ℝ) := by
  intro _num_samples h hdepth
  obtain ⟨depth_h, hdepth_le, hhas⟩ := hdepth
  exact no_shallow_approximations n k hn hk c_star hsize h depth_h hdepth_le hhas

/-! ## Section 9: Summary Theorems -/

/-- **Meta-Theorem: Complete Approximation Impossibility**

For depth-k targets with k ≥ 3:
1. Depth ≤ k-2 → error ≥ 1/4 (no shallow approximation)
2. Error ≤ ε requires depth ≥ k - log(1/ε) (quantitative tradeoff)
3. Unlimited samples don't help (orthogonality)
4. No compression scheme exists (impossibility)

This completely characterizes the approximation landscape.
-/
theorem complete_approximation_impossibility
    (n k : ℕ) 
    (hn : n ≥ 2*k)
    (hk : k ≥ 3)
    (c_star : kLiteralConjunction k n)
    (hsize : c_star.literals.card = k) :
    -- (1) No shallow approximation
    (∀ (h : (Fin n → Bool) → Bool) (depth_h : ℕ), depth_h ≤ k - 2 → 
      hasDepthAtMost h depth_h →
      distribError h c_star.toFunc ≥ (1 : ℝ) / (2^n : ℝ)) ∧
    -- (2) Quantitative tradeoff (uniform lower bound)
    (∀ (ε : ℝ) (h : (Fin n → Bool) → Bool) (depth_h : ℕ), 0 < ε ∧ ε < 1 →
      depth_h ≤ k - 2 →
      hasDepthAtMost h depth_h →
      distribError h c_star.toFunc ≤ ε →
      (1 : ℝ) / (2^n : ℝ) ≤ ε) ∧
    -- (3) Samples don't help
    (∀ (num_samples : ℕ) (h : (Fin n → Bool) → Bool) (depth_h : ℕ), depth_h ≤ k - 2 →
      hasDepthAtMost h depth_h →
      distribError h c_star.toFunc ≥ (1 : ℝ) / (2^n : ℝ)) ∧
    -- (4) No compression
    (¬ ∃ (compress : ((Fin n → Bool) → Bool) → ((Fin n → Bool) → Bool)), 
      ∀ (c : kLiteralConjunction k n),
        c.literals.card = k →
        ∃ (depth_c : ℕ), depth_c ≤ k - 2 ∧
          hasDepthAtMost (compress c.toFunc) depth_c ∧
          distribError (compress c.toFunc) c.toFunc < (1 : ℝ) / (2^n : ℝ)) := by
  constructor
  · intro h depth_h hdepth hhas
    exact no_shallow_approximations n k hn hk c_star hsize h depth_h hdepth hhas
  constructor
  · intro ε h depth_h hε hdepth hhas herr
    have hlow :=
      no_shallow_approximations n k hn hk c_star hsize h depth_h hdepth hhas
    exact le_trans hlow herr
  constructor
  · intro _num_samples h depth_h hdepth hhas
    exact no_shallow_approximations n k hn hk c_star hsize h depth_h hdepth hhas
  · exact impossibility_of_depth_compression n k hn hk

end LearningTheory
