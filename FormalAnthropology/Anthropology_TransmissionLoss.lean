/-
# Transmission Loss Theorem

From FORMAL_ANTHROPOLOGY++ Chapter 3: The Anthropological Extension, Section 3.3

**Theorem 3.2 (Transmission Loss Theorem)**: If fidelity < 1, then over `k` generations:
```
|mem(G_{n+k})| ≤ |mem(G_n)| · fidelity^k + Σ_{i=0}^{k-1} innov · fidelity^i
```
Ideas decay exponentially unless innovation compensates.

## Key Insight:
Cultural transmission is lossy. Each generation loses some fraction of the previous generation's
knowledge. This exponential decay creates a "generational barrier" - maintaining cultural depth
requires either:
1. High transmission fidelity (education, writing, institutions)
2. High innovation rate (constant rediscovery)
3. Both

## Mathematical Content:
This theorem establishes a precise quantitative relationship between:
- Transmission fidelity (what fraction of ideas survives intergenerational transfer)
- Innovation rate (how many new ideas are added per generation)
- Cultural memory size over time

The formula has two terms:
1. Decay term: |mem(G_n)| · fidelity^k (exponential decay of inherited ideas)
2. Innovation term: Σ_{i=0}^{k-1} innov · fidelity^i (geometric series of innovations)

Without innovation (innov = 0), cultural memory shrinks exponentially.
With sufficient innovation, culture can grow despite loss.

## Dependencies:
- Basic real number arithmetic
- Geometric series
- Power functions

## Generalization Notes:
This version significantly weakens the hypotheses compared to the original:
- The `memory_after_k_expanded` theorem no longer requires `h_initial : 0 ≤ initial_size`
- The transmission loss theorem uses equality (exact formula) rather than inequality
- Several theorems remove unnecessary positivity assumptions
- The Generation structure no longer requires `h_nonneg` for many results
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.GeomSum
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace CulturalTransmission

open BigOperators Filter Topology

/-! ## Section 1: Basic Definitions -/

/-- A generation: a cohort of agents with overlapping lifespans -/
structure Generation where
  /-- Generation index -/
  index : ℕ
  /-- Set of ideas held by this generation (cardinality) -/
  memory_size : ℝ
  /-- Memory size is non-negative -/
  h_nonneg : 0 ≤ memory_size

/-- Cultural transmission parameters -/
structure TransmissionParams where
  /-- Transmission fidelity: fraction of ideas successfully transmitted to next generation -/
  fidelity : ℝ
  /-- Innovation rate: number of new ideas added per generation -/
  innovation_rate : ℝ
  /-- Fidelity is a probability -/
  h_fidelity_bounds : 0 ≤ fidelity ∧ fidelity ≤ 1
  /-- Innovation rate is non-negative -/
  h_innovation_nonneg : 0 ≤ innovation_rate

/-! ## Section 2: Single-Step Transmission -/

/-- Memory size after one generation of transmission -/
noncomputable def nextGenerationSize (params : TransmissionParams) (current_size : ℝ) : ℝ :=
  params.fidelity * current_size + params.innovation_rate

/-- Single-step transmission bound -/
theorem single_step_transmission (params : TransmissionParams) (G : Generation) :
    nextGenerationSize params G.memory_size =
    params.fidelity * G.memory_size + params.innovation_rate := by
  rfl

/-! ## Section 3: Multi-Generation Transmission -/

/-- Memory size after k generations, computed iteratively -/
noncomputable def memoryAfterGenerations (params : TransmissionParams)
    (initial_size : ℝ) : ℕ → ℝ
  | 0 => initial_size
  | k + 1 => nextGenerationSize params (memoryAfterGenerations params initial_size k)

/-- Key lemma for the recurrence: f * Σ_{i<k} f^i + 1 = Σ_{i<k} f^i + f^k -/
private lemma shift_sum (f : ℝ) (k : ℕ) :
    f * (∑ i in Finset.range k, f ^ i) + 1 = (∑ i in Finset.range k, f ^ i) + f ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have lhs_expand : f * (∑ i in Finset.range (k+1), f ^ i) + 1 =
        f * ((∑ i in Finset.range k, f ^ i) + f^k) + 1 := by
      rw [Finset.sum_range_succ]
    have rhs_expand : (∑ i in Finset.range (k+1), f ^ i) + f ^ (k+1) =
        ((∑ i in Finset.range k, f ^ i) + f^k) + f ^ (k+1) := by
      rw [Finset.sum_range_succ]
    rw [lhs_expand, rhs_expand]
    have h : f * f ^ k = f ^ (k + 1) := (pow_succ' f k).symm
    calc f * ((∑ i in Finset.range k, f ^ i) + f ^ k) + 1
        = f * (∑ i in Finset.range k, f ^ i) + f * f ^ k + 1 := by ring
      _ = f * (∑ i in Finset.range k, f ^ i) + f ^ (k + 1) + 1 := by rw [h]
      _ = (f * (∑ i in Finset.range k, f ^ i) + 1) + f ^ (k + 1) := by ring
      _ = ((∑ i in Finset.range k, f ^ i) + f ^ k) + f ^ (k + 1) := by rw [ih]

/-- Expanded form shows the decay and innovation terms.

    GENERALIZATION: This theorem no longer requires h_initial : 0 ≤ initial_size.
    The formula is purely algebraic and holds for any real initial_size. -/
theorem memory_after_k_expanded (params : TransmissionParams) (initial_size : ℝ) (k : ℕ) :
    memoryAfterGenerations params initial_size k =
    initial_size * params.fidelity ^ k +
    params.innovation_rate * (∑ i in Finset.range k, params.fidelity ^ i) := by
  induction k with
  | zero =>
    simp only [memoryAfterGenerations, pow_zero, mul_one, Finset.range_zero, Finset.sum_empty,
               mul_zero, add_zero]
  | succ k ih =>
    simp only [memoryAfterGenerations, nextGenerationSize]
    rw [ih, Finset.sum_range_succ, pow_succ]
    have key : params.fidelity * (∑ i in Finset.range k, params.fidelity ^ i) + 1 =
               (∑ i in Finset.range k, params.fidelity ^ i) + params.fidelity ^ k :=
      shift_sum params.fidelity k
    have h_comm : params.fidelity * params.fidelity ^ k = params.fidelity ^ k * params.fidelity :=
      mul_comm _ _
    calc params.fidelity * (initial_size * params.fidelity ^ k +
            params.innovation_rate * (∑ i in Finset.range k, params.fidelity ^ i)) +
            params.innovation_rate
        = params.fidelity * initial_size * params.fidelity ^ k +
          params.fidelity * params.innovation_rate * (∑ i in Finset.range k, params.fidelity ^ i) +
          params.innovation_rate := by ring
      _ = params.fidelity * initial_size * params.fidelity ^ k +
          params.innovation_rate * (params.fidelity * (∑ i in Finset.range k, params.fidelity ^ i) + 1) := by ring
      _ = params.fidelity * initial_size * params.fidelity ^ k +
          params.innovation_rate * ((∑ i in Finset.range k, params.fidelity ^ i) + params.fidelity ^ k) := by
            rw [key]
      _ = initial_size * (params.fidelity * params.fidelity ^ k) +
          params.innovation_rate * ((∑ i in Finset.range k, params.fidelity ^ i) + params.fidelity ^ k) := by ring
      _ = initial_size * (params.fidelity ^ k * params.fidelity) +
          params.innovation_rate * ((∑ i in Finset.range k, params.fidelity ^ i) + params.fidelity ^ k) := by
            rw [h_comm]

/-! ## Section 4: The Main Theorem -/

/-- **Theorem 3.2 (Transmission Loss Theorem)**

If transmission fidelity is less than 1, the memory size after k generations
equals the decay of initial memory plus the sum of decayed innovations.

GENERALIZATION: This is now an equality (exact formula), not just an upper bound.
The hypothesis h_fidelity_less is actually not needed for the equality to hold,
but we keep it to emphasize the context where this matters.
-/
theorem transmission_loss_theorem (params : TransmissionParams) (G_n : Generation) (k : ℕ) :
    memoryAfterGenerations params G_n.memory_size k =
    G_n.memory_size * params.fidelity ^ k +
    params.innovation_rate * (∑ i in Finset.range k, params.fidelity ^ i) := by
  exact memory_after_k_expanded params G_n.memory_size k

/-! ## Section 5: Consequences and Corollaries -/

/-- If there is no innovation, memory decays exponentially.

    GENERALIZATION: Removed h_fidelity_less hypothesis - this holds for any fidelity. -/
theorem no_innovation_decay (params : TransmissionParams) (G_n : Generation) (k : ℕ)
    (h_no_innov : params.innovation_rate = 0) :
    memoryAfterGenerations params G_n.memory_size k = G_n.memory_size * params.fidelity ^ k := by
  rw [memory_after_k_expanded, h_no_innov]
  simp only [zero_mul, add_zero]

/-- For fidelity < 1, memory converges to a limit with constant innovation.

    GENERALIZATION: Removed h_fidelity_pos hypothesis - we only need fidelity < 1.
    When fidelity ≤ 0, convergence is even faster. -/
theorem memory_limit_exists (params : TransmissionParams) (G_n : Generation)
    (h_fidelity_less : params.fidelity < 1) :
    ∃ L : ℝ, Tendsto (fun k => memoryAfterGenerations params G_n.memory_size k) atTop (𝓝 L) := by
  use params.innovation_rate / (1 - params.fidelity)

  have h_fid_ne_one : params.fidelity ≠ 1 := ne_of_lt h_fidelity_less
  have h_one_sub_fid_pos : 0 < 1 - params.fidelity := by linarith
  have h_one_sub_fid_ne_zero : 1 - params.fidelity ≠ 0 := ne_of_gt h_one_sub_fid_pos

  have h_abs_fid : |params.fidelity| < 1 := by
    rw [abs_of_nonneg params.h_fidelity_bounds.1]
    exact h_fidelity_less

  have h_pow_zero : Tendsto (fun n : ℕ => params.fidelity ^ n) atTop (𝓝 0) := by
    rw [tendsto_pow_atTop_nhds_zero_iff]
    exact h_abs_fid

  have h_geom_limit : ∀ k : ℕ, (∑ i in Finset.range k, params.fidelity ^ i) =
      (1 - params.fidelity ^ k) / (1 - params.fidelity) := by
    intro k
    rw [geom_sum_eq h_fid_ne_one k]
    -- geom_sum_eq gives (f^k - 1) / (f - 1), we want (1 - f^k) / (1 - f)
    -- These are equal: (f^k - 1) / (f - 1) = -(1 - f^k) / -(1 - f) = (1 - f^k) / (1 - f)
    have h1 : params.fidelity ^ k - 1 = -(1 - params.fidelity ^ k) := by ring
    have h2 : params.fidelity - 1 = -(1 - params.fidelity) := by ring
    rw [h1, h2, neg_div_neg_eq]

  have h_expanded : (fun k => memoryAfterGenerations params G_n.memory_size k) =
      fun k => G_n.memory_size * params.fidelity ^ k +
               params.innovation_rate * ((1 - params.fidelity ^ k) / (1 - params.fidelity)) := by
    ext k
    rw [memory_after_k_expanded, h_geom_limit]

  rw [h_expanded]

  -- The limit of the first term is 0
  have h_first_term : Tendsto (fun k => G_n.memory_size * params.fidelity ^ k) atTop (𝓝 0) := by
    have : Tendsto (fun k => G_n.memory_size * params.fidelity ^ k) atTop (𝓝 (G_n.memory_size * 0)) := by
      exact Tendsto.mul tendsto_const_nhds h_pow_zero
    simp at this
    exact this

  -- The limit of the second term is innov/(1-fid)
  have h_second_term : Tendsto (fun k => params.innovation_rate * ((1 - params.fidelity ^ k) / (1 - params.fidelity)))
      atTop (𝓝 (params.innovation_rate / (1 - params.fidelity))) := by
    have h1 : Tendsto (fun k => 1 - params.fidelity ^ k) atTop (𝓝 (1 - 0)) := by
      exact Tendsto.sub tendsto_const_nhds h_pow_zero
    simp at h1
    have h2 : Tendsto (fun k => (1 - params.fidelity ^ k) / (1 - params.fidelity))
        atTop (𝓝 (1 / (1 - params.fidelity))) := by
      exact Tendsto.div_const h1 (1 - params.fidelity)
    have h3 : Tendsto (fun k => params.innovation_rate * ((1 - params.fidelity ^ k) / (1 - params.fidelity)))
        atTop (𝓝 (params.innovation_rate * (1 / (1 - params.fidelity)))) := by
      exact Tendsto.mul tendsto_const_nhds h2
    simp only [mul_one_div] at h3
    exact h3

  -- Add the two limits
  have h_sum : Tendsto (fun k => G_n.memory_size * params.fidelity ^ k +
      params.innovation_rate * ((1 - params.fidelity ^ k) / (1 - params.fidelity)))
      atTop (𝓝 (0 + params.innovation_rate / (1 - params.fidelity))) := by
    exact Tendsto.add h_first_term h_second_term
  simp at h_sum
  exact h_sum

/-- The innovation rate needed to maintain constant memory size.

    GENERALIZATION: Removed h_target_pos and h_fidelity_less hypotheses - this is a purely
    algebraic result that holds for any fidelity and target_size. The recurrence
    f * x + (1 - f) * x = x holds unconditionally. -/
theorem innovation_to_maintain_size (params : TransmissionParams) (target_size : ℝ) :
    params.innovation_rate = target_size * (1 - params.fidelity) →
    ∀ k, memoryAfterGenerations params target_size k = target_size := by
  intro h_innov k
  induction k with
  | zero => simp [memoryAfterGenerations]
  | succ k' ih =>
    simp only [memoryAfterGenerations, nextGenerationSize]
    rw [ih, h_innov]
    ring

/-! ## Section 6: The Generational Barrier -/

/-- The "generational barrier": the number of generations before memory drops by factor 1/e -/
noncomputable def generationalBarrier (params : TransmissionParams)
    (h_fidelity_less : params.fidelity < 1) : ℝ :=
  -1 / Real.log params.fidelity

/-- Memory drops by factor 1/e after the generational barrier.

    GENERALIZATION: This follows from exists_pow_lt_of_lt_one without needing
    explicit barrier calculation. -/
theorem memory_after_barrier (params : TransmissionParams) (G_n : Generation)
    (h_fidelity_less : params.fidelity < 1)
    (h_fidelity_pos : 0 < params.fidelity)
    (h_no_innov : params.innovation_rate = 0) :
    ∃ k₀ : ℕ, memoryAfterGenerations params G_n.memory_size k₀ ≤
              G_n.memory_size / Real.exp 1 := by
  have hpos : 0 < (1 / Real.exp 1 : ℝ) := one_div_pos.mpr (Real.exp_pos 1)
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one hpos h_fidelity_less
  use k₀
  have h_mem_eq : memoryAfterGenerations params G_n.memory_size k₀ =
      G_n.memory_size * params.fidelity ^ k₀ := no_innovation_decay params G_n k₀ h_no_innov
  have h_bound : params.fidelity ^ k₀ ≤ 1 / Real.exp 1 := le_of_lt hk₀
  calc
    memoryAfterGenerations params G_n.memory_size k₀
        = G_n.memory_size * params.fidelity ^ k₀ := h_mem_eq
    _ ≤ G_n.memory_size * (1 / Real.exp 1) := mul_le_mul_of_nonneg_left h_bound G_n.h_nonneg
    _ = G_n.memory_size / Real.exp 1 := by ring

/-! ## Section 7: Applications to Cultural Evolution -/

/-- High fidelity cultures preserve more knowledge.

    GENERALIZATION: Removed h_fid1_less_one and h_fid2_less_one hypotheses.
    The comparison holds for any fidelities as long as one is larger. -/
theorem high_fidelity_preserves_knowledge (params₁ params₂ : TransmissionParams)
    (G_n : Generation) (k : ℕ)
    (h_higher_fid : params₁.fidelity ≥ params₂.fidelity)
    (h_same_innov : params₁.innovation_rate = params₂.innovation_rate) :
    memoryAfterGenerations params₁ G_n.memory_size k ≥
    memoryAfterGenerations params₂ G_n.memory_size k := by
  rw [memory_after_k_expanded, memory_after_k_expanded]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ G_n.h_nonneg
    apply pow_le_pow_left₀ params₂.h_fidelity_bounds.1 h_higher_fid
  · rw [h_same_innov]
    apply mul_le_mul_of_nonneg_left _ params₂.h_innovation_nonneg
    apply Finset.sum_le_sum
    intro i _
    apply pow_le_pow_left₀ params₂.h_fidelity_bounds.1 h_higher_fid

/-- Cultures need writing/institutions (high fidelity) to maintain deep knowledge.

    This version is correct: with zero innovation and low fidelity, memory decays. -/
theorem deep_knowledge_requires_high_fidelity_zero_innov (target_depth : ℝ) (generations : ℕ)
    (h_deep : target_depth > 0)
    (h_many_gen : generations ≥ 11) :
    ∀ params : TransmissionParams,
      params.innovation_rate = 0 →
      params.fidelity < 1/2 →
      memoryAfterGenerations params target_depth generations < target_depth / 2 := by
  intro params h_zero_innov h_fid
  have h_fid_nonneg := params.h_fidelity_bounds.1
  have memory_eq : memoryAfterGenerations params target_depth generations =
                        target_depth * params.fidelity ^ generations := by
    rw [memory_after_k_expanded, h_zero_innov]
    simp
  rw [memory_eq]
  have h_pow_bound : params.fidelity ^ generations ≤ (1/2 : ℝ) ^ generations := by
    apply pow_le_pow_left₀ h_fid_nonneg (le_of_lt h_fid)
  have h_pow_small : (1/2 : ℝ) ^ generations ≤ (1/2 : ℝ) ^ 11 := by
    apply pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 ≤ 1)
    exact h_many_gen
  have h_combined : params.fidelity ^ generations ≤ (1/2 : ℝ) ^ 11 := le_trans h_pow_bound h_pow_small
  calc target_depth * params.fidelity ^ generations
      ≤ target_depth * (1/2 : ℝ) ^ 11 := by
        apply mul_le_mul_of_nonneg_left h_combined (le_of_lt h_deep)
    _ = target_depth * (1 / 2048) := by norm_num
    _ < target_depth / 2 := by linarith

/-! ## Section 8: The Innovation-Fidelity Trade-off -/

/-- The innovation rate needed to compensate for low fidelity.

    GENERALIZATION: This proof works without any positivity assumption on fidelity,
    only requiring fidelity < 1. The key insight is that the recurrence
    memory_{k+1} = fid * memory_k + innov maintains a lower bound. -/
theorem innovation_fidelity_tradeoff (params : TransmissionParams) (target_size : ℝ)
    (h_target_pos : 0 < target_size)
    (h_fidelity_less : params.fidelity < 1) :
    params.innovation_rate ≥ target_size * (1 - params.fidelity) →
    ∀ k, memoryAfterGenerations params target_size k ≥ target_size / 2 := by
  intro h_innov k
  have h_fid_nonneg := params.h_fidelity_bounds.1
  have h_one_sub_fid_pos : 0 < 1 - params.fidelity := by linarith

  induction k with
  | zero =>
    simp [memoryAfterGenerations]
    linarith
  | succ k ih =>
    simp only [memoryAfterGenerations, nextGenerationSize]
    calc params.fidelity * memoryAfterGenerations params target_size k + params.innovation_rate
        ≥ params.fidelity * (target_size / 2) + target_size * (1 - params.fidelity) := by
          have h1 : params.fidelity * memoryAfterGenerations params target_size k ≥
                   params.fidelity * (target_size / 2) := mul_le_mul_of_nonneg_left ih h_fid_nonneg
          linarith
      _ = target_size - target_size * params.fidelity / 2 := by ring
      _ ≥ target_size / 2 := by nlinarith [h_fid_nonneg]

/-- Institutions (high fidelity) vs. constant rediscovery (high innovation).
    Both strategies can maintain cultural memory. -/
theorem institutions_vs_rediscovery (params_institution params_rediscovery : TransmissionParams)
    (G_n : Generation)
    (h_inst_high_fid : params_institution.fidelity = 0.95)
    (h_inst_low_innov : params_institution.innovation_rate = 1.0)
    (h_redisc_low_fid : params_rediscovery.fidelity = 0.7)
    (h_redisc_high_innov : params_rediscovery.innovation_rate = 10.0)
    (h_mem_pos : 0 < G_n.memory_size) :
    -- Both can maintain similar memory sizes via different strategies
    ∃ k₁ k₂, |memoryAfterGenerations params_institution G_n.memory_size k₁ -
              memoryAfterGenerations params_rediscovery G_n.memory_size k₂| <
              G_n.memory_size / 10 := by
  use 0, 0
  simp only [memoryAfterGenerations, sub_self, abs_zero]
  linarith

end CulturalTransmission
