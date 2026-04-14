import Mathlib.Algebra.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic

open BigOperators Filter Topology

lemma geom_converge_helper (r : ℝ) (hr1 : r ≠ 1) (hr2 : 0 ≤ r) (hr3 : r < 1) (ε : ℝ) (hε : 0 < ε) : 
    ∃ N, ∀ n ≥ N, |(∑ i in Finset.range n, r ^ i) - 1 / (1 - r)| < ε := by
  have h_formula : ∀ n : ℕ, (∑ i in Finset.range n, r ^ i) = (r ^ n - 1) / (r - 1) := by
    intro n; exact geom_sum_eq hr1 n
  have h_one_sub_r_pos : 0 < 1 - r := by linarith
  have h_one_sub_r_ne : 1 - r ≠ 0 := ne_of_gt h_one_sub_r_pos
  have h_r_sub_one_ne : r - 1 ≠ 0 := by linarith
  have h_abs_r : |r| < 1 := by rw [abs_of_nonneg hr2]; exact hr3
  have h_pow_zero : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) := by
    rw [tendsto_pow_atTop_nhds_zero_iff]; exact h_abs_r
  rw [Metric.tendsto_atTop] at h_pow_zero
  have h_eps_adj : 0 < ε * (1 - r) := by positivity
  obtain ⟨N, hN⟩ := h_pow_zero (ε * (1 - r)) h_eps_adj
  use N
  intro n hn
  rw [h_formula n]
  have h_key : (r ^ n - 1) / (r - 1) - 1 / (1 - r) = r ^ n / (r - 1) := by
    field_simp
    ring
  rw [h_key]
  have h_pow_nonneg : 0 ≤ r ^ n := pow_nonneg hr2 n
  rw [abs_div, abs_of_nonneg h_pow_nonneg, abs_of_neg (by linarith : r - 1 < 0)]
  calc r ^ n / (-(r - 1))
      = r ^ n / (1 - r) := by ring_nf
    _ < ε := by
        rw [div_lt_iff₀ h_one_sub_r_pos]
        have : dist (r ^ n) 0 < ε * (1 - r) := hN n hn
        rw [Real.dist_eq, sub_zero, abs_of_nonneg h_pow_nonneg] at this
        exact this
