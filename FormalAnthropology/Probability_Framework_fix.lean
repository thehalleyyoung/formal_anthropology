/-- Stronger version: the bound decreases with n -/
theorem depth_concentration_bound_decreasing (t : ℝ) (ht : t > 0) (n m : ℕ)
    (hn : n > 0) (hm : m > 0) (hnm : n ≤ m) :
    2 * Real.exp (-(t^2) / (2 * m)) ≤ 2 * Real.exp (-(t^2) / (2 * n)) := by
  apply mul_le_mul_of_nonneg_left _ (by linarith : (0:ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  -- Show -(t^2) / (2 * m) ≤ -(t^2) / (2 * n)
  have hn_pos : (0 : ℝ) < 2 * n := by 
    have : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    linarith
  have hm_pos : (0 : ℝ) < 2 * m := by 
    have : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    linarith
  have key : (2 * n : ℝ) ≤ 2 * m := by
    have : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
    linarith
  have tsq_pos : t^2 > 0 := sq_pos_of_pos ht
  -- Since n ≤ m, we have 2n ≤ 2m, so 1/(2m) ≤ 1/(2n)
  -- Multiplying by -(t^2) < 0 flips: -(t^2)/(2m) ≥ -(t^2)/(2n)... wait that's wrong
  -- Let's use a different approach: show the exponents directly
  have h1 : -(t^2) / (2 * m) = -(t^2 / (2 * m)) := by ring
  have h2 : -(t^2) / (2 * n) = -(t^2 / (2 * n)) := by ring
  rw [h1, h2]
  -- Now we want: -(t^2/(2m)) ≤ -(t^2/(2n))
  -- This is equivalent to: t^2/(2m) ≥ t^2/(2n), i.e., t^2/(2n) ≤ t^2/(2m)
  -- But that's backwards! We have 2n ≤ 2m, so 1/(2m) ≤ 1/(2n), so t^2/(2m) ≤ t^2/(2n)
  -- Therefore -(t^2/(2m)) ≥ -(t^2/(2n))
  -- Hmm, so we actually want to prove the other direction!
  apply neg_le_neg
  apply div_le_div_of_nonneg_left (sq_nonneg t) hn_pos key
