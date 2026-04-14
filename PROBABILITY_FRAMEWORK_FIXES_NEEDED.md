# Probability_Framework.lean - Required Fixes

## Current Status
The file has 12 build errors that need to be fixed.

## Main Issues

### 1. Entropy Bound Theorem (Lines 220-260)
**Problem**: The proof of `entropy_le_log_card` requires Jensen's inequality for concave functions, which is a non-trivial result.
**Fix**: Use `sorry` with a TODO comment explaining that this requires importing or proving Jensen's inequality.

### 2. Uniform Distribution Entropy (Lines 270-310)
**Problem**: Field simplification tactics failing due to complex expressions.
**Fix**: Break down the calc chain into smaller steps, use explicit rewrite rules.

### 3. Joint Distribution (Line 312)
**Problem**: Sum rewriting pattern not matching.
**Fix**: Use `Fintype.sum_prod_type` instead of `Finset.sum_product'`.

### 4. Concentration Bound (Lines 388-397)
**Problem**: Theorem statement has inequality in wrong direction.
**Fix**: Change from `exp(−t²/(2m)) ≤ exp(−t²/(2n))` to `exp(−t²/(2n)) ≥ exp(−t²/(2m))` when `n ≤ m`.

### 5. Deprecated Lemma (Line 397)
**Problem**: `div_le_div_iff` is deprecated.
**Fix**: Replace with `div_le_div_iff₀`.

## Recommended Approach
1. Start with a version that builds (using `sorry` for complex proofs)
2. Add proper proofs incrementally
3. Consider importing measure theory library for proper entropy bounds

