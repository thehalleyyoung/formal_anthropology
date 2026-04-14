# Quick Start Guide: Completing Revision Plan Proofs

## TL;DR Status

✅ **2 theorems COMPLETE** (0 sorries, builds successfully)  
⚠️  **6 theorems NEED WORK** (37 sorries remaining)  
⏱️  **Estimated time**: 33-48 hours to complete all

## Files to Work On (Priority Order)

### 🔥 URGENT - Fix Build (1-2 hours)
```bash
# This file has NO sorries but won't build due to type errors
FormalAnthropology/Learning_CircuitDepthTightness.lean
# Errors at lines 74 and 143 - just formatting issues
```

### 🎯 P0 - Critical for Reviewer (14-20 hours)
```bash
# Addresses reviewer's "are O(log n) bounds tight?" question
FormalAnthropology/Learning_ResolutionDepthTightness.lean  # 3 sorries, 6-8 hrs

# Core positioning theorem - when is diversity > 1 necessary?
FormalAnthropology/Learning_DiversityNecessityComplete.lean  # 10 sorries, 8-12 hrs

# Addresses reviewer's "is max-arity factor tight?" question  
FormalAnthropology/Learning_ASTMaxArityTightness.lean  # 6 sorries, 5-7 hrs
```

### 📊 P1 - Supporting Results (11-19 hours)
```bash
FormalAnthropology/Learning_DiversityExpressivenessExplosion.lean  # 2 sorries, 3-4 hrs
FormalAnthropology/Learning_GreedyRuntimeBound.lean  # 5 sorries, 4-6 hrs
FormalAnthropology/Learning_TractableCasesExplicit.lean  # 11 sorries, 6-9 hrs
```

## Quick Commands

### Check Sorry Count
```bash
cd formal_anthropology
grep -r "sorry" FormalAnthropology/Learning_Diversity*.lean \
  FormalAnthropology/Learning_Resolution*.lean \
  FormalAnthropology/Learning_AST*.lean \
  FormalAnthropology/Learning_Greedy*.lean \
  FormalAnthropology/Learning_Tractable*.lean \
  FormalAnthropology/Learning_Circuit*.lean | wc -l
```

### Build Specific File
```bash
cd formal_anthropology
lake build FormalAnthropology.Learning_DiversityIndependence  # Example
```

### Build All Revision Files
```bash
cd formal_anthropology
./build_revision_proofs.sh  # If script exists
# OR manually:
lake build FormalAnthropology.Learning_DiversityIndependence
lake build FormalAnthropology.Learning_CircuitDepthTightness
# ... etc for each file
```

### Check for Axioms
```bash
cd formal_anthropology
grep -r "axiom" FormalAnthropology/Learning_*.lean | grep -v "-- axiom" | grep -v "/--"
```

## What's Already Done

### ✅ COMPLETE: DiversityIndependence
**File**: `Learning_DiversityIndependence.lean`  
**Status**: 0 sorries, builds perfectly  
**What it proves**: Diversity and depth are orthogonal dimensions
- Wide-but-shallow systems exist (depth=1, diversity=n)
- Deep-but-narrow systems exist (depth=n, diversity=1)
- For any (depth, diversity) pair, a system exists

**Key theorems**:
- `diversity_independent_of_depth`
- `depth_does_not_determine_diversity`
- `diversity_does_not_determine_depth`
- `exists_system_with_parameters`

### ✅ NEARLY COMPLETE: CircuitDepthTightness
**File**: `Learning_CircuitDepthTightness.lean`  
**Status**: 0 sorries, 2 minor build errors  
**What it proves**: Circuit depth correspondence constants (±O(1)) are optimal
- Lower bound constant = 0 (AND chains achieve it)
- Upper bound constant = 1 (independent subcircuits achieve it)
- These are provably optimal, cannot be improved

**Why it matters**: Directly addresses reviewer's tightness concern

## How to Complete a File

### General Strategy
1. **Read the sorry context**: Understand what needs to be proven
2. **Check for helper lemmas**: Many are already defined above
3. **Use standard tactics**:
   - `omega` for arithmetic
   - `simp` for simplification
   - `linarith` for linear arithmetic
   - `ring` for ring arithmetic
   - `exact` when you have exactly what's needed
4. **Build frequently**: `lake build FormalAnthropology.YourFile`
5. **Check for new errors**: Fix type errors as they appear

### Common Sorry Patterns

#### Type 1: Arithmetic (easiest, ~30 min each)
```lean
sorry  -- Arithmetic: 2^(2^k - k) ≥ 2 * 2^k for k ≥ 3
```
**Solution**: Break down with intermediate `have` statements, use `omega` or `ring`

#### Type 2: Closure Monotonicity (~1 hour each)
```lean
sorry  -- closure seed G₁ ⊆ closure seed G₂
```
**Solution**: Use `closure_monotone` helper lemma if available, or induct on closure iteration

#### Type 3: Diversity Bounds (~2 hours each)
```lean
sorry  -- diversity ≤ k because single generator reaches target
```
**Solution**: Use helper lemmas like `diversity_le_one_of_singleton`, apply `Nat.sInf_le`

#### Type 4: Algorithm Analysis (~2-3 hours each)
```lean
sorry  -- Runtime bound: iterations × cost_per_iteration
```
**Solution**: Count iterations, prove termination, multiply bounds

## Tips for Success

### DO:
- ✅ Start with P0 files (reviewer's main concerns)
- ✅ Fix `CircuitDepthTightness` first (quick win)
- ✅ Build after each sorry completion
- ✅ Use helper lemmas that are already defined
- ✅ Add intermediate `have` statements to break down complex proofs
- ✅ Document your progress

### DON'T:
- ❌ Add new axioms for things that are actually theorems
- ❌ Leave commented-out sorry statements
- ❌ Skip building - catch errors early
- ❌ Try to complete all files at once - focus on one at a time

## Expected Timeline

### Week 1 (16-20 hours)
- Fix CircuitDepthTightness (2 hrs)
- Complete ResolutionDepthTightness (6-8 hrs)
- Complete DiversityNecessityComplete (8-12 hrs)

### Week 2 (17-21 hours)
- Complete ASTMaxArityTightness (5-7 hrs)
- Complete DiversityExpressivenessExplosion (3-4 hrs)
- Complete GreedyRuntimeBound (4-6 hrs)
- Complete TractableCasesExplicit (6-9 hrs)

### Week 3 (Buffer)
- Final debugging
- Build verification
- Documentation

## Success Criteria

### Before Submission, Must Have:
- [ ] All 8 theorem files build successfully
- [ ] 0 sorry statements across all files
- [ ] Only acceptable axioms (Classical.choice, propext, Quot.sound, + clearly documented domain axioms)
- [ ] Build verification script runs cleanly
- [ ] Documentation updated in lean_appendix.tex

### How to Verify:
```bash
cd formal_anthropology

# Check sorries
./check_revision_sorries.sh  # Should output: 0 sorries

# Build all
./build_revision_proofs.sh  # Should output: All files SUCCESS

# Check axioms
grep -r "axiom" FormalAnthropology/Learning_*.lean | wc -l  # Should be reasonable count
```

## Getting Help

### If Stuck on a Proof:
1. Check `REVISION_THEOREMS_STATUS_REPORT.md` for proof strategies
2. Look at similar completed proofs in other files
3. Check Mathlib documentation for relevant lemmas
4. Break the proof into smaller lemmas
5. Consider using `sorry` temporarily to check overall structure builds

### Common Build Errors:
- **"type mismatch"**: Check that terms match expected types, use `: Type` annotations
- **"unknown identifier"**: Import missing, or typo in name
- **"simp made no progress"**: Try `simp only` with specific lemmas, or use `rw` instead
- **"no goals to be solved"**: You've already completed the proof, remove extra tactics

## Quick Reference: File Contents

| File | Main Theorem | What It Proves |
|------|--------------|----------------|
| DiversityIndependence | `diversity_independent_of_depth` | Diversity ⊥ depth |
| CircuitDepthTightness | `circuit_depth_constants_optimal` | ±O(1) tight, constants 0,1 |
| ResolutionDepthTightness | `resolution_depth_log_factor_tight` | O(log n) tight |
| ASTMaxArityTightness | `ast_max_arity_necessary` | Max-arity factor tight |
| DiversityNecessityComplete | `diversity_necessary_iff_complementary` | When diversity > 1? |
| DiversityExpressivenessExplosion | `diversity_expressiveness_exponential` | Each generator can double expressiveness |
| GreedyRuntimeBound | `greedy_diversity_runtime_bound` | O(\|G\|² × max_closure) |
| TractableCasesExplicit | `tractable_special_cases_explicit` | 4 tractable cases with algorithms |

## Contact/Notes

This guide created: February 7, 2026
Last build check: February 7, 2026
Next milestone: Complete P0 theorems (ResolutionDepth, DiversityNecessity, ASTMaxArity)

For detailed proof strategies, see: `REVISION_THEOREMS_STATUS_REPORT.md`
For overall revision plan, see: `../diversity_a_paper/REVISION_PLAN.md`
