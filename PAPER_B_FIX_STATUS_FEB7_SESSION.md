# Paper B Lean Proof Fixing Session - February 7, 2026

## Session Goal
Fix all Lean proofs for diversity_b_paper revision plan with ZERO sorries and ZERO errors.

## Current Status

### ✅ COMPLETE - Core Verified Theorems (Already Working)
1. **Learning_ComplementarityIndex** - Builds successfully ✓
2. **Learning_Theorem40_ZeroValueDiversity** - Builds successfully ✓  
3. **Learning_DiversityComputationNPHard** - Builds successfully ✓

### ✅ COMPLETE - New Diversity Theorems (Fixed This Session)
4. **Learning_DiversityNecessityCharacterization** - FIXED ✓
   - Issue: Decidability problems with `if` statements on Sets
   - Solution: Changed to propositional `hasDiversity` definition
   - Status: Builds with zero sorries ✓

5. **PaperB_DiversityValueScaling** - FIXED ✓
   - Issue: Complex ite/dite decidability, epsilon-based definitions
   - Solution: Simplified to propositional `emergenceHasValue`
   - Status: Builds with zero sorries ✓

### 🔧 IN PROGRESS - Remaining Theorems to Fix

6. **PaperB_DiversityAbilityTradeoff** - Needs fixing
   - Errors: calc chain issues, type mismatches
   - Lines: 84, 86, 104
   - Priority: HIGH (core Hong-Page result)

7. **PaperB_DiversityRobustness** - Needs fixing
   - Errors: unexpected 'variable' token, type mismatches  
   - Lines: 19, 37
   - Priority: MEDIUM

8. **PaperB_DiversityExploration** - Needs fixing
   - Errors: noncomputable def, type mismatches, apply failed
   - Lines: 36, 63, 93
   - Priority: MEDIUM

9. **PaperB_MarketConcentration** - Needs fixing
   - Errors: failed to synthesize, split_ifs issues, rewrite failures
   - Lines: 109, 172, 222
   - Priority: MEDIUM

## Key Lessons Learned

### Pattern 1: Decidability Issues
**Problem:** `if` statements on Sets require Decidable instances that don't exist.

**Solutions:**
- Use `noncomputable def` with Classical decidability
- Convert to propositional definitions (preferred)
- Use `by_cases` in proofs instead of `split_ifs`

### Pattern 2: Calc Chain Errors
**Problem:** `calc` blocks produce "unsolved goals" or type mismatches.

**Solutions:**
- Ensure each step is properly justified
- Use explicit rewrites instead of calc when complex
- Check that intermediate steps have correct types

### Pattern 3: Type Mismatches
**Problem:** Application type mismatches, usually from wrong hypothesis types.

**Solutions:**
- Check that assumptions match what tactics expect
- Use `have` to massage types before applying
- Simplify complex nested structures

## Next Steps

1. Fix PaperB_DiversityAbilityTradeoff (highest priority)
2. Fix remaining 3 files using same patterns
3. Run comprehensive build check
4. Verify NO sorries in ANY file
5. Document axiom usage with #print axioms

## Success Criteria

- [ ] All 9 theorem files build successfully
- [ ] Zero `sorry` statements in any file
- [ ] Only standard Mathlib axioms used (Classical.choice, propext, Quot.sound)
- [ ] Can run: `lake build FormalAnthropology` without errors
- [ ] Paper's lean_appendix.tex accurately reflects verification status

## Timeline Estimate

- Remaining 4 files: 5-10 turns
- Verification & documentation: 2-3 turns
- **Total: 7-13 turns remaining**

