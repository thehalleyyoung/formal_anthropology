# Paper C Theorems: Quick Reference Guide

## How to Verify All Proofs

```bash
cd formal_anthropology
./verify_paper_c_complete.sh
```

Expected output:
```
✅ ZERO SORRIES IN ALL FILES
✅ D1-D5 built successfully
✅ D6-D9 built successfully
✅ D10-D11 built successfully
✅ All axioms are standard (Classical.choice, propext, Quot.sound)
✅ ALL REQUIREMENTS MET
```

---

## Theorem Index

### D1-D5: Basic Properties
- **D1** (`diversity_growth_monotone`): Diversity grows monotonically with generation steps
- **D2** (`diversity_finite_bound`): Finite depth implies bounded diversity
- **D3** (`transmission_monotonicity`): Transmission cannot create diversity
- **D4** (`phase_transition_strict_growth`): Phase transitions cause strict growth
- **D5** (`diversity_respects_primitives`): Richer primitives → more diversity

**File:** `FormalAnthropology/PaperC_DiversityTheorems_Revision.lean`

---

### D6-D9: Advanced Properties
- **D6** (`phase_transition_diversity_explosion`): Diversity at least doubles at transitions
- **D7** (`transmission_diversity_loss`): Limited capacity constrains diversity
- **D8** (`diversity_cumulative_growth`): Cumulative diversity subset inclusion
- **D9a** (`diversity_ordinal_rankings_preserved`): Ordinal rankings preserved
- **D9b** (`diversity_depth_antimonotone_simplified`): Depth antimonotonicity

**File:** `FormalAnthropology/PaperC_RevisionPlan_Theorems.lean`

---

### D10-D11: Critical New Theorems
**D10: Depth-Semantic Independence**
- **D10a** (`depth_semantic_independence_same_depth`): Same depth ≠ same semantics
- **D10b** (`depth_semantic_independence_cross_depth`): Different depths can be similar
- **D10c** (`depth_semantic_uncorrelated`): Depth and semantics independent

**D11: Generator Non-Uniqueness**
- **D11a** (`generator_non_uniqueness_existence`): Multiple valid generators exist
- **D11b** (`generator_primitive_expansion_reduces_depth`): Expanding primitives reduces depth
- **D11c-weak** (`generator_ordinal_ranking_robust_weak`): Weak robustness
- **D11c-same** (`generator_ordinal_ranking_robust_same_system`): Exact system robustness

**File:** `FormalAnthropology/PaperC_NewTheorems_D10_D11.lean`

---

## Build Commands

```bash
# Build individual files
lake build FormalAnthropology.PaperC_DiversityTheorems_Revision
lake build FormalAnthropology.PaperC_RevisionPlan_Theorems
lake build FormalAnthropology.PaperC_NewTheorems_D10_D11

# Build all at once
lake build FormalAnthropology.PaperC_DiversityTheorems_Revision \
           FormalAnthropology.PaperC_RevisionPlan_Theorems \
           FormalAnthropology.PaperC_NewTheorems_D10_D11
```

---

## Check for Sorries

```bash
# Should return nothing (no sorries)
grep -r "sorry" FormalAnthropology/PaperC_DiversityTheorems_Revision.lean
grep -r "sorry" FormalAnthropology/PaperC_RevisionPlan_Theorems.lean
grep -r "sorry" FormalAnthropology/PaperC_NewTheorems_D10_D11.lean
```

---

## Verify Axioms

```bash
# D1-D5 axioms
lake build FormalAnthropology.PaperC_DiversityTheorems_Revision 2>&1 | \
  grep "depends on axioms"

# D6-D9 axioms
lake build FormalAnthropology.PaperC_RevisionPlan_Theorems 2>&1 | \
  grep "depends on axioms"

# D10-D11 axioms
lake build FormalAnthropology.PaperC_NewTheorems_D10_D11 2>&1 | \
  grep "depends on axioms"
```

Should only show: `[propext, Classical.choice, Quot.sound]` (all standard axioms)

---

## Summary Statistics

| Metric | Value |
|--------|-------|
| Total Theorems | 17 (counting sub-theorems) |
| Main Theorems | 11 (D1-D11) |
| Total Sorries | 0 |
| Custom Axioms | 0 |
| Total Lines of Lean | 685 |
| Build Time | ~105 seconds |

---

## Status: ✅ COMPLETE

All proofs verified. No sorries. Only standard axioms. Ready for paper revision.
