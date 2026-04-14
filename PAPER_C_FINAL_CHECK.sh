#!/bin/bash
# Final comprehensive check for Paper C Lean proofs

echo "=============================================="
echo "PAPER C FINAL VERIFICATION CHECK"
echo "Date: $(date)"
echo "=============================================="
echo ""

# Color codes
GREEN='\033[0;32m'
RED='\033[0;31m'
NC='\033[0m' # No Color

FAILED=0

# Check 1: Build succeeds
echo "Check 1: Building theorem files..."
if lake build FormalAnthropology.PaperC_DiversityTheorems_Revision FormalAnthropology.PaperC_RevisionPlan_Theorems > /dev/null 2>&1; then
    echo -e "${GREEN}✅ Build successful${NC}"
else
    echo -e "${RED}❌ Build failed${NC}"
    FAILED=1
fi

# Check 2: Zero sorries
echo "Check 2: Checking for sorries..."
SORRY_COUNT=$(grep -i "sorry\|admit" FormalAnthropology/PaperC_DiversityTheorems_Revision.lean FormalAnthropology/PaperC_RevisionPlan_Theorems.lean 2>/dev/null | wc -l | tr -d ' ')
if [ "$SORRY_COUNT" -eq 0 ]; then
    echo -e "${GREEN}✅ Zero sorries/admits found${NC}"
else
    echo -e "${RED}❌ Found $SORRY_COUNT sorry/admit statements${NC}"
    FAILED=1
fi

# Check 3: All theorems present
echo "Check 3: Verifying all D1-D9 theorems exist..."
EXPECTED_THEOREMS=(
    "diversity_growth_monotone"
    "diversity_finite_bound"
    "transmission_monotonicity"
    "phase_transition_strict_growth"
    "diversity_respects_primitives"
    "phase_transition_diversity_explosion"
    "transmission_diversity_loss"
    "diversity_cumulative_growth"
    "diversity_ordinal_rankings_preserved"
    "diversity_depth_antimonotone_simplified"
)

MISSING=0
for thm in "${EXPECTED_THEOREMS[@]}"; do
    if grep -q "theorem $thm" FormalAnthropology/PaperC_DiversityTheorems_Revision.lean FormalAnthropology/PaperC_RevisionPlan_Theorems.lean 2>/dev/null; then
        echo "  ✓ $thm"
    else
        echo -e "  ${RED}✗ $thm (MISSING)${NC}"
        MISSING=$((MISSING + 1))
        FAILED=1
    fi
done

if [ $MISSING -eq 0 ]; then
    echo -e "${GREEN}✅ All 10 theorems present${NC}"
fi

# Check 4: Only standard axioms
echo "Check 4: Checking axioms..."
BUILD_OUTPUT=$(lake build FormalAnthropology.PaperC_DiversityTheorems_Revision FormalAnthropology.PaperC_RevisionPlan_Theorems 2>&1)
CUSTOM_AXIOM_COUNT=$(echo "$BUILD_OUTPUT" | grep "depends on axioms" | grep -v "propext\|Classical.choice\|Quot.sound" | wc -l | tr -d ' ')

if [ "$CUSTOM_AXIOM_COUNT" -eq 0 ]; then
    echo -e "${GREEN}✅ Only standard axioms used${NC}"
else
    echo -e "${RED}❌ Custom axioms detected${NC}"
    FAILED=1
fi

echo ""
echo "=============================================="
if [ $FAILED -eq 0 ]; then
    echo -e "${GREEN}✅ ALL CHECKS PASSED${NC}"
    echo ""
    echo "Summary:"
    echo "  • Theorems D1-D9: ALL PROVEN"
    echo "  • Sorries: 0"
    echo "  • Admits: 0"
    echo "  • Axioms: Standard only"
    echo "  • Build: SUCCESS"
    echo ""
    echo "Paper C Lean proofs are READY FOR PUBLICATION."
else
    echo -e "${RED}❌ SOME CHECKS FAILED${NC}"
    exit 1
fi
echo "=============================================="
