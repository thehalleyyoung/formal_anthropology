#!/bin/bash
# Verification script for Paper B Lean proofs
# Run this to confirm all claimed "fully verified" theorems build successfully

echo "=========================================="
echo "Paper B Lean Proof Verification"
echo "=========================================="
echo ""

cd "$(dirname "$0")"

# Color codes
GREEN='\033[0;32m'
RED='\033[0;31m'
NC='\033[0m' # No Color

PASS=0
FAIL=0

check_file() {
    local name=$1
    echo -n "Testing $name... "
    if lake build "FormalAnthropology.$name" 2>&1 | grep -q "Build completed successfully"; then
        echo -e "${GREEN}✅ PASS${NC}"
        ((PASS++))
        return 0
    else
        echo -e "${RED}❌ FAIL${NC}"
        ((FAIL++))
        return 1
    fi
}

echo "=== Core Theorems (3 files) ==="
check_file "Learning_ComplementarityIndex"
check_file "Learning_Theorem40_ZeroValueDiversity"
check_file "Learning_DiversityComputationNPHard"
echo ""

echo "=== New Diversity Theorems (5 files) ==="
check_file "PaperB_DiversityAbilityTradeoff"
check_file "PaperB_DiversityRobustness"
check_file "PaperB_MarketConcentration"
check_file "PaperB_DiversityExploration"
check_file "PaperB_DiversityValueScaling"
echo ""

echo "=== Support Files (1 file) ==="
check_file "PaperB_CoreTheorems"
echo ""

echo "=========================================="
echo "RESULTS: $PASS passed, $FAIL failed"
echo "=========================================="
echo ""

if [ $FAIL -eq 0 ]; then
    echo -e "${GREEN}✅ ALL TESTS PASSED${NC}"
    echo "All theorems claimed as 'fully verified' build successfully."
    echo ""
    echo "Checking for sorries..."
    TOTAL_SORRIES=0
    for file in Learning_ComplementarityIndex Learning_Theorem40_ZeroValueDiversity Learning_DiversityComputationNPHard PaperB_DiversityAbilityTradeoff PaperB_DiversityRobustness PaperB_MarketConcentration PaperB_DiversityExploration PaperB_DiversityValueScaling PaperB_CoreTheorems; do
        COUNT=$(grep -o "sorry" "FormalAnthropology/$file.lean" 2>/dev/null | wc -l | tr -d ' ')
        TOTAL_SORRIES=$((TOTAL_SORRIES + COUNT))
    done
    echo "Total sorries in verified files: $TOTAL_SORRIES"
    if [ $TOTAL_SORRIES -eq 0 ]; then
        echo -e "${GREEN}✅ ZERO SORRIES CONFIRMED${NC}"
    else
        echo -e "${RED}❌ WARNING: Found $TOTAL_SORRIES sorries${NC}"
    fi
    exit 0
else
    echo -e "${RED}❌ SOME TESTS FAILED${NC}"
    exit 1
fi
