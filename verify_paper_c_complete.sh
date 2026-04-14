#!/bin/bash
echo "================================================================"
echo "PAPER C COMPREHENSIVE VERIFICATION"
echo "================================================================"
echo ""

echo "Step 1: Building all Paper C files..."
FILES=(
    "FormalAnthropology.PaperC_DiversityTheorems_Revision"
    "FormalAnthropology.PaperC_RevisionPlan_Theorems"
    "FormalAnthropology.PaperC_NewTheorems_D10"
    "FormalAnthropology.PaperC_NewTheorems_D11"
    "FormalAnthropology.PaperC_NewTheorems_D12"
    "FormalAnthropology.PaperC_NewTheorems_D13_D14"
    "FormalAnthropology.PaperC_NewTheorems_D15"
    "FormalAnthropology.PaperC_NewTheorems_D16_D20"
    "FormalAnthropology.PaperC_NewTheorems_D21_D26"
    "FormalAnthropology.PaperC_NewTheorems_D27_D29"
)

BUILD_SUCCESS=0
BUILD_FAIL=0

for file in "${FILES[@]}"; do
    if lake build "$file" > /dev/null 2>&1; then
        echo "  ✓ $file"
        ((BUILD_SUCCESS++))
    else
        echo "  ✗ $file FAILED"
        ((BUILD_FAIL++))
    fi
done

echo "  Build result: $BUILD_SUCCESS/${#FILES[@]} succeeded"
echo ""

echo "Step 2: Checking for sorry statements..."
SORRY_COUNT=$(grep -r "sorry" FormalAnthropology/PaperC*.lean 2>/dev/null | grep -v "Binary file" | grep -v "WITHOUT sorry" | wc -l)
if [ "$SORRY_COUNT" -eq 0 ]; then
    echo "  ✓ Zero sorry statements found"
else
    echo "  ✗ Found $SORRY_COUNT sorry statements:"
    grep -r "sorry" FormalAnthropology/PaperC*.lean | grep -v "Binary file" | grep -v "WITHOUT sorry"
fi
echo ""

echo "Step 3: Checking for custom axioms..."
AXIOM_COUNT=$(grep -r "^axiom " FormalAnthropology/PaperC*.lean 2>/dev/null | wc -l)
if [ "$AXIOM_COUNT" -eq 0 ]; then
    echo "  ✓ Zero custom axioms declared"
else
    echo "  ✗ Found $AXIOM_COUNT custom axiom declarations:"
    grep -r "^axiom " FormalAnthropology/PaperC*.lean
fi
echo ""

echo "Step 4: Counting theorems..."
THEOREM_COUNT=$(grep -r "^theorem\|^lemma" FormalAnthropology/PaperC*.lean 2>/dev/null | wc -l)
echo "  Total theorems/lemmas: $THEOREM_COUNT"
echo ""

echo "================================================================"
echo "VERDICT:"
if [ "$BUILD_FAIL" -eq 0 ] && [ "$SORRY_COUNT" -eq 0 ] && [ "$AXIOM_COUNT" -eq 0 ]; then
    echo "  ✅✅✅ ALL CHECKS PASSED ✅✅✅"
    echo ""
    echo "  All Paper C theorems are fully proven:"
    echo "  • $BUILD_SUCCESS files build successfully"
    echo "  • $THEOREM_COUNT theorems/lemmas proven"
    echo "  • Zero sorry statements"
    echo "  • Zero custom axioms"
    echo "  • Ready for publication"
else
    echo "  ⚠️ ISSUES FOUND:"
    [ "$BUILD_FAIL" -gt 0 ] && echo "    - $BUILD_FAIL files failed to build"
    [ "$SORRY_COUNT" -gt 0 ] && echo "    - $SORRY_COUNT sorry statements remain"
    [ "$AXIOM_COUNT" -gt 0 ] && echo "    - $AXIOM_COUNT custom axioms declared"
fi
echo "================================================================"
