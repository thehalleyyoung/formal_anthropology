#!/bin/bash
# Verification script for Paper C Revision Lean proofs

echo "========================================="
echo "Paper C Revision: Lean Proof Verification"
echo "========================================="
echo ""

echo "1. Checking for sorries in Learning_PaperC_Revision.lean..."
SORRY_COUNT=$(grep -c "sorry" FormalAnthropology/Learning_PaperC_Revision.lean || echo "0")
echo "   Sorry count: $SORRY_COUNT"
if [ "$SORRY_COUNT" -eq "0" ]; then
    echo "   ✅ PASS: Zero sorries found"
else
    echo "   ❌ FAIL: Sorries detected"
    exit 1
fi
echo ""

echo "2. Building Learning_PaperC_Revision.lean..."
if lake build FormalAnthropology.Learning_PaperC_Revision > /tmp/build.log 2>&1; then
    echo "   ✅ PASS: Build successful"
else
    echo "   ❌ FAIL: Build failed"
    tail -20 /tmp/build.log
    exit 1
fi
echo ""

echo "3. Counting theorems in file..."
THEOREM_COUNT=$(grep -c "^theorem " FormalAnthropology/Learning_PaperC_Revision.lean)
echo "   Theorem count: $THEOREM_COUNT"
if [ "$THEOREM_COUNT" -ge "9" ]; then
    echo "   ✅ PASS: At least 9 theorems found"
else
    echo "   ❌ FAIL: Less than 9 theorems"
    exit 1
fi
echo ""

echo "4. Verifying import in FormalAnthropology.lean..."
if grep -q "Learning_PaperC_Revision" FormalAnthropology.lean; then
    echo "   ✅ PASS: Import found"
else
    echo "   ❌ FAIL: Import missing"
    exit 1
fi
echo ""

echo "========================================="
echo "✅ ALL CHECKS PASSED"
echo "========================================="
echo ""
echo "Summary:"
echo "- 9 theorems proven"
echo "- 0 sorries"
echo "- Builds successfully"
echo "- Integrated into FormalAnthropology"
echo ""
echo "Theorems cover:"
echo "  Suite 1: Generator Robustness (3 theorems)"
echo "  Suite 2: Empirical Validation (2 theorems)"
echo "  Suite 3: Constraint-as-Resource (2 theorems)"
echo "  Suite 4: Computational Complexity (2 theorems)"
