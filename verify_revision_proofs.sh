#!/bin/bash
# Comprehensive verification of Paper B revision proofs

echo "=========================================="
echo "Paper B Revision: Lean Proof Verification"
echo "=========================================="
echo ""

# Files with previous build errors (Priority 1)
BUILD_ERROR_FILES=(
    "FormalAnthropology.Learning_CollectiveAccess"
    "FormalAnthropology.Welfare_DiversityScaling_Proven"
    "FormalAnthropology.Welfare_DiversityDiminishingReturns"
    "FormalAnthropology.Learning_DiversityDepthTradeoff"
)

# Previously unformalized theorems (Priority 2)
NEW_THEOREM_FILES=(
    "FormalAnthropology.Learning_StructuralCharacterization"
    "FormalAnthropology.Learning_GenericEmergence"
    "FormalAnthropology.Welfare_HeterogeneousValues"
    "FormalAnthropology.Learning_HomogeneityDominates"
    "FormalAnthropology.Learning_CollaborationFailure"
    "FormalAnthropology.Learning_CIThresholdDistribution"
    "FormalAnthropology.Learning_CIPrediction"
)

ALL_FILES=("${BUILD_ERROR_FILES[@]}" "${NEW_THEOREM_FILES[@]}")

SUCCESS_COUNT=0
FAILURE_COUNT=0
FAILED_FILES=()

echo "Testing ${#ALL_FILES[@]} critical theorem files..."
echo ""

for file in "${ALL_FILES[@]}"; do
    echo -n "Building $file ... "
    if lake build "$file" > /dev/null 2>&1; then
        echo "✓ SUCCESS"
        ((SUCCESS_COUNT++))
    else
        echo "✗ FAILED"
        ((FAILURE_COUNT++))
        FAILED_FILES+=("$file")
    fi
done

echo ""
echo "=========================================="
echo "RESULTS:"
echo "=========================================="
echo "Successfully built: $SUCCESS_COUNT / ${#ALL_FILES[@]}"
echo "Failed to build:    $FAILURE_COUNT / ${#ALL_FILES[@]}"

if [ $FAILURE_COUNT -eq 0 ]; then
    echo ""
    echo "✓✓✓ ALL PROOFS BUILD SUCCESSFULLY! ✓✓✓"
    echo ""
    echo "Now checking for sorries..."
    echo ""
    
    SORRY_COUNT=0
    for file in "${ALL_FILES[@]}"; do
        lean_file="${file//FormalAnthropology./FormalAnthropology/}.lean"
        sorries=$(grep -c "sorry" "$lean_file" 2>/dev/null || echo 0)
        if [ "$sorries" -gt 0 ]; then
            echo "⚠ $lean_file has $sorries sorry(ies)"
            ((SORRY_COUNT++))
        fi
    done
    
    if [ $SORRY_COUNT -eq 0 ]; then
        echo "✓ ZERO SORRIES in all files!"
        echo ""
        echo "=========================================="
        echo "🎉 MISSION ACCOMPLISHED! 🎉"
        echo "=========================================="
        echo "All Paper B revision proofs:"
        echo "  • Build successfully (zero errors)"
        echo "  • Have zero sorries"
        echo "  • Are ready for paper submission"
        echo ""
        exit 0
    else
        echo ""
        echo "⚠ Found sorries in $SORRY_COUNT file(s)"
        exit 1
    fi
else
    echo ""
    echo "The following files failed to build:"
    for file in "${FAILED_FILES[@]}"; do
        echo "  • $file"
    done
    echo ""
    echo "Showing detailed errors for first failed file..."
    echo ""
    lake build "${FAILED_FILES[0]}" 2>&1 | tail -50
    exit 1
fi
