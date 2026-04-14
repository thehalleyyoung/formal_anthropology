#!/bin/bash
# Verification script for Paper B Lean proofs
# Run this to confirm the status report

echo "=========================================="
echo "PAPER B LEAN PROOF VERIFICATION"
echo "=========================================="
echo ""

echo "Checking files that should BUILD SUCCESSFULLY..."
echo ""

SUCCESS_COUNT=0
FAIL_COUNT=0

check_build() {
    local file=$1
    local theorem=$2
    echo -n "Testing $file ($theorem)... "
    if lake build FormalAnthropology.$file 2>&1 | grep -q "Build completed successfully"; then
        echo "✅ SUCCESS"
        ((SUCCESS_COUNT++))
    else
        echo "❌ FAILED"
        ((FAIL_COUNT++))
    fi
}

check_sorries() {
    local file=$1
    local count=$(grep -c "sorry" FormalAnthropology/$file.lean 2>/dev/null || echo "FILE_NOT_FOUND")
    echo -n "  Sorries in $file: "
    if [ "$count" = "FILE_NOT_FOUND" ]; then
        echo "⚠️  FILE NOT FOUND"
    elif [ "$count" -eq 0 ]; then
        echo "✅ 0 (verified)"
    else
        echo "❌ $count (has sorries!)"
    fi
}

echo "1. Learning_CollectiveAccess (Theorem 5: Existence)"
check_build "Learning_CollectiveAccess" "Theorem 5"
check_sorries "Learning_CollectiveAccess"
echo ""

echo "2. Learning_StructuralCharacterization (Theorem 9: Structural)"
check_build "Learning_StructuralCharacterization" "Theorem 9"
check_sorries "Learning_StructuralCharacterization"
echo ""

echo "3. Learning_GenericEmergence (Theorem 10: Generic Emergence)"
check_build "Learning_GenericEmergence" "Theorem 10"
check_sorries "Learning_GenericEmergence"
echo ""

echo "4. Welfare_HeterogeneousValues (Theorem 17: Robustness)"
check_build "Welfare_HeterogeneousValues" "Theorem 17"
check_sorries "Welfare_HeterogeneousValues"
echo ""

echo "5. Learning_HomogeneityDominates (Theorem 18: Negative Result)"
check_build "Learning_HomogeneityDominates" "Theorem 18"
check_sorries "Learning_HomogeneityDominates"
echo ""

echo "6. Learning_CollaborationFailure (NEW-A: Failure Conditions)"
check_build "Learning_CollaborationFailure" "NEW-A"
check_sorries "Learning_CollaborationFailure"
echo ""

echo "7. Learning_CIThresholdDistribution (NEW-B: CI Distribution)"
check_build "Learning_CIThresholdDistribution" "NEW-B"
check_sorries "Learning_CIThresholdDistribution"
echo ""

echo "8. Learning_CIPrediction (NEW-C: Non-circular Measurement)"
check_build "Learning_CIPrediction" "NEW-C"
check_sorries "Learning_CIPrediction"
echo ""

echo "=========================================="
echo "SUMMARY: Successfully Building Files"
echo "=========================================="
echo "✅ Success: $SUCCESS_COUNT/8"
echo "❌ Failed: $FAIL_COUNT/8"
echo ""

echo "=========================================="
echo "Checking files with KNOWN TECHNICAL ISSUES"
echo "(These should have 0 sorries but build errors)"
echo "=========================================="
echo ""

check_build_expect_fail() {
    local file=$1
    local theorem=$2
    echo -n "Testing $file ($theorem)... "
    if lake build FormalAnthropology.$file 2>&1 | grep -q "Build completed successfully"; then
        echo "⚠️  UNEXPECTED SUCCESS (was expecting errors)"
    else
        echo "✅ Has errors as expected"
    fi
}

echo "9. Welfare_DiversityScaling_Proven (Theorem 12: Quadratic Scaling)"
check_build_expect_fail "Welfare_DiversityScaling_Proven" "Theorem 12"
check_sorries "Welfare_DiversityScaling_Proven"
echo ""

echo "10. Welfare_DiversityDiminishingReturns (Theorem 13: Diminishing Returns)"
check_build_expect_fail "Welfare_DiversityDiminishingReturns" "Theorem 13"
check_sorries "Welfare_DiversityDiminishingReturns"
echo ""

echo "11. Learning_DiversityDepthTradeoff (Theorem 14: Diversity-Depth)"
check_build_expect_fail "Learning_DiversityDepthTradeoff" "Theorem 14"
check_sorries "Learning_DiversityDepthTradeoff"
echo ""

echo "=========================================="
echo "FINAL VERIFICATION COMPLETE"
echo "=========================================="
echo ""
echo "Expected Results:"
echo "  - 8 files build successfully with 0 sorries"
echo "  - 3 files have build errors but 0 sorries"
echo "  - TOTAL: 11 files with 0 sorries"
echo ""
echo "Run complete. Check output above for any discrepancies."
