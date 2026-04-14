#!/bin/bash
# Verification script for Paper B revision plan proofs

echo "=== VERIFYING PAPER B REVISION PLAN PROOFS ==="
echo ""

# Files from REVISION_PLAN.md that need fixing:
echo "Priority 1: Fix Build Errors"
echo "============================="

echo -n "1. Theorem 5 (Learning_CollectiveAccess.lean): "
lake build FormalAnthropology.Learning_CollectiveAccess 2>&1 | grep -q "Build completed" && echo "✓ PASS" || echo "✗ FAIL"

echo -n "2. Theorem 12 (Welfare_DiversityScaling_Proven.lean): "
lake build FormalAnthropology.Welfare_DiversityScaling_Proven 2>&1 | grep -q "Build completed" && echo "✓ PASS" || echo "✗ FAIL"

echo -n "3. Theorem 13 (Welfare_DiversityDiminishingReturns.lean): "
lake build FormalAnthropology.Welfare_DiversityDiminishingReturns 2>&1 | grep -q "Build completed" && echo "✓ PASS" || echo "✗ FAIL"

echo -n "4. Theorem 14 (Learning_DiversityDepthTradeoff.lean): "
lake build FormalAnthropology.Learning_DiversityDepthTradeoff 2>&1 | grep -q "Build completed" && echo "✓ PASS" || echo "✗ FAIL"

echo ""
echo "Priority 2: Formalize New Theorems"
echo "===================================="

echo -n "5. Theorem 9 (Learning_StructuralCharacterization.lean): "
lake build FormalAnthropology.Learning_StructuralCharacterization 2>&1 | grep -q "Build completed" && echo "✓ PASS" || echo "✗ FAIL"

echo -n "6. Theorem 10 (Learning_GenericEmergence.lean): "
lake build FormalAnthropology.Learning_GenericEmergence 2>&1 | grep -q "Build completed" && echo "✓ PASS" || echo "✗ FAIL"

echo -n "7. Theorem 17 (Welfare_HeterogeneousValues.lean): "
lake build FormalAnthropology.Welfare_HeterogeneousValues 2>&1 | grep -q "Build completed" && echo "✓ PASS" || echo "✗ FAIL"

echo -n "8. Theorem 18 (Learning_HomogeneityDominates.lean): "
lake build FormalAnthropology.Learning_HomogeneityDominates 2>&1 | grep -q "Build completed" && echo "✓ PASS" || echo "✗ FAIL"

echo ""
echo "NEW Theorems (NEW-A, NEW-B, NEW-C)"
echo "===================================="

echo -n "9. NEW-A (Learning_CollaborationFailure.lean): "
lake build FormalAnthropology.Learning_CollaborationFailure 2>&1 | grep -q "Build completed" && echo "✓ PASS" || echo "✗ FAIL"

echo -n "10. NEW-B (Learning_CIThresholdDistribution.lean): "
lake build FormalAnthropology.Learning_CIThresholdDistribution 2>&1 | grep -q "Build completed" && echo "✓ PASS" || echo "✗ FAIL"

echo -n "11. NEW-C (Learning_CIPrediction.lean): "
lake build FormalAnthropology.Learning_CIPrediction 2>&1 | grep -q "Build completed" && echo "✓ PASS" || echo "✗ FAIL"

echo ""
echo "=== CHECKING FOR SORRIES ==="
echo ""

for file in Learning_CollectiveAccess Welfare_DiversityScaling_Proven Welfare_DiversityDiminishingReturns Learning_DiversityDepthTradeoff Learning_StructuralCharacterization Learning_GenericEmergence Welfare_HeterogeneousValues Learning_HomogeneityDominates Learning_CollaborationFailure Learning_CIThresholdDistribution Learning_CIPrediction; do
  count=$(grep -c "sorry" FormalAnthropology/$file.lean 2>/dev/null || echo "0")
  if [ "$count" = "0" ]; then
    echo "✓ $file: NO sorries"
  else
    echo "✗ $file: $count sorries found"
  fi
done

echo ""
echo "=== SUMMARY ==="
