#!/bin/bash
# Test all theorems mentioned in REVISION_PLAN.md for Paper B

echo "=== Testing Revision Plan Theorems ==="
echo ""

# Priority 1: Fix Build Issues
echo "Priority 1: Fix Build Issues"
echo "----------------------------"

echo "1. Theorem 5: Existence (Learning_CollectiveAccess)"
lake build FormalAnthropology.Learning_CollectiveAccess 2>&1 | grep -i "error\|sorry\|warning.*sorry" || echo "✅ BUILDS"

echo ""
echo "2. Theorem 12: Quadratic Scaling (Welfare_DiversityScaling_Proven)"
lake build FormalAnthropology.Welfare_DiversityScaling_Proven 2>&1 | grep -i "error\|sorry\|warning.*sorry" || echo "✅ BUILDS"

echo ""
echo "3. Theorem 13: Diminishing Returns (Welfare_DiversityDiminishingReturns)"
lake build FormalAnthropology.Welfare_DiversityDiminishingReturns 2>&1 | grep -i "error\|sorry\|warning.*sorry" || echo "✅ BUILDS"

echo ""
echo "4. Theorem 14: Diversity-Depth Tradeoff (Learning_DiversityDepthTradeoff)"
lake build FormalAnthropology.Learning_DiversityDepthTradeoff 2>&1 | grep -i "error\|sorry\|warning.*sorry" || echo "✅ BUILDS"

# Priority 2: Formalize Currently Unformalized
echo ""
echo "Priority 2: Currently Unformalized Theorems"
echo "-------------------------------------------"

echo "5. Theorem 9: Structural Characterization"
lake build FormalAnthropology.Learning_StructuralCharacterization 2>&1 | grep -i "error\|sorry\|warning.*sorry" || echo "✅ BUILDS"

echo ""
echo "6. Theorem 10: Generic Emergence"
lake build FormalAnthropology.Learning_GenericEmergence 2>&1 | grep -i "error\|sorry\|warning.*sorry" || echo "✅ BUILDS"

echo ""
echo "7. Theorem 17: Heterogeneous Values (Welfare_HeterogeneousValues)"
lake build FormalAnthropology.Welfare_HeterogeneousValues 2>&1 | grep -i "error\|sorry\|warning.*sorry" || echo "✅ BUILDS"

echo ""
echo "8. Theorem 18: Homogeneity Dominates (Learning_HomogeneityDominates)"
lake build FormalAnthropology.Learning_HomogeneityDominates 2>&1 | grep -i "error\|sorry\|warning.*sorry" || echo "✅ BUILDS"

# NEW theorems from revision plan
echo ""
echo "NEW Theorems (Need to Create)"
echo "-----------------------------"

echo "9. NEW-A: Collaboration Failure (needs creation)"
echo "10. NEW-B: CI Threshold Distribution"
lake build FormalAnthropology.Learning_CIThresholdDistribution 2>&1 | grep -i "error\|sorry\|warning.*sorry" || echo "✅ BUILDS"

echo ""
echo "11. NEW-C: CI Prediction (needs creation)"

echo ""
echo "=== Summary ==="
echo "Check output above for errors and sorries"
