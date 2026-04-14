#!/bin/bash
echo "=== Testing Revision Plan Files ==="
echo ""

echo "1. Learning_CollectiveAccess.lean (Theorem 5)"
lake build FormalAnthropology.Learning_CollectiveAccess 2>&1 | tail -3
echo ""

echo "2. Welfare_DiversityScaling_Proven.lean (Theorem 12)"
lake build FormalAnthropology.Welfare_DiversityScaling_Proven 2>&1 | tail -3
echo ""

echo "3. Welfare_DiversityDiminishingReturns.lean (Theorem 13)"
lake build FormalAnthropology.Welfare_DiversityDiminishingReturns 2>&1 | tail -3
echo ""

echo "4. Learning_DiversityDepthTradeoff.lean (Theorem 14)"
lake build FormalAnthropology.Learning_DiversityDepthTradeoff 2>&1 | tail -3
echo ""

echo "5. Learning_StructuralCharacterization.lean (Theorem 9)"
lake build FormalAnthropology.Learning_StructuralCharacterization 2>&1 | tail -3
echo ""

echo "6. Learning_GenericEmergence.lean (Theorem 10)"
lake build FormalAnthropology.Learning_GenericEmergence 2>&1 | tail -3
echo ""

echo "7. Welfare_HeterogeneousValues.lean (Theorem 17)"
lake build FormalAnthropology.Welfare_HeterogeneousValues 2>&1 | tail -3
echo ""

echo "8. Learning_HomogeneityDominates.lean (Theorem 18 - negative)"
lake build FormalAnthropology.Learning_HomogeneityDominates 2>&1 | tail -3
echo ""

echo "9. Learning_CollaborationFailure.lean (NEW-A)"
lake build FormalAnthropology.Learning_CollaborationFailure 2>&1 | tail -3
echo ""

echo "10. Learning_CIThresholdDistribution.lean (NEW-B)"
lake build FormalAnthropology.Learning_CIThresholdDistribution 2>&1 | tail -3
echo ""

echo "11. Learning_CIPrediction.lean (NEW-C)"
lake build FormalAnthropology.Learning_CIPrediction 2>&1 | tail -3
