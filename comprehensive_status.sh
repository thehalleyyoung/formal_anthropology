#!/bin/bash

echo "====== PAPER B REVISION PLAN - COMPREHENSIVE STATUS ======"
echo ""
echo "Priority 1: Fix Build Errors (from REVISION_PLAN.md)"
echo "========================================================="
echo ""

# Priority 1 files with build issues
echo "1. Theorem 5 (Learning_CollectiveAccess.lean):"
lake build FormalAnthropology.Learning_CollectiveAccess 2>&1 | grep -E "(error|✓|✖)" | head -5 || echo "   ✓ BUILDS SUCCESSFULLY"

echo ""
echo "2. Theorem 12 (Welfare_DiversityScaling_Proven.lean):"
lake build FormalAnthropology.Welfare_DiversityScaling_Proven 2>&1 | grep -E "(error|✓|✖)" | head -5 || echo "   ✓ BUILDS SUCCESSFULLY"

echo ""
echo "3. Theorem 13 (Welfare_DiversityDiminishingReturns.lean):"
lake build FormalAnthropology.Welfare_DiversityDiminishingReturns 2>&1 | grep -E "(error|✓|✖)" | head -5 || echo "   ✓ BUILDS SUCCESSFULLY"

echo ""
echo "4. Theorem 14 (Learning_DiversityDepthTradeoff.lean):"
lake build FormalAnthropology.Learning_DiversityDepthTradeoff 2>&1 | grep -E "(error|✓|✖)" | head -5 || echo "   ✓ BUILDS SUCCESSFULLY"

echo ""
echo "Priority 2: Formalize New Theorems (from REVISION_PLAN.md)"
echo "============================================================"
echo ""

echo "5. Theorem 9 (Learning_StructuralCharacterization.lean):"
lake build FormalAnthropology.Learning_StructuralCharacterization 2>&1 | grep -E "(error|✓|✖)" | head -5 || echo "   ✓ BUILDS SUCCESSFULLY"

echo ""
echo "6. Theorem 10 (Learning_GenericEmergence.lean):"
lake build FormalAnthropology.Learning_GenericEmergence 2>&1 | grep -E "(error|✓|✖)" | head -5 || echo "   ✓ BUILDS SUCCESSFULLY"

echo ""
echo "7. Theorem 17 (Welfare_HeterogeneousValues.lean):"
lake build FormalAnthropology.Welfare_HeterogeneousValues 2>&1 | grep -E "(error|✓|✖)" | head -5 || echo "   ✓ BUILDS SUCCESSFULLY"

echo ""
echo "8. Theorem 18/30 (Learning_HomogeneityDominates.lean):"
lake build FormalAnthropology.Learning_HomogeneityDominates 2>&1 | grep -E "(error|✓|✖)" | head -5 || echo "   ✓ BUILDS SUCCESSFULLY"

echo ""
echo "NEW theorems required by revision:"
echo "9. Theorem NEW-A (Learning_CollaborationFailure.lean):"
lake build FormalAnthropology.Learning_CollaborationFailure 2>&1 | grep -E "(error|✓|✖)" | head -5 || echo "   ✓ BUILDS SUCCESSFULLY"

echo ""
echo "10. Theorem NEW-B (Learning_CIThresholdDistribution.lean):"
lake build FormalAnthropology.Learning_CIThresholdDistribution 2>&1 | grep -E "(error|✓|✖)" | head -5 || echo "   ✓ BUILDS SUCCESSFULLY"

echo ""
echo "11. Theorem NEW-C (Learning_CIPrediction.lean):"
lake build FormalAnthropology.Learning_CIPrediction 2>&1 | grep -E "(error|✓|✖)" | head -5 || echo "   ✓ BUILDS SUCCESSFULLY"

echo ""
echo "====== SUMMARY ======"
echo ""
echo "Checking for sorries in all revision files..."
grep -l "sorry" FormalAnthropology/Learning_CollectiveAccess.lean \
  FormalAnthropology/Welfare_DiversityScaling_Proven.lean \
  FormalAnthropology/Welfare_DiversityDiminishingReturns.lean \
  FormalAnthropology/Learning_DiversityDepthTradeoff.lean \
  FormalAnthropology/Learning_StructuralCharacterization.lean \
  FormalAnthropology/Learning_GenericEmergence.lean \
  FormalAnthropology/Welfare_HeterogeneousValues.lean \
  FormalAnthropology/Learning_HomogeneityDominates.lean \
  FormalAnthropology/Learning_CollaborationFailure.lean \
  FormalAnthropology/Learning_CIThresholdDistribution.lean \
  FormalAnthropology/Learning_CIPrediction.lean 2>/dev/null || echo "No sorries found in revision files!"

