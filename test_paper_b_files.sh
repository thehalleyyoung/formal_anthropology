#!/bin/bash
echo "Testing Paper B Lean files..."
echo "=============================="

files=(
  "Learning_CollectiveAccess"
  "Welfare_DiversityScaling_Proven"
  "Welfare_DiversityDiminishingReturns"
  "Learning_DiversityDepthTradeoff"
  "Learning_StructuralCharacterization"
  "Learning_GenericEmergence"
  "Welfare_HeterogeneousValues"
  "Learning_HomogeneityDominates"
  "Learning_CollaborationFailure"
  "Learning_CIThresholdDistribution"
  "Learning_CIPrediction"
  "Learning_ComplementarityIndex"
)

for file in "${files[@]}"; do
  echo ""
  echo "Testing: $file"
  if lake build "FormalAnthropology.$file" 2>&1 | grep -q "Build completed successfully"; then
    echo "✓ SUCCESS"
  else
    echo "✗ FAILED"
  fi
done
