#!/bin/bash
# Build all Paper B key theorems and report status

echo "=== PAPER B KEY THEOREMS BUILD STATUS ===" 
echo ""
echo "Building key files..."

FILES=(
  "Learning_ComplementarityIndex"
  "Welfare_DiversityScaling_Proven"
  "Welfare_DiversityDecomposition"
  "Learning_DiversityDepthTradeoff"
  "Learning_Theorem40_ZeroValueDiversity"
  "Learning_DiversityComputationNPHard"
)

for file in "${FILES[@]}"; do
  echo "--- $file ---"
  if lake build "FormalAnthropology.$file" 2>&1 | grep -q "Build completed"; then
    echo "✓ SUCCESS"
  else
    echo "✗ FAILED"
    lake build "FormalAnthropology.$file" 2>&1 | grep "error:" | head -3
  fi
  echo ""
done
