#!/bin/bash
echo "=== CHECKING ALL REVISION PLAN THEOREMS FOR SORRIES ==="
echo ""

files=(
  "FormalAnthropology/Learning_CollectiveAccess.lean"
  "FormalAnthropology/Welfare_DiversityScaling_Proven.lean"
  "FormalAnthropology/Welfare_DiversityDiminishingReturns.lean"
  "FormalAnthropology/Learning_DiversityDepthTradeoff.lean"
  "FormalAnthropology/Learning_StructuralCharacterization.lean"
  "FormalAnthropology/Learning_GenericEmergence.lean"
  "FormalAnthropology/Welfare_HeterogeneousValues.lean"
  "FormalAnthropology/Learning_HomogeneityDominates.lean"
  "FormalAnthropology/Learning_CollaborationFailure.lean"
  "FormalAnthropology/Learning_CIThresholdDistribution.lean"
  "FormalAnthropology/Learning_CIPrediction.lean"
)

total=0
zero_sorry=0

for file in "${files[@]}"; do
  if [ -f "$file" ]; then
    count=$(grep -c "sorry" "$file" || echo "0")
    total=$((total + 1))
    if [ "$count" = "0" ]; then
      zero_sorry=$((zero_sorry + 1))
      echo "✅ $file: 0 sorries"
    else
      echo "❌ $file: $count sorries"
    fi
  else
    echo "⚠️  $file: FILE NOT FOUND"
  fi
done

echo ""
echo "===================="
echo "SUMMARY: $zero_sorry/$total files have ZERO SORRIES"
if [ "$zero_sorry" = "$total" ]; then
  echo "🎉 ALL FILES VERIFIED - ZERO SORRIES ACHIEVED!"
fi
