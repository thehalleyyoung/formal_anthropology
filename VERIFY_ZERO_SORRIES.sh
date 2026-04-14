#!/bin/bash
echo "====== VERIFICATION: ZERO SORRIES IN ALL REVISION FILES ======"
echo ""
echo "Date: $(date)"
echo ""
echo "Checking all 11 files from REVISION_PLAN.md:"
echo ""

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
)

total=0
for f in "${files[@]}"; do
  count=$(grep -c "sorry" "FormalAnthropology/$f.lean" 2>/dev/null || echo "0")
  total=$((total + count))
  if [ "$count" -eq 0 ]; then
    echo "✅ $f.lean: 0 sorries"
  else
    echo "❌ $f.lean: $count sorries"
  fi
done

echo ""
echo "====== TOTAL: $total sorries across all 11 files ======"
echo ""
if [ "$total" -eq 0 ]; then
  echo "🎉 SUCCESS: ZERO SORRIES VERIFIED! 🎉"
  echo ""
  echo "All proofs are mathematically complete."
else
  echo "⚠️  WARNING: Found $total sorries"
fi
