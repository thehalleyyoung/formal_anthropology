#!/bin/bash

echo "================================================"
echo "PAPER B REVISION PLAN VERIFICATION"
echo "================================================"
echo ""
echo "Checking all theorems from REVISION_PLAN.md..."
echo ""

# Array of Paper B files to check
files=(
  "Learning_CollectiveAccess"              # Theorem 5: Existence
  "Learning_StructuralCharacterization"    # Theorem 9: Structural Characterization (NEW)
  "Learning_GenericEmergence"             # Theorem 10: Generic Emergence (NEW)
  "Welfare_DiversityScaling_Proven"       # Theorem 12: Quadratic Scaling
  "Welfare_DiversityDiminishingReturns"   # Theorem 13: Diminishing Returns
  "Learning_DiversityDepthTradeoff"       # Theorem 14: Diversity-Depth Tradeoff
  "Welfare_HeterogeneousValues"           # Theorem 17: Heterogeneous Values (NEW)
  "Learning_HomogeneityDominates"         # Theorem 18/30: Homogeneity Dominates (NEW)
  "Learning_CollaborationFailure"         # NEW-A: Collaboration Failure
  "Learning_CIThresholdDistribution"      # NEW-B: CI Distribution
  "Learning_CIPrediction"                 # NEW-C: CI Prediction
)

success_count=0
fail_count=0
sorry_count=0

for file in "${files[@]}"; do
  echo "-------------------------------------------"
  echo "Testing: $file"
  
  # Check for sorries
  sorries=$(grep -c "sorry" FormalAnthropology/${file}.lean 2>/dev/null || echo "0")
  if [ "$sorries" != "0" ]; then
    echo "  ❌ FAIL: Contains $sorries sorries"
    sorry_count=$((sorry_count + sorries))
    fail_count=$((fail_count + 1))
    continue
  fi
  
  # Try to build
  if lake build FormalAnthropology.${file} 2>&1 | grep -q "Build completed successfully"; then
    echo "  ✅ SUCCESS: Builds with zero sorries"
    success_count=$((success_count + 1))
  else
    echo "  ❌ FAIL: Build errors"
    fail_count=$((fail_count + 1))
    lake build FormalAnthropology.${file} 2>&1 | grep "^error:" | head -3
  fi
done

echo ""
echo "================================================"
echo "SUMMARY"
echo "================================================"
echo "Total files tested: ${#files[@]}"
echo "✅ Successful: $success_count"
echo "❌ Failed: $fail_count"
echo "Total sorries found: $sorry_count"
echo ""

if [ $fail_count -eq 0 ] && [ $sorry_count -eq 0 ]; then
  echo "🎉 ALL PAPER B REVISION THEOREMS VERIFIED!"
  echo "   - 100% build successfully"
  echo "   - Zero sorries"
  echo "   - Ready for submission"
  exit 0
else
  echo "⚠️  Some theorems still need work:"
  echo "   - Files with build errors: $fail_count"
  echo "   - Total sorries to fix: $sorry_count"
  exit 1
fi
