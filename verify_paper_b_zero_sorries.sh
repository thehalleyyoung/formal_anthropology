#!/bin/bash
echo "========================================="
echo "PAPER B REVISION PLAN - ZERO SORRIES CHECK"
echo "========================================="
echo ""

files=(
  "Learning_CollectiveAccess"
  "Learning_StructuralCharacterization"
  "Learning_GenericEmergence"
  "Learning_ComplementarityIndex"
  "Welfare_HeterogeneousValues"
  "Learning_HomogeneityDominates"
  "Learning_CollaborationFailure"
  "Learning_CIThresholdDistribution"
  "Learning_CIPrediction"
)

echo "Checking for sorries in each file..."
echo "======================================"
all_zero=true
for file in "${files[@]}"; do
  sorry_count=$(grep -c "sorry" "FormalAnthropology/$file.lean" 2>/dev/null || echo "FILE_NOT_FOUND")
  if [ "$sorry_count" = "FILE_NOT_FOUND" ]; then
    echo "✗ $file: FILE NOT FOUND"
    all_zero=false
  elif [ "$sorry_count" = "0" ]; then
    echo "✓ $file: 0 sorries"
  else
    echo "✗ $file: $sorry_count sorries"
    all_zero=false
  fi
done
echo ""

echo "Building each file..."
echo "======================================"
all_build=true
for file in "${files[@]}"; do
  echo -n "Building $file... "
  if lake build "FormalAnthropology.$file" 2>&1 | grep -q "Build completed successfully"; then
    echo "✓ SUCCESS"
  else
    echo "✗ FAILED"
    all_build=false
  fi
done
echo ""

echo "========================================="
echo "FINAL SUMMARY"
echo "========================================="
if [ "$all_zero" = true ] && [ "$all_build" = true ]; then
  echo "✓✓✓ ALL PAPER B FILES: ZERO SORRIES AND BUILDING ✓✓✓"
  exit 0
else
  if [ "$all_zero" = false ]; then
    echo "✗ Some files have sorries"
  fi
  if [ "$all_build" = false ]; then
    echo "✗ Some files failed to build"
  fi
  exit 1
fi
