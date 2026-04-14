#!/bin/bash
# Verify the 6 key files from REVISION_PLAN.md build correctly

FILES=(
  "Learning_DiversityTractable"
  "Learning_VCDiversityProduct"
  "Learning_StructuralDepthResolution"
  "Learning_StructuralDepthAST"
  "Learning_ProofComplexity"
  "Learning_DepthDiversityDecomp"
)

echo "=== Checking for sorries in Paper A revision files ==="
for file in "${FILES[@]}"; do
  echo "Checking FormalAnthropology/${file}.lean..."
  if grep -q "sorry" "FormalAnthropology/${file}.lean"; then
    echo "  ❌ FOUND SORRIES"
    grep -n "sorry" "FormalAnthropology/${file}.lean"
  else
    echo "  ✅ NO SORRIES"
  fi
done

echo ""
echo "=== Building each file individually ==="
for file in "${FILES[@]}"; do
  echo "Building FormalAnthropology.${file}..."
  if lake build "FormalAnthropology.${file}" 2>&1 | grep -q "error:"; then
    echo "  ❌ BUILD FAILED"
    lake build "FormalAnthropology.${file}" 2>&1 | grep "error:" | head -5
  else
    echo "  ✅ BUILD SUCCESS"
  fi
done
