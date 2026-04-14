#!/bin/bash
# Verification script for Paper C revision Lean proofs

echo "=========================================="
echo "Paper C Revision: Lean Proof Verification"
echo "=========================================="
echo ""

echo "Checking for sorries in revision files..."
echo ""

FILES=(
  "FormalAnthropology/Learning_GeneratorRobustness.lean"
  "FormalAnthropology/Learning_EmpiricalValidation.lean"
  "FormalAnthropology/Learning_ConstraintResource.lean"
)

TOTAL_SORRIES=0

for file in "${FILES[@]}"; do
  if [ -f "$file" ]; then
    SORRY_COUNT=$(grep -c "sorry" "$file" || echo "0")
    TOTAL_SORRIES=$((TOTAL_SORRIES + SORRY_COUNT))
    if [ "$SORRY_COUNT" -eq 0 ]; then
      echo "✅ $file: 0 sorries"
    else
      echo "❌ $file: $SORRY_COUNT sorries"
    fi
  else
    echo "⚠️  $file: NOT FOUND"
  fi
done

echo ""
echo "Total sorries across all revision files: $TOTAL_SORRIES"
echo ""

if [ "$TOTAL_SORRIES" -eq 0 ]; then
  echo "✅ SUCCESS: All revision files have zero sorries!"
else
  echo "❌ FAILURE: Found $TOTAL_SORRIES sorries in revision files"
  exit 1
fi

echo ""
echo "Building revision files..."
echo ""

lake build FormalAnthropology.Learning_GeneratorRobustness \
           FormalAnthropology.Learning_EmpiricalValidation \
           FormalAnthropology.Learning_ConstraintResource

if [ $? -eq 0 ]; then
  echo ""
  echo "✅ BUILD SUCCESS: All revision files compile successfully!"
  echo ""
  echo "=========================================="
  echo "Paper C Revision Status: ✅ COMPLETE"
  echo "=========================================="
  exit 0
else
  echo ""
  echo "❌ BUILD FAILURE: Compilation errors detected"
  exit 1
fi
