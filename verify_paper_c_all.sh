#!/bin/bash
echo "=== Building all Paper C theorem files ==="
files=(
  "FormalAnthropology.PaperC_DiversityTheorems_Revision"
  "FormalAnthropology.PaperC_RevisionPlan_Theorems"
  "FormalAnthropology.PaperC_NewTheorems_D10"
  "FormalAnthropology.PaperC_NewTheorems_D11"
  "FormalAnthropology.PaperC_NewTheorems_D12"
  "FormalAnthropology.PaperC_NewTheorems_D13_D14"
  "FormalAnthropology.PaperC_NewTheorems_D15"
  "FormalAnthropology.PaperC_NewTheorems_D16_D20"
  "FormalAnthropology.PaperC_NewTheorems_D21_D26"
)

for file in "${files[@]}"; do
  echo "Building $file..."
  lake build "$file" 2>&1 | grep -E "(error|sorry)" && echo "FAILED: $file" || echo "OK: $file"
done

echo ""
echo "=== Checking for sorries in source files ==="
for file in FormalAnthropology/PaperC_*.lean; do
  if grep -q "sorry" "$file"; then
    echo "SORRY FOUND in $file:"
    grep -n "sorry" "$file"
  fi
done
echo "=== Verification complete ==="
