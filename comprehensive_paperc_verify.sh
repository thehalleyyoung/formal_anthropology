#!/bin/bash
echo "==================================================================="
echo "COMPREHENSIVE PAPER C VERIFICATION - ALL THEOREMS D1-D26"
echo "==================================================================="
echo ""

FILES=(
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

LEAN_FILES=(
  "FormalAnthropology/PaperC_DiversityTheorems_Revision.lean"
  "FormalAnthropology/PaperC_RevisionPlan_Theorems.lean"
  "FormalAnthropology/PaperC_NewTheorems_D10.lean"
  "FormalAnthropology/PaperC_NewTheorems_D11.lean"
  "FormalAnthropology/PaperC_NewTheorems_D12.lean"
  "FormalAnthropology/PaperC_NewTheorems_D13_D14.lean"
  "FormalAnthropology/PaperC_NewTheorems_D15.lean"
  "FormalAnthropology/PaperC_NewTheorems_D16_D20.lean"
  "FormalAnthropology/PaperC_NewTheorems_D21_D26.lean"
)

total_files=${#FILES[@]}
passed=0
failed=0

for i in "${!FILES[@]}"; do
  file="${FILES[$i]}"
  lean_file="${LEAN_FILES[$i]}"
  
  echo "-------------------------------------------------------------------"
  echo "[$((i+1))/$total_files] Verifying: $file"
  echo "-------------------------------------------------------------------"
  
  # Build the file
  echo "Building..."
  if lake build "$file" 2>&1 | grep -q "Build completed successfully"; then
    echo "✅ Build: PASS"
    build_pass=1
  else
    echo "❌ Build: FAIL"
    build_pass=0
    failed=$((failed+1))
    continue
  fi
  
  # Check for sorries
  echo "Checking for sorries..."
  if grep -q "sorry" "$lean_file"; then
    echo "❌ Sorries: FOUND"
    grep -n "sorry" "$lean_file" | head -3
    failed=$((failed+1))
    continue
  else
    echo "✅ Sorries: ZERO"
  fi
  
  echo "✅ COMPLETE: $file"
  passed=$((passed+1))
  echo ""
done

echo "==================================================================="
echo "SUMMARY"
echo "==================================================================="
echo "Total files:  $total_files"
echo "Passed:       $passed"
echo "Failed:       $failed"
echo ""

if [ $failed -eq 0 ]; then
  echo "🎉 ALL PAPER C THEOREMS VERIFIED: ZERO ERRORS, ZERO SORRIES"
  echo ""
  echo "Theorems D1-D26 are complete and ready for revision!"
else
  echo "⚠️  Some files need attention"
fi

echo "==================================================================="
