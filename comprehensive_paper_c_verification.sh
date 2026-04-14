#!/bin/bash

echo "=========================================="
echo "COMPREHENSIVE PAPER C VERIFICATION"
echo "Date: $(date)"
echo "=========================================="
echo ""

# List of all Paper C theorem files
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
  "FormalAnthropology.PaperC_NewTheorems_D27_D29"
)

TOTAL=0
SUCCESS=0
FAILED=0

echo "Building all Paper C theorem files..."
echo ""

for file in "${FILES[@]}"; do
  TOTAL=$((TOTAL + 1))
  echo "[$TOTAL/${#FILES[@]}] Building $file..."
  if lake build "$file" > /tmp/build_$TOTAL.log 2>&1; then
    SUCCESS=$((SUCCESS + 1))
    echo "  ✓ SUCCESS"
  else
    FAILED=$((FAILED + 1))
    echo "  ✗ FAILED - see /tmp/build_$TOTAL.log"
    tail -10 /tmp/build_$TOTAL.log
  fi
done

echo ""
echo "=========================================="
echo "BUILD SUMMARY"
echo "=========================================="
echo "Total files:    $TOTAL"
echo "Successful:     $SUCCESS"
echo "Failed:         $FAILED"
echo ""

# Check for sorries
echo "=========================================="
echo "CHECKING FOR SORRIES"
echo "=========================================="
SORRY_COUNT=0
for lean_file in FormalAnthropology/PaperC*.lean; do
  if [ -f "$lean_file" ]; then
    count=$(grep -c "sorry" "$lean_file" 2>/dev/null || echo 0)
    if [ "$count" -gt 0 ]; then
      echo "⚠ $lean_file: $count sorry statements"
      SORRY_COUNT=$((SORRY_COUNT + count))
    fi
  fi
done

if [ $SORRY_COUNT -eq 0 ]; then
  echo "✓ ZERO SORRIES - All proofs complete!"
else
  echo "✗ Found $SORRY_COUNT sorry statements"
fi
echo ""

# Check for axioms
echo "=========================================="
echo "CHECKING FOR CUSTOM AXIOMS"
echo "=========================================="
AXIOM_COUNT=0
for lean_file in FormalAnthropology/PaperC*.lean; do
  if [ -f "$lean_file" ]; then
    count=$(grep -c "^axiom " "$lean_file" 2>/dev/null || echo 0)
    if [ "$count" -gt 0 ]; then
      echo "⚠ $lean_file: $count axiom declarations"
      grep -n "^axiom " "$lean_file"
      AXIOM_COUNT=$((AXIOM_COUNT + count))
    fi
  fi
done

if [ $AXIOM_COUNT -eq 0 ]; then
  echo "✓ ZERO CUSTOM AXIOMS - Only standard Lean axioms used!"
else
  echo "✗ Found $AXIOM_COUNT custom axiom declarations"
fi
echo ""

# Final verdict
echo "=========================================="
echo "FINAL VERDICT"
echo "=========================================="
if [ $FAILED -eq 0 ] && [ $SORRY_COUNT -eq 0 ] && [ $AXIOM_COUNT -eq 0 ]; then
  echo "✓✓✓ ALL CHECKS PASSED ✓✓✓"
  echo ""
  echo "All Paper C theorems (D1-D29):"
  echo "  • Build successfully with zero errors"
  echo "  • Contain zero 'sorry' statements"
  echo "  • Use only standard Lean axioms"
  echo ""
  echo "The formalization is COMPLETE and VALID."
  exit 0
else
  echo "✗✗✗ VERIFICATION FAILED ✗✗✗"
  echo ""
  [ $FAILED -gt 0 ] && echo "  • $FAILED files failed to build"
  [ $SORRY_COUNT -gt 0 ] && echo "  • $SORRY_COUNT incomplete proofs found"
  [ $AXIOM_COUNT -gt 0 ] && echo "  • $AXIOM_COUNT custom axioms found"
  exit 1
fi
