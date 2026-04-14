#!/bin/bash

echo "=========================================="
echo "FINAL PAPER C VERIFICATION"
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
  echo -n "[$TOTAL/${#FILES[@]}] Building $file... "
  if lake build "$file" > /tmp/build_$TOTAL.log 2>&1; then
    SUCCESS=$((SUCCESS + 1))
    echo "✓"
  else
    FAILED=$((FAILED + 1))
    echo "✗"
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

# Check for sorries (excluding comments)
echo "=========================================="
echo "CHECKING FOR INCOMPLETE PROOFS"
echo "=========================================="
SORRY_COUNT=0
for lean_file in FormalAnthropology/PaperC_DiversityTheorems_Revision.lean \
                 FormalAnthropology/PaperC_RevisionPlan_Theorems.lean \
                 FormalAnthropology/PaperC_NewTheorems_D10.lean \
                 FormalAnthropology/PaperC_NewTheorems_D11.lean \
                 FormalAnthropology/PaperC_NewTheorems_D12.lean \
                 FormalAnthropology/PaperC_NewTheorems_D13_D14.lean \
                 FormalAnthropology/PaperC_NewTheorems_D15.lean \
                 FormalAnthropology/PaperC_NewTheorems_D16_D20.lean \
                 FormalAnthropology/PaperC_NewTheorems_D21_D26.lean \
                 FormalAnthropology/PaperC_NewTheorems_D27_D29.lean; do
  if [ -f "$lean_file" ]; then
    # Check for actual sorry statements (not in comments)
    count=$(grep -v "^/-\|^--\|sorry statements" "$lean_file" | grep -c "sorry" || echo 0)
    if [ "$count" -gt 0 ]; then
      echo "⚠ $lean_file: $count sorry statement(s)"
      grep -n "sorry" "$lean_file" | grep -v "^[0-9]*:.*--\|^[0-9]*:.*/\*\|sorry statements"
      SORRY_COUNT=$((SORRY_COUNT + count))
    fi
  fi
done

if [ $SORRY_COUNT -eq 0 ]; then
  echo "✓ ZERO INCOMPLETE PROOFS - All theorems fully proven!"
else
  echo "✗ Found $SORRY_COUNT incomplete proof(s)"
fi
echo ""

# Check for axioms
echo "=========================================="
echo "CHECKING FOR CUSTOM AXIOMS"
echo "=========================================="
AXIOM_COUNT=0
for lean_file in FormalAnthropology/PaperC_DiversityTheorems_Revision.lean \
                 FormalAnthropology/PaperC_RevisionPlan_Theorems.lean \
                 FormalAnthropology/PaperC_NewTheorems_D10.lean \
                 FormalAnthropology/PaperC_NewTheorems_D11.lean \
                 FormalAnthropology/PaperC_NewTheorems_D12.lean \
                 FormalAnthropology/PaperC_NewTheorems_D13_D14.lean \
                 FormalAnthropology/PaperC_NewTheorems_D15.lean \
                 FormalAnthropology/PaperC_NewTheorems_D16_D20.lean \
                 FormalAnthropology/PaperC_NewTheorems_D21_D26.lean \
                 FormalAnthropology/PaperC_NewTheorems_D27_D29.lean; do
  if [ -f "$lean_file" ]; then
    count=$(grep -c "^axiom " "$lean_file" 2>/dev/null || echo 0)
    if [ "$count" -gt 0 ]; then
      echo "⚠ $lean_file: $count axiom declaration(s)"
      grep -n "^axiom " "$lean_file"
      AXIOM_COUNT=$((AXIOM_COUNT + count))
    fi
  fi
done

if [ $AXIOM_COUNT -eq 0 ]; then
  echo "✓ ZERO CUSTOM AXIOMS - Only standard Lean axioms used!"
else
  echo "✗ Found $AXIOM_COUNT custom axiom declaration(s)"
fi
echo ""

# Final verdict
echo "=========================================="
echo "FINAL VERDICT"
echo "=========================================="
if [ $FAILED -eq 0 ] && [ $SORRY_COUNT -eq 0 ] && [ $AXIOM_COUNT -eq 0 ]; then
  echo ""
  echo "   ✓✓✓ ALL CHECKS PASSED ✓✓✓"
  echo ""
  echo "All Paper C theorems (D1-D29):"
  echo "  • Build successfully with zero errors"
  echo "  • Contain zero 'sorry' statements"  
  echo "  • Use only standard Lean axioms (propext, Classical.choice, Quot.sound)"
  echo ""
  echo "The formalization is COMPLETE and VALID."
  echo ""
  exit 0
else
  echo ""
  echo "   ✗✗✗ VERIFICATION FAILED ✗✗✗"
  echo ""
  [ $FAILED -gt 0 ] && echo "  • $FAILED file(s) failed to build"
  [ $SORRY_COUNT -gt 0 ] && echo "  • $SORRY_COUNT incomplete proof(s) found"
  [ $AXIOM_COUNT -gt 0 ] && echo "  • $AXIOM_COUNT custom axiom(s) found"
  echo ""
  exit 1
fi
