#!/bin/bash

echo "========================================"
echo "Paper C Complete Verification (D1-D27)"
echo "========================================"
echo ""

# Build all Paper C theorem files
echo "Building all Paper C theorem files..."
echo ""

FILES=(
  "PaperC_DiversityTheorems_Revision"
  "PaperC_RevisionPlan_Theorems"
  "PaperC_NewTheorems_D10"
  "PaperC_NewTheorems_D11"
  "PaperC_NewTheorems_D12"
  "PaperC_NewTheorems_D13_D14"
  "PaperC_NewTheorems_D15"
  "PaperC_NewTheorems_D16_D20"
  "PaperC_NewTheorems_D21_D26"
  "PaperC_NewTheorems_D27_D29"
)

BUILD_SUCCESS=0
for file in "${FILES[@]}"; do
  echo -n "  Building $file... "
  if lake build "FormalAnthropology.$file" 2>&1 | grep -q "Built"; then
    echo "✓"
    BUILD_SUCCESS=$((BUILD_SUCCESS + 1))
  else
    echo "✗"
  fi
done

echo ""
echo "Build Results: $BUILD_SUCCESS/${#FILES[@]} files built successfully"
echo ""

# Check for sorries
echo "Checking for sorries..."
SORRY_COUNT=$(grep -r "sorry" FormalAnthropology/PaperC*.lean 2>/dev/null | grep -v "^\s*--" | grep -v "^\s*/\*" | grep -v "without sorry" | grep -v "ZERO SORRIES" | wc -l | xargs)

if [ "$SORRY_COUNT" -eq 0 ]; then
  echo "✓ ZERO SORRIES found in all Paper C files"
else
  echo "✗ Found $SORRY_COUNT sorry statements"
  grep -r "sorry" FormalAnthropology/PaperC*.lean 2>/dev/null | grep -v "^\s*--" | grep -v "^\s*/\*" | grep -v "without sorry" | grep -v "ZERO SORRIES"
fi

echo ""
echo "Theorem Coverage:"
echo "  D1-D5:   PaperC_DiversityTheorems_Revision.lean"
echo "  D6-D9:   PaperC_RevisionPlan_Theorems.lean"
echo "  D10:     PaperC_NewTheorems_D10.lean"
echo "  D11:     PaperC_NewTheorems_D11.lean"
echo "  D12:     PaperC_NewTheorems_D12.lean"
echo "  D13-D14: PaperC_NewTheorems_D13_D14.lean"
echo "  D15:     PaperC_NewTheorems_D15.lean"
echo "  D16-D20: PaperC_NewTheorems_D16_D20.lean"
echo "  D21-D26: PaperC_NewTheorems_D21_D26.lean"
echo "  D27:     PaperC_NewTheorems_D27_D29.lean (3 variants)"
echo ""
echo "========================================"
echo "Verification Complete"
echo "========================================"
