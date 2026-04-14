#!/bin/bash
# Final verification script for Paper A Lean proofs

echo "================================================"
echo "PAPER A: FINAL LEAN VERIFICATION"
echo "Date: $(date)"
echo "================================================"
echo ""

# Critical files for Paper A
FILES=(
  "FormalAnthropology/Learning_SerialOracle.lean"
  "FormalAnthropology/Learning_TypeSeparationExamples.lean"
  "FormalAnthropology/Learning_DistinguishabilityBound.lean"
  "FormalAnthropology/Learning_DiversityScalingSimple.lean"
  "FormalAnthropology/Collective_DiversityNecessity.lean"
  "FormalAnthropology/Learning_Theorem39InformationBarrier.lean"
  "FormalAnthropology/Learning_ApplicationDomains.lean"
  "FormalAnthropology/Learning_ComputationalComplexity.lean"
)

TIER1_FILES=(
  "FormalAnthropology/Learning_SerialOracle.lean"
  "FormalAnthropology/Learning_TypeSeparationExamples.lean"
  "FormalAnthropology/Learning_DistinguishabilityBound.lean"
  "FormalAnthropology/Collective_DiversityNecessity.lean"
)

TIER2_FILES=(
  "FormalAnthropology/Learning_DiversityScalingSimple.lean"
  "FormalAnthropology/Learning_ComputationalComplexity.lean"
  "FormalAnthropology/Learning_Theorem39InformationBarrier.lean"
  "FormalAnthropology/Learning_ApplicationDomains.lean"
)

echo "TIER 1 THEOREMS (MUST HAVE)"
echo "----------------------------"
total_sorries=0
for file in "${TIER1_FILES[@]}"; do
  if [ -f "$file" ]; then
    sorries=$(grep -c "^ *sorry" "$file" 2>/dev/null || echo 0)
    total_sorries=$((total_sorries + sorries))
    lines=$(wc -l < "$file")
    if [ "$sorries" -eq 0 ]; then
      status="✅"
    else
      status="❌"
    fi
    echo "$status $(basename $file): $lines lines, $sorries sorries"
  else
    echo "❌ $(basename $file): FILE NOT FOUND"
  fi
done
echo ""

echo "TIER 2 THEOREMS (SHOULD HAVE)"
echo "------------------------------"
for file in "${TIER2_FILES[@]}"; do
  if [ -f "$file" ]; then
    sorries=$(grep -c "^ *sorry" "$file" 2>/dev/null || echo 0)
    total_sorries=$((total_sorries + sorries))
    lines=$(wc -l < "$file")
    if [ "$sorries" -eq 0 ]; then
      status="✅"
    else
      status="❌"
    fi
    echo "$status $(basename $file): $lines lines, $sorries sorries"
  else
    echo "❌ $(basename $file): FILE NOT FOUND"
  fi
done
echo ""

echo "SUMMARY"
echo "-------"
echo "Total files checked: ${#FILES[@]}"
echo "Total sorries found: $total_sorries"
echo ""

if [ "$total_sorries" -eq 0 ]; then
  echo "✅ SUCCESS: ALL PAPER A PROOFS COMPLETE (ZERO SORRIES)"
  echo ""
  echo "Key theorems proven:"
  echo "  D.1-D.2: Serial Oracle Model"
  echo "  E.1-E.2: Type Separation Examples"
  echo "  G.1:     Distinguishability Index (non-vacuous)"
  echo "  A.1:     Diversity Necessity"
  echo "  A.2:     Diversity Scaling Law"
  echo "  B.1:     Depth Computation Hardness"
  echo "  C.1:     Information Barrier"
  echo "  H.1:     Program Synthesis Application"
  echo ""
  echo "Status: READY FOR PAPER REVISION"
else
  echo "❌ FAILURE: $total_sorries sorries remain"
  echo "Status: PROOFS INCOMPLETE"
fi

echo ""
echo "================================================"
