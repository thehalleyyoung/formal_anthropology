#!/bin/bash

echo "==================================="
echo "Paper A Lean Verification Status"
echo "Date: $(date)"
echo "==================================="
echo ""

echo "Step 1: Check cited files for sorries..."
echo ""

CITED_FILES=(
  "Circuits_ParityDiversitySeparation"
  "Learning_ComputationalComplexity"
  "Learning_DiversityApproximation"
  "Learning_DiversityBarrier"
  "Learning_DiversityHierarchy"
  "Learning_DiversitySampleComplexity"
  "Learning_StructuralDepthCircuits"
)

TOTAL_SORRIES=0

for file in "${CITED_FILES[@]}"; do
  if [ -f "FormalAnthropology/${file}.lean" ]; then
    SORRIES=$(grep -c "sorry" "FormalAnthropology/${file}.lean" 2>/dev/null || echo 0)
    if [ "$SORRIES" -gt 0 ]; then
      echo "❌ ${file}.lean: $SORRIES sorries"
      TOTAL_SORRIES=$((TOTAL_SORRIES + SORRIES))
    else
      echo "✅ ${file}.lean: 0 sorries"
    fi
  else
    echo "⚠️  ${file}.lean: FILE NOT FOUND"
  fi
done

echo ""
echo "Total sorries in cited files: $TOTAL_SORRIES"
echo ""

if [ $TOTAL_SORRIES -eq 0 ]; then
  echo "✅ SUCCESS: Paper's claim of 'zero sorry statements' is TRUE"
else
  echo "❌ FAILURE: Paper has false claims about sorry-free proofs"
fi

echo ""
echo "Step 2: New files created this session..."
echo ""

NEW_FILES=(
  "Circuits_StructuralDiversity"
  "Diversity_NecessityCharacterization"
  "Learning_DiversityTractableCases"
)

for file in "${NEW_FILES[@]}"; do
  if [ -f "FormalAnthropology/${file}.lean" ]; then
    LINES=$(wc -l < "FormalAnthropology/${file}.lean")
    SORRIES=$(grep -c "sorry" "FormalAnthropology/${file}.lean" 2>/dev/null || echo 0)
    echo "📝 ${file}.lean: $LINES lines, $SORRIES sorries"
  else
    echo "⚠️  ${file}.lean: NOT CREATED"
  fi
done

echo ""
echo "Step 3: Overall codebase statistics..."
echo ""

TOTAL_FILES=$(find FormalAnthropology -name "*.lean" -type f | wc -l)
FILES_WITH_SORRIES=$(find FormalAnthropology -name "*.lean" -type f -exec grep -l "sorry" {} \; 2>/dev/null | wc -l)
FILES_WITHOUT_SORRIES=$((TOTAL_FILES - FILES_WITH_SORRIES))

echo "Total Lean files: $TOTAL_FILES"
echo "Files with sorries: $FILES_WITH_SORRIES"
echo "Files without sorries: $FILES_WITHOUT_SORRIES"
echo "Percentage complete: $(( FILES_WITHOUT_SORRIES * 100 / TOTAL_FILES ))%"

echo ""
echo "==================================="
echo "Verification Complete"
echo "==================================="
