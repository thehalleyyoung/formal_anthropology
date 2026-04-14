#!/bin/bash
# verify_paper_a_revision_theorems.sh
# Verifies all theorems required for Paper A revision

set -e

cd "$(dirname "$0")"

echo "=========================================="
echo "Paper A Revision Theorem Verification"
echo "=========================================="
echo ""

CORE_FILES=(
  "Learning_DiversityBarrier"
  "Learning_DiversityIndependence"
  "Learning_DiversityHierarchy"
  "Learning_DiversityNecessity_Complete"
  "Learning_ComputationalComplexity"
  "Learning_NaturalGeneratorsSubmodular"
  "Learning_PACFormalization"
)

NEW_FILES=(
  "Learning_DiversityCharacterization"
  "Learning_DiversityExpressivenessTradeoff"
  "Learning_VCDiversityProductTightness"
  "Learning_ActiveDiversityReduction"
  "Learning_GreedyOptimalitySubmodular"
  "Learning_DSLDesignOptimality"
  "Learning_DiversityCommunicationComplexity"
  "Learning_DiversityStability"
)

CORE_PASS=0
CORE_TOTAL=${#CORE_FILES[@]}
NEW_PASS=0
NEW_TOTAL=${#NEW_FILES[@]}

echo "=== VERIFYING CORE THEOREMS (Theorems 5-18) ==="
for file in "${CORE_FILES[@]}"; do
  echo -n "  $file ... "
  
  # Check file exists
  if [ ! -f "FormalAnthropology/${file}.lean" ]; then
    echo "❌ FILE NOT FOUND"
    continue
  fi
  
  # Check for sorries
  sorries=$(grep "sorry" "FormalAnthropology/${file}.lean" 2>/dev/null | wc -l | xargs)
  if [ "$sorries" != "0" ]; then
    echo "❌ $sorries sorries"
    continue
  fi
  
  # Check build
  lake build "FormalAnthropology.${file}" > /tmp/build_${file}.log 2>&1
  if [ $? -ne 0 ]; then
    echo "❌ Build failed"
    continue
  fi
  
  echo "✅ PASS"
  ((CORE_PASS++))
done

echo ""
echo "=== VERIFYING NEW THEOREMS (Theorems 23-30) ==="
for file in "${NEW_FILES[@]}"; do
  echo -n "  $file ... "
  
  # Check file exists
  if [ ! -f "FormalAnthropology/${file}.lean" ]; then
    echo "❌ FILE NOT FOUND"
    continue
  fi
  
  # Check for sorries
  sorries=$(grep "sorry" "FormalAnthropology/${file}.lean" 2>/dev/null | wc -l | xargs)
  if [ "$sorries" != "0" ]; then
    echo "❌ $sorries sorries"
    continue
  fi
  
  # Check build
  lake build "FormalAnthropology.${file}" > /tmp/build_${file}.log 2>&1
  if [ $? -ne 0 ]; then
    echo "❌ Build failed"
    continue
  fi
  
  echo "✅ PASS"
  ((NEW_PASS++))
done

echo ""
echo "=========================================="
echo "RESULTS"
echo "=========================================="
echo "Core Theorems:  $CORE_PASS / $CORE_TOTAL passed"
echo "New Theorems:   $NEW_PASS / $NEW_TOTAL passed"
echo "Total:          $((CORE_PASS + NEW_PASS)) / $((CORE_TOTAL + NEW_TOTAL)) passed"
echo ""

if [ $((CORE_PASS + NEW_PASS)) -eq $((CORE_TOTAL + NEW_TOTAL)) ]; then
  echo "✅ ALL THEOREMS VERIFIED - READY FOR PUBLICATION"
  exit 0
elif [ $CORE_PASS -eq $CORE_TOTAL ] && [ $NEW_PASS -ge 4 ]; then
  echo "⚠️  MINIMUM VIABLE - Core complete + 4 new theorems"
  exit 0
else
  echo "❌ VERIFICATION INCOMPLETE - More work needed"
  exit 1
fi
