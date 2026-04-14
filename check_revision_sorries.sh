#!/bin/bash

echo "=== CHECKING FOR SORRIES IN REVISION PLAN THEOREMS ==="
echo ""

# Files that should exist according to the revision plan
FILES=(
  "Learning_DiversityBarrier.lean"
  "Learning_DiversityIndependence.lean"
  "Learning_DiversityHierarchy.lean"
  "Learning_DiversityNecessity_Complete.lean"
  "Learning_ComputationalComplexity.lean"
  "Learning_GreedyOptimalitySubmodular.lean"
  "Learning_DiversityTractable.lean"
  "Learning_NaturalGeneratorsSubmodular.lean"
  "Learning_PACFormalization.lean"
  "Learning_ImproperLearningDiversityGap.lean"
  "Learning_DiversityOptimalSynthesis.lean"
  "Learning_StructuralDepthCircuits.lean"
  "Learning_DiversityDepthTradeoff.lean"
)

# New theorems that need to be created (Theorems 23-27)
NEW_FILES=(
  "Learning_DiversityCharacterization.lean"
  "Learning_DiversityExpressivenessPhaseTransition.lean"
  "Learning_SampleComplexityTight.lean"
  "Learning_ActiveDiversityReduction.lean"
  "Learning_DiversityCommunicationComplexity.lean"
)

for file in "${FILES[@]}"; do
  if [ -f "FormalAnthropology/$file" ]; then
    COUNT=$(grep -c "sorry" "FormalAnthropology/$file" 2>/dev/null || echo "0")
    if [ "$COUNT" -gt 0 ]; then
      echo "❌ $file: $COUNT sorries"
    else
      echo "✅ $file: 0 sorries"
    fi
  else
    echo "🚫 $file: FILE NOT FOUND"
  fi
done

echo ""
echo "=== NEW THEOREMS (23-27) ==="
for file in "${NEW_FILES[@]}"; do
  if [ -f "FormalAnthropology/$file" ]; then
    COUNT=$(grep -c "sorry" "FormalAnthropology/$file" 2>/dev/null || echo "0")
    if [ "$COUNT" -gt 0 ]; then
      echo "⚠️  $file: EXISTS with $COUNT sorries"
    else
      echo "✅ $file: EXISTS with 0 sorries"
    fi
  else
    echo "📝 $file: NEEDS TO BE CREATED"
  fi
done
