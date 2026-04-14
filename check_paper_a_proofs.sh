#!/bin/bash

echo "=== PAPER A CRITICAL PROOFS STATUS ==="
echo ""

# Files mentioned in NEW_THEOREMS_LIST.md
declare -a files=(
  "Learning_DepthDiversitySampleComplexity"
  "Learning_DepthDiversityGeneralizationBound" 
  "Learning_PAC_DiversityGap_Strong"
  "Learning_MacroDiversityPreservation"
  "Learning_CanonicalSeedNormalization"
  "Learning_DiversityGreedyApproximation"
  "Learning_DiversityTractableCases"
  "Learning_DominanceCorrected"
  "Learning_DiversityComputationNPComplete"
  "Learning_TypeSeparationCharacterization"
  "Learning_DiversityDominatesDepth"
  "Learning_DiversityExpressiveness"
  "Learning_DiversityNecessityComplete"
  "Learning_DiversityExpressivenessExplosion"
  "Learning_GreedyRuntimeBound"
  "Learning_DiversityTractable"
  "Learning_CircuitDepthTightness"
  "Learning_ResolutionDepthTightness"
  "Learning_ASTMaxArityTightness"
  "Learning_DiversityBarrier"
  "Learning_DiversityHierarchy"
  "Learning_ComputationalComplexity"
  "Learning_DiversityApproximation"
  "Learning_DiversitySampleComplexity"
  "Learning_StructuralDepthCircuits"
)

for base in "${files[@]}"; do
  file="FormalAnthropology/${base}.lean"
  if [ -f "$file" ]; then
    sorries=$(grep -c "sorry" "$file" 2>/dev/null || echo "0")
    if [ "$sorries" = "0" ]; then
      echo "✓ $base: EXISTS (0 sorries)"
    else
      echo "⚠ $base: EXISTS ($sorries sorries)"
    fi
  else
    echo "✗ $base: MISSING"
  fi
done
