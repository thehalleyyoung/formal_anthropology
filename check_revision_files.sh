#!/bin/bash
echo "=== REVISION PLAN FILE STATUS ==="
echo ""
echo "Files that need work (from revision plan):"
echo ""

files=(
  "Learning_CollectiveAccess.lean"
  "Welfare_DiversityScaling_Proven.lean"
  "Welfare_DiversityDiminishingReturns.lean"
  "Learning_DiversityDepthTradeoff.lean"
  "Learning_StructuralCharacterization.lean"
  "Learning_GenericEmergence.lean"
  "Welfare_HeterogeneousValues.lean"
  "Learning_HomogeneityDominates.lean"
  "Learning_CollaborationFailure.lean"
  "Learning_CIThresholdDistribution.lean"
  "Learning_CIPrediction.lean"
)

for file in "${files[@]}"; do
  filepath="FormalAnthropology/$file"
  if [ -f "$filepath" ]; then
    sorries=$(grep -c "sorry" "$filepath" 2>/dev/null || echo "0")
    axioms=$(grep -c "^axiom\|^noncomputable axiom" "$filepath" 2>/dev/null || echo "0")
    echo "✓ $file - sorries: $sorries, axioms: $axioms"
  else
    echo "✗ $file - FILE MISSING"
  fi
done
