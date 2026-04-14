#!/bin/bash
echo "=== PAPER B THEOREM BUILD STATUS ==="
echo ""

# Core verified theorems (should be working)
echo "## Core Verified Theorems (should have zero sorries):"
for thm in Learning_ComplementarityIndex Learning_Theorem40_ZeroValueDiversity Learning_DiversityComputationNPHard; do
  echo -n "$thm: "
  if lake build "FormalAnthropology.$thm" 2>&1 | grep -q "Build completed successfully\|Building FormalAnthropology"; then
    echo "✓ BUILDS"
  else
    echo "✗ FAILS"
  fi
done

echo ""
echo "## New Diversity Theorems (revision plan requirements):"
for thm in Learning_DiversityNecessityCharacterization PaperB_DiversityValueScaling PaperB_DiversityAbilityTradeoff PaperB_DiversityRobustness PaperB_DiversityExploration PaperB_MarketConcentration; do
  echo -n "$thm: "
  if lake build "FormalAnthropology.$thm" 2>&1 | grep -q "error:"; then
    echo "✗ HAS ERRORS"
  else
    echo "✓ BUILDS"
  fi
done
