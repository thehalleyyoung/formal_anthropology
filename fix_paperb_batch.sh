#!/bin/bash
echo "Building all remaining PaperB theorems..."

for thm in PaperB_DiversityAbilityTradeoff PaperB_DiversityRobustness PaperB_DiversityExploration PaperB_MarketConcentration; do
  echo ""
  echo "=== $thm ==="
  lake build "FormalAnthropology.$thm" 2>&1 | grep -E "error:" | head -3
done
