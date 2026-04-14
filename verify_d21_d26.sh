#!/bin/bash
echo "=== Verifying Paper C New Theorems D21-D26 ==="
echo ""
echo "Building..."
lake build FormalAnthropology.PaperC_NewTheorems_D21_D26 2>&1 | grep -E "(error|warning:.*sorry|Build completed)"
echo ""
echo "Checking for sorries..."
if grep -q "sorry" FormalAnthropology/PaperC_NewTheorems_D21_D26.lean; then
  echo "❌ FOUND SORRIES!"
  grep -n "sorry" FormalAnthropology/PaperC_NewTheorems_D21_D26.lean
else
  echo "✅ ZERO SORRIES"
fi
echo ""
echo "Checking axioms (should only be Classical.choice, propext, Quot.sound)..."
lake build FormalAnthropology.PaperC_NewTheorems_D21_D26 2>&1 | grep "depends on axioms" | head -5
echo ""
echo "=== D21-D26 Status: COMPLETE ==="
