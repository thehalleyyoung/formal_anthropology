#!/bin/bash
# Test compilation of Paper A key theorems

echo "Testing Paper A Critical Lean Proofs"
echo "===================================="
echo ""

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

for file in "${FILES[@]}"; do
  echo "Testing: $file"
  if [ -f "$file" ]; then
    sorries=$(grep -c "^ *sorry" "$file" 2>/dev/null || echo 0)
    echo "  Sorries: $sorries"
  else
    echo "  FILE NOT FOUND"
  fi
done

echo ""
echo "Attempting full build..."
lake build FormalAnthropology 2>&1 | tail -20
