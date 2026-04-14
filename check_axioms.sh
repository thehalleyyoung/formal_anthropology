#!/bin/bash
echo "Checking axioms for completed revision theorems..."
echo ""

FILES=(
    "FormalAnthropology/Learning_DominanceCorrected.lean"
    "FormalAnthropology/Learning_SeedRobustness.lean"
    "FormalAnthropology/Learning_DiversityDominatesDepth.lean"
    "FormalAnthropology/Learning_DiversityExpressiveness.lean"
    "FormalAnthropology/Learning_DiversityComputationNPHard.lean"
)

for f in "${FILES[@]}"; do
    echo "=== $(basename $f .lean) ==="
    grep -n "^axiom" "$f" 2>/dev/null || echo "  No axioms declared"
    echo ""
done
