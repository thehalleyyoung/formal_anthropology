#!/bin/bash
echo "=== Checking for sorries in all revision plan files ==="
for file in FormalAnthropology/Learning_CollectiveAccess.lean \
            FormalAnthropology/Welfare_DiversityScaling_Proven.lean \
            FormalAnthropology/Welfare_DiversityDiminishingReturns.lean \
            FormalAnthropology/Learning_DiversityDepthTradeoff.lean \
            FormalAnthropology/Learning_StructuralCharacterization.lean \
            FormalAnthropology/Learning_GenericEmergence.lean \
            FormalAnthropology/Welfare_HeterogeneousValues.lean \
            FormalAnthropology/Learning_HomogeneityDominates.lean \
            FormalAnthropology/Learning_CollaborationFailure.lean \
            FormalAnthropology/Learning_CIThresholdDistribution.lean \
            FormalAnthropology/Learning_CIPrediction.lean; do
    count=$(grep -c "sorry" "$file" 2>/dev/null || echo "0")
    echo "$(basename $file): $count sorries"
done
