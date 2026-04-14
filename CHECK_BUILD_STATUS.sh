#!/bin/bash
# Quick check of which files build successfully

echo "Testing Paper B Theorem Files"
echo "=============================="
echo ""

SUCCESS=0
FAIL=0

FILES=(
    "Learning_CollectiveAccess"
    "Learning_EmergenceCharacterization_NoSorries"
    "Learning_ComplementarityIndex"
    "Mechanism_CompleteInformation"
    "Mechanism_Sequential"
    "Mechanism_PatentPools"
    "Welfare_MarketStructure_NoSorries"
    "Welfare_TeamComposition_NoSorries"
    "Learning_HomogeneityDominates"
)

echo "Files that SHOULD build successfully:"
echo "-------------------------------------"
for file in "${FILES[@]}"; do
    if lake build "FormalAnthropology.$file" >/dev/null 2>&1; then
        echo "✅ $file"
        SUCCESS=$((SUCCESS + 1))
    else
        echo "❌ $file"
        FAIL=$((FAIL + 1))
    fi
done

echo ""
echo "Summary: $SUCCESS building, $FAIL failed"
