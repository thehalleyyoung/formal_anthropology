#!/bin/bash
# Test script to verify all Paper B proofs build successfully with zero sorries

echo "========================================="
echo "Paper B: Complete Proof Verification"
echo "========================================="
echo ""

# List of files to test
FILES=(
    "PaperB_CoreTheorems"
    "Learning_EmergenceCharacterization_NoSorries"
    "Welfare_TeamComposition_NoSorries"
    "Welfare_MarketStructure_NoSorries"
    "Mechanism_CompleteInformation"
    "Mechanism_Sequential"
    "Learning_CollectiveAccess"
)

BUILD_ERRORS=0
SORRY_COUNT=0

echo "Step 1: Checking for sorries..."
echo "-----------------------------------"
for file in "${FILES[@]}"; do
    SORRIES=$(grep -n "sorry" FormalAnthropology/${file}.lean 2>/dev/null | grep -v "sorry-free" | grep -v "^[[:space:]]*--" | wc -l)
    if [ "$SORRIES" -gt 0 ]; then
        echo "❌ $file: Found $SORRIES sorries"
        SORRY_COUNT=$((SORRY_COUNT + SORRIES))
    else
        echo "✅ $file: 0 sorries"
    fi
done
echo ""

echo "Step 2: Building all files..."
echo "-----------------------------------"
for file in "${FILES[@]}"; do
    echo -n "Building $file... "
    if lake build FormalAnthropology.$file 2>&1 | grep -q "Build completed successfully"; then
        echo "✅"
    else
        echo "❌"
        BUILD_ERRORS=$((BUILD_ERRORS + 1))
    fi
done
echo ""

echo "========================================="
echo "FINAL RESULTS"
echo "========================================="
echo "Total files tested: ${#FILES[@]}"
echo "Build errors: $BUILD_ERRORS"
echo "Total sorries: $SORRY_COUNT"
echo ""

if [ $BUILD_ERRORS -eq 0 ] && [ $SORRY_COUNT -eq 0 ]; then
    echo "✅ ALL TESTS PASSED"
    echo "   - Zero sorries across all files"
    echo "   - All files build successfully"
    echo "   - Paper B proofs are complete and verified"
    exit 0
else
    echo "❌ TESTS FAILED"
    [ $SORRY_COUNT -gt 0 ] && echo "   - Found $SORRY_COUNT unproven sorries"
    [ $BUILD_ERRORS -gt 0 ] && echo "   - $BUILD_ERRORS files failed to build"
    exit 1
fi
