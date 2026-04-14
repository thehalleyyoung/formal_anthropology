#!/bin/bash
# Verify all Paper B new theorems build with zero errors and zero sorries

echo "======================================"
echo "Paper B New Theorems Verification"
echo "Date: $(date)"
echo "======================================"
echo ""

echo "Checking for sorries in Paper B files..."
SORRIES=$(grep -r "sorry" FormalAnthropology/PaperB_*.lean 2>/dev/null | wc -l)
if [ $SORRIES -eq 0 ]; then
    echo "✅ ZERO sorries found in Paper B files"
else
    echo "❌ Found $SORRIES sorries:"
    grep -n "sorry" FormalAnthropology/PaperB_*.lean
fi
echo ""

echo "Building Paper B new theorem files..."
FILES=(
    "FormalAnthropology.PaperB_DiversityValueScaling"
    "FormalAnthropology.PaperB_DiversityAbilityTradeoff"
    "FormalAnthropology.PaperB_DiversityRobustness"
    "FormalAnthropology.PaperB_MarketConcentration"
    "FormalAnthropology.PaperB_DiversityExploration"
)

BUILD_SUCCESS=0
BUILD_FAIL=0

for file in "${FILES[@]}"; do
    echo "Building $file..."
    if lake build "$file" 2>&1 | grep -q "^error:"; then
        echo "❌ Build failed for $file"
        BUILD_FAIL=$((BUILD_FAIL + 1))
    else
        echo "✅ Build succeeded for $file"
        BUILD_SUCCESS=$((BUILD_SUCCESS + 1))
    fi
done

echo ""
echo "======================================"
echo "VERIFICATION SUMMARY"
echo "======================================"
echo "Sorries found: $SORRIES"
echo "Files built successfully: $BUILD_SUCCESS"
echo "Files failed to build: $BUILD_FAIL"
echo ""

if [ $SORRIES -eq 0 ] && [ $BUILD_FAIL -eq 0 ]; then
    echo "🎉 ALL CHECKS PASSED! Paper B new theorems are ready."
    exit 0
else
    echo "⚠️  Some checks failed. Review output above."
    exit 1
fi
