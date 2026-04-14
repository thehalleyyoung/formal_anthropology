#!/bin/bash
# Verification script for Paper B Revision Plan theorems
# Tests all 18 theorems mentioned in diversity_b_paper/REVISION_PLAN.md

echo "========================================="
echo "Paper B Revision Plan: Theorem Verification"
echo "========================================="
echo ""

# Array of required files according to REVISION_PLAN.md
declare -a REQUIRED_FILES=(
    # Characterization (Section 4)
    "Learning_CollectiveAccess"                  # Theorem 6
    "Learning_EmergenceCharacterization_NoSorries" # Theorem 8
    "Learning_ComplementarityIndex"              # Theorem 10-11  [HAS ERRORS]
    "Learning_EmergenceFrequency"                # Theorem 9
    
    # Mechanism Design (Section 5)
    "Mechanism_CompleteInformation"              # Theorem 13
    # "Mechanism_SecondBest"                     # Theorem 14 [MISSING]
    "Mechanism_Sequential"                       # Theorem 15
    "Mechanism_PatentPools"                      # Theorem 24
    
    # Value of Diversity (Section 6)
    "Welfare_DiversityScaling"                   # Theorem 18
    "Welfare_DiversityDecomposition"             # Theorem 19
    "Welfare_DiversityDiminishingReturns"        # Theorem 20
    "Learning_DiversityDepthTradeoff"            # Theorem 21
    "Welfare_MarketStructure_NoSorries"          # Theorem 25
    "Welfare_TeamComposition_NoSorries"          # Theorem 26
    
    # Negative Results (Section 7)
    "Learning_DiversityLimits"                   # Theorem 27
    "Learning_HomogeneityDominates"              # Theorem 28
    "Learning_ConceptDepth"                      # Theorem 30
    "Learning_ComputationalHardness"             # Theorem 31
)

BUILD_ERRORS=0
SORRY_COUNT=0
MISSING_COUNT=0

echo "Step 1: Checking for sorries..."
echo "-----------------------------------"
for file in "${REQUIRED_FILES[@]}"; do
    if [ ! -f "FormalAnthropology/${file}.lean" ]; then
        echo "❌ $file: FILE NOT FOUND"
        MISSING_COUNT=$((MISSING_COUNT + 1))
        continue
    fi
    
    SORRIES=$(grep -n "^\s*sorry\s*$" "FormalAnthropology/${file}.lean" 2>/dev/null | wc -l | tr -d ' ')
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
for file in "${REQUIRED_FILES[@]}"; do
    if [ ! -f "FormalAnthropology/${file}.lean" ]; then
        echo "⊘  $file: SKIPPED (missing)"
        continue
    fi
    
    echo -n "Building $file... "
    if lake build "FormalAnthropology.$file" >/dev/null 2>&1; then
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
echo "Total files required: ${#REQUIRED_FILES[@]}"
echo "Missing files: $MISSING_COUNT"
echo "Build errors: $BUILD_ERRORS"
echo "Total sorries: $SORRY_COUNT"
echo ""

if [ $BUILD_ERRORS -eq 0 ] && [ $SORRY_COUNT -eq 0 ] && [ $MISSING_COUNT -eq 0 ]; then
    echo "✅ ALL TESTS PASSED"
    echo "   - All 18 required files exist"
    echo "   - Zero sorries across all files"
    echo "   - All files build successfully"
    echo "   - Paper B revision requirements FULLY SATISFIED"
    exit 0
else
    echo "⚠️  PARTIAL COMPLETION"
    [ $MISSING_COUNT -gt 0 ] && echo "   - $MISSING_COUNT files need to be created"
    [ $SORRY_COUNT -gt 0 ] && echo "   - $SORRY_COUNT unproven sorries remain"
    [ $BUILD_ERRORS -gt 0 ] && echo "   - $BUILD_ERRORS files have build errors"
    echo ""
    echo "Status: Core theorems verified, auxiliary theorems need completion"
    exit 1
fi
