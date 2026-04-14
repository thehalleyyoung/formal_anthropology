#!/bin/bash
echo "================================================================"
echo "PAPER C FINAL VALIDATION - D1-D14 COMPLETE VERIFICATION"
echo "================================================================"
echo ""

PASS=0
FAIL=0

# Test 1: No sorries
echo "TEST 1: Checking for sorries..."
SORRY_COUNT=$(grep -r "sorry" FormalAnthropology/PaperC*.lean | grep -v "WITHOUT sorry" | grep -v "zero sorries" | grep -v "ZERO SORRIES" | grep -v "0 sorries" | wc -l | tr -d ' ')
if [ "$SORRY_COUNT" = "0" ]; then
    echo "  ✅ PASS: Zero sorries found"
    PASS=$((PASS + 1))
else
    echo "  ❌ FAIL: Found $SORRY_COUNT sorries"
    FAIL=$((FAIL + 1))
    grep -r "sorry" FormalAnthropology/PaperC*.lean | grep -v "WITHOUT sorry"
fi
echo ""

# Test 2: No custom axioms
echo "TEST 2: Checking for custom axioms..."
AXIOM_COUNT=$(grep "^axiom\|^noncomputable axiom" FormalAnthropology/PaperC*.lean | wc -l | tr -d ' ')
if [ "$AXIOM_COUNT" = "0" ]; then
    echo "  ✅ PASS: Zero custom axioms declared"
    PASS=$((PASS + 1))
else
    echo "  ❌ FAIL: Found $AXIOM_COUNT custom axioms"
    FAIL=$((FAIL + 1))
    grep "^axiom" FormalAnthropology/PaperC*.lean
fi
echo ""

# Test 3: All files exist
echo "TEST 3: Checking all required files exist..."
REQUIRED_FILES=(
    "FormalAnthropology/PaperC_DiversityTheorems_Revision.lean"
    "FormalAnthropology/PaperC_RevisionPlan_Theorems.lean"
    "FormalAnthropology/PaperC_NewTheorems_D10.lean"
    "FormalAnthropology/PaperC_NewTheorems_D11.lean"
    "FormalAnthropology/PaperC_NewTheorems_D12.lean"
    "FormalAnthropology/PaperC_NewTheorems_D13_D14.lean"
)

ALL_EXIST=true
for file in "${REQUIRED_FILES[@]}"; do
    if [ -f "$file" ]; then
        echo "  ✅ $file"
    else
        echo "  ❌ MISSING: $file"
        ALL_EXIST=false
    fi
done

if [ "$ALL_EXIST" = true ]; then
    echo "  ✅ PASS: All required files exist"
    PASS=$((PASS + 1))
else
    echo "  ❌ FAIL: Some files missing"
    FAIL=$((FAIL + 1))
fi
echo ""

# Test 4: Build succeeds
echo "TEST 4: Building all Paper C files..."
BUILD_OUTPUT=$(lake build FormalAnthropology.PaperC_DiversityTheorems_Revision \
                          FormalAnthropology.PaperC_RevisionPlan_Theorems \
                          FormalAnthropology.PaperC_NewTheorems_D10 \
                          FormalAnthropology.PaperC_NewTheorems_D11 \
                          FormalAnthropology.PaperC_NewTheorems_D12 \
                          FormalAnthropology.PaperC_NewTheorems_D13_D14 2>&1)
BUILD_EXIT=$?

if [ $BUILD_EXIT -eq 0 ]; then
    echo "  ✅ PASS: All files build successfully"
    PASS=$((PASS + 1))
else
    echo "  ❌ FAIL: Build failed with exit code $BUILD_EXIT"
    FAIL=$((FAIL + 1))
    echo "$BUILD_OUTPUT" | tail -20
fi
echo ""

# Test 5: Check theorem count
echo "TEST 5: Checking theorem coverage..."
echo "  Counting theorems in each file..."

D1_D5_COUNT=$(grep -c "^theorem" FormalAnthropology/PaperC_DiversityTheorems_Revision.lean || echo 0)
D6_D9_COUNT=$(grep -c "^theorem" FormalAnthropology/PaperC_RevisionPlan_Theorems.lean || echo 0)
D10_COUNT=$(grep -c "^theorem" FormalAnthropology/PaperC_NewTheorems_D10.lean || echo 0)
D11_COUNT=$(grep -c "^theorem" FormalAnthropology/PaperC_NewTheorems_D11.lean || echo 0)
D12_COUNT=$(grep -c "^theorem" FormalAnthropology/PaperC_NewTheorems_D12.lean || echo 0)
D13_D14_COUNT=$(grep -c "^theorem" FormalAnthropology/PaperC_NewTheorems_D13_D14.lean || echo 0)

echo "  D1-D5:   $D1_D5_COUNT theorems (expected: 5+)"
echo "  D6-D9:   $D6_D9_COUNT theorems (expected: 4+)"
echo "  D10:     $D10_COUNT theorems (expected: 4+)"
echo "  D11:     $D11_COUNT theorems (expected: 3+)"
echo "  D12:     $D12_COUNT theorems (expected: 5+)"
echo "  D13-D14: $D13_D14_COUNT theorems (expected: 5+)"

TOTAL_THEOREMS=$((D1_D5_COUNT + D6_D9_COUNT + D10_COUNT + D11_COUNT + D12_COUNT + D13_D14_COUNT))
echo "  Total:   $TOTAL_THEOREMS theorems"

if [ $TOTAL_THEOREMS -ge 26 ]; then
    echo "  ✅ PASS: Adequate theorem coverage ($TOTAL_THEOREMS ≥ 26)"
    PASS=$((PASS + 1))
else
    echo "  ❌ FAIL: Insufficient theorems ($TOTAL_THEOREMS < 26)"
    FAIL=$((FAIL + 1))
fi
echo ""

# Final Report
echo "================================================================"
echo "FINAL VALIDATION REPORT"
echo "================================================================"
echo ""
echo "Tests Passed: $PASS / 5"
echo "Tests Failed: $FAIL / 5"
echo ""

if [ $FAIL -eq 0 ]; then
    echo "🎉 ALL TESTS PASSED 🎉"
    echo ""
    echo "Paper C Lean Proofs Status:"
    echo "  ✅ Theorems D1-D14 completely proven"
    echo "  ✅ Zero sorries"
    echo "  ✅ Zero custom axioms"
    echo "  ✅ All files build successfully"
    echo "  ✅ $TOTAL_THEOREMS theorems formalized and proven"
    echo ""
    echo "RESULT: READY FOR PUBLICATION"
    exit 0
else
    echo "❌ VALIDATION FAILED ❌"
    echo ""
    echo "Please review failed tests above."
    exit 1
fi
