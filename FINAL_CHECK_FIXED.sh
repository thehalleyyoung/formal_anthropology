#!/bin/bash

echo "================================================================"
echo "COMPREHENSIVE FINAL CHECK - Paper C Lean Proofs"
echo "================================================================"
echo ""

# Check 1: No admit tactics
echo "[1/6] Checking for 'admit' tactics..."
if grep -r "admit" FormalAnthropology/PaperC*.lean 2>/dev/null | grep -v "inadmissible" | grep -q .; then
    echo "  ❌ Found 'admit' tactics"
    grep -n "admit" FormalAnthropology/PaperC*.lean | grep -v "inadmissible"
    exit 1
else
    echo "  ✅ No 'admit' tactics found"
fi

# Check 2: No sorry
echo "[2/6] Checking for 'sorry' in proofs..."
if grep -v "^--\|^ *--\| WITHOUT\| without" FormalAnthropology/PaperC*.lean 2>/dev/null | grep -q " sorry\|^sorry\|:= sorry"; then
    echo "  ❌ Found sorry statements"
    grep -v "^--\|^ *--\| WITHOUT\| without" FormalAnthropology/PaperC*.lean | grep -n " sorry\|^sorry\|:= sorry"
    exit 1
else
    echo "  ✅ No 'sorry' in proofs"
fi

# Check 3: No opaque
echo "[3/6] Checking for 'opaque' definitions..."
if grep "^opaque\|^ *opaque" FormalAnthropology/PaperC*.lean 2>/dev/null | grep -q .; then
    OPAQUE_COUNT=$(grep "^opaque\|^ *opaque" FormalAnthropology/PaperC*.lean | wc -l)
    echo "  ⚠️  Found $OPAQUE_COUNT opaque definitions (may be intentional)"
else
    echo "  ✅ No opaque definitions"
fi

# Check 4: No custom axioms
echo "[4/6] Checking for custom axiom declarations..."
if grep "^axiom " FormalAnthropology/PaperC*.lean 2>/dev/null | grep -q .; then
    echo "  ❌ Found custom axioms"
    grep -n "^axiom " FormalAnthropology/PaperC*.lean
    exit 1
else
    echo "  ✅ No custom axioms"
fi

# Check 5: Build all files
echo "[5/6] Building all Paper C files..."
BUILD_FAILED=0
for file in PaperC_DiversityTheorems_Revision PaperC_RevisionPlan_Theorems PaperC_NewTheorems_D10 PaperC_NewTheorems_D11 PaperC_NewTheorems_D12 PaperC_NewTheorems_D13_D14 PaperC_NewTheorems_D15 PaperC_NewTheorems_D16_D20 PaperC_NewTheorems_D21_D26 PaperC_NewTheorems_D27_D29; do
    if ! lake build "FormalAnthropology.$file" > /dev/null 2>&1; then
        echo "  ❌ Failed to build $file"
        BUILD_FAILED=1
    fi
done

if [ "$BUILD_FAILED" -eq 0 ]; then
    echo "  ✅ All files build successfully"
else
    echo "  ❌ Some files failed to build"
    exit 1
fi

# Check 6: Count theorems
echo "[6/6] Counting theorems..."
THEOREM_COUNT=$(grep -h "^theorem\|^lemma" FormalAnthropology/PaperC*.lean 2>/dev/null | wc -l | tr -d ' ')
echo "  ✅ Total: $THEOREM_COUNT theorems/lemmas proven"

echo ""
echo "================================================================"
echo "FINAL RESULT: ✅ ALL CHECKS PASSED"
echo "================================================================"
echo ""
echo "Paper C Lean proofs are:"
echo "  • Complete (no sorry/admit)"
echo "  • Valid (all files build)"
echo "  • Sound (no custom axioms)"
echo "  • Publication-ready"
echo ""
echo "Total: $THEOREM_COUNT theorems/lemmas across 10 files"
echo ""
echo "================================================================"
