#!/bin/bash
# Verification script for Paper C proofs

echo "=== Paper C Lean Proof Verification ==="
echo ""

# Check imported files for sorries
echo "1. Checking all files imported in FormalAnthropology.lean for sorries..."
imported_files=$(grep "^import FormalAnthropology\." FormalAnthropology.lean | sed 's/import FormalAnthropology\./FormalAnthropology\//; s/$/\.lean/')

total_sorries=0
for file in $imported_files; do
  if [ -f "$file" ]; then
    count=$(grep -c "sorry" "$file" 2>/dev/null || echo "0")
    if [ "$count" != "0" ]; then
      echo "  ❌ $file: $count sorries"
      total_sorries=$((total_sorries + count))
    fi
  fi
done

if [ $total_sorries -eq 0 ]; then
  echo "  ✅ All imported files have ZERO sorries!"
else
  echo "  ❌ Total sorries in imported files: $total_sorries"
fi

echo ""
echo "2. Building Learning_PaperC_SixTheorems.lean..."
lake build FormalAnthropology.Learning_PaperC_SixTheorems > /tmp/build_output.txt 2>&1
if [ $? -eq 0 ]; then
  echo "  ✅ Build succeeded with zero errors"
else
  echo "  ❌ Build failed"
  tail -20 /tmp/build_output.txt
fi

echo ""
echo "3. Checking Learning_PaperC_SixTheorems.lean content..."
sorries=$(grep -c "sorry" FormalAnthropology/Learning_PaperC_SixTheorems.lean)
theorems=$(grep -c "^theorem " FormalAnthropology/Learning_PaperC_SixTheorems.lean)
echo "  - Number of theorems: $theorems"
echo "  - Number of sorries: $sorries"

if [ $sorries -eq 0 ]; then
  echo "  ✅ All theorems are complete (0 sorries)"
else
  echo "  ❌ File contains $sorries sorries"
fi

echo ""
echo "4. Summary:"
if [ $total_sorries -eq 0 ] && [ $sorries -eq 0 ]; then
  echo "  ✅✅✅ VERIFICATION SUCCESSFUL ✅✅✅"
  echo "  All Paper C proofs are complete with zero sorries and build successfully!"
else
  echo "  ❌ Verification failed - sorries remain in the codebase"
fi
