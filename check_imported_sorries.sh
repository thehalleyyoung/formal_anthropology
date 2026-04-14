#!/bin/bash

# Extract uncommented imports from FormalAnthropology.lean
imports=$(grep "^import FormalAnthropology\.Learning" FormalAnthropology.lean | sed 's/import FormalAnthropology\.//' | sed 's/ .*//')

echo "=== Checking Imported Files for Sorries ==="
echo ""

has_sorries=0
total=0

for module in $imports; do
  file="FormalAnthropology/${module}.lean"
  total=$((total + 1))
  if [ -f "$file" ]; then
    sorries=$(grep -c "sorry" "$file" 2>/dev/null || echo "0")
    if [ "$sorries" != "0" ] && [ "$sorries" -gt 0 ]; then
      echo "⚠️  $module: $sorries sorries"
      has_sorries=$((has_sorries + 1))
    fi
  fi
done

echo ""
echo "=== SUMMARY ==="
echo "Total imported Learning_* files: $total"
echo "Files with sorries: $has_sorries"
echo "Files clean: $((total - has_sorries))"
