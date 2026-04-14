#!/bin/bash
echo "Checking all Paper C theorems D1-D29..."
for i in {1..29}; do
  echo -n "D$i: "
  if grep -r "theorem.*D$i\|def.*D$i" FormalAnthropology/PaperC*.lean 2>/dev/null | head -1 | cut -d: -f2 | head -c 80; then
    echo ""
  else
    echo "NOT FOUND"
  fi
done
