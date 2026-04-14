#!/bin/bash
# Build all NEW theorems from REVISION_PLAN.md

echo "=== Building Revision Plan Theorems ==="
echo ""

# NEW-4: Diversity-Depth Independence
echo "[1/7] Building DiversityIndependence..."
lake build FormalAnthropology.Learning_DiversityIndependence
if [ $? -eq 0 ]; then
  echo "✅ DiversityIndependence: SUCCESS"
else
  echo "❌ DiversityIndependence: FAILED"
fi
echo ""

# NEW-3: Circuit Depth Tightness
echo "[2/7] Building CircuitDepthTightness..."
lake build FormalAnthropology.Learning_CircuitDepthTightness
if [ $? -eq 0 ]; then
  echo "✅ CircuitDepthTightness: SUCCESS"
else
  echo "❌ CircuitDepthTightness: FAILED"
fi
echo ""

# NEW-1: Resolution Depth Tightness
echo "[3/7] Building ResolutionDepthTightness..."
lake build FormalAnthropology.Learning_ResolutionDepthTightness
if [ $? -eq 0 ]; then
  echo "✅ ResolutionDepthTightness: SUCCESS"
else
  echo "❌ ResolutionDepthTightness: FAILED"
fi
echo ""

# NEW-2: AST Max-Arity Tightness
echo "[4/7] Building ASTMaxArityTightness..."
lake build FormalAnthropology.Learning_ASTMaxArityTightness
if [ $? -eq 0 ]; then
  echo "✅ ASTMaxArityTightness: SUCCESS"
else
  echo "❌ ASTMaxArityTightness: FAILED"
fi
echo ""

# NEW-5: Diversity Necessity
echo "[5/7] Building DiversityNecessityComplete..."
lake build FormalAnthropology.Learning_DiversityNecessityComplete
if [ $? -eq 0 ]; then
  echo "✅ DiversityNecessityComplete: SUCCESS"
else
  echo "❌ DiversityNecessityComplete: FAILED"
fi
echo ""

# NEW-6: Expressiveness Explosion
echo "[6/7] Building DiversityExpressivenessExplosion..."
lake build FormalAnthropology.Learning_DiversityExpressivenessExplosion
if [ $? -eq 0 ]; then
  echo "✅ DiversityExpressivenessExplosion: SUCCESS"
else
  echo "❌ DiversityExpressivenessExplosion: FAILED"
fi
echo ""

# NEW-7: Greedy Runtime
echo "[7/7] Building GreedyRuntimeBound..."
lake build FormalAnthropology.Learning_GreedyRuntimeBound
if [ $? -eq 0 ]; then
  echo "✅ GreedyRuntimeBound: SUCCESS"
else
  echo "❌ GreedyRuntimeBound: FAILED"
fi
echo ""

echo "=== Build Summary ==="
echo "Check logs above for details"
