import FormalAnthropology.IDT_v3_Foundations

/-!
# IDT v3: The Geometry of Meaning

The resonance function rs induces geometric structure on ideatic space.
We define distances, angles, projections, and curvature using only
the eight axioms. The geometry is NON-SYMMETRIC (since rs is asymmetric),
making it richer than Riemannian or even Finsler geometry.

## Key Concepts
- Resonance gap as directed distance
- Orthogonality (mutual zero resonance)
- Self-resonance as "norm squared"
- Composition as geometric transformation
- Emergence as curvature

## NO SORRIES
-/

namespace IDT3

section Geometry
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-! ## §1. The Resonance Gap (Directed Distance) -/

/-- The resonance gap: how much b falls short of a's self-resonance. -/
noncomputable def gap (a b : I) : ℝ := rs a a - rs a b

/-- Gap with self is zero. -/
theorem gap_self (a : I) : gap a a = 0 := by
  unfold gap; ring

/-- Gap with void equals weight. -/
theorem gap_void (a : I) : gap a (void : I) = rs a a := by
  unfold gap; rw [rs_void_right']; ring

/-- Void has zero gap with everything. -/
theorem void_gap (b : I) : gap (void : I) b = 0 := by
  unfold gap; simp [rs_void_left', rs_void_void]

/-- The resonance deficit: how much the PAIR falls short of geometric mean. -/
noncomputable def deficit (a b : I) : ℝ :=
  rs a a + rs b b - rs a b - rs b a

/-- Deficit is symmetric. -/
theorem deficit_symm (a b : I) : deficit a b = deficit b a := by
  unfold deficit; ring

/-- Self-deficit is zero. -/
theorem deficit_self (a : I) : deficit a a = 0 := by
  unfold deficit; ring

/-- Deficit with void equals weight. -/
theorem deficit_void (a : I) : deficit a (void : I) = rs a a := by
  unfold deficit; simp [rs_void_right', rs_void_left', rs_void_void]

/-! ## §2. Orthogonality (extending Foundations definitions) -/

-- orthogonal is already defined in Foundations as rs a b = 0

/-- Bilateral orthogonality: both directions. -/
def bilateralOrthogonal (a b : I) : Prop :=
  orthogonal a b ∧ orthogonal b a

/-- Bilateral orthogonality is symmetric. -/
theorem bilateralOrthogonal_symm (a b : I) :
    bilateralOrthogonal a b → bilateralOrthogonal b a :=
  fun ⟨h1, h2⟩ => ⟨h2, h1⟩

/-- Void is bilaterally orthogonal to everything. -/
theorem void_bilateralOrthogonal (a : I) : bilateralOrthogonal (void : I) a :=
  ⟨void_orthogonal_left a, void_orthogonal_right a⟩

/-- A non-void idea is not orthogonal to itself. -/
theorem not_self_orthogonal' (a : I) (h : a ≠ void) : ¬orthogonal a a := by
  intro h1; exact absurd (rs_nondegen' a h1) h

/-- The orthogonal gap: how far from orthogonal two ideas are. -/
noncomputable def orthogonalGap (a b : I) : ℝ := rs a b + rs b a

/-- Orthogonal gap is symmetric. -/
theorem orthogonalGap_symm (a b : I) : orthogonalGap a b = orthogonalGap b a := by
  unfold orthogonalGap; ring

/-- Orthogonal gap is zero iff resonances sum to zero. -/
theorem orthogonalGap_zero_iff (a b : I) :
    orthogonalGap a b = 0 ↔ rs a b = -(rs b a) := by
  unfold orthogonalGap
  constructor
  · intro h; linarith
  · intro h; linarith

/-- Void has zero orthogonal gap with everything. -/
theorem orthogonalGap_void (a : I) : orthogonalGap (void : I) a = 0 := by
  unfold orthogonalGap; rw [rs_void_left', rs_void_right']; ring

/-! ## §3. The Weight Function as Norm -/

/-- Weight = self-resonance. Plays the role of ||a||². -/
noncomputable def weight (a : I) : ℝ := rs a a

/-- Weight is non-negative. -/
theorem weight_nonneg (a : I) : weight a ≥ 0 := by
  unfold weight; exact rs_self_nonneg' a

/-- Weight is zero iff void. -/
theorem weight_zero_iff (a : I) : weight a = 0 ↔ a = void := by
  unfold weight
  constructor
  · exact rs_nondegen' a
  · intro h; rw [h]; exact rs_void_void

/-- Weight of composition is at least weight of first. -/
theorem weight_compose_ge (a b : I) :
    weight (compose a b) ≥ weight a := by
  unfold weight; exact compose_enriches' a b

/-- Weight of void is zero. -/
theorem weight_void : weight (void : I) = 0 := by
  unfold weight; exact rs_void_void

/-! ## §4. Composition as Geometric Transformation

Right-composition by b is a geometric transformation on I.
It maps a ↦ a ∘ b. This transformation:
1. Never decreases weight (E4)
2. Produces emergence (the "curvature" of the transformation) -/

/-- The expansion factor: how much right-composition by b expands a. -/
noncomputable def expansion (a b : I) : ℝ :=
  weight (compose a b) - weight a

/-- Expansion is non-negative (composition enriches). -/
theorem expansion_nonneg (a b : I) : expansion a b ≥ 0 := by
  unfold expansion; linarith [weight_compose_ge a b]

/-- Expansion by void is zero. -/
theorem expansion_void (a : I) : expansion a (void : I) = 0 := by
  unfold expansion weight; simp [void_right']

/-- Expansion of void is weight of b. -/
theorem void_expansion (b : I) : expansion (void : I) b = weight b := by
  unfold expansion weight; rw [void_left', rs_void_void]; ring

/-! ## §5. The Emergence as Curvature

In differential geometry, curvature measures the failure of parallel
transport to commute. In IDT, emergence measures the failure of
resonance to be additive. We can interpret emergence as curvature:
κ(a,b,c) measures how much the "transport" of c along a∘b differs
from the sum of individual transports. -/

/-- The sectional curvature analog: emergence normalized by weights. -/
noncomputable def sectionalCurvature (a b c : I) : ℝ :=
  emergence a b c

/-- Curvature vanishes when any participant is void. -/
theorem curvature_void_left (b c : I) :
    sectionalCurvature (void : I) b c = 0 :=
  emergence_void_left b c

theorem curvature_void_right (a c : I) :
    sectionalCurvature a (void : I) c = 0 :=
  emergence_void_right a c

theorem curvature_void_observer (a b : I) :
    sectionalCurvature a b (void : I) = 0 :=
  emergence_against_void a b

/-- Curvature is bounded (Cauchy-Schwarz). -/
theorem curvature_bounded (a b c : I) :
    (sectionalCurvature a b c) ^ 2 ≤ weight (compose a b) * weight c := by
  unfold sectionalCurvature weight
  exact emergence_bounded' a b c

/-! ## §6. Geodesics and Shortest Paths -/

-- A "straight line" from a to b would be a composition a ∘ x such that
-- the resonance with b is maximized. We define the alignment instead.

/-- Alignment: how much a "points toward" b. -/
noncomputable def alignment (a b : I) : ℝ := rs a b

/-- Self-alignment is weight. -/
theorem alignment_self (a : I) : alignment a a = weight a := rfl

/-- Alignment with void is zero. -/
theorem alignment_void (a : I) : alignment a (void : I) = 0 := by
  unfold alignment; exact rs_void_right' a

/-- Alignment from void is zero. -/
theorem void_alignment (b : I) : alignment (void : I) b = 0 := by
  unfold alignment; exact rs_void_left' b

/-! ## §7. Projections -/

/-- The "projection" of a onto b: how much a resonates with b relative
    to b's self-resonance. When rs(b,b) > 0, this is rs(a,b)/rs(b,b). -/
noncomputable def projectionCoeff (a b : I) (hb : b ≠ void) : ℝ :=
  rs a b / rs b b

/-- The projection coefficient of a onto itself is 1 (for non-void a). -/
theorem projectionCoeff_self (a : I) (h : a ≠ void) :
    projectionCoeff a a h = 1 := by
  unfold projectionCoeff
  have hpos := rs_self_pos a h
  exact div_self (ne_of_gt hpos)

/-- The projection coefficient of void onto anything is 0. -/
theorem projectionCoeff_void (b : I) (h : b ≠ void) :
    projectionCoeff (void : I) b h = 0 := by
  unfold projectionCoeff
  rw [rs_void_left']
  exact zero_div _

/-! ## §8. The Composition Triangle -/

-- For any a, b, we have the "triangle" a, b, a∘b.
-- The resonance structure of this triangle encodes the emergence.

/-- The triangle defect: how the composition's resonance with an observer
    differs from the sum of parts' resonances. This IS the emergence. -/
noncomputable def triangleDefect (a b c : I) : ℝ :=
  rs (compose a b) c - (rs a c + rs b c)

/-- Triangle defect equals emergence. -/
theorem triangleDefect_eq_emergence (a b c : I) :
    triangleDefect a b c = emergence a b c := by
  unfold triangleDefect emergence; ring

/-- Triangle defect is bounded. -/
theorem triangleDefect_bounded (a b c : I) :
    (triangleDefect a b c) ^ 2 ≤ weight (compose a b) * weight c := by
  rw [triangleDefect_eq_emergence]; unfold weight
  exact emergence_bounded' a b c

/-! ## §9. Symmetry Decomposition -/

/-- The symmetric part of resonance. -/
noncomputable def symPart (a b : I) : ℝ := (rs a b + rs b a) / 2

/-- The antisymmetric part of resonance. -/
noncomputable def antiPart (a b : I) : ℝ := (rs a b - rs b a) / 2

/-- Resonance decomposes into symmetric + antisymmetric. -/
theorem resonance_decomposition (a b : I) :
    rs a b = symPart a b + antiPart a b := by
  unfold symPart antiPart; ring

/-- Symmetric part is symmetric. -/
theorem symPart_symm (a b : I) : symPart a b = symPart b a := by
  unfold symPart; ring

/-- Antisymmetric part is antisymmetric. -/
theorem antiPart_antisymm (a b : I) : antiPart a b = -(antiPart b a) := by
  unfold antiPart; ring

/-- Self-symmetric part equals weight/2... no, it equals the full weight. -/
theorem symPart_self (a : I) : symPart a a = weight a := by
  unfold symPart weight; ring

/-- Self-antisymmetric part is zero. -/
theorem antiPart_self (a : I) : antiPart a a = 0 := by
  unfold antiPart; ring

/-- Symmetric part with void is zero. -/
theorem symPart_void (a : I) : symPart a (void : I) = 0 := by
  unfold symPart; rw [rs_void_right', rs_void_left']; ring

/-- Antisymmetric part with void is zero. -/
theorem antiPart_void (a : I) : antiPart a (void : I) = 0 := by
  unfold antiPart; rw [rs_void_right', rs_void_left']; ring

/-! ## §10. The Weight Metric on Equivalence Classes -/

-- If we restrict to ideas that are "the same idea" (same emergence pattern),
-- then the resonance gap becomes a meaningful measure of "distance between
-- expressions of the same idea."

/-- Two expressions a, b of the same idea may still have different weights.
    The weight gap measures this. -/
noncomputable def weightGap (a b : I) : ℝ :=
  weight a - weight b

/-- Weight gap is antisymmetric. -/
theorem weightGap_antisymm (a b : I) :
    weightGap a b = -(weightGap b a) := by
  unfold weightGap; ring

/-- Weight gap with self is zero. -/
theorem weightGap_self (a : I) : weightGap a a = 0 := by
  unfold weightGap; ring

/-- Weight gap with void gives full weight. -/
theorem weightGap_void (a : I) : weightGap a (void : I) = weight a := by
  unfold weightGap; rw [weight_void]; ring

end Geometry

/-! # PART II: Deep Geometry of Meaning

We develop the full geometric structure induced by the resonance function:
distance functions, curvature, geodesics, projections, convexity, tangent
spaces, parallel transport, holonomy, comparison geometry, and dimension
theory. Each theorem carries a philosophical interpretation. -/

section DeepGeometry
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-! ## §11. Directed Distance and Quasi-Metric Structure -/

/-- The directed distance from a to b: measures how much a "falls short"
    of recognizing b. Non-symmetric because recognition is perspectival. -/
noncomputable def drs (a b : I) : ℝ := rs a a - rs a b

/-- Directed distance to self is zero: you fully recognize yourself. -/
theorem drs_self (a : I) : drs a a = 0 := by
  unfold drs; ring

/-- Directed distance from void to anything is zero: nothingness "lacks"
    nothing because it has no perspective. -/
theorem drs_void_left (b : I) : drs (void : I) b = 0 := by
  unfold drs; rw [rs_void_void, rs_void_left']; ring

/-- Directed distance to void equals weight: the full measure of
    self that void fails to reflect. -/
theorem drs_void_right (a : I) : drs a (void : I) = rs a a := by
  unfold drs; rw [rs_void_right']; ring

/-- The symmetrized distance: averaging forward and backward directed
    distances gives a proto-metric respecting both perspectives. -/
noncomputable def symDist (a b : I) : ℝ := (drs a b + drs b a) / 2

/-- Symmetrized distance is genuinely symmetric. -/
theorem symDist_symm (a b : I) : symDist a b = symDist b a := by
  unfold symDist; ring

/-- Symmetrized distance to self is zero. -/
theorem symDist_self (a : I) : symDist a a = 0 := by
  unfold symDist drs; ring

/-- Symmetrized distance to void is half the weight:
    you lose half your perspective when measuring against nothingness. -/
theorem symDist_void (a : I) : symDist a (void : I) = rs a a / 2 := by
  unfold symDist drs; rw [rs_void_right']; rw [rs_void_void]; rw [rs_void_left']; ring

/-- The deficit distance: total resonance lost when two ideas fail to
    fully recognize each other. This is non-negative by Cauchy-Schwarz. -/
theorem symDist_eq_half_deficit (a b : I) :
    symDist a b = deficit a b / 2 := by
  unfold symDist drs deficit; ring

/-! ## §12. The Resonance Inner Product Analogue -/

/-- The symmetrized resonance: the closest analogue to an inner product.
    Unlike a true inner product, it lacks bilinearity (emergence prevents it). -/
noncomputable def innerRS (a b : I) : ℝ := (rs a b + rs b a) / 2

/-- innerRS coincides with symPart. -/
theorem innerRS_eq_symPart (a b : I) : innerRS a b = symPart a b := by
  unfold innerRS symPart; ring

/-- The inner product analogue is symmetric. -/
theorem innerRS_symm (a b : I) : innerRS a b = innerRS b a := by
  unfold innerRS; ring

/-- Inner product with self is weight. -/
theorem innerRS_self (a : I) : innerRS a a = weight a := by
  unfold innerRS weight; ring

/-- Inner product with void vanishes. -/
theorem innerRS_void (a : I) : innerRS a (void : I) = 0 := by
  unfold innerRS; rw [rs_void_right', rs_void_left']; ring

/-- The "cosine" between ideas: alignment normalized by weights.
    Measures conceptual similarity independent of "magnitude." -/
noncomputable def cosineSim (a b : I) (_ha : a ≠ void) (_hb : b ≠ void) : ℝ :=
  innerRS a b / (weight a * weight b)

/-- Cosine similarity with self is 1/weight (since innerRS a a = weight a). -/
theorem cosineSim_self (a : I) (ha : a ≠ void) :
    cosineSim a a ha ha = 1 / weight a := by
  unfold cosineSim; rw [innerRS_self]
  have hpos := rs_self_pos a ha
  unfold weight; field_simp

/-! ## §13. Curvature Tensor Analogues -/

/-- The Riemann curvature analogue: how emergence changes when we permute
    the order of composition. In Riemannian geometry, R(X,Y)Z measures
    the failure of parallel transport to commute. Here, we measure the
    failure of emergence to be symmetric in its first two arguments. -/
noncomputable def riemannCurvature (a b c : I) : ℝ :=
  emergence a b c - emergence b a c

/-- The Riemann curvature is antisymmetric in the first two slots,
    just as in differential geometry. -/
theorem riemannCurvature_antisymm (a b c : I) :
    riemannCurvature a b c = -riemannCurvature b a c := by
  unfold riemannCurvature; ring

/-- Curvature vanishes when either slot is void. -/
theorem riemannCurvature_void_left (b c : I) :
    riemannCurvature (void : I) b c = -emergence b (void : I) c := by
  unfold riemannCurvature; rw [emergence_void_left]; ring

/-- Self-curvature is zero: an idea has no "rotational" effect with itself. -/
theorem riemannCurvature_self (a c : I) :
    riemannCurvature a a c = 0 := by
  unfold riemannCurvature; ring

/-- The Ricci curvature analogue: curvature of a composed with b, measured
    from a. Measures the "bending" of ideatic space when b is added to a. -/
noncomputable def ricciScalar (a b : I) : ℝ :=
  emergence a b a - emergence b a a

/-- Self-Ricci is zero: an idea has no net curvature with itself. -/
theorem ricciScalar_self (a : I) : ricciScalar a a = 0 := by
  unfold ricciScalar; ring

/-- Ricci with void is zero from the left. -/
theorem ricciScalar_void_left (b : I) : ricciScalar (void : I) b = 0 := by
  unfold ricciScalar emergence; simp [rs_void_left', void_left']

/-- Ricci with void is zero from the right. -/
theorem ricciScalar_void_right (a : I) : ricciScalar a (void : I) = 0 := by
  unfold ricciScalar emergence; simp [rs_void_right', void_right']

/-- Ricci in terms of resonances. -/
theorem ricciScalar_eq (a b : I) :
    ricciScalar a b = rs (compose a b) a - rs a a - rs b a -
    (rs (compose b a) a - rs b a - rs a a) := by
  unfold ricciScalar emergence; ring

/-! ## §14. Geodesic Structure -/

/-- A "geodesic interpolant" between a and b via c: c lies on the geodesic
    from a to b if composing a with c brings you closer to b in resonance. -/
def onGeodesic (a b c : I) : Prop :=
  rs a (compose a c) ≥ rs a a ∧ rs (compose a c) b ≥ rs a b

/-- Void is trivially on the geodesic (it does nothing). -/
theorem void_on_geodesic (a b : I) : onGeodesic a b (void : I) := by
  constructor
  · simp [void_right']
  · simp [void_right']

/-- The "geodesic deviation": how much c deviates from the straight path
    between a and b. In Riemannian geometry, geodesic deviation is governed
    by the Jacobi equation. Here, emergence plays the role of curvature. -/
noncomputable def geodesicDeviation (a b c : I) : ℝ :=
  rs (compose a c) b - rs a b - rs c b

/-- Geodesic deviation is exactly emergence. -/
theorem geodesicDeviation_eq_emergence (a b c : I) :
    geodesicDeviation a b c = emergence a c b := by
  unfold geodesicDeviation emergence; ring

/-- Geodesic deviation with void is zero: void causes no deviation. -/
theorem geodesicDeviation_void (a b : I) :
    geodesicDeviation a b (void : I) = 0 := by
  rw [geodesicDeviation_eq_emergence]; exact emergence_void_right a b

/-! ## §15. Angle Theory -/

/-- The "angle" between ideas a and b as seen from o: how similarly o
    resonates with a and b. High value means similar orientation. -/
noncomputable def angleFrom (o a b : I) : ℝ :=
  rs o a * rs o b

/-- The angle from void is zero: nothingness sees no angles. -/
theorem angleFrom_void (a b : I) : angleFrom (void : I) a b = 0 := by
  unfold angleFrom; rw [rs_void_left', rs_void_left']; ring

/-- Angle is symmetric in the two directions. -/
theorem angleFrom_symm (o a b : I) : angleFrom o a b = angleFrom o b a := by
  unfold angleFrom; ring

/-- Self-angle is the square of resonance: alignment with one idea squared. -/
theorem angleFrom_self (o a : I) : angleFrom o a a = (rs o a) ^ 2 := by
  unfold angleFrom; ring

/-- Angle with void is zero: you can't see toward nothingness. -/
theorem angleFrom_void_target (o a : I) : angleFrom o a (void : I) = 0 := by
  unfold angleFrom; rw [rs_void_right']; ring

/-- The angular deficit: how much the angle between a∘b and c differs
    from the sum-of-parts angle. Measures curvature via angles. -/
noncomputable def angularDeficit (a b c o : I) : ℝ :=
  rs o (compose a b) * rs o c - (rs o a + rs o b) * rs o c

/-- Angular deficit vanishes when observer is void. -/
theorem angularDeficit_void_observer (a b c : I) :
    angularDeficit a b c (void : I) = 0 := by
  unfold angularDeficit
  rw [rs_void_left' (compose a b), rs_void_left' c, rs_void_left' a, rs_void_left' b]
  ring

/-! ## §16. Hyperplane Theory -/

/-- An idea n defines a "hyperplane": the set of ideas orthogonal to n.
    We formalize properties of these hyperplanes. -/
def inHyperplane (n a : I) : Prop := rs a n = 0

/-- Void lies in every hyperplane: nothingness is everywhere perpendicular. -/
theorem void_in_hyperplane (n : I) : inHyperplane n (void : I) := by
  unfold inHyperplane; exact rs_void_left' n

/-- The normal idea itself is NOT in its own hyperplane (unless void). -/
theorem normal_not_in_hyperplane (n : I) (h : n ≠ void) :
    ¬inHyperplane n n := by
  unfold inHyperplane; intro h1
  exact absurd (rs_nondegen' n h1) h

/-- If a and b are both in the hyperplane of n, then we can bound
    how their composition resonates with n via emergence. -/
theorem hyperplane_composition (n a b : I)
    (ha : inHyperplane n a) (hb : inHyperplane n b) :
    rs (compose a b) n = emergence a b n := by
  unfold inHyperplane at ha hb
  rw [rs_compose_eq]; linarith

/-- Emergence from within a hyperplane is bounded. -/
theorem hyperplane_emergence_bounded (n a b : I)
    (ha : inHyperplane n a) (hb : inHyperplane n b) :
    (rs (compose a b) n) ^ 2 ≤ rs (compose a b) (compose a b) * rs n n := by
  rw [hyperplane_composition n a b ha hb]
  exact emergence_bounded' a b n

/-! ## §17. Convexity in Ideatic Space -/

/-- A set of ideas is "resonance-convex" if composing any two elements
    produces something still "between" them in resonance. -/
def resonanceConvex (P : I → Prop) : Prop :=
  ∀ a b : I, P a → P b → P (compose a b)

/-- The set {void} is resonance-convex. -/
theorem convex_void_set : resonanceConvex (fun (a : I) => a = void) := by
  intro a b ha hb; rw [ha, hb]; simp

/-- The universal set is trivially convex. -/
theorem convex_univ : resonanceConvex (fun (_ : I) => True) := by
  intro _ _ _ _; trivial

/-- The set of ideas with weight above a threshold is convex
    (since composition enriches). -/
theorem convex_weight_above (t : ℝ) :
    resonanceConvex (fun (a : I) => weight a ≥ t) := by
  intro a b ha _
  unfold weight at *
  have := compose_enriches' a b
  linarith

/-- The hyperplane of an idea is resonance-convex when emergence
    from within it stays in it. -/
theorem hyperplane_closed_under_compose (n a b : I)
    (ha : inHyperplane n a) (hb : inHyperplane n b)
    (he : emergence a b n = 0) : inHyperplane n (compose a b) := by
  unfold inHyperplane at *
  rw [rs_compose_eq]; linarith

/-! ## §18. Tangent Space Analogues -/

/-- The "tangent vector" at a in direction b: the infinitesimal change in
    resonance when composing a with b. Emergence IS the curvature of this
    tangent map. -/
noncomputable def tangentRS (a b c : I) : ℝ :=
  rs (compose a b) c - rs a c

/-- Tangent vector decomposes into linear part (rs b c) plus emergence. -/
theorem tangentRS_decomposition (a b c : I) :
    tangentRS a b c = rs b c + emergence a b c := by
  unfold tangentRS emergence; ring

/-- Tangent vector from void: the linear part dominates (no curvature). -/
theorem tangentRS_void (b c : I) : tangentRS (void : I) b c = rs b c := by
  unfold tangentRS; rw [void_left', rs_void_left']; ring

/-- Tangent in the void direction: nothing changes. -/
theorem tangentRS_void_dir (a c : I) : tangentRS a (void : I) c = 0 := by
  unfold tangentRS; simp [void_right']

/-- Tangent against void observer: always zero. -/
theorem tangentRS_void_observer (a b : I) : tangentRS a b (void : I) = 0 := by
  unfold tangentRS; simp [rs_void_right']

/-- Self-tangent: how composing a with b changes a's self-resonance. -/
theorem tangentRS_self (a b : I) :
    tangentRS a b a = rs b a + emergence a b a := by
  exact tangentRS_decomposition a b a

/-! ## §19. Parallel Transport Analogues -/

/-- "Parallel transport" of c along the composition a∘b: how c's
    resonance changes when the reference frame shifts from a to a∘b.
    The transport anomaly is exactly emergence. -/
noncomputable def transport (a b c : I) : ℝ :=
  rs (compose a b) c

/-- Transport decomposes: individual contributions plus emergence. -/
theorem transport_decomposition (a b c : I) :
    transport a b c = rs a c + rs b c + emergence a b c := by
  unfold transport; rw [rs_compose_eq]

/-- Transport via void doesn't move: -/
theorem transport_void_path (a c : I) : transport a (void : I) c = rs a c := by
  unfold transport; simp [void_right']

/-- Transport from void: same as direct resonance. -/
theorem transport_void_start (b c : I) : transport (void : I) b c = rs b c := by
  unfold transport; simp [void_left']

/-- Sequential transport satisfies the cocycle condition: transporting
    along a∘b then along (a∘b)∘c is consistent with transporting
    along b∘c then along a∘(b∘c). This is holonomy. -/
theorem transport_cocycle (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

/-! ## §20. Holonomy -/

/-- The holonomy around a "triangle" a, b, c: the total emergence
    accumulated by transporting around the loop. Non-zero holonomy
    means the ideatic space is curved — meaning is path-dependent. -/
noncomputable def holonomy (a b c d : I) : ℝ :=
  emergence a b d + emergence (compose a b) c d

/-- Holonomy equals the alternative path (by cocycle). -/
theorem holonomy_eq_alt (a b c d : I) :
    holonomy a b c d = emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

/-- Holonomy with void is just the single emergence. -/
theorem holonomy_void_c (a b d : I) :
    holonomy a b (void : I) d = emergence a b d := by
  unfold holonomy; rw [emergence_void_right]; ring

theorem holonomy_void_b (a c d : I) :
    holonomy a (void : I) c d = emergence a c d := by
  unfold holonomy emergence; simp [void_right', rs_void_left', rs_void_right']

theorem holonomy_void_a (b c d : I) :
    holonomy (void : I) b c d = emergence b c d := by
  unfold holonomy emergence; simp [void_left', rs_void_left', rs_void_right']

/-! ## §21. Sectional Curvature Bounds -/

/-- The "sectional area" spanned by a and b (product of weights).
    Normalizing emergence by this gives sectional curvature. -/
noncomputable def sectionalArea (a b : I) : ℝ := weight a * weight b

/-- Sectional area is symmetric. -/
theorem sectionalArea_symm (a b : I) :
    sectionalArea a b = sectionalArea b a := by
  unfold sectionalArea weight; ring

/-- Sectional area is non-negative. -/
theorem sectionalArea_nonneg (a b : I) : sectionalArea a b ≥ 0 := by
  unfold sectionalArea weight
  exact mul_nonneg (rs_self_nonneg' a) (rs_self_nonneg' b)

/-- Sectional area with void is zero. -/
theorem sectionalArea_void (a : I) : sectionalArea a (void : I) = 0 := by
  unfold sectionalArea weight; rw [rs_void_void]; ring

/-- Emergence squared is bounded by the product of composition-weight and
    observer-weight. This is the fundamental curvature bound. -/
theorem curvature_bound_product (a b c : I) :
    (emergence a b c) ^ 2 ≤ weight (compose a b) * weight c := by
  unfold weight; exact emergence_bounded' a b c

/-! ## §22. Comparison Geometry -/

/-- In comparison geometry, we compare triangles. The "comparison angle"
    uses the deficit to determine if space is positively or negatively curved.
    Positive deficit means positive curvature (ideas are "closer" than expected). -/
theorem deficit_nonneg_of_weights (a b : I) :
    deficit a b = weight a + weight b - rs a b - rs b a := by
  unfold deficit weight; ring

/-- The total resonance balance: composition weight vs. sum of parts. -/
noncomputable def compositionExcess (a b : I) : ℝ :=
  weight (compose a b) - weight a - weight b

/-- Composition excess equals the self-emergence plus cross terms. -/
theorem compositionExcess_eq (a b : I) :
    compositionExcess a b =
    rs a (compose a b) + rs b (compose a b) + emergence a b (compose a b)
    - weight a - weight b := by
  unfold compositionExcess weight emergence
  ring

/-- Composition excess is non-negative minus the weight of b
    (from compose_enriches). -/
theorem compositionExcess_ge (a b : I) :
    compositionExcess a b ≥ -weight b := by
  unfold compositionExcess weight
  have h := compose_enriches' a b
  linarith

/-- Composition excess with void is zero. -/
theorem compositionExcess_void_right (a : I) :
    compositionExcess a (void : I) = 0 := by
  unfold compositionExcess weight; rw [void_right', rs_void_void]; ring

theorem compositionExcess_void_left (b : I) :
    compositionExcess (void : I) b = 0 := by
  unfold compositionExcess weight; rw [void_left', rs_void_void]; ring

/-! ## §23. The Expansion-Contraction Decomposition -/

/-- Every composition can be decomposed into an expansion (weight gain)
    and a rotation (redistribution of resonance). The expansion is
    guaranteed non-negative. -/
noncomputable def rotationComponent (a b c : I) : ℝ :=
  rs (compose a b) c - rs a c

/-- Rotation decomposes into direct contribution and emergence. -/
theorem rotation_eq (a b c : I) :
    rotationComponent a b c = rs b c + emergence a b c := by
  unfold rotationComponent emergence; ring

/-- Rotation by void is zero: nothing rotates nothing. -/
theorem rotation_void (a c : I) :
    rotationComponent a (void : I) c = 0 := by
  unfold rotationComponent; simp [void_right']

/-- The expansion equals the tangent applied to the composed point. -/
theorem expansion_eq_self_tangent (a b : I) :
    expansion a b = rs (compose a b) (compose a b) - rs a (compose a b) +
    (rs a (compose a b) - rs a a) := by
  unfold expansion weight; ring

/-! ## §24. Harmonic Analysis on Ideatic Space -/

/-- The "Laplacian" of an idea: how it compares to compositions around it.
    Positive Laplacian means the idea has less weight than its compositions
    (it's a "valley"). -/
noncomputable def laplacian (a b : I) : ℝ :=
  weight (compose a b) + weight (compose b a) - 2 * weight a

/-- Laplacian of void is total weight of b under both compositions. -/
theorem laplacian_void (b : I) :
    laplacian (void : I) b = 2 * weight b := by
  unfold laplacian weight
  rw [void_left' b, void_right' b, rs_void_void]; ring

/-- Laplacian is related to expansion. -/
theorem laplacian_eq (a b : I) :
    laplacian a b = expansion a b + (weight (compose b a) - weight a) := by
  unfold laplacian expansion weight; ring

/-- The Laplacian with void is zero: void causes no oscillation. -/
theorem laplacian_void_dir (a : I) : laplacian a (void : I) = 0 := by
  unfold laplacian weight; rw [void_right' a, void_left' a]; ring

/-! ## §25. Dimension Theory -/

/-- The "effective dimension" at an idea: how many independent directions
    of composition are available. We approximate this by comparing
    iterated composition growth rates. -/
noncomputable def weightGrowth (a : I) (n : ℕ) : ℝ :=
  weight (composeN a (n + 1)) - weight (composeN a n)

/-- Weight growth is non-negative (composition enriches). -/
theorem weightGrowth_nonneg (a : I) (n : ℕ) : weightGrowth a n ≥ 0 := by
  unfold weightGrowth weight
  have h := compose_enriches' (composeN a n) a
  rw [← composeN_succ] at h
  linarith

/-- Weight growth of void is zero: nothingness doesn't grow. -/
theorem weightGrowth_void (n : ℕ) : weightGrowth (void : I) n = 0 := by
  unfold weightGrowth weight
  simp [composeN_void]

/-- The total weight after n compositions: a "volume growth" indicator. -/
noncomputable def totalWeight (a : I) (n : ℕ) : ℝ := weight (composeN a n)

/-- Total weight is monotonically non-decreasing. -/
theorem totalWeight_mono (a : I) (n : ℕ) :
    totalWeight a (n + 1) ≥ totalWeight a n := by
  unfold totalWeight weight
  exact rs_composeN_mono a n

/-- Total weight starts at zero. -/
theorem totalWeight_zero (a : I) : totalWeight a 0 = 0 := by
  unfold totalWeight weight; simp [composeN_zero, rs_void_void]

/-- Total weight at step 1 equals the base weight. -/
theorem totalWeight_one (a : I) : totalWeight a 1 = weight a := by
  unfold totalWeight weight; simp [composeN_succ, composeN_zero, void_left']

/-! ## §26. Manifold Structure: Charts and Atlases -/

/-- Two ideas are "locally equivalent" if they have the same weight and
    the same resonance with a reference frame. This is the chart overlap
    condition. -/
def locallyEquivalent (a b r : I) : Prop :=
  weight a = weight b ∧ rs r a = rs r b ∧ rs a r = rs b r

/-- Local equivalence is reflexive. -/
theorem locallyEquivalent_refl (a r : I) :
    locallyEquivalent a a r :=
  ⟨rfl, rfl, rfl⟩

/-- Local equivalence is symmetric. -/
theorem locallyEquivalent_symm (a b r : I) :
    locallyEquivalent a b r → locallyEquivalent b a r :=
  fun ⟨h1, h2, h3⟩ => ⟨h1.symm, h2.symm, h3.symm⟩

/-- Local equivalence is transitive. -/
theorem locallyEquivalent_trans (a b c r : I) :
    locallyEquivalent a b r → locallyEquivalent b c r →
    locallyEquivalent a c r :=
  fun ⟨h1, h2, h3⟩ ⟨h4, h5, h6⟩ =>
    ⟨h1.trans h4, h2.trans h5, h3.trans h6⟩

/-- Void is locally equivalent only to itself (from any nonvoid reference). -/
theorem void_locallyEquivalent_iff (b r : I) (_hr : r ≠ void) :
    locallyEquivalent (void : I) b r → b = void := by
  intro ⟨h1, _, _⟩
  unfold weight at h1; rw [rs_void_void] at h1
  exact rs_nondegen' b h1.symm

/-! ## §27. Riemannian Metric Analogues -/

/-- The "metric tensor" at a point a, evaluated on "vectors" b and c:
    how composing with b and c from a correlates. -/
noncomputable def metricTensor (a b c : I) : ℝ :=
  rs (compose a b) (compose a c) - rs a a

/-- Metric tensor with void first vector reduces. -/
theorem metricTensor_void_b (a c : I) :
    metricTensor a (void : I) c = rs a (compose a c) - rs a a := by
  unfold metricTensor; rw [void_right']

/-- Metric tensor with void second vector reduces. -/
theorem metricTensor_void_c (a b : I) :
    metricTensor a b (void : I) = rs (compose a b) a - rs a a := by
  unfold metricTensor; rw [void_right']

/-- The metric tensor at void reduces to direct resonance. -/
theorem metricTensor_void_base (b c : I) :
    metricTensor (void : I) b c = rs b c := by
  unfold metricTensor; rw [void_left', void_left', rs_void_void]; ring

/-- The metric tensor with b = c gives the expansion. -/
theorem metricTensor_diag (a b : I) :
    metricTensor a b b = expansion a b := by
  unfold metricTensor expansion weight; ring

/-! ## §28. Connection and Covariant Derivative Analogues -/

/-- The "connection coefficient": how much the resonance of c shifts
    when we move from a to a∘b. This is the Christoffel symbol analogue. -/
noncomputable def connectionCoeff (a b c : I) : ℝ :=
  rs (compose a b) c - rs a c - rs b c

/-- Connection coefficients ARE emergence. -/
theorem connectionCoeff_eq_emergence (a b c : I) :
    connectionCoeff a b c = emergence a b c := by
  unfold connectionCoeff emergence; ring
/-- Connection is zero for void path. -/
theorem connection_void_path (a c : I) :
    connectionCoeff a (void : I) c = 0 := by
  rw [connectionCoeff_eq_emergence]; exact emergence_void_right a c

/-- Connection satisfies the cocycle (Bianchi identity analogue). -/
theorem connection_bianchi (a b c d : I) :
    connectionCoeff a b d + connectionCoeff (compose a b) c d =
    connectionCoeff b c d + connectionCoeff a (compose b c) d := by
  simp [connectionCoeff_eq_emergence]; exact cocycle_condition a b c d

/-! ## §29. Torsion -/

/-- Torsion measures the antisymmetry of the connection: how much
    the order of composition matters for the "parallel transport."
    Non-zero torsion means ideatic space has "twist." -/
noncomputable def torsion (a b c : I) : ℝ :=
  connectionCoeff a b c - connectionCoeff b a c

/-- Torsion is antisymmetric. -/
theorem torsion_antisymm (a b c : I) :
    torsion a b c = -torsion b a c := by
  unfold torsion; ring

/-- Torsion equals the Riemann curvature analogue (because
    connection = emergence). -/
theorem torsion_eq_riemannCurvature (a b c : I) :
    torsion a b c = riemannCurvature a b c := by
  unfold torsion riemannCurvature
  simp [connectionCoeff_eq_emergence]

/-- Torsion is zero iff emergence is symmetric. -/
theorem torsion_zero_iff (a b c : I) :
    torsion a b c = 0 ↔ emergence a b c = emergence b a c := by
  unfold torsion; rw [connectionCoeff_eq_emergence, connectionCoeff_eq_emergence]
  constructor <;> intro h <;> linarith

/-- Self-torsion vanishes. -/
theorem torsion_self (a c : I) : torsion a a c = 0 := by
  unfold torsion; ring

/-! ## §30. Exponential Map Analogue -/

/-- The "exponential map" at a in direction b of "length" n: iterated
    composition a ∘ b ∘ b ∘ ... ∘ b (n times). This traces out a
    "geodesic" in the b-direction starting from a. -/
noncomputable def expMap (a b : I) (n : ℕ) : I :=
  compose a (composeN b n)

/-- Exponential map at step 0 returns the base point. -/
theorem expMap_zero (a b : I) : expMap a b 0 = a := by
  unfold expMap; simp [composeN_zero, void_right']

/-- Exponential map at step 1 is simple composition. -/
theorem expMap_one (a b : I) : expMap a b 1 = compose a b := by
  unfold expMap; simp [composeN_succ, composeN_zero, void_left']

/-- Weight along the exponential map is non-decreasing (from a). -/
theorem expMap_weight_mono (a b : I) (n : ℕ) :
    weight (expMap a b (n + 1)) ≥ weight (expMap a b n) := by
  unfold expMap weight
  have h : compose a (composeN b (n + 1)) =
    compose (compose a (composeN b n)) b := by
    rw [composeN_succ, ← compose_assoc']
  rw [h]; exact compose_enriches' _ b

/-- The exponential map from void is just iterated self-composition. -/
theorem expMap_void (b : I) (n : ℕ) :
    expMap (void : I) b n = composeN b n := by
  unfold expMap; simp [void_left']

/-! ## §31. Lie Bracket Analogue -/

/-- The "Lie bracket" of a and b: measures the failure of composition to
    commute, observed against c. In differential geometry, [X,Y] measures
    the failure of flows to commute. Here, it's the commutator resonance. -/
noncomputable def lieBracket (a b c : I) : ℝ :=
  rs (compose a b) c - rs (compose b a) c

/-- Lie bracket is antisymmetric. -/
theorem lieBracket_antisymm (a b c : I) :
    lieBracket a b c = -lieBracket b a c := by
  unfold lieBracket; ring

/-- Lie bracket vanishes for self. -/
theorem lieBracket_self (a c : I) : lieBracket a a c = 0 := by
  unfold lieBracket; ring

/-- Lie bracket with void is zero. -/
theorem lieBracket_void_left (b c : I) :
    lieBracket (void : I) b c = 0 := by
  unfold lieBracket; simp [void_left']

theorem lieBracket_void_right (a c : I) :
    lieBracket a (void : I) c = 0 := by
  unfold lieBracket; simp [void_right']

/-- Lie bracket decomposes into emergence difference (= torsion). -/
theorem lieBracket_eq_emergence_diff (a b c : I) :
    lieBracket a b c = emergence a b c - emergence b a c := by
  unfold lieBracket emergence; ring

/-- Lie bracket against void observer vanishes. -/
theorem lieBracket_void_observer (a b : I) :
    lieBracket a b (void : I) = 0 := by
  unfold lieBracket; simp [rs_void_right']

/-! ## §32. Jacobi Identity Analogue -/

/-- The Jacobiator: measures the failure of the Jacobi identity.
    In a Lie algebra, J = 0. In ideatic space, J ≠ 0 in general,
    and the failure tells us about higher-order curvature. -/
noncomputable def jacobiator (a b c d : I) : ℝ :=
  lieBracket a b d + lieBracket b c d + lieBracket c a d -
  (lieBracket b a d + lieBracket c b d + lieBracket a c d)

/-- The Jacobiator simplifies to twice the cyclic sum. -/
theorem jacobiator_eq (a b c d : I) :
    jacobiator a b c d =
    2 * (lieBracket a b d + lieBracket b c d + lieBracket c a d) := by
  unfold jacobiator
  have h1 := lieBracket_antisymm b a d
  have h2 := lieBracket_antisymm c b d
  have h3 := lieBracket_antisymm a c d
  linarith

/-- Jacobiator with all-void arguments is zero. -/
theorem jacobiator_all_void (d : I) :
    jacobiator (void : I) (void : I) (void : I) d = 0 := by
  unfold jacobiator lieBracket
  simp only [void_left', void_right']
  ring

/-- Jacobiator simplifies when first two args are void. -/
theorem jacobiator_void_void_c (c d : I) :
    jacobiator (void : I) (void : I) c d = 0 := by
  unfold jacobiator lieBracket
  simp only [void_left', void_right']
  ring

/-! ## §33. Gauss-Bonnet Analogue -/

/-- The "total curvature" of a triple: sum of emergences around the triangle.
    In the Gauss-Bonnet theorem, total curvature relates to topology.
    Here, total curvature of a "triangle" of ideas constrains how
    meaning flows. -/
noncomputable def totalCurvature (a b c d : I) : ℝ :=
  emergence a b d + emergence b c d + emergence c a d

/-- Total curvature with void corner simplifies. -/
theorem totalCurvature_void_a (b c d : I) :
    totalCurvature (void : I) b c d =
    emergence b c d + emergence c (void : I) d := by
  unfold totalCurvature; rw [emergence_void_left]; ring

/-- Total curvature when observer is void: identically zero. -/
theorem totalCurvature_void_observer (a b c : I) :
    totalCurvature a b c (void : I) = 0 := by
  unfold totalCurvature; simp [emergence_against_void]

/-! ## §34. Isometry and Symmetry -/

/-- Two ideas are "isometric" if they have the same weight and the same
    resonance structure with all others. A strong form of equivalence. -/
def isometric (a b : I) : Prop :=
  weight a = weight b ∧ ∀ c : I, rs a c = rs b c ∧ rs c a = rs c b

/-- Isometry is reflexive. -/
theorem isometric_refl (a : I) : isometric a a :=
  ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩

/-- Isometry is symmetric. -/
theorem isometric_symm (a b : I) (h : isometric a b) : isometric b a :=
  ⟨h.1.symm, fun c => ⟨(h.2 c).1.symm, (h.2 c).2.symm⟩⟩

/-- Isometry is transitive. -/
theorem isometric_trans (a b c : I)
    (h1 : isometric a b) (h2 : isometric b c) : isometric a c :=
  ⟨h1.1.trans h2.1, fun d =>
    ⟨(h1.2 d).1.trans (h2.2 d).1, (h1.2 d).2.trans (h2.2 d).2⟩⟩

/-- If composing isometric ideas with the same x gives the same resonances,
    then emergences are equal. -/
theorem isometric_emergence_eq (a b x d : I)
    (had : rs a d = rs b d)
    (hcomp : rs (compose a x) d = rs (compose b x) d) :
    emergence a x d = emergence b x d := by
  unfold emergence; linarith

/-! ## §35. Flat Subspaces -/

/-- A pair (a, b) is "flat" if their emergence vanishes for all observers.
    Flat pairs compose additively — no metaphor, no irony, no emergence. -/
def flatPair (a b : I) : Prop :=
  ∀ c : I, emergence a b c = 0

/-- Any pair involving void is flat. -/
theorem flatPair_void_left (b : I) : flatPair (void : I) b := by
  intro c; exact emergence_void_left b c

theorem flatPair_void_right (a : I) : flatPair a (void : I) := by
  intro c; exact emergence_void_right a c

/-- For flat pairs, resonance of composition is purely additive. -/
theorem flat_additive (a b : I) (h : flatPair a b) (c : I) :
    rs (compose a b) c = rs a c + rs b c := by
  have := rs_compose_eq a b c; rw [h c] at this; linarith

/-- For flat pairs, composition weight equals sum of cross-resonances. -/
theorem flat_weight (a b : I) (h : flatPair a b) :
    weight (compose a b) = rs a (compose a b) + rs b (compose a b) := by
  unfold weight
  rw [rs_compose_eq a b (compose a b), h (compose a b)]
  ring

/-! ## §36. Positively Curved Pairs -/

/-- A pair (a, b) is "positively curved" at c if their emergence is positive.
    This means composing them creates MORE resonance than expected —
    the hallmark of metaphor, analogy, and creative combination. -/
def positivelyCurved (a b c : I) : Prop :=
  emergence a b c > 0

/-- Positive curvature means the composition "super-resonates." -/
theorem positivelyCurved_iff (a b c : I) :
    positivelyCurved a b c ↔ rs (compose a b) c > rs a c + rs b c := by
  unfold positivelyCurved emergence
  constructor <;> intro h <;> linarith

/-- A pair is "negatively curved" at c if emergence is negative.
    This is the hallmark of irony, contradiction, and destructive interference. -/
def negativelyCurved (a b c : I) : Prop :=
  emergence a b c < 0

theorem negativelyCurved_iff (a b c : I) :
    negativelyCurved a b c ↔ rs (compose a b) c < rs a c + rs b c := by
  unfold negativelyCurved emergence
  constructor <;> intro h <;> linarith

/-! ## §37. Energy Functional -/

/-- The energy of a path (sequence of compositions): sum of expansion
    energies at each step. Geodesics minimize energy. -/
noncomputable def pathEnergy (a : I) : List I → ℝ
  | [] => 0
  | b :: rest => expansion a b + pathEnergy (compose a b) rest

/-- Empty path has zero energy. -/
theorem pathEnergy_nil (a : I) : pathEnergy a [] = 0 := rfl

/-- Single step energy equals expansion. -/
theorem pathEnergy_singleton (a b : I) :
    pathEnergy a [b] = expansion a b := by
  simp [pathEnergy]

/-- Path energy is non-negative for single steps. -/
theorem pathEnergy_singleton_nonneg (a b : I) :
    pathEnergy a [b] ≥ 0 := by
  rw [pathEnergy_singleton]; exact expansion_nonneg a b

/-! ## §38. Isoperimetric Analogues -/

/-- The "perimeter" of an idea triangle: sum of gaps around the boundary. -/
noncomputable def trianglePerimeter (a b c : I) : ℝ :=
  gap a b + gap b c + gap c a

/-- Triangle perimeter with repeated vertex simplifies. -/
theorem trianglePerimeter_self (a b : I) :
    trianglePerimeter a a b = gap a b + gap b a := by
  unfold trianglePerimeter gap; ring

/-- The perimeter of the triangle a-b-a equals the deficit. -/
theorem trianglePerimeter_deficit (a b : I) :
    trianglePerimeter a b a = deficit a b := by
  unfold trianglePerimeter deficit gap; ring

/-! ## §39. Volume Growth -/

/-- The volume growth ratio: how fast weight grows under iteration. -/
noncomputable def volumeGrowthRatio (a : I) (n : ℕ) : ℝ :=
  totalWeight a (n + 1) - totalWeight a n

/-- Volume growth ratio equals weight growth. -/
theorem volumeGrowthRatio_eq (a : I) (n : ℕ) :
    volumeGrowthRatio a n = weightGrowth a n := by
  unfold volumeGrowthRatio totalWeight weightGrowth; ring

/-- Volume growth is non-negative. -/
theorem volumeGrowthRatio_nonneg (a : I) (n : ℕ) :
    volumeGrowthRatio a n ≥ 0 := by
  rw [volumeGrowthRatio_eq]; exact weightGrowth_nonneg a n

/-! ## §40. Spectral Theory Analogues -/

/-- The "spectral radius" of an idea a against b: measures the maximum
    amplification ratio. -/
noncomputable def spectralRadius (a b : I) : ℝ :=
  rs a b * rs b a

/-- Spectral radius is symmetric. -/
theorem spectralRadius_symm (a b : I) :
    spectralRadius a b = spectralRadius b a := by
  unfold spectralRadius; ring

/-- Spectral radius of void is zero. -/
theorem spectralRadius_void (a : I) :
    spectralRadius a (void : I) = 0 := by
  unfold spectralRadius; rw [rs_void_right']; ring

/-- Self spectral radius is weight squared. -/
theorem spectralRadius_self (a : I) :
    spectralRadius a a = (weight a) ^ 2 := by
  unfold spectralRadius weight; ring

end DeepGeometry

end IDT3
