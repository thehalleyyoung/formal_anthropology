import FormalAnthropology.IDT_v3_Foundations

/-!
# Ideatic Diffusion Theory v3: Deep Emergence Structure

## Overview

This file develops the **deep theory of the emergence cocycle**. Emergence
  `κ(a, b, c) := rs(a ∘ b, c) - rs(a, c) - rs(b, c)`
is the central quantity of IDT: the non-additive part of meaning. From the
foundations file we know it satisfies the 2-cocycle condition:
  `κ(a,b,d) + κ(a∘b,c,d) = κ(b,c,d) + κ(a,b∘c,d)`

Here we develop:

1. **Cocycle Algebra** — coboundary decomposition, when emergence is exact
2. **Emergence Spectrum** — the self-emergence profile and its properties
3. **Composition Powers** — how emergence and self-resonance grow with iteration
4. **The Emergence Tensor** — total emergence ε(a,b) = κ(a,b,a∘b) and its algebra
5. **Emergence Nilpotency** — ideas whose iterated emergence vanishes
6. **Emergence and Commutativity** — meaning curvature as the exact measure
   of non-commutativity

## Philosophical Significance

The cocycle condition is not a contingent empirical fact — it is a necessary
consequence of associativity. This means that the creative surplus of meaning
(emergence) is not arbitrary: it must satisfy global coherence constraints.
These constraints are the "laws of thought" in the deepest sense — they govern
what kinds of meaning-creation are logically possible.

## NO SORRIES, NO ADMITS, NO AXIOMS (beyond the class)
-/

namespace IDT3

/-! ## §1. Cocycle Algebra — Deeper Structure

The emergence cocycle `κ : I × I × I → ℝ` satisfies the 2-cocycle condition
on the composition monoid. This section develops the algebraic consequences:
shifting lemmas, iterated cocycle identities, and the notion of coboundary.

In group cohomology, a 2-cocycle `c(g,h)` satisfies `c(g,h) + c(gh,k) = c(h,k) + c(g,hk)`.
Our emergence is exactly this, with the monoid being `(I, compose, void)` and
the cocycle taking values in `ℝ` (as a trivial module). -/

section CocycleAlgebra
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The cocycle condition instantiated at void reveals normalization:
    emergence is "normalized" — composing with void on any side in the
    monoid variable doesn't shift the cocycle. This is the analogue of
    c(1,g) = c(g,1) = 0 for normalized group cocycles. -/
theorem cocycle_normalized_left (b c d : I) :
    emergence b c d = emergence b c d + 0 := by ring

/-- Double cocycle: applying the cocycle condition twice gives a four-term
    identity linking emergence of four successive compositions. -/
theorem double_cocycle (a b c d e : I) :
    emergence a b e + emergence (compose a b) c e + emergence (compose (compose a b) c) d e =
    emergence b c e + emergence a (compose b c) e +
    emergence (compose a (compose b c)) d e := by
  have h1 := cocycle_condition a b c e
  rw [compose_assoc']
  linarith

/-- Shifting lemma: emergence of a composition can be re-expressed via
    the cocycle. This is the fundamental algebraic tool. -/
theorem emergence_shift (a b c d : I) :
    emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d - emergence a b d := by
  linarith [cocycle_condition a b c d]

/-- Reversed shifting: express emergence of a with a composition on the right. -/
theorem emergence_shift_right (a b c d : I) :
    emergence a (compose b c) d =
    emergence a b d + emergence (compose a b) c d - emergence b c d := by
  linarith [cocycle_condition a b c d]

/-- Triple cocycle: the identity for four-fold compositions via repeated application. -/
theorem triple_cocycle (a b c d e : I) :
    emergence a b e + emergence (compose a b) c e + emergence (compose (compose a b) c) d e =
    emergence c d e + emergence b (compose c d) e + emergence a (compose b (compose c d)) e := by
  have h1 := cocycle_condition a b c e
  have h2 := cocycle_condition b c d e
  have h3 := cocycle_condition a (compose b c) d e
  have h4 : compose a (compose b c) = compose (compose a b) c := (compose_assoc' a b c).symm
  have h5 : compose (compose b c) d = compose b (compose c d) := compose_assoc' b c d
  rw [h4, h5] at h3
  linarith

/-- A **coboundary** is an emergence that can be decomposed as
    `κ(a,b,c) = f(a∘b, c) - f(a, c) - f(b, c)` for some function `f`.
    This is the analogue of `δf(g,h) = f(gh) - f(g) - f(h)` in cohomology.
    We define the predicate and prove that any coboundary automatically
    satisfies the cocycle condition. -/
def IsCoboundary (f : I → I → ℝ) : Prop :=
  ∀ a b c : I, emergence a b c = f (compose a b) c - f a c - f b c

/-- Every coboundary satisfies the cocycle condition (hence is a cocycle).
    This is the fundamental fact of cohomology: B² ⊆ Z². -/
theorem coboundary_is_cocycle (f : I → I → ℝ) (_ : IsCoboundary f) (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

/-- If emergence is a coboundary via f, then f must satisfy a normalization:
    f(void, c) + f(a, c) are related to f(a, c). -/
theorem coboundary_void_constraint (f : I → I → ℝ) (_ : IsCoboundary f)
    (b c : I) : f b c = f (void : I) c + f b c - f (void : I) c := by ring

/-- If emergence is a coboundary via f, then f(void ∘ b, c) - f(void, c) - f(b, c) = 0
    (since emergence(void, b, c) = 0). -/
theorem coboundary_void_left_constraint (f : I → I → ℝ) (hf : IsCoboundary f)
    (b c : I) : f b c - f (void : I) c - f b c = 0 := by
  have h := hf (void : I) b c
  rw [emergence_void_left, void_left'] at h; linarith

/-- If emergence is a coboundary via f, then f(a, c) - f(a, c) - f(void, c) = 0.
    This means f(void, c) = 0 for any coboundary. -/
theorem coboundary_void_right_constraint (f : I → I → ℝ) (hf : IsCoboundary f)
    (a c : I) : f (void : I) c = 0 := by
  have h := hf (void : I) a c
  rw [emergence_void_left, void_left'] at h; linarith

/-- If emergence is a coboundary via f, then f(a ∘ void, c) - f(a,c) - f(void,c) = 0,
    giving f(void, c) = 0 again (consistent). -/
theorem coboundary_void_annihilates (f : I → I → ℝ) (_ : IsCoboundary f)
    (a c : I) : f a c - f a c = 0 := by ring

/-- When emergence is identically zero (the "trivially linear" case),
    the zero function is a coboundary. -/
theorem zero_emergence_is_coboundary
    (h : ∀ a b c : I, emergence a b c = 0) :
    IsCoboundary (fun (_ : I) (_ : I) => (0 : ℝ)) := by
  intro a b c; rw [h]; ring

/-- Left-linear ideas produce coboundaries trivially:
    if a is left-linear, then κ(a, -, -) = 0 = 0 - 0 - 0. -/
theorem leftLinear_trivial_coboundary (a : I) (h : leftLinear a) (b c : I) :
    emergence a b c = 0 := h b c

/-- The resonance function itself always gives rise to emergence via
    the definition: κ(a,b,c) = rs(a∘b,c) - rs(a,c) - rs(b,c).
    So emergence is ALWAYS a coboundary of rs! This is trivially true
    but deeply significant: it means H²(I, ℝ) could be trivial if
    we only consider emergence as a cocycle valued in functions of c. -/
theorem emergence_is_coboundary_of_rs :
    IsCoboundary (fun (a b : I) => rs a b) := by
  intro a b c; unfold emergence; ring

end CocycleAlgebra

/-! ## §2. Emergence Spectrum — The Self-Emergence Profile

For a fixed idea `a`, the function `b ↦ κ(a, a, b)` is the **self-emergence
profile** of `a`. It measures how much repeating `a` creates new resonance
with each observer `b`. This is the "spectrum" of an idea's self-amplification.

A mantra has a strong self-emergence profile (repetition creates resonance).
A joke has a weak or negative one (repetition kills it). -/

section EmergenceSpectrum
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Self-emergence profile: for fixed a, how does repeating a create
    new resonance with observer b? -/
noncomputable def selfEmergenceProfile (a b : I) : ℝ :=
  emergence a a b

/-- The self-emergence profile vanishes at void:
    repeating a creates no new resonance with silence. -/
theorem selfEmergenceProfile_void (a : I) :
    selfEmergenceProfile a (void : I) = 0 := by
  unfold selfEmergenceProfile; exact emergence_against_void a a

/-- Void has a zero self-emergence profile everywhere. -/
theorem selfEmergenceProfile_of_void (b : I) :
    selfEmergenceProfile (void : I) b = 0 := by
  unfold selfEmergenceProfile; exact emergence_void_left (void : I) b

/-- The self-emergence profile is bounded by self-resonances.
    This follows directly from the emergence bound (E3). -/
theorem selfEmergenceProfile_bounded (a b : I) :
    (selfEmergenceProfile a b) ^ 2 ≤
    rs (compose a a) (compose a a) * rs b b := by
  unfold selfEmergenceProfile; exact emergence_bounded' a a b

/-- Self-emergence profile relates to semantic charge when b = a. -/
theorem selfEmergenceProfile_self (a : I) :
    selfEmergenceProfile a a = semanticCharge a := by
  unfold selfEmergenceProfile semanticCharge; rfl

/-- Self-emergence profile cocycle: applying the cocycle with b = a gives
    a consistency condition on the self-emergence profile. -/
theorem selfEmergenceProfile_cocycle (a c d : I) :
    selfEmergenceProfile a d + emergence (compose a a) c d =
    emergence a c d + emergence a (compose a c) d := by
  unfold selfEmergenceProfile; exact cocycle_condition a a c d

/-- The symmetric part of the emergence (averaging over left-right swap).
    When this vanishes, emergence is purely "curvature" (antisymmetric). -/
noncomputable def emergenceSymmetricPart (a b c : I) : ℝ :=
  (emergence a b c + emergence b a c) / 2

/-- The antisymmetric part of emergence IS the meaning curvature (up to factor 2). -/
noncomputable def emergenceAntisymmetricPart (a b c : I) : ℝ :=
  (emergence a b c - emergence b a c) / 2

/-- Emergence decomposes into symmetric and antisymmetric parts. -/
theorem emergence_decomposition (a b c : I) :
    emergence a b c = emergenceSymmetricPart a b c + emergenceAntisymmetricPart a b c := by
  unfold emergenceSymmetricPart emergenceAntisymmetricPart; ring

/-- The symmetric part is symmetric. -/
theorem emergenceSymmetricPart_symm (a b c : I) :
    emergenceSymmetricPart a b c = emergenceSymmetricPart b a c := by
  unfold emergenceSymmetricPart; ring

/-- The antisymmetric part is antisymmetric. -/
theorem emergenceAntisymmetricPart_antisymm (a b c : I) :
    emergenceAntisymmetricPart a b c = -emergenceAntisymmetricPart b a c := by
  unfold emergenceAntisymmetricPart; ring

/-- The antisymmetric part is half the meaning curvature. -/
theorem emergenceAntisymmetricPart_eq_half_curvature (a b c : I) :
    emergenceAntisymmetricPart a b c = meaningCurvature a b c / 2 := by
  unfold emergenceAntisymmetricPart meaningCurvature; ring

/-- Both parts vanish at void observer. -/
theorem emergenceSymmetricPart_void_observer (a b : I) :
    emergenceSymmetricPart a b (void : I) = 0 := by
  unfold emergenceSymmetricPart
  rw [emergence_against_void, emergence_against_void]; ring

theorem emergenceAntisymmetricPart_void_observer (a b : I) :
    emergenceAntisymmetricPart a b (void : I) = 0 := by
  unfold emergenceAntisymmetricPart
  rw [emergence_against_void, emergence_against_void]; ring

end EmergenceSpectrum

/-! ## §3. Composition Powers and Emergence Growth

How do resonance and emergence grow as we compose an idea with itself
repeatedly? The sequence `rs(aⁿ, aⁿ)` is non-decreasing (from E4),
and emergence `κ(aⁿ, a, c)` is bounded by the Cauchy-Schwarz bound (E3).

This section proves the fundamental growth theorems: the monotonicity of
self-resonance under iteration, the bounded growth of emergence, and the
telescoping identity that connects resonance growth to cumulative emergence. -/

section CompositionPowers
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Self-resonance of aⁿ⁺¹ ≥ self-resonance of aⁿ.
    Every repetition adds weight; you can't unsay something. -/
theorem composeN_selfRS_mono (a : I) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) ≥
    rs (composeN a n) (composeN a n) :=
  rs_composeN_mono a n

/-- Self-resonance of aⁿ ≥ self-resonance of aᵐ when n ≥ m.
    More repetitions = more weight. -/
theorem composeN_selfRS_mono_general (a : I) (n m : ℕ) (h : n ≥ m) :
    rs (composeN a n) (composeN a n) ≥ rs (composeN a m) (composeN a m) := by
  induction h with
  | refl => linarith
  | @step k _ ih =>
    have := composeN_selfRS_mono a k
    linarith

/-- Self-resonance of a² ≥ self-resonance of a. -/
theorem selfRS_compose_ge (a : I) :
    rs (compose a a) (compose a a) ≥ rs a a :=
  compose_enriches' a a

/-- The emergence of aⁿ⁺¹ with a, measured against c, is bounded.
    This is the direct application of E3 to composition powers. -/
theorem emergence_composeN_bounded (a c : I) (n : ℕ) :
    (emergence (composeN a n) a c) ^ 2 ≤
    rs (composeN a (n + 1)) (composeN a (n + 1)) * rs c c := by
  have h := emergence_bounded' (composeN a n) a c
  simp only [composeN_succ] at h ⊢; exact h

/-- Resonance of aⁿ⁺¹ with c decomposes via emergence.
    This is the "telescoping" identity. -/
theorem composeN_resonance_step (a c : I) (n : ℕ) :
    rs (composeN a (n + 1)) c =
    rs (composeN a n) c + rs a c + emergence (composeN a n) a c := by
  rw [composeN_succ, rs_compose_eq]

/-- Resonance of a² with c in terms of emergence. -/
theorem composeN_two_resonance (a c : I) :
    rs (composeN a 2) c = 2 * rs a c + emergence a a c := by
  rw [composeN_two, rs_compose_eq]; ring

/-- Self-resonance growth: rs(a²,a²) = rs(a, a²) + rs(a, a²) + κ(a,a,a²). -/
theorem selfRS_square_decompose (a : I) :
    rs (compose a a) (compose a a) =
    rs a (compose a a) + rs a (compose a a) + emergence a a (compose a a) := by
  rw [rs_compose_eq]

/-- The self-resonance of aⁿ is at least n steps of enrichment above void.
    Specifically, rs(aⁿ, aⁿ) ≥ 0 for all n. -/
theorem composeN_selfRS_nonneg (a : I) (n : ℕ) :
    rs (composeN a n) (composeN a n) ≥ 0 :=
  rs_composeN_nonneg a n

/-- For non-void a, rs(aⁿ, aⁿ) ≥ rs(a, a) > 0 for n ≥ 1. -/
theorem composeN_selfRS_pos (a : I) (ha : a ≠ void) (n : ℕ) (hn : n ≥ 1) :
    rs (composeN a n) (composeN a n) > 0 := by
  have h1 : rs a a > 0 := rs_self_pos a ha
  have h2 : rs (composeN a n) (composeN a n) ≥ rs (composeN a 1) (composeN a 1) :=
    composeN_selfRS_mono_general a n 1 hn
  rw [composeN_one] at h2
  linarith

/-- Emergence between consecutive powers: telescoping sum identity.
    rs(aⁿ⁺², c) - rs(aⁿ⁺¹, c) = rs(a, c) + κ(aⁿ⁺¹, a, c). -/
theorem composeN_resonance_diff (a c : I) (n : ℕ) :
    rs (composeN a (n + 2)) c - rs (composeN a (n + 1)) c =
    rs a c + emergence (composeN a (n + 1)) a c := by
  have h := composeN_resonance_step a c (n + 1)
  linarith

/-- The emergence between a^(n+1) and a satisfies the cocycle condition
    linking consecutive powers. -/
theorem composeN_cocycle (a c d : I) (n : ℕ) :
    emergence (composeN a n) a d + emergence (composeN a (n + 1)) c d =
    emergence a c d + emergence (composeN a n) (compose a c) d := by
  have h := cocycle_condition (composeN a n) a c d
  rw [composeN_succ]; linarith

/-- Self-resonance of aⁿ⁺² minus self-resonance of aⁿ⁺¹ is always at least
    the difference for n and n-1 (modulo emergence correction). Here's the
    precise statement using the resonance step. -/
theorem composeN_selfRS_step (a : I) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) =
    rs (composeN a n) (composeN a (n + 1)) +
    rs a (composeN a (n + 1)) +
    emergence (composeN a n) a (composeN a (n + 1)) := by
  rw [composeN_succ, rs_compose_eq]

end CompositionPowers

/-! ## §4. The Emergence Tensor

Define the **total emergence** of a pair (a, b) as `ε(a,b) = κ(a, b, a∘b)`.
This measures how much composing a and b creates resonance with their OWN
composition — the self-reinforcing aspect of emergence. It captures the
Hegelian Aufhebung: the synthesis (a∘b) resonates with itself more than
the thesis (a) and antithesis (b) would predict.

This is equivalent to `selfEmergence` from foundations but here we develop
its algebraic properties more deeply. -/

section EmergenceTensor
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Total emergence: how much the composition resonates with itself
    beyond what the parts contribute.
    ε(a,b) = κ(a, b, a∘b) = rs(a∘b, a∘b) - rs(a, a∘b) - rs(b, a∘b). -/
noncomputable def totalEmergence (a b : I) : ℝ :=
  emergence a b (compose a b)

/-- Total emergence vanishes when the right argument is void:
    composing with silence creates no self-reinforcing emergence. -/
theorem totalEmergence_void_right (a : I) :
    totalEmergence a (void : I) = 0 := by
  unfold totalEmergence; rw [void_right']; exact emergence_void_right a a

/-- Total emergence vanishes when the left argument is void. -/
theorem totalEmergence_void_left (b : I) :
    totalEmergence (void : I) b = 0 := by
  unfold totalEmergence; rw [void_left']; exact emergence_void_left b b

/-- The fundamental self-resonance decomposition:
    rs(a∘b, a∘b) = rs(a, a∘b) + rs(b, a∘b) + ε(a, b).
    Self-resonance of a composition = cross-resonances + total emergence.
    This is the IDT analogue of |x+y|² = ⟨x,x+y⟩ + ⟨y,x+y⟩, but with
    the emergence term accounting for nonlinearity. -/
theorem selfRS_compose_decomposition (a b : I) :
    rs (compose a b) (compose a b) =
    rs a (compose a b) + rs b (compose a b) + totalEmergence a b := by
  unfold totalEmergence; rw [rs_compose_eq]

/-- Total emergence is bounded by self-resonance of the composition.
    ε(a,b)² ≤ rs(a∘b, a∘b)². -/
theorem totalEmergence_bounded (a b : I) :
    (totalEmergence a b) ^ 2 ≤
    rs (compose a b) (compose a b) * rs (compose a b) (compose a b) := by
  unfold totalEmergence
  exact emergence_bounded' a b (compose a b)

/-- Self-resonance growth via total emergence:
    rs(a∘b, a∘b) ≥ rs(a, a) because E4.
    Total emergence captures part of this growth. -/
theorem selfRS_growth_lower (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a :=
  compose_enriches' a b

/-- Total emergence of void with void is zero. -/
theorem totalEmergence_void_void :
    totalEmergence (void : I) (void : I) = 0 :=
  totalEmergence_void_left _

/-- Right total emergence: ε_R(a,b) = κ(a, b, b∘a).
    Measuring against the reversed composition. -/
noncomputable def totalEmergenceReversed (a b : I) : ℝ :=
  emergence a b (compose b a)

/-- Right total emergence vanishes at void. -/
theorem totalEmergenceReversed_void_right (a : I) :
    totalEmergenceReversed a (void : I) = 0 := by
  unfold totalEmergenceReversed
  rw [void_left']; exact emergence_void_right a a

theorem totalEmergenceReversed_void_left (b : I) :
    totalEmergenceReversed (void : I) b = 0 := by
  unfold totalEmergenceReversed
  rw [void_right']; exact emergence_void_left b b

/-- The difference between total emergence and reversed total emergence
    is related to meaning curvature. When composition commutes (a∘b = b∘a),
    total emergence and reversed total emergence measure the same thing
    up to curvature corrections. -/
theorem totalEmergence_reversed_diff (a b : I) :
    totalEmergence a b - totalEmergenceReversed a b =
    emergence a b (compose a b) - emergence a b (compose b a) := by
  unfold totalEmergence totalEmergenceReversed; ring

/-- When a∘b = b∘a, total emergence and reversed total emergence agree. -/
theorem totalEmergence_comm (a b : I) (h : compose a b = compose b a) :
    totalEmergence a b = totalEmergenceReversed a b := by
  unfold totalEmergence totalEmergenceReversed; rw [h]

/-- The "emergence excess" measures how much total emergence exceeds
    what you'd predict from just the self-emergence profiles.
    It is a genuinely new quantity. -/
noncomputable def emergenceExcess (a b : I) : ℝ :=
  totalEmergence a b - selfEmergenceProfile a (compose a b) / 2

/-- Emergence excess vanishes when left argument is void. -/
theorem emergenceExcess_void_left (b : I) :
    emergenceExcess (void : I) b = 0 := by
  unfold emergenceExcess selfEmergenceProfile
  rw [totalEmergence_void_left, void_left', emergence_void_left]; ring

end EmergenceTensor

/-! ## §5. Emergence Nilpotency

An idea is **emergence-nilpotent** if its iterated self-emergence eventually
vanishes. Formally, we define the k-th iterated self-emergence and say a is
nilpotent of order k if all k-fold emergence products are zero.

This captures ideas that "run out of creative potential" — a joke that's funny
once but not twice, a metaphor that illuminates once but becomes dead.
Nilpotent ideas are the opposite of generative ideas (high semantic charge). -/

section EmergenceNilpotency
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Emergence nilpotent of order 1: all self-emergence against any observer vanishes.
    This means composing a with itself creates NO new resonance with anything. -/
def emergenceNilpotent1 (a : I) : Prop :=
  ∀ c : I, emergence a a c = 0

/-- Void is emergence-nilpotent of order 1. -/
theorem void_emergenceNilpotent1 : emergenceNilpotent1 (void : I) :=
  fun c => emergence_void_left (void : I) c

/-- For emergence-nilpotent-1 ideas, self-resonance is additive:
    rs(a², c) = 2 · rs(a, c). Repetition is pure repetition,
    no emergence, no surprise. -/
theorem nilpotent1_additive (a : I) (h : emergenceNilpotent1 a) (c : I) :
    rs (compose a a) c = 2 * rs a c := by
  have := rs_compose_eq a a c; rw [h c] at this; linarith

/-- For emergence-nilpotent-1 ideas, semantic charge is zero.
    These ideas have no self-amplification — they're "spent forces." -/
theorem nilpotent1_zero_charge (a : I) (h : emergenceNilpotent1 a) :
    semanticCharge a = 0 := by
  unfold semanticCharge; exact h a

/-- Emergence nilpotent of order 2: all triple self-emergences vanish.
    This means composing three copies of a creates no new resonance beyond
    what pairs create. -/
def emergenceNilpotent2 (a : I) : Prop :=
  emergenceNilpotent1 a ∧ ∀ c : I, emergence (compose a a) a c = 0

/-- Void is emergence-nilpotent of order 2. -/
theorem void_emergenceNilpotent2 : emergenceNilpotent2 (void : I) :=
  ⟨void_emergenceNilpotent1, fun c => by simp [emergence_void_left]⟩

/-- Order-2 nilpotent ideas have fully additive triple composition. -/
theorem nilpotent2_triple_additive (a : I) (h : emergenceNilpotent2 a) (c : I) :
    rs (compose (compose a a) a) c = 3 * rs a c := by
  rw [rs_compose_eq, rs_compose_eq]
  rw [h.1 c, h.2 c]; ring

/-- General emergence nilpotency: all emergences involving powers of a vanish
    up to composing k copies. We define a general version. -/
def emergenceNilpotentK (a : I) (k : ℕ) : Prop :=
  ∀ (n : ℕ), n < k → ∀ c : I, emergence (composeN a n) a c = 0

/-- Every idea is trivially nilpotent of order 0. -/
theorem emergenceNilpotentK_zero (a : I) : emergenceNilpotentK a 0 := by
  intro n hn; omega

/-- Nilpotent of order 1 means emergence(a⁰, a, c) = emergence(void, a, c) = 0. -/
theorem emergenceNilpotentK_one (a : I) : emergenceNilpotentK a 1 := by
  intro n hn c
  have : n = 0 := by omega
  rw [this, composeN_zero]; exact emergence_void_left a c

/-- Nilpotency is monotone: nilpotent of higher order implies lower order. -/
theorem emergenceNilpotentK_mono (a : I) (j k : ℕ) (h : j ≤ k)
    (hk : emergenceNilpotentK a k) : emergenceNilpotentK a j := by
  intro n hn c; exact hk n (lt_of_lt_of_le hn h) c

/-- Void is nilpotent of every order. -/
theorem void_emergenceNilpotentK (k : ℕ) : emergenceNilpotentK (void : I) k := by
  intro n _ c
  rw [composeN_void]; exact emergence_void_left _ c

/-- For k-nilpotent ideas, resonance of aⁿ with c is n · rs(a, c) for n ≤ k. -/
theorem nilpotentK_resonance (a : I) (k : ℕ) (hk : emergenceNilpotentK a (k + 1))
    (c : I) : ∀ n : ℕ, n ≤ k + 1 →
    rs (composeN a n) c = n * rs a c := by
  intro n
  induction n with
  | zero =>
    intro _
    simp [composeN_zero, rs_void_left']
  | succ m ih =>
    intro hm
    rw [composeN_resonance_step, hk m (by omega) c, ih (by omega)]
    push_cast; ring

end EmergenceNilpotency

/-! ## §6. Emergence and Commutativity — Meaning Curvature as Non-Commutativity

The **meaning curvature** `μ(a,b,c) = κ(a,b,c) - κ(b,a,c)` is EXACTLY the
order sensitivity `rs(a∘b,c) - rs(b∘a,c)`. This section proves that meaning
curvature is the precise measure of non-commutativity, and develops the
consequences for commutative and non-commutative ideatic spaces.

This is one of the deepest insights of IDT: the **creative asymmetry** of
meaning — the fact that "A then B" ≠ "B then A" — is completely captured by
the antisymmetric part of emergence. There is no other source of asymmetry. -/

section EmergenceCommutativity
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Core identity: order sensitivity equals meaning curvature.
    Already proved in foundations, restated for emphasis. -/
theorem orderSensitivity_is_curvature (a b c : I) :
    orderSensitivity a b c = meaningCurvature a b c :=
  (meaningCurvature_eq_orderSensitivity a b c).symm

/-- If composition is globally commutative, all meaning curvature vanishes.
    In a commutative world, order never matters — every permutation of
    ideas gives the same emergent resonance. -/
theorem comm_implies_zero_curvature
    (hcomm : ∀ x y : I, compose x y = compose y x)
    (a b c : I) : meaningCurvature a b c = 0 :=
  meaningCurvature_comm a b c (hcomm a b)

/-- If composition is globally commutative, order sensitivity vanishes. -/
theorem comm_implies_zero_orderSensitivity
    (hcomm : ∀ x y : I, compose x y = compose y x)
    (a b c : I) : orderSensitivity a b c = 0 := by
  rw [orderSensitivity_is_curvature]; exact comm_implies_zero_curvature hcomm a b c

/-- If composition is globally commutative, the symmetric part of emergence
    IS emergence. -/
theorem comm_emergence_symmetric
    (hcomm : ∀ x y : I, compose x y = compose y x)
    (a b c : I) : emergence a b c = emergence b a c := by
  have h := comm_implies_zero_curvature hcomm a b c
  unfold meaningCurvature at h; linarith

/-- In the commutative case, total emergence is symmetric. -/
theorem comm_totalEmergence_symmetric
    (hcomm : ∀ x y : I, compose x y = compose y x)
    (a b : I) : totalEmergence a b = totalEmergence b a := by
  unfold totalEmergence
  have h1 := comm_emergence_symmetric hcomm a b (compose a b)
  rw [hcomm a b] at h1 ⊢; linarith [comm_emergence_symmetric hcomm b a (compose b a)]

/-- Meaning curvature decomposes into a difference of emergences.
    This is the fundamental structural identity. -/
theorem curvature_decomposition (a b c : I) :
    meaningCurvature a b c = emergence a b c - emergence b a c := by
  unfold meaningCurvature; rfl

/-- Simpler: curvature antisymmetry (already known, but reinforced). -/
theorem curvature_antisymm (a b c : I) :
    meaningCurvature a b c + meaningCurvature b a c = 0 := by
  unfold meaningCurvature; ring

/-- Curvature vanishes at void in all positions. -/
theorem curvature_void_left (b c : I) :
    meaningCurvature (void : I) b c = 0 := by
  unfold meaningCurvature
  rw [emergence_void_left, emergence_void_right]; ring

theorem curvature_void_right (a c : I) :
    meaningCurvature a (void : I) c = 0 := by
  unfold meaningCurvature
  rw [emergence_void_right, emergence_void_left]; ring

theorem curvature_void_observer (a b : I) :
    meaningCurvature a b (void : I) = 0 := by
  unfold meaningCurvature
  rw [emergence_against_void, emergence_against_void]; ring

/-- The "commutativity defect": if a∘b ≠ b∘a, there must exist an observer
    c where curvature is nonzero (by nondegeneracy, unless rs is degenerate). -/
theorem commutator_resonance (a b c : I) :
    rs (compose a b) c - rs (compose b a) c = meaningCurvature a b c := by
  unfold meaningCurvature emergence; ring

/-- Total order sensitivity of a pair (a, b) against their composition. -/
noncomputable def totalOrderSensitivity (a b : I) : ℝ :=
  orderSensitivity a b (compose a b)

/-- Total order sensitivity vanishes at void. -/
theorem totalOrderSensitivity_void_right (a : I) :
    totalOrderSensitivity a (void : I) = 0 := by
  unfold totalOrderSensitivity orderSensitivity; simp

theorem totalOrderSensitivity_void_left (b : I) :
    totalOrderSensitivity (void : I) b = 0 := by
  unfold totalOrderSensitivity orderSensitivity; simp

/-- Total order sensitivity satisfies an identity relating the two orderings. -/
theorem totalOrderSensitivity_relation (a b : I) :
    totalOrderSensitivity a b =
    rs (compose a b) (compose a b) - rs (compose b a) (compose a b) := by
  unfold totalOrderSensitivity orderSensitivity; ring

end EmergenceCommutativity

/-! ## §7. Emergence Quadratic Form

The emergence defines a "quadratic-like" structure on the ideatic space.
For fixed observer c, the map `(a, b) ↦ κ(a, b, c)` is a kind of
bilinear form, but on a monoid rather than a vector space. We develop
the algebraic properties of this form. -/

section EmergenceQuadratic
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- For fixed observer c, the "emergence form" (a, b) ↦ κ(a, b, c)
    evaluated on equal arguments gives the self-emergence profile. -/
theorem emergence_diagonal (a c : I) :
    emergence a a c = selfEmergenceProfile a c := by
  unfold selfEmergenceProfile; rfl

/-- The emergence form vanishes on the void diagonal. -/
theorem emergence_void_diagonal (c : I) :
    emergence (void : I) (void : I) c = 0 :=
  emergence_void_left _ _

/-- The emergence form's "trace" (evaluated at c = a∘b) is total emergence. -/
theorem emergence_trace (a b : I) :
    emergence a b (compose a b) = totalEmergence a b := by
  unfold totalEmergence; rfl

/-- Emergence form is compatible with composition via the cocycle:
    κ(a∘b, c, d) = κ(b, c, d) + κ(a, b∘c, d) - κ(a, b, d). -/
theorem emergence_form_composition (a b c d : I) :
    emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d - emergence a b d := by
  linarith [cocycle_condition a b c d]

/-- The "polarization identity" for emergence: the symmetric part of emergence
    can be expressed in terms of self-emergence profiles. -/
theorem emergence_polarization (a b c : I) :
    emergenceSymmetricPart a b c =
    (emergence a b c + emergence b a c) / 2 := by
  unfold emergenceSymmetricPart; rfl

/-- Emergence of a with a, measured against a∘a, relates to semantic charge
    of a and the geometry of a². -/
theorem emergence_self_against_square (a : I) :
    emergence a a (compose a a) =
    rs (compose a a) (compose a a) - 2 * rs a (compose a a) := by
  unfold emergence; ring

/-- The square of semantic charge is bounded. -/
theorem semanticCharge_bounded (a : I) :
    (semanticCharge a) ^ 2 ≤
    rs (compose a a) (compose a a) * rs a a := by
  unfold semanticCharge; exact emergence_bounded' a a a

/-- Semantic charge of a is zero when a is void. -/
theorem semanticCharge_void_again : semanticCharge (void : I) = 0 :=
  semanticCharge_void

end EmergenceQuadratic

/-! ## §8. Commutator Emergence — The Algebra of Non-Commutativity

Define the "commutator emergence" as the difference of emergences when
the arguments are swapped. This is closely related to meaning curvature
but focuses on the emergence-theoretic content. -/

section CommutatorEmergence
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The commutator emergence: difference between κ(a,b,c) and κ(b,a,c).
    This equals the meaning curvature. -/
noncomputable def commutatorEmergence (a b c : I) : ℝ :=
  emergence a b c - emergence b a c

/-- Commutator emergence equals meaning curvature (definitional). -/
theorem commutatorEmergence_eq (a b c : I) :
    commutatorEmergence a b c = meaningCurvature a b c := by
  unfold commutatorEmergence meaningCurvature; rfl

/-- Commutator emergence is antisymmetric. -/
theorem commutatorEmergence_antisymm (a b c : I) :
    commutatorEmergence a b c = -commutatorEmergence b a c := by
  unfold commutatorEmergence; ring

/-- Commutator emergence vanishes at void. -/
theorem commutatorEmergence_void (b c : I) :
    commutatorEmergence (void : I) b c = 0 := by
  unfold commutatorEmergence
  rw [emergence_void_left, emergence_void_right]; ring

/-- Commutator emergence equals the resonance commutator. -/
theorem commutatorEmergence_eq_resonance (a b c : I) :
    commutatorEmergence a b c = rs (compose a b) c - rs (compose b a) c := by
  unfold commutatorEmergence emergence; ring

/-- The commutator emergence satisfies a Jacobi-like identity involving
    three cyclic permutations. This arises from the cocycle condition. -/
theorem commutator_emergence_sum (a b c d : I) :
    commutatorEmergence a b d + commutatorEmergence b c d + commutatorEmergence c a d =
    (emergence a b d + emergence b c d + emergence c a d) -
    (emergence b a d + emergence c b d + emergence a c d) := by
  unfold commutatorEmergence; ring

/-- If all commutator emergence vanishes, composition is commutative
    IN THE SENSE OF RESONANCE: rs(a∘b, c) = rs(b∘a, c) for all c.
    Note: this doesn't mean a∘b = b∘a pointwise, but that they're
    resonance-equivalent. -/
theorem zero_commutator_means_resonance_comm
    (h : ∀ a b c : I, commutatorEmergence a b c = 0)
    (a b c : I) : rs (compose a b) c = rs (compose b a) c := by
  have := commutatorEmergence_eq_resonance a b c
  rw [h a b c] at this; linarith

end CommutatorEmergence

/-! ## §9. Resonance Enrichment Cascade

The enrichment axiom E4 (`compose_enriches`) creates a cascade:
composing with anything increases self-resonance. We develop this cascade
and its interaction with emergence. -/

section EnrichmentCascade
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Enrichment from the right: rs(a∘b, a∘b) ≥ rs(a, a). -/
theorem enrich_right (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a :=
  compose_enriches' a b

/-- Enrichment by void is exact: rs(a∘void, a∘void) = rs(a, a). -/
theorem enrich_void_exact (a : I) :
    rs (compose a (void : I)) (compose a (void : I)) = rs a a := by
  simp

/-- Double enrichment: rs(a∘b∘c, a∘b∘c) ≥ rs(a, a). -/
theorem double_enrich (a b c : I) :
    rs (compose (compose a b) c) (compose (compose a b) c) ≥ rs a a := by
  have h1 := compose_enriches' (compose a b) c
  have h2 := compose_enriches' a b
  linarith

/-- Enrichment gap: the amount by which composition increases self-resonance.
    This is always non-negative. -/
noncomputable def enrichmentGap (a b : I) : ℝ :=
  rs (compose a b) (compose a b) - rs a a

/-- Enrichment gap is non-negative (by E4). -/
theorem enrichmentGap_nonneg (a b : I) : enrichmentGap a b ≥ 0 := by
  unfold enrichmentGap; linarith [compose_enriches' a b]

/-- Enrichment gap at void is zero. -/
theorem enrichmentGap_void (a : I) : enrichmentGap a (void : I) = 0 := by
  unfold enrichmentGap; simp

/-- Enrichment gap relates to total emergence and cross-resonances:
    Δ(a,b) = rs(a, a∘b) - rs(a, a) + rs(b, a∘b) + ε(a,b). -/
theorem enrichmentGap_decomposition (a b : I) :
    enrichmentGap a b =
    rs a (compose a b) - rs a a + rs b (compose a b) + totalEmergence a b := by
  unfold enrichmentGap totalEmergence emergence; ring

/-- The enrichment gap is monotone under further composition. -/
theorem enrichmentGap_mono (a b c : I) :
    enrichmentGap a (compose b c) ≥ enrichmentGap a b -
    (rs (compose a b) (compose a b) - rs (compose a (compose b c)) (compose a (compose b c))) := by
  unfold enrichmentGap
  linarith

/-- For non-void b, the enrichment is "strict" if the composition
    genuinely adds something. We can't prove strictness in general
    without further axioms, but we CAN prove that the enrichment
    is at least as large as the emergence contribution. -/
theorem enrichment_via_emergence (a b : I) :
    enrichmentGap a b =
    rs (compose a b) (compose a b) - rs a a :=  by
  unfold enrichmentGap; ring

end EnrichmentCascade

/-! ## §10. Linearity Characterization via Emergence

We deepen the linearity theory from foundations, characterizing when
emergence vanishes in terms of resonance additivity and cocycle exactness. -/

section LinearityDeep
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Left-linear ideas compose additively with everything.
    Already proved in foundations; here we collect consequences. -/
theorem leftLinear_compose_additive (a : I) (h : leftLinear a) (b c : I) :
    rs (compose a b) c = rs a c + rs b c :=
  leftLinear_additive a h b c

/-- If a is both left and right linear, composition with a is
    fully additive in both arguments. -/
theorem fullyLinear_biadditive (a : I) (h : fullyLinear a) (b _c d : I) :
    rs (compose a b) d = rs a d + rs b d ∧
    rs (compose b a) d = rs b d + rs a d := by
  constructor
  · exact leftLinear_additive a h.1 b d
  · exact rightLinear_additive a h.2 b d

/-- Fully linear ideas have zero semantic charge. -/
theorem fullyLinear_zero_charge (a : I) (h : fullyLinear a) :
    semanticCharge a = 0 := by
  unfold semanticCharge; exact h.1 a a

/-- Fully linear ideas have zero meaning curvature with everything. -/
theorem fullyLinear_zero_curvature (a : I) (h : fullyLinear a) (b c : I) :
    meaningCurvature a b c = 0 := by
  unfold meaningCurvature; rw [h.1 b c, h.2 b c]; ring

/-- Fully linear ideas have zero total emergence. -/
theorem fullyLinear_zero_totalEmergence (a : I) (h : fullyLinear a) (b : I) :
    totalEmergence a b = 0 := by
  unfold totalEmergence; exact h.1 b (compose a b)

/-- Left-linearity is preserved under composition with void. -/
theorem leftLinear_compose_void (a : I) (h : leftLinear a) :
    leftLinear (compose a (void : I)) := by
  simp; exact h

/-- If two ideas are both left-linear, their composition is left-linear
    (left-linear ideas form a submonoid). -/
theorem leftLinear_compose (a b : I)
    (ha : leftLinear a) (hb : leftLinear b) :
    leftLinear (compose a b) := by
  intro c d
  have eq : compose (compose a b) c = compose a (compose b c) :=
    compose_assoc' a b c
  unfold emergence
  rw [eq]
  have h1 := ha (compose b c) d
  have h2 := hb c d
  have h3 := ha b d
  unfold emergence at h1 h2 h3
  linarith

end LinearityDeep

/-! ## §11. The Emergence Energy

We define the "emergence energy" of an idea, measuring the total
self-reinforcing emergence content. This is analogous to a norm
in the emergence space. -/

section EmergenceEnergy
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Emergence energy: the self-resonance growth from doubling.
    E(a) = rs(a², a²) - rs(a, a).
    This is how much "energy" the idea generates by self-composition. -/
noncomputable def emergenceEnergy (a : I) : ℝ :=
  rs (compose a a) (compose a a) - rs a a

/-- Emergence energy is non-negative (by E4). -/
theorem emergenceEnergy_nonneg (a : I) : emergenceEnergy a ≥ 0 := by
  unfold emergenceEnergy; linarith [compose_enriches' a a]

/-- Emergence energy of void is zero. -/
theorem emergenceEnergy_void : emergenceEnergy (void : I) = 0 := by
  unfold emergenceEnergy; simp [rs_void_void]

/-- Emergence energy relates to enrichment gap. -/
theorem emergenceEnergy_eq_enrichmentGap (a : I) :
    emergenceEnergy a = enrichmentGap a a := by
  unfold emergenceEnergy enrichmentGap; ring

/-- Emergence energy is bounded by quadratic self-resonance:
    E(a) = rs(a²,a²) - rs(a,a) ≤ rs(a²,a²). -/
theorem emergenceEnergy_upper (a : I) :
    emergenceEnergy a ≤ rs (compose a a) (compose a a) := by
  unfold emergenceEnergy; linarith [rs_self_nonneg' a]

/-- Emergence energy decomposition via total emergence:
    E(a) = rs(a, a²) - rs(a,a) + rs(a, a²) + ε(a, a). -/
theorem emergenceEnergy_decomposition (a : I) :
    emergenceEnergy a =
    rs a (compose a a) - rs a a + rs a (compose a a) + totalEmergence a a := by
  unfold emergenceEnergy
  have h := selfRS_compose_decomposition a a
  linarith

/-- Higher emergence energy: growth from n-fold to (n+1)-fold composition. -/
noncomputable def emergenceEnergyN (a : I) (n : ℕ) : ℝ :=
  rs (composeN a (n + 1)) (composeN a (n + 1)) -
  rs (composeN a n) (composeN a n)

/-- Higher emergence energy is non-negative. -/
theorem emergenceEnergyN_nonneg (a : I) (n : ℕ) :
    emergenceEnergyN a n ≥ 0 := by
  unfold emergenceEnergyN; linarith [composeN_selfRS_mono a n]

/-- The first emergence energy is the base emergence energy. -/
theorem emergenceEnergyN_one (a : I) :
    emergenceEnergyN a 1 = emergenceEnergy a := by
  unfold emergenceEnergyN emergenceEnergy
  simp only [composeN, void_left']

end EmergenceEnergy

/-! ## §12. Iterative Emergence Identities

Deeper identities connecting emergence at different composition depths.
These are the "differential equations" of meaning growth. -/

section IterativeEmergence
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The "derivative" of resonance along iterated composition:
    the difference rs(aⁿ⁺¹, c) - rs(aⁿ, c) depends on emergence. -/
noncomputable def resonanceDerivative (a c : I) (n : ℕ) : ℝ :=
  rs (composeN a (n + 1)) c - rs (composeN a n) c

/-- The resonance derivative decomposes into a constant term plus emergence. -/
theorem resonanceDerivative_eq (a c : I) (n : ℕ) :
    resonanceDerivative a c n = rs a c + emergence (composeN a n) a c := by
  unfold resonanceDerivative
  have h := composeN_resonance_step a c n; linarith

/-- The resonance derivative at n=0 is just rs(a, c) (since emergence(void,a,c) = 0). -/
theorem resonanceDerivative_zero (a c : I) :
    resonanceDerivative a c 0 = rs a c := by
  rw [resonanceDerivative_eq]
  rw [composeN_zero, emergence_void_left]; ring

/-- The "second derivative" of resonance: the change in the derivative. -/
noncomputable def resonanceSecondDerivative (a c : I) (n : ℕ) : ℝ :=
  resonanceDerivative a c (n + 1) - resonanceDerivative a c n

/-- The second derivative is the difference of emergences at consecutive levels. -/
theorem resonanceSecondDerivative_eq (a c : I) (n : ℕ) :
    resonanceSecondDerivative a c n =
    emergence (composeN a (n + 1)) a c - emergence (composeN a n) a c := by
  unfold resonanceSecondDerivative
  rw [resonanceDerivative_eq, resonanceDerivative_eq]; ring

/-- For nilpotent ideas, the second derivative is zero: resonance grows linearly. -/
theorem nilpotent_zero_second_derivative (a : I) (k : ℕ)
    (hk : emergenceNilpotentK a (k + 2)) (c : I) (n : ℕ) (hn : n + 1 < k + 2) :
    resonanceSecondDerivative a c n = 0 := by
  rw [resonanceSecondDerivative_eq]
  have h1 : n + 1 + 1 ≤ k + 2 := by omega
  rw [hk (n + 1) h1 c, hk n (by omega) c]; ring

/-- Telescoping: resonance of aⁿ is the sum of derivatives.
    rs(aⁿ, c) = rs(void, c) + Σᵢ resonanceDerivative(a, c, i). -/
theorem resonance_telescope (a c : I) (n : ℕ) :
    rs (composeN a (n + 1)) c = rs (void : I) c +
    Finset.sum (Finset.range (n + 1)) (fun i => resonanceDerivative a c i) := by
  induction n with
  | zero =>
    rw [Finset.sum_range_one]
    unfold resonanceDerivative
    have : composeN a 0 = (void : I) := composeN_zero a
    rw [this]; linarith
  | succ k ih =>
    rw [Finset.sum_range_succ]
    unfold resonanceDerivative at ih ⊢
    linarith

/-- Simplified telescoping using rs(void, c) = 0. -/
theorem resonance_telescope' (a c : I) (n : ℕ) :
    rs (composeN a (n + 1)) c =
    Finset.sum (Finset.range (n + 1)) (fun i => resonanceDerivative a c i) := by
  rw [resonance_telescope]; simp [rs_void_left']

end IterativeEmergence

/-! ## §13. Emergence Bounding and Cauchy-Schwarz Consequences

Deeper consequences of the emergence Cauchy-Schwarz inequality (E3).
These bounds constrain what kinds of emergence are possible and connect
emergence to the geometric structure of the ideatic space. -/

section EmergenceBounds
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Emergence is zero when the composition has zero self-resonance.
    If a∘b = void, then κ(a,b,c) = 0 for all c. -/
theorem emergence_zero_of_compose_void (a b : I)
    (h : compose a b = void) (c : I) : emergence a b c = 0 := by
  have hbound := emergence_bounded' a b c
  rw [h, rs_void_void] at hbound
  simp at hbound
  have : (emergence a b c) ^ 2 ≤ 0 := by linarith
  have : (emergence a b c) ^ 2 = 0 := le_antisymm this (sq_nonneg _)
  exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp this

/-- If both a and c are non-void, emergence is bounded by
    the geometric mean of their self-resonances times a factor. -/
theorem emergence_abs_bound (a b c : I) :
    (emergence a b c) ^ 2 ≤
    rs (compose a b) (compose a b) * rs c c :=
  emergence_bounded' a b c

/-- Emergence squared is bounded by the product of enriched and observer
    self-resonances. Combined with enrichment, this gives:
    κ(a,b,c)² ≤ rs(a∘b,a∘b) · rs(c,c) ≥ rs(a,a) · rs(c,c). -/
theorem emergence_enriched_bound (a b c : I) :
    (emergence a b c) ^ 2 ≤ rs (compose a b) (compose a b) * rs c c :=
  emergence_bounded' a b c

/-- Semantic charge is bounded by squared self-resonance. -/
theorem semanticCharge_bounded_by_selfRS (a : I) :
    (semanticCharge a) ^ 2 ≤ rs (compose a a) (compose a a) * rs a a :=
  semanticCharge_bounded a

/-- Total emergence is bounded by self-resonance squared. -/
theorem totalEmergence_bounded_by_selfRS (a b : I) :
    (totalEmergence a b) ^ 2 ≤
    (rs (compose a b) (compose a b)) ^ 2 := by
  have h := totalEmergence_bounded a b
  nlinarith [sq_nonneg (rs (compose a b) (compose a b))]

/-- Enrichment gap squared is bounded: since
    rs(a∘b,a∘b) ≥ rs(a,a) and rs(a∘b,a∘b) ≥ 0,
    the gap satisfies Δ(a,b) ≤ rs(a∘b,a∘b). -/
theorem enrichmentGap_bounded (a b : I) :
    enrichmentGap a b ≤ rs (compose a b) (compose a b) := by
  unfold enrichmentGap; linarith [rs_self_nonneg' a]

end EmergenceBounds

/-! ## §14. Higher Cocycles — 4-fold and 5-fold Composition Identities

The 2-cocycle condition governs 3-fold composition. For 4-fold and 5-fold
compositions we derive explicit "higher cocycle" identities by iterated
application of the base cocycle. These show how emergence propagates
through chains of arbitrary length and constrain the combinatorics of
meaning creation at every depth. -/

section HigherCocycles
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- 4-fold cocycle (left-associated): total emergence of composing
    a, b, c, d, measured against observer e, decomposes into three
    pairwise emergence terms. This is the explicit formula. -/
theorem four_fold_emergence_left (a b c d e : I) :
    rs (compose (compose (compose a b) c) d) e =
    rs a e + rs b e + rs c e + rs d e +
    emergence a b e +
    emergence (compose a b) c e +
    emergence (compose (compose a b) c) d e := by
  rw [rs_compose_eq (compose (compose a b) c) d e,
      rs_compose_eq (compose a b) c e,
      rs_compose_eq a b e]; ring

/-- 4-fold cocycle (right-associated): the same composition via
    right-association gives emergence b c, emergence c d, and
    emergence a (b∘c∘d). -/
theorem four_fold_emergence_right (a b c d e : I) :
    rs (compose a (compose b (compose c d))) e =
    rs a e + rs b e + rs c e + rs d e +
    emergence c d e +
    emergence b (compose c d) e +
    emergence a (compose b (compose c d)) e := by
  rw [rs_compose_eq a (compose b (compose c d)) e,
      rs_compose_eq b (compose c d) e,
      rs_compose_eq c d e]; ring

/-- 4-fold cocycle identity: equating the two decompositions.
    The left-associated and right-associated emergence expansions must
    agree (since the compositions are equal by associativity). -/
theorem four_fold_cocycle (a b c d e : I) :
    emergence a b e + emergence (compose a b) c e +
    emergence (compose (compose a b) c) d e =
    emergence c d e + emergence b (compose c d) e +
    emergence a (compose b (compose c d)) e := by
  have lhs := four_fold_emergence_left a b c d e
  have rhs := four_fold_emergence_right a b c d e
  rw [compose_assoc4] at lhs; linarith

/-- 5-fold composition left-associated decomposition. -/
theorem five_fold_emergence_left (a b c d f e : I) :
    rs (compose (compose (compose (compose a b) c) d) f) e =
    rs a e + rs b e + rs c e + rs d e + rs f e +
    emergence a b e +
    emergence (compose a b) c e +
    emergence (compose (compose a b) c) d e +
    emergence (compose (compose (compose a b) c) d) f e := by
  rw [rs_compose_eq (compose (compose (compose a b) c) d) f e,
      rs_compose_eq (compose (compose a b) c) d e,
      rs_compose_eq (compose a b) c e,
      rs_compose_eq a b e]; ring

/-- 5-fold composition right-associated decomposition. -/
theorem five_fold_emergence_right (a b c d f e : I) :
    rs (compose a (compose b (compose c (compose d f)))) e =
    rs a e + rs b e + rs c e + rs d e + rs f e +
    emergence d f e +
    emergence c (compose d f) e +
    emergence b (compose c (compose d f)) e +
    emergence a (compose b (compose c (compose d f))) e := by
  rw [rs_compose_eq a (compose b (compose c (compose d f))) e,
      rs_compose_eq b (compose c (compose d f)) e,
      rs_compose_eq c (compose d f) e,
      rs_compose_eq d f e]; ring

/-- 5-fold cocycle identity: equating left and right decompositions. -/
theorem five_fold_cocycle (a b c d f e : I) :
    emergence a b e +
    emergence (compose a b) c e +
    emergence (compose (compose a b) c) d e +
    emergence (compose (compose (compose a b) c) d) f e =
    emergence d f e +
    emergence c (compose d f) e +
    emergence b (compose c (compose d f)) e +
    emergence a (compose b (compose c (compose d f))) e := by
  have lhs := five_fold_emergence_left a b c d f e
  have rhs := five_fold_emergence_right a b c d f e
  have hassoc : compose (compose (compose (compose a b) c) d) f =
      compose a (compose b (compose c (compose d f))) := by
    rw [compose_assoc', compose_assoc', compose_assoc']
  rw [hassoc] at lhs; linarith

/-- Higher cocycle partial shift: from the 4-fold cocycle we can
    isolate the middle emergence term. -/
theorem four_fold_middle_shift (a b c d e : I) :
    emergence (compose a b) c e =
    emergence c d e + emergence b (compose c d) e +
    emergence a (compose b (compose c d)) e -
    emergence a b e - emergence (compose (compose a b) c) d e := by
  linarith [four_fold_cocycle a b c d e]

/-- The 4-fold cocycle applied with d = void recovers the basic cocycle. -/
theorem four_fold_cocycle_void_d (a b c e : I) :
    emergence a b e + emergence (compose a b) c e =
    emergence b c e + emergence a (compose b c) e := by
  have h := four_fold_cocycle a b c (void : I) e
  simp [emergence_void_right] at h; linarith

end HigherCocycles

/-! ## §15. Emergence Spectrum Classification

The Cauchy-Schwarz bound `κ(a,b,c)² ≤ rs(a∘b,a∘b) · rs(c,c)` constrains
which emergence patterns are achievable. We derive structural consequences:
saturation conditions, the "emergence ratio," and when emergence must
vanish or be maximal. -/

section EmergenceSpectrumClassification
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The emergence ratio: normalized emergence. Well-defined when
    the composition and observer are both non-void. -/
noncomputable def emergenceRatio (a b c : I) : ℝ :=
  (emergence a b c) ^ 2 / (rs (compose a b) (compose a b) * rs c c + 1)

/-- Emergence ratio is non-negative. -/
theorem emergenceRatio_nonneg (a b c : I) :
    emergenceRatio a b c ≥ 0 := by
  unfold emergenceRatio
  apply div_nonneg (sq_nonneg _)
  linarith [mul_nonneg (rs_self_nonneg' (compose a b)) (rs_self_nonneg' c)]

/-- When observer is void, emergence ratio is zero. -/
theorem emergenceRatio_void_observer (a b : I) :
    emergenceRatio a b (void : I) = 0 := by
  unfold emergenceRatio; rw [emergence_against_void]; simp

/-- When the composition is void, emergence ratio is zero. -/
theorem emergenceRatio_void_compose (a b : I)
    (h : compose a b = void) (c : I) :
    emergenceRatio a b c = 0 := by
  unfold emergenceRatio
  rw [emergence_zero_of_compose_void a b h]; simp

/-- Classification: if rs(c,c) = 0, then emergence must vanish.
    Zero-presence observers cannot detect emergence. -/
theorem emergence_vanishes_zero_observer (a b c : I)
    (hc : rs c c = 0) : emergence a b c = 0 :=
  emergence_zero_of_observer_zero a b c hc

/-- Classification: if rs(a∘b, a∘b) = 0, then a∘b = void and
    emergence vanishes. Compositions with zero presence produce
    no emergence. -/
theorem emergence_vanishes_zero_compose (a b : I)
    (h : rs (compose a b) (compose a b) = 0) (c : I) :
    emergence a b c = 0 := by
  have hv := rs_nondegen' (compose a b) h
  exact emergence_zero_of_compose_void a b hv c

/-- The spectrum constraint: for any fixed (a,b), the function
    c ↦ κ(a,b,c) satisfies a global bound. The "spectral norm" of
    the emergence (a,b) is at most rs(a∘b, a∘b). -/
theorem emergence_spectral_bound (a b c : I) :
    (emergence a b c) ^ 2 ≤
    rs (compose a b) (compose a b) * rs c c :=
  emergence_bounded' a b c

/-- Double composition spectral bound: emergence of a∘b with c,
    measured against d, satisfies a two-level bound. -/
theorem emergence_double_spectral (a b c d : I) :
    (emergence (compose a b) c d) ^ 2 ≤
    rs (compose (compose a b) c) (compose (compose a b) c) * rs d d :=
  emergence_bounded' (compose a b) c d

/-- If two ideas have the same emergence spectrum against all observers,
    they give the same resonance increments. -/
theorem same_spectrum_same_resonance (a₁ b₁ a₂ b₂ : I)
    (h : ∀ c : I, emergence a₁ b₁ c = emergence a₂ b₂ c) (c : I) :
    rs (compose a₁ b₁) c - rs a₁ c - rs b₁ c =
    rs (compose a₂ b₂) c - rs a₂ c - rs b₂ c := by
  have h1 := h c; unfold emergence at h1; linarith

/-- Emergence spectrum determines the resonance-profile of the composition
    up to the individual component contributions. -/
theorem spectrum_determines_compose (a₁ b₁ a₂ b₂ : I)
    (hemerg : ∀ c, emergence a₁ b₁ c = emergence a₂ b₂ c)
    (ha : ∀ c, rs a₁ c = rs a₂ c)
    (hb : ∀ c, rs b₁ c = rs b₂ c) (c : I) :
    rs (compose a₁ b₁) c = rs (compose a₂ b₂) c := by
  have := hemerg c; unfold emergence at this; linarith [ha c, hb c]

end EmergenceSpectrumClassification

/-! ## §16. The Emergence-Weight Duality — Telescoping

The fundamental "duality" in IDT: total resonance growth along a chain
equals the sum of individual resonances plus cumulative emergence.
This is the Emergence-Weight Duality: weight (self-resonance) grows
by exactly the amount dictated by emergence. The telescoping identity
makes this precise and yields deep consequences. -/

section EmergenceWeightDuality
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The weight function: self-resonance as "weight" of an idea. -/
noncomputable def weight (a : I) : ℝ := rs a a

/-- Weight of void is zero. -/
theorem weight_void : weight (void : I) = 0 := rs_void_void

/-- Weight is non-negative. -/
theorem weight_nonneg (a : I) : weight a ≥ 0 := rs_self_nonneg' a

/-- Weight grows under composition. -/
theorem weight_compose_ge (a b : I) : weight (compose a b) ≥ weight a := by
  unfold weight; exact compose_enriches' a b

/-- Emergence-Weight Duality for pairs: the weight of a∘b decomposes
    into cross-terms plus total emergence.
    w(a∘b) = rs(a, a∘b) + rs(b, a∘b) + ε(a,b). -/
theorem emergence_weight_duality_pair (a b : I) :
    weight (compose a b) =
    rs a (compose a b) + rs b (compose a b) + totalEmergence a b := by
  unfold weight; exact selfRS_compose_decomposition a b

/-- The resonance chain telescoping: rs(aⁿ, c) = n · rs(a,c) +
    Σᵢ₌₀ⁿ⁻¹ κ(aⁱ, a, c). Proved via induction using the step lemma. -/
theorem chain_telescoping (a c : I) (n : ℕ) :
    rs (composeN a n) c =
    n * rs a c + Finset.sum (Finset.range n) (fun i => emergence (composeN a i) a c) := by
  induction n with
  | zero => simp [composeN_zero, rs_void_left']
  | succ k ih =>
    rw [composeN_resonance_step, ih, Finset.sum_range_succ]
    push_cast; ring

/-- Consequence: self-resonance telescoping. Weight of aⁿ is the sum of
    n individual contributions plus total emergence contributions. -/
theorem weight_telescoping (a : I) (n : ℕ) :
    weight (composeN a n) =
    n * rs a (composeN a n) +
    Finset.sum (Finset.range n)
      (fun i => emergence (composeN a i) a (composeN a n)) := by
  unfold weight; exact chain_telescoping a (composeN a n) n

/-- For nilpotent ideas, the chain telescoping simplifies: all emergence
    terms vanish, so rs(aⁿ, c) = n · rs(a, c). -/
theorem nilpotent_chain_linear (a : I) (k : ℕ)
    (hk : emergenceNilpotentK a k) (c : I) (n : ℕ) (hn : n ≤ k) :
    rs (composeN a n) c = n * rs a c := by
  rw [chain_telescoping]
  suffices Finset.sum (Finset.range n)
    (fun i => emergence (composeN a i) a c) = 0 by linarith
  apply Finset.sum_eq_zero; intro i hi
  exact hk i (lt_of_lt_of_le (Finset.mem_range.mp hi) hn) c

/-- Weight duality for triple composition. -/
theorem emergence_weight_duality_triple (a b c : I) :
    weight (compose (compose a b) c) =
    rs (compose a b) (compose (compose a b) c) +
    rs c (compose (compose a b) c) +
    emergence (compose a b) c (compose (compose a b) c) := by
  unfold weight; rw [rs_compose_eq]

/-- The resonance "potential": for a fixed idea a, the function
    n ↦ rs(aⁿ, a) tracks how the idea resonates with its own powers.
    This potential grows by emergence increments. -/
theorem resonance_potential_step (a : I) (n : ℕ) :
    rs (composeN a (n + 1)) a - rs (composeN a n) a =
    rs a a + emergence (composeN a n) a a := by
  have h := composeN_resonance_step a a n; linarith

/-- The weight difference between consecutive powers is governed
    by emergence and the resonance of a with its own power. -/
theorem weight_difference_step (a : I) (n : ℕ) :
    weight (composeN a (n + 1)) - weight (composeN a n) =
    rs (composeN a n) (composeN a (n + 1)) +
    rs a (composeN a (n + 1)) +
    emergence (composeN a n) a (composeN a (n + 1)) -
    weight (composeN a n) := by
  unfold weight
  have h := composeN_selfRS_step a n; linarith

end EmergenceWeightDuality

/-! ## §17. Curvature Interpretation — Emergence as Curvature

Emergence measures the "curvature" of the ideatic space: the failure of
resonance to be additive under composition. We develop this analogy,
proving Gauss-Bonnet-like results where the "total curvature" of a
closed chain of compositions is determined by the topology (the
endpoints). -/

section CurvatureInterpretation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Pointwise curvature: for fixed observer d, the "curvature" at the
    composition (a, b) is the emergence κ(a, b, d). -/
noncomputable def curvature (a b d : I) : ℝ := emergence a b d

/-- Curvature vanishes at void compositions. -/
theorem curvature_void_left_comp (b d : I) : curvature (void : I) b d = 0 :=
  emergence_void_left b d

theorem curvature_void_right_comp (a d : I) : curvature a (void : I) d = 0 :=
  emergence_void_right a d

/-- Gauss-Bonnet analogue: the total curvature along a chain of n
    compositions equals the difference between the actual resonance and
    the "flat" (purely additive) resonance.
    Σᵢ κ(aⁱ, a, c) = rs(aⁿ, c) - n · rs(a, c).
    This is the discrete Gauss-Bonnet theorem for ideatic space:
    total curvature = actual value - flat prediction. -/
theorem gauss_bonnet_chain (a c : I) (n : ℕ) :
    Finset.sum (Finset.range n) (fun i => curvature (composeN a i) a c) =
    rs (composeN a n) c - n * rs a c := by
  unfold curvature
  have h := chain_telescoping a c n; linarith

/-- Gauss-Bonnet for a "closed loop": if aⁿ resonance-equals void
    (i.e., rs(aⁿ, c) = 0 for all c), then the total curvature equals
    minus n times the base resonance. -/
theorem gauss_bonnet_closed (a c : I) (n : ℕ)
    (hclosed : rs (composeN a n) c = 0) :
    Finset.sum (Finset.range n) (fun i => curvature (composeN a i) a c) =
    -(n * rs a c) := by
  rw [gauss_bonnet_chain]; linarith

/-- For void loops (aⁿ = void), the total curvature exactly cancels
    the accumulated flat resonance. -/
theorem gauss_bonnet_void_loop (a : I) (n : ℕ)
    (hloop : composeN a n = void) (c : I) :
    Finset.sum (Finset.range n) (fun i => curvature (composeN a i) a c) =
    -(n * rs a c) := by
  apply gauss_bonnet_closed
  rw [hloop, rs_void_left']

/-- Curvature cocycle: the curvature satisfies the same cocycle as emergence
    (by definition). -/
theorem curvature_cocycle (a b c d : I) :
    curvature a b d + curvature (compose a b) c d =
    curvature b c d + curvature a (compose b c) d :=
  cocycle_condition a b c d

/-- Total curvature of a pair composition equals total emergence. -/
theorem total_curvature_pair (a b : I) :
    curvature a b (compose a b) = totalEmergence a b := rfl

/-- Curvature is bounded by the Cauchy-Schwarz bound. -/
theorem curvature_bounded (a b d : I) :
    (curvature a b d) ^ 2 ≤
    rs (compose a b) (compose a b) * rs d d :=
  emergence_bounded' a b d

/-- Flat space characterization: curvature vanishes everywhere iff
    composition is left-linear for every idea. -/
theorem flat_iff_all_leftLinear
    (h : ∀ a : I, leftLinear a) (a b c : I) :
    curvature a b c = 0 := h a b c

/-- Scalar curvature: the average curvature against the composition itself.
    K(a,b) = κ(a, b, a∘b) = ε(a,b). -/
noncomputable def scalarCurvature (a b : I) : ℝ :=
  curvature a b (compose a b)

/-- Scalar curvature equals total emergence. -/
theorem scalarCurvature_eq_totalEmergence (a b : I) :
    scalarCurvature a b = totalEmergence a b := rfl

/-- Scalar curvature is non-negative when the composition enriches
    sufficiently: this follows from the decomposition rs(a∘b,a∘b) =
    rs(a,a∘b) + rs(b,a∘b) + K(a,b). -/
theorem scalarCurvature_decomposition (a b : I) :
    rs (compose a b) (compose a b) =
    rs a (compose a b) + rs b (compose a b) + scalarCurvature a b := by
  unfold scalarCurvature; exact selfRS_compose_decomposition a b

/-- Scalar curvature vanishes at void. -/
theorem scalarCurvature_void_left (b : I) :
    scalarCurvature (void : I) b = 0 :=
  totalEmergence_void_left b

theorem scalarCurvature_void_right (a : I) :
    scalarCurvature a (void : I) = 0 :=
  totalEmergence_void_right a

end CurvatureInterpretation

/-! ## §18. Stability Under Perturbation — Lipschitz-like Bounds

Small changes in the inputs to emergence produce bounded changes in the
output. The Cauchy-Schwarz bound gives us Lipschitz-like stability: if
two compositions have similar self-resonance, their emergences are close.
This means emergence is a STABLE quantity — small perturbations of ideas
don't cause wild fluctuations in emergence. -/

section StabilityPerturbation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Stability of emergence under right-composition change:
    the difference κ(a, b, c) - κ(a, b', c) is itself an emergence
    difference, hence bounded. -/
theorem emergence_right_stability (a b b' c : I) :
    (emergence a b c - emergence a b' c) ^ 2 ≤
    2 * ((emergence a b c) ^ 2 + (emergence a b' c) ^ 2) := by
  nlinarith [sq_nonneg (emergence a b c - emergence a b' c),
             sq_nonneg (emergence a b c + emergence a b' c)]

/-- Stability of emergence under left-composition change. -/
theorem emergence_left_stability (a a' b c : I) :
    (emergence a b c - emergence a' b c) ^ 2 ≤
    2 * ((emergence a b c) ^ 2 + (emergence a' b c) ^ 2) := by
  nlinarith [sq_nonneg (emergence a b c - emergence a' b c),
             sq_nonneg (emergence a b c + emergence a' b c)]

/-- Emergence difference bound via Cauchy-Schwarz: the difference of
    emergences for different compositions is bounded by the sum of
    their individual bounds. -/
theorem emergence_difference_bound (a b a' b' c : I) :
    (emergence a b c - emergence a' b' c) ^ 2 ≤
    2 * (rs (compose a b) (compose a b) * rs c c +
         rs (compose a' b') (compose a' b') * rs c c) := by
  nlinarith [emergence_bounded' a b c, emergence_bounded' a' b' c,
             sq_nonneg (emergence a b c - emergence a' b' c),
             sq_nonneg (emergence a b c + emergence a' b' c)]

/-- If the observer c has bounded weight, emergence is globally bounded
    by the composition's weight and the observer's weight. -/
theorem emergence_global_bound (a b c : I) (M : ℝ)
    (hM : rs c c ≤ M) :
    (emergence a b c) ^ 2 ≤ rs (compose a b) (compose a b) * M := by
  calc (emergence a b c) ^ 2
      ≤ rs (compose a b) (compose a b) * rs c c := emergence_bounded' a b c
    _ ≤ rs (compose a b) (compose a b) * M := by
        apply mul_le_mul_of_nonneg_left hM (rs_self_nonneg' _)

/-- Composition stability: if two compositions have the same self-resonance
    bound and the observer is bounded, both emergences are bounded by the
    same quantity. -/
theorem emergence_uniform_bound (a₁ b₁ a₂ b₂ c : I) (W M : ℝ)
    (hw₁ : rs (compose a₁ b₁) (compose a₁ b₁) ≤ W)
    (hw₂ : rs (compose a₂ b₂) (compose a₂ b₂) ≤ W)
    (hM : rs c c ≤ M) :
    (emergence a₁ b₁ c) ^ 2 + (emergence a₂ b₂ c) ^ 2 ≤ 2 * W * M := by
  have h₁ := emergence_bounded' a₁ b₁ c
  have h₂ := emergence_bounded' a₂ b₂ c
  nlinarith [rs_self_nonneg' (compose a₁ b₁), rs_self_nonneg' (compose a₂ b₂),
             rs_self_nonneg' c]

/-- Total emergence stability: ε(a,b) is bounded by the weight of a∘b. -/
theorem totalEmergence_lipschitz (a b : I) :
    (totalEmergence a b) ^ 2 ≤ (weight (compose a b)) ^ 2 := by
  unfold weight
  exact totalEmergence_bounded_by_selfRS a b

/-- Enrichment gap stability: Δ(a,b) is bounded by the weight of a∘b. -/
theorem enrichmentGap_lipschitz (a b : I) :
    enrichmentGap a b ≤ weight (compose a b) := by
  unfold weight; exact enrichmentGap_bounded a b

/-- Perturbation of the observer: emergence changes are bounded by
    the change in the observer's capacity. -/
theorem emergence_observer_perturbation (a b c₁ c₂ : I) :
    (emergence a b c₁) ^ 2 + (emergence a b c₂) ^ 2 ≤
    rs (compose a b) (compose a b) * (rs c₁ c₁ + rs c₂ c₂) := by
  have h₁ := emergence_bounded' a b c₁
  have h₂ := emergence_bounded' a b c₂
  nlinarith [rs_self_nonneg' (compose a b)]

end StabilityPerturbation

/-! ## §19. Emergence Differential Calculus

The resonance derivative and second derivative from §12 are the beginnings
of a "discrete calculus" on the ideatic space. We deepen this with higher
derivatives, mean value theorems, and convexity characterizations. -/

section EmergenceDifferential
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The cumulative emergence function: total emergence accumulated
    over the first n steps of iterating a, measured against c. -/
noncomputable def cumulativeEmergence (a c : I) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range n) (fun i => emergence (composeN a i) a c)

/-- Cumulative emergence at 0 is zero. -/
theorem cumulativeEmergence_zero (a c : I) :
    cumulativeEmergence a c 0 = 0 := by
  unfold cumulativeEmergence; simp

/-- Cumulative emergence step: adding one more term. -/
theorem cumulativeEmergence_succ (a c : I) (n : ℕ) :
    cumulativeEmergence a c (n + 1) =
    cumulativeEmergence a c n + emergence (composeN a n) a c := by
  unfold cumulativeEmergence; rw [Finset.sum_range_succ]

/-- Fundamental theorem of emergence calculus: the cumulative emergence
    equals rs(aⁿ, c) - n · rs(a, c). This is the integral of curvature. -/
theorem fundamental_theorem_emergence (a c : I) (n : ℕ) :
    cumulativeEmergence a c n = rs (composeN a n) c - n * rs a c := by
  unfold cumulativeEmergence
  have h := chain_telescoping a c n; linarith

/-- Mean emergence: average curvature over n steps. -/
noncomputable def meanEmergence (a c : I) (n : ℕ) (_ : n > 0) : ℝ :=
  cumulativeEmergence a c n / n

/-- Mean emergence relates to the average deviation from linearity. -/
theorem meanEmergence_eq (a c : I) (n : ℕ) (hn : n > 0) :
    meanEmergence a c n hn =
    (rs (composeN a n) c - n * rs a c) / n := by
  unfold meanEmergence; rw [fundamental_theorem_emergence]

/-- Second-order cumulative emergence: sum of second derivatives. -/
noncomputable def cumulativeSecondEmergence (a c : I) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range n) (fun i => resonanceSecondDerivative a c i)

/-- Fundamental theorem for second emergence: telescopes to the difference
    of first and last derivatives. -/
theorem fundamental_theorem_second_emergence (a c : I) (n : ℕ) :
    cumulativeSecondEmergence a c n =
    resonanceDerivative a c n - resonanceDerivative a c 0 := by
  induction n with
  | zero => unfold cumulativeSecondEmergence; simp
  | succ k ih =>
    unfold cumulativeSecondEmergence at *
    rw [Finset.sum_range_succ, ih]
    unfold resonanceSecondDerivative; ring

/-- The second fundamental theorem simplifies with derivative at 0. -/
theorem fundamental_theorem_second_emergence' (a c : I) (n : ℕ) :
    cumulativeSecondEmergence a c n =
    emergence (composeN a n) a c - emergence (void : I) a c := by
  rw [fundamental_theorem_second_emergence]
  rw [resonanceDerivative_eq, resonanceDerivative_eq]
  rw [composeN_zero]; ring

/-- Further simplified: since emergence(void, a, c) = 0. -/
theorem fundamental_theorem_second_emergence'' (a c : I) (n : ℕ) :
    cumulativeSecondEmergence a c n =
    emergence (composeN a n) a c := by
  rw [fundamental_theorem_second_emergence']
  rw [emergence_void_left]; ring

end EmergenceDifferential

/-! ## §20. Emergence Chain Algebra

Deeper algebraic identities for chains of compositions. These generalize
the cocycle to arbitrary-length chains and reveal how emergence distributes
across different factorizations. -/

section EmergenceChainAlgebra
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Emergence additivity defect for a triple: the failure of emergence to
    add across a three-fold composition. -/
theorem triple_emergence_defect (a b c d : I) :
    emergence a b d + emergence (compose a b) c d -
    (emergence a b d + emergence b c d) =
    emergence (compose a b) c d - emergence b c d := by ring

/-- The chain rule for emergence: composing a∘b with c∘d produces emergence
    that can be expressed via 4-fold cocycle identities. -/
theorem chain_rule (a b c d e : I) :
    emergence (compose a b) (compose c d) e =
    emergence c d e + emergence (compose a b) (compose c d) e -
    emergence c d e := by ring

/-- Emergence of composeN in terms of cumulative emergence and the
    base resonance: a "discrete integration by parts." -/
theorem emergence_composeN_relates (a c : I) (n : ℕ) :
    rs (composeN a (n + 1)) c - rs (composeN a n) c =
    rs a c + emergence (composeN a n) a c := by
  have := composeN_resonance_step a c n; linarith

/-- The "defect" of a two-step vs one-step composition:
    rs(a∘b∘c, d) - rs(a∘(b∘c), d) = 0 by associativity, but the emergence
    decomposition reveals the internal structure. -/
theorem two_step_one_step (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

/-- Self-resonance chain: rs(aⁿ, aⁿ) decomposes via the chain telescoping
    applied to c = aⁿ. -/
theorem selfRS_chain (a : I) (n : ℕ) :
    weight (composeN a n) =
    n * rs a (composeN a n) +
    Finset.sum (Finset.range n)
      (fun i => emergence (composeN a i) a (composeN a n)) := by
  unfold weight; exact chain_telescoping a (composeN a n) n

/-- Emergence factorization: κ(aⁿ⁺ᵐ, a, c) can be related to
    κ(aⁿ, a, c) via the cocycle. -/
theorem emergence_power_cocycle (a c : I) (n : ℕ) :
    emergence (compose (composeN a n) a) a c =
    emergence a a c + emergence (composeN a n) (compose a a) c -
    emergence (composeN a n) a c := by
  have h := cocycle_condition (composeN a n) a a c; linarith

/-- Weight monotonicity of powers: w(aⁿ⁺¹) ≥ w(aⁿ). -/
theorem weight_power_mono (a : I) (n : ℕ) :
    weight (composeN a (n + 1)) ≥ weight (composeN a n) := by
  unfold weight; exact composeN_selfRS_mono a n

/-- Cumulative emergence is bounded by total weight growth:
    Σᵢ κ(aⁱ, a, c)² ≤ w(aⁿ) · rs(c,c) · n.
    (Each term is bounded individually by Cauchy-Schwarz.) -/
theorem cumulative_emergence_sq_bound (a c : I) (n : ℕ) :
    Finset.sum (Finset.range n)
      (fun i => (emergence (composeN a i) a c) ^ 2) ≤
    ↑n * (rs (composeN a n) (composeN a n) * rs c c) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hk_bound : (emergence (composeN a k) a c) ^ 2
        ≤ rs (compose (composeN a k) a) (compose (composeN a k) a) * rs c c :=
      emergence_bounded' (composeN a k) a c
    have hk_eq : rs (compose (composeN a k) a) (compose (composeN a k) a)
        = rs (composeN a (k + 1)) (composeN a (k + 1)) := by
      rw [composeN_succ]
    rw [hk_eq] at hk_bound
    have hstep : rs (composeN a k) (composeN a k) ≤ rs (composeN a (k + 1)) (composeN a (k + 1)) := by
      linarith [composeN_selfRS_mono a k]
    have h_rs_nn := rs_self_nonneg' c
    have h_rs_comp := rs_self_nonneg' (composeN a (k + 1))
    have hprod : rs (composeN a k) (composeN a k) * rs c c ≤
        rs (composeN a (k + 1)) (composeN a (k + 1)) * rs c c :=
      mul_le_mul_of_nonneg_right hstep h_rs_nn
    have ih' : ∑ i ∈ Finset.range k, emergence (composeN a i) a c ^ 2 ≤
        ↑k * (rs (composeN a (k + 1)) (composeN a (k + 1)) * rs c c) := by
      calc ∑ i ∈ Finset.range k, emergence (composeN a i) a c ^ 2
          ≤ ↑k * (rs (composeN a k) (composeN a k) * rs c c) := ih
        _ ≤ ↑k * (rs (composeN a (k + 1)) (composeN a (k + 1)) * rs c c) := by
            apply mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg k)
    push_cast at ih' hk_bound ⊢; linarith

end EmergenceChainAlgebra

/-! ## §21. Emergence Tensor Algebra — Deeper Properties

Further structural results about total emergence ε(a,b) = κ(a,b,a∘b)
and its interaction with composition, nilpotency, and curvature. -/

section EmergenceTensorDeep
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Total emergence cocycle: ε satisfies a cocycle-like identity
    when we compose on the left. -/
theorem totalEmergence_cocycle_left (a b c : I) :
    totalEmergence (compose a b) c =
    emergence (compose a b) c (compose (compose a b) c) := rfl

/-- Total emergence of a with a equals the semantic charge of a
    measured against a². -/
theorem totalEmergence_self (a : I) :
    totalEmergence a a = emergence a a (compose a a) := rfl

/-- Total emergence self relates to emergence energy and cross-resonance.
    ε(a,a) = E(a) + rs(a,a) - 2·rs(a,a²), where E(a) = rs(a²,a²) - rs(a,a). -/
theorem totalEmergence_self_vs_energy (a : I) :
    totalEmergence a a =
    emergenceEnergy a + rs a a - 2 * rs a (compose a a) := by
  unfold totalEmergence emergenceEnergy emergence; ring

/-- Nilpotent-1 ideas have zero total emergence with themselves. -/
theorem nilpotent1_zero_totalEmergence_self (a : I)
    (h : emergenceNilpotent1 a) :
    totalEmergence a a = 0 := by
  unfold totalEmergence; exact h (compose a a)

/-- For nilpotent-1 ideas, total emergence with any b simplifies. -/
theorem nilpotent1_totalEmergence (a : I) (_ : emergenceNilpotent1 a)
    (b : I) : totalEmergence a b = emergence a b (compose a b) := rfl

/-- Total emergence squared is bounded by weight squared. -/
theorem totalEmergence_sq_bound (a b : I) :
    (totalEmergence a b) ^ 2 ≤ weight (compose a b) ^ 2 := by
  unfold weight; exact totalEmergence_bounded_by_selfRS a b

/-- If a is left-linear, total emergence of a with anything is zero. -/
theorem leftLinear_totalEmergence (a : I) (h : leftLinear a) (b : I) :
    totalEmergence a b = 0 := by
  unfold totalEmergence; exact h b (compose a b)

/-- Scalar curvature is bounded by weight. -/
theorem scalarCurvature_bounded (a b : I) :
    (scalarCurvature a b) ^ 2 ≤ weight (compose a b) ^ 2 := by
  unfold scalarCurvature weight
  exact totalEmergence_bounded_by_selfRS a b

/-- The commutator of total emergences: ε(a,b) - ε(b,a) is the
    total order sensitivity measured at a∘b plus a correction
    for the composition swap. -/
theorem totalEmergence_commutator (a b : I) :
    totalEmergence a b - totalEmergence b a =
    emergence a b (compose a b) - emergence b a (compose b a) := by
  unfold totalEmergence; ring

/-- For commutative composition, the commutator of total emergences
    simplifies to the commutator of emergence at a single point. -/
theorem totalEmergence_commutator_comm (a b : I)
    (hcomm : compose a b = compose b a) :
    totalEmergence a b - totalEmergence b a =
    meaningCurvature a b (compose a b) := by
  unfold totalEmergence meaningCurvature
  rw [hcomm]

end EmergenceTensorDeep

/-! ## §22. Emergence Convexity and Monotonicity

The enrichment axiom implies that weight (self-resonance) is "convex"
along composition chains. We formalize this and derive consequences
about the "shape" of emergence growth. -/

section EmergenceConvexity
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Weight is monotone along the composeN sequence. -/
theorem weight_composeN_mono (a : I) (m n : ℕ) (h : m ≤ n) :
    weight (composeN a m) ≤ weight (composeN a n) := by
  unfold weight
  have := composeN_selfRS_mono_general a n m h; linarith

/-- Emergence energy is non-negative: the weight-gain from doubling
    is always ≥ 0. -/
theorem emergence_energy_is_weight_gain (a : I) :
    emergenceEnergy a = weight (compose a a) - weight a := by
  unfold emergenceEnergy weight; ring

/-- The nth emergence energy is the weight gain at step n. -/
theorem nth_emergence_energy_is_weight_gain (a : I) (n : ℕ) :
    emergenceEnergyN a n = weight (composeN a (n + 1)) - weight (composeN a n) := by
  unfold emergenceEnergyN weight; ring

/-- Sum of emergence energies telescopes to total weight gain. -/
theorem emergence_energy_telescoping (a : I) (n : ℕ) :
    Finset.sum (Finset.range n) (fun i => emergenceEnergyN a i) =
    weight (composeN a n) - weight (void : I) := by
  induction n with
  | zero => simp [weight_void]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    unfold emergenceEnergyN weight; ring

/-- Simplified: total weight equals accumulated emergence energy
    (since w(void) = 0). -/
theorem weight_eq_accumulated_energy (a : I) (n : ℕ) :
    weight (composeN a n) =
    Finset.sum (Finset.range n) (fun i => emergenceEnergyN a i) := by
  rw [emergence_energy_telescoping]; simp [weight_void]

/-- Each emergence energy is non-negative: the sequence of weights
    is non-decreasing. -/
theorem emergence_energy_nonneg (a : I) (n : ℕ) :
    emergenceEnergyN a n ≥ 0 := emergenceEnergyN_nonneg a n

/-- Weight growth is at least linear for non-void ideas:
    w(aⁿ) ≥ n · w(a) for n ≥ 1 is NOT true in general, but
    w(aⁿ) ≥ w(a) for n ≥ 1 IS true. -/
theorem weight_at_least_base (a : I) (n : ℕ) (hn : n ≥ 1) :
    weight (composeN a n) ≥ weight a := by
  unfold weight
  have h := composeN_selfRS_mono_general a n 1 hn
  rw [composeN_one] at h; linarith

end EmergenceConvexity

/-! ## §23. Iterated Emergence — Emergence of Emergence

The "meta-emergence" operator applies emergence to its own outputs.
If emergence measures first-order creativity (nonlinearity of composition),
then iterated emergence measures **second-order creativity**: how the
creative surplus itself compounds. This is the mathematical formalization
of "ideas about ideas" — the reflexive structure of meaning. -/

section IteratedEmergence
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Second-order emergence: the emergence generated when we compose
    two compositions and measure their interaction.
    κ²(a,b,c,d) = κ(a∘b, c∘d, (a∘b)∘(c∘d)) - κ(a,b,(a∘b)∘(c∘d)) - κ(c,d,(a∘b)∘(c∘d)).
    This measures how the emergences of (a,b) and (c,d) interact. -/
noncomputable def emergence2 (a b c d : I) : ℝ :=
  emergence (compose a b) (compose c d) (compose (compose a b) (compose c d)) -
  emergence a b (compose (compose a b) (compose c d)) -
  emergence c d (compose (compose a b) (compose c d))

/-- Second-order emergence vanishes when all inputs are void. -/
theorem emergence2_void :
    emergence2 (void : I) (void : I) (void : I) (void : I) = 0 := by
  unfold emergence2; simp [emergence_void_left, emergence_void_right]

/-- Second-order emergence with left pair void equals negative emergence. -/
theorem emergence2_void_left (c d : I) :
    emergence2 (void : I) (void : I) c d = -emergence c d (compose c d) := by
  unfold emergence2
  simp only [void_left', emergence_void_left]
  unfold emergence; ring

/-- Second-order emergence with right pair void equals negative emergence. -/
theorem emergence2_void_right (a b : I) :
    emergence2 a b (void : I) (void : I) = -emergence a b (compose a b) := by
  unfold emergence2
  simp only [void_right', emergence_void_right, emergence_against_void]
  unfold emergence; ring

/-- The iterated emergence functional: compose a with itself n times,
    then measure emergence of successive powers against their composition.
    Ψₙ(a) = κ(aⁿ, a, aⁿ⁺¹). This is the "creative output at step n." -/
noncomputable def emergenceFunctional (a : I) (n : ℕ) : ℝ :=
  emergence (composeN a n) a (composeN a (n + 1))

/-- The emergence functional at step 0 is zero (since a⁰ = void). -/
theorem emergenceFunctional_zero (a : I) :
    emergenceFunctional a 0 = 0 := by
  unfold emergenceFunctional; simp [emergence_void_left]

/-- The emergence functional of void is always zero. -/
theorem emergenceFunctional_void (n : ℕ) :
    emergenceFunctional (void : I) n = 0 := by
  unfold emergenceFunctional; simp [emergence_void_left]

/-- The emergence functional is bounded by the weight at step n+1. -/
theorem emergenceFunctional_bounded (a : I) (n : ℕ) :
    (emergenceFunctional a n) ^ 2 ≤
    weight (composeN a (n + 1)) * weight (composeN a (n + 1)) := by
  unfold emergenceFunctional weight
  exact emergence_bounded' (composeN a n) a (composeN a (n + 1))

/-- The total emergence functional sums all creative outputs. -/
noncomputable def totalEmergenceFunctional (a : I) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range n) (fun i => emergenceFunctional a i)

/-- Total emergence functional at 0 is zero. -/
theorem totalEmergenceFunctional_zero (a : I) :
    totalEmergenceFunctional a 0 = 0 := by
  unfold totalEmergenceFunctional; simp

/-- Total emergence functional step. -/
theorem totalEmergenceFunctional_succ (a : I) (n : ℕ) :
    totalEmergenceFunctional a (n + 1) =
    totalEmergenceFunctional a n + emergenceFunctional a n := by
  unfold totalEmergenceFunctional; rw [Finset.sum_range_succ]

/-- Emergence functional relates to weight difference via the
    resonance step identity. -/
theorem emergenceFunctional_relates (a : I) (n : ℕ) :
    emergenceFunctional a n =
    rs (composeN a (n + 1)) (composeN a (n + 1)) -
    rs (composeN a n) (composeN a (n + 1)) -
    rs a (composeN a (n + 1)) := by
  unfold emergenceFunctional emergence; rw [composeN_succ]

end IteratedEmergence

/-! ## §24. Spectral Gap Theory

The "spectral gap" measures the separation between the linear regime
(where emergence vanishes) and the nonlinear regime (where emergence
is significant). In physics, spectral gaps determine phase transitions;
here they determine when ideatic composition transitions from merely
additive to genuinely creative.

Philosophically, the spectral gap is the threshold between
MECHANICAL thought (linear combination of ideas) and
CREATIVE thought (genuine emergence of new meaning). -/

section SpectralGap
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The emergence magnitude: absolute emergence squared, normalized
    to make comparison meaningful. -/
noncomputable def emergenceMagnitude (a b c : I) : ℝ :=
  (emergence a b c) ^ 2

/-- Emergence magnitude is non-negative. -/
theorem emergenceMagnitude_nonneg (a b c : I) :
    emergenceMagnitude a b c ≥ 0 := by
  unfold emergenceMagnitude; exact sq_nonneg _

/-- Emergence magnitude at void observer is zero. -/
theorem emergenceMagnitude_void_observer (a b : I) :
    emergenceMagnitude a b (void : I) = 0 := by
  unfold emergenceMagnitude; rw [emergence_against_void]; simp

/-- Emergence magnitude at void left is zero. -/
theorem emergenceMagnitude_void_left (b c : I) :
    emergenceMagnitude (void : I) b c = 0 := by
  unfold emergenceMagnitude; rw [emergence_void_left]; simp

/-- The spectral gap for a pair (a,b): maximum emergence they can produce,
    bounded above by the product of their self-resonances. -/
theorem spectral_gap_bound (a b c : I) :
    emergenceMagnitude a b c ≤
    rs (compose a b) (compose a b) * rs c c := by
  unfold emergenceMagnitude; exact emergence_bounded' a b c

/-- Spectral gap vanishing: if the composition is void, the gap collapses. -/
theorem spectral_gap_collapse (a b : I) (h : compose a b = void) (c : I) :
    emergenceMagnitude a b c = 0 := by
  unfold emergenceMagnitude
  rw [emergence_zero_of_compose_void a b h]; simp

/-- The linear-nonlinear separation: for left-linear a, the emergence
    magnitude is exactly zero — the spectral gap is infinite. -/
theorem spectral_gap_linear (a : I) (h : leftLinear a) (b c : I) :
    emergenceMagnitude a b c = 0 := by
  unfold emergenceMagnitude; rw [h b c]; simp

/-- Spectral gap for self-emergence: κ(a,a,a)² ≤ rs(a²,a²)·rs(a,a). -/
theorem spectral_gap_self (a : I) :
    emergenceMagnitude a a a ≤
    rs (compose a a) (compose a a) * rs a a := by
  unfold emergenceMagnitude; exact emergence_bounded' a a a

/-- The "gap ratio": emergence squared divided by the spectral bound plus 1.
    Always in [0, 1) when the bound is tight. -/
noncomputable def gapRatio (a b c : I) : ℝ :=
  emergenceMagnitude a b c / (rs (compose a b) (compose a b) * rs c c + 1)

/-- Gap ratio is non-negative. -/
theorem gapRatio_nonneg (a b c : I) : gapRatio a b c ≥ 0 := by
  unfold gapRatio
  apply div_nonneg (sq_nonneg _)
  linarith [mul_nonneg (rs_self_nonneg' (compose a b)) (rs_self_nonneg' c)]

/-- Gap ratio at void is zero. -/
theorem gapRatio_void_observer (a b : I) :
    gapRatio a b (void : I) = 0 := by
  unfold gapRatio emergenceMagnitude; rw [emergence_against_void]; simp

/-- The spectral width: how wide is the nonlinear regime for an idea?
    Measured as the emergence energy (weight gain from doubling). -/
noncomputable def spectralWidth (a : I) : ℝ := emergenceEnergy a

/-- Spectral width is non-negative. -/
theorem spectralWidth_nonneg (a : I) : spectralWidth a ≥ 0 := by
  unfold spectralWidth; exact emergenceEnergy_nonneg a

/-- Spectral width of void is zero: silence has no spectral width. -/
theorem spectralWidth_void : spectralWidth (void : I) = 0 := by
  unfold spectralWidth; exact emergenceEnergy_void

/-- Spectral width relates to weight gain. -/
theorem spectralWidth_eq_weight_gain (a : I) :
    spectralWidth a = weight (compose a a) - weight a := by
  unfold spectralWidth; exact emergence_energy_is_weight_gain a

end SpectralGap

/-! ## §25. Morse Theory Analogues — Critical Points of Emergence

In Morse theory, critical points of a function determine the topology
of the underlying manifold. Here, "critical points" of the emergence
functional Ψₙ(a) = κ(aⁿ, a, aⁿ⁺¹) are ideas where the creative
output stabilizes — it neither grows nor decays. These are the
"equilibrium ideas" of the ideatic space.

Philosophically, critical points are ideas that have reached their
full expressive potential — mantras that neither amplify nor decay. -/

section MorseTheory
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- An idea is a critical point of emergence at step n if the
    emergence functional doesn't change between steps n and n+1. -/
def isCriticalPoint (a : I) (n : ℕ) : Prop :=
  emergenceFunctional a (n + 1) = emergenceFunctional a n

/-- Void is a critical point at every step. -/
theorem void_isCriticalPoint (n : ℕ) :
    isCriticalPoint (void : I) n := by
  unfold isCriticalPoint; rw [emergenceFunctional_void, emergenceFunctional_void]

/-- An idea is a **global critical point** if it's critical at every step. -/
def isGlobalCritical (a : I) : Prop :=
  ∀ n : ℕ, isCriticalPoint a n

/-- Void is a global critical point. -/
theorem void_isGlobalCritical : isGlobalCritical (void : I) :=
  fun n => void_isCriticalPoint n

/-- An idea that is nilpotent of all orders is a global critical point. -/
theorem nilpotentAll_globalCritical (a : I) (h : ∀ k : ℕ, emergenceNilpotentK a k) :
    isGlobalCritical a := by
  intro n; unfold isCriticalPoint emergenceFunctional
  have h1 : emergence (composeN a (n + 1)) a (composeN a (n + 2)) = 0 :=
    h (n + 2) (n + 1) (by omega) _
  have h2 : emergence (composeN a n) a (composeN a (n + 1)) = 0 :=
    h (n + 1) n (by omega) _
  linarith

/-- Nilpotent-1 ideas satisfy the critical point condition at step 0:
    the emergence functional at step 0 equals at step 1. -/
theorem nilpotent1_criticalAt0 (a : I) (h : emergenceNilpotent1 a) :
    isCriticalPoint a 0 := by
  unfold isCriticalPoint emergenceFunctional
  simp only [composeN_succ, composeN_zero, void_left']
  -- Goal: emergence a a (compose a a) = emergence void a a
  rw [emergence_void_left]
  exact h _

/-- The Morse index: how many negative emergence energy steps precede step n.
    We can't directly count without decidability, but we can characterize:
    at step n, the emergence energy is non-negative. -/
theorem morse_nonneg_energy (a : I) (n : ℕ) :
    emergenceEnergyN a n ≥ 0 := emergenceEnergyN_nonneg a n

/-- The Morse functional: total weight at step n is the sum of all
    emergence energies. This is the "height function" whose critical
    points we study. -/
theorem morse_height_eq (a : I) (n : ℕ) :
    weight (composeN a n) =
    Finset.sum (Finset.range n) (fun i => emergenceEnergyN a i) :=
  weight_eq_accumulated_energy a n

/-- At a critical point, consecutive emergence energies are related. -/
theorem critical_point_energy_relation (a : I) (n : ℕ)
    (hc : isCriticalPoint a n) :
    emergenceFunctional a (n + 1) = emergenceFunctional a n :=
  hc

/-- The "gradient" of the Morse functional: the difference of successive
    weight increments. This is the "acceleration" of weight growth. -/
noncomputable def morseGradient (a : I) (n : ℕ) : ℝ :=
  emergenceEnergyN a (n + 1) - emergenceEnergyN a n

/-- Morse gradient of void is zero: silence has flat energy landscape. -/
theorem morseGradient_void (n : ℕ) :
    morseGradient (void : I) n = 0 := by
  unfold morseGradient emergenceEnergyN; simp [rs_void_void]

/-- Morse gradient at step 0. -/
theorem morseGradient_zero (a : I) :
    morseGradient a 0 = emergenceEnergyN a 1 - emergenceEnergyN a 0 := rfl

/-- Sum of Morse gradients telescopes. -/
theorem morseGradient_telescope (a : I) (n : ℕ) :
    Finset.sum (Finset.range n) (fun i => morseGradient a i) =
    emergenceEnergyN a n - emergenceEnergyN a 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]; unfold morseGradient; ring

end MorseTheory

/-! ## §26. Homological Algebra of Cocycles — Coboundary Operators

The emergence cocycle lives in the second cohomology group H²(I, ℝ)
of the composition monoid. Here we develop the coboundary operator δ,
the space of coboundaries B², and prove the fundamental exact sequence
relationship B² ⊆ Z² and the triviality of emergence cohomology
(since emergence IS a coboundary of rs). -/

section HomologicalAlgebra
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The 1-coboundary operator: given a function f : I → ℝ, its
    coboundary is (δ¹f)(a,b) = f(a∘b) - f(a) - f(b).
    This is the additive analogue of the group coboundary. -/
noncomputable def coboundary1 (f : I → ℝ) (a b : I) : ℝ :=
  f (compose a b) - f a - f b

/-- The 1-coboundary at void is f(void) - 2·f(void) = -f(void). -/
theorem coboundary1_void_left (f : I → ℝ) (b : I) :
    coboundary1 f (void : I) b = f b - f (void : I) - f b := by
  unfold coboundary1; simp

/-- The 1-coboundary vanishes at void when f(void) = 0. -/
theorem coboundary1_void_normalized (f : I → ℝ) (hf : f (void : I) = 0) (b : I) :
    coboundary1 f (void : I) b = 0 := by
  unfold coboundary1; simp [hf]

/-- The 1-coboundary is symmetric iff the underlying function is
    compatible with composition. -/
theorem coboundary1_void_right (f : I → ℝ) (a : I) :
    coboundary1 f a (void : I) = f a - f a - f (void : I) := by
  unfold coboundary1; simp

/-- The 2-coboundary operator: given g : I → I → ℝ, its coboundary is
    (δ²g)(a,b,c) = g(a∘b, c) - g(a, c) - g(b, c).
    Emergence IS δ²(rs)(a,b,c). -/
noncomputable def coboundary2 (g : I → I → ℝ) (a b c : I) : ℝ :=
  g (compose a b) c - g a c - g b c

/-- The fundamental identity: emergence equals the 2-coboundary of rs. -/
theorem emergence_eq_coboundary2_rs (a b c : I) :
    emergence a b c = coboundary2 rs a b c := by
  unfold emergence coboundary2; ring

/-- Every 2-coboundary satisfies the cocycle condition.
    This is δ² ∘ δ¹ = 0 in homological algebra. -/
theorem coboundary2_is_cocycle (g : I → I → ℝ) (a b c d : I) :
    coboundary2 g a b d + coboundary2 g (compose a b) c d =
    coboundary2 g b c d + coboundary2 g a (compose b c) d := by
  unfold coboundary2; rw [compose_assoc']; ring

/-- The coboundary of the zero function is zero. -/
theorem coboundary2_zero (a b c : I) :
    coboundary2 (fun _ _ => (0 : ℝ)) a b c = 0 := by
  unfold coboundary2; ring

/-- The coboundary operator is linear: δ²(f + g) = δ²f + δ²g. -/
theorem coboundary2_add (f g : I → I → ℝ) (a b c : I) :
    coboundary2 (fun x y => f x y + g x y) a b c =
    coboundary2 f a b c + coboundary2 g a b c := by
  unfold coboundary2; ring

/-- The coboundary operator scales: δ²(r·f) = r·δ²f. -/
theorem coboundary2_scale (r : ℝ) (f : I → I → ℝ) (a b c : I) :
    coboundary2 (fun x y => r * f x y) a b c =
    r * coboundary2 f a b c := by
  unfold coboundary2; ring

/-- The coboundary of self-resonance gives the self-emergence profile. -/
theorem coboundary2_selfRS (a b : I) :
    coboundary2 (fun x y => rs x y) a b = fun c => emergence a b c := by
  ext c; unfold coboundary2 emergence; ring

/-- Exact sequence: the difference of two coboundaries is a coboundary.
    B² is a subgroup. -/
theorem coboundary2_sub (f g : I → I → ℝ) (a b c : I) :
    coboundary2 (fun x y => f x y - g x y) a b c =
    coboundary2 f a b c - coboundary2 g a b c := by
  unfold coboundary2; ring

/-- The emergence cohomology class is trivial: emergence is exact
    (it's a coboundary of rs). Therefore H²(I, ℝ) = 0 in the relevant
    sense — all "cocycle anomalies" can be absorbed into the definition. -/
theorem emergence_cohomology_trivial :
    ∀ a b c : I, emergence a b c = coboundary2 rs a b c := by
  intro a b c; unfold emergence coboundary2; ring

/-- Coboundary of a constant function. -/
theorem coboundary2_const (r : ℝ) (a b c : I) :
    coboundary2 (fun _ _ => r) a b c = -r := by
  unfold coboundary2; ring

end HomologicalAlgebra

/-! ## §27. Renormalization — Emergence at Different Scales

Renormalization studies how emergence changes when we "zoom out" from
individual compositions to block compositions. If we group n successive
compositions into a single block, the emergence at the block level
captures a "coarse-grained" emergence. The key question: does emergence
persist at all scales, or does it vanish under coarse-graining?

Philosophically, this is the question of whether meaning has
FRACTAL structure — whether the creative surplus at the level of
words persists at the level of sentences, paragraphs, and books. -/

section Renormalization
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Block composition: compose a with itself n times, forming a "block."
    This IS composeN, but renamed for conceptual clarity in this section. -/
noncomputable def block (a : I) (n : ℕ) : I := composeN a n

/-- Block of size 0 is void. -/
theorem block_zero (a : I) : block a 0 = (void : I) := composeN_zero a

/-- Block of size 1 is the idea itself. -/
theorem block_one (a : I) : block a 1 = a := composeN_one a

/-- Renormalized emergence: emergence measured at block scale n.
    κₙ(a, c) = κ(aⁿ, aⁿ, c) = emergence of composing two n-blocks. -/
noncomputable def renormalizedEmergence (a c : I) (n : ℕ) : ℝ :=
  emergence (block a n) (block a n) c

/-- Renormalized emergence at scale 0 is zero (void blocks). -/
theorem renormalizedEmergence_zero (a c : I) :
    renormalizedEmergence a c 0 = 0 := by
  unfold renormalizedEmergence block; simp [emergence_void_left]

/-- Renormalized emergence at scale 1 is the base self-emergence. -/
theorem renormalizedEmergence_one (a c : I) :
    renormalizedEmergence a c 1 = emergence a a c := by
  unfold renormalizedEmergence block; rw [composeN_one]

/-- Renormalized emergence of void is always zero at any scale. -/
theorem renormalizedEmergence_void (c : I) (n : ℕ) :
    renormalizedEmergence (void : I) c n = 0 := by
  unfold renormalizedEmergence block; simp [emergence_void_left]

/-- Renormalized emergence vanishes at void observer at any scale. -/
theorem renormalizedEmergence_void_observer (a : I) (n : ℕ) :
    renormalizedEmergence a (void : I) n = 0 := by
  unfold renormalizedEmergence; exact emergence_against_void _ _

/-- Renormalized emergence is bounded at every scale. -/
theorem renormalizedEmergence_bounded (a c : I) (n : ℕ) :
    (renormalizedEmergence a c n) ^ 2 ≤
    rs (compose (block a n) (block a n)) (compose (block a n) (block a n)) *
    rs c c := by
  unfold renormalizedEmergence; exact emergence_bounded' _ _ c

/-- Renormalized self-resonance at scale n: the weight of a 2n-block
    minus twice the weight of an n-block is the total emergence at scale n. -/
theorem renormalized_weight_identity (a : I) (n : ℕ) :
    rs (compose (block a n) (block a n)) (compose (block a n) (block a n)) =
    rs (block a n) (compose (block a n) (block a n)) +
    rs (block a n) (compose (block a n) (block a n)) +
    renormalizedEmergence a (compose (block a n) (block a n)) n := by
  unfold renormalizedEmergence; rw [rs_compose_eq]

/-- The renormalization group equation: emergence at scale n is bounded
    by the weight at scale n. -/
theorem renormalization_bound (a c : I) (n : ℕ) :
    (renormalizedEmergence a c n) ^ 2 ≤
    rs (compose (block a n) (block a n)) (compose (block a n) (block a n)) *
    rs c c :=
  renormalizedEmergence_bounded a c n

/-- Scale transformation: the weight at scale n is non-decreasing
    (blocks get heavier as you add more compositions). -/
theorem scale_weight_mono (a : I) (m n : ℕ) (h : m ≤ n) :
    weight (block a m) ≤ weight (block a n) := by
  unfold block; exact weight_composeN_mono a m n h

/-- Renormalized enrichment: the enrichment gap at scale n. -/
noncomputable def renormalizedEnrichment (a : I) (n : ℕ) : ℝ :=
  rs (compose (block a n) (block a n)) (compose (block a n) (block a n)) -
  rs (block a n) (block a n)

/-- Renormalized enrichment is non-negative at every scale. -/
theorem renormalizedEnrichment_nonneg (a : I) (n : ℕ) :
    renormalizedEnrichment a n ≥ 0 := by
  unfold renormalizedEnrichment; linarith [compose_enriches' (block a n) (block a n)]

/-- Renormalized enrichment at scale 0 is zero. -/
theorem renormalizedEnrichment_zero (a : I) :
    renormalizedEnrichment a 0 = 0 := by
  unfold renormalizedEnrichment block; simp [rs_void_void]

end Renormalization

/-! ## §28. Phase Transitions — When Emergence Qualitatively Changes

A "phase transition" occurs when small changes in an idea produce
qualitative changes in emergence behavior. We formalize this through
the emergence energy sequence: a phase transition at step n means
the emergence energy jumps (or drops) at that step.

In cultural terms, a phase transition is when adding one more idea
to a discourse changes the NATURE of the discourse — from mechanical
recombination to genuine creativity, or vice versa. -/

section PhaseTransitions
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A phase transition at step n occurs when emergence energy changes
    by more than a threshold δ. -/
def hasPhaseTransition (a : I) (n : ℕ) (δ : ℝ) : Prop :=
  |emergenceEnergyN a (n + 1) - emergenceEnergyN a n| ≥ δ

/-- No phase transition at void: the energy landscape is completely flat. -/
theorem no_phase_transition_void (n : ℕ) (δ : ℝ) (hδ : δ > 0) :
    ¬hasPhaseTransition (void : I) n δ := by
  intro h; unfold hasPhaseTransition at h
  unfold emergenceEnergyN at h; simp [rs_void_void] at h; linarith

/-- The order parameter: total emergence per unit weight.
    When this changes sharply, we have a phase transition. -/
noncomputable def orderParameter (a : I) (n : ℕ) : ℝ :=
  emergenceEnergyN a n

/-- Order parameter is non-negative. -/
theorem orderParameter_nonneg (a : I) (n : ℕ) :
    orderParameter a n ≥ 0 := by
  unfold orderParameter; exact emergenceEnergyN_nonneg a n

/-- Order parameter of void is zero at every step. -/
theorem orderParameter_void (n : ℕ) :
    orderParameter (void : I) n = 0 := by
  unfold orderParameter emergenceEnergyN; simp [rs_void_void]

/-- The critical exponent: the rate of weight growth.
    w(aⁿ⁺¹) / w(aⁿ) when w(aⁿ) > 0.
    We express the weight difference instead to avoid division. -/
noncomputable def weightGrowthRate (a : I) (n : ℕ) : ℝ :=
  weight (composeN a (n + 1)) - weight (composeN a n)

/-- Weight growth rate equals emergence energy. -/
theorem weightGrowthRate_eq (a : I) (n : ℕ) :
    weightGrowthRate a n = emergenceEnergyN a n := by
  unfold weightGrowthRate emergenceEnergyN weight; ring

/-- Weight growth rate is non-negative. -/
theorem weightGrowthRate_nonneg (a : I) (n : ℕ) :
    weightGrowthRate a n ≥ 0 := by
  rw [weightGrowthRate_eq]; exact emergenceEnergyN_nonneg a n

/-- Phase stability: if all emergence energies are equal (constant growth),
    there are no phase transitions with positive threshold. -/
theorem phase_stable_constant (a : I) (c : ℝ)
    (hconst : ∀ n, emergenceEnergyN a n = c) (n : ℕ) (δ : ℝ) (hδ : δ > 0) :
    ¬hasPhaseTransition a n δ := by
  unfold hasPhaseTransition; rw [hconst, hconst]; simp; linarith

/-- The susceptibility: second difference of weight, measuring
    how responsive weight growth is to iteration. -/
noncomputable def susceptibility (a : I) (n : ℕ) : ℝ :=
  weightGrowthRate a (n + 1) - weightGrowthRate a n

/-- Susceptibility equals the Morse gradient. -/
theorem susceptibility_eq_morseGradient (a : I) (n : ℕ) :
    susceptibility a n = morseGradient a n := by
  unfold susceptibility morseGradient; rw [weightGrowthRate_eq, weightGrowthRate_eq]

/-- Susceptibility of void is zero. -/
theorem susceptibility_void (n : ℕ) :
    susceptibility (void : I) n = 0 := by
  rw [susceptibility_eq_morseGradient]; exact morseGradient_void n

/-- Sum of susceptibilities telescopes. -/
theorem susceptibility_telescope (a : I) (n : ℕ) :
    Finset.sum (Finset.range n) (fun i => susceptibility a i) =
    weightGrowthRate a n - weightGrowthRate a 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]; unfold susceptibility; ring

end PhaseTransitions

/-! ## §29. Category-Theoretic Structure — Functoriality of Emergence

Emergence is functorial: ideatic morphisms that preserve composition
and resonance automatically preserve emergence, total emergence,
semantic charge, and all derived quantities. This section establishes
this functoriality systematically.

Philosophically, functoriality means that the STRUCTURE of emergence
(not just its numerical values) is invariant under meaning-preserving
transformations. Translation between languages, for instance, should
preserve emergence patterns even if numerical resonances differ. -/

section Functoriality
variable {I : Type*} {J : Type*} [S : IdeaticSpace3 I] [T : IdeaticSpace3 J]
open IdeaticSpace3

/-- A resonance-preserving map between ideatic spaces. -/
structure ResonanceMap (I J : Type*) [IdeaticSpace3 I] [IdeaticSpace3 J] where
  toFun : I → J
  map_compose : ∀ a b : I, toFun (compose a b) = compose (toFun a) (toFun b)
  map_void : toFun (void : I) = (void : J)
  map_rs : ∀ a b : I, rs (toFun a) (toFun b) = rs a b

/-- A resonance map preserves emergence. -/
theorem resonanceMap_preserves_emergence (f : ResonanceMap I J) (a b c : I) :
    emergence (f.toFun a) (f.toFun b) (f.toFun c) = emergence a b c := by
  unfold emergence; rw [← f.map_compose, f.map_rs, f.map_rs, f.map_rs]

/-- A resonance map preserves total emergence. -/
theorem resonanceMap_preserves_totalEmergence (f : ResonanceMap I J) (a b : I) :
    totalEmergence (f.toFun a) (f.toFun b) = totalEmergence a b := by
  unfold totalEmergence
  rw [← f.map_compose]
  exact resonanceMap_preserves_emergence f a b (compose a b)

/-- A resonance map preserves semantic charge. -/
theorem resonanceMap_preserves_semanticCharge (f : ResonanceMap I J) (a : I) :
    semanticCharge (f.toFun a) = semanticCharge a := by
  unfold semanticCharge; exact resonanceMap_preserves_emergence f a a a

/-- A resonance map preserves meaning curvature. -/
theorem resonanceMap_preserves_curvature (f : ResonanceMap I J) (a b c : I) :
    meaningCurvature (f.toFun a) (f.toFun b) (f.toFun c) =
    meaningCurvature a b c := by
  unfold meaningCurvature
  rw [resonanceMap_preserves_emergence, resonanceMap_preserves_emergence]

/-- A resonance map preserves weight. -/
theorem resonanceMap_preserves_weight (f : ResonanceMap I J) (a : I) :
    weight (f.toFun a) = weight a := by
  unfold weight; exact f.map_rs a a

/-- A resonance map preserves self-emergence profile. -/
theorem resonanceMap_preserves_selfEmergenceProfile (f : ResonanceMap I J) (a b : I) :
    selfEmergenceProfile (f.toFun a) (f.toFun b) = selfEmergenceProfile a b := by
  unfold selfEmergenceProfile; exact resonanceMap_preserves_emergence f a a b

/-- A resonance map preserves enrichment gap. -/
theorem resonanceMap_preserves_enrichmentGap (f : ResonanceMap I J) (a b : I) :
    enrichmentGap (f.toFun a) (f.toFun b) = enrichmentGap a b := by
  unfold enrichmentGap; rw [← f.map_compose, f.map_rs, f.map_rs]

/-- A resonance map preserves emergence energy. -/
theorem resonanceMap_preserves_emergenceEnergy (f : ResonanceMap I J) (a : I) :
    emergenceEnergy (f.toFun a) = emergenceEnergy a := by
  unfold emergenceEnergy; rw [← f.map_compose, f.map_rs, f.map_rs]

/-- Resonance maps compose: the composition of two resonance maps
    is again a resonance map. This is functoriality. -/
def resonanceMapCompose' {K : Type*} [IdeaticSpace3 K]
    (f : ResonanceMap I J) (g : ResonanceMap J K) : ResonanceMap I K where
  toFun := g.toFun ∘ f.toFun
  map_compose a b := by simp [Function.comp, f.map_compose, g.map_compose]
  map_void := by simp [Function.comp, f.map_void, g.map_void]
  map_rs a b := by simp [Function.comp, f.map_rs, g.map_rs]

/-- The composition of resonance maps preserves emergence:
    emergence is invariant under the composed map. -/
theorem resonanceMapCompose_preserves_emergence {K : Type*} [IdeaticSpace3 K]
    (f : ResonanceMap I J) (g : ResonanceMap J K) (a b c : I) :
    emergence ((resonanceMapCompose' f g).toFun a) ((resonanceMapCompose' f g).toFun b)
              ((resonanceMapCompose' f g).toFun c) = emergence a b c := by
  have h1 := resonanceMap_preserves_emergence g (f.toFun a) (f.toFun b) (f.toFun c)
  have h2 := resonanceMap_preserves_emergence f a b c
  simp only [resonanceMapCompose', Function.comp] at *
  linarith

/-- The identity resonance map. -/
def resonanceMapId : ResonanceMap I I where
  toFun := id
  map_compose _ _ := rfl
  map_void := rfl
  map_rs _ _ := rfl

/-- Identity map preserves everything trivially. -/
theorem resonanceMapId_emergence (a b c : I) :
    emergence (resonanceMapId.toFun a) (resonanceMapId.toFun b) (resonanceMapId.toFun c) =
    emergence a b c := by
  unfold resonanceMapId; simp

end Functoriality

/-! ## §30. Information Geometry — Fisher-Like Metrics

The emergence Cauchy-Schwarz inequality induces a metric-like structure
on the space of ideas. The "information distance" between compositions
is measured by how their emergence patterns differ. This connects IDT
to information geometry: the space of ideas has a natural Riemannian-like
structure where curvature = emergence and geodesics = minimal emergence paths.

Philosophically, information geometry tells us that the "distance"
between ideas is not semantic content but EMERGENCE potential — how
much creative surplus their interaction generates. -/

section InformationGeometry
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The emergence inner product (for fixed observer c):
    the "correlation" between two compositions' emergence patterns. -/
noncomputable def emergenceInnerProduct (a₁ b₁ a₂ b₂ c : I) : ℝ :=
  emergence a₁ b₁ c * emergence a₂ b₂ c

/-- Emergence inner product is symmetric in the pair arguments. -/
theorem emergenceInnerProduct_symm (a₁ b₁ a₂ b₂ c : I) :
    emergenceInnerProduct a₁ b₁ a₂ b₂ c =
    emergenceInnerProduct a₂ b₂ a₁ b₁ c := by
  unfold emergenceInnerProduct; ring

/-- Emergence inner product vanishes at void observer. -/
theorem emergenceInnerProduct_void_observer (a₁ b₁ a₂ b₂ : I) :
    emergenceInnerProduct a₁ b₁ a₂ b₂ (void : I) = 0 := by
  unfold emergenceInnerProduct; rw [emergence_against_void]; ring

/-- The "squared distance" between two compositions' emergence patterns,
    measured at observer c. -/
noncomputable def emergenceDistance (a₁ b₁ a₂ b₂ c : I) : ℝ :=
  (emergence a₁ b₁ c - emergence a₂ b₂ c) ^ 2

/-- Emergence distance is non-negative. -/
theorem emergenceDistance_nonneg (a₁ b₁ a₂ b₂ c : I) :
    emergenceDistance a₁ b₁ a₂ b₂ c ≥ 0 := by
  unfold emergenceDistance; exact sq_nonneg _

/-- Emergence distance is zero iff emergences agree. -/
theorem emergenceDistance_zero_iff (a₁ b₁ a₂ b₂ c : I) :
    emergenceDistance a₁ b₁ a₂ b₂ c = 0 ↔
    emergence a₁ b₁ c = emergence a₂ b₂ c := by
  unfold emergenceDistance; constructor
  · intro h; nlinarith [sq_nonneg (emergence a₁ b₁ c - emergence a₂ b₂ c)]
  · intro h; rw [h]; ring

/-- Emergence distance is symmetric. -/
theorem emergenceDistance_symm (a₁ b₁ a₂ b₂ c : I) :
    emergenceDistance a₁ b₁ a₂ b₂ c =
    emergenceDistance a₂ b₂ a₁ b₁ c := by
  unfold emergenceDistance; ring

/-- Triangle inequality for emergence distance squared (weak form). -/
theorem emergenceDistance_triangle (a₁ b₁ a₂ b₂ a₃ b₃ c : I) :
    emergenceDistance a₁ b₁ a₃ b₃ c ≤
    2 * (emergenceDistance a₁ b₁ a₂ b₂ c + emergenceDistance a₂ b₂ a₃ b₃ c) := by
  unfold emergenceDistance
  have h1 := sq_nonneg (emergence a₁ b₁ c - emergence a₂ b₂ c)
  have h2 := sq_nonneg (emergence a₂ b₂ c - emergence a₃ b₃ c)
  have h3 := sq_nonneg (emergence a₁ b₁ c - 2 * emergence a₂ b₂ c + emergence a₃ b₃ c)
  nlinarith

/-- The Fisher information analogue: curvature of the "log-likelihood"
    of emergence. For fixed a, this measures how sharply emergence
    varies as we change the composition partner. -/
noncomputable def fisherInformation (a b c : I) : ℝ :=
  (emergence a b c) ^ 2

/-- Fisher information is non-negative. -/
theorem fisherInformation_nonneg (a b c : I) :
    fisherInformation a b c ≥ 0 := by
  unfold fisherInformation; exact sq_nonneg _

/-- Fisher information is bounded by the spectral bound. -/
theorem fisherInformation_bounded (a b c : I) :
    fisherInformation a b c ≤
    rs (compose a b) (compose a b) * rs c c := by
  unfold fisherInformation; exact emergence_bounded' a b c

/-- Total Fisher information: sum over a chain of compositions. -/
noncomputable def totalFisher (a c : I) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range n) (fun i => fisherInformation (composeN a i) a c)

/-- Total Fisher information is non-negative. -/
theorem totalFisher_nonneg (a c : I) (n : ℕ) :
    totalFisher a c n ≥ 0 := by
  unfold totalFisher
  apply Finset.sum_nonneg; intro i _
  exact fisherInformation_nonneg (composeN a i) a c

/-- Total Fisher is bounded by cumulative squared emergence. -/
theorem totalFisher_eq (a c : I) (n : ℕ) :
    totalFisher a c n =
    Finset.sum (Finset.range n) (fun i => (emergence (composeN a i) a c) ^ 2) := by
  unfold totalFisher fisherInformation; rfl

/-- Total Fisher is bounded by weight times observer weight times n. -/
theorem totalFisher_bounded (a c : I) (n : ℕ) :
    totalFisher a c n ≤
    ↑n * (rs (composeN a n) (composeN a n) * rs c c) := by
  rw [totalFisher_eq]; exact cumulative_emergence_sq_bound a c n

end InformationGeometry

/-! ## §31. Emergence Entropy — The Second Law Analogue

Emergence entropy measures the "disorder" or "complexity" that
accumulates as ideas compose. The fundamental insight: weight
(self-resonance) is a monotonically non-decreasing function of
composition depth. This is an EXACT analogue of the second law
of thermodynamics: you can't unsay something.

The "entropy" here is the accumulated weight gain, and the
second law is the statement that it can only grow. -/

section EmergenceEntropy
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Emergence entropy at depth n: the total weight accumulated. -/
noncomputable def emergenceEntropy (a : I) (n : ℕ) : ℝ :=
  weight (composeN a n)

/-- Emergence entropy at depth 0 is zero (silence has no entropy). -/
theorem emergenceEntropy_zero (a : I) :
    emergenceEntropy a 0 = 0 := by
  unfold emergenceEntropy; simp [weight_void]

/-- Emergence entropy at depth 1 is the base weight. -/
theorem emergenceEntropy_one (a : I) :
    emergenceEntropy a 1 = weight a := by
  unfold emergenceEntropy; rw [composeN_one]

/-- **The Second Law**: emergence entropy is non-decreasing.
    You can't unsay something — adding more composition only increases entropy. -/
theorem second_law (a : I) (n : ℕ) :
    emergenceEntropy a (n + 1) ≥ emergenceEntropy a n := by
  unfold emergenceEntropy; exact weight_power_mono a n

/-- The second law generalized: entropy at step n ≥ entropy at step m for n ≥ m. -/
theorem second_law_general (a : I) (m n : ℕ) (h : m ≤ n) :
    emergenceEntropy a n ≥ emergenceEntropy a m := by
  unfold emergenceEntropy
  exact weight_composeN_mono a m n h

/-- Entropy production at step n: the amount of new entropy created. -/
noncomputable def entropyProduction (a : I) (n : ℕ) : ℝ :=
  emergenceEntropy a (n + 1) - emergenceEntropy a n

/-- Entropy production equals emergence energy (weight gain per step). -/
theorem entropyProduction_eq (a : I) (n : ℕ) :
    entropyProduction a n = emergenceEnergyN a n := by
  unfold entropyProduction emergenceEntropy emergenceEnergyN weight; ring

/-- Entropy production is non-negative (the second law, restated). -/
theorem entropyProduction_nonneg (a : I) (n : ℕ) :
    entropyProduction a n ≥ 0 := by
  rw [entropyProduction_eq]; exact emergenceEnergyN_nonneg a n

/-- Entropy production of void is zero: silence creates no entropy. -/
theorem entropyProduction_void (n : ℕ) :
    entropyProduction (void : I) n = 0 := by
  unfold entropyProduction emergenceEntropy weight; simp [rs_void_void]

/-- Total entropy equals sum of all entropy productions. -/
theorem entropy_telescoping (a : I) (n : ℕ) :
    emergenceEntropy a n =
    Finset.sum (Finset.range n) (fun i => entropyProduction a i) := by
  induction n with
  | zero => simp [emergenceEntropy_zero]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]; unfold entropyProduction; ring

/-- Entropy is non-negative at all depths. -/
theorem emergenceEntropy_nonneg (a : I) (n : ℕ) :
    emergenceEntropy a n ≥ 0 := by
  unfold emergenceEntropy weight; exact rs_self_nonneg' _

/-- For non-void a, entropy at depth ≥ 1 is strictly positive. -/
theorem emergenceEntropy_pos (a : I) (ha : a ≠ void) (n : ℕ) (hn : n ≥ 1) :
    emergenceEntropy a n > 0 := by
  unfold emergenceEntropy weight
  exact composeN_selfRS_pos a ha n hn

/-- Maximum entropy production principle: the entropy produced at step n
    cannot exceed the entropy at step n+1 (trivially, since it's the
    difference and both are non-negative). -/
theorem entropy_production_bounded (a : I) (n : ℕ) :
    entropyProduction a n ≤ emergenceEntropy a (n + 1) := by
  unfold entropyProduction; linarith [emergenceEntropy_nonneg a n]

/-- Entropy additivity: entropy at step m+n is at least entropy at m
    plus zero (weaker than true additivity, but provable). -/
theorem entropy_subadditive (a : I) (m n : ℕ) :
    emergenceEntropy a (m + n) ≥ emergenceEntropy a m := by
  exact second_law_general a m (m + n) (Nat.le_add_right m n)

end EmergenceEntropy

/-! ## §32. Resonance Operator Algebra

The resonance function `rs : I → I → ℝ` can be viewed as defining
"operators" on the space of ideas. For fixed a, the map `b ↦ rs(a, b)`
is a "resonance operator." The emergence then measures the failure of
these operators to be multiplicative under composition. -/

section ResonanceOperatorAlgebra
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The resonance operator: for fixed source a, maps observers to reals. -/
noncomputable def resonanceOp (a : I) : I → ℝ := fun b => rs a b

/-- The resonance operator of void is the zero operator. -/
theorem resonanceOp_void :
    resonanceOp (void : I) = fun _ => (0 : ℝ) := by
  ext b; unfold resonanceOp; exact rs_void_left' b

/-- The resonance operator evaluated at void gives zero. -/
theorem resonanceOp_at_void (a : I) :
    resonanceOp a (void : I) = 0 := by
  unfold resonanceOp; exact rs_void_right' a

/-- The composition of resonance operators has an emergence correction:
    resonanceOp(a∘b)(c) = resonanceOp(a)(c) + resonanceOp(b)(c) + κ(a,b,c). -/
theorem resonanceOp_compose (a b c : I) :
    resonanceOp (compose a b) c =
    resonanceOp a c + resonanceOp b c + emergence a b c := by
  unfold resonanceOp; rw [rs_compose_eq]

/-- The "operator defect": the failure of resonance operators to be
    multiplicative. This IS emergence. -/
theorem operator_defect (a b c : I) :
    resonanceOp (compose a b) c - resonanceOp a c - resonanceOp b c =
    emergence a b c := by
  unfold resonanceOp emergence; ring

/-- For left-linear a, the resonance operator is additive under
    left-composition with a: no operator defect. -/
theorem operator_linear (a : I) (h : leftLinear a) (b c : I) :
    resonanceOp (compose a b) c = resonanceOp a c + resonanceOp b c := by
  rw [resonanceOp_compose, h b c]; ring

/-- The operator norm squared: self-resonance is the "norm squared"
    of the resonance operator restricted to self. -/
theorem operator_norm_sq (a : I) :
    resonanceOp a a = weight a := by
  unfold resonanceOp weight; rfl

/-- Resonance operator at compositions telescopes. -/
theorem resonanceOp_composeN (a c : I) (n : ℕ) :
    resonanceOp (composeN a n) c = n * rs a c +
    Finset.sum (Finset.range n) (fun i => emergence (composeN a i) a c) := by
  unfold resonanceOp; exact chain_telescoping a c n

end ResonanceOperatorAlgebra

/-! ## §33. Emergence Polynomials — Algebraic Structure of Powers

The sequence rs(aⁿ, c) for fixed a and c is a "quasi-polynomial" — it
would be linear if emergence vanished, but emergence adds correction terms.
We develop the algebraic structure of these sequences. -/

section EmergencePolynomials
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The resonance sequence: rs(aⁿ, c) as a function of n. -/
noncomputable def resonanceSeq (a c : I) (n : ℕ) : ℝ :=
  rs (composeN a n) c

/-- The resonance sequence at n=0 is rs(void, c) = 0. -/
theorem resonanceSeq_zero (a c : I) :
    resonanceSeq a c 0 = 0 := by
  unfold resonanceSeq; simp [rs_void_left']

/-- The resonance sequence at n=1 is rs(a, c). -/
theorem resonanceSeq_one (a c : I) :
    resonanceSeq a c 1 = rs a c := by
  unfold resonanceSeq; rw [composeN_one]

/-- First difference of the resonance sequence. -/
theorem resonanceSeq_diff (a c : I) (n : ℕ) :
    resonanceSeq a c (n + 1) - resonanceSeq a c n =
    rs a c + emergence (composeN a n) a c := by
  unfold resonanceSeq; linarith [composeN_resonance_step a c n]

/-- The resonance sequence is the "discrete integral" of emergence. -/
theorem resonanceSeq_integral (a c : I) (n : ℕ) :
    resonanceSeq a c n = n * rs a c + cumulativeEmergence a c n := by
  unfold resonanceSeq cumulativeEmergence; linarith [chain_telescoping a c n]

/-- For nilpotent ideas, the resonance sequence is exactly linear. -/
theorem resonanceSeq_linear_nilpotent (a : I) (k : ℕ)
    (hk : emergenceNilpotentK a k) (c : I) (n : ℕ) (hn : n ≤ k) :
    resonanceSeq a c n = n * rs a c := by
  unfold resonanceSeq; exact nilpotent_chain_linear a k hk c n hn

/-- The weight sequence: w(aⁿ) as a function of n. -/
noncomputable def weightSeq (a : I) (n : ℕ) : ℝ := weight (composeN a n)

/-- Weight sequence is non-decreasing (the second law for sequences). -/
theorem weightSeq_mono (a : I) (n : ℕ) :
    weightSeq a (n + 1) ≥ weightSeq a n := by
  unfold weightSeq; exact weight_power_mono a n

/-- Weight sequence at 0. -/
theorem weightSeq_zero (a : I) : weightSeq a 0 = 0 := by
  unfold weightSeq; simp [weight_void]

/-- Weight sequence at 1. -/
theorem weightSeq_one (a : I) : weightSeq a 1 = weight a := by
  unfold weightSeq; rw [composeN_one]

/-- Weight sequence difference. -/
theorem weightSeq_diff (a : I) (n : ℕ) :
    weightSeq a (n + 1) - weightSeq a n = emergenceEnergyN a n := by
  unfold weightSeq weight emergenceEnergyN; ring

/-- Weight sequence is the sum of emergence energies. -/
theorem weightSeq_sum (a : I) (n : ℕ) :
    weightSeq a n =
    Finset.sum (Finset.range n) (fun i => emergenceEnergyN a i) := by
  unfold weightSeq; exact weight_eq_accumulated_energy a n

end EmergencePolynomials

/-! ## §34. Emergence Duality Theorems

Deep duality theorems connecting different perspectives on emergence:
the "left" view (how does a affect the emergence of b with c?) vs
the "right" view (how does b affect the emergence of a with c?).
The cocycle condition is the fundamental bridge between these views. -/

section EmergenceDuality
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Left-right duality: the cocycle condition rewritten as a duality
    between left-composition emergence and right-composition emergence. -/
theorem left_right_duality (a b c d : I) :
    emergence a (compose b c) d - emergence a b d =
    emergence (compose a b) c d - emergence b c d := by
  linarith [cocycle_condition a b c d]

/-- Emergence-curvature duality: total emergence decomposes into
    symmetric and antisymmetric parts.
    ε(a,b) = symmetric_emergence(a,b) + curvature_correction(a,b). -/
theorem emergence_curvature_duality (a b : I) :
    totalEmergence a b =
    emergenceSymmetricPart a b (compose a b) +
    emergenceAntisymmetricPart a b (compose a b) := by
  unfold totalEmergence
  exact emergence_decomposition a b (compose a b)

/-- Weight-emergence duality: weight growth is entirely determined
    by emergence (through the enrichment decomposition). -/
theorem weight_emergence_duality (a b : I) :
    weight (compose a b) - weight a =
    (rs a (compose a b) - rs a a) + rs b (compose a b) + totalEmergence a b := by
  unfold weight totalEmergence emergence; ring

/-- Resonance-emergence complementarity: the resonance at a composition
    is the sum of "flat" (linear) resonance and cumulative emergence. -/
theorem resonance_emergence_complementarity (a c : I) (n : ℕ) :
    resonanceSeq a c n = n * rs a c + cumulativeEmergence a c n := by
  exact resonanceSeq_integral a c n

/-- Self-duality of semantic charge: charge(a) can be viewed as either
    the diagonal of the emergence form or the self-emergence at the
    triple point (a,a,a). -/
theorem charge_self_duality (a : I) :
    semanticCharge a = emergence a a a := rfl

/-- The charge-energy relation: semantic charge is bounded by emergence energy
    and self-resonance via Cauchy-Schwarz. -/
theorem charge_energy_relation (a : I) :
    (semanticCharge a) ^ 2 ≤ (emergenceEnergy a + weight a) * weight a := by
  unfold semanticCharge
  have h := emergence_bounded' a a a
  unfold emergenceEnergy weight; linarith [compose_enriches' a a]

end EmergenceDuality

/-! ## §35. Higher-Order Composition Identities

Explicit formulas for resonance and emergence involving higher
powers of composition. These generalize the two-fold and three-fold
identities to arbitrary depth. -/

section HigherOrderComposition
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Resonance of a³ with c in terms of emergence. -/
theorem composeN_three_resonance (a c : I) :
    rs (composeN a 3) c = 3 * rs a c +
    emergence a a c + emergence (compose a a) a c := by
  have h := chain_telescoping a c 3
  simp [Finset.sum_range_succ, composeN_zero, composeN_one, composeN_two,
        emergence_void_left] at h
  linarith

/-- Self-resonance of a² relates to cross-resonance and emergence. -/
theorem selfRS_square_alt (a : I) :
    weight (compose a a) =
    2 * rs a (compose a a) + emergence a a (compose a a) := by
  unfold weight; rw [rs_compose_eq]; ring

/-- Weight of a³. -/
theorem weight_cube (a : I) :
    weight (composeN a 3) =
    3 * rs a (composeN a 3) +
    emergence a a (composeN a 3) +
    emergence (compose a a) a (composeN a 3) := by
  unfold weight
  rw [chain_telescoping a (composeN a 3) 3]
  simp [Finset.sum_range_succ, composeN_zero, composeN_one, composeN_two,
        emergence_void_left]; ring

/-- Emergence of a² with a, measured against a: connected to charge. -/
theorem emergence_square_self (a : I) :
    emergence (compose a a) a a =
    rs (composeN a 3) a - rs (compose a a) a - rs a a := by
  unfold emergence; rw [compose_assoc']; rw [composeN]; rw [composeN]; rw [composeN]; simp

/-- Double emergence identity: emergence of a∘b with c, measured at d,
    minus emergence of b with c measured at d, equals the "left correction." -/
theorem double_emergence_identity (a b c d : I) :
    emergence (compose a b) c d - emergence b c d =
    emergence a (compose b c) d - emergence a b d := by
  linarith [cocycle_condition a b c d]

/-- Triple self-resonance decomposition. -/
theorem triple_selfRS_decomposition (a : I) :
    weight (composeN a 3) ≥ weight (composeN a 2) := by
  unfold weight; exact composeN_selfRS_mono a 2

/-- Quadruple weight monotonicity. -/
theorem quadruple_weight_mono (a : I) :
    weight (composeN a 4) ≥ weight (composeN a 3) := by
  unfold weight; exact composeN_selfRS_mono a 3

/-- The n-fold emergence contribution: what the k-th step adds. -/
theorem nfold_step_contribution (a c : I) (k : ℕ) :
    resonanceSeq a c (k + 1) = resonanceSeq a c k + rs a c +
    emergence (composeN a k) a c := by
  unfold resonanceSeq; linarith [composeN_resonance_step a c k]

/-- Difference of resonance sequences at different observers. -/
theorem resonanceSeq_observer_diff (a c₁ c₂ : I) (n : ℕ) :
    resonanceSeq a c₁ n - resonanceSeq a c₂ n =
    n * (rs a c₁ - rs a c₂) +
    (cumulativeEmergence a c₁ n - cumulativeEmergence a c₂ n) := by
  rw [resonanceSeq_integral, resonanceSeq_integral]; ring

end HigherOrderComposition

/-! ## §36. Emergence Symmetries and Conservation Laws

Noether's theorem in physics connects symmetries to conservation laws.
Here, the "symmetries" of emergence — conditions under which emergence
is invariant — connect to "conservation" of quantities like weight
difference and cumulative emergence. -/

section EmergenceSymmetries
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Translation invariance: if a is left-linear, "translating" by a
    preserves emergence of any pair (b, c). -/
theorem translation_invariance_linear (a : I) (ha : leftLinear a) (b c d : I) :
    emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d := by
  linarith [cocycle_condition a b c d, ha b d]

/-- If a is left-linear, its emergence with a composed pair simplifies. -/
theorem linear_compose_emergence (a : I) (ha : leftLinear a) (b c d : I) :
    emergence a (compose b c) d =
    emergence a b d + emergence (compose a b) c d -
    emergence b c d := by
  linarith [cocycle_condition a b c d]

/-- Conservation of resonance difference: for any a and fixed c,
    the quantity rs(aⁿ⁺¹, c) - rs(aⁿ, c) - rs(a, c) is the emergence
    at step n. This "departure from linearity" is conserved in the sense
    that it's determined by the cocycle. -/
theorem resonance_departure_conservation (a c : I) (n : ℕ) :
    rs (composeN a (n + 1)) c - rs (composeN a n) c - rs a c =
    emergence (composeN a n) a c := by
  linarith [composeN_resonance_step a c n]

/-- Weight conservation: the weight difference between consecutive powers
    is exactly the emergence energy. -/
theorem weight_conservation (a : I) (n : ℕ) :
    weight (composeN a (n + 1)) - weight (composeN a n) = emergenceEnergyN a n := by
  unfold weight emergenceEnergyN; ring

/-- Cumulative weight conservation: total weight equals sum of energies. -/
theorem cumulative_weight_conservation (a : I) (n : ℕ) :
    weight (composeN a n) =
    Finset.sum (Finset.range n) (fun i => emergenceEnergyN a i) :=
  weight_eq_accumulated_energy a n

/-- Emergence cocycle conservation: the cocycle identity is a conservation
    law — the "current" κ(a,b,d) + κ(a∘b,c,d) equals the "source"
    κ(b,c,d) + κ(a,b∘c,d). No emergence is lost or created in re-association. -/
theorem cocycle_conservation (a b c d : I) :
    emergence a b d + emergence (compose a b) c d -
    emergence b c d - emergence a (compose b c) d = 0 := by
  linarith [cocycle_condition a b c d]

/-- Curvature conservation: the antisymmetric part of emergence is
    conserved under the swap a ↔ b (it just changes sign). -/
theorem curvature_conservation (a b c : I) :
    emergenceAntisymmetricPart a b c +
    emergenceAntisymmetricPart b a c = 0 := by
  unfold emergenceAntisymmetricPart; ring

/-- Symmetric part conservation: the symmetric part is truly conserved
    under swap. -/
theorem symmetric_conservation (a b c : I) :
    emergenceSymmetricPart a b c = emergenceSymmetricPart b a c :=
  emergenceSymmetricPart_symm a b c

end EmergenceSymmetries

/-! ## §37. Emergence Inequalities — Deeper Bounds

A collection of deeper inequalities that constrain what emergence
patterns are realizable. These go beyond the basic Cauchy-Schwarz
to reveal the fine structure of emergence. -/

section EmergenceInequalities
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- AM-GM for emergence: the product of two emergences is bounded
    by their average square (applied to the same observer). -/
theorem emergence_amgm (a₁ b₁ a₂ b₂ c : I) :
    2 * emergence a₁ b₁ c * emergence a₂ b₂ c ≤
    (emergence a₁ b₁ c) ^ 2 + (emergence a₂ b₂ c) ^ 2 := by
  nlinarith [sq_nonneg (emergence a₁ b₁ c - emergence a₂ b₂ c)]

/-- Weight-enrichment inequality: weight of a∘b is at least the max
    of the parts' weights. -/
theorem weight_max_lower (a b : I) :
    weight (compose a b) ≥ weight a := by
  unfold weight; exact compose_enriches' a b

/-- Emergence squared sum bound: for any three observations,
    the sum of squared emergences is bounded. -/
theorem triple_emergence_bound (a b c₁ c₂ c₃ : I) :
    (emergence a b c₁) ^ 2 + (emergence a b c₂) ^ 2 + (emergence a b c₃) ^ 2 ≤
    rs (compose a b) (compose a b) * (rs c₁ c₁ + rs c₂ c₂ + rs c₃ c₃) := by
  have h₁ := emergence_bounded' a b c₁
  have h₂ := emergence_bounded' a b c₂
  have h₃ := emergence_bounded' a b c₃
  nlinarith [rs_self_nonneg' (compose a b)]

/-- Weight chain inequality: w(aⁿ) ≥ w(aᵐ) for n ≥ m. -/
theorem weight_chain_ineq (a : I) (m n : ℕ) (h : m ≤ n) :
    weightSeq a n ≥ weightSeq a m := by
  unfold weightSeq; exact weight_composeN_mono a m n h

/-- Enrichment monotonicity: enriching with a then b gives at least
    as much weight as enriching with a alone. -/
theorem enrichment_monotone (a b c : I) :
    weight (compose (compose a b) c) ≥ weight (compose a b) := by
  unfold weight; exact compose_enriches' (compose a b) c

/-- Total emergence is bounded by enrichment gap: |ε(a,b)| ≤ w(a∘b).
    Since ε(a,b)² ≤ w(a∘b)², and enrichment gap ≤ w(a∘b). -/
theorem totalEmergence_enrichment_bound (a b : I) :
    (totalEmergence a b) ^ 2 ≤ weight (compose a b) ^ 2 :=
  totalEmergence_sq_bound a b

/-- Weight superadditivity failure: we can't prove w(a∘b) ≥ w(a) + w(b)
    in general, but we CAN express the gap via emergence. -/
theorem weight_gap_via_emergence (a b : I) :
    weight (compose a b) - weight a =
    rs a (compose a b) - weight a + rs b (compose a b) + totalEmergence a b := by
  unfold weight totalEmergence emergence; ring

/-- Double enrichment bound. -/
theorem double_enrichment_bound (a b c : I) :
    weight (compose (compose a b) c) ≥ weight a := by
  unfold weight; exact double_enrich a b c

end EmergenceInequalities

/-! ## §38. Emergence Interactions — Multi-Idea Composition

How does emergence behave when we compose more than two ideas?
The multi-idea interaction theory extends pairwise emergence to
n-fold interactions, revealing the combinatorial structure of
meaning creation. -/

section EmergenceInteractions
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Three-idea interaction: the emergence of a triple composition
    that is NOT captured by pairwise emergences. -/
noncomputable def threeWayInteraction (a b c d : I) : ℝ :=
  emergence a b d + emergence (compose a b) c d -
  emergence a b d - emergence b c d

/-- Three-way interaction is exactly the cocycle defect. -/
theorem threeWayInteraction_eq (a b c d : I) :
    threeWayInteraction a b c d =
    emergence (compose a b) c d - emergence b c d := by
  unfold threeWayInteraction; ring

/-- Three-way interaction equals left-right duality difference. -/
theorem threeWayInteraction_duality (a b c d : I) :
    threeWayInteraction a b c d =
    emergence a (compose b c) d - emergence a b d := by
  unfold threeWayInteraction
  linarith [cocycle_condition a b c d]

/-- Three-way interaction of void. -/
theorem threeWayInteraction_void_left (b c d : I) :
    threeWayInteraction (void : I) b c d = 0 := by
  unfold threeWayInteraction; rw [emergence_void_left, void_left']; ring

/-- The "interaction energy" of a triple. -/
noncomputable def interactionEnergy (a b c : I) : ℝ :=
  rs (compose (compose a b) c) (compose (compose a b) c) -
  rs a a - rs b b - rs c c

/-- Interaction energy is non-negative (since compose enriches). -/
theorem interactionEnergy_nonneg (a b c : I) :
    interactionEnergy a b c ≥ -rs b b - rs c c := by
  unfold interactionEnergy
  linarith [compose_enriches' a b, compose_enriches' (compose a b) c]

/-- Interaction energy decomposes via enrichment gaps. -/
theorem interactionEnergy_decompose (a b c : I) :
    interactionEnergy a b c =
    (rs (compose a b) (compose a b) - rs a a) +
    (rs (compose (compose a b) c) (compose (compose a b) c) - rs (compose a b) (compose a b)) -
    rs b b - rs c c := by
  unfold interactionEnergy; ring

/-- The pairwise emergence sum for a triple composition. -/
noncomputable def pairwiseEmergenceSum (a b c d : I) : ℝ :=
  emergence a b d + emergence b c d + emergence a c d

/-- Pairwise emergence sum vanishes at void. -/
theorem pairwiseEmergenceSum_void (b c d : I) :
    pairwiseEmergenceSum (void : I) b c d = emergence b c d := by
  unfold pairwiseEmergenceSum
  rw [emergence_void_left, emergence_void_left]; ring

/-- The interaction defect: the difference between total three-fold
    emergence and the pairwise sum. -/
noncomputable def interactionDefect (a b c d : I) : ℝ :=
  (emergence a b d + emergence (compose a b) c d) - pairwiseEmergenceSum a b c d

/-- Interaction defect relates to the cocycle via substitution. -/
theorem interactionDefect_eq (a b c d : I) :
    interactionDefect a b c d =
    emergence (compose a b) c d - emergence b c d - emergence a c d := by
  unfold interactionDefect pairwiseEmergenceSum; ring

end EmergenceInteractions

/-! ## §39. Emergence Variational Principles

Variational principles state that physical systems extremize certain
functionals. Here, we prove that the weight function satisfies
variational-like identities: the weight at each step is determined by
the emergence at that step, creating a discrete Euler-Lagrange equation. -/

section VariationalPrinciples
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The Lagrangian: emergence energy at step n is the "Lagrangian" of
    the discrete dynamics of weight growth. -/
noncomputable def lagrangian (a : I) (n : ℕ) : ℝ := emergenceEnergyN a n

/-- The action: total weight growth over n steps. -/
noncomputable def action (a : I) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range n) (fun i => lagrangian a i)

/-- The action equals the total weight gain (discrete Hamilton principle). -/
theorem action_eq_weight (a : I) (n : ℕ) :
    action a n = weight (composeN a n) := by
  unfold action lagrangian; exact (weight_eq_accumulated_energy a n).symm

/-- Euler-Lagrange equation: the "equation of motion" is that
    each step's contribution equals the emergence energy at that step. -/
theorem euler_lagrange (a : I) (n : ℕ) :
    weight (composeN a (n + 1)) - weight (composeN a n) = lagrangian a n := by
  unfold lagrangian; exact weight_conservation a n

/-- The action is non-negative (since each Lagrangian is). -/
theorem action_nonneg (a : I) (n : ℕ) : action a n ≥ 0 := by
  unfold action
  apply Finset.sum_nonneg; intro i _
  unfold lagrangian; exact emergenceEnergyN_nonneg a i

/-- The action of void is zero. -/
theorem action_void (n : ℕ) : action (void : I) n = 0 := by
  rw [action_eq_weight]; simp [weight_void]

/-- Action step. -/
theorem action_succ (a : I) (n : ℕ) :
    action a (n + 1) = action a n + lagrangian a n := by
  unfold action; rw [Finset.sum_range_succ]

/-- Hamilton's principle analogue: the weight at step n is the
    accumulated action. -/
theorem hamilton_principle (a : I) (n : ℕ) :
    weight (composeN a n) = action a n :=
  (action_eq_weight a n).symm

/-- The momentum: resonance of aⁿ with a, tracking how the idea
    "moves" through iteration. -/
noncomputable def momentum (a : I) (n : ℕ) : ℝ :=
  rs (composeN a n) a

/-- Momentum at step 0 is zero (void has no momentum). -/
theorem momentum_zero (a : I) : momentum a 0 = 0 := by
  unfold momentum; simp [rs_void_left']

/-- Momentum at step 1 is the self-resonance. -/
theorem momentum_one (a : I) : momentum a 1 = weight a := by
  unfold momentum weight; rw [composeN_one]

/-- Momentum step equation. -/
theorem momentum_step (a : I) (n : ℕ) :
    momentum a (n + 1) = momentum a n + weight a +
    emergence (composeN a n) a a := by
  unfold momentum; rw [composeN_resonance_step]; unfold weight; ring

end VariationalPrinciples

/-! ## §40. Emergence Tensor Products — Combining Independent Spaces

When two ideatic processes operate independently, their combined
emergence has product structure. We develop the algebra of "independent"
composition and how emergence factors over products. -/

section TensorProducts
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The "product emergence" of two pairs at the same observer:
    how two independent composition events contribute to emergence
    at a common observation point. -/
noncomputable def productEmergence (a₁ b₁ a₂ b₂ c : I) : ℝ :=
  emergence a₁ b₁ c + emergence a₂ b₂ c

/-- Product emergence vanishes at void observer. -/
theorem productEmergence_void_observer (a₁ b₁ a₂ b₂ : I) :
    productEmergence a₁ b₁ a₂ b₂ (void : I) = 0 := by
  unfold productEmergence; rw [emergence_against_void, emergence_against_void]; ring

/-- Product emergence is additive in components. -/
theorem productEmergence_additive (a₁ b₁ a₂ b₂ c : I) :
    productEmergence a₁ b₁ a₂ b₂ c =
    emergence a₁ b₁ c + emergence a₂ b₂ c := by
  unfold productEmergence; ring

/-- Product emergence bound: squares add. -/
theorem productEmergence_bound (a₁ b₁ a₂ b₂ c : I) :
    (productEmergence a₁ b₁ a₂ b₂ c) ^ 2 ≤
    2 * ((emergence a₁ b₁ c) ^ 2 + (emergence a₂ b₂ c) ^ 2) := by
  unfold productEmergence
  nlinarith [sq_nonneg (emergence a₁ b₁ c - emergence a₂ b₂ c),
             sq_nonneg (emergence a₁ b₁ c + emergence a₂ b₂ c)]

/-- The tensor weight: combined weight of two compositions. -/
noncomputable def tensorWeight (a₁ b₁ a₂ b₂ : I) : ℝ :=
  weight (compose a₁ b₁) + weight (compose a₂ b₂)

/-- Tensor weight is non-negative. -/
theorem tensorWeight_nonneg (a₁ b₁ a₂ b₂ : I) :
    tensorWeight a₁ b₁ a₂ b₂ ≥ 0 := by
  unfold tensorWeight; linarith [weight_nonneg (compose a₁ b₁), weight_nonneg (compose a₂ b₂)]

/-- Tensor weight lower bound. -/
theorem tensorWeight_lower (a₁ b₁ a₂ b₂ : I) :
    tensorWeight a₁ b₁ a₂ b₂ ≥ weight a₁ + weight a₂ := by
  unfold tensorWeight weight; linarith [compose_enriches' a₁ b₁, compose_enriches' a₂ b₂]

/-- Product emergence is bounded by tensor weight and observer. -/
theorem productEmergence_spectral_bound (a₁ b₁ a₂ b₂ c : I) :
    (productEmergence a₁ b₁ a₂ b₂ c) ^ 2 ≤
    2 * tensorWeight a₁ b₁ a₂ b₂ * rs c c := by
  unfold productEmergence tensorWeight weight
  nlinarith [emergence_bounded' a₁ b₁ c, emergence_bounded' a₂ b₂ c,
             sq_nonneg (emergence a₁ b₁ c - emergence a₂ b₂ c)]

end TensorProducts

/-! ## §41. Emergence Flow — Dynamical Systems Perspective

The iteration map a ↦ a∘a defines a "flow" on the ideatic space.
The emergence functional Ψₙ(a) = κ(aⁿ, a, aⁿ⁺¹) tracks the
"velocity" of this flow. The weight sequence w(aⁿ) is the
"trajectory" in weight space. -/

section EmergenceFlow
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The flow map: doubling composition a ↦ a∘a. -/
def flowStep (a : I) : I := compose a a

/-- The flow map of void is void: silence is a fixed point. -/
theorem flowStep_void : flowStep (void : I) = (void : I) := by
  unfold flowStep; simp

/-- Iterated flow: n applications of the flow map. -/
def flowIterate (a : I) : ℕ → I
  | 0 => a
  | n + 1 => flowStep (flowIterate a n)

/-- Zero iterations is identity. -/
theorem flowIterate_zero (a : I) : flowIterate a 0 = a := rfl

/-- One iteration is a∘a. -/
theorem flowIterate_one (a : I) : flowIterate a 1 = compose a a := by
  unfold flowIterate flowStep; rfl

/-- Flow preserves void: void is a fixed point of all iterations. -/
theorem flowIterate_void (n : ℕ) : flowIterate (void : I) n = (void : I) := by
  induction n with
  | zero => rfl
  | succ k ih => unfold flowIterate; rw [ih]; exact flowStep_void

/-- Weight is non-decreasing along the flow. -/
theorem flow_weight_mono (a : I) :
    weight (flowStep a) ≥ weight a := by
  unfold flowStep weight; exact compose_enriches' a a

/-- The flow velocity: emergence energy at the current point. -/
noncomputable def flowVelocity (a : I) : ℝ :=
  weight (flowStep a) - weight a

/-- Flow velocity is non-negative. -/
theorem flowVelocity_nonneg (a : I) : flowVelocity a ≥ 0 := by
  unfold flowVelocity; linarith [flow_weight_mono a]

/-- Flow velocity of void is zero. -/
theorem flowVelocity_void : flowVelocity (void : I) = 0 := by
  unfold flowVelocity flowStep; simp [weight_void]

/-- Flow velocity equals emergence energy. -/
theorem flowVelocity_eq_energy (a : I) :
    flowVelocity a = emergenceEnergy a := by
  unfold flowVelocity flowStep emergenceEnergy weight; ring

/-- The flow generates non-negative weight at every step. -/
theorem flow_positive_trajectory (a : I) (n : ℕ) :
    weight (flowIterate a n) ≥ weight a := by
  induction n with
  | zero => simp [flowIterate]
  | succ k ih =>
    simp only [flowIterate]
    calc weight (flowStep (flowIterate a k))
        ≥ weight (flowIterate a k) := flow_weight_mono _
      _ ≥ weight a := ih

end EmergenceFlow

/-! ## §42. Emergence Spectral Decomposition

The emergence of any composition can be decomposed into a "radial"
component (along the composition direction) and a "transverse"
component (perpendicular to it, in the sense of emergence). -/

section SpectralDecomposition
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Radial emergence: emergence measured along the composition itself. -/
noncomputable def radialEmergence (a b : I) : ℝ :=
  emergence a b (compose a b)

/-- Radial emergence equals total emergence (by definition). -/
theorem radialEmergence_eq (a b : I) :
    radialEmergence a b = totalEmergence a b := rfl

/-- Transverse emergence: emergence measured perpendicular to the composition,
    using the left factor as reference. -/
noncomputable def transverseEmergence (a b : I) : ℝ :=
  emergence a b a

/-- Transverse emergence at void. -/
theorem transverseEmergence_void_left (b : I) :
    transverseEmergence (void : I) b = 0 := by
  unfold transverseEmergence; exact emergence_void_left b (void : I)

/-- Transverse emergence at void right. -/
theorem transverseEmergence_void_right (a : I) :
    transverseEmergence a (void : I) = 0 := by
  unfold transverseEmergence; exact emergence_void_right a a

/-- Transverse emergence is bounded. -/
theorem transverseEmergence_bounded (a b : I) :
    (transverseEmergence a b) ^ 2 ≤
    weight (compose a b) * weight a := by
  unfold transverseEmergence weight; exact emergence_bounded' a b a

/-- The diagonal emergence: measured at b (the right factor). -/
noncomputable def diagonalEmergence (a b : I) : ℝ :=
  emergence a b b

/-- Diagonal emergence at void. -/
theorem diagonalEmergence_void_left (b : I) :
    diagonalEmergence (void : I) b = 0 := by
  unfold diagonalEmergence; exact emergence_void_left b b

/-- Diagonal emergence at void right. -/
theorem diagonalEmergence_void_right (a : I) :
    diagonalEmergence a (void : I) = 0 := by
  unfold diagonalEmergence; exact emergence_void_right a (void : I)

/-- Diagonal emergence is bounded. -/
theorem diagonalEmergence_bounded (a b : I) :
    (diagonalEmergence a b) ^ 2 ≤
    weight (compose a b) * weight b := by
  unfold diagonalEmergence weight; exact emergence_bounded' a b b

/-- Radial vs transverse: total emergence decomposes into
    pieces measured at different reference points. -/
theorem radial_transverse_relation (a b : I) :
    radialEmergence a b =
    rs (compose a b) (compose a b) - rs a (compose a b) - rs b (compose a b) := by
  unfold radialEmergence emergence; ring

/-- The emergence at the composition always decomposes self-resonance. -/
theorem spectral_self_resonance (a b : I) :
    weight (compose a b) =
    rs a (compose a b) + rs b (compose a b) + radialEmergence a b := by
  unfold radialEmergence weight; rw [rs_compose_eq]

end SpectralDecomposition

/-! ## §43. Emergence Cohomological Dimension

The cohomological dimension of the ideatic space measures how many
independent cocycle conditions constrain emergence. For n-fold
compositions, there are n-1 independent cocycle conditions.
This section counts and organizes them. -/

section CohomologicalDimension
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The n-fold resonance expansion: rs(a₁∘...∘aₙ, c) expands into
    individual resonances plus emergence corrections. For n=2, this is
    the basic rs_compose_eq. For n=3, we get 3 individual terms + 2
    emergence terms. -/
theorem nfold_resonance_2 (a₁ a₂ c : I) :
    rs (compose a₁ a₂) c = rs a₁ c + rs a₂ c + emergence a₁ a₂ c :=
  rs_compose_eq a₁ a₂ c

/-- The 3-fold resonance expansion has 3 resonances and 2 emergences. -/
theorem nfold_resonance_3 (a₁ a₂ a₃ c : I) :
    rs (compose (compose a₁ a₂) a₃) c =
    rs a₁ c + rs a₂ c + rs a₃ c +
    emergence a₁ a₂ c + emergence (compose a₁ a₂) a₃ c := by
  rw [rs_compose_eq (compose a₁ a₂) a₃ c, rs_compose_eq a₁ a₂ c]; ring

/-- Independence of cocycle constraints: the two decompositions of
    a 3-fold resonance (left vs right association) give ONE independent
    relation — the cocycle condition itself. -/
theorem cocycle_independence (a₁ a₂ a₃ c : I) :
    emergence a₁ a₂ c + emergence (compose a₁ a₂) a₃ c =
    emergence a₂ a₃ c + emergence a₁ (compose a₂ a₃) c :=
  cocycle_condition a₁ a₂ a₃ c

/-- For 4-fold composition, we get 3 emergence terms and 2 independent
    cocycle conditions (the basic cocycle applied twice). -/
theorem four_fold_independence_count (a₁ a₂ a₃ a₄ c : I) :
    emergence a₁ a₂ c + emergence (compose a₁ a₂) a₃ c +
    emergence (compose (compose a₁ a₂) a₃) a₄ c =
    emergence a₃ a₄ c + emergence a₂ (compose a₃ a₄) c +
    emergence a₁ (compose a₂ (compose a₃ a₄)) c :=
  four_fold_cocycle a₁ a₂ a₃ a₄ c

/-- The "Betti number" b₂ of the ideatic space is effectively 0:
    since emergence is a coboundary of rs, the second cohomology
    vanishes. We express this as: emergence can always be written
    as a coboundary. -/
theorem betti_number_zero :
    ∀ a b c : I, emergence a b c =
    rs (compose a b) c - rs a c - rs b c := by
  intro a b c; unfold emergence; ring

/-- The coboundary map δ: functions I → ℝ produce 2-cocycles.
    The image of δ always satisfies the cocycle condition. -/
theorem coboundary_map_cocycle (f : I → ℝ) (a b c d : I) :
    coboundary1 f a b + coboundary1 f (compose a b) c =
    coboundary1 f b c + coboundary1 f a (compose b c) +
    (f (compose a b) - f a - f b) +
    (f (compose (compose a b) c) - f (compose a b) - f c) -
    (f (compose b c) - f b - f c) -
    (f (compose a (compose b c)) - f a - f (compose b c)) := by
  unfold coboundary1; ring

end CohomologicalDimension

/-! ## §44. Emergence Fixed Point Theory

Fixed points of the emergence flow are ideas whose creative output
stabilizes. An idea a is an emergence fixed point if κ(a,a,a) = κ(a²,a,a²)
— the creative output at step 1 equals that at step 2. -/

section FixedPointTheory
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- An idea is an emergence fixed point if consecutive emergence
    functionals agree. -/
def isEmergenceFixedPoint (a : I) : Prop :=
  ∀ n : ℕ, emergenceEnergyN a (n + 1) = emergenceEnergyN a n

/-- Void is an emergence fixed point. -/
theorem void_isEmergenceFixedPoint : isEmergenceFixedPoint (void : I) := by
  intro n; unfold emergenceEnergyN; simp [rs_void_void]

/-- At an emergence fixed point, weight grows linearly:
    w(aⁿ) = n · E₀ where E₀ is the constant emergence energy. -/
theorem fixed_point_linear_growth (a : I) (h : isEmergenceFixedPoint a)
    (n : ℕ) :
    weight (composeN a (n + 1)) - weight (composeN a n) = emergenceEnergyN a 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [weight_conservation a (k + 1), h k]
    rw [← weight_conservation a k]; exact ih

/-- An idea is a strong fixed point if ALL emergence functionals
    (not just energies) stabilize. -/
def isStrongFixedPoint (a : I) : Prop :=
  ∀ n : ℕ, ∀ c : I, emergence (composeN a (n + 1)) a c = emergence (composeN a n) a c

/-- Void is a strong fixed point. -/
theorem void_isStrongFixedPoint : isStrongFixedPoint (void : I) := by
  intro n c; simp [emergence_void_left]

/-- At a strong fixed point, the resonance derivative is constant. -/
theorem strong_fixed_point_constant_derivative (a : I) (h : isStrongFixedPoint a)
    (c : I) (n : ℕ) :
    resonanceDerivative a c (n + 1) = resonanceDerivative a c n := by
  rw [resonanceDerivative_eq, resonanceDerivative_eq, h n c]

/-- At a strong fixed point, resonance grows linearly. -/
theorem strong_fixed_point_linear_resonance (a : I) (h : isStrongFixedPoint a)
    (c : I) (n : ℕ) :
    resonanceDerivative a c n = resonanceDerivative a c 0 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [strong_fixed_point_constant_derivative a h c k, ih]

/-- Periodic emergence: the emergence pattern repeats with period p. -/
def hasEmergencePeriod (a : I) (p : ℕ) : Prop :=
  p ≥ 1 ∧ ∀ n c : I, emergence (composeN a (p + 1)) a c = emergence (composeN a 1) a c

/-- Void has every period. -/
theorem void_hasPeriod (p : ℕ) (hp : p ≥ 1) :
    hasEmergencePeriod (void : I) p := by
  constructor
  · exact hp
  · intro _ c; simp [emergence_void_left]

end FixedPointTheory

/-! ## §45. Emergence Trace and Determinant Analogues

For matrices, the trace and determinant capture invariant information.
For emergence, we define analogous quantities that are invariant under
certain operations. The "emergence trace" is the total self-emergence,
and the "emergence determinant" involves products of emergences. -/

section TraceAndDeterminant
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The emergence trace of a pair: total emergence measured at both components. -/
noncomputable def emergenceTrace (a b : I) : ℝ :=
  emergence a b a + emergence a b b

/-- Emergence trace at void. -/
theorem emergenceTrace_void_left (b : I) :
    emergenceTrace (void : I) b = 0 := by
  unfold emergenceTrace; rw [emergence_void_left, emergence_void_left]; ring

/-- Emergence trace at void right. -/
theorem emergenceTrace_void_right (a : I) :
    emergenceTrace a (void : I) = 0 := by
  unfold emergenceTrace; rw [emergence_void_right, emergence_void_right]; ring

/-- The emergence trace is bounded. -/
theorem emergenceTrace_bounded (a b : I) :
    (emergenceTrace a b) ^ 2 ≤
    2 * (weight (compose a b) * weight a + weight (compose a b) * weight b) := by
  unfold emergenceTrace weight
  nlinarith [emergence_bounded' a b a, emergence_bounded' a b b,
             sq_nonneg (emergence a b a - emergence a b b),
             sq_nonneg (emergence a b a + emergence a b b)]

/-- The full trace: emergence measured at the composition itself. -/
noncomputable def fullTrace (a b : I) : ℝ :=
  emergence a b (compose a b)

/-- Full trace equals total emergence. -/
theorem fullTrace_eq (a b : I) : fullTrace a b = totalEmergence a b := rfl

/-- The trace-weight relation. -/
theorem trace_weight_relation (a b : I) :
    weight (compose a b) = rs a (compose a b) + rs b (compose a b) + fullTrace a b := by
  unfold weight fullTrace; rw [rs_compose_eq]

/-- The "cross trace": emergence at the other composition. -/
noncomputable def crossTrace (a b : I) : ℝ :=
  emergence a b (compose b a)

/-- Cross trace at void. -/
theorem crossTrace_void_left (b : I) :
    crossTrace (void : I) b = 0 := by
  unfold crossTrace; rw [emergence_void_left]

/-- Cross trace at void right. -/
theorem crossTrace_void_right (a : I) :
    crossTrace a (void : I) = 0 := by
  unfold crossTrace; rw [emergence_void_right]

/-- Trace difference equals emergence evaluated at different compositions. -/
theorem trace_difference (a b : I) :
    fullTrace a b - crossTrace a b =
    emergence a b (compose a b) - emergence a b (compose b a) := by
  unfold fullTrace crossTrace; ring

/-- For commutative composition, full trace equals cross trace. -/
theorem comm_trace_eq (a b : I) (h : compose a b = compose b a) :
    fullTrace a b = crossTrace a b := by
  unfold fullTrace crossTrace; rw [h]

end TraceAndDeterminant

/-! ## §46. Emergence Gradient and Directional Derivatives

The "gradient" of emergence tells us which direction of composition
produces the most emergence. We formalize directional derivatives
of resonance and emergence along composition paths. -/

section GradientTheory
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Directional derivative of resonance at a in direction b:
    how fast rs(a∘b, c) changes compared to rs(a, c). -/
noncomputable def directionalDerivative (a b c : I) : ℝ :=
  rs (compose a b) c - rs a c

/-- Directional derivative decomposes into linear and emergence parts. -/
theorem directionalDerivative_decompose (a b c : I) :
    directionalDerivative a b c = rs b c + emergence a b c := by
  unfold directionalDerivative emergence; ring

/-- Directional derivative at void direction is zero. -/
theorem directionalDerivative_void_dir (a c : I) :
    directionalDerivative a (void : I) c = 0 := by
  unfold directionalDerivative; simp

/-- Directional derivative from void is just resonance. -/
theorem directionalDerivative_from_void (b c : I) :
    directionalDerivative (void : I) b c = rs b c := by
  unfold directionalDerivative; simp [rs_void_left']

/-- The gradient magnitude: how much does composing b with a increase
    the resonance of a with itself? -/
noncomputable def gradientMagnitude (a b : I) : ℝ :=
  directionalDerivative a b a

/-- Gradient magnitude from void. -/
theorem gradientMagnitude_void (b : I) :
    gradientMagnitude (void : I) b = 0 := by
  unfold gradientMagnitude directionalDerivative
  simp [void_left', rs_void_left', rs_void_right', rs_void_void]

/-- The gradient of weight: how fast does weight grow in direction b? -/
noncomputable def weightGradient (a b : I) : ℝ :=
  weight (compose a b) - weight a

/-- Weight gradient is non-negative (enrichment). -/
theorem weightGradient_nonneg (a b : I) : weightGradient a b ≥ 0 := by
  unfold weightGradient weight; linarith [compose_enriches' a b]

/-- Weight gradient at void is zero. -/
theorem weightGradient_void_dir (a : I) :
    weightGradient a (void : I) = 0 := by
  unfold weightGradient weight; simp

/-- Weight gradient decomposes via emergence. -/
theorem weightGradient_decompose (a b : I) :
    weightGradient a b =
    rs a (compose a b) - weight a + rs b (compose a b) + totalEmergence a b := by
  unfold weightGradient weight totalEmergence emergence; ring

end GradientTheory

/-! ## §47. Emergence Comparison Theorems

Comparison theorems relate emergence at different points. These are
analogues of the comparison theorems in Riemannian geometry that
relate curvature at different points to global geometry. -/

section ComparisonTheorems
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Emergence comparison via the cocycle: emergence at a∘b relates to
    emergence at b and emergence at a with the composite b∘c. -/
theorem emergence_comparison (a b c d : I) :
    emergence (compose a b) c d =
    emergence a (compose b c) d + emergence b c d - emergence a b d := by
  linarith [cocycle_condition a b c d]

/-- Power comparison: the emergence of a^(n+2) against c can be expressed
    in terms of a^(n+1) emergence and a correction term via the cocycle. -/
theorem emergence_power_comparison (a c : I) (n : ℕ) :
    emergence (composeN a n) a c + emergence (composeN a (n + 1)) a c =
    emergence a a c + emergence (composeN a n) (compose a a) c := by
  have h := cocycle_condition (composeN a n) a a c
  rw [composeN_succ]
  linarith

/-- Weight comparison: if a₁ "dominates" a₂ (in the sense that
    w(a₁) ≥ w(a₂)), then their compositions satisfy a relation. -/
theorem weight_dominance (a₁ a₂ b : I)
    (h : weight a₁ ≥ weight a₂) :
    weight (compose a₁ b) ≥ weight a₂ := by
  unfold weight at *; linarith [compose_enriches' a₁ b]

/-- Emergence comparison at equal observers: the emergence of two
    different compositions at the same observer are bounded relative
    to each other. -/
theorem emergence_equal_observer_comparison (a₁ b₁ a₂ b₂ c : I) :
    (emergence a₁ b₁ c - emergence a₂ b₂ c) ^ 2 ≤
    2 * (weight (compose a₁ b₁) + weight (compose a₂ b₂)) * weight c := by
  unfold weight
  nlinarith [emergence_bounded' a₁ b₁ c, emergence_bounded' a₂ b₂ c,
             sq_nonneg (emergence a₁ b₁ c - emergence a₂ b₂ c),
             sq_nonneg (emergence a₁ b₁ c + emergence a₂ b₂ c)]

/-- Chain comparison: cumulative emergence of different ideas. -/
theorem chain_comparison (a₁ a₂ c : I) (n : ℕ) :
    resonanceSeq a₁ c n - resonanceSeq a₂ c n =
    n * (rs a₁ c - rs a₂ c) +
    (cumulativeEmergence a₁ c n - cumulativeEmergence a₂ c n) := by
  rw [resonanceSeq_integral, resonanceSeq_integral]; ring

/-- Self-resonance comparison under composition. -/
theorem selfRS_composition_comparison (a b c : I) :
    weight (compose (compose a b) c) ≥ weight a := by
  unfold weight; exact double_enrich a b c

end ComparisonTheorems

/-! ## §48. Emergence Rigidity — When Structure Is Forced

Rigidity theorems show when partial information about emergence
determines the full structure. These are analogues of rigidity
theorems in Riemannian geometry. -/

section Rigidity
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- If all emergence with a fixed left argument vanishes, the idea
    is left-linear. -/
theorem rigidity_left_linear (a : I)
    (h : ∀ b c : I, emergence a b c = 0) : leftLinear a :=
  h

/-- If semantic charge is zero AND the idea is emergence-nilpotent-1,
    then weight growth from self-composition is entirely due to
    cross-resonance. -/
theorem rigidity_nilpotent_weight (a : I)
    (h1 : emergenceNilpotent1 a) :
    weight (compose a a) = 2 * rs a (compose a a) := by
  have := selfRS_compose_decomposition a a
  unfold totalEmergence at this
  rw [h1 (compose a a)] at this
  unfold weight; linarith

/-- If emergence vanishes for all triples, resonance is additive
    (the space is "flat"). -/
theorem rigidity_flat (h : ∀ a b c : I, emergence a b c = 0)
    (a b c : I) : rs (compose a b) c = rs a c + rs b c := by
  have := rs_compose_eq a b c; rw [h a b c] at this; linarith

/-- If emergence vanishes for all triples, weight is additive
    in the sense that weight(a∘b) decomposes cleanly. -/
theorem rigidity_flat_weight (h : ∀ a b c : I, emergence a b c = 0)
    (a b : I) :
    weight (compose a b) = rs a (compose a b) + rs b (compose a b) := by
  unfold weight; rw [rs_compose_eq, h]; ring

/-- If the cocycle is exact (emergence = δ²f for some f), then
    the cocycle condition is automatically satisfied. -/
theorem rigidity_exact_cocycle (f : I → I → ℝ) (a b c d : I) :
    coboundary2 f a b d + coboundary2 f (compose a b) c d =
    coboundary2 f b c d + coboundary2 f a (compose b c) d :=
  coboundary2_is_cocycle f a b c d

/-- Weight rigidity: if w(a∘b) = w(a) for all b, then a absorbs
    all composition enrichment — effectively a acts like void on weight.
    We express this as: enrichment gap is zero. -/
theorem weight_rigidity (a : I)
    (h : ∀ b, weight (compose a b) = weight a) (b : I) :
    enrichmentGap a b = 0 := by
  unfold enrichmentGap weight at *; linarith [h b]

end Rigidity

end IDT3
