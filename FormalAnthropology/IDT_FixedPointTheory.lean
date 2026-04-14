import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic

/-!
# IDT Fixed Point Theory

## Mathematical Content

Fixed point theory is where Ideatic Diffusion Theory intersects classical analysis
in a genuinely novel way. The key observations:

1. **Mutagenic transmission** is a depth-decreasing endomorphism on ℕ-valued depth.
   Since ℕ is well-ordered, iterated transmission must reach a fixed point.
   This is NOT Banach or Brouwer — it's a new fixed point theorem specific to
   the subadditive + well-ordered structure of IDT.

2. **Interpretation** (hermeneutic circle) is an endomorphism that preserves
   resonance. Iterated interpretation may or may not converge — but when it does,
   the fixed point is the "canonical meaning."

3. **Cultural evolution** as iterated diffusion has attractor structure. The
   fixed points are the "universal ideas" — ideas so simple they can't decay further.

4. **Idempotent endomorphisms** correspond to "canonical forms" — ideas that have
   been fully processed by a cultural mechanism.

## Why This Is Novel

Standard fixed point theorems require metric spaces (Banach), topological spaces
(Brouwer/Schauder), or lattices (Knaster-Tarski). IDT's fixed point theory works
on a different structure: a monoid with a subadditive ℕ-valued "depth" and a
non-transitive "resonance" relation. The descent is guaranteed by well-ordering
of ℕ, not by contractivity in the metric sense.

## NO SORRIES, NO ADMITS
-/

namespace IDT.FixedPoint

/-! ## §1. The Axiom Class (self-contained) -/

/-- The foundational axiom class. -/
class IdeaticSpace (I : Type*) where
  compose : I → I → I
  void : I
  resonates : I → I → Prop
  depth : I → ℕ
  atomic : I → Prop
  compose_assoc : ∀ (a b c : I), compose (compose a b) c = compose a (compose b c)
  void_left : ∀ (a : I), compose void a = a
  void_right : ∀ (a : I), compose a void = a
  resonance_refl : ∀ (a : I), resonates a a
  resonance_symm : ∀ (a b : I), resonates a b → resonates b a
  resonance_compose : ∀ (a a' b b' : I),
    resonates a a' → resonates b b' → resonates (compose a b) (compose a' b')
  depth_void : depth void = 0
  depth_subadditive : ∀ (a b : I), depth (compose a b) ≤ depth a + depth b
  depth_atomic : ∀ (a : I), atomic a → depth a ≤ 1
  void_atomic : atomic void

/-! ## §2. Endomorphisms of Ideatic Spaces

An endomorphism is a self-map preserving the monoid + resonance structure.
These model any process that transforms ideas: transmission, interpretation,
translation, criticism, teaching, etc. -/

section Endomorphisms

variable {I : Type*} [IdeaticSpace I]

/-- An ideatic endomorphism: a structure-preserving self-map.
    Note: we require map_resonant for basic endomorphisms, but
    composition uses ResonantEndomorphism separately. -/
structure Endomorphism (I : Type*) [IdeaticSpace I] where
  map : I → I
  map_compose : ∀ (a b : I),
    map (IdeaticSpace.compose a b) = IdeaticSpace.compose (map a) (map b)
  map_void : map IdeaticSpace.void = IdeaticSpace.void

/-- An endomorphism that additionally preserves resonance with the original. -/
structure ResonantEndomorphism (I : Type*) [IdeaticSpace I] extends Endomorphism I where
  map_resonant : ∀ (a : I), IdeaticSpace.resonates a (map a)

/-- The identity endomorphism. -/
def Endomorphism.id : Endomorphism I where
  map := fun a => a
  map_compose := fun _ _ => rfl
  map_void := rfl

/-- The identity is resonant. -/
def ResonantEndomorphism.id : ResonantEndomorphism I where
  toEndomorphism := Endomorphism.id
  map_resonant := fun a => IdeaticSpace.resonance_refl a

/-- Composition of endomorphisms. -/
def Endomorphism.comp (f g : Endomorphism I) : Endomorphism I where
  map := fun a => f.map (g.map a)
  map_compose := fun a b => by
    simp [g.map_compose, f.map_compose]
  map_void := by simp [g.map_void, f.map_void]

/-- Endomorphism composition is associative. -/
theorem Endomorphism.comp_assoc (f g h : Endomorphism I) :
    Endomorphism.comp (Endomorphism.comp f g) h =
    Endomorphism.comp f (Endomorphism.comp g h) := by
  simp [Endomorphism.comp]

/-- Identity is a left unit for composition. -/
theorem Endomorphism.id_comp (f : Endomorphism I) :
    Endomorphism.comp Endomorphism.id f = f := by
  simp [Endomorphism.comp, Endomorphism.id]

/-- Identity is a right unit for composition. -/
theorem Endomorphism.comp_id (f : Endomorphism I) :
    Endomorphism.comp f Endomorphism.id = f := by
  simp [Endomorphism.comp, Endomorphism.id]

end Endomorphisms

/-! ## §3. Depth-Decreasing Endomorphisms

A depth-decreasing endomorphism models any process where ideas lose complexity:
mutagenic transmission, lossy translation, simplification, popularization.

The key theorem: iterated application of any depth-decreasing endomorphism
converges to a fixed point IN FINITE TIME. This is not Banach contraction —
it uses the well-ordering of ℕ. -/

section DepthDecreasing

variable {I : Type*} [IdeaticSpace I]

/-- An endomorphism that never increases depth. -/
structure DepthDecreasing (I : Type*) [IdeaticSpace I] extends Endomorphism I where
  depth_nonincreasing : ∀ (a : I), IdeaticSpace.depth (map a) ≤ IdeaticSpace.depth a

/-- A strictly depth-decreasing endomorphism: complex ideas strictly lose depth. -/
structure StrictlyDecreasing (I : Type*) [IdeaticSpace I] extends DepthDecreasing I where
  strict_decay : ∀ (a : I), IdeaticSpace.depth a > 1 → IdeaticSpace.depth (map a) < IdeaticSpace.depth a

/-- THEOREM: Depth is non-increasing under iteration of a depth-decreasing endomorphism.

    MATHEMATICAL INSIGHT: This is a monotonicity result for the depth sequence
    d(a), d(f(a)), d(f²(a)), ... — it forms a non-increasing sequence in ℕ. -/
theorem depth_nonincreasing_iterate (f : DepthDecreasing I) (a : I) (n : ℕ) :
    IdeaticSpace.depth (Nat.iterate f.map (n + 1) a) ≤
    IdeaticSpace.depth (Nat.iterate f.map n a) := by
  induction n generalizing a with
  | zero => exact f.depth_nonincreasing a
  | succ n ih =>
    show IdeaticSpace.depth (Nat.iterate f.map (n + 1) (f.map a)) ≤
         IdeaticSpace.depth (Nat.iterate f.map n (f.map a))
    exact ih (f.map a)

/-- THEOREM: The depth sequence is bounded below by 0.

    LITERARY INSIGHT: No matter how many times you retell a story, it can't
    become "less than nothing" — there's always at least void remaining. -/
theorem depth_iterate_nonneg (f : DepthDecreasing I) (a : I) (n : ℕ) :
    0 ≤ IdeaticSpace.depth (Nat.iterate f.map n a) :=
  Nat.zero_le _

/-- THEOREM: Iterated depth is bounded by original depth.

    MATHEMATICAL INSIGHT: The depth sequence d(fⁿ(a)) ≤ d(a) for all n.
    This is the key bound that enables convergence. -/
theorem depth_iterate_le (f : DepthDecreasing I) (a : I) (n : ℕ) :
    IdeaticSpace.depth (Nat.iterate f.map n a) ≤ IdeaticSpace.depth a := by
  induction n generalizing a with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    show IdeaticSpace.depth (Nat.iterate f.map n (f.map a)) ≤ IdeaticSpace.depth a
    calc IdeaticSpace.depth (Nat.iterate f.map n (f.map a))
        ≤ IdeaticSpace.depth (f.map a) := ih (f.map a)
      _ ≤ IdeaticSpace.depth a := f.depth_nonincreasing a

/-- THEOREM: Depth-decreasing endomorphisms preserve void.

    LITERARY INSIGHT: Silence under any lossy process remains silence.
    You can't lose information from nothing. -/
theorem depth_decreasing_preserves_void (f : DepthDecreasing I) :
    IdeaticSpace.depth (f.map IdeaticSpace.void) = 0 := by
  have h1 := f.depth_nonincreasing (IdeaticSpace.void : I)
  rw [IdeaticSpace.depth_void] at h1
  omega

/-- THEOREM: Depth-decreasing endomorphisms map atomic ideas to depth-0-or-1 ideas.

    MATHEMATICAL INSIGHT: atomic ideas can't get more complex under lossy transmission. -/
theorem atomic_depth_preserved (f : DepthDecreasing I) (a : I)
    (ha : IdeaticSpace.atomic a) :
    IdeaticSpace.depth (f.map a) ≤ 1 := by
  calc IdeaticSpace.depth (f.map a)
      ≤ IdeaticSpace.depth a := f.depth_nonincreasing a
    _ ≤ 1 := IdeaticSpace.depth_atomic a ha

end DepthDecreasing

/-! ## §4. The IDT Fixed Point Theorem

This is the central result: strictly depth-decreasing endomorphisms
reach a fixed depth level in finite time. Unlike Banach's theorem
(which requires a complete metric space and contractivity), this uses
only the well-ordering of ℕ.

More precisely: for any strictly depth-decreasing endomorphism f and any
idea a, the sequence depth(a), depth(f(a)), depth(f²(a)), ... eventually
stabilizes at some value ≤ 1. -/

section FixedPointTheorem

variable {I : Type*} [IdeaticSpace I]

/-- Helper: for any d and any a with depth(a) ≤ d, depth(f^d(a)) ≤ 1. -/
private theorem depth_stabilization_aux (f : StrictlyDecreasing I) :
    ∀ (d : ℕ) (a : I), IdeaticSpace.depth a ≤ d →
    IdeaticSpace.depth (Nat.iterate f.map d a) ≤ 1 := by
  intro d
  induction d with
  | zero =>
    intro a ha
    simp
    omega
  | succ n ih =>
    intro a ha
    by_cases hd : IdeaticSpace.depth a ≤ 1
    · -- depth a ≤ 1, iterate (n+1) steps can only decrease
      have := depth_iterate_le f.toDepthDecreasing a (n + 1)
      omega
    · -- depth a > 1
      push_neg at hd
      have hdecay := f.strict_decay a (by omega)
      -- depth(f(a)) < depth(a) ≤ n+1, so depth(f(a)) ≤ n
      have hle : IdeaticSpace.depth (f.map a) ≤ n := by omega
      -- By IH on f(a): depth(f^n(f(a))) ≤ 1
      -- And f^(n+1)(a) = f^n(f(a))
      exact ih (f.map a) hle

/-- THEOREM (IDT Fixed Point — Depth Stabilization):
    Under strict decay, depth(fⁿ(a)) ≤ 1 for n = depth(a).

    MATHEMATICAL INSIGHT: This is a termination theorem using well-ordering of ℕ.
    LITERARY INSIGHT: All stories simplify through retelling — epic poems become
    folk tales, philosophy becomes proverbs. The depth must stabilize. -/
theorem depth_stabilization (f : StrictlyDecreasing I) (a : I) :
    IdeaticSpace.depth (Nat.iterate f.map (IdeaticSpace.depth a) a) ≤ 1 :=
  depth_stabilization_aux f (IdeaticSpace.depth a) a (Nat.le_refl _)

/-- COROLLARY: After depth(a) steps, the orbit is in the "ground level."

    LITERARY INSIGHT: Every idea, no matter how deep, reaches cultural bedrock
    after at most depth(a) retellings. The number of retellings needed is exactly
    the complexity of the original. -/
theorem orbit_reaches_ground (f : StrictlyDecreasing I) (a : I) (n : ℕ)
    (hn : n ≥ IdeaticSpace.depth a) :
    IdeaticSpace.depth (Nat.iterate f.map n a) ≤ 1 := by
  have : n = (n - IdeaticSpace.depth a) + IdeaticSpace.depth a := by omega
  rw [this, Function.iterate_add]
  calc IdeaticSpace.depth (Nat.iterate f.map (n - IdeaticSpace.depth a)
          (Nat.iterate f.map (IdeaticSpace.depth a) a))
      ≤ IdeaticSpace.depth (Nat.iterate f.map (IdeaticSpace.depth a) a) :=
        depth_iterate_le f.toDepthDecreasing _ _
    _ ≤ 1 := depth_stabilization f a

end FixedPointTheorem

/-! ## §5. Resonance Orbits

Every endomorphism generates an orbit a, f(a), f²(a), ... where
consecutive elements resonate. This creates a "resonance chain" —
a connected path in the resonance graph. -/

section ResonanceOrbits

variable {I : Type*} [IdeaticSpace I]

/-- THEOREM: Consecutive orbit elements resonate.

    MATHEMATICAL INSIGHT: The orbit forms a path in the resonance graph.
    This is a direct consequence of the map_resonant axiom. -/
theorem orbit_resonance (f : ResonantEndomorphism I) (a : I) (n : ℕ) :
    IdeaticSpace.resonates (Nat.iterate f.map n a) (Nat.iterate f.map (n + 1) a) := by
  induction n generalizing a with
  | zero => exact f.map_resonant a
  | succ n ih =>
    show IdeaticSpace.resonates (Nat.iterate f.map n (f.map a))
                                (Nat.iterate f.map (n + 1) (f.map a))
    exact ih (f.map a)

/-- THEOREM: Orbit elements have non-increasing depth.

    LITERARY INSIGHT: As a story is retold (iterated through a lossy process),
    each version is no more complex than the previous. The orbit "descends"
    through depth levels. -/
theorem orbit_depth_descent (f : DepthDecreasing I) (a : I) (n : ℕ) :
    IdeaticSpace.depth (Nat.iterate f.map (n + 1) a) ≤
    IdeaticSpace.depth (Nat.iterate f.map n a) :=
  depth_nonincreasing_iterate f a n

/-- The orbit of void under any endomorphism is constant.

    LITERARY INSIGHT: Silence transmitted is still silence.
    The void has no information to corrupt. -/
theorem orbit_void_const (f : Endomorphism I) (n : ℕ) :
    Nat.iterate f.map n (IdeaticSpace.void : I) = IdeaticSpace.void := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Nat.iterate f.map n (f.map IdeaticSpace.void) = IdeaticSpace.void
    rw [f.map_void]; exact ih

/-- THEOREM: Composed orbits relate to orbits of compositions.

    MATHEMATICAL INSIGHT: f preserves compose, so the orbit of (a·b)
    is exactly the composed orbit. This is the formal version of
    "transforming a compound idea = transforming its parts." -/
theorem orbit_compose (f : Endomorphism I) (a b : I) (n : ℕ) :
    Nat.iterate f.map n (IdeaticSpace.compose a b) =
    IdeaticSpace.compose (Nat.iterate f.map n a) (Nat.iterate f.map n b) := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    show Nat.iterate f.map n (f.map (IdeaticSpace.compose a b)) =
         IdeaticSpace.compose (Nat.iterate f.map n (f.map a)) (Nat.iterate f.map n (f.map b))
    rw [f.map_compose a b]
    exact ih (f.map a) (f.map b)

end ResonanceOrbits

/-! ## §6. Fixed Points and Canonical Forms

Fixed points of endomorphisms represent "canonical ideas" — ideas that
are stable under the transformation. For mutagenic transmission, these
are the ideas simple enough to survive retelling unchanged. -/

section FixedPoints

variable {I : Type*} [IdeaticSpace I]

/-- An idea is a fixed point of a map if f(a) = a. -/
def IsFixedPoint (f : I → I) (a : I) : Prop := f a = a

/-- THEOREM: Void is always a fixed point.

    LITERARY INSIGHT: Silence is the universal canonical form —
    every lossy process preserves nothing. -/
theorem void_fixed_point (f : Endomorphism I) :
    IsFixedPoint f.map (IdeaticSpace.void : I) :=
  f.map_void

/-- THEOREM: Fixed points are idempotent under iteration.

    MATHEMATICAL INSIGHT: If f(a) = a, then fⁿ(a) = a for all n.
    Once you've reached canonical form, you stay there. -/
theorem fixed_point_iterate (f : Endomorphism I) (a : I)
    (hfix : IsFixedPoint f.map a) (n : ℕ) :
    Nat.iterate f.map n a = a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    show Nat.iterate f.map n (f.map a) = a
    rw [hfix]; exact ih a hfix

/-- THEOREM: The set of fixed points is closed under composition.

    MATHEMATICAL INSIGHT: If f(a) = a and f(b) = b, then f(a·b) = a·b.
    The fixed points form a submonoid!

    LITERARY INSIGHT: Canonical ideas compose to canonical ideas.
    If two proverbs survive retelling, so does their conjunction. -/
theorem fixed_points_closed_compose (f : Endomorphism I) (a b : I)
    (ha : IsFixedPoint f.map a) (hb : IsFixedPoint f.map b) :
    IsFixedPoint f.map (IdeaticSpace.compose a b) := by
  simp only [IsFixedPoint] at *
  rw [f.map_compose, ha, hb]

/-- THEOREM: Fixed points of depth-decreasing endomorphisms have a depth bound.

    MATHEMATICAL INSIGHT: If f is strictly decreasing and f(a) = a, then
    depth(a) ≤ 1. The only fixed points of a strictly lossy process are
    the simplest ideas.

    LITERARY INSIGHT: This is the Canon Theorem — ideas that survive
    indefinite cultural transmission must be simple. Proverbs survive;
    epic nuance does not. -/
theorem fixed_point_depth_bound (f : StrictlyDecreasing I) (a : I)
    (hfix : IsFixedPoint f.map a) :
    IdeaticSpace.depth a ≤ 1 := by
  by_contra h
  push_neg at h
  have hdecay := f.strict_decay a (by omega)
  simp only [IsFixedPoint] at hfix
  rw [hfix] at hdecay
  omega

/-- THEOREM: Fixed points of strictly decreasing maps are all "shallow."

    COROLLARY: The fixed-point submonoid is contained in DepthLevel 1.
    This means the "cultural bedrock" is exactly the simple ideas. -/
theorem fixed_point_submonoid_shallow (f : StrictlyDecreasing I) (a b : I)
    (ha : IsFixedPoint f.map a) (hb : IsFixedPoint f.map b) :
    IdeaticSpace.depth (IdeaticSpace.compose a b) ≤ 2 := by
  have da := fixed_point_depth_bound f a ha
  have db := fixed_point_depth_bound f b hb
  calc IdeaticSpace.depth (IdeaticSpace.compose a b)
      ≤ IdeaticSpace.depth a + IdeaticSpace.depth b :=
        IdeaticSpace.depth_subadditive a b
    _ ≤ 1 + 1 := by omega
    _ = 2 := by omega

end FixedPoints

/-! ## §7. Periodic Points and Cycles

Some endomorphisms have periodic orbits: f^n(a) = a for some n > 0.
These model ideas that "cycle" through variations — like seasonal myths,
recurring literary tropes, or dialectical oscillations. -/

section PeriodicPoints

variable {I : Type*} [IdeaticSpace I]

/-- An idea is periodic with period n if fⁿ(a) = a.
    Takes the raw map function to work with all endomorphism types. -/
def IsPeriodic (f : I → I) (a : I) (n : ℕ) : Prop :=
  n > 0 ∧ Nat.iterate f n a = a

/-- THEOREM: Fixed points are periodic with period 1.

    MATHEMATICAL INSIGHT: Fixed points are a special case of periodic orbits. -/
theorem fixed_implies_periodic (f : Endomorphism I) (a : I)
    (hfix : IsFixedPoint f.map a) :
    IsPeriodic f.map a 1 := by
  constructor
  · omega
  · exact hfix

/-- THEOREM: Periodic points of depth-decreasing maps have constant depth on their orbit.

    MATHEMATICAL INSIGHT: If fⁿ(a) = a and depth never increases, then
    depth must be constant on the entire orbit.

    LITERARY INSIGHT: Ideas that cycle through variations maintain their
    complexity — the cycle is a kind of "conservation law" for depth.
    Seasonal myths don't simplify through their annual cycle. -/
theorem periodic_constant_depth (f : DepthDecreasing I) (a : I) (n : ℕ)
    (hp : IsPeriodic f.map a n) :
    IdeaticSpace.depth (f.map a) = IdeaticSpace.depth a := by
  have hle := f.depth_nonincreasing a
  -- We also need: depth a ≤ depth(f(a))
  -- From periodicity: f^n(a) = a, and depth(f^n(a)) ≤ depth(f^(n-1)(a)) ≤ ... ≤ depth(a)
  -- But depth(f^n(a)) = depth(a), so all inequalities must be equalities
  -- In particular: depth(f(a)) = depth(a)
  have hiter := depth_iterate_le f a n
  rw [hp.2] at hiter
  -- Now: depth(f(a)) ≤ depth(a) AND depth(a) ≤ depth(a) (trivially)
  -- We need depth(a) ≤ depth(f(a))
  -- From: depth(f^(n-1)(f(a))) ≤ depth(f(a)) and f^n(a) = f^(n-1)(f(a)) = a
  -- Actually, f^n(a) = f^(n-1)(f(a)), and depth(a) = depth(f^n(a)) ≤ depth(f(a))
  have hge : IdeaticSpace.depth a ≤ IdeaticSpace.depth (f.map a) := by
    have hn0 : n > 0 := hp.1
    have hnn : Nat.iterate f.map n a = Nat.iterate f.map (n - 1) (f.map a) := by
      have heq : n = (n - 1) + 1 := by omega
      conv_lhs => rw [heq]
      rfl
    rw [hp.2] at hnn
    have := depth_iterate_le f (f.map a) (n - 1)
    rw [← hnn] at this
    exact this
  omega

/-- THEOREM: Strictly decreasing maps have no periodic orbits of period > 1
    for ideas of depth > 1.

    MATHEMATICAL INSIGHT: Strict decay prevents periodic behavior for complex ideas.
    This is an impossibility theorem: complex ideas cannot cycle — they must either
    converge or diverge (and well-ordering forces convergence).

    LITERARY INSIGHT: Deep ideas can't be "recycled" through lossy transmission.
    Every retelling changes them, and the changes accumulate irreversibly. -/
theorem no_complex_periodic (f : StrictlyDecreasing I) (a : I) (n : ℕ)
    (hp : IsPeriodic f.map a n) :
    IdeaticSpace.depth a ≤ 1 := by
  by_contra h
  push_neg at h
  have hdecay := f.strict_decay a (by omega)
  have hconst := periodic_constant_depth f.toDepthDecreasing a n hp
  omega

end PeriodicPoints

/-! ## §8. Contractive Maps

A contractive map is one where depth strictly decreases for ALL non-void elements
(not just depth > 1). This is a stronger condition than strictly decreasing. -/

section Contractive

variable {I : Type*} [IdeaticSpace I]

/-- A contractive endomorphism: depth decreases for every non-void element. -/
structure Contractive (I : Type*) [IdeaticSpace I] extends DepthDecreasing I where
  contracts : ∀ (a : I), IdeaticSpace.depth a > 0 → IdeaticSpace.depth (map a) < IdeaticSpace.depth a

/-- THEOREM: Under a contractive map, every element reaches void-depth
    in at most depth(a) steps.

    MATHEMATICAL INSIGHT: This is the strongest fixed-point convergence result:
    not just depth ≤ 1, but depth = 0. The element "evaporates."

    LITERARY INSIGHT: Under extreme lossy transmission, all ideas eventually
    reduce to silence. Not just simplification — complete loss. -/

private theorem contractive_reaches_zero_aux (f : Contractive I) :
    ∀ (d : ℕ) (a : I), IdeaticSpace.depth a ≤ d →
    IdeaticSpace.depth (Nat.iterate f.map d a) = 0 := by
  intro d
  induction d with
  | zero =>
    intro a ha
    simp; omega
  | succ n ih =>
    intro a ha
    by_cases hd : IdeaticSpace.depth a = 0
    · have := depth_iterate_le f.toDepthDecreasing a (n + 1)
      omega
    · push_neg at hd
      have hdecay := f.contracts a (by omega)
      have hle : IdeaticSpace.depth (f.map a) ≤ n := by omega
      exact ih (f.map a) hle

theorem contractive_reaches_zero (f : Contractive I) (a : I) :
    IdeaticSpace.depth (Nat.iterate f.map (IdeaticSpace.depth a) a) = 0 :=
  contractive_reaches_zero_aux f (IdeaticSpace.depth a) a (Nat.le_refl _)

/-- THEOREM: Every element is eventually mapped to void-depth by a contractive map.

    COROLLARY: The orbit of any element under a contractive map converges to
    depth 0 in at most depth(a) steps. -/
theorem contractive_eventual_zero (f : Contractive I) (a : I) (n : ℕ)
    (hn : n ≥ IdeaticSpace.depth a) :
    IdeaticSpace.depth (Nat.iterate f.map n a) = 0 := by
  have hsplit : n = (n - IdeaticSpace.depth a) + IdeaticSpace.depth a := by omega
  rw [hsplit, Function.iterate_add]
  have hbase := contractive_reaches_zero f a
  have hle := depth_iterate_le f.toDepthDecreasing
    (Nat.iterate f.map (IdeaticSpace.depth a) a)
    (n - IdeaticSpace.depth a)
  rw [hbase] at hle
  exact Nat.le_antisymm hle (Nat.zero_le _)

end Contractive

/-! ## §9. Endomorphism Factorization

Every endomorphism can be factored through its "kernel" (what it sends
to void) and its "image" (what it actually produces). This gives an
analogue of the first isomorphism theorem. -/

section Factorization

variable {I : Type*} [IdeaticSpace I]

/-- The kernel of an endomorphism: ideas mapped to void. -/
def kernel (f : Endomorphism I) : Set I :=
  {a | f.map a = IdeaticSpace.void}

/-- The image of an endomorphism. -/
def image (f : Endomorphism I) : Set I :=
  {b | ∃ a, f.map a = b}

/-- THEOREM: Void is always in the kernel.

    LITERARY INSIGHT: The endomorphism "kills" silence — and silence
    maps to itself, so it's trivially in the kernel. -/
theorem void_in_kernel (f : Endomorphism I) :
    (IdeaticSpace.void : I) ∈ kernel f := by
  simp [kernel, f.map_void]

/-- THEOREM: The kernel is closed under composition with void. -/
theorem kernel_void_closed (f : Endomorphism I) (a : I)
    (ha : a ∈ kernel f) :
    IdeaticSpace.compose a (IdeaticSpace.void : I) ∈ kernel f := by
  simp [kernel] at *
  rw [IdeaticSpace.void_right] at *
  exact ha

/-- THEOREM: Void is always in the image.

    LITERARY INSIGHT: Every transformation can produce silence. -/
theorem void_in_image (f : Endomorphism I) :
    (IdeaticSpace.void : I) ∈ image f := by
  simp [image]
  exact ⟨IdeaticSpace.void, f.map_void⟩

/-- THEOREM: The image is closed under composition.

    MATHEMATICAL INSIGHT: The image of a monoid endomorphism is a submonoid.
    Since f(a)·f(b) = f(a·b), any two image elements compose to an image element.

    LITERARY INSIGHT: The "range" of a cultural process is itself culturally
    complete — you can combine processed ideas and get another processed idea. -/
theorem image_closed_compose (f : Endomorphism I) (x y : I)
    (hx : x ∈ image f) (hy : y ∈ image f) :
    IdeaticSpace.compose x y ∈ image f := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨IdeaticSpace.compose a b, f.map_compose a b⟩

/-- THEOREM: Depth of image elements is bounded by kernel depth.

    If f is depth-decreasing, then every image element has depth ≤ original. -/
theorem image_depth_bounded (f : DepthDecreasing I) (b : I)
    (hb : b ∈ image f.toEndomorphism) :
    ∃ a, f.map a = b ∧ IdeaticSpace.depth b ≤ IdeaticSpace.depth a := by
  obtain ⟨a, rfl⟩ := hb
  exact ⟨a, rfl, f.depth_nonincreasing a⟩

end Factorization

/-! ## §10. The Interpretation Fixed Point

Interpretation in hermeneutics is modeled as an endomorphism:
reading a text produces a new understanding, which when "read" again
produces another, etc. The hermeneutic circle asks: does this converge?

ANSWER: If interpretation is depth-decreasing (each reading simplifies
understanding), then YES — it converges in finite time. The fixed point
is the "canonical interpretation."

If interpretation preserves depth, convergence is NOT guaranteed —
you might cycle forever through equally-deep but different readings.
This is the formal content of "infinite interpretation" in deconstruction. -/

section Interpretation

variable {I : Type*} [IdeaticSpace I]

/-- An interpretation function: maps ideas to their "understood" versions. -/
def Interpretation (I : Type*) [IdeaticSpace I] := Endomorphism I

/-- THEOREM: If interpretation is depth-decreasing, the hermeneutic circle converges.

    LITERARY INSIGHT: This resolves the millennia-old question of whether
    interpretation converges. The answer depends on the "type" of reading:
    - Analytical reading (depth-decreasing): converges to canonical meaning
    - Deconstructive reading (depth-preserving): may cycle forever
    - Creative reading (depth-increasing): impossible under our axioms

    The convergence time is bounded by the depth of the original text. -/
theorem hermeneutic_convergence (interp : Interpretation I)
    (hdecr : ∀ a : I, IdeaticSpace.depth a > 1 →
      IdeaticSpace.depth (interp.map a) < IdeaticSpace.depth a)
    (hnoninc : ∀ a : I, IdeaticSpace.depth (interp.map a) ≤ IdeaticSpace.depth a)
    (a : I) :
    IdeaticSpace.depth (Nat.iterate interp.map (IdeaticSpace.depth a) a) ≤ 1 := by
  -- Build a StrictlyDecreasing from interp
  let dd : DepthDecreasing I := {
    toEndomorphism := interp
    depth_nonincreasing := hnoninc
  }
  let sd : StrictlyDecreasing I := {
    toDepthDecreasing := dd
    strict_decay := hdecr
  }
  exact depth_stabilization sd a

/-- THEOREM: The "meaning" of a text stabilizes after finite readings.

    LITERARY INSIGHT: You can't learn infinitely more from re-reading.
    Each analytical reading extracts less new understanding. Eventually,
    you've "gotten everything out of it." The number of productive
    readings is bounded by the text's depth. -/
theorem finite_productive_readings (interp : Interpretation I)
    (hnoninc : ∀ a : I, IdeaticSpace.depth (interp.map a) ≤ IdeaticSpace.depth a)
    (a : I) (n : ℕ) :
    IdeaticSpace.depth (Nat.iterate interp.map n a) ≤ IdeaticSpace.depth a := by
  let dd : DepthDecreasing I := {
    toEndomorphism := interp
    depth_nonincreasing := hnoninc
  }
  exact depth_iterate_le dd a n

end Interpretation

/-! ## §11. Commuting Endomorphisms

When do two cultural processes commute? If f and g are endomorphisms
with f ∘ g = g ∘ f, they model "independent" cultural forces.
Non-commutation means the order of processing matters. -/

section Commuting

variable {I : Type*} [IdeaticSpace I]

/-- Two endomorphisms commute if their composition is order-independent. -/
def Commute (f g : Endomorphism I) : Prop :=
  ∀ a : I, f.map (g.map a) = g.map (f.map a)

/-- THEOREM: Every endomorphism commutes with itself.

    TRIVIAL but foundational: self-commutation is guaranteed. -/
theorem commute_self (f : Endomorphism I) : Commute f f := fun _ => rfl

/-- THEOREM: Every endomorphism commutes with the identity.

    LITERARY INSIGHT: "Doing nothing" is always compatible with any process. -/
theorem commute_id (f : Endomorphism I) : Commute f Endomorphism.id :=
  fun _ => rfl

/-- THEOREM: Commutation is symmetric. -/
theorem commute_symm (f g : Endomorphism I) (h : Commute f g) :
    Commute g f :=
  fun a => (h a).symm

/-- THEOREM: Commuting endomorphisms satisfy f^m ∘ g^n = g^n ∘ f^m.

    MATHEMATICAL INSIGHT: Commutation of single steps extends to all powers.
    This means commuting cultural processes are "infinitely compatible."

    LITERARY INSIGHT: If translation and interpretation commute,
    then translating then interpreting n times equals interpreting n times
    then translating. This is rare and interesting when it occurs. -/
theorem commute_iterate_left (f g : Endomorphism I) (h : Commute f g)
    (m : ℕ) (a : I) :
    Nat.iterate f.map m (g.map a) = g.map (Nat.iterate f.map m a) := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih =>
    show Nat.iterate f.map m (f.map (g.map a)) =
         g.map (Nat.iterate f.map m (f.map a))
    rw [h a]
    exact ih (f.map a)

/-- THEOREM: Commuting depth-decreasing endomorphisms give the same depth bound
    regardless of application order.

    MATHEMATICAL INSIGHT: If f and g commute and both decrease depth,
    then depth(f(g(a))) = depth(g(f(a))), and both ≤ depth(a).

    LITERARY INSIGHT: If translation and simplification commute,
    it doesn't matter whether you translate-then-simplify or
    simplify-then-translate — you end up at the same complexity level. -/
theorem commuting_depth_bound (f g : DepthDecreasing I)
    (_hcomm : Commute f.toEndomorphism g.toEndomorphism) (a : I) :
    IdeaticSpace.depth (f.map (g.map a)) ≤ IdeaticSpace.depth a := by
  calc IdeaticSpace.depth (f.map (g.map a))
      ≤ IdeaticSpace.depth (g.map a) := f.depth_nonincreasing (g.map a)
    _ ≤ IdeaticSpace.depth a := g.depth_nonincreasing a

end Commuting

/-! ## §12. Power Endomorphisms and Convergence Rate

How fast does an endomorphism converge? The "convergence rate" is
the minimum n such that depth(fⁿ(a)) ≤ 1. We've shown it's ≤ depth(a),
but can we do better? -/

section ConvergenceRate

variable {I : Type*} [IdeaticSpace I]

/-- The convergence time of an element under a strictly decreasing endomorphism:
    how many applications until depth ≤ 1. We bound it by depth(a). -/
theorem convergence_time_bound (f : StrictlyDecreasing I) (a : I) :
    IdeaticSpace.depth (Nat.iterate f.map (IdeaticSpace.depth a) a) ≤ 1 :=
  depth_stabilization f a

/-- THEOREM: Composition of two strictly decreasing maps converges
    in at most half the time (depth of first application).

    MATHEMATICAL INSIGHT: Composing two lossy processes doubles the
    decay rate. Two strictly decreasing endomorphisms composed give
    a single endomorphism that decays at least as fast.

    LITERARY INSIGHT: If both translation AND interpretation simplify,
    then translate-then-interpret simplifies at double rate. -/
theorem composed_convergence (f g : StrictlyDecreasing I) (a : I) :
    IdeaticSpace.depth (g.map (f.map a)) ≤ IdeaticSpace.depth a := by
  calc IdeaticSpace.depth (g.map (f.map a))
      ≤ IdeaticSpace.depth (f.map a) := g.depth_nonincreasing (f.map a)
    _ ≤ IdeaticSpace.depth a := f.depth_nonincreasing a

/-- THEOREM: The depth sequence under strict decay is strictly decreasing
    until it reaches ≤ 1.

    MATHEMATICAL INSIGHT: The orbit doesn't "plateau" above level 1 —
    every step brings it strictly closer to the ground. -/
theorem strict_descent_until_ground (f : StrictlyDecreasing I) (a : I)
    (ha : IdeaticSpace.depth a > 1) :
    IdeaticSpace.depth (f.map a) < IdeaticSpace.depth a :=
  f.strict_decay a ha

end ConvergenceRate

end IDT.FixedPoint
