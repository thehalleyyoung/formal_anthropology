import Mathlib.Tactic
import Mathlib.Data.Nat.Defs

/-!
# IDT Advanced Theorems: Structural Results for the Expanded Monograph

This file establishes 30 new theorems in Ideatic Diffusion Theory,
organized into seven thematic clusters. Each theorem connects
mathematical structure to literary-theoretical insight.

## Cluster 1: Resonance Monotonicity
Left and right composition preserve resonance independently.

## Cluster 2: The Algebra of Endomorphisms
Endomorphisms form a semigroup under composition; fixed points form a submonoid.
The "Derrida Theorem" shows no deep idea can be its own interpretation.

## Cluster 3: Power Element Theory (Tradition Algebra)
The power function is a monoid homomorphism from (ℕ,+) to (IS,∘).

## Cluster 4: Self-Reference and Idempotents
Self-reinforcing ideas are invariant under interpretation.

## Cluster 5: Orbit Dynamics
Combining depth stabilization with resonance preservation yields
convergence theorems for ideatic orbits.

## Cluster 6: Multi-Endomorphism Interactions
What happens when multiple interpretive processes interact.

## Cluster 7: Depth Filtration and Stratification
Depth levels form a filtration compatible with the monoid structure.
-/

set_option autoImplicit false

namespace IDT.Advanced

/-! ### Core Axiom System (self-contained) -/

class IdeaticSpace (I : Type*) where
  void : I
  compose : I → I → I
  resonates : I → I → Prop
  depth : I → ℕ
  compose_assoc : ∀ (a b c : I), compose (compose a b) c = compose a (compose b c)
  void_left : ∀ (a : I), compose void a = a
  void_right : ∀ (a : I), compose a void = a
  resonance_refl : ∀ (a : I), resonates a a
  resonance_symm : ∀ (a b : I), resonates a b → resonates b a
  resonance_compose : ∀ (a a' b b' : I),
    resonates a a' → resonates b b' → resonates (compose a b) (compose a' b')
  depth_void : depth void = 0
  depth_compose_le : ∀ (a b : I), depth (compose a b) ≤ depth a + depth b
  depth_void_unique : ∀ (a : I), depth a = 0 → a = void

variable {I : Type*} [IdeaticSpace I]

open IdeaticSpace

/-- Iterated self-composition: the "tradition" of an idea. -/
def composeN (a : I) : ℕ → I
  | 0 => void
  | n + 1 => compose (composeN a n) a

/-! ### Structures -/

/-- An endomorphism of an ideatic space: an interpretation that
    preserves monoid structure. -/
structure Endo (I : Type*) [IdeaticSpace I] where
  f : I → I
  map_void : f void = void
  map_compose : ∀ (a b : I), f (compose a b) = compose (f a) (f b)

/-- A depth-decreasing endomorphism: an interpretation that
    never makes ideas more complex. -/
structure DepthDec (I : Type*) [IdeaticSpace I] extends Endo I where
  depth_le : ∀ (a : I), depth (f a) ≤ depth a

/-- A strictly decreasing endomorphism: an interpretation that
    actively simplifies complex ideas. -/
structure StrictDec (I : Type*) [IdeaticSpace I] extends DepthDec I where
  strict : ∀ (a : I), depth a > 1 → depth (f a) < depth a

/-! ### Infrastructure Lemmas -/

private theorem iter_depth_le (g : DepthDec I) (a : I) (n : ℕ) :
    depth (Nat.iterate g.f n a) ≤ depth a := by
  induction n generalizing a with
  | zero => exact le_refl _
  | succ n ih =>
    calc depth (Nat.iterate g.f n (g.f a))
        ≤ depth (g.f a) := ih (g.f a)
      _ ≤ depth a := g.depth_le a

private theorem depth_stab_aux (g : StrictDec I) :
    ∀ (d : ℕ) (a : I), depth a ≤ d →
    depth (Nat.iterate g.f d a) ≤ 1 := by
  intro d
  induction d with
  | zero => intro a ha; simp; omega
  | succ n ih =>
    intro a ha
    by_cases hd : depth a ≤ 1
    · have := iter_depth_le g.toDepthDec a (n + 1); omega
    · push_neg at hd
      exact ih (g.f a) (by have := g.strict a (by omega); omega)

private theorem depth_stabilization (g : StrictDec I) (a : I) :
    depth (Nat.iterate g.f (depth a) a) ≤ 1 :=
  depth_stab_aux g (depth a) a (le_refl _)

private theorem resonance_consensus_aux
    (f : I → I) (hpres : ∀ x y : I, resonates x y → resonates (f x) (f y))
    {a b : I} (h : resonates a b) (n : ℕ) :
    resonates (Nat.iterate f n a) (Nat.iterate f n b) := by
  induction n generalizing a b with
  | zero => exact h
  | succ n ih => exact ih (hpres a b h)

/-! ================================================================
    CLUSTER 1: RESONANCE MONOTONICITY
    Composition preserves resonance in each argument separately.
    ================================================================ -/

/-- **Theorem A1: Left Resonance Preservation.**
    Adding common context preserves resonance. If two ideas resonate,
    embedding them in the same larger context preserves their resonance.
    Literary meaning: prefixing the same tradition to two resonant works
    does not destroy their thematic connection. -/
theorem left_res_preservation (a : I) {b c : I}
    (h : resonates b c) :
    resonates (compose a b) (compose a c) :=
  resonance_compose a a b c (resonance_refl a) h

/-- **Theorem A2: Right Resonance Preservation.**
    Appending common context preserves resonance.
    Literary meaning: suffixing the same coda to two resonant texts
    preserves their resonance. -/
theorem right_res_preservation {a b : I} (c : I)
    (h : resonates a b) :
    resonates (compose a c) (compose b c) :=
  resonance_compose a b c c h (resonance_refl c)

/-- **Theorem A3: Triple Resonance Composition.**
    If three pairs of ideas each resonate, their triple
    compositions also resonate. This extends R3 to depth-3 structures.
    Literary meaning: resonance propagates through arbitrarily deep
    hierarchical structures. -/
theorem triple_resonance {a a' b b' c c' : I}
    (hab : resonates a a') (hbc : resonates b b') (hcc : resonates c c') :
    resonates (compose (compose a b) c) (compose (compose a' b') c') :=
  resonance_compose _ _ _ _ (resonance_compose a a' b b' hab hbc) hcc

/-- **Theorem A4: Quadruple Resonance Composition.**
    Resonance propagation extends to depth-4 structures.
    This establishes the general pattern by which resonance
    scales to complex compositional hierarchies. -/
theorem quad_resonance {a a' b b' c c' d d' : I}
    (ha : resonates a a') (hb : resonates b b')
    (hc : resonates c c') (hd : resonates d d') :
    resonates (compose (compose (compose a b) c) d)
              (compose (compose (compose a' b') c') d') :=
  resonance_compose _ _ _ _ (triple_resonance ha hb hc) hd

/-! ================================================================
    CLUSTER 2: THE ALGEBRA OF ENDOMORPHISMS
    ================================================================ -/

/-- **Theorem B1: Endomorphism Composition Depth Bound.**
    Composing two depth-decreasing interpretive methods produces a method
    at least as lossy as either alone.
    Literary meaning: layered interpretation (e.g., first historicist,
    then psychoanalytic) compounds the simplification. -/
theorem endo_compose_depth (g h : DepthDec I) (a : I) :
    depth (g.f (h.f a)) ≤ depth a :=
  le_trans (g.depth_le (h.f a)) (h.depth_le a)

/-- **Theorem B2: The Derrida Theorem (No Deep Fixed Points).**
    Under strict interpretive decay, no complex idea can serve as its
    own definitive interpretation. All stable meanings are shallow.
    This formalizes Derrida's insight that "transcendental signifieds"
    cannot sustain themselves under conditions of interpretive slippage.
    Mathematically: if f is a contraction on depth, its fixed points
    must lie in the "ground level" of the filtration. -/
theorem no_deep_fixed_points (g : StrictDec I) {a : I}
    (hfix : g.f a = a) : depth a ≤ 1 := by
  by_contra h
  push_neg at h
  have : depth (g.f a) < depth a := g.strict a h
  rw [hfix] at this
  exact Nat.lt_irrefl _ this

/-- **Theorem B3: Fixed Point Submonoid (Closure).**
    The set of stable meanings is closed under composition.
    Literary meaning: combining two "settled" interpretations yields
    another settled interpretation. The canon is compositionally closed. -/
theorem fixed_compose (g : Endo I) {a b : I}
    (ha : g.f a = a) (hb : g.f b = b) :
    g.f (compose a b) = compose a b := by
  rw [g.map_compose, ha, hb]

/-- **Theorem B4: The Shallow Canon Theorem.**
    Under strict decay, composing any two fixed points yields an idea
    of depth at most 2. The algebra of stable meanings is severely
    constrained: it lives within the bottom two strata.
    Literary meaning: the set of things that can be definitively said
    about a complex text is necessarily shallow and limited. -/
theorem fixed_compose_bounded (g : StrictDec I) {a b : I}
    (ha : g.f a = a) (hb : g.f b = b) :
    depth (compose a b) ≤ 2 := by
  have h1 := no_deep_fixed_points g ha
  have h2 := no_deep_fixed_points g hb
  calc depth (compose a b) ≤ depth a + depth b := depth_compose_le a b
    _ ≤ 1 + 1 := Nat.add_le_add h1 h2
    _ = 2 := by omega

/-- **Theorem B5: Commuting Methods Share Stable Ground.**
    If two interpretive methods commute (can be applied in any order),
    then each preserves the other's stable meanings.
    Literary meaning: compatible critical methods must agree on what
    is "settled." A feminist reading and a Marxist reading that can
    be applied in either order must preserve each other's conclusions. -/
theorem commuting_preserve_fixed (g h : Endo I)
    (hcomm : ∀ (x : I), g.f (h.f x) = h.f (g.f x))
    {a : I} (hfix : h.f a = a) :
    h.f (g.f a) = g.f a := by
  rw [← hcomm, hfix]

/-- **Theorem B6: Endomorphism Iteration Depth.**
    Iterating a depth-decreasing endomorphism n times still yields
    a depth-decreasing map. -/
theorem iter_still_depth_dec (g : DepthDec I) (a : I) (n : ℕ) :
    depth (Nat.iterate g.f n a) ≤ depth a :=
  iter_depth_le g a n

/-! ================================================================
    CLUSTER 3: POWER ELEMENT THEORY (Tradition Algebra)
    ================================================================ -/

/-- **Theorem C1: Tradition Decomposition.**
    The power function is a monoid homomorphism from (ℕ,+) to (IS,∘):
    a^(m+n) = a^m ∘ a^n. Any tradition can be split at any historical
    point without altering the cumulative result.
    Literary meaning: the accumulated canon of a literary period can be
    decomposed into sub-periods. The Victorian novel tradition equals
    early-Victorian composed with late-Victorian. -/
theorem tradition_decomposition (a : I) (m n : ℕ) :
    composeN a (m + n) = compose (composeN a m) (composeN a n) := by
  induction n with
  | zero =>
    simp only [Nat.add_zero, composeN]
    rw [void_right]
  | succ n ih =>
    have hmn : m + (n + 1) = (m + n) + 1 := by omega
    rw [hmn]
    show compose (composeN a (m + n)) a =
         compose (composeN a m) (compose (composeN a n) a)
    rw [ih, compose_assoc]

/-- **Theorem C2: Power Depth Bound.**
    The depth of a tradition of length n is bounded by n times the
    depth of the founding idea.
    Literary meaning: a tradition cannot gain depth beyond what its
    founding works supply, multiplied by the number of iterations. -/
theorem power_depth_bound (a : I) (n : ℕ) :
    depth (composeN a n) ≤ n * depth a := by
  induction n with
  | zero => simp [composeN, depth_void]
  | succ n ih =>
    calc depth (composeN a (n + 1))
        = depth (compose (composeN a n) a) := rfl
      _ ≤ depth (composeN a n) + depth a := depth_compose_le _ _
      _ ≤ n * depth a + depth a := Nat.add_le_add_right ih _
      _ = (n + 1) * depth a := by ring

/-- **Theorem C3: The Tradition Homomorphism.**
    An interpretation applied to an entire tradition equals the
    tradition built from the interpreted founding idea:
    f(a^n) = f(a)^n.
    Literary meaning: reading a tradition through a single lens is
    equivalent to building the tradition from the lens-altered source.
    A Marxist reading of the entire Romantic tradition equals the
    tradition generated by a Marxist reading of Romanticism's origin. -/
theorem endo_power (g : Endo I) (a : I) (n : ℕ) :
    g.f (composeN a n) = composeN (g.f a) n := by
  induction n with
  | zero => simp [composeN, g.map_void]
  | succ n ih =>
    show g.f (compose (composeN a n) a) = compose (composeN (g.f a) n) (g.f a)
    rw [g.map_compose, ih]

/-- **Theorem C4: Canonical Tradition Stability.**
    If an idea is a fixed point, its entire tradition is also fixed.
    Literary meaning: if the Bible is a fixed point under Christian
    exegesis, then the entire tradition of Biblical commentary is
    also fixed—it reproduces itself under the same exegesis. -/
theorem power_fixed (g : Endo I) {a : I}
    (hfix : g.f a = a) (n : ℕ) :
    g.f (composeN a n) = composeN a n := by
  rw [endo_power, hfix]

/-- **Theorem C5: Unit Tradition.**
    The tradition of length one is the idea itself. -/
theorem composeN_one_eq (a : I) : composeN a 1 = a := by
  show compose void a = a
  exact void_left a

/-! ================================================================
    CLUSTER 4: SELF-REFERENCE AND IDEMPOTENTS
    ================================================================ -/

/-- **Theorem D1: Idempotent Transmission (Mise en Abyme Invariance).**
    If a text is self-reinforcing (a∘a = a, like a mise en abyme),
    then every reading of it is also self-reinforcing.
    Literary meaning: the self-referential quality of works like
    Borges's "Pierre Menard" or Nabokov's "Pale Fire" is preserved
    under any structural interpretation. -/
theorem idempotent_transmission (g : Endo I) {a : I}
    (h : compose a a = a) :
    compose (g.f a) (g.f a) = g.f a := by
  rw [← g.map_compose, h]

/-- **Theorem D2: Idempotent Orbit Preservation.**
    The idempotent property is preserved along the entire orbit
    of an endomorphism. Every iterate of a self-referencing idea
    remains self-referencing.
    Literary meaning: the mise en abyme structure, once established,
    is ineradicable—no amount of reinterpretation can destroy it. -/
theorem idempotent_orbit (g : Endo I) {a : I}
    (h : compose a a = a) (n : ℕ) :
    compose (Nat.iterate g.f n a) (Nat.iterate g.f n a) =
    Nat.iterate g.f n a := by
  induction n generalizing a with
  | zero => exact h
  | succ n ih =>
    show compose (Nat.iterate g.f n (g.f a))
                 (Nat.iterate g.f n (g.f a)) =
         Nat.iterate g.f n (g.f a)
    apply ih
    rw [← g.map_compose, h]

/-- **Theorem D3: Idempotent Fixed Points Are Shallow.**
    Under strict decay, a self-reinforcing idea that is also a fixed
    point must have depth ≤ 1.
    Literary meaning: a perfectly self-referencing, stable text
    cannot be deep. Infinite self-reference and stability together
    force shallowness—a formalization of the suspicion that
    perfect self-consciousness precludes depth. -/
theorem idempotent_fixed_shallow (g : StrictDec I) {a : I}
    (_h_idem : compose a a = a) (h_fix : g.f a = a) :
    depth a ≤ 1 :=
  no_deep_fixed_points g h_fix

/-! ================================================================
    CLUSTER 5: ORBIT DYNAMICS
    ================================================================ -/

/-- **Theorem E1: Orbit Composition Factorization.**
    An endomorphism distributes over composition at every iterate:
    f^n(a∘b) = f^n(a) ∘ f^n(b).
    Literary meaning: the fate of a synthesis is determined by
    the fates of its components. -/
theorem orbit_compose_factor (g : Endo I) (a b : I) (n : ℕ) :
    Nat.iterate g.f n (compose a b) =
    compose (Nat.iterate g.f n a) (Nat.iterate g.f n b) := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    show Nat.iterate g.f n (g.f (compose a b)) =
         compose (Nat.iterate g.f n (g.f a)) (Nat.iterate g.f n (g.f b))
    rw [g.map_compose]
    exact ih (g.f a) (g.f b)

/-- **Theorem E2: Convergent Resonance.**
    Under strict decay with resonance preservation, resonant ideas
    converge to resonant shallow residues. After enough iterations,
    both orbits have depth ≤ 1 AND they still resonate.
    Literary meaning: under conditions of interpretive simplification,
    resonant traditions eventually agree on shallow platitudes—but
    they agree. This formalizes the observation that distant literary
    traditions, when sufficiently simplified, converge to the same
    "universal themes." -/
theorem convergent_resonance (g : StrictDec I)
    (hpres : ∀ x y : I, resonates x y → resonates (g.f x) (g.f y))
    {a b : I} (h : resonates a b) (n : ℕ)
    (hn : n ≥ depth a) (hm : n ≥ depth b) :
    resonates (Nat.iterate g.f n a) (Nat.iterate g.f n b) ∧
    depth (Nat.iterate g.f n a) ≤ 1 ∧
    depth (Nat.iterate g.f n b) ≤ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact resonance_consensus_aux g.f hpres h n
  · have h1 := depth_stabilization g a
    have h3 : n = depth a + (n - depth a) := by omega
    rw [h3, Function.iterate_add_apply]
    have h4 : depth (Nat.iterate g.f (n - depth a) a) ≤ depth a :=
      iter_depth_le g.toDepthDec a _
    exact depth_stab_aux g (depth a) _ h4
  · have h1 := depth_stabilization g b
    have h3 : n = depth b + (n - depth b) := by omega
    rw [h3, Function.iterate_add_apply]
    have h4 : depth (Nat.iterate g.f (n - depth b) b) ≤ depth b :=
      iter_depth_le g.toDepthDec b _
    exact depth_stab_aux g (depth b) _ h4

/-- **Theorem E3: Canon Depth Absorption.**
    A canonical text (fixed point), when composed with any idea that
    has been sufficiently interpreted, yields something whose depth
    is bounded by depth(p) + 1.
    Literary meaning: a canonical text absorbs all sufficiently
    processed ideas into its own orbit. After enough simplification,
    adding any idea to Shakespeare changes Shakespeare's depth by at
    most 1. -/
theorem canon_depth_absorption (g : StrictDec I)
    {p : I} (_hfix : g.f p = p) {a : I} (n : ℕ)
    (hn : n ≥ depth a) :
    depth (compose p (Nat.iterate g.f n a)) ≤ depth p + 1 := by
  have h3 : n = depth a + (n - depth a) := by omega
  rw [h3, Function.iterate_add_apply]
  have h4 : depth (Nat.iterate g.f (n - depth a) a) ≤ depth a :=
    iter_depth_le g.toDepthDec a _
  have h5 : depth (Nat.iterate g.f (depth a) (Nat.iterate g.f (n - depth a) a)) ≤ 1 :=
    depth_stab_aux g (depth a) _ h4
  calc depth (compose p (Nat.iterate g.f (depth a) (Nat.iterate g.f (n - depth a) a)))
      ≤ depth p + depth (Nat.iterate g.f (depth a) (Nat.iterate g.f (n - depth a) a)) :=
        depth_compose_le _ _
    _ ≤ depth p + 1 := Nat.add_le_add_left h5 _

/-- **Theorem E4: Fixed Point Resonance with Powers.**
    If an idea resonates with a fixed point, then all their powers
    resonate pairwise.
    Literary meaning: if a work resonates with a canonical text,
    then the entire tradition built on that work resonates with
    the tradition built on the canonical text. -/
theorem fixed_point_power_resonance
    {p a : I} (hres : resonates a p) (n : ℕ) :
    resonates (composeN a n) (composeN p n) := by
  induction n with
  | zero => exact resonance_refl void
  | succ n ih =>
    show resonates (compose (composeN a n) a) (compose (composeN p n) p)
    exact resonance_compose _ _ _ _ ih hres

/-- **Theorem E5: Orbit Void Convergence.**
    Under any endomorphism, the orbit of void stays at void forever.
    Void is the universal fixed point.
    Literary meaning: silence, once established, is permanent under
    every interpretation. -/
theorem orbit_void_stable (g : Endo I) (n : ℕ) :
    Nat.iterate g.f n (void : I) = void := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Nat.iterate g.f n (g.f void) = void
    rw [g.map_void, ih]

/-! ================================================================
    CLUSTER 6: MULTI-ENDOMORPHISM INTERACTIONS
    ================================================================ -/

/-- **Theorem F1: Translation Round-Trip Depth Bound.**
    Applying two depth-decreasing maps in sequence (a "round-trip
    translation") produces depth bounded by the original.
    Literary meaning: translating Homer into English and back
    produces something at most as deep as the original Greek. -/
theorem translation_roundtrip (f g : DepthDec I) (a : I) :
    depth (f.f (g.f a)) ≤ depth a :=
  le_trans (f.depth_le (g.f a)) (g.depth_le a)

/-- **Theorem F2: Double Strict Descent.**
    Two strict decay maps composed produce even faster convergence.
    If both f and g are strictly decreasing and depth(a) > 1,
    then depth(f(g(a))) < depth(a).
    Literary meaning: passing a text through two simplifying
    interpretations compounds the loss. -/
theorem double_strict_descent (f g : StrictDec I) {a : I}
    (ha : depth a > 1) :
    depth (f.f (g.f a)) < depth a := by
  have hg : depth (g.f a) ≤ depth a := g.depth_le a
  by_cases hga : depth (g.f a) > 1
  · calc depth (f.f (g.f a)) < depth (g.f a) := f.strict (g.f a) hga
      _ ≤ depth a := hg
  · push_neg at hga
    calc depth (f.f (g.f a)) ≤ depth (g.f a) := f.depth_le (g.f a)
      _ ≤ 1 := hga
      _ < depth a := ha

/-- **Theorem F3: Endomorphism Chain Depth.**
    A chain of three depth-decreasing endomorphisms applied to an idea
    still produces something of bounded depth. -/
theorem triple_endo_depth (f g h : DepthDec I) (a : I) :
    depth (f.f (g.f (h.f a))) ≤ depth a :=
  le_trans (f.depth_le _) (le_trans (g.depth_le _) (h.depth_le a))

/-- **Theorem F4: Resonance Persistence Under Endo Chains.**
    If a ~ b and two maps both preserve resonance,
    then f(g(a)) ~ f(g(b)).
    Literary meaning: resonance survives iterated reinterpretation
    as long as each method individually preserves it. -/
theorem resonance_chain_persistence
    (f g : I → I)
    (hf : ∀ x y : I, resonates x y → resonates (f x) (f y))
    (hg : ∀ x y : I, resonates x y → resonates (g x) (g y))
    {a b : I} (h : resonates a b) :
    resonates (f (g a)) (f (g b)) :=
  hf _ _ (hg _ _ h)

/-! ================================================================
    CLUSTER 7: DEPTH FILTRATION AND STRATIFICATION
    ================================================================ -/

/-- The depth filtration: F_n = {a : depth(a) ≤ n}. -/
def InFiltration (a : I) (n : ℕ) : Prop := depth a ≤ n

/-- **Theorem G1: Filtration Composition Closure.**
    Composing an element of F_m with an element of F_n yields an
    element of F_{m+n}. The filtration is compatible with composition.
    Literary meaning: combining ideas of bounded complexity
    produces ideas of bounded composite complexity. -/
theorem filtration_compose_closed {a b : I} {m n : ℕ}
    (ha : InFiltration a m) (hb : InFiltration b n) :
    InFiltration (compose a b) (m + n) := by
  unfold InFiltration at *
  calc depth (compose a b) ≤ depth a + depth b := depth_compose_le a b
    _ ≤ m + n := Nat.add_le_add ha hb

/-- **Theorem G2: Filtration Endomorphism Invariance.**
    Depth-decreasing endomorphisms preserve each level of the filtration.
    Literary meaning: a simplifying interpretation never moves an idea
    to a higher stratum—it can only push ideas downward. -/
theorem filtration_endo_invariant (g : DepthDec I) {a : I} {n : ℕ}
    (ha : InFiltration a n) :
    InFiltration (g.f a) n := by
  unfold InFiltration at *
  exact le_trans (g.depth_le a) ha

/-- **Theorem G3: Strict Descent Step.**
    Under strict decay, ideas of depth > 1 descend by at least one
    stratum. If a ∈ F_n and depth(a) > 1, then f(a) ∈ F_{n-1}.
    Literary meaning: each round of simplifying interpretation
    strips away at least one layer of complexity. -/
theorem strict_descent_step (g : StrictDec I) {a : I} {n : ℕ}
    (ha : InFiltration a n) (hd : depth a > 1) :
    InFiltration (g.f a) (n - 1) := by
  unfold InFiltration at *
  have := g.strict a hd
  omega

/-- **Theorem G4: Void Lives in F_0.**
    The void (silence) is in every level of the filtration. -/
theorem void_in_filtration (n : ℕ) :
    InFiltration (void : I) n := by
  unfold InFiltration
  rw [depth_void]
  exact Nat.zero_le n

/-- **Theorem G5: Filtration Nesting.**
    F_m ⊆ F_n whenever m ≤ n. The filtration is monotone.
    Literary meaning: the set of ideas of bounded complexity
    grows as the bound increases. -/
theorem filtration_nesting {a : I} {m n : ℕ} (hmn : m ≤ n)
    (ha : InFiltration a m) :
    InFiltration a n := by
  unfold InFiltration at *
  omega

/-- **Theorem G6: Triple Composition Filtration.**
    Composing three elements from filtration levels m, n, k
    yields an element of F_{m+n+k}. -/
theorem triple_filtration {a b c : I} {m n k : ℕ}
    (ha : InFiltration a m) (hb : InFiltration b n)
    (hc : InFiltration c k) :
    InFiltration (compose (compose a b) c) (m + n + k) := by
  apply filtration_compose_closed
  · exact filtration_compose_closed ha hb
  · exact hc

/-! ================================================================
    ADDITIONAL STRUCTURAL RESULTS
    ================================================================ -/

/-- **Theorem H1: Resonant Idempotent Left Absorption.**
    If a is idempotent and a ~ b, then (a∘b) ~ (a∘a) = a∘a.
    By R3 with a ~ a (refl) and b ~ a (symm of h).
    Literary meaning: combining a self-reinforcing text with something
    it resonates with produces something that resonates with the
    text's self-dialogue. -/
theorem resonant_idempotent_left {a b : I}
    (hres : resonates a b) :
    resonates (compose a b) (compose a a) :=
  resonance_compose a a b a (resonance_refl a) (resonance_symm a b hres)

/-- **Theorem H2: Resonant Idempotent Right Absorption.**
    If a ~ b, then (a∘b) ~ (b∘b). -/
theorem resonant_idempotent_right {a b : I}
    (hres : resonates a b) :
    resonates (compose a b) (compose b b) :=
  resonance_compose a b b b hres (resonance_refl b)

/-- **Theorem H3: ComposeN Depth Non-Negative.**
    Traditions always have non-negative depth (as natural numbers). -/
theorem composeN_depth_nonneg (a : I) (n : ℕ) :
    0 ≤ depth (composeN a n) :=
  Nat.zero_le _

/-- **Theorem H4: Void ComposeN.**
    The tradition of void is always void, regardless of length. -/
theorem void_composeN (n : ℕ) : composeN (void : I) n = void := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show compose (composeN void n) void = void
    rw [void_right, ih]

/-- **Theorem H5: Double Composition Resonance.**
    If a ~ b, then (a∘a) ~ (b∘b): self-compositions of resonant
    ideas are resonant.
    Literary meaning: if two ideas resonate, their respective
    self-reinforcements also resonate. -/
theorem double_compose_resonance {a b : I}
    (h : resonates a b) :
    resonates (compose a a) (compose b b) :=
  resonance_compose a b a b h h

/-- **Theorem H6: Fixed Point Under Iteration.**
    If f(a) = a, then f^n(a) = a for all n.
    Literary meaning: a canonical text remains canonical under
    any number of repeated interpretations. -/
theorem fixed_point_iterate (g : Endo I) {a : I}
    (hfix : g.f a = a) (n : ℕ) :
    Nat.iterate g.f n a = a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Nat.iterate g.f n (g.f a) = a
    rw [hfix, ih]

end IDT.Advanced
