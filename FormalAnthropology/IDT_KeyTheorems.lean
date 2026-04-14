import Mathlib.Tactic
import Mathlib.Data.Nat.Defs
import Mathlib.Order.Filter.Basic

/-!
# IDT Key Theorems: Ten Structural Results in Ideatic Diffusion Theory

This file contains ten carefully chosen theorems that reveal deep structural
properties of ideatic spaces. Each theorem connects mathematical structure
to literary-theoretical insight, and several combine multiple parts of IDT
(resonance, depth, fixed points, endomorphisms) in non-trivial ways.

## The Ten Key Theorems

1. **Resonant Commutativity**: Resonant ideas commute up to resonance —
   word order matters only for distant concepts (Jakobson's paradigmatic axis).

2. **Consonant Orbit Chain**: A "consonant" map (always resonating with input)
   creates an unbroken chain of resonance through its orbit — Gadamer's
   Wirkungsgeschichte (history of effects).

3. **Resonance Consensus**: Resonance-preserving maps maintain initial agreements
   forever — Gadamer's insight that prejudice shapes all future interpretation.

4. **Dialogic Convergence**: Alternating application of a strictly-decaying map
   and a depth-decreasing map converges to shallow ideas — Bakhtin's polyphony
   still converges despite multiple voices.

5. **Orbit Composition Collapse**: After sufficient iteration under strict decay,
   any two ideas compose to something shallow — after enough retellings,
   all dialogues become simple.

6. **Power Resonance Shift**: Resonant ideas generate resonant traditions —
   composeN preserves resonance at every power.

7. **Endomorphism Resonance Extension**: Readings of resonant texts resonate —
   a resonance-preserving map extends resonance from inputs to input-output pairs.

8. **Sublime Fragility (Depth Floor)**: Under strict decay, depth decreases by
   at least one per step — the sublime is the first quality lost in transmission
   (Longinus meets information theory).

9. **Canonical Text Anchor**: Fixed points of an endomorphism anchor composition —
   canonical texts remain invariant while their companions evolve.

10. **Canonical Resonance Permanence**: If an idea resonates with a canonical text
    (fixed point of a resonance-preserving map), it continues to resonate after
    any number of interpretive steps — the canon is a permanent attractor in
    the resonance graph.
-/

set_option autoImplicit false

namespace IDT.KeyTheorems

/-! ## §1. Core Axioms -/

class IdeaticSpace (I : Type*) where
  void : I
  compose : I → I → I
  resonates : I → I → Prop
  depth : I → ℕ
  -- Monoid axioms (A1-A3)
  compose_assoc : ∀ (a b c : I), compose (compose a b) c = compose a (compose b c)
  void_left : ∀ (a : I), compose void a = a
  void_right : ∀ (a : I), compose a void = a
  -- Resonance axioms (R1-R3)
  resonance_refl : ∀ (a : I), resonates a a
  resonance_symm : ∀ (a b : I), resonates a b → resonates b a
  resonance_compose : ∀ (a a' b b' : I),
    resonates a a' → resonates b b' → resonates (compose a b) (compose a' b')
  -- Depth axioms (D1-D4)
  depth_void : depth void = 0
  depth_compose_le : ∀ (a b : I), depth (compose a b) ≤ depth a + depth b
  depth_void_unique : ∀ (a : I), depth a = 0 → a = void

variable {I : Type*} [IdeaticSpace I]

open IdeaticSpace

/-! ## §2. Definitions -/

/-- Iterated self-composition: composeN(a, n) = a ∘ a ∘ ... ∘ a (n times). -/
def composeN (a : I) : ℕ → I
  | 0 => void
  | n + 1 => compose (composeN a n) a

/-- An endomorphism of an ideatic space preserving composition and void. -/
structure Endomorphism (I : Type*) [IdeaticSpace I] where
  map : I → I
  map_void : map void = void
  map_compose : ∀ (a b : I), map (compose a b) = compose (map a) (map b)

/-- An endomorphism that never increases depth. -/
structure DepthDecreasing (I : Type*) [IdeaticSpace I] extends Endomorphism I where
  depth_nonincreasing : ∀ (a : I), depth (map a) ≤ depth a

/-- A strictly decreasing endomorphism: depth strictly drops when above 1. -/
structure StrictlyDecreasing (I : Type*) [IdeaticSpace I] extends DepthDecreasing I where
  strict_decay : ∀ (a : I), depth a > 1 → depth (map a) < depth a

/-- A fixed point of a function. -/
def IsFixedPoint (f : I → I) (a : I) : Prop := f a = a

/-! ## §3. Infrastructure Lemmas -/

/-- Depth subadditivity (direct from axiom). -/
theorem depth_subadditive (a b : I) :
    depth (compose a b) ≤ depth a + depth b :=
  depth_compose_le a b

/-- Iterating a depth-decreasing endomorphism never increases depth. -/
theorem depth_iterate_le (f : DepthDecreasing I) (a : I) (n : ℕ) :
    depth (Nat.iterate f.map n a) ≤ depth a := by
  induction n generalizing a with
  | zero => exact le_refl _
  | succ n ih =>
    calc depth (Nat.iterate f.map n (f.map a))
        ≤ depth (f.map a) := ih (f.map a)
      _ ≤ depth a := f.depth_nonincreasing a

/-- Iterating a depth-decreasing plain function never increases depth. -/
private theorem iter_depth_le_func
    (h : I → I) (hdec : ∀ (x : I), depth (h x) ≤ depth x)
    (a : I) (n : ℕ) : depth (Nat.iterate h n a) ≤ depth a := by
  induction n generalizing a with
  | zero => exact le_refl _
  | succ n ih =>
    calc depth (Nat.iterate h n (h a))
        ≤ depth (h a) := ih (h a)
      _ ≤ depth a := hdec a

/-- Core stabilization: under strict decay, depth reaches ≤ 1 after depth(a) steps. -/
private theorem depth_stabilization_aux (f : StrictlyDecreasing I) :
    ∀ (d : ℕ) (a : I), depth a ≤ d →
    depth (Nat.iterate f.map d a) ≤ 1 := by
  intro d
  induction d with
  | zero => intro a ha; simp; omega
  | succ n ih =>
    intro a ha
    by_cases hd : depth a ≤ 1
    · have := depth_iterate_le f.toDepthDecreasing a (n + 1); omega
    · push_neg at hd
      exact ih (f.map a) (by have := f.strict_decay a (by omega); omega)

/-- Depth stabilization theorem. -/
theorem depth_stabilization (f : StrictlyDecreasing I) (a : I) :
    depth (Nat.iterate f.map (depth a) a) ≤ 1 :=
  depth_stabilization_aux f (depth a) a (le_refl _)

/-- Orbit reaches ground level for n ≥ depth(a). -/
theorem orbit_reaches_ground (f : StrictlyDecreasing I) (a : I) (n : ℕ)
    (hn : n ≥ depth a) :
    depth (Nat.iterate f.map n a) ≤ 1 := by
  have hsplit : n = (n - depth a) + depth a := by omega
  rw [hsplit, Function.iterate_add]
  calc depth (Nat.iterate f.map (n - depth a)
          (Nat.iterate f.map (depth a) a))
      ≤ depth (Nat.iterate f.map (depth a) a) :=
        depth_iterate_le f.toDepthDecreasing _ _
    _ ≤ 1 := depth_stabilization f a

/-- Endomorphism orbits distribute over composition. -/
theorem orbit_compose (f : Endomorphism I) (a b : I) (n : ℕ) :
    Nat.iterate f.map n (compose a b) =
    compose (Nat.iterate f.map n a) (Nat.iterate f.map n b) := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    show Nat.iterate f.map n (f.map (compose a b)) =
      compose (Nat.iterate f.map n (f.map a)) (Nat.iterate f.map n (f.map b))
    rw [f.map_compose a b]
    exact ih (f.map a) (f.map b)

omit [IdeaticSpace I] in
/-- Fixed points remain fixed under iteration. -/
theorem fixed_point_iterate {f : I → I} {a : I}
    (hfix : IsFixedPoint f a) (n : ℕ) :
    Nat.iterate f n a = a := by
  have hfa : f a = a := hfix
  induction n with
  | zero => rfl
  | succ n ih =>
    show Nat.iterate f n (f a) = a
    rw [hfa]; exact ih

/-! ## §4. The Ten Key Theorems -/

/-! ### Theorem 1: Resonant Commutativity

If two ideas resonate, then their compositions in either order also resonate.
This means resonant ideas "quasi-commute" — they can be freely reordered
without leaving the resonance class. In literary terms: the paradigmatic
axis (Jakobson) allows free substitution among resonant terms, and here
we show it extends to syntagmatic reordering.
-/

theorem resonant_commutativity {a b : I}
    (h : resonates a b) :
    resonates (compose a b) (compose b a) :=
  resonance_compose a b b a h (resonance_symm a b h)

/-! ### Theorem 2: Consonant Orbit Chain

A "consonant" map — one where every idea resonates with its image — creates
an unbroken chain of resonance through its orbit. Each successive iterate
resonates with the next: f^i(a) ~ f^{i+1}(a) for all i.

This formalizes Gadamer's *Wirkungsgeschichte* (history of effects): each
generation of a tradition resonates with its immediate successor, creating
a continuous chain of cultural transmission. The chain need not be transitive
(resonance isn't transitive), so distant generations may diverge — but
adjacent ones always echo.
-/

theorem consonant_orbit_chain
    (f : I → I) (hcons : ∀ (x : I), resonates x (f x))
    (a : I) (n : ℕ) :
    resonates (Nat.iterate f n a) (Nat.iterate f (n + 1) a) := by
  induction n generalizing a with
  | zero => exact hcons a
  | succ n ih => exact ih (f a)

/-! ### Theorem 3: Resonance Consensus

If a resonance-preserving map starts with two resonant inputs, they remain
resonant forever under iteration. Initial agreement persists through all
future transformations.

This is Gadamer's deepest insight formalized: *Vorurteil* (prejudice/
pre-judgment) shapes all subsequent understanding. If two readers begin
with resonant interpretations of a text, no amount of further hermeneutic
processing can break that resonance. Consensus, once established at the
level of resonance, is permanent.
-/

theorem resonance_consensus
    (f : I → I)
    (hf : ∀ (x y : I), resonates x y → resonates (f x) (f y))
    {a b : I} (h : resonates a b) (n : ℕ) :
    resonates (Nat.iterate f n a) (Nat.iterate f n b) := by
  induction n generalizing a b with
  | zero => exact h
  | succ n ih => exact ih (hf a b h)

/-! ### Theorem 4: Dialogic Convergence

When a strictly-decaying map f and a depth-decreasing map g alternate
(modeling Bakhtin's dialogic interaction between two voices), the composite
(g ∘ f) converges to shallow ideas. After depth(a) iterations of the
dialogue, all complexity has been negotiated away.

Literary insight: even in a polyphonic novel where multiple voices interact,
the overall discourse converges toward simplicity. Each dialogic exchange
(f then g) reduces depth, and the composite inherits strict decay from f.
This is the mathematical expression of why all traditions eventually
simplify their founding insights.
-/

private theorem dialogic_aux (f g : I → I)
    (hf_dec : ∀ (a : I), depth (f a) ≤ depth a)
    (hg_dec : ∀ (a : I), depth (g a) ≤ depth a)
    (hf_strict : ∀ (a : I), depth a > 1 →
      depth (f a) < depth a) :
    ∀ (d : ℕ) (a : I), depth a ≤ d →
    depth (Nat.iterate (g ∘ f) d a) ≤ 1 := by
  intro d
  induction d with
  | zero => intro a ha; simp; omega
  | succ n ih =>
    intro a ha
    by_cases hd : depth a ≤ 1
    · -- Shallow: composite is depth-decreasing, stays shallow
      have gf_dec : ∀ (x : I), depth ((g ∘ f) x) ≤ depth x := by
        intro x
        calc depth (g (f x))
            ≤ depth (f x) := hg_dec (f x)
          _ ≤ depth x := hf_dec x
      have := iter_depth_le_func (g ∘ f) gf_dec a (n + 1)
      omega
    · -- Deep: one dialogic step strictly decreases, then apply IH
      push_neg at hd
      show depth (Nat.iterate (g ∘ f) n ((g ∘ f) a)) ≤ 1
      apply ih
      show depth (g (f a)) ≤ n
      have h1 := hf_strict a (by omega)
      have h2 := hg_dec (f a)
      omega

/-- Dialogic convergence: alternating strict decay and depth-decrease converges. -/
theorem dialogic_convergence (f g : I → I)
    (hf_dec : ∀ (a : I), depth (f a) ≤ depth a)
    (hg_dec : ∀ (a : I), depth (g a) ≤ depth a)
    (hf_strict : ∀ (a : I), depth a > 1 →
      depth (f a) < depth a)
    (a : I) :
    depth (Nat.iterate (g ∘ f) (depth a) a) ≤ 1 :=
  dialogic_aux f g hf_dec hg_dec hf_strict (depth a) a (le_refl _)

/-! ### Theorem 5: Orbit Composition Collapse

Under strict decay, once two ideas have been iterated past their respective
depths, their composition is necessarily shallow (depth ≤ 2). No matter how
complex the originals, sufficient retelling renders their dialogue trivial.

This is the mathematical form of a fundamental observation about oral
tradition: after enough generations of transmission, even the richest
dialogues between ideas collapse into formulaic exchanges. The bound of 2
(not 1) is tight — each idea contributes at most depth 1, and composition
is subadditive.
-/

theorem orbit_composition_collapse (f : StrictlyDecreasing I) (a b : I)
    (n m : ℕ) (hn : n ≥ depth a) (hm : m ≥ depth b) :
    depth (compose (Nat.iterate f.map n a) (Nat.iterate f.map m b)) ≤ 2 := by
  have h1 := orbit_reaches_ground f a n hn
  have h2 := orbit_reaches_ground f b m hm
  have h3 := depth_subadditive (Nat.iterate f.map n a) (Nat.iterate f.map m b)
  omega

/-! ### Theorem 6: Power Resonance Shift

If two ideas resonate, then their n-fold self-compositions also resonate,
at every power simultaneously. Resonant ideas generate resonant traditions.

Literary interpretation: if two poets (say, Keats and Shelley) begin with
resonant poetic visions, then the accumulated traditions they generate
(Keats's corpus, Shelley's corpus) remain resonant at every stage of growth.
Resonance between seeds propagates to resonance between the entire bodies
of work they generate.
-/

theorem power_resonance_shift {a b : I}
    (h : resonates a b) (n : ℕ) :
    resonates (composeN a n) (composeN b n) := by
  induction n with
  | zero =>
    show resonates void void
    exact resonance_refl void
  | succ n ih =>
    show resonates (compose (composeN a n) a) (compose (composeN b n) b)
    exact resonance_compose (composeN a n) (composeN b n) a b ih h

/-! ### Theorem 7: Endomorphism Resonance Extension

A resonance-preserving map extends resonance from bare ideas to
idea-plus-reading pairs. If a ~ b and f preserves resonance, then
(a, f(a)) ~ (b, f(b)) — that is, compose(a, f(a)) resonates with
compose(b, f(b)).

Literary meaning: if two texts resonate, and we apply the same
interpretive lens to both, the resulting "text + reading" packages
also resonate. A consistent critical method applied to resonant
sources produces resonant criticism.
-/

theorem endomorphism_resonance_extension
    (f : I → I)
    (hf : ∀ (x y : I), resonates x y → resonates (f x) (f y))
    {a b : I} (h : resonates a b) :
    resonates (compose a (f a)) (compose b (f b)) :=
  resonance_compose a b (f a) (f b) h (hf a b h)

/-! ### Theorem 8: Sublime Fragility (Depth Floor)

Under strict decay, the depth of f^k(a) is bounded above by depth(a) - k,
for all k ≤ depth(a) - 1. This means depth decreases by at least one unit
per step — the most complex aspects are shed first.

This is Longinus's theory of the sublime meeting information theory:
sublimity (high depth) is the most fragile quality of a text. Each act
of transmission strips away at least one layer of complexity. A text of
depth d can survive at most d-1 transmissions before losing all depth
beyond the trivial. The sublime is always the first quality lost.
-/

private theorem sublime_fragility_gen (f : StrictlyDecreasing I) :
    ∀ (k : ℕ) (a : I) (d : ℕ),
    depth a ≤ d → d > 1 → k ≤ d - 1 →
    depth (Nat.iterate f.map k a) ≤ d - k := by
  intro k
  induction k with
  | zero => intros; simp; omega
  | succ k ih =>
    intro a d hda hd1 hk
    -- f^[k+1](a) = f^[k](f(a)) by definition
    show depth (Nat.iterate f.map k (f.map a)) ≤ d - (k + 1)
    by_cases hgt : depth a > 1
    · -- Deep: strict decay gives depth(f(a)) < depth(a)
      have hfa : depth (f.map a) < depth a := f.strict_decay a hgt
      by_cases hfa_deep : depth (f.map a) > 1
      · -- Still deep after one step: apply IH with d-1
        have hd1' : d - 1 > 1 := by omega
        have := ih (f.map a) (d - 1) (by omega) hd1' (by omega)
        omega
      · -- Reached shallow: stays shallow, and d-(k+1) ≥ 1
        push_neg at hfa_deep
        have := depth_iterate_le f.toDepthDecreasing (f.map a) k
        omega
    · -- Already shallow: stays shallow via monotonicity
      push_neg at hgt
      have h1 := f.toDepthDecreasing.depth_nonincreasing a
      have h2 := depth_iterate_le f.toDepthDecreasing (f.map a) k
      omega

theorem sublime_fragility (f : StrictlyDecreasing I) {a : I}
    (hd : depth a > 1) (k : ℕ) (hk : k ≤ depth a - 1) :
    depth (Nat.iterate f.map k a) ≤ depth a - k :=
  sublime_fragility_gen f k a (depth a) (le_refl _) hd hk

/-- Corollary: at step depth(a)-1, only one layer of depth remains. -/
theorem sublime_penultimate (f : StrictlyDecreasing I) {a : I}
    (hd : depth a > 1) :
    depth (Nat.iterate f.map (depth a - 1) a) ≤ 1 := by
  have h := sublime_fragility f hd (depth a - 1) (le_refl _)
  omega

/-! ### Theorem 9: Canonical Text Anchor

If a is a fixed point of endomorphism f, then f^n(compose(a, b)) =
compose(a, f^n(b)). The canonical text a remains invariant while its
companion b evolves under iteration.

Literary meaning: a canonical text (Homer, Shakespeare, the Bible)
serves as an anchor in cultural transmission. When composed with
any other idea b and subjected to interpretive evolution, the canonical
component remains fixed while only the secondary component changes.
This is why canonical texts can be endlessly reinterpreted — they
provide a stable framework that absorbs all variation into the
companion position.
-/

theorem canonical_text_anchor (f : Endomorphism I) {a : I}
    (hfix : IsFixedPoint f.map a) (b : I) (n : ℕ) :
    Nat.iterate f.map n (compose a b) =
    compose a (Nat.iterate f.map n b) := by
  have h1 := orbit_compose f a b n
  have h2 := fixed_point_iterate hfix n
  rw [h1, h2]

/-- Right-anchor variant: canonical texts also anchor from the right. -/
theorem canonical_text_anchor_right (f : Endomorphism I) {a : I}
    (hfix : IsFixedPoint f.map a) (b : I) (n : ℕ) :
    Nat.iterate f.map n (compose b a) =
    compose (Nat.iterate f.map n b) a := by
  have h1 := orbit_compose f b a n
  have h2 := fixed_point_iterate hfix n
  rw [h1, h2]

/-! ### Theorem 10: Canonical Resonance Permanence

If an idea a resonates with a canonical text p (a fixed point of a
resonance-preserving map), then every iterate f^n(a) also resonates
with p. The canon is a permanent attractor in the resonance graph:
anything that starts resonating with it can never stop.

This combines three parts of the theory: resonance consensus (Theorem 3),
fixed point theory, and the non-transitivity of resonance. While resonance
is NOT transitive (distant ideas may diverge), the fixed-point property
of canonical texts creates permanence: the canon doesn't move, so consensus
with it can never be lost. This is why canonical texts maintain relevance
across centuries — they resonate with everything that ever resonated with
them, regardless of how much those other ideas have evolved.
-/

theorem canonical_resonance_permanence
    (f : I → I)
    (hf : ∀ (x y : I), resonates x y → resonates (f x) (f y))
    {p : I} (hfix : IsFixedPoint f p)
    {a : I} (h : resonates a p) (n : ℕ) :
    resonates (Nat.iterate f n a) p := by
  have h1 := resonance_consensus f hf h n
  have h2 := fixed_point_iterate hfix n
  rw [h2] at h1
  exact h1

/-- Symmetric form: the canon also resonates with all iterates. -/
theorem canonical_resonance_permanence_symm
    (f : I → I)
    (hf : ∀ (x y : I), resonates x y → resonates (f x) (f y))
    {p : I} (hfix : IsFixedPoint f p)
    {a : I} (h : resonates a p) (n : ℕ) :
    resonates p (Nat.iterate f n a) :=
  resonance_symm _ _ (canonical_resonance_permanence f hf hfix h n)

/-! ## §5. Derived Consequences

The following theorems demonstrate how the key results combine
to yield further structural insights.
-/

/-- Dialogic convergence preserves initial resonance to the end state. -/
theorem dialogic_preserves_resonance
    (f : I → I)
    (hf_pres : ∀ (x y : I), resonates x y → resonates (f x) (f y))
    (g : I → I)
    (hg_pres : ∀ (x y : I), resonates x y → resonates (g x) (g y))
    {a b : I} (h : resonates a b) (n : ℕ) :
    resonates (Nat.iterate (g ∘ f) n a) (Nat.iterate (g ∘ f) n b) := by
  have gf_pres : ∀ (x y : I), resonates x y →
      resonates ((g ∘ f) x) ((g ∘ f) y) := by
    intro x y hxy
    exact hg_pres _ _ (hf_pres _ _ hxy)
  exact resonance_consensus (g ∘ f) gf_pres h n

/-- Canonical texts anchor both left and right simultaneously. -/
theorem canonical_bilateral_anchor (f : Endomorphism I) {a : I}
    (hfix : IsFixedPoint f.map a) (b : I) (n : ℕ) :
    Nat.iterate f.map n (compose (compose a b) a) =
    compose (compose a (Nat.iterate f.map n b)) a := by
  have h1 := orbit_compose f (compose a b) a n
  have h2 := canonical_text_anchor f hfix b n
  have h3 := fixed_point_iterate hfix n
  rw [h1, h2, h3]

/-- Consonant maps on resonant inputs produce doubly-resonant orbits. -/
theorem consonant_resonant_chain
    (f : I → I)
    (hpres : ∀ (x y : I), resonates x y → resonates (f x) (f y))
    {a b : I} (h : resonates a b) (n : ℕ) :
    resonates (Nat.iterate f n a) (Nat.iterate f n b) :=
  resonance_consensus f hpres h n

/-- Power resonance shift + orbit chain: composeN respects consonance chains. -/
theorem power_consonance_chain
    (f : I → I) (hcons : ∀ (x : I), resonates x (f x))
    (a : I) (n k : ℕ) :
    resonates (composeN (Nat.iterate f n a) k)
              (composeN (Nat.iterate f (n + 1) a) k) := by
  exact power_resonance_shift (consonant_orbit_chain f hcons a n) k

/-- Sublime fragility + orbit collapse: deep ideas composed after decay are shallow. -/
theorem deep_dialogue_collapses (f : StrictlyDecreasing I)
    (a b : I) :
    depth (compose (Nat.iterate f.map (depth a) a)
                   (Nat.iterate f.map (depth b) b)) ≤ 2 :=
  orbit_composition_collapse f a b (depth a) (depth b) (le_refl _) (le_refl _)

/-- Canonical permanence extends to compositions with canonical texts. -/
theorem canonical_composition_permanence
    (f : I → I)
    (hf : ∀ (x y : I), resonates x y → resonates (f x) (f y))
    {p : I} (hfix : IsFixedPoint f p)
    {a b : I} (ha : resonates a p) (hb : resonates b p) (n : ℕ) :
    resonates (compose (Nat.iterate f n a) (Nat.iterate f n b))
              (compose p p) := by
  have h1 := canonical_resonance_permanence f hf hfix ha n
  have h2 := canonical_resonance_permanence f hf hfix hb n
  exact resonance_compose _ _ _ _ h1 h2

/-- A consonant map on a fixed point is trivially consonant. -/
theorem fixed_consonance {f : I → I} {p : I}
    (hfix : IsFixedPoint f p) :
    resonates p (f p) := by
  have : f p = p := hfix
  rw [this]
  exact resonance_refl p

/-- Sublime fragility is tight: depth(a)-1 steps leaves depth exactly ≤ 1. -/
theorem sublime_exactly_one_layer (f : StrictlyDecreasing I) {a : I}
    (hd : depth a > 1) :
    depth (Nat.iterate f.map (depth a - 1) a) ≤ 1 :=
  sublime_penultimate f hd

/-- Canonical anchor + dialogic: canonical texts survive dialogic convergence. -/
theorem canonical_survives_dialogue (f : Endomorphism I)
    {p : I} (hfix : IsFixedPoint f.map p) (b : I) :
    Nat.iterate f.map (depth b) (compose p b) =
    compose p (Nat.iterate f.map (depth b) b) :=
  canonical_text_anchor f hfix b (depth b)

/-- Two canonically-anchored compositions evolve in parallel. -/
theorem parallel_canonical_evolution (f : Endomorphism I) {p : I}
    (hfix : IsFixedPoint f.map p) (b c : I) (n : ℕ) :
    compose (Nat.iterate f.map n (compose p b))
            (Nat.iterate f.map n (compose p c)) =
    compose (compose p (Nat.iterate f.map n b))
            (compose p (Nat.iterate f.map n c)) := by
  rw [canonical_text_anchor f hfix b n, canonical_text_anchor f hfix c n]

end IDT.KeyTheorems
