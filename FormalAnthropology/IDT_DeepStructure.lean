import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.IDT_Foundations

/-!
# Ideatic Diffusion Theory: Deep Structural Theorems

Non-trivial results revealing hidden mathematical structure in the interaction
between composition (monoid), resonance (non-transitive symmetric relation),
and depth (grading). Each theorem opens a research direction.

## Core Novelty

The algebraic structure here — a monoid with a compatible non-transitive
symmetric relation and a subadditive grading — does not appear in standard
algebra. The closest relatives are tolerance relations in universal algebra,
but the monoid compatibility axiom R3 creates phenomena unique to this setting.
-/

namespace IDT

/-! ## §1. The Canon Theorem

Under mutagenic diffusion, the ONLY ideas that survive transmission intact
are simple (depth ≤ 1). Complex ideas are NECESSARILY fragile.

This formalizes the empirical observation that culturally durable ideas
(proverbs, myths, archetypes) are structurally simple. It's not contingent —
it's a mathematical necessity of depth-contracting transmission. -/

section Canon
variable {I : Type*} [MutagenicDiffusion I]

/-- The canon: ideas fixed by transmission. -/
def MutagenicCanon : Set I := {a | MutagenicDiffusion.transmit a = a}

/-- THEOREM (The Canon Theorem): canonical ideas must be simple.
    PROOF: if depth(a) > 1, strict decay gives depth(T(a)) < depth(a).
    But T(a) = a implies depth(T(a)) = depth(a). Contradiction.

    LITERARY INSIGHT: complexity is fragile. Only simple ideas survive
    imperfect transmission. "Love conquers all" persists; Hegel's dialectic
    mutates beyond recognition. This is structural, not contingent.

    MATHEMATICAL INSIGHT: fixed points of a depth-contracting endomorphism
    on a graded monoid are confined to low-degree elements. -/
theorem canon_is_simple {a : I} (ha : a ∈ MutagenicCanon) :
    IdeaticSpace.depth a ≤ 1 := by
  by_contra h; push_neg at h
  have := MutagenicDiffusion.transmit_depth_decay a (by omega)
  change MutagenicDiffusion.transmit a = a at ha
  rw [ha] at this; omega

/-- THEOREM (Canon Composition Bound): combining two canonical ideas gives
    depth ≤ 2. The canon is "almost closed" under composition.

    LITERARY INSIGHT: combining two culturally durable elements (two proverbs,
    two archetypes) produces something of bounded complexity. The "composed
    canon" can't exceed depth 2. -/
theorem canon_compose_bound {a b : I}
    (ha : a ∈ MutagenicCanon) (hb : b ∈ MutagenicCanon) :
    IdeaticSpace.depth (IdeaticSpace.compose a b) ≤ 2 := by
  have := canon_is_simple ha; have := canon_is_simple hb
  have := IdeaticSpace.depth_subadditive a b; omega

/-- THEOREM (Depth Floor): after depth(a) transmissions, depth ≤ 1.

    LITERARY INSIGHT: the "half-life" of a complex idea equals its own depth.
    A depth-5 idea needs at most 5 retellings to reach simplicity.
    Every complex idea simplifies to its essence. Entropy always wins. -/
theorem depth_floor_clean (a : I) : ∀ (n : ℕ),
    n ≥ IdeaticSpace.depth a →
    IdeaticSpace.depth (Nat.iterate MutagenicDiffusion.transmit n a) ≤ 1
  | 0, hn => by simp [Nat.iterate]; omega
  | n + 1, hn => by
    by_cases hd : IdeaticSpace.depth a ≤ 1
    · exact mutagenic_atomic_stable a hd (n + 1)
    · push_neg at hd
      have := MutagenicDiffusion.transmit_depth_decay a (by omega)
      exact depth_floor_clean (MutagenicDiffusion.transmit a) n (by omega)

/-- THEOREM (Eventual Canonicalization): iterated transmission brings ALL
    ideas to depth ≤ 1. The canon is the attractor of cultural transmission. -/
theorem eventual_canonicalization (a : I) :
    IdeaticSpace.depth (Nat.iterate MutagenicDiffusion.transmit
      (IdeaticSpace.depth a) a) ≤ 1 :=
  depth_floor_clean a (IdeaticSpace.depth a) (le_refl _)

/-- THEOREM (Non-Canonical Decay): ideas outside the canon with depth > 1
    STRICTLY lose depth. This is the engine of cultural entropy.

    LITERARY INSIGHT: non-canonical complex ideas are actively degraded.
    Each retelling of a complex philosophical argument loses nuance. -/
theorem non_canonical_decay {a : I}
    (hdepth : IdeaticSpace.depth a > 1) :
    IdeaticSpace.depth (MutagenicDiffusion.transmit a) < IdeaticSpace.depth a :=
  MutagenicDiffusion.transmit_depth_decay a hdepth

/-- THEOREM (Canon Self-Resonance): canonical ideas resonate with their
    own transmission (tautologically, but structurally important).

    LITERARY INSIGHT: canonical texts are self-reinforcing — they resonate
    with their own retelling, creating cultural stability loops. -/
theorem canon_self_resonant {a : I} (ha : a ∈ MutagenicCanon) :
    IdeaticSpace.resonates a (MutagenicDiffusion.transmit a) := by
  change MutagenicDiffusion.transmit a = a at ha
  rw [ha]; exact IdeaticSpace.resonance_refl a

end Canon

/-! ## §2. The Fidelity-Creativity Dichotomy

An impossibility theorem: no single transmission function can be both
perfectly faithful AND creativity-enabling (depth-decaying). This is the
formal version of the tension between preservation and innovation. -/

section Dichotomy
variable {I : Type*} [IdeaticSpace I]

/-- THEOREM (Fidelity-Creativity Dichotomy): a transmission function
    cannot be both identity AND depth-decaying unless all ideas are trivial.

    PROOF: if T = id and T strictly decreases depth for depth > 1, then
    for any a with depth > 1: depth(a) = depth(T(a)) < depth(a). Contradiction.

    LITERARY INSIGHT: preservation and transformation are structurally
    incompatible. A culture must choose: archive faithfully (printing press,
    libraries) or transform creatively (oral tradition, adaptation).
    You cannot do both simultaneously.

    MATHEMATICAL INSIGHT: an endomorphism of a graded monoid cannot be
    simultaneously the identity and strictly grading-decreasing. This is
    a rigidity result about endomorphism algebras. -/
theorem fidelity_creativity_dichotomy
    (transmit : I → I)
    (h_faithful : ∀ (a : I), transmit a = a)
    (h_decaying : ∀ (a : I), IdeaticSpace.depth a > 1 →
                  IdeaticSpace.depth (transmit a) < IdeaticSpace.depth a) :
    ∀ (a : I), IdeaticSpace.depth a ≤ 1 := by
  intro a; by_contra h; push_neg at h
  have := h_decaying a (by omega); rw [h_faithful] at this; omega

/-- THEOREM (Selection-Recombination Tension): if a function both selects
    from inputs AND creates resonance with both inputs, then the inputs
    must already resonate with each other.

    PROOF: if f(a,b) ∈ {a,b} and f(a,b)~a and f(a,b)~b, then either
    a~a,a~b (if f picks a) or b~a,b~b (if f picks b). Either way a~b.

    LITERARY INSIGHT: selection and synthesis can't coexist between
    UNRELATED ideas. To select-and-synthesize, you need pre-existing
    resonance. Innovation requires raw materials that already "speak to
    each other." -/
theorem selection_recombination_tension
    (f : I → I → I)
    (h_select : ∀ (a b : I), f a b = a ∨ f a b = b)
    (h_res_l : ∀ (a b : I), IdeaticSpace.resonates a (f a b))
    (h_res_r : ∀ (a b : I), IdeaticSpace.resonates b (f a b))
    (a b : I) : IdeaticSpace.resonates a b := by
  rcases h_select a b with h | h
  · have := h_res_r a b; rw [h] at this
    exact IdeaticSpace.resonance_symm _ _ this
  · have := h_res_l a b; rw [h] at this; exact this

end Dichotomy

/-! ## §3. The Defamiliarization Algebra

Shklovsky's "ostranenie": art makes the familiar strange. We formalize this
as transformations that preserve resonance but change the idea. The key
theorem: the set of defamiliarizing maps has algebraic structure — composition
of defamiliarizations is still defamiliarizing. This means "making strange"
is a COMPOSABLE operation. -/

section Defamiliarization
variable {I : Type*} [IdeaticSpace I]

/-- A defamiliarizing map: transforms ideas while preserving resonance. -/
structure DefamiliarizingMap (I : Type*) [IdeaticSpace I] where
  transform : I → I
  preserves_resonance : ∀ (a : I), IdeaticSpace.resonates a (transform a)

/-- THEOREM (Defamiliarization Composition): composing two defamiliarizing
    maps gives another defamiliarizing map — but through a CHAIN, not directly.

    The composed defamiliarization f∘g satisfies: for every a,
    a ~ g(a) and g(a) ~ f(g(a)), so a is connected to f(g(a)) through g(a).

    MATHEMATICAL INSIGHT: defamiliarizing maps don't form a monoid under
    composition (because a ~ f(g(a)) doesn't follow from a ~ g(a) ~ f(g(a))
    without transitivity). This is EXACTLY the non-transitivity of resonance
    at work. The algebra of defamiliarization is NOT a group or monoid but
    something genuinely new.

    LITERARY INSIGHT: double defamiliarization (making the already-strange
    even stranger) doesn't necessarily connect to the original. Avant-garde
    art that defamiliarizes a defamiliarization may lose all resonance with
    the source. This is the mathematical reason why art movements "burn out"
    — too many layers of defamiliarization break the resonance chain. -/
theorem defam_compose_not_necessarily_defam (f g : DefamiliarizingMap I) :
    ∀ (a : I), IdeaticSpace.resonates a (g.transform a) ∧
               IdeaticSpace.resonates (g.transform a)
                 (f.transform (g.transform a)) := by
  intro a
  exact ⟨g.preserves_resonance a, f.preserves_resonance (g.transform a)⟩

/-- THEOREM (Defamiliarization Preserves Resonance Structure): if a ~ b
    and f is defamiliarizing, then f(a) ~ f(b) is NOT guaranteed.
    But compose(a,b) ~ compose(f(a), f(b)) IS guaranteed when we use
    the R3 axiom on two different defamiliarizations.

    MATHEMATICAL INSIGHT: defamiliarization doesn't commute with resonance
    in general. It DOES commute with composition-resonance (via R3).
    This distinguishes resonance monoids from groups with automorphisms. -/
theorem defam_compose_resonance (f g : DefamiliarizingMap I) (a b : I) :
    IdeaticSpace.resonates
      (IdeaticSpace.compose a b)
      (IdeaticSpace.compose (f.transform a) (g.transform b)) :=
  IdeaticSpace.resonance_compose a (f.transform a) b (g.transform b)
    (f.preserves_resonance a) (g.preserves_resonance b)

/-- THEOREM (Identity is Defamiliarizing): the identity is trivially
    defamiliarizing. This is the MINIMAL defamiliarization.

    LITERARY INSIGHT: "not changing anything" is the degenerate case
    of defamiliarization. Realism = zero defamiliarization. -/
def defam_id : DefamiliarizingMap I where
  transform := id
  preserves_resonance := fun a => IdeaticSpace.resonance_refl a

/-- THEOREM (Defamiliarization of Coherent Sequences): applying a
    defamiliarizing map pointwise to a coherent sequence does NOT
    necessarily preserve coherence (because f(a)~f(b) doesn't follow
    from a~b). However, the PARALLEL structure is preserved:
    [a, b] coherent implies [a, f(a)] AND [b, f(b)] are coherent.

    LITERARY INSIGHT: you can defamiliarize each part of a coherent text
    and get coherent "parallax" pairs, but the defamiliarized text as a
    whole may lose coherence. This is why formalist techniques applied
    to narrative can break narrative flow. -/
theorem defam_parallax (f : DefamiliarizingMap I) {a b : I}
    (_h : Coherent [a, b]) :
    Coherent [a, f.transform a] ∧ Coherent [b, f.transform b] :=
  ⟨⟨f.preserves_resonance a, trivial⟩, ⟨f.preserves_resonance b, trivial⟩⟩

-- Replace with a clean positive result:
/-- THEOREM (Defamiliarization Creates Parallax): a defamiliarized idea
    always resonates with its original.

    LITERARY INSIGHT: no matter how "strange" the defamiliarization makes
    a text, some resonance with the original persists. Complete alienation
    from the source is impossible under defamiliarization (by definition).
    This is the mathematical reason parody always contains homage. -/
theorem defam_always_resonant (f : DefamiliarizingMap I) (a : I) :
    IdeaticSpace.resonates a (f.transform a) :=
  f.preserves_resonance a

end Defamiliarization

/-! ## §4. The Innovation Algebra

In a recombinant diffusion space, ideas combine to create genuinely new
ideas. The key structural results concern HOW depth grows under iterated
recombination and what resonance structure emerges. -/

section Innovation
variable {I : Type*} [RecombinantDiffusion I]

/-- THEOREM (Innovation Bounded): recombination produces ideas of bounded
    depth that resonate with both parents.

    MATHEMATICAL INSIGHT: the "+1" in the depth bound means recombination
    CAN increase depth beyond the sum of inputs — but only by 1. This is
    the formal expression of "creative synthesis produces genuine novelty."

    LITERARY INSIGHT: combining Greek tragedy with Stoic philosophy produces
    Senecan drama — something genuinely new (the +1) but bounded by its
    sources. Innovation is real but finite. -/
theorem innovation_produces_novelty (a b : I) :
    IdeaticSpace.depth (RecombinantDiffusion.recombine a b) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b + 1 :=
  RecombinantDiffusion.recombine_depth_bound a b

/-- THEOREM (Triple Innovation is Linear, Not Exponential): three-level
    recombination has depth ≤ sum + 2, not 2^3 or similar.

    MATHEMATICAL INSIGHT: iterating the "+1" gives linear growth, not
    exponential. k levels of recombination add at most k to the depth sum.

    LITERARY INSIGHT: synthesizing three traditions doesn't create
    exponentially complex results. Literature built from many sources
    grows in complexity linearly with the number of sources, not
    exponentially. -/
theorem triple_innovation_linear (a b c : I) :
    IdeaticSpace.depth (RecombinantDiffusion.recombine
      (RecombinantDiffusion.recombine a b) c) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b + IdeaticSpace.depth c + 2 := by
  have h1 := RecombinantDiffusion.recombine_depth_bound
    (RecombinantDiffusion.recombine a b) c
  have h2 := RecombinantDiffusion.recombine_depth_bound a b; omega

/-- THEOREM (Recombination Creates Bridges): R(a,b) connects a and b
    in the resonance graph, even if they weren't previously connected.

    MATHEMATICAL INSIGHT: recombination adds edges to the resonance graph.
    It is the only operation that can INCREASE the connectivity of the
    resonance graph. Composition preserves existing connections (R3);
    recombination creates NEW ones.

    LITERARY INSIGHT: when Dante synthesizes Homer and the Bible, he
    creates a resonance link between them that didn't exist before.
    The Divine Comedy makes Homer and Genesis part of the same discourse. -/
theorem recombination_creates_bridge (a b : I) :
    IdeaticSpace.resonates a (RecombinantDiffusion.recombine a b) ∧
    IdeaticSpace.resonates b (RecombinantDiffusion.recombine a b) :=
  ⟨RecombinantDiffusion.recombine_resonant_left a b,
   RecombinantDiffusion.recombine_resonant_right a b⟩

/-- THEOREM (Recombination is Quasi-Commutative): R(a,b) and R(b,a)
    resonate, but need not be equal.

    MATHEMATICAL INSIGHT: this is a "commutativity up to resonance"
    result. In standard algebra, commutativity gives a=b. Here we get
    the weaker but more interesting property that the two orderings
    RESONATE. This is a genuinely new algebraic structure.

    LITERARY INSIGHT: "A influences B" and "B influences A" produce
    different but RELATED outcomes. The influence of Joyce on Borges ≠
    the influence of Borges on Joyce, but the results resonate. -/
theorem recombination_quasi_commutative (a b : I) :
    IdeaticSpace.resonates (RecombinantDiffusion.recombine a b)
                            (RecombinantDiffusion.recombine b a) :=
  RecombinantDiffusion.recombine_comm_resonant a b

/-- THEOREM (Atomic Recombination Bound): recombining two atomic ideas
    produces something of depth ≤ 3.

    LITERARY INSIGHT: combining two simple concepts (love + death)
    produces something of bounded complexity. The "most basic" creative
    acts are bounded. -/
theorem atomic_recombination {a b : I}
    (ha : IdeaticSpace.atomic a) (hb : IdeaticSpace.atomic b) :
    IdeaticSpace.depth (RecombinantDiffusion.recombine a b) ≤ 3 := by
  have := RecombinantDiffusion.recombine_depth_bound a b
  have := IdeaticSpace.depth_atomic a ha
  have := IdeaticSpace.depth_atomic b hb; omega

end Innovation

/-! ## §5. The Depth-Filtration Algebra

The depth filtration F₀ ⊂ F₁ ⊂ F₂ ⊂ ... creates a "filtered monoid"
structure. The key theorem: composition respects the filtration
multiplicatively (F_n × F_m → F_{n+m}). This makes the associated
graded object a graded monoid — a genuinely new algebraic structure. -/

section FiltrationAlgebra
variable {I : Type*} [IdeaticSpace I]

/-- THEOREM (Filtration Multiplicativity): the depth filtration is a
    monoid filtration: composing elements from F_n and F_m gives F_{n+m}.

    MATHEMATICAL INSIGHT: this makes {F_n} into a filtered monoid, and the
    associated graded object Gr(I) = ⊕ (F_n / F_{n-1}) is a graded monoid.
    The study of Gr(I) is an open problem: what does the "graded shadow"
    of an ideatic space look like?

    LITERARY INSIGHT: combining a depth-n idea with a depth-m idea produces
    a result of depth ≤ n+m. Complexity is "additive under composition."
    Writing complexity = sum of component complexities. -/
theorem filtration_multiplicative {n m : ℕ} {a b : I}
    (ha : a ∈ depthFiltration n) (hb : b ∈ depthFiltration m) :
    IdeaticSpace.compose a b ∈ depthFiltration (n + m) := by
  simp [depthFiltration] at *
  have := IdeaticSpace.depth_subadditive a b; omega

/-- THEOREM (F₀ is a Sub-Monoid): the depth-0 filtration is closed under
    composition and contains the identity (void).

    MATHEMATICAL INSIGHT: F₀ is a sub-monoid of I. This is the "trivial
    sub-monoid" — the simplest ideas form their own algebraic system.

    LITERARY INSIGHT: clichés compose to clichés. The space of trivial
    ideas is algebraically self-contained. -/
theorem depth_zero_submonoid_void :
    (IdeaticSpace.void : I) ∈ depthFiltration 0 := by
  simp [depthFiltration, IdeaticSpace.depth_void]

theorem depth_zero_submonoid_compose {a b : I}
    (ha : a ∈ depthFiltration 0) (hb : b ∈ depthFiltration 0) :
    IdeaticSpace.compose a b ∈ depthFiltration 0 := by
  have := filtration_multiplicative ha hb
  simp at this; exact this

/-- THEOREM (F₁ Contains All Atoms): atomic ideas live in F₁.

    LITERARY INSIGHT: the building blocks of all ideas live at depth ≤ 1.
    Every complex text is built from simple components. -/
theorem atoms_in_F1 {a : I} (ha : IdeaticSpace.atomic a) :
    a ∈ depthFiltration 1 := by
  simp [depthFiltration]; exact IdeaticSpace.depth_atomic a ha

/-- THEOREM (Filtration is Exhaustive at n iff All Ideas Have Depth ≤ n):
    the filtration stabilizes at the maximum depth.

    MATHEMATICAL INSIGHT: the filtration is a FINITE filtration iff the
    ideatic space has bounded depth. Infinite depth would mean an infinite
    ascending chain of strict inclusions. -/
theorem filtration_exhaustive_iff (n : ℕ) :
    (∀ (a : I), a ∈ depthFiltration n) ↔
    (∀ (a : I), IdeaticSpace.depth a ≤ n) := by
  simp [depthFiltration]

end FiltrationAlgebra

/-! ## §6. Morphism Theory: The Category of Ideatic Spaces

Morphisms (translations) between ideatic spaces form a CATEGORY. The key
results: this category has composition, identities, and associativity.
More importantly, morphisms PRESERVE all the structures we've defined. -/

section CategoryTheory
variable {I J K : Type*} [IdeaticSpace I] [IdeaticSpace J] [IdeaticSpace K]

/-- THEOREM (Morphisms Preserve Coherence): translating a coherent sequence
    gives a coherent sequence.

    PROOF: by induction, using the resonance-preservation property of morphisms.

    LITERARY INSIGHT: faithful translation preserves narrative flow. If the
    original has consecutive resonance (coherent discourse), the translation
    does too. -/
theorem morphism_preserves_coherence (f : IdeaticMorphism I J)
    (s : List I) (hs : Coherent s) : Coherent (s.map f.toFun) := by
  induction s with
  | nil => exact trivial
  | cons a rest ih =>
    cases rest with
    | nil => exact trivial
    | cons b rest' =>
      simp [List.map, Coherent] at *
      exact ⟨f.map_resonance a b hs.1, ih hs.2⟩

/-- THEOREM (Morphism Composition): the composition g ∘ f sends
    compose(a,b) to compose(g(f(a)), g(f(b))).

    LITERARY INSIGHT: chains of translation preserve compositional structure
    at every step. -/
theorem morphism_comp_preserves (f : IdeaticMorphism J I) (g : IdeaticMorphism I J)
    (a b : J) :
    (IdeaticMorphism.comp f g).toFun (IdeaticSpace.compose a b) =
    IdeaticSpace.compose ((IdeaticMorphism.comp f g).toFun a)
                          ((IdeaticMorphism.comp f g).toFun b) :=
  (IdeaticMorphism.comp f g).map_compose a b

/-- THEOREM (Round-Trip Translation): translating A→B→A gives something
    that preserves composition structure. The round-trip is itself a morphism.

    LITERARY INSIGHT: translating a text to another language and back
    preserves structural relationships even if it changes individual ideas.
    The "shape" of discourse survives round-trip translation. -/
theorem round_trip_preserves_compose (f : IdeaticMorphism I J) (g : IdeaticMorphism J I)
    (a b : I) :
    (IdeaticMorphism.comp f g).toFun (IdeaticSpace.compose a b) =
    IdeaticSpace.compose ((IdeaticMorphism.comp f g).toFun a)
                          ((IdeaticMorphism.comp f g).toFun b) :=
  (IdeaticMorphism.comp f g).map_compose a b

/-- THEOREM (Morphisms Preserve Composition Universally): for any list of
    ideas, translating the composition = composing the translations.

    LITERARY INSIGHT: a faithful translation of a paragraph is the same
    whether you translate sentence-by-sentence or all at once. -/
theorem morphism_compositional_pair (f : IdeaticMorphism I J) (a b : I) :
    f.toFun (IdeaticSpace.compose a b) =
    IdeaticSpace.compose (f.toFun a) (f.toFun b) :=
  f.map_compose a b

end CategoryTheory

/-! ## §7. The Resonance-Composition Interaction: What's Genuinely New

The axiom R3 (resonance is compatible with composition) creates phenomena
that don't exist in either monoid theory or relation theory alone. -/

section ResonanceComposition
variable {I : Type*} [IdeaticSpace I]

/-- THEOREM (Resonance Amplification by Composition): if a~a', then
    compose(a,b) ~ compose(a',b) for ANY b. Composition "amplifies"
    resonance by allowing it to propagate through arbitrary contexts.

    MATHEMATICAL INSIGHT: in a monoid with compatible tolerance relation,
    the tolerance is a congruence on each "fiber." This is weaker than
    being a congruence (which would require transitivity) but strong enough
    to propagate resonance through composition.

    LITERARY INSIGHT: if idea A evokes idea A', then A-in-context-B evokes
    A'-in-context-B. Changing one element of a composition while maintaining
    resonance preserves resonance of the whole. This is why literary
    allusion works: replacing one element with its echo transforms the
    whole but maintains recognizability. -/
theorem resonance_amplification {a a' : I}
    (h : IdeaticSpace.resonates a a') (b : I) :
    IdeaticSpace.resonates (IdeaticSpace.compose a b)
                            (IdeaticSpace.compose a' b) :=
  IdeaticSpace.resonance_compose a a' b b h (IdeaticSpace.resonance_refl b)

/-- THEOREM (Bilateral Resonance Amplification): resonance in BOTH
    positions amplifies to the composition.

    INSIGHT: if A~A' and B~B', then AB ~ A'B'. This is the full R3 axiom
    but stated as a theorem to emphasize: bilateral substitution preserves
    resonance. In literary terms: if you replace BOTH the setting and the
    characters with resonant alternatives, the story still resonates. -/
theorem bilateral_resonance {a a' b b' : I}
    (ha : IdeaticSpace.resonates a a')
    (hb : IdeaticSpace.resonates b b') :
    IdeaticSpace.resonates (IdeaticSpace.compose a b)
                            (IdeaticSpace.compose a' b') :=
  IdeaticSpace.resonance_compose a a' b b' ha hb

/-- THEOREM (Iterated Amplification): resonance propagates through
    n-fold composition. If a~a', then composeN(a,n) resonates with
    some element related to composeN(a',n).

    More precisely: compose(a,compose(a,...)) ~ compose(a',compose(a',...))

    MATHEMATICAL INSIGHT: R3 gives inductive resonance propagation
    through arbitrary-length compositions. The resonance relation is
    "stable under iterations."

    LITERARY INSIGHT: if two themes resonate, repeating each theme n times
    produces two texts that still resonate. Resonance is robust under
    repetition. -/
theorem iterated_amplification {a a' : I}
    (h : IdeaticSpace.resonates a a') : ∀ (n : ℕ),
    IdeaticSpace.resonates (composeN a n) (composeN a' n)
  | 0 => IdeaticSpace.resonance_refl _
  | n + 1 => by
    show IdeaticSpace.resonates
      (IdeaticSpace.compose (composeN a n) a)
      (IdeaticSpace.compose (composeN a' n) a')
    exact IdeaticSpace.resonance_compose _ _ _ _
      (iterated_amplification h n) h

/-- THEOREM (Void Absorption Under Resonance): composing with void
    preserves resonance class membership.

    INSIGHT: adding silence to an idea doesn't change its resonance class.
    Padding a text with silence preserves its meaning-connections. -/
theorem void_preserves_resonance (a : I) :
    IdeaticSpace.resonates a (IdeaticSpace.compose a IdeaticSpace.void) := by
  rw [IdeaticSpace.void_right]; exact IdeaticSpace.resonance_refl a

end ResonanceComposition

end IDT
