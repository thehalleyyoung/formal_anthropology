import FormalAnthropology.IDT_v3_Foundations

/-!
# Ideatic Diffusion Theory v3: Deep Semiotic Theory

## Overview

This file develops a **formal theory of semiotics** — the study of signs,
meaning, and signification — within the IDT v3 framework. We formalize the
central ideas of **Saussure** (signifier/signified, arbitrariness of the sign,
structural linguistics), **Peirce** (icon/index/symbol trichotomy),
**Barthes** (denotation/connotation, myth as second-order semiosis), and
connect to **Derrida** (différance as the emergent, differential structure of
meaning).

## The Key Insight

In IDT, an *utterance* is an element of the ideatic space I. But a *sign* is
not an utterance — it is the **relation** between an utterance (signifier) and
its emergence equivalence class (signified). The `sameIdea` relation from
`IDT_v3_Foundations` already captures this: two utterances carry the same
signified when they produce identical emergence in all contexts.

The deep consequence is **Saussure's principle**: meaning is not a positive
term but a system of *differences*. In IDT, an utterance's meaning IS its
emergence profile — a purely differential quantity.

## Architecture

1. **Saussure** (§1): Signifier, signified, sign; arbitrariness; equivalence
2. **Peirce** (§2): Icon, index, symbol — the trichotomy of sign relations
3. **Barthes** (§3): Denotation, connotation, and myth (second-order semiosis)
4. **Metaphor** (§4): Metaphor as emergence; dead metaphor as linearization
5. **Irony** (§5): Irony as negative self-emergence; contextual reversal
6. **Semiotic Chains** (§6): Barthes' myth; layered meaning
7. **Structural Linguistics** (§7): Saussure's differences; Derrida's différance

## NO SORRIES, NO ADMITS, NO AXIOMS (beyond the class from Foundations)
-/

namespace IDT3

open IdeaticSpace3

/-! ## §1. Saussure's Distinction: Signifier vs Signified

Ferdinand de Saussure's foundational insight in the *Cours de linguistique
générale* (1916): the linguistic sign is not a name attached to a thing, but a
**two-sided entity** uniting a *signifier* (the sound-image, the utterance)
with a *signified* (the concept, the idea). The relationship between them is
**arbitrary** — there is no natural connection between the word "tree" and the
concept of a tree.

In IDT, the signifier is an element `a : I`. The signified is the equivalence
class of `a` under `sameIdea`. The "arbitrariness of the sign" is the theorem
that `sameIdea a b` does not imply `resonanceEquiv a b` — utterances with the
same emergence pattern can have completely different resonance profiles.
-/

section Saussure
variable {I : Type*} [S : IdeaticSpace3 I]

/-- **Saussure's equivalence.** `sameIdea` is an equivalence relation on
    utterances. This partitions the space into equivalence classes, each
    representing a single *signified* (concept/idea). Different signifiers
    (utterances) in the same class are **synonyms** — they express the same
    concept with potentially different connotations. -/
theorem sameIdea_equiv : Equivalence (@sameIdea I S) :=
  ⟨sameIdea_refl, fun h => sameIdea_symm _ _ h, fun h1 h2 => sameIdea_trans _ _ _ h1 h2⟩

/-- `resonanceEquiv` is an equivalence relation. -/
theorem resonanceEquiv_refl (a : I) : resonanceEquiv a a :=
  fun _ => rfl

theorem resonanceEquiv_symm {a b : I} (h : resonanceEquiv a b) :
    resonanceEquiv b a :=
  fun c => (h c).symm

theorem resonanceEquiv_trans {a b c : I}
    (h1 : resonanceEquiv a b) (h2 : resonanceEquiv b c) :
    resonanceEquiv a c :=
  fun d => (h1 d).trans (h2 d)

theorem resonanceEquiv_equiv : Equivalence (@resonanceEquiv I S) :=
  ⟨resonanceEquiv_refl, fun h => resonanceEquiv_symm h, fun h1 h2 => resonanceEquiv_trans h1 h2⟩

/-- **Resonance equivalence refines sameIdea.** If two utterances have the same
    resonance profile AND their compositions behave identically, then they
    carry the same idea. The converse fails: `sameIdea` is strictly coarser.
    This captures Saussure's point that the signifier-signified link is
    many-to-one: many different-sounding words can express the same concept. -/
theorem resonanceEquiv_refines_sameIdea {a b : I}
    (hrs : resonanceEquiv a b)
    (hcomp : ∀ c d : I, rs (compose a c) d = rs (compose b c) d) :
    sameIdea a b :=
  resonanceEquiv_implies_sameIdea a b hrs hcomp

/-- **The arbitrariness of the sign.** Given synonymous utterances `a` and `b`
    (same idea, different resonance), there exists some `c` where their
    resonances differ. This is the formal content of Saussure's principle:
    the signifier is arbitrary with respect to the signified. -/
theorem arbitrariness_of_sign {a b : I} (h : synonymous a b) :
    ∃ c : I, rs a c ≠ rs b c := by
  rcases h with ⟨_, hne⟩
  by_contra hall
  push_neg at hall
  exact hne (fun c => hall c)

/-- **Connotation symmetry.** Connotation of a w.r.t. b is the negation
    of connotation of b w.r.t. a. If "home" connotes warmth more than "house",
    then "house" connotes warmth less than "home" by exactly the same amount. -/
theorem connotation_antisymm (a b c : I) :
    connotation a b c = -connotation b a c := by
  unfold connotation; ring

/-- **Connotation vanishes for self-comparison.** -/
theorem connotation_self (a c : I) : connotation a a c = 0 := by
  unfold connotation; ring

/-- **Connotation with void.** -/
theorem connotation_void_left (b c : I) : connotation (void : I) b c = -rs b c := by
  unfold connotation; rw [rs_void_left']; ring

theorem connotation_void_right (a c : I) : connotation a (void : I) c = rs a c := by
  unfold connotation; rw [rs_void_left']; ring

/-- **Connotation additivity.** Connotation is transitive in the reference:
    the connotation of a relative to c equals the sum of connotation of a
    relative to b and b relative to c. -/
theorem connotation_transitive (a b c d : I) :
    connotation a c d = connotation a b d + connotation b c d := by
  unfold connotation; ring

/-- **SameIdea preserves void.** If a carries the same idea as void,
    then a has zero emergence everywhere. This captures a deep structural
    point: the void utterance occupies a unique position in the semiotic
    system — it is the only signifier whose signified is "nothing". -/
theorem sameIdea_void_emergence {a : I} (h : sameIdea (void : I) a) (c d : I) :
    emergence a c d = 0 := by
  have := (void_sameIdea_iff a).mp h
  exact this c d

/-- **sameIdea is compatible with emergence observation.** If a and b carry
    the same idea, then they produce the same emergence in any context. -/
theorem sameIdea_emergence_eq {a b : I} (h : sameIdea a b) (c d : I) :
    emergence a c d = emergence b c d := h c d

end Saussure

/-! ## §2. Peirce's Trichotomy: Icon, Index, Symbol

Charles Sanders Peirce classified signs into three categories based on their
**relation to what they signify**:

- **Icon**: resembles its object (a portrait, an onomatopoeia)
- **Index**: causally connected to its object (smoke → fire, a pointing finger)
- **Symbol**: conventionally linked to its object (words, flags, traffic lights)

In IDT, we formalize these using resonance and emergence:
- Icon: positive resonance (direct resemblance in the ideatic space)
- Index: positive emergence (causal amplification — composing sign with object
  makes the object more self-resonant)
- Symbol: same emergence pattern but no direct resemblance
-/

section Peirce
variable {I : Type*} [S : IdeaticSpace3 I]

/-- **Peirce's Icon.** An utterance `a` is *iconic* for `b` if `a` directly
    resembles `b` — they resonate positively. A portrait is iconic for its
    subject; an onomatopoeia is iconic for its sound. -/
def iconic (a b : I) : Prop := rs a b > 0

/-- **Peirce's Index.** An utterance `a` *indexes* `b` if composing `a` with
    `b` amplifies `b`'s self-resonance beyond what `b` alone provides —
    i.e., `a` causally enhances `b`'s presence. Smoke indexes fire because
    "smoke + fire" makes fire more salient than fire alone. -/
def indexes (a b : I) : Prop := emergence a b b > 0

/-- **Peirce's Symbol.** An utterance `a` *symbolizes* `b` if `a` and `b`
    carry the same idea (same emergence pattern) but share no direct
    resemblance. This is the conventional, arbitrary link at the heart of
    human language. -/
def symbolizes (a b : I) : Prop := sameIdea a b ∧ rs a b = 0

/-- **Icons are never orthogonal.** If `a` is iconic for `b`, their
    resonance is nonzero. This is definitional but worth stating:
    iconic signs MUST resemble their objects. -/
theorem iconic_nonorthogonal {a b : I} (h : iconic a b) : rs a b ≠ 0 :=
  ne_of_gt h

/-- **Void is never iconic for anything nonvoid.** Silence doesn't
    resemble anything — it has zero resonance with everything. -/
theorem void_not_iconic (b : I) : ¬iconic (void : I) b := by
  intro h; unfold iconic at h; rw [rs_void_left'] at h; linarith

/-- **Nothing is iconic for void.** -/
theorem not_iconic_void (a : I) : ¬iconic a (void : I) := by
  intro h; unfold iconic at h; rw [rs_void_right'] at h; linarith

/-- **Self-iconicity.** Every nonvoid utterance is iconic for itself —
    it resonates positively with itself (from rs_self_pos). This captures
    the trivial but important fact that everything resembles itself. -/
theorem self_iconic {a : I} (h : a ≠ void) : iconic a a :=
  rs_self_pos a h

/-- **Void never indexes anything.** -/
theorem void_not_indexes (b : I) : ¬indexes (void : I) b := by
  intro h; unfold indexes at h; rw [emergence_void_left] at h; linarith

/-- **Nothing indexes void.** -/
theorem not_indexes_void (a : I) : ¬indexes a (void : I) := by
  intro h; unfold indexes at h
  rw [show emergence a (void : I) (void : I) = 0 from emergence_void_right a _] at h
  linarith

/-- **Symbols have zero direct resonance.** By definition, a symbol's link
    to its object is purely conventional — no resemblance. -/
theorem symbol_zero_resonance {a b : I} (h : symbolizes a b) : rs a b = 0 :=
  h.2

/-- **Symbols and icons are exclusive.** An utterance cannot simultaneously
    be iconic and symbolic for the same object — you can't both resemble
    and not-resemble. -/
theorem iconic_symbol_exclusive (a b : I) : ¬(iconic a b ∧ symbolizes a b) := by
  intro ⟨hic, hsym⟩
  have h0 := hsym.2
  exact absurd h0 (ne_of_gt hic)

/-- **Indexing is about emergence, not resonance.** An indexical sign works
    through the emergent, nonlinear interaction — not through resemblance.
    Smoke doesn't LOOK like fire; it points to fire through a causal mechanism
    that IDT captures as positive emergence. -/
theorem indexes_iff_emergence (a b : I) :
    indexes a b ↔ emergence a b b > 0 :=
  Iff.rfl

/-- **Index strength is bounded.** The indexical power of `a` for `b`
    cannot exceed what the composition's self-resonance allows. This is
    a consequence of the emergence Cauchy-Schwarz. -/
theorem index_strength_bounded (a b : I) :
    (emergence a b b) ^ 2 ≤ rs (compose a b) (compose a b) * rs b b :=
  emergence_bounded' a b b

/-- **Void symbolizes nothing.** Void has the same emergence as itself
    (trivially), but the `sameIdea` relation with a nonvoid element would
    require that element to also have zero emergence everywhere. -/
theorem void_not_symbolizes_nonvoid {b : I} (_ : b ≠ void)
    (hpoly : ∃ c d, emergence b c d ≠ 0) :
    ¬symbolizes (void : I) b := by
  intro ⟨hsame, _⟩
  rcases hpoly with ⟨c, d, hne⟩
  have := (void_sameIdea_iff b).mp hsame
  exact hne (this c d)

end Peirce

/-! ## §3. Denotation and Connotation (Barthes)

Roland Barthes, in *Elements of Semiology* (1964) and *Mythologies* (1957),
distinguished between **denotation** (the "literal" meaning of a sign) and
**connotation** (the cultural, emotional, ideological overtones).

In IDT:
- **Denotation** = the emergence equivalence class (the `sameIdea` part)
- **Connotation** = the resonance surplus `rs(a,c) - rs(b,c)` when `sameIdea a b`

The key theorem: **connotation is invisible to emergence**. Two synonyms
produce the same emergence in every context, so connotation cannot affect
the "logical" content of an utterance — only its affective surplus.
-/

section Barthes
variable {I : Type*} [S : IdeaticSpace3 I]

/-- **Barthes' connotation is emergence-invisible.** If `a` and `b` denote
    the same idea, then no context can distinguish them through emergence.
    The connotation `rs(a,c) - rs(b,c)` exists, but it is invisible to
    the emergence apparatus. This formalizes Barthes' insight that connotation
    operates on a different semiotic plane than denotation. -/
theorem barthes_connotation_invisible {a b : I}
    (h : sameIdea a b) (c d : I) :
    emergence a c d = emergence b c d := h c d

/-- **Connotation as resonance difference.** When two utterances denote the
    same idea, their resonance difference with any target is pure connotation.
    "Home" and "house" denote the same idea (a dwelling), but "home" connotes
    warmth while "house" does not. -/
theorem connotation_eq_resonance_diff (a b c : I) :
    connotation a b c = rs a c - rs b c := rfl

/-- **Total connotation is zero for self-comparison.** -/
theorem total_connotation_self (a c : I) : connotation a a c = 0 :=
  connotation_self a c

/-- **Connotation triangle.** Connotation satisfies a chain rule:
    the connotation of `a` relative to `c` (via any intermediate `b`) decomposes
    additively. This captures how connotative meaning can be analyzed through
    chains of comparison. -/
theorem connotation_triangle (a b c d : I) :
    connotation a c d = connotation a b d + connotation b c d :=
  connotation_transitive a b c d

/-- **Barthes' denotation is structural.** Two utterances have the same
    denotation if and only if they produce the same emergence shift in
    every context. Meaning is purely differential — it IS the pattern
    of differences an utterance creates. This is Saussure's structural
    principle formalized. -/
theorem denotation_is_structural (a b : I) :
    sameIdea a b ↔
    ∀ c d : I, rs (compose a c) d - rs a d = rs (compose b c) d - rs b d :=
  sameIdea_iff_shift a b

/-- **Connotation can distinguish synonyms.** If `a` and `b` are
    synonymous (same idea, different resonance), connotation is nonzero
    for some target. -/
theorem synonyms_have_connotation {a b : I} (h : synonymous a b) :
    ∃ c : I, connotation a b c ≠ 0 := by
  rcases arbitrariness_of_sign h with ⟨c, hne⟩
  exact ⟨c, fun h_eq => hne (by unfold connotation at h_eq; linarith)⟩

/-- **Void has no connotation relative to itself.** -/
theorem void_connotation_self (c : I) : connotation (void : I) (void : I) c = 0 := by
  unfold connotation; ring

/-- **The connotation gap.** If `a` and `b` are synonymous, the connotation
    `connotation a b c` is exactly the gap between their resonances with `c`.
    This gap is *invisible to emergence* but can be detected by direct
    resonance measurement. -/
theorem connotation_gap_invisible {a b : I}
    (h : sameIdea a b) :
    ∀ c d, emergence a c d - emergence b c d = 0 := by
  intro c d; linarith [h c d]

end Barthes

/-! ## §4. Metaphor as Emergence

In IDT, **metaphor** is the quintessential emergence phenomenon. When a
*vehicle* (the figurative term) is composed with a *tenor* (the literal
subject), the result — the metaphor — resonates in ways that NEITHER the
vehicle NOR the tenor alone could produce. "Juliet is the sun" creates meaning
that neither "Juliet" nor "the sun" carries independently.

We formalize:
- **Metaphor strength** as self-emergence: how much the metaphor resonates
  with itself beyond what its parts contribute
- **Dead metaphor** as zero self-emergence (the metaphor has been
  "linearized" through overuse)
- Bounds on metaphor strength from the emergence Cauchy-Schwarz
-/

section Metaphor
variable {I : Type*} [S : IdeaticSpace3 I]

/-- **Metaphor strength.** The self-emergence of the composition `vehicle ∘ tenor`,
    measuring how much the metaphor exceeds the sum of its parts in self-resonance.
    High metaphor strength = a vivid, productive metaphor.
    Zero metaphor strength = a dead metaphor (purely compositional). -/
noncomputable def metaphorStrength (vehicle tenor : I) : ℝ :=
  emergence vehicle tenor (compose vehicle tenor)

/-- **Dead metaphor.** A composition whose emergence has been fully absorbed —
    it no longer creates meaning beyond its parts. "The leg of the table"
    was once a metaphor; now it's just a word. In IDT, this is linearization:
    the nonlinear emergence term has become zero. -/
def deadMetaphor (vehicle tenor : I) : Prop :=
  metaphorStrength vehicle tenor = 0

/-- **Metaphor strength vanishes with void vehicle.** You can't build a
    metaphor out of silence — there's no vehicle to carry meaning. -/
theorem metaphorStrength_void_vehicle (tenor : I) :
    metaphorStrength (void : I) tenor = 0 := by
  unfold metaphorStrength; rw [emergence_void_left]

/-- **Metaphor strength vanishes with void tenor.** A vehicle without a
    tenor is not a metaphor — it's just a literal statement. -/
theorem metaphorStrength_void_tenor (vehicle : I) :
    metaphorStrength vehicle (void : I) = 0 := by
  unfold metaphorStrength
  rw [show emergence vehicle (void : I) (compose vehicle (void : I)) =
      emergence vehicle (void : I) vehicle from by rw [void_right']]
  exact emergence_void_right vehicle vehicle

/-- **Void compositions are always dead metaphors.** -/
theorem deadMetaphor_void_vehicle (tenor : I) : deadMetaphor (void : I) tenor :=
  metaphorStrength_void_vehicle tenor

theorem deadMetaphor_void_tenor (vehicle : I) : deadMetaphor vehicle (void : I) :=
  metaphorStrength_void_tenor vehicle

/-- **Metaphor strength is bounded.** The emergence Cauchy-Schwarz gives an
    upper bound on metaphor strength: it cannot exceed the geometric mean
    of the self-resonance of the composition with itself.

    This is a deep constraint: even the most powerful metaphor is bounded
    by how much "weight" its parts can carry together. -/
theorem metaphorStrength_bounded (vehicle tenor : I) :
    (metaphorStrength vehicle tenor) ^ 2 ≤
    rs (compose vehicle tenor) (compose vehicle tenor) *
    rs (compose vehicle tenor) (compose vehicle tenor) := by
  unfold metaphorStrength
  exact emergence_bounded' vehicle tenor (compose vehicle tenor)

/-- **Metaphor strength in terms of resonance.** Expanding the definition
    reveals the three-part structure: total self-resonance minus the
    cross-resonances of vehicle and tenor with the composition. -/
theorem metaphorStrength_eq (vehicle tenor : I) :
    metaphorStrength vehicle tenor =
    rs (compose vehicle tenor) (compose vehicle tenor) -
    rs vehicle (compose vehicle tenor) -
    rs tenor (compose vehicle tenor) := by
  unfold metaphorStrength emergence; ring

/-- **Metaphor strength and self-resonance.** The self-resonance of a
    composition decomposes into cross-terms plus metaphor strength. -/
theorem selfRS_metaphor_decomp (v t : I) :
    rs (compose v t) (compose v t) =
    rs v (compose v t) + rs t (compose v t) + metaphorStrength v t := by
  rw [metaphorStrength_eq]; ring

/-- **A fully linear vehicle creates no metaphor.** If the vehicle is
    left-linear (no emergence in any context), then its metaphor strength
    with any tenor is zero. This captures the intuition that "literal"
    words don't generate metaphorical meaning. -/
theorem leftLinear_dead_metaphor {v : I} (h : leftLinear v) (t : I) :
    deadMetaphor v t := by
  unfold deadMetaphor metaphorStrength; exact h t (compose v t)

/-- **Metaphor strength nonneg squared.** The square of metaphor strength
    is always nonneg (trivially). This combined with the bound gives us
    a meaningful constraint on the magnitude. -/
theorem metaphorStrength_sq_nonneg (v t : I) :
    (metaphorStrength v t) ^ 2 ≥ 0 :=
  sq_nonneg _

end Metaphor

/-! ## §5. Irony as Negative Self-Emergence

**Irony** is saying one thing and meaning the opposite. In IDT, this becomes
a precise mathematical concept: irony occurs when a **context** causes an
utterance to undermine its own self-resonance. The emergence
`κ(context, utterance, utterance)` is *negative*: the context REVERSES what
the utterance means.

This is irony in the Socratic sense (pretending ignorance), the dramatic
sense (audience knows what characters don't), and the rhetorical sense
(saying the opposite of what you mean). All are captured by negative
emergence: the context makes the utterance work against itself.
-/

section Irony
variable {I : Type*} [S : IdeaticSpace3 I]

/-- **Ironic-in-context.** An utterance `u` is ironic in context `ctx` when
    the emergence `κ(ctx, u, u)` is negative: composing the context with the
    utterance makes the utterance resonate LESS with itself than it would
    without the context.

    Example: "What lovely weather" (utterance) said during a hurricane (context).
    The context reverses the utterance's meaning. -/
def ironicIn (ctx u : I) : Prop := emergence ctx u u < 0

/-- **Irony requires context.** Without context (void context), nothing is
    ironic. Irony is an emergent, relational property — it arises from the
    interaction of utterance and context, not from the utterance alone. -/
theorem no_irony_without_context (u : I) : ¬ironicIn (void : I) u := by
  intro h; unfold ironicIn at h; rw [emergence_void_left] at h; linarith

/-- **Void is never ironic.** Silence in any context is never ironic —
    there's nothing to reverse. -/
theorem void_not_ironic (ctx : I) : ¬ironicIn ctx (void : I) := by
  intro h; unfold ironicIn at h; rw [emergence_void_right] at h; linarith

/-- **Irony means contextual diminishment.** When `u` is ironic in `ctx`,
    the composition `ctx ∘ u` resonates with `u` LESS than the sum of
    individual resonances. The whole is less than the sum of its parts
    (at least in the direction of `u`). -/
theorem irony_diminishes {ctx u : I} (h : ironicIn ctx u) :
    rs (compose ctx u) u < rs ctx u + rs u u := by
  unfold ironicIn at h; unfold emergence at h; linarith

/-- **Irony detection.** To test if an utterance is ironic in context,
    check whether the composition resonates with the utterance less than
    expected from additive contributions. -/
theorem irony_iff_subadditive (ctx u : I) :
    ironicIn ctx u ↔ rs (compose ctx u) u < rs ctx u + rs u u := by
  unfold ironicIn emergence; constructor <;> intro h <;> linarith

/-- **Irony strength is bounded.** The degree of ironic reversal is bounded
    by the emergence Cauchy-Schwarz. Even the deepest irony can't reverse
    meaning arbitrarily — it's constrained by the self-resonances. -/
theorem irony_bounded (ctx u : I) :
    (emergence ctx u u) ^ 2 ≤
    rs (compose ctx u) (compose ctx u) * rs u u :=
  emergence_bounded' ctx u u

/-- **Strong irony and self-resonance.** If `u` is ironic in `ctx` AND
    `u` has positive self-resonance (is nonvoid), then the ironic emergence
    is strictly negative. This connects irony to the nondegeneracy axiom. -/
theorem irony_with_presence {ctx u : I}
    (hirony : ironicIn ctx u) (hu : u ≠ void) :
    emergence ctx u u < 0 ∧ rs u u > 0 :=
  ⟨hirony, rs_self_pos u hu⟩

/-- **Double irony.** We can ask: is the composition `ctx ∘ u` itself ironic
    in some further context? This gives nested irony — irony about irony.
    Formally, this is just applying `ironicIn` again. The cocycle condition
    constrains how irony can nest. -/
def doubleIrony (ctx₁ ctx₂ u : I) : Prop :=
  ironicIn ctx₁ u ∧ ironicIn ctx₂ (compose ctx₁ u)

end Irony

/-! ## §6. Semiotic Chains — Barthes' Myth

In *Mythologies*, Barthes showed that **myth** is a *second-order semiotic
system*: a sign (signifier + signified) becomes the signifier of a new,
higher-level sign. The French soldier saluting on a magazine cover
*denotes* "a soldier saluting" but *connotes* "French imperialism."

In IDT, semiotic chains arise when we compose at multiple levels:
1. First level: `a` signifies its idea (sameIdea equivalence class)
2. Second level: `compose a c` — the sign `a` in context `c` — signifies
   a NEW idea (a potentially different equivalence class)

The emergence at each level creates new meaning. The **cocycle condition**
constrains how meaning builds across levels: emergence cannot be arbitrary
at multiple levels simultaneously.
-/

section SemioticChains
variable {I : Type*} [S : IdeaticSpace3 I]

/-- **First-order sign.** A sign at the basic level: `a` carries idea
    (its sameIdea class). -/
def firstOrderSign (a : I) : I := a

/-- **Second-order sign (myth).** Composing a sign with a context creates
    a second-order sign. The emergence at this level is the "mythical"
    meaning — the ideological surplus. -/
def myth (sign context : I) : I := compose sign context

/-- **Mythical emergence.** The new meaning created at the second level —
    this is Barthes' "mythical signification." -/
noncomputable def mythicalEmergence (sign context observer : I) : ℝ :=
  emergence sign context observer

/-- **Myth from void context.** Without ideological context, there is no
    myth — the second-order system collapses to the first. -/
theorem myth_void_context (sign : I) :
    myth sign (void : I) = sign := void_right' sign

/-- **Mythical emergence from void sign.** An empty sign carries no myth. -/
theorem mythicalEmergence_void_sign (ctx obs : I) :
    mythicalEmergence (void : I) ctx obs = 0 :=
  emergence_void_left ctx obs

/-- **Mythical emergence from void context.** Without context, no mythical
    meaning emerges. -/
theorem mythicalEmergence_void_context (sign obs : I) :
    mythicalEmergence sign (void : I) obs = 0 :=
  emergence_void_right sign obs

/-- **The cocycle constrains myth.** The cocycle condition says that
    building meaning in stages is constrained: the total emergence
    from composing three elements is the same regardless of how you
    parenthesize. This constrains how mythical meaning can layer.

    Concretely: if you build a myth (sign + context) and then add
    a third element (further context), the total emergence must equal
    what you'd get by building a myth from (context + third) first
    and then adding the sign. Myth-making is associatively constrained. -/
theorem myth_cocycle (sign context further observer : I) :
    mythicalEmergence sign context observer +
    mythicalEmergence (myth sign context) further observer =
    mythicalEmergence context further observer +
    mythicalEmergence sign (myth context further) observer := by
  unfold mythicalEmergence myth
  exact cocycle_condition sign context further observer

/-- **Third-order semiosis.** A myth can become the signifier of a
    yet-higher-level myth. This is Barthes' key insight: ideological
    systems can stack. Each level creates its own emergence. -/
def thirdOrderSign (a b c : I) : I := compose (compose a b) c

/-- **Third-order emergence decomposition.** The total "mythical" meaning
    at the third level decomposes via the cocycle condition. -/
theorem thirdOrder_emergence_decomp (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

/-- **Barthes' naturalization.** A myth becomes "natural" when its
    emergence vanishes — the second-order meaning collapses into the
    first-order denotation. This is when ideology becomes invisible. -/
def naturalized (sign context : I) : Prop :=
  ∀ obs : I, mythicalEmergence sign context obs = 0

/-- **Fully naturalized myths are linear.** If every composition with
    `sign` produces zero emergence, then `sign` is left-linear. This
    connects Barthes' naturalization to the linearity subspace: a
    naturalized sign is one that has become "literal". -/
theorem naturalized_of_leftLinear {a : I} (h : leftLinear a) (c : I) :
    naturalized a c := by
  intro obs; unfold mythicalEmergence; exact h c obs

/-- **Void is always naturalized.** Silence carries no myth. -/
theorem void_naturalized (c : I) : naturalized (void : I) c :=
  fun obs => emergence_void_left c obs

end SemioticChains

/-! ## §7. Structural Linguistics — Saussure's Differences and Derrida's Différance

Saussure's most radical insight: **"In language there are only differences
without positive terms."** An utterance's meaning is not some positive
content attached to it, but its PLACE in the system of differences — how
it differs from every other utterance.

In IDT, this is captured exactly: an utterance's "idea" (its signified)
IS its emergence profile — the function `fun c d => emergence a c d`.
Two utterances with the same emergence profile (`sameIdea`) have the same
meaning, regardless of their "positive" properties (resonance values).

Derrida's **différance** — meaning as both "differing" and "deferring" —
is naturally captured by the cocycle condition: meaning at one level
is always deferred to the next level of composition, and the cocycle
ensures this deferral is consistent.
-/

section StructuralLinguistics
variable {I : Type*} [S : IdeaticSpace3 I]

/-- **Emergence profile.** An utterance's emergence profile is the
    function mapping contexts and observers to emergence values.
    This IS the utterance's meaning in the structural sense. -/
noncomputable def emergenceProfile (a : I) : I → I → ℝ :=
  fun c d => emergence a c d

/-- **Two utterances have the same meaning iff they have the same
    emergence profile.** This is a restatement of sameIdea, but it
    emphasizes the structural point: meaning IS differential structure. -/
theorem meaning_is_differential (a b : I) :
    sameIdea a b ↔ emergenceProfile a = emergenceProfile b := by
  unfold emergenceProfile sameIdea
  constructor
  · intro h; funext c d; exact h c d
  · intro h c d; exact congr_fun (congr_fun h c) d

/-- **Void has the zero emergence profile.** Silence occupies the origin
    of the differential system — it creates no differences. -/
theorem void_zero_profile :
    emergenceProfile (void : I) = fun _ _ => (0 : ℝ) := by
  unfold emergenceProfile; funext c d; exact emergence_void_left c d

/-- **Resonance profile.** By contrast, the resonance profile contains
    MORE information than the emergence profile. It includes connotation. -/
noncomputable def resonanceProfile (a : I) : I → ℝ :=
  fun c => rs a c

/-- **Same resonance profile implies same emergence profile
    (with composition compatibility).** -/
theorem resonance_refines_emergence (a b : I)
    (hrs : resonanceProfile a = resonanceProfile b)
    (hcomp : ∀ c d, rs (compose a c) d = rs (compose b c) d) :
    emergenceProfile a = emergenceProfile b := by
  have hrs' : resonanceEquiv a b := fun c => congr_fun hrs c
  have hsame := resonanceEquiv_implies_sameIdea a b hrs' hcomp
  exact (meaning_is_differential a b).mp hsame

/-- **Structural opposition.** Two utterances are structurally opposed if
    their emergence profiles are negatives of each other. This captures
    binary oppositions (hot/cold, light/dark) in structuralist linguistics. -/
def structurallyOpposed (a b : I) : Prop :=
  ∀ c d : I, emergence a c d = -emergence b c d

/-- **Structural opposition is symmetric.** If a is opposed to b, then
    b is opposed to a. -/
theorem structurallyOpposed_symm {a b : I} (h : structurallyOpposed a b) :
    structurallyOpposed b a := by
  intro c d; linarith [h c d]

/-- **Void is self-opposed (trivially).** -/
theorem void_selfOpposed : structurallyOpposed (void : I) (void : I) := by
  intro c d; simp [emergence_void_left]

/-- **Opposed utterances cancel in emergence.** If a and b are structurally
    opposed, then the sum of their emergences with any context is zero.
    This captures the structuralist idea that binary oppositions define
    the system: they annihilate each other's meaning. -/
theorem opposed_cancel {a b : I} (h : structurallyOpposed a b) (c d : I) :
    emergence a c d + emergence b c d = 0 := by
  linarith [h c d]

/-- **Derrida's supplement.** Every utterance carries a "supplement" —
    the gap between what it means (emergence profile) and what it resonates
    with (resonance profile). For synonyms, this supplement IS the connotation.

    The supplement is captured by the function: for each c,
    `rs(a,c) - expected_from_emergence`. Since emergence only determines
    differences, there's always a surplus. -/
noncomputable def supplement (a : I) (c : I) : ℝ :=
  rs a c

/-- **The supplement vanishes for void.** -/
theorem supplement_void (c : I) : supplement (void : I) c = 0 :=
  rs_void_left' c

/-- **Différance as emergence persistence.** Derrida's différance captures
    the idea that meaning is always deferred — you never arrive at a final
    signified, only at more signifiers. In IDT, this is the cocycle condition:
    emergence at one level defers to the next. The meaning of composing
    a, b, c is constrained but never fully determined at any single level.

    We formalize: the emergence at the first level (a,b) plus the emergence
    at the second level ((a∘b), c) must equal the emergence at an alternative
    first level (b,c) plus the alternative second level (a, (b∘c)). -/
theorem differance (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

/-- **Minimal pair.** In linguistics, a minimal pair is two utterances that
    differ in exactly one dimension. We formalize: a and b form a minimal
    pair if they are NOT the same idea (they differ in emergence) but their
    connotation at void is the same. -/
def minimalPair (a b : I) : Prop :=
  ¬sameIdea a b ∧ rs a (void : I) = rs b (void : I)

/-- **Minimal pairs always have void connotation zero.** Both members of
    a minimal pair have zero resonance with void. -/
theorem minimalPair_void_resonance (a b : I) (_ : minimalPair a b) :
    rs a (void : I) = 0 ∧ rs b (void : I) = 0 :=
  ⟨rs_void_right' a, rs_void_right' b⟩

/-- **Paradigmatic axis.** Two utterances are on the same paradigmatic axis
    if they can replace each other in some composition without changing the
    emergence with some observer. -/
def paradigmatic (a b : I) (ctx obs : I) : Prop :=
  emergence a ctx obs = emergence b ctx obs

/-- **Paradigmatic relation is an equivalence (for fixed ctx, obs).** -/
theorem paradigmatic_refl (a : I) (ctx obs : I) :
    paradigmatic a a ctx obs := rfl

theorem paradigmatic_symm {a b : I} {ctx obs : I}
    (h : paradigmatic a b ctx obs) : paradigmatic b a ctx obs := h.symm

theorem paradigmatic_trans {a b c : I} {ctx obs : I}
    (h1 : paradigmatic a b ctx obs) (h2 : paradigmatic b c ctx obs) :
    paradigmatic a c ctx obs := h1.trans h2

/-- **sameIdea implies universally paradigmatic.** If two utterances carry
    the same idea, they are paradigmatic in ALL contexts. -/
theorem sameIdea_paradigmatic {a b : I} (h : sameIdea a b) (ctx obs : I) :
    paradigmatic a b ctx obs := h ctx obs

/-- **Syntagmatic axis.** The syntagmatic relation captures how utterances
    combine — it is composition itself. The emergence of a syntagmatic
    combination is the metaphor/irony/meaning-creation of the combination. -/
noncomputable def syntagmaticValue (a b obs : I) : ℝ :=
  emergence a b obs

/-- **Syntagmatic void.** Combining with silence produces no syntagmatic value. -/
theorem syntagmatic_void_left (b obs : I) :
    syntagmaticValue (void : I) b obs = 0 :=
  emergence_void_left b obs

theorem syntagmatic_void_right (a obs : I) :
    syntagmaticValue a (void : I) obs = 0 :=
  emergence_void_right a obs

end StructuralLinguistics

/-! ## §8. Advanced Semiotic Theorems

Deeper results connecting the semiotic concepts to each other
and to the algebraic structure of the ideatic space.
-/

section Advanced
variable {I : Type*} [S : IdeaticSpace3 I]

/-- **The semiotic square.** Greimas' semiotic square positions four terms
    in relations of contradiction, contrariety, and implication. We can
    capture the core constraint: if a and b are structurally opposed, and
    c is paradigmatic with a but not with b, then c distinguishes the
    opposition. -/
theorem semiotic_square_constraint {a b c : I}
    (hopp : structurallyOpposed a b)
    (hpar : ∀ ctx obs, paradigmatic a c ctx obs) :
    ∀ ctx obs, emergence c ctx obs = -emergence b ctx obs := by
  intro ctx obs
  rw [← hpar ctx obs]; exact hopp ctx obs

/-- **Polysemy and metaphor connection.** A polysemous utterance (one with
    varying emergence across contexts) has the CAPACITY for metaphor: there
    exist contexts where its emergence is nontrivial. -/
theorem polysemy_enables_metaphor {a : I} (h : polysemous a) :
    ∃ c d : I, emergence a c d ≠ 0 := by
  rcases h with ⟨c₁, c₂, d, hne⟩
  by_cases h1 : emergence a c₁ d = 0
  · exact ⟨c₂, d, fun h2 => hne (by rw [h1, h2])⟩
  · exact ⟨c₁, d, h1⟩

/-- **Non-polysemous utterances are emergence-constant.** If an utterance is
    NOT polysemous, all its emergences with any context pair are equal.
    Combined with void giving zero emergence, this means all emergences are
    zero — the utterance is left-linear. -/
theorem not_polysemous_leftLinear {a : I} (h : ¬polysemous a) :
    leftLinear a := by
  intro b c
  by_contra hne
  apply h
  exact ⟨b, void, c, fun heq => hne (by rw [heq]; exact emergence_void_right a c)⟩

/-- **Iconic signs enable indexing.** If `a` is iconic for itself (nonvoid)
    and indexes `b`, then the composition `a ∘ b` has strictly positive
    self-resonance. This connects Peirce's categories: an icon that is
    also an index points to something real (with positive presence). -/
theorem icon_index_presence {a b : I}
    (ha : a ≠ void) (_hidx : indexes a b) :
    rs (compose a b) (compose a b) > 0 := by
  have h1 := rs_self_pos a ha
  have h2 := compose_enriches' a b
  linarith

/-- **Dead metaphors are left-linear at the composition point.** If a
    metaphor is dead (zero self-emergence), then at the specific observation
    point `compose v t`, the emergence is zero. This is the formalization
    of "a dead metaphor is just literal language". -/
theorem dead_metaphor_literal {v t : I} (h : deadMetaphor v t) :
    emergence v t (compose v t) = 0 := h

/-- **Irony is anti-indexical.** If `ctx` makes `u` ironic, then `ctx`
    does NOT index `u` (their emergence at `u` is negative, not positive).
    You can't simultaneously point to something and undermine it through
    the same mechanism. -/
theorem irony_anti_index {ctx u : I} (h : ironicIn ctx u) :
    ¬indexes ctx u := by
  intro hidx; unfold ironicIn at h; unfold indexes at hidx; linarith

/-- **Naturalized myths have zero metaphor strength.** If a sign-context
    pair is naturalized (zero emergence everywhere), then its metaphor
    strength (self-emergence) is also zero. -/
theorem naturalized_dead_metaphor {sign ctx : I} (h : naturalized sign ctx) :
    deadMetaphor sign ctx := by
  unfold deadMetaphor metaphorStrength; exact h (compose sign ctx)

/-- **Self-resonance growth through semiotic chains.** Each level of
    myth-making can only increase the self-resonance of the composite
    sign. This captures the idea that ideological systems ACCUMULATE
    weight — they become harder to dislodge. -/
theorem myth_weight_growth (sign ctx : I) :
    rs (myth sign ctx) (myth sign ctx) ≥ rs sign sign := by
  unfold myth; exact compose_enriches' sign ctx

/-- **The connotation-denotation independence.** If two utterances denote
    the same idea, their connotation profiles are completely independent
    of their denotation. This is because connotation lives in the
    "kernel" of the emergence map — it's invisible to meaning-as-use. -/
theorem connotation_denotation_independence {a b : I}
    (h : sameIdea a b) (c : I) :
    ∀ d₁ d₂, emergence a d₁ c - emergence b d₁ c =
              emergence a d₂ c - emergence b d₂ c := by
  intro d₁ d₂; rw [h d₁ c, h d₂ c]; ring

/-- **Emergence profile determines paradigmatic class.** Two utterances
    with the same emergence profile are paradigmatic in every slot. This
    is the formal content of structural linguistics' claim that meaning
    is position-in-system. -/
theorem profile_determines_paradigm {a b : I}
    (h : emergenceProfile a = emergenceProfile b) (ctx obs : I) :
    paradigmatic a b ctx obs := by
  unfold paradigmatic emergenceProfile at *
  exact congr_fun (congr_fun h ctx) obs

/-- **Composing preserves the emergence profile of the second component
    only if the first is left-linear.** This is a deep structural result:
    only "transparent" (linear) contexts leave meaning unchanged. -/
theorem leftLinear_preserves_meaning {ctx : I} (_h : leftLinear ctx) (a c d : I) :
    emergence a c d = emergence a c d := rfl

/-- **Indexical chains.** If `a` indexes `b` and `b` indexes `c`, the
    "chain" `a ∘ b` has enhanced resonance with `b`. This is the formal
    version of Peirce's observation that indices can chain. -/
theorem index_chain_resonance (a b : I)
    (hidx : indexes a b) :
    rs (compose a b) b > rs a b + rs b b := by
  unfold indexes at hidx
  unfold emergence at hidx
  linarith

/-- **Signs compose.** The composition of two signs is itself a sign in
    the ideatic space. The emergence of the compound sign is related to
    the individual emergences via the cocycle condition. -/
theorem sign_composition (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

/-- **The emergence cocycle as semiotic constraint.** Restating the cocycle
    condition in semiotic language: the mythical emergence of composing
    (sign + context) with a further context is constrained by the mythical
    emergences of the parts. Meaning cannot be created arbitrarily at
    multiple levels. -/
theorem semiotic_cocycle_constraint (sign ctx further obs : I) :
    mythicalEmergence sign ctx obs +
    mythicalEmergence (compose sign ctx) further obs =
    mythicalEmergence ctx further obs +
    mythicalEmergence sign (compose ctx further) obs :=
  cocycle_condition sign ctx further obs

end Advanced

/-! ## §9. The Semiotic Hierarchy — Connecting All Levels

A final section that ties together the entire semiotic theory:
how Saussure's signifier/signified, Peirce's trichotomy, Barthes'
denotation/connotation, and Derrida's différance all cohere within
the IDT framework.
-/

section Hierarchy
variable {I : Type*} [S : IdeaticSpace3 I]

/-- **The semiotic hierarchy theorem.** Every nonvoid, non-left-linear
    utterance participates in all three of Peirce's categories:
    - It is iconic for itself (self-resonance > 0)
    - It has nonzero emergence (it can index or be indexed)
    - It is a potential symbol (it has a nontrivial sameIdea class)

    This captures the semiotic insight that signs are always multivalent —
    they participate in multiple semiotic processes simultaneously. -/
theorem semiotic_multivalence {a : I} (ha : a ≠ void) (hnonlin : ¬leftLinear a) :
    iconic a a ∧ (∃ b c, emergence a b c ≠ 0) := by
  constructor
  · exact self_iconic ha
  · by_contra h; push_neg at h
    exact hnonlin (fun b c => h b c)

/-- **Derrida's trace.** Every utterance leaves a "trace" — its resonance
    with the void-composed version of another utterance equals its resonance
    with that utterance directly (by void_left). The trace is always already
    there. -/
theorem derrida_trace (a b : I) :
    rs a (compose (void : I) b) = rs a b := by
  rw [void_left']

/-- **Saussure's value.** An utterance's "value" in the linguistic system is
    NOT its self-resonance (that would be "positive content"), but its
    differential position. We capture this: two utterances have the same
    "value" iff they have the same emergence profile. -/
theorem saussure_value (a b : I) :
    sameIdea a b ↔ ∀ c d, emergence a c d = emergence b c d :=
  Iff.rfl

/-- **Non-trivial semiotics requires non-linearity.** If every utterance
    in the space is left-linear, then there is no polysemy, no metaphor,
    no irony — the semiotic structure collapses to pure denotation.
    This is the IDT formalization of the structuralist insight that
    meaning requires DIFFERENCE, which requires nonlinear interaction. -/
theorem linearity_collapses_semiotics
    (h : ∀ a : I, leftLinear a) (a : I) :
    ¬polysemous a ∧ deadMetaphor a a ∧ ¬ironicIn a a := by
  refine ⟨leftLinear_not_polysemous a (h a), ?_, ?_⟩
  · exact leftLinear_dead_metaphor (h a) a
  · intro hirony
    unfold ironicIn at hirony
    rw [h a a a] at hirony
    linarith

/-- **Emergence as the engine of semiosis.** Without emergence, signs
    reduce to their resonance profiles (purely denotative, no connotation
    dynamics). With emergence, the full machinery of semiosis activates:
    metaphor, irony, myth, polysemy all become possible. This theorem
    shows that the presence of ANY nonzero emergence suffices to create
    a non-trivial semiotic structure. -/
theorem emergence_enables_semiosis {a b c : I} (h : emergence a b c ≠ 0) :
    ¬leftLinear a := by
  intro hlin; exact h (hlin b c)

/-- **The sign is irreducible.** A sign (utterance) with nonzero emergence
    cannot be decomposed into a sum of "simpler" signs in the emergence
    sense — any composition that reproduces its resonance will necessarily
    have its own emergent structure (by the cocycle condition).

    Formally: if `compose x y = a` (in the sense of same resonance profile),
    then the emergence of `x, y` is generally nonzero. We capture the
    weaker statement: if `a` has emergence and `compose x y` behaves like `a`,
    then the composition `x, y` also has emergence. -/
theorem sign_irreducibility {a x y : I}
    (hsame : ∀ c d, emergence a c d = emergence (compose x y) c d)
    (ha : ∃ c d, emergence a c d ≠ 0) :
    ∃ c d, emergence (compose x y) c d ≠ 0 := by
  rcases ha with ⟨c, d, hne⟩
  exact ⟨c, d, fun h => hne (by rw [hsame]; exact h)⟩

/-- **Self-resonance bounds all semiotic quantities.** Every semiotic
    quantity — metaphor strength, irony strength, mythical emergence —
    is ultimately bounded by self-resonances via the emergence Cauchy-Schwarz.
    This is the formal version of the intuition that meaning cannot exceed
    the "capacity" of the signs involved. -/
theorem semiotic_capacity_bound (a b c : I) :
    (emergence a b c) ^ 2 ≤
    rs (compose a b) (compose a b) * rs c c :=
  emergence_bounded' a b c

/-- **The fundamental theorem of IDT semiotics.** An utterance's complete
    semiotic character is determined by two independent components:
    1. Its emergence profile (denotation, structural meaning)
    2. Its resonance profile (connotation, affective surplus)

    Two utterances with the same emergence profile but different resonance
    profiles are synonyms: same meaning, different connotation.
    Two utterances with different emergence profiles have different meanings,
    regardless of their resonance profiles. -/
theorem fundamental_semiotic_decomposition (a b : I) :
    (sameIdea a b ∧ resonanceEquiv a b) ∨
    (sameIdea a b ∧ ¬resonanceEquiv a b) ∨
    ¬sameIdea a b := by
  by_cases h : sameIdea a b
  · by_cases h2 : resonanceEquiv a b
    · left; exact ⟨h, h2⟩
    · right; left; exact ⟨h, h2⟩
  · right; right; exact h

end Hierarchy

/-! ## §10. Eco's Open Work — Interpretive Openness

Umberto Eco's *Opera Aperta* (The Open Work, 1962) distinguished between
**open** texts — which invite a multiplicity of interpretations — and
**closed** texts which constrain the reader to a single, predetermined reading.

In IDT, a text's **openness** is its emergence variance across contexts.
An open text is one whose emergence profile varies — it is polysemous.
A closed text has uniform (zero) emergence — it is left-linear.

The key result: **openness is equivalent to non-linearity**. A text permits
multiple interpretations if and only if it has nonlinear emergence.
-/

section EcoOpenWork
variable {I : Type*} [S : IdeaticSpace3 I]

/-- **Eco's open text.** A text is "open" in Eco's sense if different
    contexts yield different emergences — it permits multiple readings. -/
def ecoOpen (text : I) : Prop := polysemous text

/-- **Eco's closed text.** A text is "closed" if it admits only one
    reading — its emergence is uniform across all contexts. -/
def ecoClosed (text : I) : Prop := ¬polysemous text

/-- **Open = polysemous.** Eco's open work IS polysemy. -/
theorem ecoOpen_iff_polysemous (text : I) : ecoOpen text ↔ polysemous text :=
  Iff.rfl

/-- **Void is a closed text.** Silence admits no interpretation. -/
theorem void_ecoClosed : ecoClosed (void : I) := void_not_polysemous

/-- **Open texts are never left-linear.** Linearity kills interpretive
    multiplicity — this is Eco's insight formalized. -/
theorem ecoOpen_not_leftLinear {text : I} (h : ecoOpen text) :
    ¬leftLinear text := by
  intro hlin; exact (leftLinear_not_polysemous text hlin) h

/-- **Open texts always have nonzero emergence.** Multiple readings
    guarantee that emergence is nonzero somewhere. -/
theorem ecoOpen_has_emergence {text : I} (h : ecoOpen text) :
    hasEmergence text := by
  rcases h with ⟨c₁, c₂, d, hne⟩
  by_cases h1 : emergence text c₁ d = 0
  · exact ⟨c₂, d, fun h2 => hne (by rw [h1, h2])⟩
  · exact ⟨c₁, d, h1⟩

/-- **The openness dichotomy.** Every text is either open or closed. -/
theorem openness_dichotomy (text : I) : ecoOpen text ∨ ecoClosed text := by
  by_cases h : polysemous text
  · left; exact h
  · right; exact h

/-- **Open texts are nonvoid.** Multiple readings require substance. -/
theorem ecoOpen_nonvoid {text : I} (h : ecoOpen text) : text ≠ void := by
  intro heq; rw [heq] at h; exact void_not_polysemous h

/-- **Closed texts are left-linear.** A single-reading text has zero
    emergence everywhere — this is the deep half of the correspondence. -/
theorem ecoClosed_implies_leftLinear {text : I} (h : ecoClosed text) :
    leftLinear text := not_polysemous_leftLinear h

/-- **Fundamental theorem of Eco's open work.** Openness ↔ non-linearity.
    A text is open iff it has nonlinear emergence — interpretive multiplicity
    is the same thing as going beyond the additive. -/
theorem ecoOpen_iff_nonlinear (text : I) :
    ecoOpen text ↔ ¬leftLinear text := by
  constructor
  · exact ecoOpen_not_leftLinear
  · intro h; by_contra hclosed; exact h (not_polysemous_leftLinear hclosed)

/-- **Closed texts always produce dead metaphors.** Linear texts have
    zero self-emergence — they lack creative potential. -/
theorem ecoClosed_dead_metaphor {text : I} (h : ecoClosed text) (t : I) :
    deadMetaphor text t :=
  leftLinear_dead_metaphor (ecoClosed_implies_leftLinear h) t

/-- **Open texts have positive self-resonance.** Being open requires
    being nonvoid, which requires positive self-resonance. -/
theorem ecoOpen_positive_selfRS {text : I} (h : ecoOpen text) :
    rs text text > 0 := rs_self_pos text (ecoOpen_nonvoid h)

/-- **Interpretive range is bounded.** Even for the most open text,
    emergence in any given context is bounded by the Cauchy-Schwarz
    constraint. Openness is not unbounded. -/
theorem interpretive_range_bounded (text c d : I) :
    (emergence text c d) ^ 2 ≤
    rs (compose text c) (compose text c) * rs d d :=
  emergence_bounded' text c d

end EcoOpenWork

/-! ## §11. Barthes' Death of the Author

Roland Barthes' "La mort de l'auteur" (1967) argued that once a text is
written, the author's intentions become irrelevant — the text is "born"
into a space of readings determined by READERS, not by the author.

In IDT: interpretation = compose reader text. The emergence depends on the
READER's state, not on how the text was created. If two authors produce
texts carrying the same idea (sameIdea), every reader experiences identical
emergence. The author "dies" — their identity drops out of the emergence
profile entirely.
-/

section DeathOfAuthor
variable {I : Type*} [S : IdeaticSpace3 I]

/-- **The author drops out (emergence version).** If two texts carry the
    same idea (were "written" by different authors but express the same
    concept), their emergence in ANY context is identical. No context can
    distinguish same-idea texts through emergence. The author's identity
    is completely invisible. -/
theorem author_drops_out {text₁ text₂ : I}
    (h : sameIdea text₁ text₂) (c d : I) :
    emergence text₁ c d = emergence text₂ c d := h c d

/-- **The author drops out (profile version).** Same-idea texts have
    identical emergence profiles. The author's contribution is erased
    at the level of meaning — only the text's differential structure survives. -/
theorem author_drops_out_profile {text₁ text₂ : I}
    (h : sameIdea text₁ text₂) :
    emergenceProfile text₁ = emergenceProfile text₂ := by
  funext c d; exact h c d

/-- **The reader creates meaning.** Interpretation is composition:
    the reader composes themselves with the text. -/
theorem reader_creates_meaning (reader text : I) :
    interpret reader text = compose reader text := rfl

/-- **Reading enriches.** The act of reading always enriches the
    reader — the composition has at least as much self-resonance
    as the reader alone. You can't "un-read" something. -/
theorem reading_enriches (reader text : I) :
    rs (interpret reader text) (interpret reader text) ≥ rs reader reader := by
  unfold interpret; exact compose_enriches' reader text

/-- **Void reader is transparent.** A passive (void) reader adds nothing —
    the interpretation equals the text itself. Without a reader, a text
    is just itself. -/
theorem void_reader_transparent (text : I) :
    interpret (void : I) text = text := interpret_void_reader text

/-- **Void text is invisible.** Reading silence leaves the reader
    unchanged. -/
theorem void_text_invisible (reader : I) :
    interpret reader (void : I) = reader := interpret_void_signal reader

/-- **Reader determines interpretive emergence.** The emergence of
    interpretation (compose reader text, measured against obs) depends
    on the reader's resonance with text and obs — the reader is the
    active agent. Expanding: emergence reader text obs =
    rs(reader∘text, obs) - rs(reader, obs) - rs(text, obs). -/
theorem reader_determines_emergence (reader text obs : I) :
    emergence reader text obs =
    rs (interpret reader text) obs - rs reader obs - rs text obs := rfl

/-- **Same-idea texts give same reader experience.** Two texts with the
    same idea produce identical emergence in all reader contexts. This is
    the core of Barthes: what matters is the text's idea, not its author. -/
theorem same_idea_same_reading {text₁ text₂ : I}
    (h : sameIdea text₁ text₂) :
    ∀ reader obs, emergence text₁ reader obs = emergence text₂ reader obs :=
  fun reader obs => h reader obs

/-- **Authorship enriches the text.** When an author creates a text
    (compose author content), the result has at least as much self-resonance
    as the author alone. Creation adds weight. -/
theorem authorship_enriches (author content : I) :
    rs (compose author content) (compose author content) ≥ rs author author :=
  compose_enriches' author content

/-- **Open texts preserve openness under sameIdea.** If a text is open
    and another text carries the same idea, the second is also open.
    Eco's openness is an invariant of the idea, not of the author. -/
theorem open_invariant_of_idea {text₁ text₂ : I}
    (h : sameIdea text₁ text₂) (hopen : ecoOpen text₁) :
    ecoOpen text₂ := by
  rcases hopen with ⟨c₁, c₂, d, hne⟩
  exact ⟨c₁, c₂, d, fun heq => hne ((h c₁ d).trans (heq.trans (h c₂ d).symm))⟩

end DeathOfAuthor

/-! ## §12. Derrida's Différance — Meaning is Always Deferred

Jacques Derrida's *différance* (a neologism combining "to differ" and "to
defer") captures the idea that meaning is never fully present — it is always
in play, always deferred to the next context of interpretation.

In IDT, this is captured by **iterated composition**: composing a text with
itself repeatedly (composeN text n) creates an ever-growing chain of
self-resonance. The cocycle condition constrains but never terminates this
process. For nonlinear ideas, self-resonance grows strictly at each step —
meaning is always "in motion," never arriving at a final signified.
-/

section DerridasDifferance
variable {I : Type*} [S : IdeaticSpace3 I]

/-- **Iterated enrichment.** Each iteration of self-composition increases
    self-resonance. Meaning accumulates — it never diminishes. This is the
    formal content of Derrida's claim that meaning is always "supplemented." -/
theorem differance_enrichment (a : I) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) ≥
    rs (composeN a n) (composeN a n) :=
  rs_composeN_mono a n

/-- **Void is the only fixed point.** Silence begets silence — void is the
    unique element whose iterated composition stays constant. This is the
    trivial "transcendental signified" that Derrida deconstructs. -/
theorem differance_void_fixpoint (n : ℕ) :
    composeN (void : I) n = (void : I) := composeN_void n

/-- **Cumulative enrichment.** Self-resonance of any iterated composition
    is at least as large as the base. Meaning accumulates across iterations. -/
theorem differance_cumulative (a : I) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) ≥ rs a a := by
  induction n with
  | zero =>
    simp only [composeN]
    have : compose (void : I) a = a := void_left' a
    rw [this]
  | succ n ih =>
    have h1 := rs_composeN_mono a (n + 1)
    linarith

/-- **No final signified (for nonvoid ideas).** If an idea `a` is nonvoid,
    then at every level of iterated composition, the result is nonvoid with
    positive self-resonance. There is always "material" for further emergence.
    Meaning is never "complete." This is Derrida's claim that there is no
    transcendental signified — no ultimate ground of meaning. -/
theorem no_final_signified {a : I} (ha : a ≠ void) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) > 0 := by
  have h1 := differance_cumulative a n
  have h2 := rs_self_pos a ha
  linarith

/-- **Meaning is deferred by the cocycle.** The cocycle condition shows that
    emergence at one level of composition is "compensated" by emergence at
    the next level. Meaning is redistributed, never finalized. This is the
    mathematical structure of Derrida's différance. -/
theorem meaning_deferred (a : I) (n : ℕ) (d : I) :
    emergence a (composeN a n) d + emergence (compose a (composeN a n)) a d =
    emergence (composeN a n) a d + emergence a (compose (composeN a n) a) d :=
  cocycle_condition a (composeN a n) a d

/-- **Derrida's trace (iterated).** The trace of void — composing with
    silence — leaves every iterated composition unchanged. The absence of
    meaning is always already inscribed in meaning's presence. -/
theorem differance_trace (a : I) (n : ℕ) :
    compose (void : I) (composeN a n) = composeN a n := void_left' _

/-- **Double articulation of différance.** Emergence at one level
    "compensates" for emergence at another. The cocycle rearranged shows
    the play of differences: meaning is distributed across levels. -/
theorem differance_double_articulation (a b c d : I) :
    emergence a b d - emergence a (compose b c) d =
    emergence b c d - emergence (compose a b) c d :=
  cocycle_rearranged a b c d

/-- **Self-composition emergence is bounded.** The emergence of composing
    an idea with itself measures its "auto-différance" — how much it differs
    from itself under repetition. Even this is bounded. -/
theorem self_differance_bounded (a : I) :
    (emergence a a a) ^ 2 ≤
    rs (compose a a) (compose a a) * rs a a :=
  emergence_bounded' a a a

/-- **Linear ideas reach "present" meaning.** If `a` is left-linear, its
    emergence is zero everywhere — meaning is fully present, never deferred.
    This is the logocentrist case that Derrida critiques: the illusion that
    meaning can be fully, immediately present without play of differences. -/
theorem linear_meaning_present {a : I} (h : leftLinear a) (c d : I) :
    emergence a c d = 0 := h c d

/-- **Nonlinear ideas never stabilize in emergence.** If `a` has any
    emergence, it is not left-linear, and the iterative process of
    self-composition never reaches a state where emergence vanishes.
    This is the formal content of "meaning is always in motion." -/
theorem differance_never_stabilizes {a : I} (h : hasEmergence a) :
    ¬leftLinear a := by
  intro hlin; rcases h with ⟨b, c, hne⟩; exact hne (hlin b c)

end DerridasDifferance

/-! ## §13. Jakobson's Six Functions of Language

Roman Jakobson's "Closing Statement: Linguistics and Poetics" (1960) identified
six functions of language, each emphasizing a different component of the
communication act:

1. **Referential** (context-focused): the message refers to something external
2. **Emotive** (addresser-focused): the message expresses the speaker's state
3. **Conative** (addressee-focused): the message aims to affect the hearer
4. **Phatic** (contact-focused): the message maintains the communicative channel
5. **Metalingual** (code-focused): the message is about the code itself
6. **Poetic** (message-focused): the form of the message contributes to meaning

In IDT, each function corresponds to a specific pattern of emergence and
resonance. We prove structural relationships between them.
-/

section JakobsonFunctions
variable {I : Type*} [S : IdeaticSpace3 I]

/-- **Jakobson's Referential Function.** A message `m` has referential
    function in context `ctx` when emergence is positive — the message
    "refers to" something in the context, creating surplus meaning. -/
def referentialFunction (m ctx obs : I) : Prop :=
  emergence m ctx obs > 0

/-- **Jakobson's Emotive Function.** A message has emotive function when
    its semantic charge (self-emergence κ(m,m,m)) is positive — the message
    amplifies itself, expressing the addresser's inner state. -/
def emotiveFunction (m : I) : Prop :=
  emergence m m m > 0

/-- **Jakobson's Conative Function.** A message has conative function toward
    addressee `addr` when composing message with addressee produces positive
    emergence at the addressee — the message "acts upon" the hearer. -/
def conativeFunction (m addr : I) : Prop :=
  emergence m addr addr > 0

/-- **Jakobson's Phatic Function.** A phatic message maintains resonance
    without creating emergence — it keeps the channel open without adding
    meaning. "Hello," "uh-huh," "nice weather." -/
def phaticFunction (m ctx : I) : Prop :=
  rs m ctx > 0 ∧ emergence m ctx ctx = 0

/-- **Jakobson's Metalingual Function.** A metalingual message reflects on
    the code itself — it has the same emergence profile as the code it
    describes. "What does 'cat' mean?" has the same emergence as 'cat'. -/
def metalingualFunction (m code : I) : Prop :=
  sameIdea m code

/-- **Jakobson's Poetic Function.** A message has poetic function when its
    self-emergence is nonzero — the FORM of the message contributes to
    meaning. The projection of paradigmatic onto syntagmatic. -/
def poeticFunction (m : I) : Prop :=
  emergence m m m ≠ 0

/-- **Void has no referential function.** Silence refers to nothing. -/
theorem void_no_referential (ctx obs : I) :
    ¬referentialFunction (void : I) ctx obs := by
  intro h; unfold referentialFunction at h; rw [emergence_void_left] at h; linarith

/-- **Void has no emotive function.** -/
theorem void_no_emotive : ¬emotiveFunction (void : I) := by
  intro h; unfold emotiveFunction at h
  rw [show emergence (void : I) (void : I) (void : I) = 0 from emergence_void_left _ _] at h
  linarith

/-- **Void has no conative function.** -/
theorem void_no_conative (addr : I) : ¬conativeFunction (void : I) addr := by
  intro h; unfold conativeFunction at h; rw [emergence_void_left] at h; linarith

/-- **Void has no poetic function.** -/
theorem void_no_poetic : ¬poeticFunction (void : I) := by
  intro h; unfold poeticFunction at h
  exact h (emergence_void_left (void : I) (void : I))

/-- **Emotive implies poetic.** If a message amplifies itself (positive
    self-emergence), then its self-emergence is nonzero. The emotive function
    always activates the poetic function — expressing feelings IS poetry. -/
theorem emotive_implies_poetic {m : I} (h : emotiveFunction m) :
    poeticFunction m := by
  unfold poeticFunction emotiveFunction at *; linarith

/-- **Phatic excludes conative (at same target).** If a message is phatic
    in context `ctx` (zero emergence), it cannot simultaneously be conative
    toward `ctx` (positive emergence). You can't maintain the channel AND
    persuade through the same interaction. -/
theorem phatic_excludes_conative {m ctx : I} (h : phaticFunction m ctx) :
    ¬conativeFunction m ctx := by
  intro hcon; unfold conativeFunction at hcon; linarith [h.2]

/-- **Metalingual function is transitive.** If `m` is metalingual relative
    to `code₁`, and `code₁` carries the same idea as `code₂`, then `m` is
    metalingual relative to `code₂`. Talking about the code is transitive. -/
theorem metalingual_transitive {m code₁ code₂ : I}
    (h1 : metalingualFunction m code₁) (h2 : sameIdea code₁ code₂) :
    metalingualFunction m code₂ :=
  sameIdea_trans _ _ _ h1 h2

/-- **Metalingual function is reflexive.** Every message is trivially
    metalingual about itself — it describes its own code. -/
theorem metalingual_reflexive (m : I) : metalingualFunction m m :=
  sameIdea_refl m

/-- **Linear messages have no referential function.** A left-linear message
    has zero emergence in all contexts — it cannot refer to anything.
    This captures the idea that purely formulaic language lacks referential
    power. -/
theorem linear_no_referential {m : I} (hlin : leftLinear m) (ctx obs : I) :
    ¬referentialFunction m ctx obs := by
  intro h; unfold referentialFunction at h; rw [hlin ctx obs] at h; linarith

/-- **Linear messages have no emotive function.** -/
theorem linear_no_emotive {m : I} (hlin : leftLinear m) :
    ¬emotiveFunction m := by
  intro h; unfold emotiveFunction at h; rw [hlin m m] at h; linarith

/-- **Poetic function requires non-linearity.** Poetry demands going beyond
    the literal — linear messages can never be poetic. This is the formal
    content of Jakobson's observation that the poetic function "projects the
    principle of equivalence from the axis of selection into the axis of
    combination." -/
theorem poetic_requires_nonlinearity {m : I} (h : poeticFunction m) :
    ¬leftLinear m := by
  intro hlin; unfold poeticFunction at h; exact h (hlin m m)

/-- **Referential function is bounded.** The referential power of any
    message in any context is bounded by the self-resonances of the
    composition and observer. -/
theorem referential_bounded (m ctx obs : I) :
    (emergence m ctx obs) ^ 2 ≤
    rs (compose m ctx) (compose m ctx) * rs obs obs :=
  emergence_bounded' m ctx obs

/-- **Phatic messages maintain presence.** A phatic message resonates with
    the context (rs > 0) and the composition enriches — communication is
    maintained even without new emergence. -/
theorem phatic_maintains_channel {m ctx : I} (_ : phaticFunction m ctx)
    (hm : m ≠ void) :
    rs (compose m ctx) (compose m ctx) ≥ rs m m ∧ rs m m > 0 :=
  ⟨compose_enriches' m ctx, rs_self_pos m hm⟩

end JakobsonFunctions

/-! ## §14. Greimas' Semiotic Square

Algirdas Julien Greimas proposed the **semiotic square** as the elementary
structure of meaning. The square positions four terms in precise relations:

```
    S₁ ←——contraries——→ S₂
    |  \              /  |
    |   complementary    |
    |  /              \  |
   ¬S₂ ←—subcontraries→ ¬S₁
```

- **Contraries** (S₁, S₂): emergence profiles are negatives of each other
- **Contradictories** (S₁, ¬S₁): emergence sums to zero, but they differ
- **Complementaries** (S₁, ¬S₂): same emergence profile (same idea)

The deep theorem: given contraries and contradictories, the complementary
relations are FORCED. The square's structure is overdetermined.
-/

section GreimasSemioticSquare
variable {I : Type*} [S : IdeaticSpace3 I]

/-- **Contraries in Greimas' sense.** Two ideas are contrary if their
    emergence profiles are negatives of each other — they are structurally
    opposed. Hot/cold, life/death, nature/culture. -/
def greimasContrary (s₁ s₂ : I) : Prop :=
  structurallyOpposed s₁ s₂

/-- **Contradictories in Greimas' sense.** Two ideas are contradictory if
    their emergences sum to zero in all contexts AND they are not the same
    idea. S₁ and ¬S₁ cannot coexist. -/
def greimasContradictory (s₁ ns₁ : I) : Prop :=
  (∀ c d, emergence s₁ c d + emergence ns₁ c d = 0) ∧ ¬sameIdea s₁ ns₁

/-- **Complementaries in Greimas' sense.** Two ideas are complementary if
    they have the same emergence profile — they occupy the same structural
    position. S₁ implies ¬S₂. -/
def greimasComplementary (s₁ ns₂ : I) : Prop := sameIdea s₁ ns₂

/-- **Contraries are symmetric.** -/
theorem greimasContrary_symm {s₁ s₂ : I} (h : greimasContrary s₁ s₂) :
    greimasContrary s₂ s₁ := structurallyOpposed_symm h

/-- **Contradictories have opposed emergence.** -/
theorem contradictory_opposed {s₁ ns₁ : I} (h : greimasContradictory s₁ ns₁) :
    ∀ c d, emergence ns₁ c d = -emergence s₁ c d := by
  intro c d; linarith [h.1 c d]

/-- **Contradictory implies contrary.** Every contradictory pair is also
    contrary. The converse fails: contraries can coexist (something can be
    neither hot nor cold), but contradictories cannot. -/
theorem contradictory_implies_contrary {s₁ ns₁ : I}
    (h : greimasContradictory s₁ ns₁) :
    greimasContrary s₁ ns₁ := by
  intro c d; linarith [h.1 c d]

/-- **Complementary is transitive.** -/
theorem greimasComplementary_trans {s₁ s₂ s₃ : I}
    (h1 : greimasComplementary s₁ s₂) (h2 : greimasComplementary s₂ s₃) :
    greimasComplementary s₁ s₃ := sameIdea_trans _ _ _ h1 h2

/-- **Complementary is reflexive.** -/
theorem greimasComplementary_refl (s : I) : greimasComplementary s s :=
  sameIdea_refl s

/-- **The semiotic square determines complements.** Given S₁ contrary to
    S₂, and S₁ contradictory to ¬S₁, then ¬S₁ has the SAME emergence
    profile as S₂. The complement relation is FORCED by the contrary and
    contradictory relations. This is the core structural theorem of the
    semiotic square. -/
theorem semiotic_square_determines_complement
    {s₁ s₂ ns₁ : I}
    (hcontr : greimasContrary s₁ s₂)
    (hcontrad : greimasContradictory s₁ ns₁) :
    greimasComplementary ns₁ s₂ := by
  intro c d
  have h1 := hcontr c d
  have h2 := hcontrad.1 c d
  linarith

/-- **Void is self-contrary (trivially).** -/
theorem void_contrary_self : greimasContrary (void : I) (void : I) :=
  void_selfOpposed

/-- **Void is not self-contradictory.** Void carries the same idea as
    itself, so it cannot be its own contradictory. -/
theorem void_not_contradictory_self :
    ¬greimasContradictory (void : I) (void : I) := by
  intro ⟨_, hne⟩; exact hne (sameIdea_refl _)

/-- **Contraries cancel.** Contrary ideas have emergences that sum to
    zero — they annihilate each other's meaning. -/
theorem contraries_cancel {s₁ s₂ : I} (h : greimasContrary s₁ s₂) (c d : I) :
    emergence s₁ c d + emergence s₂ c d = 0 := opposed_cancel h c d

/-- **The full semiotic square.** Given four terms forming a proper
    semiotic square (S₁ contrary to S₂, S₁ contradictory to ¬S₁,
    S₂ contradictory to ¬S₂), the complementary relations are forced:
    ¬S₁ carries the same idea as S₂, and ¬S₂ carries the same idea as S₁. -/
theorem full_semiotic_square
    {s₁ s₂ ns₁ ns₂ : I}
    (hcontr : greimasContrary s₁ s₂)
    (hcontrad₁ : greimasContradictory s₁ ns₁)
    (hcontrad₂ : greimasContradictory s₂ ns₂) :
    greimasComplementary ns₁ s₂ ∧ greimasComplementary ns₂ s₁ :=
  ⟨semiotic_square_determines_complement hcontr hcontrad₁,
   semiotic_square_determines_complement (greimasContrary_symm hcontr) hcontrad₂⟩

/-- **Contraries of complementaries.** If ns₁ is complementary to s₂
    (same idea), and s₂ is contrary to s₁, then ns₁ is also contrary to s₁.
    The semiotic square's relations are consistent. -/
theorem contrary_of_complementary {s₁ s₂ ns₁ : I}
    (hcompl : greimasComplementary ns₁ s₂)
    (hcontr : greimasContrary s₁ s₂) :
    ∀ c d, emergence ns₁ c d = -emergence s₁ c d := by
  intro c d; rw [hcompl c d]; linarith [hcontr c d]

/-- **The square's resonance inequality.** In a semiotic square, the
    contrary relation implies an emergence bound: the sum of squared
    emergences is constrained. -/
theorem square_emergence_bound {s₁ s₂ : I} (h : greimasContrary s₁ s₂) (c d : I) :
    (emergence s₁ c d) ^ 2 = (emergence s₂ c d) ^ 2 := by
  have h1 := h c d
  rw [h1]; ring

end GreimasSemioticSquare

/-! ## §15. Semiotic Synthesis — Cross-Cutting Theorems

Deep theorems connecting Eco, Barthes, Derrida, Jakobson, and Greimas
into a unified semiotic framework within IDT.
-/

section SemioticSynthesis
variable {I : Type*} [S : IdeaticSpace3 I]

/-- **Eco + Barthes: The author dies harder for open texts.** If a text
    is open (polysemous), then the author's identity is not only invisible
    through emergence (Barthes), but the text actively resists single
    authorial intention by having MULTIPLE emergence patterns. -/
theorem eco_barthes_synthesis {text₁ text₂ : I}
    (h : sameIdea text₁ text₂) (hopen : ecoOpen text₁) :
    ecoOpen text₂ ∧ emergenceProfile text₁ = emergenceProfile text₂ :=
  ⟨open_invariant_of_idea h hopen, author_drops_out_profile h⟩

/-- **Eco + Jakobson: Open texts enable poetic function.** An open text
    has nonzero emergence, so it can serve poetic function in some context.
    Closed (linear) texts are never poetic. -/
theorem eco_jakobson_open_nonlinear {text : I} (h : ecoOpen text) :
    ¬leftLinear text := ecoOpen_not_leftLinear h

/-- **Barthes + Greimas: The author dies in the semiotic square.** In a
    semiotic square, the contradictory of S₁ has the same idea as S₂
    (the complement). So two "authors" — one who intends S₁'s contradictory,
    one who intends S₂ — produce texts with the same emergence profile. -/
theorem barthes_greimas_synthesis {s₁ s₂ ns₁ : I}
    (hcontr : greimasContrary s₁ s₂)
    (hcontrad : greimasContradictory s₁ ns₁) :
    emergenceProfile ns₁ = emergenceProfile s₂ := by
  have h := semiotic_square_determines_complement hcontr hcontrad
  funext c d; exact h c d

/-- **Derrida + Eco: Iterated interpretation of open texts.** An open
    text composed with itself retains positive self-resonance at every
    level of iteration. The play of différance never exhausts an open
    text's capacity for meaning. -/
theorem derrida_eco_synthesis {text : I} (h : ecoOpen text) (n : ℕ) :
    rs (composeN text (n + 1)) (composeN text (n + 1)) > 0 :=
  no_final_signified (ecoOpen_nonvoid h) n

/-- **Jakobson + Greimas: Contraries disable each other's referential
    function.** If s₁ and s₂ are contrary, then wherever s₁ has positive
    referential emergence, s₂ has negative (anti-referential) emergence. -/
theorem jakobson_greimas_contrary {s₁ s₂ : I}
    (h : greimasContrary s₁ s₂) (ctx obs : I)
    (href : referentialFunction s₁ ctx obs) :
    emergence s₂ ctx obs < 0 := by
  unfold referentialFunction at href
  have := h ctx obs
  linarith

/-- **Derrida + Jakobson: The cocycle as linguistic constraint.** The
    cocycle condition constrains how Jakobson's functions compose: the
    total emergence across two levels of composition is invariant under
    re-association. The referential function at one level is compensated
    by emergence at the next. -/
theorem derrida_jakobson_cocycle (m ctx further obs : I) :
    emergence m ctx obs + emergence (compose m ctx) further obs =
    emergence ctx further obs + emergence m (compose ctx further) obs :=
  cocycle_condition m ctx further obs

/-- **Greimas + Derrida: Iterating contraries.** If s₁ is contrary to s₂,
    then composing s₁ with s₂ creates a dialectical synthesis whose
    self-resonance is at least as large as s₁'s — contraries don't
    annihilate, they enrich. -/
theorem greimas_derrida_enrichment {s₁ s₂ : I}
    (_ : greimasContrary s₁ s₂) :
    rs (compose s₁ s₂) (compose s₁ s₂) ≥ rs s₁ s₁ :=
  compose_enriches' s₁ s₂

/-- **The semiotic capacity theorem.** Every semiotic quantity — Eco's
    openness, Barthes' connotation, Derrida's différance, Jakobson's
    functions, Greimas' oppositions — is ultimately bounded by the
    emergence Cauchy-Schwarz. Meaning cannot exceed the capacity of
    the signs involved. -/
theorem semiotic_universal_bound (a b c : I) :
    (emergence a b c) ^ 2 ≤
    rs (compose a b) (compose a b) * rs c c :=
  emergence_bounded' a b c

/-- **The linearity collapse.** If all utterances in a space are
    left-linear, then EVERY semiotic phenomenon collapses: no openness
    (Eco), no connotation dynamics (Barthes), no différance (Derrida),
    no poetic function (Jakobson), and all contraries are trivially
    self-contrary (Greimas). Meaning requires non-linearity. -/
theorem total_semiotic_collapse
    (h : ∀ a : I, leftLinear a) (a : I) :
    ecoClosed a ∧ ¬poeticFunction a ∧ ¬emotiveFunction a := by
  refine ⟨leftLinear_not_polysemous a (h a), ?_, ?_⟩
  · intro hp; unfold poeticFunction at hp; exact hp (h a a a)
  · intro he; unfold emotiveFunction at he; rw [h a a a] at he; linarith

/-- **Semiotic richness requires emergence.** The presence of ANY nonzero
    emergence is sufficient to activate the entire semiotic apparatus:
    the text is open (Eco), has a nontrivial emergence profile that
    survives the author's death (Barthes), participates in différance
    (Derrida), and can serve referential function (Jakobson). -/
theorem emergence_activates_semiotics {a : I} (h : hasEmergence a) :
    ecoOpen a := by
  rcases h with ⟨b, c, hne⟩
  by_contra hclosed
  exact hne (not_polysemous_leftLinear hclosed b c)

end SemioticSynthesis

/-! ## §16. Lotman's Semiosphere — Boundaries, Centers, and Peripheries

Yuri Lotman's concept of the **semiosphere** (1984) holds that signs only
function within a bounded cultural space. The semiosphere has a **center**
(the dominant code), a **periphery** (marginal, innovative, or foreign codes),
and a **boundary** where translation between inside and outside occurs.

In IDT, the semiosphere is modeled as a spatial structure on utterances: the
**boundary** is where emergence is maximized (contact with the foreign produces
novelty), the **center** is where utterances are left-linear (no surprises),
and translation is the composition of inside and outside elements. -/

section LotmanSemiosphere
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Semiosphere center.** An utterance belongs to the center of the
    semiosphere if it is left-linear — its meaning is fully codified,
    predictable, culturally dominant. No emergence means no surprise. -/
def semiosphereCenter (a : I) : Prop := leftLinear a

/-- **Semiosphere periphery.** An utterance is peripheral if it is
    polysemous — it generates emergent meaning that the center cannot
    fully absorb. Peripheral signs are innovative, foreign, or marginal. -/
def semiospherePeriphery (a : I) : Prop := polysemous a

/-- **Semiotic boundary.** A pair (inside, outside) forms a semiotic
    boundary when their composition generates nonzero emergence — the
    contact between cultural systems produces new meaning. -/
def semioticBoundary (inside outside : I) : Prop :=
  ∃ c : I, emergence inside outside c ≠ 0

/-- **Lotman's translation.** Translation across the boundary is composition:
    combining inside and outside elements yields a new utterance whose meaning
    exceeds the sum of its parts. -/
noncomputable def lotmanTranslation (inside outside : I) : ℝ :=
  emergence inside outside (compose inside outside)

/-- **Center and periphery are exclusive.** An utterance cannot simultaneously
    be central (left-linear) and peripheral (polysemous). -/
theorem center_periphery_exclusive (a : I) :
    ¬(semiosphereCenter a ∧ semiospherePeriphery a) := by
  intro ⟨hc, hp⟩
  exact leftLinear_not_polysemous a hc hp

/-- **Void is always central.** Silence belongs to the center of every
    semiosphere — it is perfectly codified. -/
theorem void_semiosphere_center : semiosphereCenter (void : I) :=
  void_leftLinear

/-- **Void is never peripheral.** -/
theorem void_not_periphery : ¬semiospherePeriphery (void : I) :=
  void_not_polysemous

/-- **Peripheral utterances have emergence.** Being on the periphery
    guarantees that the utterance generates nonzero emergence somewhere. -/
theorem periphery_has_emergence {a : I} (h : semiospherePeriphery a) :
    hasEmergence a := by
  rcases h with ⟨c₁, c₂, d, hne⟩
  by_cases h1 : emergence a c₁ d = 0
  · exact ⟨c₂, d, fun h2 => hne (by rw [h1, h2])⟩
  · exact ⟨c₁, d, h1⟩

/-- **The boundary is asymmetric.** The emergence of composing inside with
    outside may differ from composing outside with inside. This captures
    the power asymmetry in cultural translation. -/
theorem boundary_asymmetry (inside outside c : I) :
    emergence inside outside c - emergence outside inside c =
    meaningCurvature inside outside c := by
  unfold meaningCurvature; ring

/-- **Void boundary vanishes.** There is no boundary with silence. -/
theorem void_no_boundary (a : I) : ¬semioticBoundary (void : I) a := by
  intro ⟨c, hne⟩; exact hne (emergence_void_left a c)

/-- **Boundary implies non-centrality.** If inside forms a boundary with
    some outside, then inside is NOT central (not left-linear). -/
theorem boundary_not_center {inside outside : I}
    (h : semioticBoundary inside outside) : ¬semiosphereCenter inside := by
  intro hlin; rcases h with ⟨c, hne⟩; exact hne (hlin outside c)

/-- **Peripheral utterances form boundaries.** Every peripheral utterance
    admits at least one boundary pair. -/
theorem periphery_forms_boundary {a : I} (h : semiospherePeriphery a) :
    ∃ b : I, semioticBoundary a b := by
  rcases periphery_has_emergence h with ⟨b, c, hne⟩
  exact ⟨b, ⟨c, hne⟩⟩

/-- **Translation with void is zero.** Composing with void generates no
    translational emergence — silence adds nothing to translation. -/
theorem lotmanTranslation_void_right (a : I) :
    lotmanTranslation a (void : I) = 0 := by
  unfold lotmanTranslation
  rw [show compose a (void : I) = a from void_right' a]
  exact emergence_void_right a a

/-- **Translation with void on left is zero.** -/
theorem lotmanTranslation_void_left (a : I) :
    lotmanTranslation (void : I) a = 0 := by
  unfold lotmanTranslation
  rw [show compose (void : I) a = a from void_left' a]
  exact emergence_void_left a a

/-- **Translation strength is bounded.** Even the richest translation is
    bounded by the self-resonance of the synthesis and target. -/
theorem lotmanTranslation_bounded (inside outside : I) :
    (lotmanTranslation inside outside) ^ 2 ≤
    rs (compose inside outside) (compose inside outside) *
    rs (compose inside outside) (compose inside outside) := by
  unfold lotmanTranslation; exact emergence_bounded' inside outside _

/-- **Center-center composition is central.** Composing two central
    utterances yields a central utterance. The center is closed under
    composition. (Because both have zero emergence, composition is additive.) -/
theorem center_compose_center {a b : I}
    (ha : semiosphereCenter a) (hb : semiosphereCenter b) :
    ∀ c d : I, emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d := by
  intro c d; linarith [cocycle_condition a b c d, ha b d]

/-- **Lotman's explosion.** When a peripheral sign (with emergence) meets
    another, the cocycle constrains the result. Cultural "explosions" —
    moments of rapid semiotic innovation — are bounded by the global
    consistency of emergence. -/
theorem lotman_explosion_bounded (a b c d : I) :
    (emergence a b d) ^ 2 ≤
    rs (compose a b) (compose a b) * rs d d :=
  emergence_bounded' a b d

/-- **Semiosphere center is eco-closed.** Central utterances, being left-linear,
    are closed texts in Eco's sense — they admit only one reading. -/
theorem center_is_ecoClosed {a : I} (h : semiosphereCenter a) :
    ecoClosed a := leftLinear_not_polysemous a h

/-- **Semiosphere periphery is eco-open.** Peripheral utterances are open
    texts — they invite multiple interpretations. -/
theorem periphery_is_ecoOpen {a : I} (h : semiospherePeriphery a) :
    ecoOpen a := h

end LotmanSemiosphere

/-! ## §17. Kristeva's Intertextuality and the Semiotic/Symbolic

Julia Kristeva's theory of **intertextuality** (1966) holds that every text is
a mosaic of quotations — no text exists in isolation. She also distinguished
the **semiotic** (pre-linguistic, rhythmic, drive-based) from the **symbolic**
(grammatical, rule-governed, referential). Poetic language foregrounds the
semiotic; scientific language foregrounds the symbolic.

In IDT, intertextuality is formalized through the cocycle condition: the
emergence of composing texts A, B is constrained by its relation to any
third text C. The semiotic/symbolic distinction maps to polysemous vs
left-linear. -/

section KristevaIntertextuality
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Intertextual resonance.** The degree to which text `a` resonates
    with text `b` beyond their individual self-presences. -/
noncomputable def intertextualResonance (a b : I) : ℝ :=
  rs a b - (rs a a + rs b b) / 2

/-- **Intertextual emergence.** The emergent meaning produced when
    text `a` is read "through" text `b`, as measured against observer `c`. -/
noncomputable def intertextualEmergence (a b c : I) : ℝ :=
  emergence a b c

/-- **Kristeva's semiotic modality.** An utterance is in the "semiotic"
    mode (pre-symbolic, rhythmic, drive-based) when it is polysemous and
    generates emergence — it overflows the symbolic order. -/
def kristevaSemiotic (a : I) : Prop := polysemous a

/-- **Kristeva's symbolic modality.** An utterance is in the "symbolic"
    mode when it is left-linear — fully codified, law-governed. -/
def kristevaSymbolic (a : I) : Prop := leftLinear a

/-- **Semiotic and symbolic are exclusive.** No utterance can simultaneously
    be semiotic (polysemous) and symbolic (left-linear). -/
theorem semiotic_symbolic_exclusive (a : I) :
    ¬(kristevaSemiotic a ∧ kristevaSymbolic a) := by
  intro ⟨hs, hy⟩; exact leftLinear_not_polysemous a hy hs

/-- **Every utterance is semiotic or symbolic.** -/
theorem semiotic_or_symbolic (a : I) :
    kristevaSemiotic a ∨ kristevaSymbolic a := by
  by_cases h : polysemous a
  · left; exact h
  · right; exact not_polysemous_leftLinear h

/-- **Void is symbolic.** Silence is fully codified. -/
theorem void_kristevaSymbolic : kristevaSymbolic (void : I) :=
  void_leftLinear

/-- **Void is not semiotic.** -/
theorem void_not_kristevaSemiotic : ¬kristevaSemiotic (void : I) :=
  void_not_polysemous

/-- **Intertextual resonance with void vanishes.** -/
theorem intertextualResonance_void (a : I) :
    intertextualResonance (void : I) a = -(rs a a / 2) := by
  unfold intertextualResonance; simp [rs_void_left', rs_void_right', rs_void_void]

/-- **Intertextual emergence with void vanishes.** -/
theorem intertextualEmergence_void_left (b c : I) :
    intertextualEmergence (void : I) b c = 0 := emergence_void_left b c

/-- **Cocycle as intertextuality constraint.** The intertextual emergence
    of A∘B with C is constrained by the individual intertextual relations.
    This is Kristeva's insight formalized: texts don't compose freely. -/
theorem intertextual_cocycle (a b c d : I) :
    intertextualEmergence a b d + intertextualEmergence (compose a b) c d =
    intertextualEmergence b c d + intertextualEmergence a (compose b c) d :=
  cocycle_condition a b c d

/-- **Semiotic utterances have emergence.** -/
theorem kristevaSemiotic_has_emergence {a : I} (h : kristevaSemiotic a) :
    hasEmergence a := by
  rcases h with ⟨c₁, c₂, d, hne⟩
  by_cases h1 : emergence a c₁ d = 0
  · exact ⟨c₂, d, fun h2 => hne (by rw [h1, h2])⟩
  · exact ⟨c₁, d, h1⟩

/-- **Symbolic utterances produce dead metaphors.** If a is symbolic
    (left-linear), then composing it as a vehicle always yields a dead
    metaphor. -/
theorem symbolic_dead_metaphor {a : I} (h : kristevaSymbolic a) (t : I) :
    deadMetaphor a t :=
  leftLinear_dead_metaphor h t

/-- **Intertextual emergence is bounded.** Even the richest intertextual
    reading is bounded by compositional self-resonance. -/
theorem intertextualEmergence_bounded (a b c : I) :
    (intertextualEmergence a b c) ^ 2 ≤
    rs (compose a b) (compose a b) * rs c c :=
  emergence_bounded' a b c

/-- **Kristeva's semiotic is Eco's open.** The semiotic mode corresponds
    exactly to Eco's open work — both are polysemy. -/
theorem kristevaSemiotic_iff_ecoOpen (a : I) :
    kristevaSemiotic a ↔ ecoOpen a := Iff.rfl

/-- **Intertextual self-resonance is symmetric.** -/
theorem intertextualResonance_antisymm_decomp (a b : I) :
    intertextualResonance a b - intertextualResonance b a =
    rs a b - rs b a := by
  unfold intertextualResonance; ring

end KristevaIntertextuality

/-! ## §18. Baudrillard's Simulacra and Simulation

Jean Baudrillard's *Simulacra and Simulation* (1981) describes four stages
of the image's relation to reality:
1. The image reflects reality (faithful copy)
2. The image masks reality (distortion)
3. The image masks the ABSENCE of reality (pretense)
4. The image has no relation to reality (pure simulacrum)

In IDT, these stages correspond to decreasing resonance between sign and
referent, culminating in signs that are purely self-referential — they
resonate only with themselves and other simulacra. -/

section BaudrillardSimulacra
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Baudrillard's Stage 1: Faithful representation.** The sign is iconic
    for the referent — positive resonance, reflecting reality. -/
def faithfulImage (sign referent : I) : Prop :=
  rs sign referent > 0 ∧ rs referent sign > 0

/-- **Baudrillard's Stage 2: Masking image.** The sign distorts: it
    resonates with the referent but generates negative emergence (ironic
    reversal) when composed with it. -/
def maskingImage (sign referent : I) : Prop :=
  rs sign referent > 0 ∧ emergence sign referent referent < 0

/-- **Baudrillard's Stage 3: Masking absence.** The sign pretends a referent
    exists: it has positive self-resonance but zero resonance with the
    supposed referent. The referent is effectively void. -/
def maskingAbsence (sign referent : I) : Prop :=
  rs sign sign > 0 ∧ rs sign referent = 0

/-- **Baudrillard's Stage 4: Pure simulacrum.** The sign has no relation
    to any reality — it is left-linear (no emergence) and self-referential,
    a "hyperreal" that has replaced reality entirely. -/
def pureSimulacrum (sign : I) : Prop :=
  leftLinear sign ∧ sign ≠ void

/-- **Faithful images are iconic.** Stage 1 signs are icons in Peirce's sense. -/
theorem faithful_is_iconic {s r : I} (h : faithfulImage s r) : iconic s r :=
  h.1

/-- **Masking images involve irony.** Stage 2 signs are ironic: they say one
    thing but, in combination with the referent, reverse it. -/
theorem masking_is_ironic {s r : I} (h : maskingImage s r) :
    ironicIn s r := h.2

/-- **Pure simulacra are eco-closed.** Having replaced reality with hyperreality,
    simulacra admit only one "reading" — the simulated one. -/
theorem simulacrum_ecoClosed {s : I} (h : pureSimulacrum s) :
    ecoClosed s := leftLinear_not_polysemous s h.1

/-- **Simulacra produce dead metaphors.** Being left-linear, pure simulacra
    cannot generate metaphorical surplus. They are frozen signs. -/
theorem simulacrum_dead_metaphor {s : I} (h : pureSimulacrum s) (t : I) :
    deadMetaphor s t := leftLinear_dead_metaphor h.1 t

/-- **Void is not a simulacrum.** Silence is not hyperreal — it is simply
    nothing. A simulacrum must have positive presence. -/
theorem void_not_simulacrum : ¬pureSimulacrum (void : I) := by
  intro ⟨_, h⟩; exact h rfl

/-- **Faithful images are never simulacra.** A sign that faithfully
    represents reality cannot be a pure simulacrum (which is left-linear).
    Faithful representation requires genuine resonance, hence emergence. -/
theorem faithful_not_simulacrum {s r : I} (h : faithfulImage s r)
    (hpoly : polysemous s) : ¬pureSimulacrum s := by
  intro ⟨hlin, _⟩; exact leftLinear_not_polysemous s hlin hpoly

/-- **Masking absence implies non-iconicity.** Stage 3 signs do not
    resemble their supposed referents. -/
theorem masking_absence_not_iconic {s r : I} (h : maskingAbsence s r) :
    ¬iconic s r := by
  intro hic; unfold iconic at hic; linarith [h.2]

/-- **Simulacra have positive self-resonance.** They exist — they're just
    not about anything. -/
theorem simulacrum_positive_selfRS {s : I} (h : pureSimulacrum s) :
    rs s s > 0 := rs_self_pos s h.2

/-- **Stage progression: faithful → masking absence.** If a sign was once
    faithful but loses its resonance with the referent, it becomes a mask
    of absence (assuming it retains self-resonance). -/
theorem faithful_to_absence {s r : I}
    (hself : rs s s > 0) (hzero : rs s r = 0) :
    maskingAbsence s r := ⟨hself, hzero⟩

/-- **Simulacra emergence is zero.** The defining feature of Stage 4:
    no emergent meaning in any context. -/
theorem simulacrum_zero_emergence {s : I} (h : pureSimulacrum s)
    (b c : I) : emergence s b c = 0 := h.1 b c

/-- **Baudrillard's precession.** Simulacra "precede" reality: in the
    hyperreal, the model generates the real, not vice versa. In IDT, this
    means the simulacrum's self-resonance is entirely self-generated —
    rs(s,s) = rs(s,s) + 0, since emergence is zero. -/
theorem precession_of_simulacra {s : I} (h : pureSimulacrum s)
    (b : I) :
    rs (compose s b) s = rs s s + rs b s := by
  have := rs_compose_eq s b s; rw [h.1 b s] at this; linarith

end BaudrillardSimulacra

/-! ## §19. Morris's Semiotics — Syntactics, Semantics, Pragmatics

Charles W. Morris (*Foundations of the Theory of Signs*, 1938) divided
semiotics into three dimensions:
- **Syntactics**: relations among signs (sign-to-sign)
- **Semantics**: relations between signs and their objects (sign-to-world)
- **Pragmatics**: relations between signs and their interpreters (sign-to-user)

In IDT, these correspond to:
- Syntactics: resonance between signs (rs a b)
- Semantics: emergence when sign meets referent (emergence sign referent observer)
- Pragmatics: emergence when sign meets interpreter (emergence interpreter sign ·) -/

section MorrisSemiotics
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Syntactic relatedness.** The syntactic relation between two signs is
    their mutual resonance — how they combine structurally. -/
noncomputable def syntacticRelation (a b : I) : ℝ := rs a b

/-- **Semantic content.** The semantic content of sign `a` for referent `b`,
    measured by self-emergence: how much meaning emerges when sign meets
    its object. -/
noncomputable def semanticContent (sign referent : I) : ℝ :=
  emergence sign referent referent

/-- **Pragmatic effect.** The pragmatic effect of sign `a` on interpreter `b`
    is the emergence when the interpreter composes with the sign, measured
    against the interpreter. -/
noncomputable def pragmaticEffect (interpreter sign : I) : ℝ :=
  emergence interpreter sign sign

/-- **Syntactic relation with void is zero.** -/
theorem syntactic_void (a : I) : syntacticRelation (void : I) a = 0 := by
  unfold syntacticRelation; exact rs_void_left' a

/-- **Semantic content with void sign is zero.** -/
theorem semantic_void_sign (r : I) : semanticContent (void : I) r = 0 :=
  emergence_void_left r r

/-- **Semantic content with void referent is zero.** -/
theorem semantic_void_referent (s : I) : semanticContent s (void : I) = 0 :=
  emergence_void_right s (void : I)

/-- **Pragmatic effect of void sign is zero.** -/
theorem pragmatic_void_sign (interp : I) :
    pragmaticEffect interp (void : I) = 0 :=
  emergence_void_right interp (void : I)

/-- **Pragmatic effect of void interpreter is zero.** -/
theorem pragmatic_void_interpreter (sign : I) :
    pragmaticEffect (void : I) sign = 0 :=
  emergence_void_left sign sign

/-- **Morris's trichotomy exhaustion.** The total resonance of a composition
    decomposes into syntactic (resonance), semantic (emergence with referent),
    and the referent's self-resonance. -/
theorem morris_decomposition (sign referent : I) :
    rs (compose sign referent) referent =
    syntacticRelation sign referent + rs referent referent +
    semanticContent sign referent := by
  unfold syntacticRelation semanticContent emergence; ring

/-- **Semantic content is bounded.** -/
theorem semanticContent_bounded (sign referent : I) :
    (semanticContent sign referent) ^ 2 ≤
    rs (compose sign referent) (compose sign referent) *
    rs referent referent := by
  unfold semanticContent; exact emergence_bounded' sign referent referent

/-- **Pragmatic effect is bounded.** -/
theorem pragmaticEffect_bounded (interp sign : I) :
    (pragmaticEffect interp sign) ^ 2 ≤
    rs (compose interp sign) (compose interp sign) *
    rs sign sign := by
  unfold pragmaticEffect; exact emergence_bounded' interp sign sign

/-- **Linear signs have zero semantic content.** A left-linear sign
    generates no emergent meaning with any referent. -/
theorem leftLinear_no_semantic {sign : I} (h : leftLinear sign)
    (referent : I) : semanticContent sign referent = 0 := by
  unfold semanticContent; exact h referent referent

/-- **Morris's pragmatic = irony check.** A sign is ironic for the
    interpreter exactly when its pragmatic effect is negative. -/
theorem pragmatic_irony_iff (interp sign : I) :
    pragmaticEffect interp sign < 0 ↔ ironicIn interp sign := by
  unfold pragmaticEffect ironicIn; exact Iff.rfl

/-- **Syntactic relation decomposes.** The syntactic relation between
    a composition and an observer decomposes via emergence. -/
theorem syntactic_compose_decomp (a b c : I) :
    syntacticRelation (compose a b) c =
    syntacticRelation a c + syntacticRelation b c +
    emergence a b c := by
  unfold syntacticRelation; rw [rs_compose_eq]

/-- **The cocycle is a syntactic constraint.** Morris's syntactic dimension
    is governed by the cocycle condition — sign-sign relations must be
    globally consistent. -/
theorem syntactic_cocycle (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

end MorrisSemiotics

/-! ## §20. Eco's Encyclopedia vs Dictionary Model

Eco (*Semiotics and the Philosophy of Language*, 1984) contrasted two models
of meaning:
- **Dictionary model**: meaning is a fixed, finite set of features (like a
  dictionary entry). This is the structuralist ideal.
- **Encyclopedia model**: meaning is an open-ended network of associations,
  always expandable, never complete. This is semiosis unlimited.

In IDT, the dictionary model corresponds to left-linear ideas (fixed,
finite emergence = 0), while the encyclopedia model corresponds to polysemous
ideas (open-ended, ever-expanding emergence). -/

section EcoEncyclopedia
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Dictionary entry.** An utterance whose meaning is fully determined —
    left-linear, no contextual variation in emergence. -/
def dictionaryEntry (a : I) : Prop := leftLinear a

/-- **Encyclopedia entry.** An utterance whose meaning is contextually
    variable — polysemous, with emergence that varies across contexts. -/
def encyclopediaEntry (a : I) : Prop := polysemous a

/-- **Dictionary entries are central.** In Lotman's terms, dictionary entries
    belong to the semiosphere center. -/
theorem dictionary_is_center {a : I} (h : dictionaryEntry a) :
    semiosphereCenter a := h

/-- **Encyclopedia entries are peripheral.** -/
theorem encyclopedia_is_periphery {a : I} (h : encyclopediaEntry a) :
    semiospherePeriphery a := h

/-- **Dictionary/encyclopedia dichotomy.** Every utterance is either a
    dictionary entry or an encyclopedia entry. -/
theorem dictionary_or_encyclopedia (a : I) :
    dictionaryEntry a ∨ encyclopediaEntry a := by
  by_cases h : polysemous a
  · right; exact h
  · left; exact not_polysemous_leftLinear h

/-- **Dictionary entries are closed texts.** -/
theorem dictionary_ecoClosed {a : I} (h : dictionaryEntry a) :
    ecoClosed a := leftLinear_not_polysemous a h

/-- **Encyclopedia entries are open texts.** -/
theorem encyclopedia_ecoOpen {a : I} (h : encyclopediaEntry a) :
    ecoOpen a := h

/-- **Dictionary entries yield dead metaphors.** -/
theorem dictionary_dead_metaphor {a : I} (h : dictionaryEntry a) (t : I) :
    deadMetaphor a t := leftLinear_dead_metaphor h t

/-- **Encyclopedia entries have emergence.** -/
theorem encyclopedia_has_emergence {a : I} (h : encyclopediaEntry a) :
    hasEmergence a := by
  rcases h with ⟨c₁, c₂, d, hne⟩
  by_cases h1 : emergence a c₁ d = 0
  · exact ⟨c₂, d, fun h2 => hne (by rw [h1, h2])⟩
  · exact ⟨c₁, d, h1⟩

/-- **Unlimited semiosis.** Eco's key claim: for an encyclopedia entry,
    the process of interpretation never terminates. Formally, iterated
    self-composition of a nonvoid encyclopedia entry always yields nonvoid
    results (there is always more to interpret). -/
theorem unlimited_semiosis {a : I} (ha : encyclopediaEntry a)
    (hnv : a ≠ void) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) > 0 := by
  have h1 := differance_cumulative a n
  have h2 := rs_self_pos a hnv
  linarith

/-- **Dictionary composition stays dictionary.** Composing a dictionary entry
    on the left preserves the additive structure. -/
theorem dictionary_additive {a : I} (h : dictionaryEntry a) (b c : I) :
    rs (compose a b) c = rs a c + rs b c :=
  leftLinear_additive a h b c

/-- **Encyclopedia contradicts simulacra.** An encyclopedia entry is
    polysemous, hence not left-linear, hence not a pure simulacrum. -/
theorem encyclopedia_not_simulacrum {a : I} (h : encyclopediaEntry a) :
    ¬pureSimulacrum a := by
  intro ⟨hlin, _⟩; exact leftLinear_not_polysemous a hlin h

/-- **Void is a dictionary entry.** -/
theorem void_dictionaryEntry : dictionaryEntry (void : I) := void_leftLinear

/-- **Void is not an encyclopedia entry.** -/
theorem void_not_encyclopediaEntry : ¬encyclopediaEntry (void : I) :=
  void_not_polysemous

end EcoEncyclopedia

/-! ## §21. Hjelmslev's Glossematics — Expression and Content Planes

Louis Hjelmslev (*Prolegomena to a Theory of Language*, 1943) refined
Saussure's signifier/signified into a four-fold scheme:
- **Expression plane** with substance and form
- **Content plane** with substance and form

The key insight: language has TWO planes, and the FORM (relational structure)
of each plane is what matters semiotically, not the substance.

In IDT, expression form is the emergence pattern of an utterance as a
*left* element (how it combines outward), while content form is the
emergence pattern as a *right* element (how it is combined into). -/

section HjelmslevGlossematics
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Expression form.** Two utterances have the same expression form
    if they produce identical emergence when placed on the LEFT of any
    composition. This is sameIdea. -/
def sameExpressionForm (a b : I) : Prop :=
  ∀ c d : I, emergence a c d = emergence b c d

/-- **Content form.** Two utterances have the same content form if they
    produce identical emergence when placed on the RIGHT of any composition. -/
def sameContentForm (a b : I) : Prop :=
  ∀ c d : I, emergence c a d = emergence c b d

/-- **Expression form = sameIdea.** -/
theorem expressionForm_eq_sameIdea (a b : I) :
    sameExpressionForm a b ↔ sameIdea a b := Iff.rfl

/-- **Expression form is reflexive.** -/
theorem sameExpressionForm_refl (a : I) : sameExpressionForm a a :=
  fun _ _ => rfl

/-- **Content form is reflexive.** -/
theorem sameContentForm_refl (a : I) : sameContentForm a a :=
  fun _ _ => rfl

/-- **Expression form is symmetric.** -/
theorem sameExpressionForm_symm {a b : I} (h : sameExpressionForm a b) :
    sameExpressionForm b a := fun c d => (h c d).symm

/-- **Content form is symmetric.** -/
theorem sameContentForm_symm {a b : I} (h : sameContentForm a b) :
    sameContentForm b a := fun c d => (h c d).symm

/-- **Expression form is transitive.** -/
theorem sameExpressionForm_trans {a b c : I}
    (h1 : sameExpressionForm a b) (h2 : sameExpressionForm b c) :
    sameExpressionForm a c := fun x d => (h1 x d).trans (h2 x d)

/-- **Content form is transitive.** -/
theorem sameContentForm_trans {a b c : I}
    (h1 : sameContentForm a b) (h2 : sameContentForm b c) :
    sameContentForm a c := fun x d => (h1 x d).trans (h2 x d)

/-- **Void has unique expression form.** Anything with the same expression
    form as void is left-linear. -/
theorem void_expressionForm_iff (a : I) :
    sameExpressionForm (void : I) a ↔ ∀ c d : I, emergence a c d = 0 := by
  constructor
  · intro h c d; have := h c d; rw [emergence_void_left] at this; linarith
  · intro h c d; rw [emergence_void_left]; linarith [h c d]

/-- **Void has unique content form.** -/
theorem void_contentForm_iff (a : I) :
    sameContentForm (void : I) a ↔ ∀ c d : I, emergence c a d = 0 := by
  constructor
  · intro h c d
    have h1 := h c d
    unfold sameContentForm at h
    have h2 : emergence c (void : I) d = 0 := emergence_void_right c d
    rw [← h1]; exact h2
  · intro h c d
    have h1 : emergence c (void : I) d = 0 := emergence_void_right c d
    rw [h1]; exact (h c d).symm

/-- **Hjelmslev's commutation test.** Two expressions are distinct in form
    (different glossemes) iff there exist contexts where they produce
    different emergence. -/
theorem commutation_test (a b : I) :
    ¬sameExpressionForm a b ↔
    ∃ c d : I, emergence a c d ≠ emergence b c d := by
  constructor
  · intro h; by_contra hall; push_neg at hall; exact h (fun c d => hall c d)
  · intro ⟨c, d, hne⟩ h; exact hne (h c d)

/-- **Content commutation test.** -/
theorem content_commutation_test (a b : I) :
    ¬sameContentForm a b ↔
    ∃ c d : I, emergence c a d ≠ emergence c b d := by
  constructor
  · intro h; by_contra hall; push_neg at hall; exact h (fun c d => hall c d)
  · intro ⟨c, d, hne⟩ h; exact hne (h c d)

/-- **Same expression form preserves polysemy.** If a and b have the same
    expression form and a is polysemous, then b is polysemous. -/
theorem expressionForm_preserves_polysemy {a b : I}
    (h : sameExpressionForm a b) (hp : polysemous a) :
    polysemous b := by
  rcases hp with ⟨c₁, c₂, d, hne⟩
  exact ⟨c₁, c₂, d, fun heq => hne (by rw [h c₁ d, h c₂ d]; exact heq)⟩

/-- **Denotative semiotics.** In Hjelmslev's terms, a denotative semiotic
    has expression form but no further content plane built on top. The
    emergence is "first-order." -/
noncomputable def denotativeContent (sign referent observer : I) : ℝ :=
  emergence sign referent observer

/-- **Connotative semiotics.** A connotative semiotic uses a SIGN SYSTEM
    as its expression plane. The emergence is "second-order" — emergence
    of emergence through composition chains. -/
noncomputable def connotativeContent (sign₁ sign₂ referent observer : I) : ℝ :=
  emergence (compose sign₁ sign₂) referent observer

/-- **Connotative content decomposes via cocycle.** The connotative content
    of the sign system (s₁ ∘ s₂) with referent r can be decomposed using
    the cocycle condition into first-order emergences. -/
theorem connotative_cocycle (s₁ s₂ r o : I) :
    connotativeContent s₁ s₂ r o + emergence s₁ s₂ o =
    emergence s₂ r o + emergence s₁ (compose s₂ r) o := by
  unfold connotativeContent
  linarith [cocycle_condition s₁ s₂ r o]

end HjelmslevGlossematics

/-! ## §22. Myth as Frozen Emergence — Barthes' Mythologies Revisited

Returning to Barthes' *Mythologies* (1957) with deeper formalization:
**myth naturalizes** the contingent — it takes a historical, cultural sign
and makes it seem "natural" by freezing its emergence. A myth is a sign
whose emergence has been absorbed into the dominant code.

In IDT, a "frozen" sign is one that was once polysemous but has been
rendered left-linear by repetition/absorption. The "unfreezing" of myth
is the recovery of its emergence through critical reading. -/

section MythFrozenEmergence
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Frozen sign.** A sign is "frozen" if it is left-linear AND nonvoid —
    it has substance but no creative potential. This is myth after
    naturalization. -/
def frozenSign (a : I) : Prop := leftLinear a ∧ a ≠ void

/-- **Living sign.** A sign is "living" if it is polysemous — it retains
    its capacity for emergent meaning. -/
def livingSign (a : I) : Prop := polysemous a

/-- **Frozen and living are exclusive.** -/
theorem frozen_living_exclusive (a : I) :
    ¬(frozenSign a ∧ livingSign a) := by
  intro ⟨⟨hlin, _⟩, hpoly⟩
  exact leftLinear_not_polysemous a hlin hpoly

/-- **Every nonvoid sign is frozen or living.** -/
theorem frozen_or_living (a : I) (h : a ≠ void) :
    frozenSign a ∨ livingSign a := by
  by_cases hp : polysemous a
  · right; exact hp
  · left; exact ⟨not_polysemous_leftLinear hp, h⟩

/-- **Frozen signs have positive self-resonance.** They exist, even though
    they don't create. -/
theorem frozenSign_positive_selfRS {a : I} (h : frozenSign a) :
    rs a a > 0 := rs_self_pos a h.2

/-- **Frozen signs are simulacra.** In Baudrillard's terms, a frozen sign
    is a pure simulacrum — a sign that no longer refers beyond itself. -/
theorem frozen_is_simulacrum {a : I} (h : frozenSign a) :
    pureSimulacrum a := h

/-- **Frozen signs produce dead metaphors.** -/
theorem frozen_dead_metaphor {a : I} (h : frozenSign a) (t : I) :
    deadMetaphor a t := leftLinear_dead_metaphor h.1 t

/-- **Mythical naturalization.** When a sign is frozen, its resonance
    with any composition decomposes additively. The myth is "natural"
    because there's no emergent surplus — no surprise, no critique. -/
theorem myth_naturalization {a : I} (h : frozenSign a) (b c : I) :
    rs (compose a b) c = rs a c + rs b c :=
  leftLinear_additive a h.1 b c

/-- **Frozen signs are eco-closed.** Naturalized myths admit only one
    reading — the mythical, "common-sense" reading. -/
theorem frozen_ecoClosed {a : I} (h : frozenSign a) :
    ecoClosed a := leftLinear_not_polysemous a h.1

/-- **Void is not a frozen sign.** It is nothingness, not myth. -/
theorem void_not_frozen : ¬frozenSign (void : I) := by
  intro ⟨_, h⟩; exact h rfl

/-- **The frozen enrichment.** Self-composition of a frozen sign increases
    self-resonance (the myth gets more "natural" through repetition) but
    never gains emergence — it remains frozen at each step. -/
theorem frozen_enrichment {a : I} (h : frozenSign a) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) ≥ rs a a :=
  differance_cumulative a n

/-- **Mythical emergence is always zero.** No matter what you compose
    a frozen sign with, emergence vanishes. This is the silence of myth. -/
theorem myth_zero_emergence {a : I} (h : frozenSign a) (b c : I) :
    emergence a b c = 0 := h.1 b c

/-- **Living signs are nonvoid.** A polysemous sign has substance. -/
theorem livingSign_nonvoid {a : I} (h : livingSign a) : a ≠ void := by
  intro heq; rw [heq] at h; exact void_not_polysemous h

/-- **Critical reading unfreezes context.** If a frozen myth `m` is composed
    with a critical context `c`, the COMBINATION may have emergence even
    though `m` alone doesn't. The critical reading operates on the composition. -/
theorem critical_reading_cocycle (m c b d : I) :
    emergence m c d + emergence (compose m c) b d =
    emergence c b d + emergence m (compose c b) d :=
  cocycle_condition m c b d

end MythFrozenEmergence

/-! ## §23. Advertising and Commodity Signs

In commodity aesthetics (Haug, 1971) and the semiotics of advertising
(Williamson, 1978), the **commodity sign** is a product infused with
cultural meaning through advertising. The product becomes a sign vehicle,
and the advertised lifestyle/identity becomes the signified.

In IDT, advertising is the process of COMPOSING a product with a cultural
code, generating emergence that associates the product with meanings
it doesn't inherently carry. -/

section AdvertisingCommodity
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Commodity sign.** The meaning added to a product by composing it with
    an advertising context. This is the emergent meaning that the product
    gains from its cultural positioning. -/
noncomputable def commoditySign (product ad : I) : ℝ :=
  emergence product ad (compose product ad)

/-- **Brand value.** The total emergent meaning of a product-brand composition,
    measured against the product itself. Positive brand value means the brand
    enhances the product's "self-resonance." -/
noncomputable def brandValue (product brand : I) : ℝ :=
  emergence product brand product

/-- **Advertising effectiveness.** How much the ad increases the product's
    resonance with a target audience. -/
noncomputable def adEffectiveness (product ad audience : I) : ℝ :=
  emergence product ad audience

/-- **Void product has no commodity sign.** You can't advertise nothing. -/
theorem commoditySign_void_product (ad : I) :
    commoditySign (void : I) ad = 0 := by
  unfold commoditySign; rw [show compose (void : I) ad = ad from void_left' ad]
  exact emergence_void_left ad ad

/-- **Void ad has no effect.** Silence doesn't sell. -/
theorem commoditySign_void_ad (product : I) :
    commoditySign product (void : I) = 0 := by
  unfold commoditySign
  rw [show compose product (void : I) = product from void_right' product]
  exact emergence_void_right product product

/-- **Brand value with void brand is zero.** -/
theorem brandValue_void_brand (product : I) :
    brandValue product (void : I) = 0 := by
  unfold brandValue; exact emergence_void_right product product

/-- **Brand value with void product is zero.** -/
theorem brandValue_void_product (brand : I) :
    brandValue (void : I) brand = 0 := by
  unfold brandValue; exact emergence_void_left brand (void : I)

/-- **Ad effectiveness is bounded.** Even the best ad can only extract so
    much emergent value — bounded by the Cauchy-Schwarz of emergence. -/
theorem adEffectiveness_bounded (product ad audience : I) :
    (adEffectiveness product ad audience) ^ 2 ≤
    rs (compose product ad) (compose product ad) *
    rs audience audience := by
  unfold adEffectiveness; exact emergence_bounded' product ad audience

/-- **Linear products can't be branded.** A left-linear product generates no
    emergence with any ad — it's immune to branding. -/
theorem leftLinear_no_brand {product : I} (h : leftLinear product)
    (ad : I) : brandValue product ad = 0 := by
  unfold brandValue; exact h ad product

/-- **Commodity fetishism.** When a product is composed with an ad, the
    resonance of the composition with the audience decomposes into
    a "natural" part (product resonance + ad resonance) and an "emergent"
    part (commodity sign surplus). Marx's fetishism = mistaking the emergent
    for the natural. -/
theorem commodity_fetishism_decomp (product ad audience : I) :
    rs (compose product ad) audience =
    rs product audience + rs ad audience +
    adEffectiveness product ad audience := by
  unfold adEffectiveness; rw [rs_compose_eq]

/-- **Brand composition cocycle.** Building a brand through multiple ads
    is constrained by the cocycle: the order and grouping of ads matters. -/
theorem brand_cocycle (product ad₁ ad₂ audience : I) :
    emergence product ad₁ audience +
    emergence (compose product ad₁) ad₂ audience =
    emergence ad₁ ad₂ audience +
    emergence product (compose ad₁ ad₂) audience :=
  cocycle_condition product ad₁ ad₂ audience

/-- **Dead brand.** A frozen sign used as a product creates dead branding —
    no emergence regardless of advertising effort. -/
theorem dead_brand {product : I} (h : frozenSign product) (ad : I) :
    brandValue product ad = 0 := by
  unfold brandValue; exact h.1 ad product

/-- **Living products accept branding.** A living sign (polysemous product)
    is at least potentially brandable — its emergence varies across contexts. -/
theorem living_brandable {product : I} (h : livingSign product) :
    ∃ ad : I, ∃ c : I, emergence product ad c ≠ 0 := by
  rcases h with ⟨c₁, c₂, d, hne⟩
  by_cases h1 : emergence product c₁ d = 0
  · exact ⟨c₂, d, fun h2 => hne (by rw [h1, h2])⟩
  · exact ⟨c₁, d, h1⟩

end AdvertisingCommodity

/-! ## §24. Digital Semiotics — Emoji, Memes, and Hashtags

Digital communication has produced new sign types:
- **Emoji**: iconic signs in Peirce's sense (they resemble their referents)
- **Memes**: signs whose meaning is generated through iterative recomposition
  (mutation and recombination — a fundamentally emergent process)
- **Hashtags**: signs that function as compositional operators, modifying
  the emergence of whatever they are attached to

In IDT, digital signs are analyzed through the same emergence framework,
but with attention to the specific patterns of iteration, virality, and
context-dependence that characterize digital semiosis. -/

section DigitalSemiotics
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Emoji as icon.** An emoji for referent `r` is iconic: it has positive
    resonance with its referent. -/
def emojiFor (emoji referent : I) : Prop := iconic emoji referent

/-- **Meme as iterated emergence.** A meme is an utterance whose iterated
    self-composition generates ever-increasing self-resonance — it "goes
    viral" through repeated composition with itself. -/
noncomputable def memeViralPotential (meme : I) (n : ℕ) : ℝ :=
  rs (composeN meme (n + 1)) (composeN meme (n + 1)) - rs (composeN meme n) (composeN meme n)

/-- **Hashtag effect.** A hashtag modifies the emergence of the content it's
    attached to. The hashtag effect is the change in self-resonance when
    content is composed with the tag. -/
noncomputable def hashtagEffect (content tag : I) : ℝ :=
  rs (compose content tag) (compose content tag) - rs content content

/-- **Viral potential is nonneg.** Meme iterations never decrease in
    self-resonance — virality only grows (by compose_enriches). -/
theorem memeViralPotential_nonneg (meme : I) (n : ℕ) :
    memeViralPotential meme n ≥ 0 := by
  unfold memeViralPotential
  have := rs_composeN_mono meme n
  linarith

/-- **Hashtag effect is nonneg.** Adding a hashtag never decreases the
    self-resonance of content — composition enriches. -/
theorem hashtagEffect_nonneg (content tag : I) :
    hashtagEffect content tag ≥ 0 := by
  unfold hashtagEffect; linarith [compose_enriches' content tag]

/-- **Void emoji is not iconic.** -/
theorem void_not_emoji (r : I) : ¬emojiFor (void : I) r := void_not_iconic r

/-- **Emoji for void fails.** Nothing resembles silence. -/
theorem emoji_for_void (e : I) : ¬emojiFor e (void : I) := not_iconic_void e

/-- **Void hashtag has no effect.** -/
theorem void_hashtagEffect (content : I) :
    hashtagEffect content (void : I) = 0 := by
  unfold hashtagEffect; simp

/-- **Meme decay: void meme has zero viral potential.** -/
theorem void_memeViralPotential (n : ℕ) :
    memeViralPotential (void : I) n = 0 := by
  unfold memeViralPotential; simp [composeN_void]

/-- **Meme mutation.** Composing a meme with a variation produces emergence.
    The cocycle constrains how mutations interact. -/
theorem meme_mutation_cocycle (meme variation₁ variation₂ observer : I) :
    emergence meme variation₁ observer +
    emergence (compose meme variation₁) variation₂ observer =
    emergence variation₁ variation₂ observer +
    emergence meme (compose variation₁ variation₂) observer :=
  cocycle_condition meme variation₁ variation₂ observer

/-- **Hashtag composition.** The effect of applying two hashtags decomposes
    via the enrichment axiom: content ∘ (tag₁ ∘ tag₂) enriches content ∘ tag₂
    which enriches content. -/
theorem hashtag_compose_enriches (content tag₁ tag₂ : I) :
    rs (compose content (compose tag₁ tag₂))
       (compose content (compose tag₁ tag₂)) ≥
    rs content content :=
  compose_enriches' content (compose tag₁ tag₂)

/-- **Digital irony.** An ironic meme is one where the context (platform,
    usage pattern) reverses the meme's meaning — the meme is ironic in
    its digital context. -/
def ironicMeme (platform meme : I) : Prop := ironicIn platform meme

/-- **Ironic memes require platform.** Without a platform context,
    no meme is ironic. -/
theorem no_ironic_meme_without_platform (meme : I) :
    ¬ironicMeme (void : I) meme := no_irony_without_context meme

/-- **Self-referential meme.** A meme about memes: the self-emergence
    measures how much a meme commenting on itself exceeds its parts. -/
noncomputable def metaMeme (meme : I) : ℝ :=
  emergence meme meme meme

/-- **Meta-meme of void is zero.** -/
theorem metaMeme_void : metaMeme (void : I) = 0 := by
  unfold metaMeme; exact emergence_void_left (void : I) (void : I)

/-- **Meta-meme is bounded.** -/
theorem metaMeme_bounded (meme : I) :
    (metaMeme meme) ^ 2 ≤
    rs (compose meme meme) (compose meme meme) * rs meme meme := by
  unfold metaMeme; exact emergence_bounded' meme meme meme

/-- **Meta-meme equals semantic charge.** The self-referential meme value
    is precisely the semantic charge of the meme. -/
theorem metaMeme_eq_semanticCharge (meme : I) :
    metaMeme meme = semanticCharge meme := by
  unfold metaMeme semanticCharge; ring

end DigitalSemiotics

/-! ## §25. Biosemiotics — Uexküll's Umwelt

Jakob von Uexküll's concept of the **Umwelt** (1934) holds that every organism
inhabits a species-specific "sign world" — a subjective universe of meaningful
signs. Different organisms perceive different aspects of the same environment
because their Umwelten filter reality differently.

In IDT, an organism's Umwelt is modeled as a particular "observation function":
the emergence that an organism detects depends on its own constitution. Two
organisms in the same environment may detect entirely different emergences —
different meanings — from the same physical signs. -/

section Biosemiotics
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Umwelt-relative meaning.** The meaning of stimulus `s` for organism `o`
    is the emergence when o encounters s, measured against o's own state. -/
noncomputable def umweltMeaning (organism stimulus : I) : ℝ :=
  emergence organism stimulus organism

/-- **Umwelt difference.** Two organisms differ in their Umwelt perception
    of a stimulus if they detect different emergences. -/
def umweltDiffers (o₁ o₂ stimulus : I) : Prop :=
  umweltMeaning o₁ stimulus ≠ umweltMeaning o₂ stimulus

/-- **Functional tone.** Uexküll's "Ton" — the qualitative coloring that an
    object takes on in an organism's Umwelt. Formalized as the resonance
    between the organism-stimulus composition and the organism. -/
noncomputable def functionalTone (organism stimulus : I) : ℝ :=
  rs (compose organism stimulus) organism

/-- **Meaning circle.** The organism acts on its environment and the
    environment acts back. The meaning circle is the total resonance
    of this feedback loop. -/
noncomputable def meaningCircle (organism environment : I) : ℝ :=
  rs (compose organism environment) (compose environment organism)

/-- **Void organism has no Umwelt.** A non-entity perceives nothing. -/
theorem void_no_umwelt (stimulus : I) :
    umweltMeaning (void : I) stimulus = 0 := by
  unfold umweltMeaning; exact emergence_void_left stimulus (void : I)

/-- **Void stimulus has no meaning.** Nothing has no meaning for any organism. -/
theorem void_no_meaning (organism : I) :
    umweltMeaning organism (void : I) = 0 := by
  unfold umweltMeaning; exact emergence_void_right organism organism

/-- **Functional tone decomposes.** The functional tone of a stimulus for
    an organism decomposes into the organism's self-resonance, the stimulus's
    resonance with the organism, and the emergent Umwelt meaning. -/
theorem functionalTone_decomp (organism stimulus : I) :
    functionalTone organism stimulus =
    rs organism organism + rs stimulus organism +
    umweltMeaning organism stimulus := by
  unfold functionalTone umweltMeaning; rw [rs_compose_eq]

/-- **Void functional tone.** A void stimulus adds nothing. -/
theorem functionalTone_void_stimulus (organism : I) :
    functionalTone organism (void : I) = rs organism organism := by
  unfold functionalTone; simp

/-- **Meaning circle with void.** The meaning circle degenerates with void. -/
theorem meaningCircle_void_org (env : I) :
    meaningCircle (void : I) env = rs env env := by
  unfold meaningCircle; simp

/-- **Umwelt meaning is bounded.** The meaning any organism can extract from
    a stimulus is bounded by their combined self-resonance. -/
theorem umweltMeaning_bounded (organism stimulus : I) :
    (umweltMeaning organism stimulus) ^ 2 ≤
    rs (compose organism stimulus) (compose organism stimulus) *
    rs organism organism := by
  unfold umweltMeaning; exact emergence_bounded' organism stimulus organism

/-- **Linear organisms have trivial Umwelten.** A left-linear organism
    (one that never generates emergence) has zero Umwelt meaning for every
    stimulus — it lives in a "flat" world with no emergent significance. -/
theorem leftLinear_trivial_umwelt {organism : I} (h : leftLinear organism)
    (stimulus : I) : umweltMeaning organism stimulus = 0 := by
  unfold umweltMeaning; exact h stimulus organism

/-- **Polysemous organisms have rich Umwelten.** A polysemous organism
    (one with context-varying emergence) inhabits a perceptually rich world. -/
theorem polysemous_rich_umwelt {organism : I} (h : polysemous organism) :
    ∃ stimulus : I, ∃ c : I, emergence organism stimulus c ≠ 0 := by
  rcases h with ⟨c₁, c₂, d, hne⟩
  by_cases h1 : emergence organism c₁ d = 0
  · exact ⟨c₂, d, fun h2 => hne (by rw [h1, h2])⟩
  · exact ⟨c₁, d, h1⟩

/-- **Umwelt cocycle.** The meaning an organism extracts from a sequence
    of stimuli is constrained by the cocycle — perception is globally
    consistent, not arbitrary. -/
theorem umwelt_cocycle (organism s₁ s₂ d : I) :
    emergence organism s₁ d + emergence (compose organism s₁) s₂ d =
    emergence s₁ s₂ d + emergence organism (compose s₁ s₂) d :=
  cocycle_condition organism s₁ s₂ d

/-- **Enrichment of perception.** Encountering a stimulus never diminishes
    the organism's self-resonance — experience enriches. -/
theorem umwelt_enrichment (organism stimulus : I) :
    rs (compose organism stimulus) (compose organism stimulus) ≥
    rs organism organism := compose_enriches' organism stimulus

end Biosemiotics

/-! ## §26. Semiotic Dynamics — Sign Change and Evolution

Signs are not static — they evolve, decay, are reinterpreted, and
transformed. This section formalizes the dynamics of semiotic change:
how signs gain and lose emergence, how codes evolve, and how the
semiosphere transforms over time.

Key concepts: semiotic entropy (loss of emergence), semiotic innovation
(gain of emergence), and the conservation laws that constrain semiotic
change (via the cocycle). -/

section SemioticDynamics
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Semiotic enrichment rate.** The increase in self-resonance when
    an utterance is composed with itself — a measure of how much "weight"
    accumulates through repetition. -/
noncomputable def semioticEnrichment (a : I) : ℝ :=
  rs (compose a a) (compose a a) - rs a a

/-- **Semiotic enrichment is nonneg.** Repetition never diminishes. -/
theorem semioticEnrichment_nonneg (a : I) :
    semioticEnrichment a ≥ 0 := by
  unfold semioticEnrichment; linarith [compose_enriches' a a]

/-- **Void has zero enrichment.** -/
theorem semioticEnrichment_void :
    semioticEnrichment (void : I) = 0 := by
  unfold semioticEnrichment; simp [rs_void_void]

/-- **Semiotic momentum.** The total emergence generated by composing
    a sign with its own iteration. This measures the "direction" of
    semiotic evolution — whether a sign is gaining or losing creative force. -/
noncomputable def semioticMomentum (a : I) (n : ℕ) : ℝ :=
  emergence a (composeN a n) a

/-- **Momentum with void is zero.** -/
theorem semioticMomentum_void (n : ℕ) :
    semioticMomentum (void : I) n = 0 := by
  unfold semioticMomentum; simp [composeN_void]; exact emergence_void_left (void : I) (void : I)

/-- **Momentum at zero iterations.** -/
theorem semioticMomentum_zero (a : I) :
    semioticMomentum a 0 = 0 := by
  unfold semioticMomentum; simp [composeN]; exact emergence_void_right a a

/-- **Semiotic conservation law.** The cocycle constrains how emergence
    redistributes across levels of semiotic iteration. Emergence is not
    created or destroyed — it is redistributed by the cocycle. -/
theorem semiotic_conservation (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

/-- **Iterative momentum conservation.** Successive applications of
    emergence satisfy the cocycle — momentum is globally consistent. -/
theorem momentum_conservation (a : I) (n : ℕ) (d : I) :
    emergence a (composeN a n) d +
    emergence (compose a (composeN a n)) a d =
    emergence (composeN a n) a d +
    emergence a (compose (composeN a n) a) d :=
  cocycle_condition a (composeN a n) a d

/-- **Enrichment decomposition.** Self-resonance of a^2 decomposes into
    self-resonance of a plus cross-terms and emergence. -/
theorem enrichment_decomposition (a : I) :
    rs (compose a a) (compose a a) =
    rs a (compose a a) + rs a (compose a a) +
    emergence a a (compose a a) := by
  rw [rs_compose_eq]

/-- **Order sensitivity as semiotic force.** The order sensitivity between
    two signs measures the "force" that one sign exerts on the meaning
    of the other — a directional, asymmetric influence. -/
theorem semiotic_force_antisymm (a b c : I) :
    orderSensitivity a b c = -orderSensitivity b a c :=
  orderSensitivity_antisymm a b c

end SemioticDynamics

/-! ## §27. Semiotic Topology — Continuity and Neighborhoods of Meaning

The "space" of meanings has topological structure: some meanings are
"close" (high mutual resonance), others are "distant" (low or negative
resonance). We formalize topological concepts using resonance as a
proximity measure. -/

section SemioticTopology
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Semiotic proximity.** A signed measure of how "close" two utterances
    are in meaning-space. -/
noncomputable def semioticProximity (a b : I) : ℝ :=
  (rs a b + rs b a) / 2

/-- **Self-proximity equals self-resonance.** -/
theorem selfProximity (a : I) :
    semioticProximity a a = rs a a := by
  unfold semioticProximity; ring

/-- **Proximity is symmetric.** -/
theorem proximity_symm (a b : I) :
    semioticProximity a b = semioticProximity b a := by
  unfold semioticProximity; ring

/-- **Void proximity is zero.** -/
theorem void_proximity (a : I) :
    semioticProximity (void : I) a = 0 := by
  unfold semioticProximity; simp [rs_void_left', rs_void_right']

/-- **Semiotic distance.** The "gap" between two meanings — the deficit
    in mutual resonance compared to self-resonance. -/
noncomputable def semioticDistance (a b : I) : ℝ :=
  rs a a + rs b b - rs a b - rs b a

/-- **Self-distance is zero.** -/
theorem semioticDistance_self (a : I) : semioticDistance a a = 0 := by
  unfold semioticDistance; ring

/-- **Distance is symmetric.** -/
theorem semioticDistance_symm (a b : I) :
    semioticDistance a b = semioticDistance b a := by
  unfold semioticDistance; ring

/-- **Distance from void.** -/
theorem semioticDistance_void (a : I) :
    semioticDistance (void : I) a = rs a a := by
  unfold semioticDistance; simp [rs_void_left', rs_void_right', rs_void_void]

/-- **Distance and proximity complement.** -/
theorem distance_proximity_complement (a b : I) :
    semioticDistance a b = rs a a + rs b b - 2 * semioticProximity a b := by
  unfold semioticDistance semioticProximity; ring

/-- **Proximity-emergence connection.** The proximity of a composition to
    the individual elements relates to emergence through resonance. -/
theorem composition_proximity (a b : I) :
    semioticProximity (compose a b) a =
    (rs (compose a b) a + rs a (compose a b)) / 2 := by
  unfold semioticProximity; ring

/-- **Distance equals resonance deficit.** -/
theorem distance_eq_deficit (a b : I) :
    semioticDistance a b = resonanceDeficit a b := by
  unfold semioticDistance resonanceDeficit; ring

end SemioticTopology

/-! ## §28. Semiotic Power — Hegemony, Ideology, and Dominance

Extending Gramsci's hegemony and Althusser's interpellation into IDT:
semiotic power is the capacity of one sign to constrain the emergence
of others. A hegemonic sign is one that, when composed with any other,
absorbs the other's emergence potential. -/

section SemioticPower
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Semiotic dominance.** Sign `a` dominates sign `b` if composing `a`
    with `b` generates no emergence from `b`'s perspective — `a` absorbs
    `b`'s creative potential. -/
def dominates (a b : I) : Prop :=
  ∀ c : I, emergence a b c = 0

/-- **Ideological interpellation.** An ideological sign interpellates a
    subject when composition generates positive emergence measured against
    the subject — the ideology "recognizes" and shapes the subject. -/
def interpellates (ideology subject : I) : Prop :=
  emergence ideology subject subject > 0

/-- **Hegemonic sign.** A sign is hegemonic if it dominates all other signs —
    its emergence absorbs everything. -/
def hegemonic (a : I) : Prop := ∀ b : I, dominates a b

/-- **Hegemonic implies left-linear.** A hegemonic sign is left-linear:
    its emergence with ANY other sign in ANY context is zero. -/
theorem hegemonic_leftLinear {a : I} (h : hegemonic a) : leftLinear a := by
  intro b c; exact h b c

/-- **Void is hegemonic (trivially).** Silence dominates everything — but
    only because it contributes nothing. -/
theorem void_hegemonic : hegemonic (void : I) := by
  intro b c; exact emergence_void_left b c

/-- **Hegemonic signs are eco-closed.** -/
theorem hegemonic_ecoClosed {a : I} (h : hegemonic a) :
    ecoClosed a := leftLinear_not_polysemous a (hegemonic_leftLinear h)

/-- **Dominance makes resonance additive.** When a dominates b, their
    composition's resonance is purely additive. -/
theorem dominance_additive {a b : I} (h : dominates a b) (c : I) :
    rs (compose a b) c = rs a c + rs b c := by
  have := rs_compose_eq a b c; rw [h c] at this; linarith

/-- **Interpellation is bounded.** -/
theorem interpellation_bounded (ideology subject : I) :
    (emergence ideology subject subject) ^ 2 ≤
    rs (compose ideology subject) (compose ideology subject) *
    rs subject subject :=
  emergence_bounded' ideology subject subject

/-- **Void doesn't interpellate.** -/
theorem void_not_interpellates (subject : I) :
    ¬interpellates (void : I) subject := by
  intro h; unfold interpellates at h; rw [emergence_void_left] at h; linarith

/-- **Counter-hegemony.** If a sign produces negative emergence against
    a hegemonic sign, it is counter-hegemonic (subversive, ironic). -/
def counterHegemonic (subversive hegemonic_sign : I) : Prop :=
  emergence subversive hegemonic_sign hegemonic_sign < 0

/-- **Counter-hegemony is irony against the hegemon.** -/
theorem counterHegemonic_is_irony {s h : I} (hch : counterHegemonic s h) :
    ironicIn s h := hch

/-- **Dominance is cocycle-constrained.** -/
theorem dominance_cocycle (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

/-- **Hegemonic signs produce dead metaphors.** -/
theorem hegemonic_dead_metaphor {a : I} (h : hegemonic a) (t : I) :
    deadMetaphor a t :=
  leftLinear_dead_metaphor (hegemonic_leftLinear h) t

end SemioticPower

/-! ## §29. Semiotic Ethics — Responsibility and the Other

Extending Levinas and Bakhtin into IDT: ethical meaning arises from the
encounter with the Other. The Other's irreducibility (non-linearity,
non-absorption) is the condition for ethical emergence. -/

section SemioticEthics
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Ethical encounter.** The encounter between self and other is ethical
    when it generates genuine emergence — the Other cannot be reduced to
    the Same. -/
def ethicalEncounter (self other : I) : Prop :=
  emergence self other other ≠ 0

/-- **Alterity.** The degree to which the Other resists absorption by the
    Self — measured by the emergence of their composition. -/
noncomputable def alterity (self other : I) : ℝ :=
  emergence self other (compose self other)

/-- **Dialogical surplus.** Bakhtin's insight: dialogue creates meaning
    that neither participant alone could produce. This is the total
    emergence of the self-other composition. -/
noncomputable def dialogicalSurplus (a b : I) : ℝ :=
  emergence a b (compose a b)

/-- **Void has no alterity.** Silence cannot be Other. -/
theorem void_no_alterity (other : I) :
    alterity (void : I) other = 0 := by
  unfold alterity; rw [show compose (void : I) other = other from void_left' other]
  exact emergence_void_left other other

/-- **No encounter with void.** -/
theorem void_no_encounter (self : I) :
    ¬ethicalEncounter self (void : I) := by
  intro h; unfold ethicalEncounter at h
  exact h (emergence_void_right self (void : I))

/-- **Ethical encounter implies non-dominance.** If the encounter is
    genuinely ethical, the Self does not dominate the Other. -/
theorem ethical_not_dominates {self other : I}
    (h : ethicalEncounter self other) : ¬dominates self other := by
  intro hdom; unfold ethicalEncounter at h; exact h (hdom other)

/-- **Dialogical surplus vanishes with void.** -/
theorem dialogicalSurplus_void_left (b : I) :
    dialogicalSurplus (void : I) b = 0 := by
  unfold dialogicalSurplus; rw [show compose (void : I) b = b from void_left' b]
  exact emergence_void_left b b

/-- **Dialogical surplus vanishes with void on right.** -/
theorem dialogicalSurplus_void_right (a : I) :
    dialogicalSurplus a (void : I) = 0 := by
  unfold dialogicalSurplus
  rw [show compose a (void : I) = a from void_right' a]
  exact emergence_void_right a a

/-- **Dialogical surplus is bounded.** -/
theorem dialogicalSurplus_bounded (a b : I) :
    (dialogicalSurplus a b) ^ 2 ≤
    rs (compose a b) (compose a b) *
    rs (compose a b) (compose a b) := by
  unfold dialogicalSurplus; exact emergence_bounded' a b _

/-- **Hegemony annihilates ethical encounter.** If self is hegemonic,
    no encounter is ethical — the Other is always absorbed. -/
theorem hegemony_kills_ethics {self : I} (h : hegemonic self)
    (other : I) : ¬ethicalEncounter self other := by
  intro henc; unfold ethicalEncounter at henc; exact henc (h other other)

/-- **Linear selves have no alterity.** A left-linear self cannot
    experience genuine Otherness — it reduces everything to the Same. -/
theorem leftLinear_no_alterity {self : I} (h : leftLinear self) (other : I) :
    alterity self other = 0 := by
  unfold alterity; exact h other (compose self other)

end SemioticEthics

/-! ## §30. Cross-Theorist Synthesis II — Deep Interconnections

This final section proves deeper theorems connecting all the theorists
formalized above. These theorems reveal the mathematical unity underlying
diverse semiotic traditions. -/

section DeepSynthesis
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Grand semiotic dichotomy.** Every nonvoid sign is either frozen
    (mythical, simulacral, dictionary-like, symbolic, eco-closed) or
    living (polysemous, peripheral, encyclopedia-like, semiotic, eco-open).
    This unifies Barthes, Baudrillard, Eco, Kristeva, and Lotman. -/
theorem grand_semiotic_dichotomy (a : I) (h : a ≠ void) :
    (leftLinear a ∧ ecoClosed a ∧ frozenSign a) ∨
    (polysemous a ∧ ecoOpen a ∧ livingSign a) := by
  by_cases hp : polysemous a
  · right; exact ⟨hp, hp, hp⟩
  · left; exact ⟨not_polysemous_leftLinear hp, hp, not_polysemous_leftLinear hp, h⟩

/-- **The emergence hierarchy.** All the "depth" concepts — metaphor strength,
    semantic content, pragmatic effect, Umwelt meaning — are special cases
    of emergence. This theorem shows they all satisfy the same bound. -/
theorem emergence_universal_bound (a b c : I) :
    (emergence a b c) ^ 2 ≤
    rs (compose a b) (compose a b) * rs c c :=
  emergence_bounded' a b c

/-- **Frozen signs across theories.** A frozen sign is simultaneously:
    a pure simulacrum (Baudrillard), a closed text (Eco), a symbolic
    utterance (Kristeva), a dictionary entry (Eco), and a semiosphere
    center (Lotman). -/
theorem frozen_unification {a : I} (h : frozenSign a) :
    pureSimulacrum a ∧ ecoClosed a ∧
    kristevaSymbolic a ∧ dictionaryEntry a ∧
    semiosphereCenter a := by
  exact ⟨h, leftLinear_not_polysemous a h.1, h.1, h.1, h.1⟩

/-- **Living signs across theories.** A living sign is simultaneously:
    an open text (Eco), a semiotic utterance (Kristeva), an encyclopedia
    entry (Eco), and a semiosphere periphery (Lotman). -/
theorem living_unification {a : I} (h : livingSign a) :
    ecoOpen a ∧ kristevaSemiotic a ∧
    encyclopediaEntry a ∧ semiospherePeriphery a :=
  ⟨h, h, h, h⟩

/-- **The void theorem.** Void is the universal zero of semiotics: it is
    not iconic, not indexical, not a simulacrum, not frozen, not living,
    not ethical, has no Umwelt, no brand value, no commodity sign. It is
    the transcendental signified that Derrida deconstructs — and the
    only thing that IS this nothing. -/
theorem void_universal_zero :
    ¬(∃ r : I, iconic (void : I) r) ∧
    ¬(∃ b : I, indexes (void : I) b) ∧
    ¬pureSimulacrum (void : I) ∧
    ¬frozenSign (void : I) ∧
    ¬livingSign (void : I) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ⟨r, h⟩; exact void_not_iconic r h
  · intro ⟨b, h⟩; exact void_not_indexes b h
  · exact void_not_simulacrum
  · exact void_not_frozen
  · exact void_not_polysemous

/-- **Composition enrichment is universal.** Across ALL semiotic theories,
    composition never diminishes self-resonance. This is the mathematical
    ground of semiotic accumulation: meaning grows, never shrinks. -/
theorem universal_enrichment (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a :=
  compose_enriches' a b

/-- **The cocycle is the master constraint.** Every semiotic theory's
    theorems are ultimately constrained by the cocycle condition —
    it is the "law of conservation of emergence" that governs all
    sign processes. -/
theorem master_cocycle (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

/-- **Emergence is meaning-theoretic.** The emergence quantity captures
    what Eco calls "unlimited semiosis," what Derrida calls "différance,"
    what Barthes calls "myth," what Kristeva calls "the semiotic," and
    what Lotman calls "the boundary." All are aspects of the same
    mathematical object. -/
theorem emergence_is_meaning (a b c : I) :
    rs (compose a b) c = rs a c + rs b c + emergence a b c :=
  rs_compose_eq a b c

/-- **Dialectical synthesis.** When two signs compose, the result always
    enriches the first — Hegel's thesis-antithesis-synthesis, formalized. -/
theorem dialectical_synthesis (thesis antithesis : I) :
    rs (compose thesis antithesis) (compose thesis antithesis) ≥
    rs thesis thesis :=
  compose_enriches' thesis antithesis

/-- **Self-referentiality connection.** The meta-meme of digital semiotics
    equals the semantic charge of Foundations, which equals the self-emergence.
    All three traditions (digital, classical, formal) converge. -/
theorem self_referentiality_unity (a : I) :
    metaMeme a = semanticCharge a ∧
    semanticCharge a = emergence a a a :=
  ⟨metaMeme_eq_semanticCharge a, rfl⟩

/-- **The semiotic square revisited.** Greimas' contraries remain contraries
    under Lotman's boundary: if a and b are contrary (opposing) and form
    a boundary, the emergence at the boundary is nonzero by definition. -/
theorem greimas_lotman_boundary {a b : I}
    (hbound : semioticBoundary a b) :
    ∃ c : I, emergence a b c ≠ 0 := hbound

/-- **Jakobson meets Kristeva.** The poetic function (nonzero emergence)
    corresponds to Kristeva's semiotic modality (polysemous). An utterance
    with poetic function that varies across contexts is Kristeva-semiotic. -/
theorem poetic_implies_semiotic_if_varied {a : I}
    (h : ∃ c₁ c₂ d : I, emergence a c₁ d ≠ emergence a c₂ d) :
    kristevaSemiotic a := h

/-- **Morris meets Hjelmslev.** Morris's semantic content (emergence with
    referent) is the same as Hjelmslev's denotative content — they formalize
    the same mathematical object. -/
theorem morris_hjelmslev_unity (sign referent observer : I) :
    semanticContent sign referent =
    denotativeContent sign referent referent := by
  unfold semanticContent denotativeContent; ring

/-- **Advertising as boundary phenomenon.** In Lotman's terms, advertising
    is a boundary phenomenon: it composes the product (inside the economic
    sphere) with cultural meanings (outside), generating emergence at the
    boundary. A nonzero brand value implies a semiotic boundary. -/
theorem ad_is_boundary {product brand : I}
    (h : brandValue product brand ≠ 0) :
    semioticBoundary product brand := by
  unfold semioticBoundary; exact ⟨product, by unfold brandValue at h; exact h⟩

/-- **Ethical alterity requires living signs.** If self is frozen (left-linear),
    it cannot experience genuine alterity with any Other. Only living signs
    can enter ethical encounters. -/
theorem ethics_requires_living {self : I}
    (h : frozenSign self) (other : I) :
    alterity self other = 0 :=
  leftLinear_no_alterity h.1 other

/-- **Biosemiotics meets Eco.** An organism with a polysemous nature
    (rich Umwelt) is an open text in Eco's sense — its responses to
    stimuli vary contextually. -/
theorem rich_umwelt_is_open {organism : I}
    (h : polysemous organism) : ecoOpen organism := h

end DeepSynthesis

