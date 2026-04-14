import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic

/-!
# Literary Rhetoric: Algebraic Theory of Rhetorical Transformations

This file formalizes **rhetorical transformations** — tropes, figures of speech,
and compositional devices — as algebraic operations on an ideatic space.

## Core Insight

A **trope** (metaphor, irony, synecdoche, metonymy) is a *resonance-preserving
endomorphism*: it transforms an idea into something different but meaning-adjacent.
The identity trope (literal speech) is the unit. Tropes compose associatively,
forming a monoid. The depth-related classifications (faithful, diminishing,
amplifying, bounded) impose further algebraic structure.

## Extension

For the literary rhetoric context, we add **resonance transitivity** to the base
axioms. This is justified by the linguistic principle that meaning-adjacency
chains: if A evokes B and B evokes C, then A evokes C (through B as mediator).
This enables a rich compositional theory of tropes.

## Sections

- §1 Ideatic Space (local redefinition with transitivity)
- §2 Trope Algebra (monoid structure)
- §3 Depth Classifications (faithful, diminishing, amplifying)
- §4 Iterated Application (depth bounds under iteration)
- §5 Irony (approximate involutions)
- §6 Metaphor (domain-crossing tropes)
- §7 Parallelism and Coherence (list operations)
- §8 Rhetorical Figures (anaphora, epistrophe, chiasmus)
- §9 Depth Spectrum (bounded tropes, composition bounds)

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

set_option autoImplicit false

namespace LiteraryRhetoric

/-! ## §1. Ideatic Space (Local Redefinition)

We extend the standard IDT axioms with resonance transitivity.
LITERARY JUSTIFICATION: in rhetoric, if metaphor A evokes meaning B,
and B evokes meaning C, then A evokes C through the mediating link.
This is the foundation of "chains of association" in literary theory. -/

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
  resonance_trans : ∀ (a b c : I), resonates a b → resonates b c → resonates a c
  resonance_compose : ∀ (a a' b b' : I),
    resonates a a' → resonates b b' → resonates (compose a b) (compose a' b')
  depth_void : depth void = 0
  depth_subadditive : ∀ (a b : I), depth (compose a b) ≤ depth a + depth b
  depth_atomic : ∀ (a : I), atomic a → depth a ≤ 1
  void_atomic : atomic void

variable {I : Type*} [IdeaticSpace I]

open IdeaticSpace

/-! ## §2. Trope Algebra

A **trope** is a resonance-preserving endomorphism on ideas. Tropes form
a monoid: identity is literal speech, composition is layered figuration. -/

section TropeAlgebra

/-- A Trope bundles a transformation with a proof that every output resonates
    with its input. This captures the defining property of figurative language:
    the figurative meaning is always recoverable from the literal. -/
structure Trope (I : Type*) [IdeaticSpace I] where
  transform : I → I
  preserves_resonance : ∀ (a : I), resonates a (transform a)

/-- **Theorem 1** (Identity Trope): Literal speech — the identity transformation.
    LITERARY INSIGHT: saying exactly what you mean is the trivial trope. -/
def id_trope : Trope I where
  transform := id
  preserves_resonance := fun a => resonance_refl a

/-- **Theorem 2**: The identity trope acts as the identity on each element. -/
@[simp] theorem id_trope_apply (a : I) : (id_trope : Trope I).transform a = a := rfl

/-- **Theorem 3** (Trope Composition): Composing two tropes yields a trope.
    LITERARY INSIGHT: layering metaphors ("mixed metaphor") is itself a trope,
    because resonance chains through the intermediate meaning. -/
def comp_trope (f g : Trope I) : Trope I where
  transform := f.transform ∘ g.transform
  preserves_resonance := fun a =>
    resonance_trans a (g.transform a) (f.transform (g.transform a))
      (g.preserves_resonance a) (f.preserves_resonance (g.transform a))

/-- **Theorem 4**: Composition is functorial on transforms. -/
theorem comp_trope_apply (f g : Trope I) (a : I) :
    (comp_trope f g).transform a = f.transform (g.transform a) := rfl

/-- **Theorem 5**: Identity is a left unit for trope composition. -/
theorem comp_trope_id_left (f : Trope I) (a : I) :
    (comp_trope id_trope f).transform a = f.transform a := rfl

/-- **Theorem 6**: Identity is a right unit for trope composition. -/
theorem comp_trope_id_right (f : Trope I) (a : I) :
    (comp_trope f id_trope).transform a = f.transform a := rfl

/-- **Theorem 7**: Trope composition is associative on transforms.
    LITERARY INSIGHT: the order of "peeling off" figurative layers doesn't matter. -/
theorem comp_trope_assoc (f g h : Trope I) (a : I) :
    (comp_trope (comp_trope f g) h).transform a =
    (comp_trope f (comp_trope g h)).transform a := rfl

/-- **Theorem 8**: Every trope maps void to something resonant with void.
    LITERARY INSIGHT: a figure of speech applied to silence produces
    something that still "sounds like" silence. -/
theorem trope_void_resonant (f : Trope I) :
    resonates (void : I) (f.transform void) :=
  f.preserves_resonance void

/-- **Theorem 9**: Resonance is symmetric for tropes — the output resonates
    back to the input. -/
theorem trope_resonant_symm (f : Trope I) (a : I) :
    resonates (f.transform a) a :=
  resonance_symm a (f.transform a) (f.preserves_resonance a)

/-- **Theorem 10**: A trope applied to both components of a composition gives
    a result that resonates with the original composition.
    LITERARY INSIGHT: applying the same figure to an entire compound idea
    preserves the compound's semantic coherence. -/
theorem trope_compose_resonant (f : Trope I) (a b : I) :
    resonates (compose a b) (compose (f.transform a) (f.transform b)) :=
  resonance_compose a (f.transform a) b (f.transform b)
    (f.preserves_resonance a) (f.preserves_resonance b)

/-- **Theorem 11**: Composing a trope's output with void on the right is trivial. -/
theorem trope_output_void_right (f : Trope I) (a : I) :
    compose (f.transform a) (void : I) = f.transform a :=
  void_right (f.transform a)

/-- **Theorem 12**: Composing void on the left with a trope's output is trivial. -/
theorem trope_output_void_left (f : Trope I) (a : I) :
    compose (void : I) (f.transform a) = f.transform a :=
  void_left (f.transform a)

end TropeAlgebra

/-! ## §3. Depth Classifications

Tropes classified by how they affect depth (complexity):
- **Faithful**: preserves depth exactly (lossless transformation)
- **Diminishing**: never increases depth (lossy but safe)
- **Amplifying**: never decreases depth (always enriches) -/

section DepthClassifications

/-- A trope is **faithful** if it preserves depth exactly.
    LITERARY INSIGHT: a perfect metaphor transforms meaning without
    changing complexity — Shakespeare's "All the world's a stage"
    is as deep as its literal equivalent. -/
def IsFaithful (f : Trope I) : Prop :=
  ∀ (a : I), depth (f.transform a) = depth a

/-- A trope is **diminishing** if it never increases depth.
    LITERARY INSIGHT: simplification, paraphrase, summary — these
    reduce or maintain complexity but never add it. -/
def IsDiminishing (f : Trope I) : Prop :=
  ∀ (a : I), depth (f.transform a) ≤ depth a

/-- A trope is **amplifying** if it never decreases depth.
    LITERARY INSIGHT: elaboration, amplificatio — these
    enrich complexity but never reduce it. -/
def IsAmplifying (f : Trope I) : Prop :=
  ∀ (a : I), depth a ≤ depth (f.transform a)

/-- **Theorem 13**: The identity trope is faithful. -/
theorem id_is_faithful : IsFaithful (id_trope : Trope I) :=
  fun _ => rfl

/-- **Theorem 14**: The identity trope is diminishing. -/
theorem id_is_diminishing : IsDiminishing (id_trope : Trope I) :=
  fun _ => le_refl _

/-- **Theorem 15**: The identity trope is amplifying. -/
theorem id_is_amplifying : IsAmplifying (id_trope : Trope I) :=
  fun _ => le_refl _

/-- **Theorem 16**: Faithful implies diminishing. -/
theorem faithful_is_diminishing {f : Trope I} (h : IsFaithful f) : IsDiminishing f :=
  fun a => le_of_eq (h a)

/-- **Theorem 17**: Faithful implies amplifying. -/
theorem faithful_is_amplifying {f : Trope I} (h : IsFaithful f) : IsAmplifying f :=
  fun a => ge_of_eq (h a)

/-- **Theorem 18**: Faithful iff both diminishing and amplifying.
    LITERARY INSIGHT: a transformation that neither gains nor loses
    complexity is exactly a faithful one. -/
theorem faithful_iff_dim_and_amp (f : Trope I) :
    IsFaithful f ↔ (IsDiminishing f ∧ IsAmplifying f) := by
  constructor
  · intro h; exact ⟨faithful_is_diminishing h, faithful_is_amplifying h⟩
  · intro ⟨hd, ha⟩; intro a; exact le_antisymm (hd a) (ha a)

/-- **Theorem 19**: Diminishing tropes compose to diminishing tropes.
    LITERARY INSIGHT: paraphrasing a paraphrase only simplifies further. -/
theorem diminishing_comp {f g : Trope I}
    (hf : IsDiminishing f) (hg : IsDiminishing g) :
    IsDiminishing (comp_trope f g) := by
  intro a
  calc depth ((comp_trope f g).transform a)
      = depth (f.transform (g.transform a)) := rfl
    _ ≤ depth (g.transform a) := hf (g.transform a)
    _ ≤ depth a := hg a

/-- **Theorem 20**: Amplifying tropes compose to amplifying tropes.
    LITERARY INSIGHT: elaborating an elaboration only enriches further. -/
theorem amplifying_comp {f g : Trope I}
    (hf : IsAmplifying f) (hg : IsAmplifying g) :
    IsAmplifying (comp_trope f g) := by
  intro a
  calc depth a
      ≤ depth (g.transform a) := hg a
    _ ≤ depth (f.transform (g.transform a)) := hf (g.transform a)

/-- **Theorem 21**: Faithful tropes compose to faithful tropes.
    LITERARY INSIGHT: composing two perfect metaphors is perfect. -/
theorem faithful_comp {f g : Trope I}
    (hf : IsFaithful f) (hg : IsFaithful g) :
    IsFaithful (comp_trope f g) := by
  rw [faithful_iff_dim_and_amp]
  exact ⟨diminishing_comp (faithful_is_diminishing hf) (faithful_is_diminishing hg),
         amplifying_comp (faithful_is_amplifying hf) (faithful_is_amplifying hg)⟩

/-- **Theorem 22**: A diminishing trope maps void to depth 0.
    LITERARY INSIGHT: simplifying silence gives silence-depth. -/
theorem diminishing_void_depth {f : Trope I} (h : IsDiminishing f) :
    depth (f.transform (void : I)) = 0 := by
  have h1 := h (void : I)
  rw [depth_void] at h1
  omega

/-- **Theorem 23**: A diminishing trope maps atomic ideas to depth ≤ 1. -/
theorem diminishing_atomic {f : Trope I} (h : IsDiminishing f)
    (a : I) (ha : atomic a) :
    depth (f.transform a) ≤ 1 :=
  le_trans (h a) (depth_atomic a ha)

end DepthClassifications

/-! ## §4. Iterated Application

Applying a trope repeatedly: `iterate_transform f n a` applies f to a
exactly n times. Depth bounds accumulate predictably. -/

section IteratedApplication

/-- Iterated trope application: apply the trope n times. -/
def iterate_transform (f : Trope I) : ℕ → I → I
  | 0 => id
  | n + 1 => f.transform ∘ (iterate_transform f n)

/-- **Theorem 24**: Zero iterations is the identity. -/
@[simp] theorem iterate_zero (f : Trope I) (a : I) :
    iterate_transform f 0 a = a := rfl

/-- **Theorem 25**: One iteration is a single application. -/
theorem iterate_one (f : Trope I) (a : I) :
    iterate_transform f 1 a = f.transform a := rfl

/-- **Theorem 26**: Successor iteration unfolds to transform ∘ iterate. -/
theorem iterate_succ (f : Trope I) (n : ℕ) (a : I) :
    iterate_transform f (n + 1) a = f.transform (iterate_transform f n a) := rfl

/-- **Theorem 27**: Each iteration resonates with the previous.
    LITERARY INSIGHT: each re-reading (re-application of the trope)
    stays semantically connected to the prior reading. -/
theorem iterate_step_resonant (f : Trope I) (n : ℕ) (a : I) :
    resonates (iterate_transform f n a) (iterate_transform f (n + 1) a) :=
  f.preserves_resonance (iterate_transform f n a)

/-- **Theorem 28**: Iterated application resonates with the original.
    LITERARY INSIGHT: no matter how many times you re-interpret,
    the result always echoes the original (via the chain). -/
theorem iterate_resonant_with_original (f : Trope I) :
    ∀ (n : ℕ) (a : I), resonates a (iterate_transform f n a) := by
  intro n
  induction n with
  | zero => intro a; exact resonance_refl a
  | succ n ih =>
    intro a
    exact resonance_trans a (iterate_transform f n a) (iterate_transform f (n + 1) a)
      (ih a) (iterate_step_resonant f n a)

/-- **Theorem 29**: Diminishing trope iterated n times: depth bounded by original.
    LITERARY INSIGHT: repeatedly simplifying never exceeds original complexity. -/
theorem diminishing_iterate {f : Trope I} (h : IsDiminishing f) :
    ∀ (n : ℕ) (a : I), depth (iterate_transform f n a) ≤ depth a := by
  intro n
  induction n with
  | zero => intro a; exact le_refl _
  | succ n ih =>
    intro a
    calc depth (iterate_transform f (n + 1) a)
        = depth (f.transform (iterate_transform f n a)) := rfl
      _ ≤ depth (iterate_transform f n a) := h _
      _ ≤ depth a := ih a

/-- **Theorem 30**: Faithful trope iterated n times preserves depth exactly. -/
theorem faithful_iterate {f : Trope I} (h : IsFaithful f) :
    ∀ (n : ℕ) (a : I), depth (iterate_transform f n a) = depth a := by
  intro n
  induction n with
  | zero => intro a; rfl
  | succ n ih =>
    intro a
    calc depth (iterate_transform f (n + 1) a)
        = depth (f.transform (iterate_transform f n a)) := rfl
      _ = depth (iterate_transform f n a) := h _
      _ = depth a := ih a

end IteratedApplication

/-! ## §5. Irony

An **irony** is a trope whose double application resonates with the original.
Applying irony twice "cancels out" — not exactly (that would be an involution),
but approximately, returning to the resonance neighborhood.
LITERARY INSIGHT: the double meaning of irony unfolds and then refolds,
leaving the reader back where they started — but changed. -/

section Irony

/-- An irony is a trope where applying twice resonates with the original.
    This captures the "double negation" character of ironic speech. -/
structure Irony (I : Type*) [IdeaticSpace I] extends Trope I where
  double_resonant : ∀ (a : I), resonates a (transform (transform a))

/-- **Theorem 31**: The identity is trivially an irony. -/
def id_irony : Irony I where
  transform := id
  preserves_resonance := fun a => resonance_refl a
  double_resonant := fun a => resonance_refl a

/-- **Theorem 32**: An irony's single application resonates with input. -/
theorem irony_single_resonant (f : Irony I) (a : I) :
    resonates a (f.transform a) :=
  f.preserves_resonance a

/-- **Theorem 33**: An irony's double application resonates with input. -/
theorem irony_double_resonant (f : Irony I) (a : I) :
    resonates a (f.transform (f.transform a)) :=
  f.double_resonant a

/-- **Theorem 34**: Triple irony resonates with single irony.
    LITERARY INSIGHT: f(f(f(a))) ≈ f(a) because f(f(x)) ≈ x for x = f(a). -/
theorem irony_triple_single (f : Irony I) (a : I) :
    resonates (f.transform a) (f.transform (f.transform (f.transform a))) :=
  f.double_resonant (f.transform a)

/-- **Theorem 35**: Double irony resonates symmetrically. -/
theorem irony_double_symm (f : Irony I) (a : I) :
    resonates (f.transform (f.transform a)) a :=
  resonance_symm a (f.transform (f.transform a)) (f.double_resonant a)

/-- **Theorem 36**: Irony on composed ideas resonates via composition.
    LITERARY INSIGHT: ironic commentary on a compound idea preserves
    the compound structure through double application. -/
theorem irony_compose_double (f : Irony I) (a b : I) :
    resonates (compose a b)
      (compose (f.transform (f.transform a)) (f.transform (f.transform b))) :=
  resonance_compose a (f.transform (f.transform a)) b (f.transform (f.transform b))
    (f.double_resonant a) (f.double_resonant b)

/-- **Theorem 37**: Quadruple irony resonates with double irony.
    LITERARY INSIGHT: the "spiral" of ironic readings converges —
    each pair of applications brings you back to the neighborhood. -/
theorem irony_quadruple_double (f : Irony I) (a : I) :
    resonates (f.transform (f.transform a))
      (f.transform (f.transform (f.transform (f.transform a)))) :=
  f.double_resonant (f.transform (f.transform a))

/-- **Theorem 38**: Quadruple irony resonates with the original. -/
theorem irony_quadruple_original (f : Irony I) (a : I) :
    resonates a (f.transform (f.transform (f.transform (f.transform a)))) :=
  resonance_trans a (f.transform (f.transform a))
    (f.transform (f.transform (f.transform (f.transform a))))
    (f.double_resonant a) (irony_quadruple_double f a)

end Irony

/-! ## §6. Metaphor (Domain-Crossing Tropes)

A **metaphor** is a trope that maps ideas from a source domain into a target
domain. The defining property: elements of the source are sent to the target.
LITERARY INSIGHT: "Juliet is the sun" maps from the ASTRONOMICAL domain
to the ROMANTIC domain while preserving resonance. -/

section Metaphor

/-- A metaphor is a trope with specified source and target domains.
    The crossing condition ensures source ideas land in the target. -/
structure Metaphor (I : Type*) [IdeaticSpace I] extends Trope I where
  source_domain : Set I
  target_domain : Set I
  crosses : ∀ (a : I), a ∈ source_domain → transform a ∈ target_domain

/-- **Theorem 39**: A metaphor maps source elements to the target. -/
theorem metaphor_maps_source (m : Metaphor I) (a : I) (h : a ∈ m.source_domain) :
    m.transform a ∈ m.target_domain :=
  m.crosses a h

/-- **Theorem 40**: A metaphor applied to a source element resonates with it. -/
theorem metaphor_resonant (m : Metaphor I) (a : I) :
    resonates a (m.transform a) :=
  m.preserves_resonance a

/-- **Theorem 41**: Chaining metaphors — if m₁ maps A→B and m₂ maps B→C,
    their composition maps A→C.
    LITERARY INSIGHT: "the ship of state ploughs through stormy seas"
    chains NAUTICAL→POLITICAL→METEOROLOGICAL metaphors. -/
theorem metaphor_chain_crosses
    (m₁ m₂ : Metaphor I)
    (h_compat : ∀ (a : I), a ∈ m₁.source_domain →
      m₁.transform a ∈ m₂.source_domain)
    (a : I) (ha : a ∈ m₁.source_domain) :
    m₂.transform (m₁.transform a) ∈ m₂.target_domain :=
  m₂.crosses (m₁.transform a) (h_compat a ha)

/-- **Theorem 42**: A metaphor with source = target is an endomorphor
    (internal trope within a single domain). -/
theorem metaphor_endo (m : Metaphor I)
    (h : m.source_domain = m.target_domain)
    (a : I) (ha : a ∈ m.source_domain) :
    m.transform a ∈ m.source_domain := by
  have h1 := m.crosses a ha
  rw [← h] at h1
  exact h1

/-- **Theorem 43**: The identity metaphor on any domain maps the domain to itself. -/
def id_metaphor (d : Set I) : Metaphor I where
  transform := id
  preserves_resonance := fun a => resonance_refl a
  source_domain := d
  target_domain := d
  crosses := fun _ h => h

end Metaphor

/-! ## §7. Parallelism and Coherence

**Parallelism** applies the same trope to every element of a list.
LITERARY INSIGHT: anaphora ("I have a dream that... I have a dream that...")
is parallel application of a framing trope.

**Coherence** means adjacent elements resonate. We show that parallel application
preserves certain coherence properties. -/

section ParallelismCoherence

/-- Parallel application: apply the same trope to every element of a list. -/
def parallel_apply (f : Trope I) (s : List I) : List I :=
  s.map f.transform

/-- **Theorem 44**: Parallel application preserves list length.
    LITERARY INSIGHT: parallelism doesn't add or remove elements —
    it transforms each one in place. -/
theorem parallel_length (f : Trope I) (s : List I) :
    (parallel_apply f s).length = s.length := by
  simp [parallel_apply]

/-- **Theorem 45**: Parallel application of the identity is the identity. -/
theorem parallel_id (s : List I) :
    parallel_apply (id_trope : Trope I) s = s := by
  simp [parallel_apply, id_trope, List.map_id]

/-- **Theorem 46**: Parallel application distributes over append.
    LITERARY INSIGHT: applying a trope to a concatenated text is the same
    as applying it to each part separately. -/
theorem parallel_append (f : Trope I) (s t : List I) :
    parallel_apply f (s ++ t) = parallel_apply f s ++ parallel_apply f t := by
  simp [parallel_apply, List.map_append]

/-- **Theorem 47**: Parallel application of the empty list is empty. -/
@[simp] theorem parallel_nil (f : Trope I) :
    parallel_apply f ([] : List I) = [] := rfl

/-- **Theorem 48**: Parallel application of a singleton. -/
theorem parallel_singleton (f : Trope I) (a : I) :
    parallel_apply f [a] = [f.transform a] := rfl

/-- **Theorem 49**: Parallel application of a cons. -/
theorem parallel_cons (f : Trope I) (a : I) (s : List I) :
    parallel_apply f (a :: s) = f.transform a :: parallel_apply f s := rfl

/-- **Theorem 50**: Composing parallel applications is parallel application
    of the composed trope.
    LITERARY INSIGHT: applying one trope then another to each element
    is the same as applying the composed trope to each element. -/
theorem parallel_comp (f g : Trope I) (s : List I) :
    parallel_apply f (parallel_apply g s) = parallel_apply (comp_trope f g) s := by
  simp [parallel_apply, comp_trope, List.map_map]

/-- A list is **coherent** if every adjacent pair resonates.
    LITERARY INSIGHT: in a coherent text, each idea flows into the next. -/
def Coherent : List I → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => resonates a b ∧ Coherent (b :: rest)

/-- **Theorem 51**: The empty list is vacuously coherent. -/
theorem coherent_nil : Coherent ([] : List I) := trivial

/-- **Theorem 52**: A singleton list is coherent. -/
theorem coherent_singleton (a : I) : Coherent [a] := trivial

/-- **Theorem 53**: A pair is coherent iff the two elements resonate. -/
theorem coherent_pair (a b : I) :
    Coherent [a, b] ↔ resonates a b := by
  constructor
  · intro h; exact h.1
  · intro h; exact ⟨h, trivial⟩

end ParallelismCoherence

/-! ## §8. Rhetorical Figures

Formalization of specific rhetorical devices:
- **Anaphora**: repetition at the beginning (same idea repeated)
- **Epistrophe**: repetition at the end (same ending for each idea)
- **Chiasmus**: ABBA structure (reversal of composition order) -/

section RhetoricalFigures

/-- Anaphora: repeating the same idea n times.
    LITERARY INSIGHT: "I have a dream..." repeated creates emphasis
    through rhythmic repetition. -/
def anaphora (a : I) (n : ℕ) : List I := List.replicate n a

/-- **Theorem 54**: Anaphora has the specified length. -/
theorem anaphora_length (a : I) (n : ℕ) : (@anaphora I a n).length = n :=
  List.length_replicate n a

/-- **Theorem 55**: Zero-length anaphora is the empty list. -/
@[simp] theorem anaphora_zero (a : I) : @anaphora I a 0 = [] := rfl

/-- **Theorem 56**: Anaphora is always coherent — every adjacent pair
    is the same element, which resonates with itself.
    LITERARY INSIGHT: repetition is the simplest form of coherence. -/
theorem anaphora_coherent (a : I) (n : ℕ) : Coherent (anaphora a n) := by
  unfold anaphora
  induction n with
  | zero => exact trivial
  | succ m ih =>
    cases m with
    | zero => exact trivial
    | succ k => exact ⟨resonance_refl a, ih⟩

/-- **Theorem 57**: Parallel application of a trope to anaphora gives
    anaphora of the transformed element.
    LITERARY INSIGHT: applying the same figure to a repeated element
    gives repetition of the figured element. -/
theorem parallel_anaphora (f : Trope I) (a : I) (n : ℕ) :
    parallel_apply f (anaphora a n) = anaphora (f.transform a) n := by
  simp [parallel_apply, anaphora, List.map_replicate]

/-- Epistrophe: each idea in a list is composed with a fixed ending.
    LITERARY INSIGHT: "...of the people, ...by the people, ...for the people"
    — each clause ends the same way. -/
def epistrophe (elements : List I) (ending : I) : List I :=
  elements.map (fun a => compose a ending)

/-- **Theorem 58**: Epistrophe preserves list length. -/
theorem epistrophe_length (elements : List I) (ending : I) :
    (epistrophe elements ending).length = elements.length := by
  simp [epistrophe]

/-- **Theorem 59**: Epistrophe with void ending is the identity.
    LITERARY INSIGHT: ending with silence changes nothing. -/
theorem epistrophe_void (elements : List I) :
    epistrophe elements (void : I) = elements := by
  simp [epistrophe, void_right, List.map_id']

/-- Chiasmus: the ABBA pattern — compose a b vs compose b a.
    LITERARY INSIGHT: "ask not what your country can do for you —
    ask what you can do for your country" reverses the composition. -/
def chiasmus (a b : I) : I × I := (compose a b, compose b a)

/-- **Theorem 60**: The first element of a chiasmus is compose a b. -/
theorem chiasmus_fst (a b : I) : (chiasmus a b).1 = compose a b := rfl

/-- **Theorem 61**: The second element is compose b a. -/
theorem chiasmus_snd (a b : I) : (chiasmus a b).2 = compose b a := rfl

/-- **Theorem 62**: A chiasmus with void gives (a, a).
    LITERARY INSIGHT: reversing "something and nothing" is still "something". -/
theorem chiasmus_void_right (a : I) :
    chiasmus a (void : I) = (a, a) := by
  simp [chiasmus, void_right, void_left]

/-- **Theorem 63**: Both halves of a chiasmus have bounded depth. -/
theorem chiasmus_depth_bound (a b : I) :
    depth (chiasmus a b).1 ≤ depth a + depth b ∧
    depth (chiasmus a b).2 ≤ depth b + depth a := by
  constructor
  · exact depth_subadditive a b
  · exact depth_subadditive b a

/-- **Theorem 64**: A chiasmus where a = b gives the same element twice. -/
theorem chiasmus_self (a : I) : (chiasmus a a).1 = (chiasmus a a).2 := rfl

end RhetoricalFigures

/-! ## §9. Depth Spectrum

A trope is **k-bounded** if it changes depth by at most k.
LITERARY INSIGHT: some tropes are "mild" (small k), transforming meaning
gently; others are "radical" (large k), transforming meaning drastically.
The depth spectrum classifies tropes by their maximum depth change. -/

section DepthSpectrum

/-- A trope is **depth-bounded by k** if depth never increases by more than k. -/
def IsDepthBounded (f : Trope I) (k : ℕ) : Prop :=
  ∀ (a : I), depth (f.transform a) ≤ depth a + k

/-- **Theorem 65**: The identity trope is 0-bounded. -/
theorem id_depth_bounded_zero : IsDepthBounded (id_trope : Trope I) 0 := by
  intro a; simp [id_trope]

/-- **Theorem 66**: A diminishing trope is 0-bounded.
    LITERARY INSIGHT: diminishing tropes are the "mildest" — they
    never increase complexity at all. -/
theorem diminishing_is_zero_bounded {f : Trope I} (h : IsDiminishing f) :
    IsDepthBounded f 0 := by
  intro a
  simp
  exact h a

/-- **Theorem 67**: If a trope is k-bounded, it is also m-bounded for m ≥ k.
    LITERARY INSIGHT: a mild trope is automatically classified as
    radical — mild is a special case of radical. -/
theorem depth_bounded_weaken {f : Trope I} {k m : ℕ}
    (hkm : k ≤ m) (h : IsDepthBounded f k) : IsDepthBounded f m := by
  intro a
  calc depth (f.transform a) ≤ depth a + k := h a
    _ ≤ depth a + m := Nat.add_le_add_left hkm _

/-- **Theorem 68**: Composing a k-bounded and an m-bounded trope gives
    a (k+m)-bounded trope.
    LITERARY INSIGHT: layering a mild trope on a moderate trope gives
    a result bounded by the sum of their depth budgets. -/
theorem depth_bounded_comp {f g : Trope I} {k m : ℕ}
    (hf : IsDepthBounded f k) (hg : IsDepthBounded g m) :
    IsDepthBounded (comp_trope f g) (k + m) := by
  intro a
  calc depth ((comp_trope f g).transform a)
      = depth (f.transform (g.transform a)) := rfl
    _ ≤ depth (g.transform a) + k := hf (g.transform a)
    _ ≤ (depth a + m) + k := Nat.add_le_add_right (hg a) k
    _ = depth a + (m + k) := by omega
    _ = depth a + (k + m) := by omega

/-- **Theorem 69**: A k-bounded trope applied to void has depth ≤ k.
    LITERARY INSIGHT: applying a bounded trope to silence produces
    something of bounded complexity. -/
theorem depth_bounded_void {f : Trope I} {k : ℕ}
    (h : IsDepthBounded f k) : depth (f.transform (void : I)) ≤ k := by
  have := h (void : I)
  rw [depth_void] at this
  omega

/-- **Theorem 70**: A k-bounded trope applied to an atomic idea has depth ≤ 1 + k. -/
theorem depth_bounded_atomic {f : Trope I} {k : ℕ}
    (h : IsDepthBounded f k) (a : I) (ha : atomic a) :
    depth (f.transform a) ≤ 1 + k := by
  have h1 := h a
  have h2 := depth_atomic a ha
  omega

/-- **Theorem 71**: Iterated k-bounded trope: depth after n applications ≤ depth a + n * k.
    LITERARY INSIGHT: repeated application of a bounded trope accumulates
    depth change linearly. -/
theorem depth_bounded_iterate {f : Trope I} {k : ℕ}
    (h : IsDepthBounded f k) :
    ∀ (n : ℕ) (a : I), depth (iterate_transform f n a) ≤ depth a + n * k := by
  intro n
  induction n with
  | zero => intro a; simp [iterate_transform]
  | succ n ih =>
    intro a
    calc depth (iterate_transform f (n + 1) a)
        = depth (f.transform (iterate_transform f n a)) := rfl
      _ ≤ depth (iterate_transform f n a) + k := h _
      _ ≤ (depth a + n * k) + k := Nat.add_le_add_right (ih a) k
      _ = depth a + (n * k + k) := by omega
      _ = depth a + (n + 1) * k := by ring_nf

end DepthSpectrum

/-! ## §10. Additional Algebraic Properties

Further theorems connecting the various structures. -/

section AdditionalProperties

/-- The total depth of a list of ideas. -/
def depthSum (s : List I) : ℕ := s.foldl (fun acc x => acc + depth x) 0

/-- **Theorem 72**: Depth sum of the empty list is 0. -/
@[simp] theorem depthSum_nil : depthSum ([] : List I) = 0 := rfl

/-- Depth sum as a map-then-sum, equivalent formulation. -/
def depthSumAlt (s : List I) : ℕ := (s.map depth).sum

/-- **Theorem 73**: Depth sum of a singleton. -/
theorem depthSumAlt_singleton (a : I) : depthSumAlt [a] = depth a := by
  simp [depthSumAlt]

/-- **Theorem 74**: A diminishing trope cannot increase the alt depth sum
    of a singleton. -/
theorem diminishing_depthSumAlt_singleton {f : Trope I} (h : IsDiminishing f) (a : I) :
    depthSumAlt (parallel_apply f [a]) ≤ depthSumAlt [a] := by
  simp [depthSumAlt, parallel_apply]
  exact h a

/-- A trope is **resonance-strengthening** if the composed pair always
    has bounded depth relative to input. -/
def IsResonanceStrengthening (f : Trope I) : Prop :=
  ∀ (a : I), depth (compose a (f.transform a)) ≤ 2 * depth a

/-- **Theorem 75**: A diminishing, resonance-strengthening trope has the
    composed pair bounded by twice the input depth. -/
theorem dim_strengthening_bound {f : Trope I}
    (hd : IsDiminishing f) (a : I) :
    depth (compose a (f.transform a)) ≤ depth a + depth a := by
  calc depth (compose a (f.transform a))
      ≤ depth a + depth (f.transform a) := depth_subadditive a (f.transform a)
    _ ≤ depth a + depth a := Nat.add_le_add_left (hd a) _

/-- **Theorem 76**: Void composed with a trope's output has bounded depth. -/
theorem void_trope_depth {f : Trope I} {k : ℕ}
    (h : IsDepthBounded f k) :
    depth (compose (void : I) (f.transform (void : I))) ≤ k := by
  rw [void_left]
  exact depth_bounded_void h

/-- **Theorem 77**: Faithful trope applied to void gives depth 0. -/
theorem faithful_void_depth {f : Trope I} (h : IsFaithful f) :
    depth (f.transform (void : I)) = 0 := by
  rw [h]; exact depth_void

/-- **Theorem 78**: Composing two trope outputs has depth bounded by the
    sum of their individual depth bounds. -/
theorem compose_trope_outputs_depth (f g : Trope I) (a b : I) :
    depth (compose (f.transform a) (g.transform b)) ≤
    depth (f.transform a) + depth (g.transform b) :=
  depth_subadditive (f.transform a) (g.transform b)

/-- **Theorem 79**: A diminishing trope composed with itself (applied sequentially)
    gives depth ≤ original depth. -/
theorem diminishing_double {f : Trope I} (h : IsDiminishing f) (a : I) :
    depth (f.transform (f.transform a)) ≤ depth a :=
  le_trans (h (f.transform a)) (h a)

/-- **Theorem 80**: An amplifying trope applied twice gives depth ≥ original. -/
theorem amplifying_double {f : Trope I} (h : IsAmplifying f) (a : I) :
    depth a ≤ depth (f.transform (f.transform a)) :=
  le_trans (h a) (h (f.transform a))

/-- **Theorem 81**: A faithful trope applied n times to void always gives depth 0. -/
theorem faithful_iterate_void {f : Trope I} (h : IsFaithful f) (n : ℕ) :
    depth (iterate_transform f n (void : I)) = 0 := by
  rw [faithful_iterate h]
  exact depth_void

/-- **Theorem 82**: Every trope resonates with the identity trope's output
    when applied to the same element. -/
theorem trope_resonates_with_id (f : Trope I) (a : I) :
    resonates ((id_trope : Trope I).transform a) (f.transform a) := by
  simp [id_trope]
  exact f.preserves_resonance a

/-- **Theorem 83**: Two tropes applied to the same input have outputs
    that both resonate with the input, hence with each other (via transitivity). -/
theorem two_tropes_resonate (f g : Trope I) (a : I) :
    resonates (f.transform a) (g.transform a) := by
  exact resonance_trans (f.transform a) a (g.transform a)
    (trope_resonant_symm f a) (g.preserves_resonance a)

/-- **Theorem 84**: Parallel application to anaphora of void gives anaphora
    of trope-applied-void. -/
theorem parallel_anaphora_void (f : Trope I) (n : ℕ) :
    parallel_apply f (anaphora (void : I) n) = anaphora (f.transform void) n := by
  simp [parallel_apply, anaphora, List.map_replicate]

end AdditionalProperties

end LiteraryRhetoric
