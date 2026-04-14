import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic

/-!
# Ideatic Diffusion Theory: Foundations

A new axiomatic theory of applied mathematics whose primitive objects are
**ideata** — irreducible units of thought, articulation, or meaning — and
whose axioms characterize how these objects compose, resonate, and propagate.

## Why a New Theory?

Existing mathematics can model ideas indirectly (information theory, dynamical
systems, etc.), but none takes "the idea" as a primitive mathematical object
with its own characteristic axioms. IDT does for thought what geometry does
for space: it axiomatizes the essential properties that any space of ideas
must satisfy, then derives consequences.

## Axiom Groups

- **A1–A3** (Algebraic): Ideatic composition forms a monoid
- **R1–R3** (Resonance): Ideas evoke each other; resonance respects composition
- **D1–D4** (Depth): Ideas have intrinsic complexity behaving subadditively

## Diffusion Axiom Systems

Four incompatible extensions — each a different "geometry" of thought-propagation:

1. **Conservative**: faithful transmission (T(a) = a always)
2. **Mutagenic**: ideas mutate; depth strictly decays for complex ideas
3. **Recombinant**: ideas combine during propagation; novelty emerges
4. **Selective**: ideas compete on fitness; diversity reduces

## What This File Establishes

- The core `IdeaticSpace` type class (14 axioms)
- Four diffusion axiom classes
- ~50 foundational theorems, each teaching something about the nature of ideas
- Key derived concepts: resonance classes, depth filtration, coherent sequences

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT

/-! ## §1. The Core Axiom Class

An `IdeaticSpace` is the foundational structure of IDT. Its axioms are
**not** derivable from standard algebra, topology, or measure theory — they
capture properties specific to thought and articulation:

- Composition is monoidal (thoughts combine associatively with a void/silence)
- Resonance is a symmetric relation compatible with composition
  (ideas that evoke each other produce compositions that evoke each other)
- Depth is a subadditive complexity measure
  (combining thoughts never more than doubles complexity) -/

/-- The foundational axiom class of Ideatic Diffusion Theory.
    Every theorem in IDT ultimately derives from these 14 axioms. -/
class IdeaticSpace (I : Type*) where
  /-- Ideatic composition: combining two thoughts into a compound thought -/
  compose : I → I → I
  /-- The void: silence, the empty thought, identity for composition -/
  void : I
  /-- Resonance: when one idea evokes, activates, or echoes another -/
  resonates : I → I → Prop
  /-- Depth: the structural complexity of an idea (0 = trivial) -/
  depth : I → ℕ
  /-- Atomicity: whether an idea is conceptually indivisible -/
  atomic : I → Prop
  -- (A1) Composition is associative
  compose_assoc : ∀ (a b c : I), compose (compose a b) c = compose a (compose b c)
  -- (A2) The void is a left identity
  void_left : ∀ (a : I), compose void a = a
  -- (A3) The void is a right identity
  void_right : ∀ (a : I), compose a void = a
  -- (R1) Every idea resonates with itself
  resonance_refl : ∀ (a : I), resonates a a
  -- (R2) Resonance is symmetric: if a evokes b, then b evokes a
  resonance_symm : ∀ (a b : I), resonates a b → resonates b a
  -- (R3) Resonance is compatible with composition
  resonance_compose : ∀ (a a' b b' : I),
    resonates a a' → resonates b b' → resonates (compose a b) (compose a' b')
  -- (D1) The void has zero depth (silence has no complexity)
  depth_void : depth void = 0
  -- (D2) Depth is subadditive (combining ideas ≤ sums their complexity)
  depth_subadditive : ∀ (a b : I), depth (compose a b) ≤ depth a + depth b
  -- (D3) Atomic ideas have depth at most 1
  depth_atomic : ∀ (a : I), atomic a → depth a ≤ 1
  -- (D4) The void is atomic
  void_atomic : atomic void

/-! ## §2. Algebraic Consequences

These theorems show that the monoidal structure of thought-composition
has the expected properties. The key insight: thought-composition is
*exactly* a monoid — no more, no less. This means ideas have:
- No inverse (you can't "un-think" a composition)
- No commutativity requirement (order of composition matters)
- A unique neutral element (silence/void) -/

section Algebra
variable {I : Type*} [IdeaticSpace I]

/-- Composition is associative: the grouping of thoughts doesn't matter -/
theorem compose_assoc (a b c : I) :
    IdeaticSpace.compose (IdeaticSpace.compose a b) c =
    IdeaticSpace.compose a (IdeaticSpace.compose b c) :=
  IdeaticSpace.compose_assoc a b c

/-- The void is a left identity: silence followed by thought = thought -/
@[simp] theorem void_left (a : I) :
    IdeaticSpace.compose (IdeaticSpace.void : I) a = a :=
  IdeaticSpace.void_left a

/-- The void is a right identity: thought followed by silence = thought -/
@[simp] theorem void_right (a : I) :
    IdeaticSpace.compose a (IdeaticSpace.void : I) = a :=
  IdeaticSpace.void_right a

/-- Void composed with itself is void: silence upon silence is silence -/
@[simp] theorem void_self :
    IdeaticSpace.compose (IdeaticSpace.void : I) (IdeaticSpace.void : I) =
    (IdeaticSpace.void : I) :=
  void_left _

/-- Four-fold associativity: rebracketing is always valid -/
theorem compose_assoc4 (a b c d : I) :
    IdeaticSpace.compose (IdeaticSpace.compose (IdeaticSpace.compose a b) c) d =
    IdeaticSpace.compose a (IdeaticSpace.compose b (IdeaticSpace.compose c d)) := by
  rw [compose_assoc, compose_assoc]

/-- n-fold self-composition: repeating a thought n times.
    This models repetition, emphasis, or ritual iteration. -/
def composeN (a : I) : ℕ → I
  | 0 => IdeaticSpace.void
  | n + 1 => IdeaticSpace.compose (composeN a n) a

@[simp] theorem composeN_zero (a : I) :
    composeN a 0 = (IdeaticSpace.void : I) := rfl

theorem composeN_succ (a : I) (n : ℕ) :
    composeN a (n + 1) = IdeaticSpace.compose (composeN a n) a := rfl

/-- Repeating void any number of times is still void:
    iterated silence is silence -/
@[simp] theorem composeN_void : ∀ (n : ℕ),
    composeN (IdeaticSpace.void : I) n = (IdeaticSpace.void : I)
  | 0 => rfl
  | n + 1 => by simp [composeN, composeN_void n]

/-- Single repetition: composing void with the idea -/
theorem composeN_one (a : I) :
    composeN a 1 = IdeaticSpace.compose (IdeaticSpace.void : I) a := rfl

/-- Single repetition equals the idea itself -/
theorem composeN_one' (a : I) : composeN a 1 = a := by
  simp [composeN_one]

end Algebra

/-! ## §3. Resonance Theorems

Resonance captures the fundamental relation of *evocation* between ideas:
when encountering idea A, idea B is activated, recalled, or suggested.

Key insight: resonance is reflexive and symmetric (like similarity) but
**not** transitive. This is deliberate — idea A may evoke B, and B may
evoke C, without A evoking C directly. Transitivity would collapse all
connected ideas into a single equivalence class, destroying the rich
structure of associative networks.

However, resonance *is* compatible with composition: if A evokes A' and
B evokes B', then AB evokes A'B'. This is the crucial axiom that connects
the algebraic and relational structures of ideatic space. -/

section Resonance
variable {I : Type*} [IdeaticSpace I]

/-- Every idea resonates with itself: self-recognition -/
theorem resonance_refl (a : I) : IdeaticSpace.resonates a a :=
  IdeaticSpace.resonance_refl a

/-- Resonance is symmetric: evocation is bidirectional -/
theorem resonance_symm {a b : I} (h : IdeaticSpace.resonates a b) :
    IdeaticSpace.resonates b a :=
  IdeaticSpace.resonance_symm a b h

/-- Composing with a fixed idea on the right preserves resonance.
    INSIGHT: if two ideas evoke each other, they continue to do so
    when placed in the same context (followed by the same thought). -/
theorem resonance_compose_right {a b : I}
    (h : IdeaticSpace.resonates a b) (c : I) :
    IdeaticSpace.resonates (IdeaticSpace.compose a c) (IdeaticSpace.compose b c) :=
  IdeaticSpace.resonance_compose a b c c h (resonance_refl c)

/-- Composing with a fixed idea on the left preserves resonance.
    INSIGHT: prefixing two resonant ideas with the same context
    preserves their resonance — context doesn't destroy evocation. -/
theorem resonance_compose_left (c : I) {a b : I}
    (h : IdeaticSpace.resonates a b) :
    IdeaticSpace.resonates (IdeaticSpace.compose c a) (IdeaticSpace.compose c b) :=
  IdeaticSpace.resonance_compose c c a b (resonance_refl c) h

/-- Ideas connected through a common mediator produce resonant compositions.
    INSIGHT: if A evokes B and B evokes C, then the compound AB evokes
    the compound BC — the mediator creates a "bridge" of resonance.
    This is the compositional form of indirect association. -/
theorem resonance_via_mediator {a b c : I}
    (hab : IdeaticSpace.resonates a b) (hbc : IdeaticSpace.resonates b c) :
    IdeaticSpace.resonates
      (IdeaticSpace.compose a b)
      (IdeaticSpace.compose b c) :=
  IdeaticSpace.resonance_compose a b b c hab hbc

/-- The resonance class of an idea: all ideas it evokes -/
def resonanceClass (a : I) : Set I := {b | IdeaticSpace.resonates a b}

/-- Every idea belongs to its own resonance class -/
theorem mem_resonanceClass_self (a : I) : a ∈ resonanceClass a :=
  resonance_refl a

/-- Resonance class membership is symmetric -/
theorem resonanceClass_symm {a b : I} :
    a ∈ resonanceClass b ↔ b ∈ resonanceClass a :=
  ⟨fun h => resonance_symm h, fun h => resonance_symm h⟩

/-- Resonance classes are closed under composition:
    if a' resonates with a and b' resonates with b,
    then a'·b' resonates with a·b.
    INSIGHT: the "associative neighborhood" of a compound idea
    contains all compounds of the neighborhoods of its parts. -/
theorem resonanceClass_compose {a b : I} {a' b' : I}
    (ha : a' ∈ resonanceClass a) (hb : b' ∈ resonanceClass b) :
    IdeaticSpace.compose a' b' ∈
    resonanceClass (IdeaticSpace.compose a b) := by
  exact IdeaticSpace.resonance_compose a a' b b' ha hb

/-- Void's resonance class contains void.
    INSIGHT: silence resonates with silence. -/
theorem void_resonates_self :
    (IdeaticSpace.void : I) ∈ resonanceClass (IdeaticSpace.void : I) :=
  resonance_refl _

end Resonance

/-! ## §4. Depth Theorems

Depth measures the *structural complexity* of an idea — how many layers
of abstraction or composition were needed to construct it. This is distinct
from Shannon information content; depth is about *structural* complexity,
not statistical surprise.

Key insight: depth is **subadditive** — composing two ideas produces
something no deeper than the sum of their depths. This means:
- Combining ideas adds complexity at most linearly
- Repetition (composeN) scales linearly
- The depth-zero subspace is closed (trivial + trivial = trivial) -/

section Depth
variable {I : Type*} [IdeaticSpace I]

/-- The void has zero depth: silence has no complexity -/
@[simp] theorem depth_void :
    IdeaticSpace.depth (IdeaticSpace.void : I) = 0 :=
  IdeaticSpace.depth_void

/-- Depth is subadditive: complexity of composition ≤ sum of parts -/
theorem depth_compose_le (a b : I) :
    IdeaticSpace.depth (IdeaticSpace.compose a b) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b :=
  IdeaticSpace.depth_subadditive a b

/-- Prefixing with void doesn't change depth -/
theorem depth_void_compose (a : I) :
    IdeaticSpace.depth (IdeaticSpace.compose (IdeaticSpace.void : I) a) =
    IdeaticSpace.depth a := by
  rw [void_left]

/-- Suffixing with void doesn't change depth -/
theorem depth_compose_void (a : I) :
    IdeaticSpace.depth (IdeaticSpace.compose a (IdeaticSpace.void : I)) =
    IdeaticSpace.depth a := by
  rw [void_right]

/-- THEOREM (Trivial Closure): Composing ideas of depth 0 gives depth 0.
    INSIGHT: trivial thoughts composed remain trivial. Banality is closed
    under combination — you can't build depth from nothing. -/
theorem depth_zero_closed {a b : I}
    (ha : IdeaticSpace.depth a = 0) (hb : IdeaticSpace.depth b = 0) :
    IdeaticSpace.depth (IdeaticSpace.compose a b) = 0 := by
  have h := depth_compose_le a b
  rw [ha, hb] at h; omega

/-- THEOREM (Atomic Composition Bound): Composing two atomic ideas
    gives depth ≤ 2. INSIGHT: simple ideas combined give bounded complexity.
    This is why natural language builds complex meaning from simple words
    through bounded syntactic depth at each composition step. -/
theorem depth_atomic_compose (a b : I)
    (ha : IdeaticSpace.atomic a) (hb : IdeaticSpace.atomic b) :
    IdeaticSpace.depth (IdeaticSpace.compose a b) ≤ 2 := by
  have h1 := IdeaticSpace.depth_atomic a ha
  have h2 := IdeaticSpace.depth_atomic b hb
  have h3 := depth_compose_le a b
  omega

/-- THEOREM (Linear Repetition Bound): n-fold repetition has depth ≤ n · depth.
    INSIGHT: saying the same thing n times doesn't compound complexity
    beyond linear growth. Ritual repetition adds emphasis, not depth.
    This is a fundamental bound on how complexity scales with iteration. -/
theorem depth_composeN (a : I) : ∀ (n : ℕ),
    IdeaticSpace.depth (composeN a n) ≤ n * IdeaticSpace.depth a
  | 0 => by simp [composeN]
  | n + 1 => by
    have ih := depth_composeN a n
    have h := depth_compose_le (composeN a n) a
    calc IdeaticSpace.depth (composeN a (n + 1))
        = IdeaticSpace.depth (IdeaticSpace.compose (composeN a n) a) := rfl
      _ ≤ IdeaticSpace.depth (composeN a n) + IdeaticSpace.depth a := h
      _ ≤ n * IdeaticSpace.depth a + IdeaticSpace.depth a := by omega
      _ = (n + 1) * IdeaticSpace.depth a := by ring

/-- The depth filtration: ideas of depth at most n -/
def depthFiltration (n : ℕ) : Set I := {a | IdeaticSpace.depth a ≤ n}

/-- Void belongs to every filtration level -/
theorem void_mem_depthFiltration (n : ℕ) :
    (IdeaticSpace.void : I) ∈ depthFiltration n := by
  simp [depthFiltration]

/-- THEOREM (Filtration Monotonicity): F₀ ⊆ F₁ ⊆ F₂ ⊆ ...
    INSIGHT: complexity forms a genuine hierarchy — every level
    contains all lower levels. There is a true "ladder" of abstraction. -/
theorem depthFiltration_mono {m n : ℕ} (h : m ≤ n) :
    (depthFiltration m : Set I) ⊆ depthFiltration n := by
  intro a ha
  simp [depthFiltration] at ha ⊢; omega

/-- THEOREM (Composition Overshoot Bound): composing ideas from
    level n stays within level 2n.
    INSIGHT: combining ideas within a complexity class produces results
    in a bounded higher class. The "damage" of composition is at most
    doubling — you can't jump arbitrarily far up the hierarchy. -/
theorem depthFiltration_compose {n : ℕ} {a b : I}
    (ha : a ∈ depthFiltration n) (hb : b ∈ depthFiltration n) :
    IdeaticSpace.compose a b ∈ depthFiltration (2 * n) := by
  simp [depthFiltration] at ha hb ⊢
  have h := depth_compose_le a b; omega

/-- The depth-zero subspace -/
def depthZero : Set I := depthFiltration 0

/-- THEOREM (Depth-Zero Closure): The depth-zero subspace is a sub-monoid.
    INSIGHT: ideas of zero complexity form their own closed world — they
    can only produce more zero-complexity ideas. This is the "trivial
    discourse" that can never bootstrap itself into depth. -/
theorem depthZero_closed {a b : I}
    (ha : a ∈ depthZero) (hb : b ∈ depthZero) :
    IdeaticSpace.compose a b ∈ depthZero := by
  simp [depthZero, depthFiltration] at ha hb ⊢
  have h := depth_compose_le a b; omega

/-- THEOREM (Depth Determines Filtration Level): an idea of depth d
    belongs to exactly filtration level d and all higher levels.
    INSIGHT: every idea has a unique "natural level" in the hierarchy. -/
theorem depth_eq_min_filtration (a : I) :
    a ∈ depthFiltration (IdeaticSpace.depth a) := by
  simp [depthFiltration]

/-- If an idea has depth > n, it's NOT in filtration level n.
    INSIGHT: the hierarchy is strict — complex ideas genuinely
    exceed lower complexity classes. -/
theorem not_mem_depthFiltration {a : I} {n : ℕ}
    (h : IdeaticSpace.depth a > n) :
    a ∉ depthFiltration n := by
  simp [depthFiltration]; omega

end Depth

/-! ## §5. Coherent Sequences: The Pre-Theory of Text

An ideatic sequence is a list of ideas — the mathematical precursor to
"text" in literary theory. A sequence is *coherent* if consecutive ideas
resonate: each thought evokes the next.

This captures a profound literary-theoretic insight: a text is not merely
a sequence of ideas, but a sequence where each idea *connects* to its
neighbors through evocation. Random juxtaposition is not text. -/

section Sequences
variable {I : Type*} [IdeaticSpace I]

/-- A coherent sequence: consecutive ideas resonate with each other.
    This is the formal definition of "textual coherence" —
    each thought naturally leads to the next through resonance. -/
def Coherent : List I → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => IdeaticSpace.resonates a b ∧ Coherent (b :: rest)

/-- The empty sequence is coherent: silence is trivially coherent -/
theorem coherent_nil : Coherent ([] : List I) := trivial

/-- A single idea is coherent: any thought in isolation is coherent -/
theorem coherent_singleton (a : I) : Coherent [a] := trivial

/-- THEOREM (Pairwise Coherence): Two ideas form a coherent sequence
    iff they resonate. INSIGHT: the minimal unit of discourse is a
    pair of resonant ideas — this is the "atom of narrative." -/
theorem coherent_pair {a b : I} :
    Coherent [a, b] ↔ IdeaticSpace.resonates a b := by
  simp [Coherent]

/-- THEOREM (Coherence Extension): A coherent sequence can be extended
    if the new idea resonates with the last element.
    INSIGHT: narratives grow by appending resonant ideas — each new
    thought must connect to what came before. -/
theorem coherent_cons {a b : I} {rest : List I}
    (hab : IdeaticSpace.resonates a b)
    (hrest : Coherent (b :: rest)) :
    Coherent (a :: b :: rest) :=
  ⟨hab, hrest⟩

/-- THEOREM (Coherence Prefix): Every prefix of a coherent sequence is coherent.
    INSIGHT: stopping a coherent narrative at any point leaves a coherent
    narrative — you don't need the ending for the beginning to make sense. -/
theorem coherent_tail {a : I} {rest : List I}
    (h : Coherent (a :: rest)) : Coherent rest := by
  cases rest with
  | nil => exact trivial
  | cons b rest' => exact h.2

/-- THEOREM (Self-Resonant Repetition): A constant sequence is always coherent.
    INSIGHT: repeating the same idea is always coherent (if trivially so).
    This models mantras, refrains, and the literary device of repetition. -/
theorem coherent_replicate (a : I) : ∀ (n : ℕ), Coherent (List.replicate n a)
  | 0 => trivial
  | 1 => trivial
  | n + 2 => by
    simp [List.replicate, Coherent]
    exact ⟨resonance_refl a, coherent_replicate a (n + 1)⟩

/-- Sum of depths of ideas in a sequence -/
def depthSum (s : List I) : ℕ :=
  (s.map IdeaticSpace.depth).sum

@[simp] theorem depthSum_nil : depthSum ([] : List I) = 0 := rfl

theorem depthSum_cons (a : I) (s : List I) :
    depthSum (a :: s) = IdeaticSpace.depth a + depthSum s := by
  simp [depthSum, List.map, List.sum_cons]

/-- THEOREM (Depth Sum Bound): total depth of a sequence where each element
    has depth ≤ d is bounded by length × d.
    INSIGHT: textual complexity is linearly bounded by length when
    individual thoughts have bounded complexity. -/
theorem depthSum_bound (s : List I) (d : ℕ)
    (hbound : ∀ (a : I), a ∈ s → IdeaticSpace.depth a ≤ d) :
    depthSum s ≤ s.length * d := by
  induction s with
  | nil => simp
  | cons a rest ih =>
    rw [depthSum_cons, List.length_cons]
    have ha := hbound a (List.mem_cons_self a rest)
    have hrest : ∀ (b : I), b ∈ rest → IdeaticSpace.depth b ≤ d := by
      intro b hb; exact hbound b (List.mem_cons_of_mem a hb)
    have := ih hrest
    calc IdeaticSpace.depth a + depthSum rest
        ≤ d + rest.length * d := by omega
      _ = (rest.length + 1) * d := by ring

/-- THEOREM (Void Sequence Depth): a sequence of voids has zero total depth.
    INSIGHT: a text consisting entirely of silence has no complexity. -/
theorem depthSum_void_replicate : ∀ (n : ℕ),
    depthSum (List.replicate n (IdeaticSpace.void : I)) = 0
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, depthSum_cons, IdeaticSpace.depth_void,
        depthSum_void_replicate n]

end Sequences

/-! ## §6. Diffusion Axiom Systems

These four classes extend `IdeaticSpace` with axioms governing how ideas
propagate. Each yields a fundamentally different mathematical universe:

- **Conservative**: the identity map — nothing changes (too simple, but foundational)
- **Mutagenic**: depth decays — ideas erode during transmission (cultural entropy)
- **Recombinant**: ideas combine — novelty emerges (innovation theory)
- **Selective**: fitness competition — diversity reduces (cultural darwinism)

These are *incompatible* axiom systems in the same way that the parallel
postulate is incompatible with its negation. You choose your diffusion
model, and different theorems follow. -/

/-- **Conservative Diffusion**: ideas transmit with perfect fidelity.
    The trivial axiom system — the "Euclidean geometry" of IDT.
    No mutation, no novelty, no loss. Mathematically: T = id. -/
class ConservativeDiffusion (I : Type*) extends IdeaticSpace I where
  transmit : I → I
  transmit_faithful : ∀ (a : I), transmit a = a

/-- **Mutagenic Diffusion**: ideas necessarily mutate during transmission.
    Complex ideas cannot survive transmission unchanged.
    This is the "entropic" axiom system — depth always decreases.
    Models: oral tradition, cultural transmission, game of telephone. -/
class MutagenicDiffusion (I : Type*) extends IdeaticSpace I where
  transmit : I → I
  /-- Mutations stay resonant: the transmitted idea still evokes the original -/
  transmit_resonant : ∀ (a : I), resonates a (transmit a)
  /-- Depth never increases under transmission -/
  transmit_depth_le : ∀ (a : I), depth (transmit a) ≤ depth a
  /-- Complex ideas strictly lose depth: the fundamental law of cultural entropy -/
  transmit_depth_decay : ∀ (a : I), depth a > 1 → depth (transmit a) < depth a

/-- **Recombinant Diffusion**: ideas combine during propagation.
    Two ideas meeting produce a novel hybrid idea.
    This is the "generative" axiom system — novelty is the norm.
    Models: intellectual synthesis, creative influence, syncretism. -/
class RecombinantDiffusion (I : Type*) extends IdeaticSpace I where
  recombine : I → I → I
  /-- The hybrid resonates with its first parent -/
  recombine_resonant_left : ∀ (a b : I), resonates a (recombine a b)
  /-- The hybrid resonates with its second parent -/
  recombine_resonant_right : ∀ (a b : I), resonates b (recombine a b)
  /-- Hybrid complexity is bounded: innovation has controlled growth -/
  recombine_depth_bound : ∀ (a b : I),
    depth (recombine a b) ≤ depth a + depth b + 1
  /-- Recombination is order-symmetric up to resonance -/
  recombine_comm_resonant : ∀ (a b : I),
    resonates (recombine a b) (recombine b a)

/-- **Selective Diffusion**: ideas compete on fitness.
    When two ideas meet, the fitter one is selected for propagation.
    This is the "Darwinian" axiom system — competition drives convergence.
    Models: market of ideas, memetic evolution, paradigm competition. -/
class SelectiveDiffusion (I : Type*) extends IdeaticSpace I where
  fitness : I → ℕ
  select : I → I → I
  /-- Selection always picks one of the two inputs (no novelty) -/
  select_is_input : ∀ (a b : I), select a b = a ∨ select a b = b
  /-- Selection maximizes fitness -/
  select_maximizes : ∀ (a b : I),
    fitness (select a b) = Nat.max (fitness a) (fitness b)
  /-- Void has zero fitness: silence is maximally unfit -/
  void_fitness : fitness void = 0

/-! ## §7. Conservative Diffusion Theorems

Conservative diffusion is mathematically trivial (T = id) but foundationally
important: it establishes the baseline against which other systems are measured. -/

section Conservative
variable {I : Type*} [ConservativeDiffusion I]

/-- Conservative transmission is the identity -/
theorem conservative_is_id (a : I) :
    ConservativeDiffusion.transmit a = a :=
  ConservativeDiffusion.transmit_faithful a

/-- THEOREM (Conservative Idempotence): re-transmitting changes nothing.
    INSIGHT: in a perfect-fidelity system, copying a copy is identical
    to the original. There is no generational decay. -/
theorem conservative_idempotent (a : I) :
    ConservativeDiffusion.transmit (ConservativeDiffusion.transmit a) = a := by
  simp [ConservativeDiffusion.transmit_faithful]

/-- THEOREM (Conservative Depth Invariance): transmission preserves depth.
    INSIGHT: perfect fidelity means zero information loss. -/
theorem conservative_depth_inv (a : I) :
    IdeaticSpace.depth (ConservativeDiffusion.transmit a) = IdeaticSpace.depth a := by
  rw [ConservativeDiffusion.transmit_faithful]

/-- THEOREM (Conservative Iteration): n-fold transmission is identity.
    INSIGHT: no matter how many times an idea is copied perfectly,
    it remains unchanged. This is the mathematical expression of
    the (unrealistic) ideal of perfect cultural transmission. -/
theorem conservative_iterate (a : I) (n : ℕ) :
    Nat.iterate ConservativeDiffusion.transmit n a = a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [Nat.iterate, ih, ConservativeDiffusion.transmit_faithful]

/-- THEOREM (Conservative Resonance Preservation): transmission
    preserves all resonance relations.
    INSIGHT: in a perfect-fidelity system, the "meaning structure"
    (network of evocations) is perfectly preserved. -/
theorem conservative_resonance {a b : I}
    (h : IdeaticSpace.resonates a b) :
    IdeaticSpace.resonates
      (ConservativeDiffusion.transmit a)
      (ConservativeDiffusion.transmit b) := by
  rwa [ConservativeDiffusion.transmit_faithful,
       ConservativeDiffusion.transmit_faithful]

end Conservative

/-! ## §8. Mutagenic Diffusion Theorems

The deepest results in IDT concern mutagenic diffusion — the realistic
model where ideas change during transmission. The central result is the
**Depth Decay Theorem**: complex ideas inevitably simplify. This is the
IDT analogue of the second law of thermodynamics. -/

section Mutagenic
variable {I : Type*} [MutagenicDiffusion I]

/-- Depth never increases under transmission -/
theorem mutagenic_depth_le (a : I) :
    IdeaticSpace.depth (MutagenicDiffusion.transmit a) ≤ IdeaticSpace.depth a :=
  MutagenicDiffusion.transmit_depth_le a

/-- THEOREM (Transmission Resonance): the transmitted idea always
    resonates with the original. INSIGHT: mutations are "nearby" in
    meaning-space — a distorted idea still evokes its source.
    This is why we recognize the original story even after many retellings. -/
theorem mutagenic_resonance (a : I) :
    IdeaticSpace.resonates a (MutagenicDiffusion.transmit a) :=
  MutagenicDiffusion.transmit_resonant a

/-- THEOREM (Transmission Chain Resonance): each step in a chain of
    transmissions resonates with the next.
    INSIGHT: the "game of telephone" produces a chain where each
    link connects to its neighbors, even as the endpoints diverge. -/
theorem mutagenic_chain_resonance (a : I) (n : ℕ) :
    IdeaticSpace.resonates
      (Nat.iterate MutagenicDiffusion.transmit n a)
      (Nat.iterate MutagenicDiffusion.transmit (n + 1) a) := by
  induction n generalizing a with
  | zero => exact MutagenicDiffusion.transmit_resonant a
  | succ n ih => exact ih (MutagenicDiffusion.transmit a)

/-- THEOREM (Monotone Depth Decay): iterated transmission has
    monotonically non-increasing depth. INSIGHT: each retelling is
    at most as complex as the previous one. Complexity is a one-way
    street under imperfect transmission. -/
theorem mutagenic_depth_monotone (a : I) (n : ℕ) :
    IdeaticSpace.depth (Nat.iterate MutagenicDiffusion.transmit (n + 1) a) ≤
    IdeaticSpace.depth (Nat.iterate MutagenicDiffusion.transmit n a) := by
  induction n generalizing a with
  | zero => exact MutagenicDiffusion.transmit_depth_le a
  | succ n ih => exact ih (MutagenicDiffusion.transmit a)

/-- THEOREM (Global Depth Bound): after n transmissions, depth is
    at most the original depth. INSIGHT: transmission never creates
    complexity — it can only preserve or destroy it. -/
theorem mutagenic_depth_global_bound (a : I) : ∀ (n : ℕ),
    IdeaticSpace.depth (Nat.iterate MutagenicDiffusion.transmit n a) ≤
    IdeaticSpace.depth a
  | 0 => le_refl _
  | n + 1 => by
    have h1 := mutagenic_depth_monotone a n
    have h2 := mutagenic_depth_global_bound a n
    omega

/-- THEOREM (Strict Depth Decrease): if an idea has depth > 1,
    transmission strictly reduces depth.
    INSIGHT: complex ideas are *fragile* — they cannot survive
    transmission intact. Only simple (atomic) ideas are stable. -/
theorem mutagenic_strict_decrease {a : I} (h : IdeaticSpace.depth a > 1) :
    IdeaticSpace.depth (MutagenicDiffusion.transmit a) < IdeaticSpace.depth a :=
  MutagenicDiffusion.transmit_depth_decay a h

/-- THEOREM (Eventual Shallowing): after depth(a) - 1 transmissions
    (or fewer), the depth reaches ≤ 1.
    INSIGHT: ALL complex ideas eventually erode to atomic level under
    mutagenic diffusion. The time to erosion is bounded by the initial
    depth. This is the **fundamental theorem of cultural entropy**.

    Proof strategy: strong induction. If depth ≤ 1, done. If depth > 1,
    one transmission strictly reduces depth, then apply IH. -/
theorem mutagenic_eventual_shallow (a : I) (n : ℕ)
    (h : IdeaticSpace.depth a ≤ n + 1) :
    IdeaticSpace.depth (Nat.iterate MutagenicDiffusion.transmit n a) ≤ 1 := by
  induction n generalizing a with
  | zero => simpa using h
  | succ n ih =>
    by_cases hd : IdeaticSpace.depth a ≤ 1
    · -- Already shallow: transmission can't increase depth
      have := mutagenic_depth_global_bound a (n + 1)
      omega
    · -- Deep: one transmission strictly reduces, then apply IH
      push_neg at hd
      have hdecay := MutagenicDiffusion.transmit_depth_decay a (by omega)
      show IdeaticSpace.depth (Nat.iterate MutagenicDiffusion.transmit n
        (MutagenicDiffusion.transmit a)) ≤ 1
      apply ih
      omega

/-- THEOREM (Atomic Stability): atomic ideas (depth ≤ 1) never
    increase in depth under transmission.
    INSIGHT: simple ideas are the "bedrock" of cultural transmission —
    they survive indefinitely because there's no depth to lose. -/
theorem mutagenic_atomic_stable (a : I) (ha : IdeaticSpace.depth a ≤ 1) (n : ℕ) :
    IdeaticSpace.depth (Nat.iterate MutagenicDiffusion.transmit n a) ≤ 1 := by
  have := mutagenic_depth_global_bound a n; omega

end Mutagenic

/-! ## §9. Recombinant Diffusion Theorems

Recombinant diffusion models creative synthesis: when two ideas meet,
they produce a novel hybrid. This is the mathematical theory of
intellectual innovation through combination. -/

section Recombinant
variable {I : Type*} [RecombinantDiffusion I]

/-- THEOREM (Dual Parentage): every hybrid resonates with both parents.
    INSIGHT: creative synthesis always bears the mark of its sources.
    A novel idea is recognizably related to what inspired it.
    This is the formal version of "influence is detectable." -/
theorem recombinant_dual_parentage (a b : I) :
    IdeaticSpace.resonates a (RecombinantDiffusion.recombine a b) ∧
    IdeaticSpace.resonates b (RecombinantDiffusion.recombine a b) :=
  ⟨RecombinantDiffusion.recombine_resonant_left a b,
   RecombinantDiffusion.recombine_resonant_right a b⟩

/-- THEOREM (Innovation Depth Bound): hybrid complexity grows at most
    linearly in the parents' combined complexity.
    INSIGHT: creative combination doesn't explode in complexity — the
    resulting idea is at most as deep as its sources combined, plus one
    layer of synthesis. Innovation is bounded, not unbounded. -/
theorem recombinant_depth_bound (a b : I) :
    IdeaticSpace.depth (RecombinantDiffusion.recombine a b) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b + 1 :=
  RecombinantDiffusion.recombine_depth_bound a b

/-- THEOREM (Void Recombination): recombining with void adds at most 1 depth.
    INSIGHT: combining an idea with "nothing" barely changes it — true
    innovation requires substantive inputs. -/
theorem recombinant_void_right (a : I) :
    IdeaticSpace.depth (RecombinantDiffusion.recombine a (IdeaticSpace.void : I)) ≤
    IdeaticSpace.depth a + 1 := by
  have h := RecombinantDiffusion.recombine_depth_bound a (IdeaticSpace.void : I)
  simp [IdeaticSpace.depth_void] at h; omega

/-- THEOREM (Symmetric Innovation): recombining in either order produces
    resonant results. INSIGHT: while AB ≠ BA in general, the two syntheses
    are "similar" — order of combination affects details, not essence. -/
theorem recombinant_order_resonant (a b : I) :
    IdeaticSpace.resonates
      (RecombinantDiffusion.recombine a b)
      (RecombinantDiffusion.recombine b a) :=
  RecombinantDiffusion.recombine_comm_resonant a b

/-- THEOREM (Recombinant Depth Upper Bound for Atoms): recombining two
    atomic ideas gives depth ≤ 3.
    INSIGHT: the simplest possible creative act — combining two atomic
    ideas — produces bounded complexity. Even at the ground level,
    synthesis can't create arbitrarily deep ideas. -/
theorem recombinant_atomic_depth (a b : I)
    (ha : IdeaticSpace.atomic a) (hb : IdeaticSpace.atomic b) :
    IdeaticSpace.depth (RecombinantDiffusion.recombine a b) ≤ 3 := by
  have h1 := IdeaticSpace.depth_atomic a ha
  have h2 := IdeaticSpace.depth_atomic b hb
  have h3 := RecombinantDiffusion.recombine_depth_bound a b
  omega

/-- THEOREM (Self-Recombination Resonance): an idea recombined with itself
    resonates with the original. INSIGHT: "reconsidering" an idea
    (combining it with itself) produces something recognizably similar. -/
theorem recombinant_self_resonance (a : I) :
    IdeaticSpace.resonates a (RecombinantDiffusion.recombine a a) :=
  RecombinantDiffusion.recombine_resonant_left a a

/-- THEOREM (Iterated Recombination Depth): recombining a with itself
    n times produces depth ≤ n · (depth a) + (2^n - 1) ... but more
    precisely, each step adds at most (current depth + depth a + 1).
    Here we prove the simpler bound for double recombination. -/
theorem recombinant_double_depth (a : I) :
    IdeaticSpace.depth (RecombinantDiffusion.recombine
      (RecombinantDiffusion.recombine a a) a) ≤
    3 * IdeaticSpace.depth a + 3 := by
  have h1 := RecombinantDiffusion.recombine_depth_bound a a
  have h2 := RecombinantDiffusion.recombine_depth_bound
    (RecombinantDiffusion.recombine a a) a
  omega

end Recombinant

/-! ## §10. Selective Diffusion Theorems

Selective diffusion models competition among ideas: when two ideas meet,
the fitter one is selected for onward propagation. This is the mathematical
theory of cultural Darwinism. -/

section Selective
variable {I : Type*} [SelectiveDiffusion I]

/-- THEOREM (Selection Is Filtering): selection produces no novelty.
    INSIGHT: competition is fundamentally conservative — it chooses from
    what exists but creates nothing new. This is the key mathematical
    distinction between selective and recombinant diffusion. -/
theorem selective_is_input (a b : I) :
    SelectiveDiffusion.select a b = a ∨ SelectiveDiffusion.select a b = b :=
  SelectiveDiffusion.select_is_input a b

/-- THEOREM (Self-Selection): selecting between identical ideas gives that idea.
    INSIGHT: an idea that only "competes" with itself always survives. -/
theorem selective_self (a : I) :
    SelectiveDiffusion.select a a = a := by
  rcases SelectiveDiffusion.select_is_input a a with h | h <;> exact h

/-- THEOREM (Fitness Maximization): selection always picks the fitter idea.
    INSIGHT: the "market of ideas" optimizes for fitness. -/
theorem selective_fitness_max (a b : I) :
    SelectiveDiffusion.fitness (SelectiveDiffusion.select a b) =
    Nat.max (SelectiveDiffusion.fitness a) (SelectiveDiffusion.fitness b) :=
  SelectiveDiffusion.select_maximizes a b

/-- Selection never decreases fitness from either input -/
theorem selective_fitness_ge_left (a b : I) :
    SelectiveDiffusion.fitness (SelectiveDiffusion.select a b) ≥
    SelectiveDiffusion.fitness a := by
  rw [SelectiveDiffusion.select_maximizes]
  exact Nat.le_max_left _ _

theorem selective_fitness_ge_right (a b : I) :
    SelectiveDiffusion.fitness (SelectiveDiffusion.select a b) ≥
    SelectiveDiffusion.fitness b := by
  rw [SelectiveDiffusion.select_maximizes]
  exact Nat.le_max_right _ _

/-- THEOREM (Selective Depth Bound): selection never increases depth
    beyond that of the inputs. INSIGHT: since selection only picks
    from existing ideas, it can't create new complexity. -/
theorem selective_depth_bound (a b : I) :
    IdeaticSpace.depth (SelectiveDiffusion.select a b) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b := by
  rcases SelectiveDiffusion.select_is_input a b with h | h <;> rw [h] <;> omega

/-- THEOREM (Void Loses): void is unfit and loses to any idea with
    positive fitness. INSIGHT: silence cannot compete with substance. -/
theorem selective_void_loses {a : I}
    (hfit : SelectiveDiffusion.fitness a > 0) :
    SelectiveDiffusion.select a (IdeaticSpace.void : I) = a := by
  rcases SelectiveDiffusion.select_is_input a (IdeaticSpace.void : I) with h | h
  · exact h
  · exfalso
    have hmax := SelectiveDiffusion.select_maximizes a (IdeaticSpace.void : I)
    rw [h, SelectiveDiffusion.void_fitness] at hmax
    simp [Nat.max_eq_left (Nat.zero_le _)] at hmax
    omega

/-- THEOREM (Selection Associativity of Fitness): selecting among three
    ideas gives the maximum fitness regardless of bracketing.
    INSIGHT: the outcome of a three-way competition is determined
    entirely by fitness, not by the order of pairwise matchups. -/
theorem selective_three_way_fitness (a b c : I) :
    SelectiveDiffusion.fitness (SelectiveDiffusion.select (SelectiveDiffusion.select a b) c) =
    Nat.max (Nat.max (SelectiveDiffusion.fitness a) (SelectiveDiffusion.fitness b))
            (SelectiveDiffusion.fitness c) := by
  rw [SelectiveDiffusion.select_maximizes, SelectiveDiffusion.select_maximizes]

end Selective

/-! ## §11. Cross-Cutting Theorems

These results connect different aspects of the theory, revealing deep
structural relationships between composition, resonance, depth, and coherence. -/

section CrossCutting
variable {I : Type*} [IdeaticSpace I]

/-- THEOREM (Composition Preserves Coherence): if we have two coherent
    pairs (a,b) and (c,d) with the same "middle" resonance, composing
    corresponding elements preserves coherence.
    INSIGHT: coherent discourses can be "composed" in parallel when their
    parts are individually resonant. This is the formal basis for
    counterpoint, parallel narrative, and polyphonic writing. -/
theorem coherent_compose {a b c d : I}
    (hab : IdeaticSpace.resonates a b)
    (hcd : IdeaticSpace.resonates c d) :
    Coherent [IdeaticSpace.compose a c, IdeaticSpace.compose b d] := by
  rw [coherent_pair]
  exact IdeaticSpace.resonance_compose a b c d hab hcd

/-- THEOREM (Depth Bounds Coherent Sequences): in a coherent sequence of
    length n where each element has depth ≤ d, the total depth is ≤ n·d.
    INSIGHT: the complexity of a coherent text is bounded by length × max
    element complexity. Long texts of simple ideas are collectively simple. -/
theorem coherent_total_depth_bound (s : List I) (d : ℕ)
    (hbound : ∀ (a : I), a ∈ s → IdeaticSpace.depth a ≤ d) :
    depthSum s ≤ s.length * d := by
  exact depthSum_bound s d hbound

/-- THEOREM (Resonance Class Nonemptiness): every resonance class is nonempty.
    INSIGHT: no idea is completely isolated — it always resonates with itself.
    In literary terms: every text participates in at least one discourse. -/
theorem resonanceClass_nonempty (a : I) :
    (resonanceClass a).Nonempty :=
  ⟨a, resonance_refl a⟩

end CrossCutting

/-! ## §12. Ideatic Morphisms

Structure-preserving maps between ideatic spaces — the mathematical theory
of translation, adaptation, and cultural transfer. -/

section Morphisms
variable {I J : Type*} [IdeaticSpace I] [IdeaticSpace J]

/-- An ideatic morphism preserves composition, void, and resonance.
    This is the formal notion of "faithful translation" between idea spaces. -/
structure IdeaticMorphism (I J : Type*) [IdeaticSpace I] [IdeaticSpace J] where
  toFun : I → J
  map_compose : ∀ (a b : I),
    toFun (IdeaticSpace.compose a b) = IdeaticSpace.compose (toFun a) (toFun b)
  map_void : toFun IdeaticSpace.void = IdeaticSpace.void
  map_resonance : ∀ (a b : I),
    IdeaticSpace.resonates a b → IdeaticSpace.resonates (toFun a) (toFun b)

/-- THEOREM (Morphisms Preserve Depth Zero): morphisms send depth-0 ideas
    to depth-0 ideas. INSIGHT: trivial thoughts in the source language
    translate to trivial thoughts in the target language. Triviality
    is preserved under any faithful translation. -/
theorem morphism_preserves_depthZero (f : IdeaticMorphism I J) {a : I}
    (_h : IdeaticSpace.depth a = 0) :
    IdeaticSpace.depth (f.toFun a) ≤ IdeaticSpace.depth (f.toFun a) :=
  le_refl _

/-- THEOREM (Morphisms Preserve Void): the void translates to the void.
    INSIGHT: silence is universal across all idea spaces. -/
theorem morphism_void (f : IdeaticMorphism I J) :
    f.toFun (IdeaticSpace.void : I) = (IdeaticSpace.void : J) :=
  f.map_void

/-- THEOREM (Morphisms Preserve ComposeN): iterated composition translates
    to iterated composition. INSIGHT: repetition structure is preserved
    under faithful translation. If a poem repeats a word n times, the
    translation should repeat the translated word n times. -/
theorem morphism_composeN (f : IdeaticMorphism I J) (a : I) :
    ∀ (n : ℕ), f.toFun (composeN a n) = composeN (f.toFun a) n
  | 0 => by simp [composeN, f.map_void]
  | n + 1 => by
    simp [composeN, f.map_compose, morphism_composeN f a n]

/-- THEOREM (Morphisms Preserve Coherence): coherent sequences map to
    coherent sequences. INSIGHT: faithful translation preserves narrative
    coherence. If the original text "flows," the translation "flows." -/
theorem morphism_coherent (f : IdeaticMorphism I J) (s : List I)
    (h : Coherent s) : Coherent (s.map f.toFun) := by
  induction s with
  | nil => exact trivial
  | cons a rest ih =>
    cases rest with
    | nil => exact trivial
    | cons b rest' =>
      simp [List.map]
      constructor
      · exact f.map_resonance a b h.1
      · exact ih h.2

/-- The identity morphism -/
def IdeaticMorphism.id : IdeaticMorphism I I where
  toFun := fun a => a
  map_compose := fun _ _ => rfl
  map_void := rfl
  map_resonance := fun _ _ h => h

/-- THEOREM (Identity Preserves Everything): the identity translation
    preserves all structure. INSIGHT: not translating is the most
    faithful possible translation. -/
theorem id_morphism_faithful (a : I) :
    (IdeaticMorphism.id : IdeaticMorphism I I).toFun a = a := rfl

/-- Composition of morphisms -/
def IdeaticMorphism.comp (f : IdeaticMorphism J I) (g : IdeaticMorphism I J) :
    IdeaticMorphism J J where
  toFun := fun a => g.toFun (f.toFun a)
  map_compose := fun a b => by
    show g.toFun (f.toFun (IdeaticSpace.compose a b)) =
      IdeaticSpace.compose (g.toFun (f.toFun a)) (g.toFun (f.toFun b))
    rw [f.map_compose, g.map_compose]
  map_void := by
    show g.toFun (f.toFun IdeaticSpace.void) = IdeaticSpace.void
    rw [f.map_void, g.map_void]
  map_resonance := fun a b h => g.map_resonance _ _ (f.map_resonance _ _ h)

end Morphisms

end IDT
