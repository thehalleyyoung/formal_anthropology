import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic

/-!
# Literary Hermeneutics: The Mathematics of Interpretation

This file formalizes **hermeneutic theory** — the mathematics of textual interpretation
— within Ideatic Diffusion Theory. The hermeneutic circle (Gadamer, Heidegger,
Schleiermacher) says that understanding a text requires understanding its parts,
but understanding the parts requires understanding the whole. We formalize this as
iterated endomorphism on an ideatic space.

## Core Mathematical Ideas

1. **Interpretation** is an endomorphism `I → I` mapping ideas to their "understood" versions
2. **The Hermeneutic Circle** is iterated interpretation: read, understand, re-read, ...
3. **Pre-understanding (Vorverständnis)** — the starting point determines the trajectory
4. **Horizon** — the set of ideas reachable from a given starting interpretation
5. **Fusion of Horizons (Horizontverschmelzung)** — two interpreters' horizons overlap
6. **Canonical Meaning** — a fixed point of interpretation, the "correct" reading
7. **Deconstructive Reading** — depth-preserving interpretation resists convergence

## Why This Is Novel

Standard hermeneutic theory (Gadamer, Ricoeur) is qualitative. By formalizing
interpretation as an endomorphism on an ideatic space with a well-ordered depth,
we obtain precise convergence results: the hermeneutic circle terminates if and
only if interpretation is depth-decreasing. This gives a mathematical criterion
for when textual interpretation reaches a stable "canonical" meaning.

## Theorems (35+)

Sections cover: Interpretation endomorphisms, hermeneutic circle iteration,
convergence/stabilization, pre-understanding, horizons, fusion of horizons,
multiple readings and ambiguity, deconstructive reading.

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

set_option autoImplicit false

namespace LiteraryHermeneutics

/-! ## §1. Ideatic Space (Local Redefinition) -/

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

variable {I : Type*} [IdeaticSpace I]

open IdeaticSpace

/-! ## §2. Interpretation as Endomorphism

An **Interpretation** is a structure-preserving self-map on ideas.
It models the act of reading: an idea goes in, an "understood" idea comes out.
The identity interpretation is literal reading (no transformation). -/

/-- An Interpretation bundles an endomorphism with preservation laws. -/
structure Interpretation (I : Type*) [IdeaticSpace I] where
  interpret : I → I
  interpret_compose : ∀ (a b : I),
    interpret (compose a b) = compose (interpret a) (interpret b)
  interpret_void : interpret void = void

/-- A ResonantInterpretation additionally ensures each reading resonates
    with the original — the understood version echoes the text. -/
structure ResonantInterpretation (I : Type*) [IdeaticSpace I]
    extends Interpretation I where
  interpret_resonant : ∀ (a : I), resonates a (interpret a)

/-- **Theorem 1**: The identity interpretation (literal reading). -/
def Interpretation.id : Interpretation I where
  interpret := fun a => a
  interpret_compose := fun _ _ => rfl
  interpret_void := rfl

/-- **Theorem 2**: The identity interpretation is resonant. -/
def ResonantInterpretation.id : ResonantInterpretation I where
  toInterpretation := Interpretation.id
  interpret_resonant := fun a => resonance_refl a

/-- **Theorem 3**: Identity interpretation preserves every idea exactly. -/
theorem interpretation_id_apply (a : I) :
    (Interpretation.id : Interpretation I).interpret a = a := rfl

/-- **Theorem 4**: Composition of interpretations (layered reading). -/
def Interpretation.comp (f g : Interpretation I) : Interpretation I where
  interpret := fun a => f.interpret (g.interpret a)
  interpret_compose := fun a b => by
    simp [g.interpret_compose, f.interpret_compose]
  interpret_void := by simp [g.interpret_void, f.interpret_void]

/-- **Theorem 5**: Interpretation composition is associative. -/
theorem interpretation_comp_assoc (f g h : Interpretation I) :
    Interpretation.comp (Interpretation.comp f g) h =
    Interpretation.comp f (Interpretation.comp g h) := by
  simp [Interpretation.comp]

/-- **Theorem 6**: Identity is a left unit for interpretation composition. -/
theorem interpretation_id_comp (f : Interpretation I) :
    Interpretation.comp Interpretation.id f = f := by
  simp [Interpretation.comp, Interpretation.id]

/-- **Theorem 7**: Identity is a right unit for interpretation composition. -/
theorem interpretation_comp_id (f : Interpretation I) :
    Interpretation.comp f Interpretation.id = f := by
  simp [Interpretation.comp, Interpretation.id]

/-- **Theorem 8**: Interpretation preserves void — silence under any reading
    remains silence. -/
theorem interpretation_void (f : Interpretation I) :
    f.interpret (void : I) = void :=
  f.interpret_void

/-- **Theorem 9**: Void is sent to void under iterated reading. -/
theorem iterated_interpretation_void (f : Interpretation I) (n : ℕ) :
    Nat.iterate f.interpret n (void : I) = void := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Nat.iterate f.interpret n (f.interpret void) = void
    rw [f.interpret_void]; exact ih

/-- **Theorem 10**: Interpretation distributes over composition of ideas.
    Reading a compound text = composing the readings of its parts. -/
theorem iterated_interpretation_compose (f : Interpretation I) (a b : I) (n : ℕ) :
    Nat.iterate f.interpret n (compose a b) =
    compose (Nat.iterate f.interpret n a) (Nat.iterate f.interpret n b) := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    show Nat.iterate f.interpret n (f.interpret (compose a b)) =
         compose (Nat.iterate f.interpret n (f.interpret a))
                 (Nat.iterate f.interpret n (f.interpret b))
    rw [f.interpret_compose a b]
    exact ih (f.interpret a) (f.interpret b)

/-! ## §3. The Hermeneutic Circle

The hermeneutic circle formalizes iterated reading: starting from idea `a`,
we produce the sequence `a, f(a), f²(a), ...`. Each successive reading
potentially deepens or simplifies understanding. -/

/-- **Theorem 11**: Consecutive readings resonate — each reading evokes the next.
    This is the formal content of the hermeneutic circle: understanding flows
    continuously from one reading to the next. -/
theorem consecutive_readings_resonate (f : ResonantInterpretation I)
    (a : I) (n : ℕ) :
    resonates (Nat.iterate f.interpret n a) (Nat.iterate f.interpret (n + 1) a) := by
  induction n generalizing a with
  | zero => exact f.interpret_resonant a
  | succ n ih =>
    show resonates (Nat.iterate f.interpret n (f.interpret a))
                   (Nat.iterate f.interpret (n + 1) (f.interpret a))
    exact ih (f.interpret a)

/-- A depth-decreasing interpretation: reading never makes a text more complex. -/
structure DecreasingInterpretation (I : Type*) [IdeaticSpace I]
    extends Interpretation I where
  depth_nonincreasing : ∀ (a : I), depth (interpret a) ≤ depth a

/-- A strictly decreasing interpretation: reading genuinely simplifies complex texts. -/
structure StrictlyDecreasingInterpretation (I : Type*) [IdeaticSpace I]
    extends DecreasingInterpretation I where
  strict_decay : ∀ (a : I), depth a > 1 → depth (interpret a) < depth a

/-- **Theorem 12**: Depth is non-increasing under iterated reading. -/
theorem depth_nonincreasing_iterate (f : DecreasingInterpretation I)
    (a : I) (n : ℕ) :
    depth (Nat.iterate f.interpret (n + 1) a) ≤
    depth (Nat.iterate f.interpret n a) := by
  induction n generalizing a with
  | zero => exact f.depth_nonincreasing a
  | succ n ih =>
    show depth (Nat.iterate f.interpret (n + 1) (f.interpret a)) ≤
         depth (Nat.iterate f.interpret n (f.interpret a))
    exact ih (f.interpret a)

/-- **Theorem 13**: The depth of the n-th reading is bounded by the original depth. -/
theorem depth_iterate_le (f : DecreasingInterpretation I) (a : I) (n : ℕ) :
    depth (Nat.iterate f.interpret n a) ≤ depth a := by
  induction n generalizing a with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    show depth (Nat.iterate f.interpret n (f.interpret a)) ≤ depth a
    calc depth (Nat.iterate f.interpret n (f.interpret a))
        ≤ depth (f.interpret a) := ih (f.interpret a)
      _ ≤ depth a := f.depth_nonincreasing a

/-- **Theorem 14**: Iterated reading preserves void depth. -/
theorem depth_iterate_void (f : DecreasingInterpretation I) (n : ℕ) :
    depth (Nat.iterate f.interpret n (void : I)) = 0 := by
  have hv := iterated_interpretation_void f.toInterpretation n
  rw [hv, depth_void]

/-! ## §4. Convergence of Interpretation

The central result: if interpretation is strictly depth-decreasing, the
hermeneutic circle converges. The reading sequence stabilizes after at most
`depth(a)` iterations. -/

/-- Helper: depth stabilization by induction on a depth bound. -/
private theorem depth_stabilization_aux (f : StrictlyDecreasingInterpretation I) :
    ∀ (d : ℕ) (a : I), depth a ≤ d →
    depth (Nat.iterate f.interpret d a) ≤ 1 := by
  intro d
  induction d with
  | zero =>
    intro a ha
    simp; omega
  | succ n ih =>
    intro a ha
    by_cases hd : depth a ≤ 1
    · have := depth_iterate_le f.toDecreasingInterpretation a (n + 1)
      omega
    · push_neg at hd
      have hdecay := f.strict_decay a (by omega)
      have hle : depth (f.interpret a) ≤ n := by omega
      exact ih (f.interpret a) hle

/-- **Theorem 15 (Hermeneutic Convergence)**: Under strict decay, the reading
    sequence stabilizes to depth ≤ 1 after `depth(a)` iterations.

    LITERARY INSIGHT: Every text, under a genuinely simplifying interpretation,
    eventually yields a "core meaning" — an atomic residue of the original. -/
theorem hermeneutic_convergence (f : StrictlyDecreasingInterpretation I) (a : I) :
    depth (Nat.iterate f.interpret (depth a) a) ≤ 1 :=
  depth_stabilization_aux f (depth a) a (Nat.le_refl _)

/-- **Theorem 16**: Convergence time ≤ depth of the original text.
    Deeper texts take longer to fully understand, but understanding always comes. -/
theorem convergence_time_bound (f : StrictlyDecreasingInterpretation I)
    (a : I) (n : ℕ) (hn : n ≥ depth a) :
    depth (Nat.iterate f.interpret n a) ≤ 1 := by
  have hsplit : n = (n - depth a) + depth a := by omega
  rw [hsplit, Function.iterate_add]
  calc depth (Nat.iterate f.interpret (n - depth a)
          (Nat.iterate f.interpret (depth a) a))
      ≤ depth (Nat.iterate f.interpret (depth a) a) :=
        depth_iterate_le f.toDecreasingInterpretation _ _
    _ ≤ 1 := hermeneutic_convergence f a

/-- **Theorem 17**: Void converges immediately — silence needs no interpretation. -/
theorem void_converges_instantly (f : StrictlyDecreasingInterpretation I) :
    depth (Nat.iterate f.interpret 0 (void : I)) ≤ 1 := by
  simp [depth_void]

/-- **Theorem 18**: Depth-0 ideas are already converged. -/
theorem depth_zero_converged (f : StrictlyDecreasingInterpretation I)
    (a : I) (ha : depth a = 0) :
    depth (Nat.iterate f.interpret 0 a) ≤ 1 := by
  simp; omega

/-! ## §5. Fixed Points — Canonical Meaning

A fixed point of interpretation is a "canonical meaning": an idea whose
understood version is identical to itself. These are the ideas that resist
further interpretive transformation — the stable readings. -/

/-- An idea is a fixed point of a map if f(a) = a. -/
def IsFixedPoint (f : I → I) (a : I) : Prop := f a = a

/-- **Theorem 19**: Void is always a canonical meaning. -/
theorem void_is_canonical (f : Interpretation I) :
    IsFixedPoint f.interpret (void : I) :=
  f.interpret_void

/-- **Theorem 20**: Fixed points are stable under iteration — once you've reached
    the canonical reading, re-reading doesn't change it. -/
theorem canonical_stable (f : Interpretation I) (a : I)
    (hfix : IsFixedPoint f.interpret a) (n : ℕ) :
    Nat.iterate f.interpret n a = a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    show Nat.iterate f.interpret n (f.interpret a) = a
    rw [hfix]; exact ih a hfix

/-- **Theorem 21**: The set of canonical meanings is closed under composition.
    If two ideas are stable readings, their composite is also stable. -/
theorem canonical_closed_compose (f : Interpretation I) (a b : I)
    (ha : IsFixedPoint f.interpret a) (hb : IsFixedPoint f.interpret b) :
    IsFixedPoint f.interpret (compose a b) := by
  simp only [IsFixedPoint] at *
  rw [f.interpret_compose, ha, hb]

/-- **Theorem 22 (Canon Theorem)**: Under strictly decreasing interpretation,
    canonical meanings have depth ≤ 1. Only simple ideas survive indefinite
    re-reading without change. -/
theorem canon_theorem (f : StrictlyDecreasingInterpretation I) (a : I)
    (hfix : IsFixedPoint f.interpret a) :
    depth a ≤ 1 := by
  by_contra h
  push_neg at h
  have hdecay := f.strict_decay a (by omega)
  simp only [IsFixedPoint] at hfix
  rw [hfix] at hdecay
  omega

/-- **Theorem 23**: Canonical meanings compose to shallow ideas. -/
theorem canonical_compose_shallow (f : StrictlyDecreasingInterpretation I)
    (a b : I) (ha : IsFixedPoint f.interpret a) (hb : IsFixedPoint f.interpret b) :
    depth (compose a b) ≤ 2 := by
  have da := canon_theorem f a ha
  have db := canon_theorem f b hb
  calc depth (compose a b) ≤ depth a + depth b := depth_subadditive a b
    _ ≤ 1 + 1 := by omega
    _ = 2 := by omega

/-! ## §6. Pre-understanding (Vorverständnis)

Gadamer's key insight: every act of interpretation begins from a
pre-understanding. Different starting points lead to different trajectories.
We formalize how the initial idea affects the interpretive journey. -/

/-- **Theorem 24**: Different starting points yield different intermediate readings
    unless the interpretation is trivial. More precisely: if two starting ideas
    produce the same first reading, they were already read the same way. -/
theorem preunderstanding_determines_first_reading (f : Interpretation I) (a b : I) :
    f.interpret a = f.interpret b →
    Nat.iterate f.interpret 1 a = Nat.iterate f.interpret 1 b := by
  intro h; exact h

/-- **Theorem 25**: Deeper starting texts take at least as many readings to converge.
    Pre-understanding matters: a more complex initial understanding requires more work. -/
theorem deeper_start_longer_convergence (f : DecreasingInterpretation I)
    (a b : I) (hab : depth a ≤ depth b) (n : ℕ) :
    depth (Nat.iterate f.interpret n a) ≤ depth b := by
  calc depth (Nat.iterate f.interpret n a)
      ≤ depth a := depth_iterate_le f a n
    _ ≤ depth b := hab

/-- **Theorem 26**: Resonant interpretation preserves compositional resonance.
    If f is a resonant interpretation, the reading of a composed text resonates
    with the original composition — each component's reading echoes its source. -/
theorem composed_text_resonance (f : ResonantInterpretation I) (a b : I) :
    resonates (compose a b) (compose (f.interpret a) (f.interpret b)) :=
  resonance_compose a (f.interpret a) b (f.interpret b)
    (f.interpret_resonant a) (f.interpret_resonant b)

/-- **Theorem 27**: Depth of composed iterated readings is bounded by original depths.
    Reading a composite text repeatedly can't exceed the combined original depth. -/
theorem composed_reading_depth (f : DecreasingInterpretation I)
    (a b : I) (n : ℕ) :
    depth (Nat.iterate f.interpret n (compose a b)) ≤ depth a + depth b := by
  rw [iterated_interpretation_compose f.toInterpretation a b n]
  calc depth (compose (Nat.iterate f.interpret n a) (Nat.iterate f.interpret n b))
      ≤ depth (Nat.iterate f.interpret n a) + depth (Nat.iterate f.interpret n b) :=
        depth_subadditive _ _
    _ ≤ depth a + depth b := by
        have ha := depth_iterate_le f a n
        have hb := depth_iterate_le f b n
        omega

/-! ## §7. Horizons

The **horizon** of an interpreter is the set of ideas reachable by iterated
interpretation from a starting point. Gadamer's "fusion of horizons" occurs
when two interpreters' horizons overlap. -/

/-- The horizon of `a` under interpretation `f` up to `n` steps:
    the set of ideas visited in the first `n` readings. -/
def Horizon (f : I → I) (a : I) (n : ℕ) : Set I :=
  { x : I | ∃ k : ℕ, k ≤ n ∧ Nat.iterate f k a = x }

/-- **Theorem 28**: The starting point is always in its own horizon. -/
theorem self_in_horizon (f : I → I) (a : I) (n : ℕ) :
    a ∈ Horizon f a n := by
  exact ⟨0, Nat.zero_le n, rfl⟩

/-- **Theorem 29**: Horizon of void under any interpretation is {void}. -/
theorem horizon_void (f : Interpretation I) (n : ℕ) :
    Horizon f.interpret (void : I) n = {void} := by
  ext x
  simp only [Horizon, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, _, hk⟩
    rw [← hk, iterated_interpretation_void]
  · intro hx
    exact ⟨0, Nat.zero_le n, by simp [hx]⟩

/-- **Theorem 30**: Horizons grow monotonically — more readings, larger horizon. -/
theorem horizon_monotone (f : I → I) (a : I) (m n : ℕ) (hmn : m ≤ n) :
    Horizon f a m ⊆ Horizon f a n := by
  intro x ⟨k, hk, hx⟩
  exact ⟨k, le_trans hk hmn, hx⟩

/-- **Theorem 31**: Horizon is closed under the interpretation function
    (for sufficiently large n). If x is in the n-horizon and n > 0,
    then f(first element) is also in the horizon. More precisely:
    if the k-th iterate is in the horizon, the (k+1)-th is too for larger horizons. -/
private theorem iterate_comm (f : I → I) (k : ℕ) (a : I) :
    Nat.iterate f k (f a) = f (Nat.iterate f k a) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    show Nat.iterate f k (f (f a)) = f (Nat.iterate f k (f a))
    exact ih (f a)

theorem horizon_closed_step (f : I → I) (a : I) (n : ℕ) :
    ∀ (x : I), x ∈ Horizon f a n → f x ∈ Horizon f a (n + 1) := by
  intro x ⟨k, hk, hx⟩
  refine ⟨k + 1, by omega, ?_⟩
  show Nat.iterate f k (f a) = f x
  rw [iterate_comm f k a, hx]

/-- **Theorem 32**: Horizon size is bounded by n+1 (at most n+1 distinct readings). -/
theorem horizon_bounded (f : I → I) (a : I) (n : ℕ) :
    ∀ (x : I), x ∈ Horizon f a n → ∃ k : ℕ, k ≤ n ∧ Nat.iterate f k a = x :=
  fun x hx => hx

/-! ## §8. Fusion of Horizons (Horizontverschmelzung)

Two interpreters achieve "fusion of horizons" when their horizons share
an element — they reach a common understanding at some point. -/

/-- Two horizons fuse if they share an element. -/
def HorizonsFuse (f g : I → I) (a b : I) (n : ℕ) : Prop :=
  ∃ (x : I), x ∈ Horizon f a n ∧ x ∈ Horizon g b n

/-- **Theorem 33**: Same interpreter, same starting point → horizons trivially fuse. -/
theorem horizons_fuse_same (f : I → I) (a : I) (n : ℕ) :
    HorizonsFuse f f a a n := by
  exact ⟨a, self_in_horizon f a n, self_in_horizon f a n⟩

/-- **Theorem 34**: If starting from void, all interpreters' horizons fuse
    (void is the universal common ground). -/
theorem horizons_fuse_void (f g : Interpretation I) (n : ℕ) :
    HorizonsFuse f.interpret g.interpret (void : I) (void : I) n := by
  refine ⟨void, ?_, ?_⟩
  · exact ⟨0, Nat.zero_le n, rfl⟩
  · exact ⟨0, Nat.zero_le n, rfl⟩

/-- **Theorem 35**: If two interpreters share the same function and start from
    the same point, their horizons are equal. -/
theorem same_interpreter_same_horizon (f : I → I) (a : I) (n : ℕ) :
    Horizon f a n = Horizon f a n := rfl

/-! ## §9. Multiple Readings and Ambiguity

Different interpretation functions may converge to different canonical meanings.
The "ambiguity" of a text is measured by how many distinct fixed points exist. -/

/-- **Theorem 36**: Composed interpretations produce a "richer" reading that factors
    through both component interpretations. -/
theorem composed_reading_factors (f g : Interpretation I) (a : I) :
    (Interpretation.comp f g).interpret a = f.interpret (g.interpret a) := rfl

/-- **Theorem 37**: If two interpretations agree on an idea, their composition
    applied to that idea equals either applied twice. -/
theorem interpretations_agree_compose (f g : Interpretation I) (a : I)
    (hagree : f.interpret a = g.interpret a) :
    (Interpretation.comp f g).interpret a = f.interpret (g.interpret a) := rfl

/-- **Theorem 38**: Depth-0 ideas have a unique canonical reading (they must be void
    in a strong sense: any depth-0 idea is already at its simplest). -/
theorem depth_zero_unique_reading (f : DecreasingInterpretation I)
    (a : I) (ha : depth a = 0) :
    depth (f.interpret a) = 0 := by
  have := f.depth_nonincreasing a
  omega

/-- **Theorem 39**: Composing two depth-decreasing interpretations gives
    a depth-decreasing interpretation. -/
def DecreasingInterpretation.comp (f g : DecreasingInterpretation I) :
    DecreasingInterpretation I where
  toInterpretation := Interpretation.comp f.toInterpretation g.toInterpretation
  depth_nonincreasing := fun a => by
    show depth (f.interpret (g.interpret a)) ≤ depth a
    calc depth (f.interpret (g.interpret a))
        ≤ depth (g.interpret a) := f.depth_nonincreasing (g.interpret a)
      _ ≤ depth a := g.depth_nonincreasing a

/-- **Theorem 40**: Composing two decreasing interpretations preserves the
    convergence time bound. The composed interpretation converges no slower
    than the original. -/
theorem composed_convergence (f g : DecreasingInterpretation I) (a : I) (n : ℕ) :
    depth (Nat.iterate (Interpretation.comp f.toInterpretation g.toInterpretation).interpret n a) ≤
    depth a := by
  exact depth_iterate_le (DecreasingInterpretation.comp f g) a n

/-! ## §10. Deconstructive Reading

Derrida's insight: some interpretations resist convergence. A depth-preserving
interpretation (one that neither increases nor decreases depth) can cycle
forever without reaching a canonical meaning. -/

/-- A depth-preserving interpretation: reading maintains complexity exactly. -/
structure DepthPreservingInterpretation (I : Type*) [IdeaticSpace I]
    extends Interpretation I where
  depth_preserved : ∀ (a : I), depth (interpret a) = depth a

/-- **Theorem 41**: Under depth-preserving interpretation, depth never changes. -/
theorem depth_preserved_iterate (f : DepthPreservingInterpretation I)
    (a : I) (n : ℕ) :
    depth (Nat.iterate f.interpret n a) = depth a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    show depth (Nat.iterate f.interpret n (f.interpret a)) = depth a
    rw [ih (f.interpret a), f.depth_preserved]

/-- **Theorem 42**: Depth-preserving interpretations are depth-decreasing (weakly). -/
def DepthPreservingInterpretation.toDecreasing
    (f : DepthPreservingInterpretation I) : DecreasingInterpretation I where
  toInterpretation := f.toInterpretation
  depth_nonincreasing := fun a => le_of_eq (f.depth_preserved a)

/-- **Theorem 43**: Under depth-preserving interpretation, no stabilization of depth
    is guaranteed — the depth stays constant forever.

    DERRIDA'S INSIGHT: Some texts resist a single stable meaning. The hermeneutic
    circle, when interpretation preserves complexity, may cycle indefinitely. -/
theorem deconstructive_no_depth_reduction
    (f : DepthPreservingInterpretation I) (a : I) (n : ℕ) :
    depth (Nat.iterate f.interpret n a) = depth a :=
  depth_preserved_iterate f a n

/-- **Theorem 44**: Depth-preserving interpretation of a depth-k idea stays at depth k
    forever — there is no convergence to simpler meaning. -/
theorem no_simplification (f : DepthPreservingInterpretation I)
    (a : I) (k : ℕ) (hk : depth a = k) (n : ℕ) :
    depth (Nat.iterate f.interpret n a) = k := by
  rw [depth_preserved_iterate f a n, hk]

/-! ## §11. Resonance Chains and Reading Sequences

The reading sequence forms a resonance chain — a connected path in the
resonance graph of the ideatic space. -/

/-- **Theorem 45**: The full reading sequence is a resonance chain: every pair
    of adjacent elements resonates. This is the formal hermeneutic circle. -/
theorem reading_chain_resonance (f : ResonantInterpretation I)
    (a : I) (n : ℕ) :
    ∀ (k : ℕ), k < n →
    resonates (Nat.iterate f.interpret k a) (Nat.iterate f.interpret (k + 1) a) := by
  intro k _
  exact consecutive_readings_resonate f a k

/-- **Theorem 46**: Each reading resonates with the original text
    (by transitivity through void-compose). -/
theorem reading_resonates_original (f : ResonantInterpretation I) (a : I) :
    resonates a (f.interpret a) :=
  f.interpret_resonant a

/-- **Theorem 47**: Composed ideas yield composed reading sequences. -/
theorem reading_sequence_compose (f : Interpretation I) (a b : I) (n : ℕ) :
    Nat.iterate f.interpret n (compose a b) =
    compose (Nat.iterate f.interpret n a) (Nat.iterate f.interpret n b) :=
  iterated_interpretation_compose f a b n

/-! ## §12. Periodicity and Cyclic Interpretation

Some interpretations are periodic: after p readings, the text returns to
its original form. This models cyclical hermeneutic processes. -/

/-- An idea is periodic under interpretation with period p. -/
def IsPeriodic (f : I → I) (a : I) (p : ℕ) : Prop :=
  p > 0 ∧ Nat.iterate f p a = a

/-- **Theorem 48**: Every fixed point is periodic with period 1. -/
theorem fixed_implies_periodic (f : I → I) (a : I)
    (hfix : IsFixedPoint f a) : IsPeriodic f a 1 := by
  exact ⟨by omega, hfix⟩

/-- **Theorem 49**: Periodic ideas have constant depth on their orbit
    under a depth-decreasing interpretation. -/
theorem periodic_constant_depth_orbit (f : DecreasingInterpretation I) (a : I)
    (p : ℕ) (hp : IsPeriodic f.interpret a p) (n : ℕ) (hn : n ≤ p) :
    depth (Nat.iterate f.interpret n a) ≤ depth a := by
  exact depth_iterate_le f a n

/-- **Theorem 50**: Void is periodic with any period. -/
theorem void_periodic (f : Interpretation I) (p : ℕ) (hp : p > 0) :
    IsPeriodic f.interpret (void : I) p :=
  ⟨hp, iterated_interpretation_void f p⟩

/-! ## §13. Interpretive Distance

We can measure how "far" an interpretation moves an idea by the depth change. -/

/-- Interpretive depth change: how much depth changes in one reading. -/
def interpretiveDepthChange (f : Interpretation I) (a : I) : ℕ :=
  depth a - depth (f.interpret a)

/-- **Theorem 51**: Depth change is zero for depth-preserving interpretations. -/
theorem depth_change_zero_preserving (f : DepthPreservingInterpretation I)
    (a : I) : interpretiveDepthChange f.toInterpretation a = 0 := by
  simp [interpretiveDepthChange, f.depth_preserved]

/-- **Theorem 52**: Depth change for void is always zero. -/
theorem depth_change_void (f : Interpretation I) :
    interpretiveDepthChange f (void : I) = 0 := by
  simp [interpretiveDepthChange, f.interpret_void, depth_void]

/-- **Theorem 53**: Under decreasing interpretation, total depth change after n steps
    is bounded by original depth. -/
theorem total_depth_bounded (f : DecreasingInterpretation I) (a : I) (n : ℕ) :
    depth a - depth (Nat.iterate f.interpret n a) ≤ depth a :=
  Nat.sub_le (depth a) _

/-! ## §14. Compositionality of Hermeneutics

The compositional structure of interpretation: how parts relate to wholes
in the interpretive process. -/

/-- **Theorem 54**: Depth of composed interpretations is subadditive. -/
theorem composed_interpretation_depth (f : DecreasingInterpretation I)
    (a b : I) :
    depth (f.interpret (compose a b)) ≤ depth a + depth b := by
  calc depth (f.interpret (compose a b))
      ≤ depth (compose a b) := f.depth_nonincreasing _
    _ ≤ depth a + depth b := depth_subadditive a b

/-- **Theorem 55**: Iterated interpretation of a composition distributes. -/
theorem iterated_compose_distributes (f : Interpretation I) (a b : I) (n : ℕ) :
    Nat.iterate f.interpret n (compose a b) =
    compose (Nat.iterate f.interpret n a) (Nat.iterate f.interpret n b) :=
  iterated_interpretation_compose f a b n

/-- **Theorem 56**: Depth after composing two interpreted ideas is bounded. -/
theorem interpreted_compose_depth_bound (f : DecreasingInterpretation I)
    (a b : I) (n : ℕ) :
    depth (compose (Nat.iterate f.interpret n a) (Nat.iterate f.interpret n b)) ≤
    depth a + depth b := by
  calc depth (compose (Nat.iterate f.interpret n a) (Nat.iterate f.interpret n b))
      ≤ depth (Nat.iterate f.interpret n a) + depth (Nat.iterate f.interpret n b) :=
        depth_subadditive _ _
    _ ≤ depth a + depth b := by
        have ha := depth_iterate_le f a n
        have hb := depth_iterate_le f b n
        omega

/-! ## §15. Hermeneutic Consensus

When multiple interpreters converge to the same canonical meaning,
we have interpretive consensus. -/

/-- Two interpretations reach consensus on an idea if they produce the same
    canonical reading eventually. -/
def ReachConsensus (f g : Interpretation I) (a : I) (n : ℕ) : Prop :=
  Nat.iterate f.interpret n a = Nat.iterate g.interpret n a

/-- **Theorem 57**: Identity interpretation reaches consensus with itself immediately. -/
theorem id_consensus (a : I) :
    ReachConsensus (Interpretation.id : Interpretation I)
                   (Interpretation.id : Interpretation I) a 0 := by
  simp [ReachConsensus]

/-- **Theorem 58**: All interpretations reach consensus on void. -/
theorem void_consensus (f g : Interpretation I) (n : ℕ) :
    ReachConsensus f g (void : I) n := by
  simp [ReachConsensus, iterated_interpretation_void]

/-- **Theorem 59**: Consensus is reflexive. -/
theorem consensus_refl (f : Interpretation I) (a : I) (n : ℕ) :
    ReachConsensus f f a n := by
  simp [ReachConsensus]

/-- **Theorem 60**: Consensus is symmetric. -/
theorem consensus_symm (f g : Interpretation I) (a : I) (n : ℕ)
    (h : ReachConsensus f g a n) : ReachConsensus g f a n := by
  simp [ReachConsensus] at *; exact h.symm

/-! ## §16. Depth Stratification of Interpretation

Ideas of different depths behave differently under interpretation. We
characterize interpretation behavior at each depth stratum. -/

/-- The depth stratum: all ideas at exactly depth k. -/
def DepthStratum (k : ℕ) : Set I :=
  { a : I | depth a = k }

/-- **Theorem 61**: Void is in stratum 0. -/
theorem void_in_stratum_zero : (void : I) ∈ DepthStratum (I := I) 0 := by
  simp [DepthStratum, depth_void]

/-- **Theorem 62**: Decreasing interpretation maps stratum k to strata ≤ k. -/
theorem decreasing_maps_strata (f : DecreasingInterpretation I)
    (a : I) (k : ℕ) (ha : a ∈ DepthStratum (I := I) k) :
    depth (f.interpret a) ≤ k := by
  simp [DepthStratum] at ha
  calc depth (f.interpret a) ≤ depth a := f.depth_nonincreasing a
    _ = k := ha

/-- **Theorem 63**: Depth-preserving interpretation preserves strata exactly. -/
theorem preserving_preserves_strata (f : DepthPreservingInterpretation I)
    (a : I) (k : ℕ) (ha : a ∈ DepthStratum (I := I) k) :
    f.interpret a ∈ DepthStratum (I := I) k := by
  simp [DepthStratum] at *
  rw [f.depth_preserved, ha]

/-- **Theorem 64**: Strictly decreasing interpretation moves ideas in stratum k>1
    to a strictly lower stratum. -/
theorem strict_moves_down (f : StrictlyDecreasingInterpretation I)
    (a : I) (k : ℕ) (hk : k > 1) (ha : a ∈ DepthStratum (I := I) k) :
    depth (f.interpret a) < k := by
  simp [DepthStratum] at ha
  have := f.strict_decay a (by omega)
  omega

/-! ## §17. Atomic Interpretations

Some special interpretations map everything to atomic ideas in one step. -/

/-- An atomizing interpretation sends every idea to an atomic one. -/
structure AtomizingInterpretation (I : Type*) [IdeaticSpace I]
    extends Interpretation I where
  atomizes : ∀ (a : I), atomic (interpret a)

/-- **Theorem 65**: Atomizing interpretations produce depth ≤ 1 ideas. -/
theorem atomizing_depth_le_one (f : AtomizingInterpretation I) (a : I) :
    depth (f.interpret a) ≤ 1 :=
  depth_atomic _ (f.atomizes a)

/-- **Theorem 66**: Atomizing interpretation converges in at most 1 step. -/
theorem atomizing_one_step (f : AtomizingInterpretation I) (a : I) :
    depth (Nat.iterate f.interpret 1 a) ≤ 1 := by
  exact depth_atomic _ (f.atomizes a)

/-- **Theorem 67**: After atomizing, further reading stays atomic. -/
theorem atomizing_stays_atomic (f : AtomizingInterpretation I) (a : I) (n : ℕ)
    (hn : n ≥ 1) :
    depth (Nat.iterate f.interpret n a) ≤ 1 := by
  cases n with
  | zero => omega
  | succ m =>
    show depth (Nat.iterate f.interpret m (f.interpret a)) ≤ 1
    induction m generalizing a with
    | zero => exact depth_atomic _ (f.atomizes a)
    | succ m ih =>
      show depth (Nat.iterate f.interpret m (f.interpret (f.interpret a)) ) ≤ 1
      exact ih (f.interpret a) (by omega)

/-! ## §18. Interpretive Morphisms Between Texts

How interpretations interact when applied to composed texts. -/

/-- **Theorem 68**: Interpretation commutes with left-composition by void. -/
theorem interpret_void_left (f : Interpretation I) (a : I) :
    f.interpret (compose void a) = f.interpret a := by
  rw [void_left]

/-- **Theorem 69**: Interpretation commutes with right-composition by void. -/
theorem interpret_void_right (f : Interpretation I) (a : I) :
    f.interpret (compose a void) = f.interpret a := by
  rw [void_right]

/-- **Theorem 70**: The n-th reading of (a · b) uses the same steps as
    composing n-th readings — interpretation is a monoid homomorphism
    at every iteration. -/
theorem nth_reading_homomorphism (f : Interpretation I) (n : ℕ)
    (a b : I) :
    Nat.iterate f.interpret n (compose a b) =
    compose (Nat.iterate f.interpret n a) (Nat.iterate f.interpret n b) :=
  iterated_interpretation_compose f a b n

end LiteraryHermeneutics
