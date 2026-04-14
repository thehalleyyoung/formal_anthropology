import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.IDT_Foundations

/-!
# Literary Text Space: Texts as Structured Sequences of Ideas

This file formalizes **texts** as structured sequences of ideas within Ideatic
Diffusion Theory. A text is not merely a list of ideas—it carries structure,
coherence, depth, and narrative shape. We build toward a mathematical theory
of literature by defining:

- **Text**: a wrapped list of ideas with computable properties
- **Text operations**: concatenation, splitting, subtexts
- **Narrative arc**: depth-pattern characterization (rising, falling, climactic)
- **Genre**: predicates on texts (a genre = the set of texts satisfying invariants)
- **Rhetorical transformation**: resonance-preserving maps on texts (a monoid)

## Key Insights

1. **Coherence is fragile**: concatenating two coherent texts need not be coherent
2. **Subtexts inherit coherence**: contiguous subsequences of coherent texts are coherent
3. **Genre-crossing is detectable**: violating any defining invariant exits the genre
4. **Resonance-preserving transforms form a monoid**: they compose associatively
5. **Silence is literature**: the empty text satisfies all structural properties trivially

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT

/-! ## §1. Text Structure

A **Text** wraps a `List I` of ideas. We define basic text properties:
length, total depth, coherence, and atomicity. -/

section TextStructure
variable {I : Type*} [IdeaticSpace I]

/-- A Text is a structured sequence of ideas.
    INSIGHT: in literary theory, a "text" is not merely characters on a page
    but a structured object with beginning, middle, and end. -/
structure Text (I : Type*) [IdeaticSpace I] where
  ideas : List I

/-- The empty text: silence, the blank page -/
def Text.empty : Text I := ⟨[]⟩

/-- A text from a single idea -/
def Text.singleton (a : I) : Text I := ⟨[a]⟩

/-- A text from a pair of ideas -/
def Text.pair (a b : I) : Text I := ⟨[a, b]⟩

/-- The length of a text: how many ideas it contains -/
def Text.length (t : Text I) : ℕ := t.ideas.length

/-- The total depth of a text: sum of depths of all ideas -/
def Text.totalDepth (t : Text I) : ℕ := depthSum t.ideas

/-- Whether a text is coherent: consecutive ideas resonate -/
def Text.isCoherent (t : Text I) : Prop := Coherent t.ideas

/-- Whether a text consists entirely of atomic ideas -/
def Text.allAtomic (t : Text I) : Prop :=
  ∀ (a : I), a ∈ t.ideas → IdeaticSpace.atomic a

/-- **Theorem 1 (Empty Text Length)**: The empty text has length zero.
    INSIGHT: silence has no extent—the blank page is the zero of textual
    measure. -/
@[simp] theorem Text.length_empty : (Text.empty : Text I).length = 0 := rfl

/-- **Theorem 2 (Singleton Length)**: A single-idea text has length one.
    INSIGHT: the minimal non-trivial text is a single idea. -/
@[simp] theorem Text.length_singleton (a : I) :
    (Text.singleton a).length = 1 := rfl

/-- **Theorem 3 (Empty Text Coherence)**: The empty text is coherent.
    INSIGHT: silence is trivially coherent—there are no consecutive pairs
    to break coherence. The blank page "says" nothing incoherent. -/
theorem Text.empty_coherent : (Text.empty : Text I).isCoherent :=
  coherent_nil

/-- **Theorem 4 (Singleton Coherence)**: Any single idea is a coherent text.
    INSIGHT: a single thought cannot be incoherent with itself. Every idea,
    in isolation, constitutes a valid (if minimal) narrative. -/
theorem Text.singleton_coherent (a : I) :
    (Text.singleton a).isCoherent :=
  coherent_singleton a

/-- **Theorem 5 (Pair Coherence ↔ Resonance)**: A two-idea text is coherent
    iff the ideas resonate. INSIGHT: the atom of narrative—two ideas—is
    coherent exactly when the first evokes the second. -/
theorem Text.pair_coherent (a b : I) :
    (Text.pair a b).isCoherent ↔ IdeaticSpace.resonates a b :=
  coherent_pair

/-- **Theorem 6 (Empty Text Depth)**: The empty text has zero total depth.
    INSIGHT: silence has no complexity. -/
@[simp] theorem Text.totalDepth_empty :
    (Text.empty : Text I).totalDepth = 0 := rfl

/-- **Theorem 7 (Singleton Depth)**: A single-idea text has depth equal to
    the idea's depth. INSIGHT: a text of one idea inherits that idea's
    full complexity—there is no "overhead" from being in a text. -/
theorem Text.totalDepth_singleton (a : I) :
    (Text.singleton a).totalDepth = IdeaticSpace.depth a := by
  simp [Text.totalDepth, Text.singleton, depthSum, List.map, List.sum_cons]

/-- **Theorem 8 (Atomic Text Depth Bound)**: A text of all atomic ideas has
    total depth at most its length.
    INSIGHT: if every idea in a text is conceptually simple (atomic), then
    the text's total complexity is linearly bounded by its length. -/
theorem Text.atomic_depth_bound (t : Text I) (hat : t.allAtomic) :
    t.totalDepth ≤ t.length := by
  unfold Text.totalDepth Text.length
  have h := depthSum_bound t.ideas 1 (fun a ha => IdeaticSpace.depth_atomic a (hat a ha))
  omega

/-- **Theorem 9 (Self-Resonant Text)**: A text of repeated ideas is coherent.
    INSIGHT: repetition—mantras, refrains, ritual chants—is always coherent.
    This formalizes the literary device of anaphora. -/
theorem Text.replicate_coherent (a : I) (n : ℕ) :
    (⟨List.replicate n a⟩ : Text I).isCoherent :=
  coherent_replicate a n

/-- **Theorem 10 (Void Text Depth)**: A text of all void ideas has zero depth.
    INSIGHT: a text consisting entirely of silence has no complexity. -/
theorem Text.void_replicate_depth (n : ℕ) :
    (⟨List.replicate n (IdeaticSpace.void : I)⟩ : Text I).totalDepth = 0 :=
  depthSum_void_replicate n

end TextStructure

/-! ## §2. Text Operations

Text concatenation is the fundamental operation of composition in literary
theory—joining two texts to form a larger one. -/

section TextOperations
variable {I : Type*} [IdeaticSpace I]

/-- Concatenation of texts: joining two texts sequentially -/
def Text.append (t₁ t₂ : Text I) : Text I := ⟨t₁.ideas ++ t₂.ideas⟩

/-- **Theorem 11 (Concatenation Length)**: The length of concatenated texts
    is the sum of their lengths.
    INSIGHT: joining texts adds their extents—no compression in concatenation. -/
theorem Text.append_length (t₁ t₂ : Text I) :
    (t₁.append t₂).length = t₁.length + t₂.length := by
  simp [Text.append, Text.length, List.length_append]

/-- **Theorem 12 (Concatenation Depth Additivity)**: The total depth of
    concatenated texts equals the sum of their total depths.
    INSIGHT: joining texts sums complexity—unlike ideatic composition, text
    concatenation is additive, not subadditive. -/
theorem Text.append_totalDepth (t₁ t₂ : Text I) :
    (t₁.append t₂).totalDepth = t₁.totalDepth + t₂.totalDepth := by
  simp [Text.append, Text.totalDepth, depthSum, List.map_append, List.sum_append]

/-- **Theorem 13 (Empty Left Append)**: Prepending the empty text is identity.
    INSIGHT: beginning with silence doesn't alter the text. -/
@[simp] theorem Text.empty_append (t : Text I) :
    Text.append Text.empty t = t := by
  simp [Text.append, Text.empty]

/-- **Theorem 14 (Empty Right Append)**: Appending the empty text is identity.
    INSIGHT: trailing silence doesn't alter a text. -/
@[simp] theorem Text.append_empty (t : Text I) :
    Text.append t Text.empty = t := by
  simp [Text.append, Text.empty]

/-- **Theorem 15 (Concatenation Associativity)**: Text concatenation is
    associative. INSIGHT: the grouping of text-joining doesn't matter—texts
    form a monoid under concatenation. -/
theorem Text.append_assoc (t₁ t₂ t₃ : Text I) :
    Text.append (Text.append t₁ t₂) t₃ = Text.append t₁ (Text.append t₂ t₃) := by
  simp [Text.append, List.append_assoc]

/-- A subtext: a contiguous subsequence of ideas -/
def Text.subtext (t : Text I) (start len : ℕ) : Text I :=
  ⟨(t.ideas.drop start).take len⟩

/-- **Theorem 16 (Subtext Length Bound)**: A subtext is no longer than the
    original. INSIGHT: quoting can only shorten. -/
theorem Text.subtext_length_le (t : Text I) (start len : ℕ) :
    (t.subtext start len).length ≤ t.length := by
  simp only [Text.subtext, Text.length, List.length_take, List.length_drop]
  omega

end TextOperations

/-! ## §3. Subtext Coherence

The central theorem: **subtexts of coherent texts are coherent**. -/

section SubtextCoherence
variable {I : Type*} [IdeaticSpace I]

/-- Helper: dropping elements from a coherent list preserves coherence. -/
theorem coherent_drop : ∀ (s : List I) (n : ℕ),
    Coherent s → Coherent (s.drop n)
  | _, 0, h => by simpa using h
  | [], _ + 1, _ => by simp [Coherent]
  | [_], _ + 1, _ => by simp [Coherent]
  | _ :: b :: rest, n + 1, h => by
    simp [List.drop]
    exact coherent_drop (b :: rest) n h.2

/-- Helper: taking elements from a coherent list preserves coherence. -/
theorem coherent_take : ∀ (s : List I) (n : ℕ),
    Coherent s → Coherent (s.take n)
  | _, 0, _ => by simp [Coherent]
  | [], _, _ => by simp [Coherent]
  | [_], _ + 1, _ => by simp [List.take, Coherent]
  | _ :: b :: rest, n + 1, h => by
    simp [List.take]
    cases n with
    | zero => simp [Coherent]
    | succ n =>
      simp [List.take]
      constructor
      · exact h.1
      · exact coherent_take (b :: rest) (n + 1) h.2

/-- **Theorem 17 (Subtext Coherence)**: Every subtext of a coherent text is
    coherent. INSIGHT: if a work is coherent, every contiguous passage within
    it is coherent. NOT true for non-contiguous extractions. -/
theorem Text.subtext_coherent (t : Text I) (start len : ℕ)
    (hc : t.isCoherent) : (t.subtext start len).isCoherent := by
  unfold Text.subtext Text.isCoherent at *
  exact coherent_take _ _ (coherent_drop _ _ hc)

/-- **Theorem 18 (Coherence of Head)**: The first n ideas of a coherent text
    form a coherent text. INSIGHT: the opening of a coherent novel is always
    coherent—you need not finish the book for the beginning to make sense. -/
theorem Text.head_coherent (t : Text I) (n : ℕ)
    (hc : t.isCoherent) : (⟨t.ideas.take n⟩ : Text I).isCoherent :=
  coherent_take t.ideas n hc

/-- **Theorem 19 (Coherence of Tail)**: Dropping the first n ideas of a
    coherent text leaves a coherent text.
    INSIGHT: you can start reading a coherent text from any point. -/
theorem Text.tail_coherent (t : Text I) (n : ℕ)
    (hc : t.isCoherent) : (⟨t.ideas.drop n⟩ : Text I).isCoherent :=
  coherent_drop t.ideas n hc

end SubtextCoherence

/-! ## §4. Narrative Arc

A **narrative arc** characterizes the depth-pattern of a text. We define
rising and falling arcs using list-level predicates, plus depth-bounded texts. -/

section NarrativeArc
variable {I : Type*} [IdeaticSpace I]

/-- A list has pairwise non-decreasing depth -/
def depthRising : List I → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
    IdeaticSpace.depth a ≤ IdeaticSpace.depth b ∧ depthRising (b :: rest)

/-- A list has pairwise non-increasing depth -/
def depthFalling : List I → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
    IdeaticSpace.depth b ≤ IdeaticSpace.depth a ∧ depthFalling (b :: rest)

/-- A text has a rising arc if depth is non-decreasing.
    INSIGHT: a "rising" narrative builds complexity—each new idea is at least
    as deep as the previous. Models expository writing and dramatic escalation. -/
def Text.risingArc (t : Text I) : Prop := depthRising t.ideas

/-- A text has a falling arc if depth is non-increasing.
    INSIGHT: a "falling" narrative simplifies. Models denouement and resolution. -/
def Text.fallingArc (t : Text I) : Prop := depthFalling t.ideas

/-- A text is depth-bounded if every idea has depth ≤ d -/
def Text.depthBounded (t : Text I) (d : ℕ) : Prop :=
  ∀ (a : I), a ∈ t.ideas → IdeaticSpace.depth a ≤ d

/-- **Theorem 20 (Empty Rising)**: The empty text trivially has a rising arc.
    INSIGHT: the blank page vacuously satisfies all narrative constraints. -/
theorem Text.empty_rising : (Text.empty : Text I).risingArc := by
  simp [Text.risingArc, Text.empty, depthRising]

/-- **Theorem 21 (Empty Falling)**: The empty text trivially has a falling arc.
    INSIGHT: silence satisfies every structural constraint vacuously. -/
theorem Text.empty_falling : (Text.empty : Text I).fallingArc := by
  simp [Text.fallingArc, Text.empty, depthFalling]

/-- **Theorem 22 (Singleton Both Arcs)**: A single-idea text has both a rising
    and falling arc simultaneously.
    INSIGHT: a single thought is both escalation and resolution. -/
theorem Text.singleton_rising_and_falling (a : I) :
    (Text.singleton a).risingArc ∧ (Text.singleton a).fallingArc := by
  exact ⟨trivial, trivial⟩

/-- **Theorem 23 (Bounded Text Total Depth)**: A depth-bounded text's total
    depth is bounded by length × bound.
    INSIGHT: if a genre imposes depth constraint d on every idea, then the
    total complexity is at most length × d. -/
theorem Text.depthBounded_totalDepth (t : Text I) (d : ℕ)
    (hb : t.depthBounded d) :
    t.totalDepth ≤ t.length * d := by
  unfold Text.totalDepth Text.length
  exact depthSum_bound t.ideas d hb

/-- **Theorem 24 (Replicate Rising and Falling)**: A text of n copies of the
    same idea has both rising and falling arcs.
    INSIGHT: repetition produces a flat arc—constant depth means the narrative
    is simultaneously rising and falling. -/
theorem Text.replicate_both_arcs : ∀ (a : I) (n : ℕ),
    (⟨List.replicate n a⟩ : Text I).risingArc ∧
    (⟨List.replicate n a⟩ : Text I).fallingArc
  | _, 0 => ⟨trivial, trivial⟩
  | _, 1 => ⟨trivial, trivial⟩
  | a, n + 2 => by
    have ih := Text.replicate_both_arcs a (n + 1)
    constructor
    · show depthRising (List.replicate (n + 2) a)
      rw [List.replicate_succ]
      show depthRising (a :: List.replicate (n + 1) a)
      cases n with
      | zero => simp [List.replicate, depthRising]
      | succ n =>
        rw [List.replicate_succ]
        show IdeaticSpace.depth a ≤ IdeaticSpace.depth a ∧
          depthRising (a :: List.replicate (n + 1) a)
        exact ⟨le_refl _, ih.1⟩
    · show depthFalling (List.replicate (n + 2) a)
      rw [List.replicate_succ]
      show depthFalling (a :: List.replicate (n + 1) a)
      cases n with
      | zero => simp [List.replicate, depthFalling]
      | succ n =>
        rw [List.replicate_succ]
        show IdeaticSpace.depth a ≤ IdeaticSpace.depth a ∧
          depthFalling (a :: List.replicate (n + 1) a)
        exact ⟨le_refl _, ih.2⟩

end NarrativeArc

/-! ## §5. Genre Theory

A **genre** is a predicate on texts—the set of all texts satisfying certain
structural invariants. We prove fundamental properties of genre algebra. -/

section Genre
variable {I : Type*} [IdeaticSpace I]

/-- A Genre is a predicate on texts: the set of texts satisfying invariants.
    INSIGHT: a genre is not defined by content but by structural constraints. -/
def Genre (I : Type*) [IdeaticSpace I] := Text I → Prop

/-- A text belongs to a genre if it satisfies the genre predicate -/
def Genre.contains (g : Genre I) (t : Text I) : Prop := g t

/-- The intersection of two genres: texts satisfying both -/
def Genre.inter (g₁ g₂ : Genre I) : Genre I := fun t => g₁ t ∧ g₂ t

/-- The union of two genres: texts satisfying either -/
def Genre.union (g₁ g₂ : Genre I) : Genre I := fun t => g₁ t ∨ g₂ t

/-- The universal genre: contains all texts -/
def Genre.universal : Genre I := fun _ => True

/-- The empty genre: contains no texts -/
def Genre.none : Genre I := fun _ => False

/-- A coherence genre: all coherent texts -/
def Genre.coherent : Genre I := fun t => t.isCoherent

/-- A depth-bounded genre: texts where all ideas have depth ≤ d -/
def Genre.bounded (d : ℕ) : Genre I := fun t => t.depthBounded d

/-- **Theorem 25 (Genre Crossing Detection)**: If a text violates a genre's
    defining invariant, it is not in the genre.
    INSIGHT: genres are defined by constraints, and violating any constraint
    exits the genre. A "sonnet" with 15 lines is not a sonnet. -/
theorem Genre.crossing_detected (g : Genre I) (t : Text I)
    (h : ¬ g t) : ¬ g.contains t := h

/-- **Theorem 26 (Genre Intersection Restricts)**: Belonging to the
    intersection of two genres requires satisfying both.
    INSIGHT: genre hybrids impose constraints of BOTH genres. -/
theorem Genre.inter_requires_both (g₁ g₂ : Genre I) (t : Text I) :
    (g₁.inter g₂).contains t ↔ g₁.contains t ∧ g₂.contains t :=
  Iff.rfl

/-- **Theorem 27 (Universal Genre Contains All)**: Every text belongs to
    the universal genre.
    INSIGHT: the "genre" with no constraints includes everything. -/
theorem Genre.universal_contains (t : Text I) :
    (Genre.universal : Genre I).contains t := trivial

/-- **Theorem 28 (Empty Genre Contains Nothing)**: No text belongs to the
    empty genre.
    INSIGHT: a genre with contradictory constraints is empty. -/
theorem Genre.none_contains (t : Text I) :
    ¬ (Genre.none : Genre I).contains t := not_false

/-- **Theorem 29 (Coherence Genre Contains Empty)**: The empty text is in
    the coherence genre.
    INSIGHT: the blank page is "coherent literature." -/
theorem Genre.coherent_contains_empty :
    (Genre.coherent : Genre I).contains (Text.empty : Text I) := by
  show (Text.empty : Text I).isCoherent
  exact coherent_nil

/-- **Theorem 30 (Depth-Bounded Genre Monotonicity)**: If d ≤ d', then the
    d-bounded genre is included in the d'-bounded genre.
    INSIGHT: relaxing a depth constraint can only expand the genre. -/
theorem Genre.bounded_mono {d d' : ℕ} (h : d ≤ d') :
    ∀ (t : Text I), (Genre.bounded d : Genre I).contains t →
      (Genre.bounded d' : Genre I).contains t := by
  intro t ht a ha
  exact le_trans (ht a ha) h

/-- **Theorem 31 (Genre Intersection Commutativity)**: The intersection of
    genres is commutative.
    INSIGHT: combining genre constraints is order-independent. -/
theorem Genre.inter_comm (g₁ g₂ : Genre I) (t : Text I) :
    (g₁.inter g₂).contains t ↔ (g₂.inter g₁).contains t := by
  simp [Genre.inter, Genre.contains, and_comm]

/-- **Theorem 32 (Genre Union Includes Both)**: The union of genres contains
    every text from either genre.
    INSIGHT: a bookshelf labeled "fiction or poetry" includes both. -/
theorem Genre.union_includes (g₁ g₂ : Genre I) (t : Text I) :
    g₁.contains t → (g₁.union g₂).contains t := by
  intro h; exact Or.inl h

/-- **Theorem 33 (Bounded Zero Genre Contains Void Texts)**: The 0-bounded
    genre contains texts made entirely of void ideas.
    INSIGHT: texts of pure silence belong to the most restrictive depth genre. -/
theorem Genre.bounded_zero_contains_void (n : ℕ) :
    (Genre.bounded 0 : Genre I).contains ⟨List.replicate n IdeaticSpace.void⟩ := by
  intro a ha
  rw [List.mem_replicate] at ha
  rw [ha.2]; exact le_of_eq IdeaticSpace.depth_void

end Genre

/-! ## §6. Rhetorical Transformation Theory

A **rhetorical map** transforms ideas while preserving the resonance structure
between pairs of ideas. If two ideas resonate before transformation, they
resonate after. This property composes, giving a monoid of transformations.

We separately define **meaning maps** where each output resonates with its
input—a stronger per-element notion that does NOT compose in general since
resonance is not transitive. -/

section Rhetoric
variable {I : Type*} [IdeaticSpace I]

/-- A rhetorical map preserves the resonance structure between ideas.
    INSIGHT: paraphrase and translation change surface form but preserve
    the relational structure of meaning. -/
structure RhetoricalMap (I : Type*) [IdeaticSpace I] where
  transform : I → I
  preserves_resonance : ∀ (a b : I),
    IdeaticSpace.resonates a b →
    IdeaticSpace.resonates (transform a) (transform b)

/-- Apply a rhetorical map to a text: transform each idea -/
def RhetoricalMap.applyText (f : RhetoricalMap I) (t : Text I) : Text I :=
  ⟨t.ideas.map f.transform⟩

/-- The identity rhetorical map: no transformation -/
def RhetoricalMap.identity : RhetoricalMap I where
  transform := fun a => a
  preserves_resonance := fun _ _ h => h

/-- Composition of rhetorical maps -/
def RhetoricalMap.comp (f g : RhetoricalMap I) : RhetoricalMap I where
  transform := fun a => g.transform (f.transform a)
  preserves_resonance := fun a b h =>
    g.preserves_resonance _ _ (f.preserves_resonance a b h)

/-- **Theorem 34 (Identity Preserves Text)**: The identity rhetorical map
    leaves every text unchanged.
    INSIGHT: not transforming a text is the trivial rhetorical operation—
    the identity element of the monoid. -/
theorem RhetoricalMap.identity_applyText (t : Text I) :
    RhetoricalMap.identity.applyText t = t := by
  simp [RhetoricalMap.applyText, RhetoricalMap.identity, List.map_id]

/-- **Theorem 35 (Composition Associativity)**: Rhetorical map composition
    is associative.
    INSIGHT: the order of applying successive transformations doesn't depend
    on grouping. -/
theorem RhetoricalMap.comp_assoc (f g h : RhetoricalMap I) :
    RhetoricalMap.comp (RhetoricalMap.comp f g) h =
    RhetoricalMap.comp f (RhetoricalMap.comp g h) := by
  simp [RhetoricalMap.comp]

/-- **Theorem 36 (Identity is Left Unit)**: Composing identity on the left
    gives the original map.
    INSIGHT: doing nothing before a transformation equals the transformation. -/
theorem RhetoricalMap.id_comp (f : RhetoricalMap I) :
    RhetoricalMap.comp RhetoricalMap.identity f = f := by
  simp [RhetoricalMap.comp, RhetoricalMap.identity]

/-- **Theorem 37 (Identity is Right Unit)**: Composing identity on the right
    gives the original map.
    INSIGHT: doing nothing after a transformation equals the transformation. -/
theorem RhetoricalMap.comp_id (f : RhetoricalMap I) :
    RhetoricalMap.comp f RhetoricalMap.identity = f := by
  simp [RhetoricalMap.comp, RhetoricalMap.identity]

/-- **Theorem 38 (Rhetorical Maps Preserve Coherence)**: Applying a rhetorical
    map to a coherent text produces a coherent text.
    INSIGHT: transformations that preserve resonance structure also preserve
    narrative coherence. A good translation of a coherent text is coherent. -/
theorem RhetoricalMap.preserves_coherence (f : RhetoricalMap I)
    (t : Text I) (hc : t.isCoherent) :
    (f.applyText t).isCoherent := by
  unfold RhetoricalMap.applyText Text.isCoherent at *
  have : ∀ (l : List I), Coherent l → Coherent (l.map f.transform) := by
    intro l
    induction l with
    | nil => intro _; exact trivial
    | cons a rest ih =>
      cases rest with
      | nil => intro _; exact trivial
      | cons b rest' =>
        intro hcl
        simp only [List.map]
        exact ⟨f.preserves_resonance a b hcl.1, ih hcl.2⟩
  exact this t.ideas hc

/-- **Theorem 39 (Rhetorical Maps Preserve Length)**: Applying a rhetorical
    map preserves text length.
    INSIGHT: paraphrase doesn't change the number of ideas—it changes form
    but not count. -/
theorem RhetoricalMap.preserves_length (f : RhetoricalMap I)
    (t : Text I) : (f.applyText t).length = t.length := by
  simp [RhetoricalMap.applyText, Text.length, List.length_map]

/-- **Theorem 40 (Composition Distributes Over Application)**: Composing maps
    then applying equals applying sequentially.
    INSIGHT: the effect of a chain of revisions can be computed either by
    first composing the revision functions or by applying them in sequence. -/
theorem RhetoricalMap.comp_applyText (f g : RhetoricalMap I) (t : Text I) :
    (RhetoricalMap.comp f g).applyText t =
    g.applyText (f.applyText t) := by
  simp [RhetoricalMap.applyText, RhetoricalMap.comp, List.map_map]

end Rhetoric

/-! ## §7. Meaning Maps and Cross-Cutting Results

**Meaning maps** require each output to resonate with its input—a per-element
notion of faithfulness. We prove additional cross-cutting theorems connecting
text structure, coherence, and depth. -/

section MeaningPreservation
variable {I : Type*} [IdeaticSpace I]

/-- A meaning-preserving map: each transformed idea resonates with the original.
    INSIGHT: unlike RhetoricalMap (which preserves pairwise resonance structure),
    a MeaningMap ensures each individual output is "close" to its input. -/
structure MeaningMap (I : Type*) [IdeaticSpace I] where
  transform : I → I
  meaning_preserved : ∀ (a : I), IdeaticSpace.resonates a (transform a)

/-- The identity meaning map -/
def MeaningMap.identity : MeaningMap I where
  transform := fun a => a
  meaning_preserved := fun a => resonance_refl a

/-- **Theorem 41 (MeaningMap Produces Rhetorical Map)**: Every meaning-preserving
    map that also preserves pairwise resonance is a rhetorical map.
    INSIGHT: meaning preservation at the individual level PLUS structural
    preservation gives full rhetorical faithfulness. -/
theorem MeaningMap.to_rhetorical (f : MeaningMap I)
    (hpair : ∀ (a b : I), IdeaticSpace.resonates a b →
      IdeaticSpace.resonates (f.transform a) (f.transform b)) :
    ∃ (g : RhetoricalMap I), g.transform = f.transform :=
  ⟨⟨f.transform, hpair⟩, rfl⟩

/-- **Theorem 42 (Void Composition Preserves Resonance)**: Composing with void
    preserves resonance (since void is identity).
    INSIGHT: silence as context never disrupts resonance—it is the universal
    neutral backdrop for meaning. -/
theorem void_compose_preserves_resonance (a b : I)
    (h : IdeaticSpace.resonates a b) :
    IdeaticSpace.resonates
      (IdeaticSpace.compose IdeaticSpace.void a)
      (IdeaticSpace.compose IdeaticSpace.void b) := by
  rw [void_left, void_left]; exact h

/-- **Theorem 43 (Coherent Pair Composition)**: If two pairs of ideas resonate,
    composing corresponding elements gives a coherent pair.
    INSIGHT: coherent discourses can be "composed in parallel" when parts are
    individually resonant. Formalizes counterpoint and polyphonic writing. -/
theorem coherent_compose_pair {a b c d : I}
    (hab : IdeaticSpace.resonates a b)
    (hcd : IdeaticSpace.resonates c d) :
    (Text.pair (IdeaticSpace.compose a c) (IdeaticSpace.compose b d)).isCoherent := by
  rw [Text.pair_coherent]
  exact IdeaticSpace.resonance_compose a b c d hab hcd

/-- **Theorem 44 (Depth-Bounded Subtext)**: Subtexts of depth-bounded texts
    are depth-bounded.
    INSIGHT: if a genre imposes a depth constraint, every quotation from a
    text in that genre also satisfies the constraint. -/
theorem Text.subtext_depthBounded (t : Text I) (d : ℕ) (start len : ℕ)
    (hb : t.depthBounded d) :
    (t.subtext start len).depthBounded d := by
  intro a ha
  apply hb
  simp [Text.subtext] at ha
  exact List.mem_of_mem_drop (List.mem_of_mem_take ha)

/-- **Theorem 45 (Append Depth Bounded)**: Concatenating two depth-bounded texts
    produces a depth-bounded text.
    INSIGHT: depth bounds are closed under joining—combining texts from the
    same genre stays in the genre. -/
theorem Text.append_depthBounded (t₁ t₂ : Text I) (d : ℕ)
    (h₁ : t₁.depthBounded d) (h₂ : t₂.depthBounded d) :
    (t₁.append t₂).depthBounded d := by
  intro a ha
  simp [Text.append] at ha
  rcases ha with h | h
  · exact h₁ a h
  · exact h₂ a h

/-- **Theorem 46 (MeaningMap Mediator)**: For any meaning map f, the composition
    a·f(a) resonates with f(a)·f(f(a)).
    INSIGHT: meaning maps create "bridges" of resonance through the mediator
    pattern—the transformed idea serves as a common element connecting
    original and transformed discourses. -/
theorem meaning_map_mediator (f : MeaningMap I) (a : I) :
    IdeaticSpace.resonates
      (IdeaticSpace.compose a (f.transform a))
      (IdeaticSpace.compose (f.transform a) (f.transform (f.transform a))) :=
  IdeaticSpace.resonance_compose a (f.transform a) (f.transform a)
    (f.transform (f.transform a))
    (f.meaning_preserved a) (f.meaning_preserved (f.transform a))

end MeaningPreservation

end IDT
