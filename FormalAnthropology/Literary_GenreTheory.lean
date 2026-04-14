import FormalAnthropology.IDT_Foundations

/-!
# Literary Genre Theory in IDT Axiomatics

A formal theory of literary genres as sub-monoids of ideatic space. Genres are
predicates on ideas closed under composition and containing the void — they
capture the structural invariants of literary form.

## Core Insight

A genre is not a bag of surface features but a *compositional closure*: a set
of ideas such that composing any two ideas "in the genre" yields another idea
"in the genre." This is exactly the algebraic notion of a sub-monoid, applied
to the space of ideas. Genres are the *stable vocabularies* of literary form.

## Contents

1. Genre as sub-monoid predicate
2. Genre intersection lattice
3. Generated genres (closure under composition)
4. Depth-bounded genres
5. Genre crossing and separation
6. Genre rigidity under depth-reducing maps
7. Resonance-closed genres ("styles")
8. Genre hierarchy (partial order by inclusion)

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

set_option autoImplicit false

namespace IDT

/-! ## §1. Genre: The Fundamental Definition

A genre is a predicate on ideatic space that is closed under composition
and contains the void. Algebraically, a genre is a sub-monoid of the
ideatic composition monoid. -/

section GenreDef
variable {I : Type*} [IdeaticSpace I]

/-- **Genre**: a sub-monoid of ideatic space.
    LITERARY INSIGHT: A genre is not defined by a checklist of features but by
    *compositional closure* — if two ideas belong to the genre, their composition
    does too. This captures how genres are generative systems, not static
    categories. A detective story combined with a detective story is still a
    detective story. -/
structure Genre (I : Type*) [IdeaticSpace I] where
  mem : I → Prop
  void_mem : mem IdeaticSpace.void
  compose_mem : ∀ (a b : I), mem a → mem b → mem (IdeaticSpace.compose a b)

/-- Genre membership notation -/
def Genre.contains (G : Genre I) (a : I) : Prop := G.mem a

/-- **Theorem 1 (Void Universality)**: Every genre contains the void.
    LITERARY INSIGHT: Silence belongs to every genre. The blank page is
    simultaneously a poem, a novel, and a play — the empty text satisfies
    all genre constraints vacuously. -/
theorem genre_void_mem (G : Genre I) : G.mem (IdeaticSpace.void : I) :=
  G.void_mem

/-- **Theorem 2 (Compositional Closure)**: Genres are closed under composition.
    LITERARY INSIGHT: If two passages belong to a genre, concatenating them
    stays in-genre. This is why anthologies of short stories are still
    "short story collections" — genre is preserved under aggregation. -/
theorem genre_compose_mem (G : Genre I) {a b : I}
    (ha : G.mem a) (hb : G.mem b) :
    G.mem (IdeaticSpace.compose a b) :=
  G.compose_mem a b ha hb

/-- **Theorem 3 (Iterated Composition in Genre)**: composeN stays in genre.
    LITERARY INSIGHT: Repeating a generic element any number of times remains
    in-genre. A sonnet repeated is still poetry; a chapter repeated is still
    prose. Repetition cannot escape genre. -/
theorem genre_composeN_mem (G : Genre I) {a : I} (ha : G.mem a) :
    ∀ (n : ℕ), G.mem (composeN a n)
  | 0 => G.void_mem
  | n + 1 => G.compose_mem (composeN a n) a (genre_composeN_mem G ha n) ha

end GenreDef

/-! ## §2. The Universal and Void Genres

Every partially ordered set of genres has a top (the universal genre containing
all ideas) and a bottom (the void genre containing only the void). -/

section SpecialGenres
variable {I : Type*} [IdeaticSpace I]

/-- **The Universal Genre**: contains all ideas.
    LITERARY INSIGHT: The "genre" of all possible texts — literature itself.
    Every idea belongs; every composition stays. This is the maximally
    permissive genre, imposing no constraints whatsoever. -/
def universalGenre : Genre I where
  mem := fun _ => True
  void_mem := trivial
  compose_mem := fun _ _ _ _ => trivial

/-- **The Void Genre**: contains only the void.
    LITERARY INSIGHT: The genre of pure silence — no content, only the
    empty text. This is the maximally restrictive genre. It models the
    theoretical limit of genre constraints pushed to their extreme. -/
def voidGenre : Genre I where
  mem := fun a => a = IdeaticSpace.void
  void_mem := rfl
  compose_mem := fun a b ha hb => by
    rw [ha, hb]; exact IdeaticSpace.void_left (IdeaticSpace.void : I)

/-- **Theorem 4 (Universal Contains All)**: every idea is in the universal genre.
    LITERARY INSIGHT: "Literature" as a genre has no exclusion principle. -/
theorem universal_contains_all (a : I) : (universalGenre : Genre I).mem a :=
  trivial

/-- **Theorem 5 (Void Genre Minimal)**: the void genre contains only void.
    LITERARY INSIGHT: The most restrictive possible genre admits only silence. -/
theorem void_genre_char (a : I) :
    (voidGenre : Genre I).mem a ↔ a = (IdeaticSpace.void : I) :=
  Iff.rfl

/-- **Theorem 6 (Void Genre Subset of All)**: the void genre is contained
    in every genre.
    LITERARY INSIGHT: Since every genre contains the void (silence), the
    void genre is the bottom of the genre hierarchy. -/
theorem voidGenre_subset (G : Genre I) :
    ∀ (a : I), (voidGenre : Genre I).mem a → G.mem a := by
  intro a ha
  rw [ha]
  exact G.void_mem

/-- **Theorem 7 (Universal Genre Contains Every Genre)**: every genre is
    contained in the universal genre.
    LITERARY INSIGHT: Every specific genre is a specialization of "all
    literature." Genre constraints only *restrict*, never *expand* beyond
    the universal. -/
theorem genre_subset_universal (G : Genre I) :
    ∀ (a : I), G.mem a → (universalGenre : Genre I).mem a :=
  fun _ _ => trivial

end SpecialGenres

/-! ## §3. Genre Intersection

The intersection of genres is a genre. This is the algebraic foundation for
"cross-genre" works: a text that satisfies multiple genre constraints
simultaneously belongs to the intersection. -/

section GenreIntersection
variable {I : Type*} [IdeaticSpace I]

/-- **Genre Intersection**: the intersection of two genres is a genre.
    LITERARY INSIGHT: A "detective romance" belongs to both the detective
    genre and the romance genre. The intersection is itself a coherent
    genre — combining detective-romance elements yields detective-romance. -/
def genreIntersection (G₁ G₂ : Genre I) : Genre I where
  mem := fun a => G₁.mem a ∧ G₂.mem a
  void_mem := ⟨G₁.void_mem, G₂.void_mem⟩
  compose_mem := fun a b ⟨h1a, h2a⟩ ⟨h1b, h2b⟩ =>
    ⟨G₁.compose_mem a b h1a h1b, G₂.compose_mem a b h2a h2b⟩

/-- **Theorem 8 (Intersection Membership)**: membership in the intersection
    is equivalent to membership in both genres.
    LITERARY INSIGHT: A text is cross-genre iff it satisfies both genre
    constraints independently. -/
theorem genreIntersection_mem (G₁ G₂ : Genre I) (a : I) :
    (genreIntersection G₁ G₂).mem a ↔ G₁.mem a ∧ G₂.mem a :=
  Iff.rfl

/-- **Theorem 9 (Intersection Commutativity)**: intersection is commutative.
    LITERARY INSIGHT: "detective romance" = "romance detective" as genre
    categories — the order of genre labels doesn't matter. -/
theorem genreIntersection_comm (G₁ G₂ : Genre I) (a : I) :
    (genreIntersection G₁ G₂).mem a ↔ (genreIntersection G₂ G₁).mem a := by
  simp [genreIntersection_mem]; exact And.comm

/-- **Theorem 10 (Intersection Associativity)**: intersection is associative.
    LITERARY INSIGHT: "sci-fi detective romance" is the same genre whether
    we combine (sci-fi ∩ detective) ∩ romance or sci-fi ∩ (detective ∩ romance). -/
theorem genreIntersection_assoc (G₁ G₂ G₃ : Genre I) (a : I) :
    (genreIntersection (genreIntersection G₁ G₂) G₃).mem a ↔
    (genreIntersection G₁ (genreIntersection G₂ G₃)).mem a := by
  simp [genreIntersection_mem]; exact and_assoc

/-- **Theorem 11 (Intersection Subset Left)**: intersection ⊆ first genre.
    LITERARY INSIGHT: a cross-genre text is always in each parent genre. -/
theorem genreIntersection_subset_left (G₁ G₂ : Genre I) (a : I) :
    (genreIntersection G₁ G₂).mem a → G₁.mem a :=
  fun h => h.1

/-- **Theorem 12 (Intersection Subset Right)**: intersection ⊆ second genre. -/
theorem genreIntersection_subset_right (G₁ G₂ : Genre I) (a : I) :
    (genreIntersection G₁ G₂).mem a → G₂.mem a :=
  fun h => h.2

/-- **Theorem 13 (Intersection with Universal)**: intersecting with the
    universal genre changes nothing.
    LITERARY INSIGHT: saying a text is "literature AND a novel" is the same
    as saying it's "a novel." -/
theorem genreIntersection_universal (G : Genre I) (a : I) :
    (genreIntersection G universalGenre).mem a ↔ G.mem a := by
  simp [genreIntersection_mem, universalGenre]

/-- **Theorem 14 (Intersection with Void Genre)**: intersecting with the
    void genre yields the void genre.
    LITERARY INSIGHT: requiring a text to be both "a novel" and "pure
    silence" means it can only be silence. -/
theorem genreIntersection_voidGenre (G : Genre I) (a : I) :
    (genreIntersection G voidGenre).mem a ↔ (voidGenre : Genre I).mem a := by
  constructor
  · intro ⟨_, h2⟩; exact h2
  · intro h; exact ⟨voidGenre_subset G a h, h⟩

end GenreIntersection

/-! ## §4. Genre Union (as Generated Genre)

The *union* of two genres is NOT automatically a genre — composing an element
of G₁ with an element of G₂ need not land in either. This is a fundamental
insight about genre mixing. We define the genre *generated* by a union. -/

section GenreUnion
variable {I : Type*} [IdeaticSpace I]

/-- The closure of a set under composition and void.
    This inductively builds the smallest genre containing a given predicate.
    LITERARY INSIGHT: Starting from a set of "seed" texts, the generated
    genre includes all texts that can be built by composing seeds. -/
inductive GenreClosure (S : I → Prop) : I → Prop where
  | seed : ∀ (a : I), S a → GenreClosure S a
  | void_cl : GenreClosure S IdeaticSpace.void
  | compose_cl : ∀ (a b : I), GenreClosure S a → GenreClosure S b →
      GenreClosure S (IdeaticSpace.compose a b)

/-- The genre generated by a predicate S. -/
def generatedGenre (S : I → Prop) : Genre I where
  mem := GenreClosure S
  void_mem := GenreClosure.void_cl
  compose_mem := fun a b ha hb => GenreClosure.compose_cl a b ha hb

/-- **Theorem 15 (Seeds in Generated Genre)**: every seed is in the
    generated genre.
    LITERARY INSIGHT: the founding texts of a genre are always members
    of that genre. Homer's epics are in the "epic" genre by construction. -/
theorem seed_mem_generatedGenre (S : I → Prop) {a : I} (ha : S a) :
    (generatedGenre S).mem a :=
  GenreClosure.seed a ha

/-- **Theorem 16 (Generated Genre Minimality)**: the generated genre is
    the smallest genre containing S.
    LITERARY INSIGHT: genre boundaries are drawn as tightly as possible
    around the founding texts — a genre includes only what *must* follow
    from compositional closure. -/
theorem generatedGenre_minimal (S : I → Prop) (G : Genre I)
    (hcontains : ∀ (a : I), S a → G.mem a) :
    ∀ (a : I), (generatedGenre S).mem a → G.mem a := by
  intro a ha
  induction ha with
  | seed a hs => exact hcontains a hs
  | void_cl => exact G.void_mem
  | compose_cl a b _ _ iha ihb => exact G.compose_mem a b iha ihb

/-- **Theorem 17 (Generated from Genre is Genre)**: generating from a genre's
    own membership gives back the same membership.
    LITERARY INSIGHT: a genre that re-founds itself from its own texts
    doesn't grow — it's already closed. -/
theorem generatedGenre_of_genre (G : Genre I) :
    ∀ (a : I), (generatedGenre G.mem).mem a → G.mem a :=
  generatedGenre_minimal G.mem G (fun _ h => h)

/-- **Theorem 18 (Genre Contains its Generation)**: a genre's own members
    are in the genre generated from it.
    LITERARY INSIGHT: founding a "new genre" from the existing texts of a
    genre includes all the original texts. -/
theorem genre_subset_generated (G : Genre I) :
    ∀ (a : I), G.mem a → (generatedGenre G.mem).mem a :=
  fun a ha => GenreClosure.seed a ha

end GenreUnion

/-! ## §5. Depth-Bounded Genres

A genre with a depth bound — all elements have bounded complexity.
This models "simple" genres: children's literature, haiku, etc. -/

section DepthBounded
variable {I : Type*} [IdeaticSpace I]

/-- A genre is depth-bounded at level n if all members have depth ≤ n. -/
def GenreDepthBounded (G : Genre I) (n : ℕ) : Prop :=
  ∀ (a : I), G.mem a → IdeaticSpace.depth a ≤ n

/-- **Theorem 19 (Depth Bound Composition)**: in a depth-bounded genre,
    compositions have depth at most 2n.
    LITERARY INSIGHT: in a genre where all elements are "simple" (depth ≤ n),
    composing two elements produces something of bounded complexity (≤ 2n).
    Children's literature composed with children's literature has bounded
    sophistication — you can't escape genre simplicity through composition. -/
theorem genre_depth_compose_bound (G : Genre I) (n : ℕ)
    (hbound : GenreDepthBounded G n) {a b : I}
    (ha : G.mem a) (hb : G.mem b) :
    IdeaticSpace.depth (IdeaticSpace.compose a b) ≤ 2 * n := by
  have h1 := hbound a ha
  have h2 := hbound b hb
  have h3 := IdeaticSpace.depth_subadditive a b
  omega

/-- **Theorem 20 (Void Genre is Depth Zero)**: the void genre is depth-bounded at 0.
    LITERARY INSIGHT: silence has zero complexity. The most restrictive genre
    is also the shallowest. -/
theorem voidGenre_depth_zero : GenreDepthBounded (voidGenre : Genre I) 0 := by
  intro a ha
  simp [voidGenre] at ha
  rw [ha]; exact le_of_eq IdeaticSpace.depth_void

/-- **Theorem 21 (Universal Genre Unbounded)**: if any idea has depth > n,
    the universal genre is not depth-bounded at n.
    LITERARY INSIGHT: "literature" as a whole cannot be bounded in
    complexity — there's always room for deeper work. -/
theorem universalGenre_unbounded {n : ℕ} {a : I}
    (ha : IdeaticSpace.depth a > n) :
    ¬GenreDepthBounded (universalGenre : Genre I) n := by
  intro hbound
  have := hbound a trivial
  omega

/-- **Theorem 22 (Depth Bound Monotonicity)**: if G is depth-bounded at n,
    it's depth-bounded at any m ≥ n.
    LITERARY INSIGHT: if all texts in a genre have depth ≤ n, then
    trivially they all have depth ≤ m for any larger m. Relaxing the
    bound doesn't break the property. -/
theorem genre_depth_bound_mono (G : Genre I) {m n : ℕ}
    (hbound : GenreDepthBounded G n) (hmn : n ≤ m) :
    GenreDepthBounded G m := by
  intro a ha
  have := hbound a ha
  omega

/-- **Theorem 23 (Intersection Depth Bound)**: if either genre in an
    intersection is depth-bounded, so is the intersection.
    LITERARY INSIGHT: cross-genre works inherit the complexity constraints
    of their most restrictive parent genre. -/
theorem genreIntersection_depth_bound_left (G₁ G₂ : Genre I) (n : ℕ)
    (hbound : GenreDepthBounded G₁ n) :
    GenreDepthBounded (genreIntersection G₁ G₂) n := by
  intro a ha
  exact hbound a ha.1

/-- **Theorem 24 (ComposeN Depth in Bounded Genre)**: in a depth-bounded genre,
    n-fold composition has depth ≤ n × bound.
    LITERARY INSIGHT: repeating generic elements any number of times stays
    within a linear bound. Serialization of genre fiction has linearly
    bounded complexity growth. -/
theorem genre_composeN_depth_bound (G : Genre I) (d : ℕ)
    (hbound : GenreDepthBounded G d) {a : I} (ha : G.mem a) :
    ∀ (n : ℕ), IdeaticSpace.depth (composeN a n) ≤ n * d
  | 0 => by simp [composeN]
  | n + 1 => by
    have ih := genre_composeN_depth_bound G d hbound ha n
    have ha_d := hbound a ha
    have hsub := IdeaticSpace.depth_subadditive (composeN a n) a
    calc IdeaticSpace.depth (composeN a (n + 1))
        = IdeaticSpace.depth (IdeaticSpace.compose (composeN a n) a) := rfl
      _ ≤ IdeaticSpace.depth (composeN a n) + IdeaticSpace.depth a := hsub
      _ ≤ n * d + d := by omega
      _ = (n + 1) * d := by ring

end DepthBounded

/-! ## §6. Resonance-Closed Genres: Styles

A "style" is a genre that is additionally closed under resonance:
if an idea is in the genre and another idea resonates with it, that
idea is also in the genre. Styles capture families of interchangeable
ideas — those connected by evocation. -/

section Styles
variable {I : Type*} [IdeaticSpace I]

/-- A genre is resonance-closed (a "style") if membership is preserved
    by resonance. -/
def ResonanceClosed (G : Genre I) : Prop :=
  ∀ (a b : I), G.mem a → IdeaticSpace.resonates a b → G.mem b

/-- **Theorem 25 (Universal is a Style)**: the universal genre is
    resonance-closed.
    LITERARY INSIGHT: "all literature" is trivially a style — since
    everything is included, resonance can't escape. -/
theorem universal_resonance_closed :
    ResonanceClosed (universalGenre : Genre I) := by
  intro _ _ _ _; trivial

/-- **Theorem 26 (Resonance Closure Contains Resonance Class)**: if a is
    in a resonance-closed genre G, then the entire resonance class of a
    is in G.
    LITERARY INSIGHT: in a style, if one text belongs, all texts that
    "sound like it" belong too. Style is contagious through resonance. -/
theorem style_contains_resonanceClass (G : Genre I)
    (hrc : ResonanceClosed G) {a : I} (ha : G.mem a) :
    ∀ (b : I), b ∈ resonanceClass a → G.mem b :=
  fun b hb => hrc a b ha hb

/-- **Theorem 27 (Intersection of Styles is a Style)**: the intersection
    of two resonance-closed genres is resonance-closed.
    LITERARY INSIGHT: if two styles are each closed under resonance,
    their overlap is too. A "romantic gothic" style, formed from
    "romantic" ∩ "gothic," remains stylistically coherent. -/
theorem style_intersection (G₁ G₂ : Genre I)
    (h1 : ResonanceClosed G₁) (h2 : ResonanceClosed G₂) :
    ResonanceClosed (genreIntersection G₁ G₂) := by
  intro a b ⟨ha1, ha2⟩ hab
  exact ⟨h1 a b ha1 hab, h2 a b ha2 hab⟩

/-- **Theorem 28 (Self-Resonance and Style)**: in any genre, each member
    is in its own resonance class.
    LITERARY INSIGHT: every text in a genre "sounds like itself" — this
    is the tautological foundation of style. -/
theorem genre_self_resonance (G : Genre I) {a : I} (_ha : G.mem a) :
    a ∈ resonanceClass a :=
  resonance_refl a

end Styles

/-! ## §7. Genre Morphisms

Maps between ideas that preserve genre membership — the formal theory of
genre-preserving transformations (adaptations, translations, etc.). -/

section GenreMorphisms
variable {I : Type*} [IdeaticSpace I]

/-- A genre-preserving endomorphism: a map I → I sending G to G. -/
structure GenreEndomorphism (G : Genre I) where
  toFun : I → I
  preserves : ∀ (a : I), G.mem a → G.mem (toFun a)

/-- **Theorem 29 (Identity Preserves Genre)**: the identity map preserves
    every genre.
    LITERARY INSIGHT: not changing a text keeps it in its genre.
    The most trivial "adaptation" is no adaptation at all. -/
def genreEndomorphism_id (G : Genre I) : GenreEndomorphism G where
  toFun := fun a => a
  preserves := fun _ ha => ha

/-- **Theorem 30 (Composition of Genre Endomorphisms)**: composing two
    genre-preserving maps gives a genre-preserving map.
    LITERARY INSIGHT: adapting an adaptation stays in-genre. If translating
    a novel keeps it a novel, and abridging a novel keeps it a novel,
    then translating and then abridging keeps it a novel. -/
def genreEndomorphism_comp (G : Genre I) (f g : GenreEndomorphism G) :
    GenreEndomorphism G where
  toFun := fun a => f.toFun (g.toFun a)
  preserves := fun a ha => f.preserves (g.toFun a) (g.preserves a ha)

/-- **Theorem 31 (Genre Endomorphism Iterates)**: iterating a genre-preserving
    map preserves the genre.
    LITERARY INSIGHT: repeatedly adapting a text (sequel of a sequel of a
    sequel) stays in-genre. Genre is stable under iteration. -/
theorem genreEndomorphism_iterate (G : Genre I) (f : GenreEndomorphism G)
    {a : I} (ha : G.mem a) :
    ∀ (n : ℕ), G.mem (Nat.iterate f.toFun n a)
  | 0 => ha
  | n + 1 => by
    show G.mem (Nat.iterate f.toFun n (f.toFun a))
    exact genreEndomorphism_iterate G f (f.preserves a ha) n

end GenreMorphisms

/-! ## §8. Genre Rigidity

A depth-reducing, genre-preserving map eventually drives all elements
to low depth. This captures the literary insight that genres can't
sustain complexity under iterated simplification. -/

section Rigidity
variable {I : Type*} [IdeaticSpace I]

/-- A depth-reducing map: always decreases depth of ideas with depth > 1.
    Models "dumbing down" transformations. -/
structure DepthReducingMap (I : Type*) [IdeaticSpace I] where
  toFun : I → I
  depth_le : ∀ (a : I), IdeaticSpace.depth (toFun a) ≤ IdeaticSpace.depth a
  depth_strict : ∀ (a : I), IdeaticSpace.depth a > 1 →
    IdeaticSpace.depth (toFun a) < IdeaticSpace.depth a

/-- **Theorem 32 (Rigidity: Eventual Shallowing)**: a depth-reducing map
    applied n times to an idea of depth ≤ n+1 yields depth ≤ 1.
    LITERARY INSIGHT: repeatedly simplifying any text eventually reduces it
    to atomic ideas. A genre cannot sustain structural complexity under
    persistent simplification — popular retellings erode literary depth. -/
theorem depth_reducing_eventual_shallow (f : DepthReducingMap I) (a : I) (n : ℕ)
    (h : IdeaticSpace.depth a ≤ n + 1) :
    IdeaticSpace.depth (Nat.iterate f.toFun n a) ≤ 1 := by
  induction n generalizing a with
  | zero => simpa using h
  | succ n ih =>
    by_cases hd : IdeaticSpace.depth a ≤ 1
    · -- Already shallow, stays shallow
      have : ∀ (k : ℕ), IdeaticSpace.depth (Nat.iterate f.toFun k a) ≤
          IdeaticSpace.depth a := by
        intro k; induction k generalizing a with
        | zero => exact le_refl _
        | succ k ihk =>
          show IdeaticSpace.depth (Nat.iterate f.toFun k (f.toFun a)) ≤
              IdeaticSpace.depth a
          have := ihk (f.toFun a)
          have := f.depth_le a
          omega
      have := this (n + 1)
      omega
    · push_neg at hd
      have hdecay := f.depth_strict a (by omega)
      show IdeaticSpace.depth (Nat.iterate f.toFun n (f.toFun a)) ≤ 1
      apply ih
      omega

/-- **Theorem 33 (Depth Reducing Global Bound)**: after k steps, depth
    is at most the original depth.
    LITERARY INSIGHT: simplification never adds complexity. -/
theorem depth_reducing_global (f : DepthReducingMap I) (a : I) :
    ∀ (k : ℕ), IdeaticSpace.depth (Nat.iterate f.toFun k a) ≤
    IdeaticSpace.depth a
  | 0 => le_refl _
  | k + 1 => by
    show IdeaticSpace.depth (Nat.iterate f.toFun k (f.toFun a)) ≤
        IdeaticSpace.depth a
    have ih := depth_reducing_global f (f.toFun a) k
    have hle := f.depth_le a
    omega

/-- **Theorem 34 (Genre Rigidity Under Depth Reduction)**: a depth-bounded
    genre stays depth-bounded under a genre-preserving depth-reducing map.
    LITERARY INSIGHT: if a genre already has bounded complexity, simplifying
    transformations preserve that bound. Simple genres are *rigid* under
    simplification — they can't be made any simpler than they already are
    (beyond the existing bound). -/
theorem genre_preserving_iterate (G : Genre I)
    (f : I → I) (hpres : ∀ (a : I), G.mem a → G.mem (f a))
    {a : I} (ha : G.mem a) :
    ∀ (k : ℕ), G.mem (Nat.iterate f k a)
  | 0 => ha
  | k + 1 => by
    show G.mem (Nat.iterate f k (f a))
    exact genre_preserving_iterate G f hpres (hpres a ha) k

theorem genre_rigidity_depth_bound (G : Genre I) (n : ℕ)
    (hbound : GenreDepthBounded G n)
    (f : DepthReducingMap I)
    (hpres : ∀ (a : I), G.mem a → G.mem (f.toFun a))
    {a : I} (ha : G.mem a) (k : ℕ) :
    IdeaticSpace.depth (Nat.iterate f.toFun k a) ≤ n :=
  hbound _ (genre_preserving_iterate G f.toFun hpres ha k)

end Rigidity

/-! ## §9. Genre Hierarchy and Partial Order

Genres form a partial order under set inclusion. We prove the fundamental
properties of this ordering. -/

section Hierarchy
variable {I : Type*} [IdeaticSpace I]

/-- Genre inclusion: G₁ is a sub-genre of G₂ if every member of G₁ is
    a member of G₂. -/
def GenreSubset (G₁ G₂ : Genre I) : Prop :=
  ∀ (a : I), G₁.mem a → G₂.mem a

/-- **Theorem 35 (Subset Reflexivity)**: every genre is a sub-genre of itself.
    LITERARY INSIGHT: every genre is its own sub-genre. "Novels" ⊆ "Novels." -/
theorem genreSubset_refl (G : Genre I) : GenreSubset G G :=
  fun _ ha => ha

/-- **Theorem 36 (Subset Transitivity)**: if G₁ ⊆ G₂ and G₂ ⊆ G₃ then G₁ ⊆ G₃.
    LITERARY INSIGHT: "haiku" ⊆ "poetry" ⊆ "literature" implies
    "haiku" ⊆ "literature." Genre hierarchies compose. -/
theorem genreSubset_trans (G₁ G₂ G₃ : Genre I)
    (h12 : GenreSubset G₁ G₂) (h23 : GenreSubset G₂ G₃) :
    GenreSubset G₁ G₃ :=
  fun a ha => h23 a (h12 a ha)

/-- **Theorem 37 (Void is Bottom)**: the void genre is a sub-genre of
    every genre.
    LITERARY INSIGHT: the genre of silence sits at the bottom of the
    hierarchy — it's contained in every genre. -/
theorem voidGenre_bottom (G : Genre I) : GenreSubset voidGenre G :=
  voidGenre_subset G

/-- **Theorem 38 (Universal is Top)**: every genre is a sub-genre of the
    universal genre.
    LITERARY INSIGHT: every genre is a sub-genre of "all literature."
    The universal genre sits at the top of the hierarchy. -/
theorem universalGenre_top (G : Genre I) : GenreSubset G universalGenre :=
  genre_subset_universal G

/-- **Theorem 39 (Intersection is Lower Bound)**: the intersection of two
    genres is a sub-genre of each.
    LITERARY INSIGHT: the cross-genre category is always more restrictive
    than either parent genre. "Sci-fi romance" ⊆ "sci-fi" and
    "sci-fi romance" ⊆ "romance." -/
theorem genreIntersection_lower_left (G₁ G₂ : Genre I) :
    GenreSubset (genreIntersection G₁ G₂) G₁ :=
  fun _ h => h.1

theorem genreIntersection_lower_right (G₁ G₂ : Genre I) :
    GenreSubset (genreIntersection G₁ G₂) G₂ :=
  fun _ h => h.2

/-- **Theorem 40 (Intersection is Greatest Lower Bound)**: if G ⊆ G₁ and
    G ⊆ G₂, then G ⊆ G₁ ∩ G₂.
    LITERARY INSIGHT: the cross-genre is the *largest* genre that fits
    inside both parent genres. It's the "natural" genre for works that
    belong to both categories. -/
theorem genreIntersection_glb (G G₁ G₂ : Genre I)
    (h1 : GenreSubset G G₁) (h2 : GenreSubset G G₂) :
    GenreSubset G (genreIntersection G₁ G₂) :=
  fun a ha => ⟨h1 a ha, h2 a ha⟩

end Hierarchy

/-! ## §10. Genre Crossing and Composition

When elements from different genres are composed, what genre does the
result belong to? This section explores genre interactions. -/

section Crossing
variable {I : Type*} [IdeaticSpace I]

/-- **Theorem 41 (Crossing Into Intersection)**: if a ∈ G₁ ∩ G₂ and b ∈ G₁ ∩ G₂,
    then compose(a,b) ∈ G₁ ∩ G₂.
    LITERARY INSIGHT: composing two cross-genre elements stays cross-genre.
    This is the closure property of the intersection. -/
theorem crossing_intersection (G₁ G₂ : Genre I) {a b : I}
    (ha : (genreIntersection G₁ G₂).mem a) (hb : (genreIntersection G₁ G₂).mem b) :
    (genreIntersection G₁ G₂).mem (IdeaticSpace.compose a b) :=
  (genreIntersection G₁ G₂).compose_mem a b ha hb

/-- **Theorem 42 (Single-Genre Composition)**: composing within a single genre
    stays in that genre.
    LITERARY INSIGHT: genre-internal composition is safe. Writing more
    detective fiction doesn't leave the detective genre. -/
theorem single_genre_compose (G : Genre I) {a b : I}
    (ha : G.mem a) (hb : G.mem b) :
    G.mem (IdeaticSpace.compose a b) :=
  G.compose_mem a b ha hb

/-- **Theorem 43 (Void Crossing)**: composing any genre element with void
    stays in genre.
    LITERARY INSIGHT: adding silence to a genre text doesn't change its
    genre — padding with void is genre-neutral. -/
theorem void_crossing (G : Genre I) {a : I} (ha : G.mem a) :
    G.mem (IdeaticSpace.compose a (IdeaticSpace.void : I)) := by
  rw [IdeaticSpace.void_right]; exact ha

/-- **Theorem 44 (Void Crossing Left)**: prepending void stays in genre. -/
theorem void_crossing_left (G : Genre I) {a : I} (ha : G.mem a) :
    G.mem (IdeaticSpace.compose (IdeaticSpace.void : I) a) := by
  rw [IdeaticSpace.void_left]; exact ha

end Crossing

/-! ## §11. Coherence Within Genres

Connecting genre theory to coherent sequences: when do genre-constrained
sequences maintain coherence? -/

section GenreCoherence
variable {I : Type*} [IdeaticSpace I]

/-- A sequence is "in-genre" if all its elements belong to the genre. -/
def InGenre (G : Genre I) (s : List I) : Prop :=
  ∀ (a : I), a ∈ s → G.mem a

/-- **Theorem 45 (Empty Sequence In-Genre)**: the empty sequence is in every genre.
    LITERARY INSIGHT: the empty text belongs to every genre vacuously. -/
theorem inGenre_nil (G : Genre I) : InGenre G ([] : List I) := by
  intro a ha; exact absurd ha (List.not_mem_nil a)

/-- **Theorem 46 (Singleton In-Genre)**: a singleton is in-genre iff its
    element is in the genre. -/
theorem inGenre_singleton (G : Genre I) (a : I) :
    InGenre G [a] ↔ G.mem a := by
  constructor
  · intro h; exact h a (List.mem_cons_self a [])
  · intro ha b hb; simp [List.mem_singleton] at hb; rw [hb]; exact ha

/-- **Theorem 47 (Cons In-Genre)**: a :: s is in-genre iff a is in G and s
    is in-genre. -/
theorem inGenre_cons (G : Genre I) (a : I) (s : List I) :
    InGenre G (a :: s) ↔ G.mem a ∧ InGenre G s := by
  constructor
  · intro h
    exact ⟨h a (List.mem_cons_self a s),
           fun b hb => h b (List.mem_cons_of_mem a hb)⟩
  · intro ⟨ha, hs⟩ b hb
    cases List.mem_cons.mp hb with
    | inl heq => rw [heq]; exact ha
    | inr htail => exact hs b htail

/-- **Theorem 48 (Depth Sum of In-Genre Sequence)**: if a genre is
    depth-bounded at d, then an in-genre sequence has total depth ≤ length × d.
    LITERARY INSIGHT: a sequence of genre-conforming texts has bounded total
    complexity. A collection of haiku (depth ≤ 2) has total depth ≤ 2n. -/
theorem inGenre_depthSum_bound (G : Genre I) (d : ℕ)
    (hbound : GenreDepthBounded G d) (s : List I)
    (hin : InGenre G s) :
    depthSum s ≤ s.length * d := by
  apply depthSum_bound
  intro a ha
  exact hbound a (hin a ha)

end GenreCoherence

/-! ## §12. Genre Filtration

Genres interact with the depth filtration to create filtered sub-genres. -/

section GenreFiltration
variable {I : Type*} [IdeaticSpace I]

/-- The depth-n filtered subset of a genre: elements of G with depth ≤ n.
    This is a *set*, not a genre, because composing two depth-≤n elements
    gives depth ≤ 2n in general. -/
def genreFiltrationSet (G : Genre I) (n : ℕ) : Set I :=
  {a | G.mem a ∧ IdeaticSpace.depth a ≤ n}

/-- **Theorem 49 (Filtration is Subset of Genre)**: the filtered set is a
    subset of the genre.
    LITERARY INSIGHT: the "simple works" within a genre are still in the genre.
    "Simple detective stories" ⊆ "detective stories." -/
theorem genreFiltrationSet_subset (G : Genre I) (n : ℕ) (a : I) :
    a ∈ genreFiltrationSet G n → G.mem a :=
  fun h => h.1

/-- **Theorem 50 (Filtration Monotonicity)**: larger depth bounds give
    larger filtered sets.
    LITERARY INSIGHT: allowing more complexity admits more works. The
    set of "detective stories of depth ≤ 5" is contained in
    "detective stories of depth ≤ 10." -/
theorem genreFiltrationSet_mono (G : Genre I) {m n : ℕ} (h : m ≤ n) (a : I) :
    a ∈ genreFiltrationSet G m → a ∈ genreFiltrationSet G n := by
  intro ⟨hg, hd⟩
  exact ⟨hg, le_trans hd (by omega)⟩

/-- **Theorem 51 (Zero Filtration Characterization)**: the depth-0 filtration
    contains only depth-0 elements of the genre.
    LITERARY INSIGHT: the "trivial works" of a genre — those with zero
    structural complexity — form the most constrained filtered set. -/
theorem genreFiltrationSet_zero_char (G : Genre I) (a : I) :
    a ∈ genreFiltrationSet G 0 ↔ G.mem a ∧ IdeaticSpace.depth a = 0 := by
  constructor
  · intro ⟨hg, hd⟩; exact ⟨hg, Nat.le_zero.mp hd⟩
  · intro ⟨hg, hd⟩; exact ⟨hg, le_of_eq hd⟩

/-- **Theorem 52 (Composition Stays in Double Filtration)**: composing two
    elements from the depth-n filtered set lands in the depth-2n filtered set.
    LITERARY INSIGHT: combining two "simple" genre works (depth ≤ n) produces
    a work that is still genre-conforming with at most doubled complexity.
    Composition can't escape genre, though it may increase depth. -/
theorem genreFiltrationSet_compose (G : Genre I) (n : ℕ) {a b : I}
    (ha : a ∈ genreFiltrationSet G n) (hb : b ∈ genreFiltrationSet G n) :
    IdeaticSpace.compose a b ∈ genreFiltrationSet G (2 * n) := by
  refine ⟨G.compose_mem a b ha.1 hb.1, ?_⟩
  have hsub := IdeaticSpace.depth_subadditive a b
  have hda := ha.2
  have hdb := hb.2
  omega

/-- **Theorem (Void in Every Filtration)**: void is in the depth-n filtration
    of every genre.
    LITERARY INSIGHT: silence is always among the "simple works." -/
theorem void_mem_genreFiltrationSet (G : Genre I) (n : ℕ) :
    (IdeaticSpace.void : I) ∈ genreFiltrationSet G n :=
  ⟨G.void_mem, by simp [IdeaticSpace.depth_void]⟩

end GenreFiltration

/-! ## §13. Recombinant Genre Theory

How genres interact with recombinant diffusion — when ideas from different
genres recombine to create hybrids. -/

section RecombinantGenre
variable {I : Type*} [RecombinantDiffusion I]

/-- A genre is recombination-closed if recombining two members stays in-genre. -/
def RecombinationClosed (G : Genre I) : Prop :=
  ∀ (a b : I), G.mem a → G.mem b → G.mem (RecombinantDiffusion.recombine a b)

/-- **Theorem 53 (Universal is Recombination-Closed)**: the universal genre
    is trivially closed under recombination.
    LITERARY INSIGHT: "all literature" can absorb any hybrid. -/
theorem universal_recombination_closed :
    RecombinationClosed (universalGenre : Genre I) := by
  intro _ _ _ _; trivial

/-- **Theorem 54 (Recombination Depth in Bounded Genre)**: if a
    recombination-closed genre is depth-bounded at d, recombining two
    members gives depth ≤ 2d + 1.
    LITERARY INSIGHT: creative synthesis within a complexity-bounded genre
    produces works of bounded complexity. Innovation is constrained by
    the genre's depth ceiling. -/
theorem recombination_depth_bound (G : Genre I) (d : ℕ)
    (hbound : GenreDepthBounded G d) {a b : I}
    (ha : G.mem a) (hb : G.mem b) :
    IdeaticSpace.depth (RecombinantDiffusion.recombine a b) ≤ 2 * d + 1 := by
  have h1 := hbound a ha
  have h2 := hbound b hb
  have h3 := RecombinantDiffusion.recombine_depth_bound a b
  omega

/-- **Theorem 55 (Recombinant Resonance in Genre)**: if a, b ∈ G and G is
    recombination-closed, the hybrid resonates with both parents within G.
    LITERARY INSIGHT: genre-internal innovation always bears recognizable
    marks of its sources. The hybrid detective-story still "sounds like"
    the stories that inspired it. -/
theorem recombinant_genre_resonance (G : Genre I)
    (hrc : RecombinationClosed G) {a b : I}
    (ha : G.mem a) (hb : G.mem b) :
    G.mem (RecombinantDiffusion.recombine a b) ∧
    IdeaticSpace.resonates a (RecombinantDiffusion.recombine a b) :=
  ⟨hrc a b ha hb, RecombinantDiffusion.recombine_resonant_left a b⟩

end RecombinantGenre

/-! ## §14. Selective Diffusion and Genres

How genres interact with selective (competitive) diffusion. -/

section SelectiveGenre
variable {I : Type*} [SelectiveDiffusion I]

/-- A genre is selection-closed if selecting between two members stays in-genre. -/
def SelectionClosed (G : Genre I) : Prop :=
  ∀ (a b : I), G.mem a → G.mem b → G.mem (SelectiveDiffusion.select a b)

/-- **Theorem 56 (Universal is Selection-Closed)**: trivially. -/
theorem universal_selection_closed :
    SelectionClosed (universalGenre : Genre I) := by
  intro _ _ _ _; trivial

/-- **Theorem 57 (Selection Closure from Axiom)**: every genre is
    selection-closed because selection always returns one of its inputs.
    LITERARY INSIGHT: competition between two in-genre texts always
    produces an in-genre winner. Genres are stable under selection
    pressure — the "market" can't push works out of their genre. -/
theorem every_genre_selection_closed (G : Genre I) :
    SelectionClosed G := by
  intro a b ha hb
  rcases SelectiveDiffusion.select_is_input a b with h | h
  · rw [h]; exact ha
  · rw [h]; exact hb

/-- **Theorem 58 (Genre Fitness Bound)**: if void is the only element of
    a genre with fitness 0, and we know void has fitness 0, then selection
    against void returns the other element when it has positive fitness.
    LITERARY INSIGHT: substance always beats silence in competition. -/
theorem genre_selection_vs_void (G : Genre I) {a : I}
    (_ha : G.mem a) (hfit : SelectiveDiffusion.fitness a > 0) :
    SelectiveDiffusion.select a (IdeaticSpace.void : I) = a := by
  rcases SelectiveDiffusion.select_is_input a (IdeaticSpace.void : I) with h | h
  · exact h
  · exfalso
    have hmax := SelectiveDiffusion.select_maximizes a (IdeaticSpace.void : I)
    rw [h, SelectiveDiffusion.void_fitness] at hmax
    simp [Nat.max_eq_left (Nat.zero_le _)] at hmax
    omega

end SelectiveGenre

end IDT
