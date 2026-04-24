import FormalAnthropology.IDT_Foundations

/-!
# Signalling Games in IDT — Chapter 15: Repertoire Curation and Museum Theory

**Anthropological motivation.** The receiver is not passive. Every mind
*curates* its repertoire: selecting which ideas to retain, which to discard,
and which new ideas to admit. This is the formal structure of:

- **Museum curation**: deciding which artifacts to display (and which to archive)
- **Education**: expanding the student's repertoire with new concepts
- **Censorship**: filtering the repertoire to remove "dangerous" ideas
- **Bourdieu's cultural capital**: the accumulated, curated stock of ideas
  that determines one's interpretive capacity

This chapter formalizes repertoire curation:

- **curate**: filter a repertoire by a predicate
- **expand**: add a new idea to the front of a repertoire
- Theorems on how curation and expansion affect interpretation depth,
  repertoire size, and the depthSum invariant

We prove 18 theorems connecting curation to museum theory, education
policy, censorship dynamics, and the political economy of knowledge.

## 18 Theorems, 0 Sorries
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.Signal.Ch15

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- Curate a repertoire: keep only ideas satisfying predicate p.
    This models selective retention — the museum curator choosing
    which artifacts to display, the teacher choosing which concepts
    to emphasize, the censor choosing which ideas to permit. -/
def curate (rep : List I) (p : I → Bool) : List I :=
  rep.filter p

/-- Expand a repertoire by adding a new idea to the front.
    This models learning: acquiring a new concept, encountering
    a new artifact, or absorbing a new cultural input. -/
def expand (rep : List I) (new_idea : I) : List I :=
  new_idea :: rep

/-- Interpretation: when a receiver with repertoire `rep` encounters signal `s`,
    they produce `[compose(r₁, s), compose(r₂, s), …]`. -/
def interpret (rep : List I) (signal : I) : List I :=
  rep.map (fun r => IdeaticSpace.compose r signal)

/-! ## §2. Curation Fundamentals -/

/-- **Theorem 15.1 (Curation Preserves Membership).**
    Every element of the curated repertoire was in the original.

    *Anthropological significance*: A museum can only display what it
    owns. Curation is selection, not creation — the formal basis of
    the archivist's constraint. You cannot curate what you don't have. -/
theorem curate_subset (rep : List I) (p : I → Bool) :
    ∀ x ∈ curate rep p, x ∈ rep := by
  intro x hx
  exact List.mem_of_mem_filter hx

/-- **Theorem 15.2 (Curation Reduces Length).**
    The curated repertoire is never longer than the original.

    *Anthropological significance*: Curation only removes — it never
    inflates. A censored library is always smaller than the uncensored
    original. This formalizes the "information loss" inherent in any
    act of selection. -/
theorem curate_length_le (rep : List I) (p : I → Bool) :
    (curate rep p).length ≤ rep.length := by
  exact List.length_filter_le p rep

/-- **Theorem 15.3 (Vacuous Curation is Empty).**
    Filtering by a predicate that rejects everything yields the empty list.

    *Anthropological significance*: Total censorship — rejecting every
    idea — produces cultural void. This is the formal limit of
    suppression: complete censorship = complete cultural erasure. -/
theorem vacuous_curate (rep : List I) :
    curate rep (fun _ => false) = [] := by
  simp [curate]

/-- **Theorem 15.4 (Universal Curation is Identity).**
    Filtering by a predicate that accepts everything yields the original.

    *Anthropological significance*: A museum that displays everything
    is just a warehouse. "Curating" with no selection criterion is
    structurally equivalent to no curation at all — the formal basis
    of the "unedited" archive. -/
theorem universal_curate (rep : List I) :
    curate rep (fun _ => true) = rep := by
  simp [curate]

/-! ## §3. Expansion Fundamentals -/

/-- **Theorem 15.5 (Expansion Increases Length).**
    Adding a new idea increases the repertoire by exactly one.

    *Anthropological significance*: Each learning event adds exactly
    one new schema. Education is *incremental* — you learn one thing
    at a time. This constrains theories of "epiphany" or "gestalt
    shift" to be single-idea additions in the formal model. -/
theorem expand_length (rep : List I) (new_idea : I) :
    (expand rep new_idea).length = rep.length + 1 := by
  simp [expand]

/-- **Theorem 15.6 (New Idea is in Expanded Repertoire).**
    The newly added idea is a member of the expanded repertoire.

    *Anthropological significance*: What you learn, you possess.
    The student who has been taught a concept *has* that concept
    in their repertoire — the structural basis of education as
    repertoire expansion. -/
theorem new_idea_mem_expand (rep : List I) (new_idea : I) :
    new_idea ∈ expand rep new_idea := by
  simp [expand]

/-- **Theorem 15.7 (Old Ideas Survive Expansion).**
    All ideas in the original repertoire are in the expanded version.

    *Anthropological significance*: Learning doesn't erase prior
    knowledge. The student who learns calculus still remembers
    arithmetic. Expansion is *monotone* — repertoires only grow. -/
theorem old_ideas_survive (rep : List I) (new_idea : I) :
    ∀ x ∈ rep, x ∈ expand rep new_idea := by
  intro x hx
  exact List.mem_cons_of_mem _ hx

/-! ## §4. Curation and Interpretation -/

/-- **Theorem 15.8 (Curated Interpretation is Sublist).**
    Interpreting a curated repertoire gives a subset of interpretations
    compared to the full repertoire's length.

    *Anthropological significance*: A censored mind produces fewer
    interpretations. The number of possible readings of a text is
    bounded by the reader's (curated) repertoire size. A narrower
    education yields fewer perspectives. -/
theorem curated_interp_length (rep : List I) (p : I → Bool) (s : I) :
    (interpret (curate rep p) s).length ≤ (interpret rep s).length := by
  simp [interpret, curate]
  exact List.length_filter_le p rep

/-- **Theorem 15.9 (Empty Curation Yields No Interpretation).**
    If curation removes everything, there are no interpretations.

    *Anthropological significance*: The culturally emptied mind
    cannot interpret anything. Total censorship followed by signal
    reception = zero interpretive output. The "blank slate after
    brainwashing" theorem. -/
theorem empty_curate_no_interp (rep : List I) (s : I) :
    interpret (curate rep (fun _ => false)) s = [] := by
  simp [interpret, vacuous_curate]

/-! ## §5. Expansion and Interpretation -/

/-- **Theorem 15.10 (Expanded Interpretation Adds One).**
    Interpreting an expanded repertoire produces one more interpretation
    than the original.

    *Anthropological significance*: Each new idea in the repertoire
    adds exactly one new interpretive possibility. Education's return
    is precisely one new perspective per concept learned — the
    fundamental unit of *Bildung*. -/
theorem expanded_interp_length (rep : List I) (new_idea s : I) :
    (interpret (expand rep new_idea) s).length = (interpret rep s).length + 1 := by
  simp [interpret, expand]

/-- **Theorem 15.11 (Expansion Interpretation Structure).**
    Interpreting an expanded repertoire = new interpretation :: old interpretations.

    *Anthropological significance*: The new concept's interpretation
    appears first, followed by all prior interpretations unchanged.
    Learning adds a new lens without distorting existing ones — the
    "additive" model of education. -/
theorem expanded_interp_structure (rep : List I) (new_idea s : I) :
    interpret (expand rep new_idea) s =
    IdeaticSpace.compose new_idea s :: interpret rep s := rfl

/-- **Theorem 15.12 (Void Expansion Doesn't Change Interpretations).**
    Adding void to the repertoire adds compose(void, s) = s as a new
    interpretation, but all other interpretations are unchanged.

    *Anthropological significance*: Adding "empty receptivity" (the
    Keatsian negative capability) to one's repertoire adds the raw
    signal as a new interpretation. The educationally valuable
    "empty slot" lets you see the signal unmediated. -/
theorem void_expansion_raw_signal (rep : List I) (s : I) :
    interpret (expand rep (IdeaticSpace.void : I)) s =
    s :: interpret rep s := by
  simp [expanded_interp_structure, IDT.void_left]

/-! ## §6. DepthSum Bounds -/

/-- **Theorem 15.13 (Curated DepthSum Bound).**
    The depthSum of a curated repertoire ≤ depthSum of the original.

    *Anthropological significance*: Curation (selection, censorship)
    can only reduce total cultural depth. A museum that hides artifacts
    loses depth; a censored library is shallower than the uncensored
    one. Information destruction is irreversible in the depth metric. -/
theorem curated_depthSum_le (rep : List I) (p : I → Bool) :
    depthSum (curate rep p) ≤ depthSum rep := by
  induction rep with
  | nil => simp [curate, depthSum]
  | cons r rest ih =>
    rw [depthSum_cons]
    simp only [curate, List.filter] at ih ⊢
    split
    · rw [depthSum_cons]
      have := ih
      linarith
    · have := ih
      linarith

/-- **Theorem 15.14 (Expanded DepthSum Bound).**
    The depthSum of an expanded repertoire = depthSum + depth(new_idea).

    *Anthropological significance*: Each new idea adds exactly its
    depth to the total cultural capital. Education is a *linear*
    accumulation of depth — Bourdieu's cultural capital grows
    additively with each new acquisition. -/
theorem expanded_depthSum (rep : List I) (new_idea : I) :
    depthSum (expand rep new_idea) = IdeaticSpace.depth new_idea + depthSum rep := by
  simp [expand, depthSum_cons]

/-- **Theorem 15.15 (Void Expansion DepthSum).**
    Adding void to the repertoire doesn't change depthSum.

    *Anthropological significance*: Adding "nothing" to one's cultural
    stock adds zero depth. The void is costless to maintain in
    the repertoire — the formal basis of "keeping an open mind"
    being free in the depth metric. -/
theorem void_expansion_depthSum (rep : List I) :
    depthSum (expand rep (IdeaticSpace.void : I)) = depthSum rep := by
  rw [expanded_depthSum, IdeaticSpace.depth_void, Nat.zero_add]

/-! ## §7. Structural Curation Theorems -/

/-- **Theorem 15.16 (Double Curation is Single Curation).**
    Curating a curated repertoire by the same predicate is idempotent.

    *Anthropological significance*: Censoring an already-censored
    library by the same criterion has no further effect. The
    "diminishing returns" of redundant censorship — once you've
    removed all "heretical" books, removing them again changes nothing. -/
theorem curate_idempotent (rep : List I) (p : I → Bool) :
    curate (curate rep p) p = curate rep p := by
  simp [curate, List.filter_filter, Bool.and_self]

/-- **Theorem 15.17 (Expand Then Curate Accepting).**
    If the new idea passes the predicate, expanding then curating
    keeps it.

    *Anthropological significance*: If a newly acquired idea passes
    the censorship test, it survives curation. "Approved learning"
    is permanent — the accepted idea stays in the repertoire through
    subsequent curation rounds. -/
theorem expand_curate_keeps {new_idea : I} {p : I → Bool}
    (hp : p new_idea = true) (rep : List I) :
    curate (expand rep new_idea) p = new_idea :: curate rep p := by
  simp [expand, curate, List.filter, hp]

/-- **Theorem 15.18 (Expand Then Curate Rejecting).**
    If the new idea fails the predicate, expanding then curating
    removes it — as if it was never learned.

    *Anthropological significance*: Ideas that fail the censorship
    test are immediately purged. The "forbidden knowledge" theorem:
    learning something that the regime rejects is structurally
    equivalent to never having learned it, after curation. This
    formalizes the futility of teaching banned concepts in
    totalitarian educational systems. -/
theorem expand_curate_removes {new_idea : I} {p : I → Bool}
    (hp : p new_idea = false) (rep : List I) :
    curate (expand rep new_idea) p = curate rep p := by
  simp [expand, curate, List.filter, hp]

end IDT.Signal.Ch15
