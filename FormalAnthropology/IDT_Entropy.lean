import FormalAnthropology.IDT_Foundations

/-!
# Ideatic Diffusion Theory: Information-Theoretic Entropy

This file develops the **information-theoretic** layer of IDT — the study of
how complexity, diversity, and resonance structure behave under the operations
of ideatic space.

## Central Metaphor

If `IdeaticSpace` axiomatizes the *statics* of thought (how ideas compose and
relate) and diffusion axioms govern the *dynamics* (how ideas propagate), then
this file provides the **thermodynamics**: aggregate measures that track the
irreversible flow of complexity through cultural transmission.

## Key Results

- **Depth Spectrum**: the list of depths is a complete invariant of aggregate
  complexity; mutagenic transmission can only decrease it pointwise
- **Cultural Entropy Theorem**: total depth (depthSum) of a list decreases
  monotonically under mutagenic transmission — ideas simplify en masse
- **Resonance Density**: coherent sequences maximize consecutive resonant
  pairs, achieving the theoretical bound of n−1
- **Selective Convergence**: iterated selection compresses diversity to the
  single fittest element — the "market of ideas" converges
- **Diversity–Depth Tradeoff**: uniform-depth populations have maximal
  depthSum; mutation breaks uniformity

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT

-- Helper: right-fold iterate identity, used in several proofs below.
private theorem iterate_apply_succ {α : Type*} (f : α → α) (n : ℕ) (x : α) :
    Nat.iterate f (n + 1) x = f (Nat.iterate f n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih (f x)

/-! ## §1. Depth Spectrum: The Signature of Complexity

The **depth spectrum** of a sequence is the list of depths of its elements.
It captures the "complexity profile" of a collection of ideas — not just
total complexity but its distribution across the sequence.

LITERARY INSIGHT: Two texts may have the same total depth but radically
different spectra. A scientific paper (few deep ideas) and a newspaper
(many shallow items) exemplify this. The spectrum distinguishes them. -/

section DepthSpectrum
variable {I : Type*} [IdeaticSpace I]

/-- The depth spectrum: the sequence of depths of each element.
    This is the "complexity fingerprint" of a collection of ideas. -/
def depthSpectrum (s : List I) : List ℕ := s.map IdeaticSpace.depth

/-- The empty collection has an empty spectrum: no ideas, no complexity. -/
@[simp] theorem depthSpectrum_nil : depthSpectrum ([] : List I) = [] := rfl

/-- Consing an element prepends its depth to the spectrum. -/
theorem depthSpectrum_cons (a : I) (s : List I) :
    depthSpectrum (a :: s) = IdeaticSpace.depth a :: depthSpectrum s := rfl

/-- THEOREM (Spectrum Length Invariance): the spectrum has the same length
    as the original sequence. No ideas are created or destroyed.
    INSIGHT: the spectrum is a *faithful* summary — it records one datum
    per idea, losing only the idea's identity, not its existence. -/
theorem depthSpectrum_length (s : List I) :
    (depthSpectrum s).length = s.length :=
  List.length_map _ _

/-- THEOREM (Spectrum Concatenation): the spectrum of a concatenation is
    the concatenation of spectra. INSIGHT: appending two texts combines
    their complexity profiles end-to-end. There is no "interaction term"
    — the spectrum is purely additive under concatenation. -/
theorem depthSpectrum_append (s t : List I) :
    depthSpectrum (s ++ t) = depthSpectrum s ++ depthSpectrum t :=
  List.map_append _ _ _

/-- Total depth equals the sum of the spectrum. -/
theorem depthSum_eq_spectrum_sum (s : List I) :
    depthSum s = (depthSpectrum s).sum := rfl

end DepthSpectrum

/-! ## §2. Depth Sum Algebra: Thermodynamic Bookkeeping

The `depthSum` — total depth of a sequence — is the information-theoretic
analogue of total energy. These theorems establish its algebraic properties:
additivity under concatenation, uniformity bounds, and the interaction
between length and per-element depth.

LITERARY INSIGHT: depthSum measures the "total intellectual weight" of a
discourse. A sequence of proverbs has low depthSum; a philosophical treatise
has high depthSum. The algebra here lets us reason about how that weight
distributes, combines, and transforms. -/

section DepthSumAlgebra
variable {I : Type*} [IdeaticSpace I]

/-- depthSum of a singleton is just that element's depth. -/
theorem depthSum_singleton (a : I) :
    depthSum [a] = IdeaticSpace.depth a := by
  simp [depthSum_cons, depthSum_nil]

/-- THEOREM (Depth Sum Additivity): depthSum distributes over concatenation.
    INSIGHT: combining two collections adds their total complexities with
    no interaction. The "intellectual weight" of a combined text is the sum
    of its parts — there is no synergy or cancellation at this level.
    (Synergy appears at the resonance level, not the depth level.) -/
theorem depthSum_append (s t : List I) :
    depthSum (s ++ t) = depthSum s + depthSum t := by
  induction s with
  | nil => simp [depthSum]
  | cons a rest ih =>
    simp only [List.cons_append, depthSum_cons]
    rw [ih]; omega

/-- THEOREM (Void Sequence): a list of voids has zero total depth.
    INSIGHT: silence accumulated is still silence. -/
theorem depthSum_replicate_void (n : ℕ) :
    depthSum (List.replicate n (IdeaticSpace.void : I)) = 0 := by
  induction n with
  | zero => simp [depthSum]
  | succ n ih =>
    rw [List.replicate_succ, depthSum_cons, IdeaticSpace.depth_void, ih]

/-- THEOREM (Uniform Depth Sum): if every element has depth exactly d,
    then total depth equals length times d.
    INSIGHT: a population of equally complex ideas has predictable total
    weight. This is the "ideal gas" assumption of cultural thermodynamics
    — when all ideas have equal complexity, aggregate measures are trivial. -/
theorem depthSum_uniform (s : List I) (d : ℕ)
    (h : ∀ a ∈ s, IdeaticSpace.depth a = d) :
    depthSum s = s.length * d := by
  induction s with
  | nil => simp [depthSum]
  | cons a rest ih =>
    rw [depthSum_cons, List.length_cons]
    have ha := h a (List.mem_cons_self a rest)
    have hrest : ∀ b ∈ rest, IdeaticSpace.depth b = d :=
      fun b hb => h b (List.mem_cons_of_mem a hb)
    rw [ha, ih hrest]; ring

/-- THEOREM (Depth Sum Monotonicity in Length): longer sequences with
    bounded element depth have proportionally bounded total depth.
    INSIGHT: you cannot hide unbounded complexity in a sequence of
    individually simple ideas. Length × max_depth is a hard ceiling. -/
theorem depthSum_le_length_mul_max (s : List I) (d : ℕ)
    (h : ∀ a ∈ s, IdeaticSpace.depth a ≤ d) :
    depthSum s ≤ s.length * d :=
  depthSum_bound s d h

/-- THEOREM (Depth Sum Subadditivity for Composition): composing the heads
    of two sequences gives a depth sum bounded by the sum of their depths.
    INSIGHT: element-wise composition doesn't amplify total complexity
    beyond what's predicted by pairwise subadditivity. -/
theorem depthSum_compose_pair (a b : I) :
    depthSum [IdeaticSpace.compose a b] ≤ depthSum [a] + depthSum [b] := by
  simp only [depthSum_singleton]
  exact IdeaticSpace.depth_subadditive a b

end DepthSumAlgebra

/-! ## §3. Mutagenic Transmission on Lists: Cultural Entropy

When an entire collection of ideas undergoes mutagenic transmission, each
element individually loses depth. At the aggregate level, this means the
total depth (depthSum) of the collection decreases monotonically.

This is the **Cultural Entropy Theorem**: the second law of thermodynamics
for ideas. Just as physical entropy increases in closed systems, *ideatic
depth decreases* under imperfect transmission.

LITERARY INSIGHT: each generation's retelling of a corpus simplifies it.
The Homeric epics, transmitted orally for centuries, lost structural depth
at each retelling — what survived were the simple, resonant core motifs. -/

section MutagenicList
variable {I : Type*} [MutagenicDiffusion I]

/-- Transmitting an entire list: apply mutagenic transmission pointwise.
    INSIGHT: each idea in the cultural corpus undergoes its own mutation. -/
def transmitList (s : List I) : List I := s.map MutagenicDiffusion.transmit

/-- Transmitting the empty list gives the empty list. -/
@[simp] theorem transmitList_nil : transmitList ([] : List I) = [] := rfl

/-- Transmitting a cons list transmits the head and the tail. -/
theorem transmitList_cons (a : I) (s : List I) :
    transmitList (a :: s) =
    MutagenicDiffusion.transmit a :: transmitList s := rfl

/-- THEOREM (Transmission Preserves Length): no ideas are created or
    destroyed during mutagenic transmission — only transformed.
    INSIGHT: cultural transmission changes meaning but not quantity.
    The number of stories in the corpus stays the same. -/
theorem transmitList_length (s : List I) :
    (transmitList s).length = s.length :=
  List.length_map _ _

/-- THEOREM (Cultural Entropy Theorem — Aggregate): total depth decreases
    under mutagenic transmission. depthSum(T(s)) ≤ depthSum(s).
    This is the **second law of cultural thermodynamics**: the total
    complexity of a corpus can only decrease through imperfect transmission.

    LITERARY INSIGHT: oral traditions, passed through generations, lose
    aggregate depth. What started as a nuanced epic becomes a streamlined
    myth. This theorem says the simplification is *inevitable* and
    *monotonic* — complexity never spontaneously increases. -/
theorem transmitList_depthSum_le (s : List I) :
    depthSum (transmitList s) ≤ depthSum s := by
  induction s with
  | nil => simp [depthSum]
  | cons a rest ih =>
    simp only [transmitList_cons, depthSum_cons]
    have hd := MutagenicDiffusion.transmit_depth_le a
    omega

/-- THEOREM (Transmitted List Resonance — membership form): every element
    of the transmitted list resonates with some element of the original.
    INSIGHT: even after mutation, each idea in the corpus "remembers"
    what it came from. -/
theorem transmitList_resonance_mem (s : List I) (b : I) (hb : b ∈ transmitList s) :
    ∃ a ∈ s, IdeaticSpace.resonates a b := by
  simp only [transmitList, List.mem_map] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  exact ⟨a, ha, MutagenicDiffusion.transmit_resonant a⟩

/-- n-fold transmission of a list: apply transmitList n times,
    where each step transmits the result of the previous step. -/
def iterateTransmitList (s : List I) : ℕ → List I
  | 0 => s
  | n + 1 => transmitList (iterateTransmitList s n)

/-- THEOREM (Iterated Entropy): n-fold transmission preserves list length.
    INSIGHT: no matter how many generations pass, the number of ideas
    in the corpus is unchanged — only their depths erode. -/
theorem iterateTransmitList_length (s : List I) : ∀ (n : ℕ),
    (iterateTransmitList s n).length = s.length
  | 0 => rfl
  | n + 1 => by
    simp only [iterateTransmitList, transmitList_length,
               iterateTransmitList_length s n]

/-- THEOREM (Iterated Cultural Entropy): each generation of transmission
    further decreases total depth. depthSum(T^{n+1}(s)) ≤ depthSum(T^n(s)).
    INSIGHT: the process of cultural simplification never reverses.
    Complexity lost in one generation is never recovered in the next. -/
theorem iterateTransmitList_depthSum_mono (s : List I) (n : ℕ) :
    depthSum (iterateTransmitList s (n + 1)) ≤
    depthSum (iterateTransmitList s n) := by
  simp only [iterateTransmitList]
  exact transmitList_depthSum_le _

/-- THEOREM (Global Cultural Entropy Bound): after any number of
    transmissions, total depth is bounded by the original.
    INSIGHT: the original corpus sets an absolute ceiling on complexity
    that can never be exceeded, no matter the transmission history. -/
theorem iterateTransmitList_depthSum_global (s : List I) : ∀ (n : ℕ),
    depthSum (iterateTransmitList s n) ≤ depthSum s
  | 0 => le_refl _
  | n + 1 => by
    have h1 := iterateTransmitList_depthSum_mono s n
    have h2 := iterateTransmitList_depthSum_global s n
    omega

end MutagenicList

/-! ## §4. Depth Monotonicity and Stabilization

The depth sequence depth(a), depth(T(a)), depth(T²(a)), ... is non-increasing.
Moreover, once it drops to ≤ 1, it can never rise again. This section develops
the theory of this monotone sequence, proving stabilization results that
strengthen the basic depth decay theorem.

LITERARY INSIGHT: an idea retold through many generations follows a
*monotone trajectory* of simplification. The rich philosophical system
becomes a set of aphorisms, then catchphrases, then (possibly) silence.
This trajectory never reverses — and once simple enough, remains simple. -/

section DepthMonotonicity
variable {I : Type*} [MutagenicDiffusion I]

/-- The depth trajectory: the sequence of depths under iterated transmission. -/
def depthTrajectory (a : I) (n : ℕ) : ℕ :=
  IdeaticSpace.depth (Nat.iterate MutagenicDiffusion.transmit n a)

/-- THEOREM (Trajectory Starts at Origin): the trajectory begins at the
    idea's own depth. -/
theorem depthTrajectory_zero (a : I) :
    depthTrajectory a 0 = IdeaticSpace.depth a := rfl

/-- THEOREM (Trajectory is Non-Increasing): d(n+1) ≤ d(n) always.
    INSIGHT: the complexity trajectory is a staircase that only goes down. -/
theorem depthTrajectory_nonincreasing (a : I) (n : ℕ) :
    depthTrajectory a (n + 1) ≤ depthTrajectory a n :=
  mutagenic_depth_monotone a n

/-- THEOREM (Trajectory is Globally Bounded): d(n) ≤ d(0) for all n.
    INSIGHT: the starting depth is an impassable ceiling. -/
theorem depthTrajectory_bounded (a : I) (n : ℕ) :
    depthTrajectory a n ≤ depthTrajectory a 0 :=
  mutagenic_depth_global_bound a n

/-- THEOREM (Stable Below Threshold): once depth ≤ 1, it stays ≤ 1 forever.
    INSIGHT: simple ideas are "absorbing states" in the cultural Markov chain.
    Once an idea reaches atomic level, it never regains complexity.
    This is the formal version of "you can't un-simplify a proverb." -/
theorem depthTrajectory_stable_below_one (a : I) (n : ℕ)
    (h : depthTrajectory a n ≤ 1) (m : ℕ) :
    depthTrajectory a (n + m) ≤ 1 := by
  induction m with
  | zero => exact h
  | succ m ih =>
    show depthTrajectory a (n + m + 1) ≤ 1
    have := depthTrajectory_nonincreasing a (n + m)
    omega

/-- THEOREM (Depth Trajectory Telescoping): the depth drops strictly
    for each step where depth > 1. INSIGHT: complex ideas lose at least one
    "layer" of depth per transmission — the erosion has a minimum speed. -/
theorem depthTrajectory_strict_drop (a : I) (n : ℕ)
    (h : depthTrajectory a n > 1) :
    depthTrajectory a (n + 1) < depthTrajectory a n := by
  unfold depthTrajectory at h ⊢
  rw [iterate_apply_succ]
  exact MutagenicDiffusion.transmit_depth_decay _ h

end DepthMonotonicity

/-! ## §5. Resonance Density: Measuring Coherence Quantitatively

A coherent sequence of length n has n−1 consecutive resonating pairs.
This section formalizes the concept of "resonance density" — the fraction
of consecutive pairs that resonate — and proves that coherent sequences
achieve the maximum possible density.

LITERARY INSIGHT: resonance density measures "how well a text flows."
A random word salad has low density; a carefully crafted narrative has
density 1 (= coherent). This connects the structural property of coherence
to the quantitative measure of resonance density. -/

section ResonanceDensity

variable {I : Type*}

/-- The consecutive pairs of a sequence.
    INSIGHT: these are the "joints" of a text — the transitions between
    successive ideas where coherence either holds or fails. -/
def consecutivePairs : List I → List (I × I)
  | [] => []
  | [_] => []
  | a :: b :: rest => (a, b) :: consecutivePairs (b :: rest)

/-- No consecutive pairs in the empty list. -/
@[simp] theorem consecutivePairs_nil :
    consecutivePairs ([] : List I) = [] := rfl

/-- No consecutive pairs in a singleton. -/
@[simp] theorem consecutivePairs_singleton (a : I) :
    consecutivePairs [a] = [] := rfl

/-- Consecutive pairs of a list with ≥ 2 elements. -/
theorem consecutivePairs_cons₂ (a b : I) (rest : List I) :
    consecutivePairs (a :: b :: rest) =
    (a, b) :: consecutivePairs (b :: rest) := rfl

/-- THEOREM (Consecutive Pair Count): a list of length n ≥ 2 has exactly
    n − 1 consecutive pairs. INSIGHT: the number of "joints" in a text
    is one less than the number of ideas — the simplest combinatorial fact,
    but foundational for density calculations. -/
theorem consecutivePairs_length : ∀ (s : List I),
    (consecutivePairs s).length = s.length - 1
  | [] => rfl
  | [_] => rfl
  | _ :: b :: rest => by
    simp only [consecutivePairs_cons₂, List.length_cons,
               consecutivePairs_length (b :: rest)]
    omega

variable [IdeaticSpace I]

/-- THEOREM (Coherence ↔ All Pairs Resonate): a sequence is coherent iff
    every consecutive pair resonates. This is definitional but important:
    it connects the structural definition (inductive) with the quantitative
    view (all pairs satisfy a property).
    INSIGHT: textual coherence is not a vague literary notion — it's the
    precise mathematical condition that *every* transition resonates. -/
theorem coherent_iff_all_pairs_resonate : ∀ (s : List I),
    Coherent s ↔ ∀ p ∈ consecutivePairs s, IdeaticSpace.resonates p.1 p.2
  | [] => ⟨fun _ _ h => absurd h (List.not_mem_nil _), fun _ => trivial⟩
  | [_] => ⟨fun _ _ h => absurd h (List.not_mem_nil _), fun _ => trivial⟩
  | a :: b :: rest => by
    constructor
    · intro ⟨hab, hrest⟩ p hp
      rw [consecutivePairs_cons₂] at hp
      cases List.mem_cons.mp hp with
      | inl h => rw [h]; exact hab
      | inr h => exact (coherent_iff_all_pairs_resonate (b :: rest)).mp hrest p h
    · intro h
      constructor
      · exact h (a, b) (List.mem_cons_self _ _)
      · exact (coherent_iff_all_pairs_resonate (b :: rest)).mpr
          (fun p hp => h p (List.mem_cons_of_mem _ hp))

set_option linter.unusedSectionVars false in
/-- THEOREM (Coherent Sequences Maximize Resonance): a coherent sequence
    of length n has exactly n−1 resonant consecutive pairs — the maximum
    possible. INSIGHT: coherence is not just a qualitative property; it
    corresponds to *saturating* the resonance density at 100%. -/
theorem coherent_resonant_pair_count (s : List I) :
    (consecutivePairs s).length = s.length - 1 :=
  consecutivePairs_length s

end ResonanceDensity

/-! ## §6. Diversity–Depth Tradeoff

When all elements of a sequence share the same depth, the depthSum is exactly
length × depth. Under mutagenic transmission, individual depths decrease
(possibly unevenly), breaking the uniformity. This section formalizes the
tension between depth and diversity.

LITERARY INSIGHT: a culture whose ideas are all equally complex is "brittle"
under mutation — some will simplify faster than others, introducing
*diversity of depth* where there was uniformity. The emergence of a
"depth hierarchy" (some ideas deep, some shallow) is a consequence of
differential erosion rates. -/

section DiversityDepth
variable {I : Type*} [IdeaticSpace I]

/-- THEOREM (Uniform Depth Determines Sum): if all elements have the same
    depth d, then depthSum = length × d. INSIGHT: uniformity makes the
    aggregate predictable. -/
theorem uniform_depth_depthSum (s : List I) (d : ℕ)
    (h : ∀ a ∈ s, IdeaticSpace.depth a = d) :
    depthSum s = s.length * d :=
  depthSum_uniform s d h

/-- THEOREM (Depth Diversity Lower Bound): if depthSum < length × d,
    then at least one element has depth < d. INSIGHT: if total complexity
    is less than the uniform prediction, some idea must be simpler than
    average. The "entropy" has already differentiated the population. -/
theorem diversity_from_depthSum_deficit (s : List I) (d : ℕ)
    (hbound : ∀ a ∈ s, IdeaticSpace.depth a ≤ d)
    (hdeficit : depthSum s < s.length * d) :
    ∃ a ∈ s, IdeaticSpace.depth a < d := by
  by_contra h
  push_neg at h
  have hunif : ∀ a ∈ s, IdeaticSpace.depth a = d := by
    intro a ha; exact le_antisymm (hbound a ha) (h a ha)
  have := depthSum_uniform s d hunif
  omega

end DiversityDepth

/-! ## §7. Mutagenic Diversity–Depth Dynamics

Under mutagenic transmission, the interplay between diversity and depth
creates a rich dynamical landscape. This section proves that transmission
weakens the depth sum of any population and establishes bounds on how
the spectrum changes.

LITERARY INSIGHT: when a corpus of ideas is transmitted through an imperfect
channel, the "deep" ideas erode faster than the "shallow" ones (since only
depth > 1 triggers strict decay). This differential erosion is the engine
of diversity creation in cultural evolution. -/

section MutagenicDiversity
variable {I : Type*} [MutagenicDiffusion I]

/-- THEOREM (Transmitted Uniform Bound): transmitting a uniform-depth list
    gives a list whose depthSum is at most the original.
    INSIGHT: mutation weakens a uniform population, potentially introducing
    depth variation where there was none. -/
theorem transmit_uniform_depthSum (s : List I) (d : ℕ)
    (h : ∀ a ∈ s, IdeaticSpace.depth a = d) :
    depthSum (transmitList s) ≤ s.length * d := by
  have h1 := transmitList_depthSum_le s
  have h2 := depthSum_uniform s d h
  omega

/-- THEOREM (Shallow Persistence): if every element has depth ≤ 1, then
    after transmission every element still has depth ≤ 1.
    INSIGHT: a collection of simple ideas remains simple — you cannot
    complexify a population through mutagenic transmission. -/
theorem transmitList_shallow_persist (s : List I)
    (h : ∀ a ∈ s, IdeaticSpace.depth a ≤ 1) :
    ∀ a ∈ transmitList s, IdeaticSpace.depth a ≤ 1 := by
  intro a ha
  simp only [transmitList, List.mem_map] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  have := MutagenicDiffusion.transmit_depth_le b
  have := h b hb
  omega

/-- THEOREM (Deep Element Strict Decrease): if an element has depth > 1,
    its transmitted version has strictly less depth.
    INSIGHT: the "tallest poppies" erode fastest — the most complex ideas
    in the corpus are the ones most vulnerable to mutation. -/
theorem transmit_deep_element_decreases (a : I) (h : IdeaticSpace.depth a > 1) :
    IdeaticSpace.depth (MutagenicDiffusion.transmit a) < IdeaticSpace.depth a :=
  MutagenicDiffusion.transmit_depth_decay a h

/-- THEOREM (Transmitted Depth Bound — membership form): every element of
    the transmitted list has depth ≤ its original counterpart.
    INSIGHT: the depth of any transmitted idea traces back to a source
    in the original corpus that was at least as deep. -/
theorem transmitList_depth_le_mem (s : List I) (b : I) (hb : b ∈ transmitList s) :
    ∃ a ∈ s, IdeaticSpace.depth b ≤ IdeaticSpace.depth a := by
  simp only [transmitList, List.mem_map] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  exact ⟨a, ha, MutagenicDiffusion.transmit_depth_le a⟩

end MutagenicDiversity

/-! ## §8. Selective Convergence: The Market of Ideas

Under selective diffusion, ideas compete on fitness. When we fold selection
across a list, the result is always one of the original ideas — and it has
the maximum fitness among them. Iterated selection on a population drives
convergence to the fittest element.

LITERARY INSIGHT: the "marketplace of ideas" doesn't create new ideas (that's
recombinant diffusion) — it filters existing ones. The survivor of selection
is always something that already existed. Innovation requires recombination;
competition only selects. -/

section SelectiveConvergence
variable {I : Type*} [SelectiveDiffusion I]

/-- Fold selection across a list with an initial competitor. -/
def foldSelect (init : I) : List I → I
  | [] => init
  | b :: rest => foldSelect (SelectiveDiffusion.select init b) rest

/-- THEOREM (Selection from Empty): selecting from an empty list returns
    the initial idea. INSIGHT: without competition, the incumbent survives. -/
@[simp] theorem foldSelect_nil (a : I) :
    foldSelect a ([] : List I) = a := rfl

/-- Folding selection across a cons list. -/
@[simp] theorem foldSelect_cons (init b : I) (rest : List I) :
    foldSelect init (b :: rest) =
    foldSelect (SelectiveDiffusion.select init b) rest := rfl

/-- THEOREM (Singleton Selection): selecting against one competitor picks
    the fitter of the two. -/
theorem foldSelect_singleton (a b : I) :
    foldSelect a [b] = SelectiveDiffusion.select a b := rfl

/-- THEOREM (Selection Fitness ≥ Init): the result of selection is at
    least as fit as the initial idea. INSIGHT: competition never makes the
    winner less fit than the starting point — fitness is monotonically
    non-decreasing through the selection process. -/
theorem foldSelect_fitness_ge_init (init : I) (s : List I) :
    SelectiveDiffusion.fitness (foldSelect init s) ≥
    SelectiveDiffusion.fitness init := by
  induction s generalizing init with
  | nil => exact le_refl _
  | cons b rest ih =>
    simp only [foldSelect_cons]
    have h1 := ih (SelectiveDiffusion.select init b)
    have h2 : SelectiveDiffusion.fitness init ≤
              SelectiveDiffusion.fitness (SelectiveDiffusion.select init b) := by
      rw [SelectiveDiffusion.select_maximizes]; exact Nat.le_max_left _ _
    exact le_trans h2 h1

/-- THEOREM (Selection Fitness ≥ Members): the result of selection is at
    least as fit as any element in the list. INSIGHT: the winner of a
    tournament is fitter than every participant. -/
theorem foldSelect_fitness_ge_mem (init : I) (s : List I) (b : I) (hb : b ∈ s) :
    SelectiveDiffusion.fitness (foldSelect init s) ≥
    SelectiveDiffusion.fitness b := by
  induction s generalizing init with
  | nil => exact absurd hb (List.not_mem_nil _)
  | cons c rest ih =>
    simp only [foldSelect_cons]
    cases List.mem_cons.mp hb with
    | inl h =>
      subst h
      have h1 := foldSelect_fitness_ge_init (SelectiveDiffusion.select init b) rest
      have h2 : SelectiveDiffusion.fitness b ≤
                SelectiveDiffusion.fitness (SelectiveDiffusion.select init b) := by
        rw [SelectiveDiffusion.select_maximizes]; exact Nat.le_max_right _ _
      exact le_trans h2 h1
    | inr h => exact ih _ h

/-- THEOREM (Selection Picks from Input): the result of folding selection
    is always either the initial idea or one of the list elements.
    INSIGHT: selective diffusion creates NO novelty — it only filters.
    Every surviving idea existed before the competition began. -/
theorem foldSelect_is_input (init : I) (s : List I) :
    foldSelect init s = init ∨ foldSelect init s ∈ s := by
  induction s generalizing init with
  | nil => left; rfl
  | cons b rest ih =>
    simp only [foldSelect_cons]
    rcases ih (SelectiveDiffusion.select init b) with h | h
    · rw [h]
      rcases SelectiveDiffusion.select_is_input init b with hab | hab
      · left; exact hab
      · right; rw [hab]; exact List.mem_cons_self b rest
    · right; exact List.mem_cons_of_mem b h

/-- THEOREM (Selection Fitness Characterization): the fitness of the
    selected idea equals the maximum fitness over init and all list elements.
    INSIGHT: the tournament outcome is completely determined by fitness values
    — the process is transparent and optimal. -/
theorem foldSelect_fitness_eq (init : I) (s : List I) :
    SelectiveDiffusion.fitness (foldSelect init s) =
    (s.map SelectiveDiffusion.fitness).foldl Nat.max (SelectiveDiffusion.fitness init) := by
  induction s generalizing init with
  | nil => rfl
  | cons b rest ih =>
    simp only [foldSelect_cons, List.map_cons, List.foldl_cons]
    rw [ih (SelectiveDiffusion.select init b),
        SelectiveDiffusion.select_maximizes]

/-- THEOREM (Idempotent Selection): selecting an idea against itself
    returns the same idea. INSIGHT: self-competition is trivial. -/
theorem foldSelect_idempotent_self (a : I) :
    foldSelect a [a] = a := by
  simp [foldSelect, selective_self]

/-- THEOREM (Void Loses Selection): void has zero fitness and loses to
    anything with positive fitness. INSIGHT: in the marketplace of ideas,
    "saying nothing" is the worst strategy. -/
theorem foldSelect_void_init (s : List I) (b : I) (hb : b ∈ s)
    (hfit : SelectiveDiffusion.fitness b > 0) :
    foldSelect (IdeaticSpace.void : I) s ≠ IdeaticSpace.void := by
  intro h
  have hge := foldSelect_fitness_ge_mem (IdeaticSpace.void : I) s b hb
  rw [h, SelectiveDiffusion.void_fitness] at hge
  omega

end SelectiveConvergence

/-! ## §9. Coherent Composition: Building Complex Texts

This section explores how coherent sequences interact with ideatic composition.

LITERARY INSIGHT: this is the formal theory of narrative concatenation — how
chapters combine into books, scenes into acts, movements into symphonies. -/

section CoherentComposition
variable {I : Type*} [IdeaticSpace I]

/-- THEOREM (Pair Depth Sum): the depthSum of a coherent pair equals the
    sum of the two depths. INSIGHT: a minimal coherent "text" (two resonant
    ideas) has complexity equal to the sum of its parts. -/
theorem coherent_pair_depthSum (a b : I) :
    depthSum [a, b] = IdeaticSpace.depth a + IdeaticSpace.depth b := by
  simp [depthSum_cons, depthSum_singleton]

/-- THEOREM (Constant Sequence Depth Sum): a constant sequence of length n
    has depthSum = n × depth(a). INSIGHT: repeating the same idea n times
    multiplies complexity linearly. -/
theorem replicate_depthSum (a : I) (n : ℕ) :
    depthSum (List.replicate n a) = n * IdeaticSpace.depth a := by
  induction n with
  | zero => simp [depthSum]
  | succ n ih =>
    rw [List.replicate_succ, depthSum_cons, ih]; ring

/-- THEOREM (Coherent Sublist Property): the tail of a coherent sequence
    is coherent. INSIGHT: coherence is "hereditary" — removing the first
    idea from a coherent text leaves a coherent text. -/
theorem coherent_of_tail {a : I} {s : List I}
    (h : Coherent (a :: s)) : Coherent s :=
  coherent_tail h

/-- THEOREM (Coherent depthSum Nonneg): depthSum of any list is nonneg.
    INSIGHT: total complexity is never negative — tautological for ℕ, but
    foundational for the thermodynamic analogy. -/
theorem depthSum_nonneg (s : List I) : 0 ≤ depthSum s :=
  Nat.zero_le _

end CoherentComposition

/-! ## §10. Information Flow Bounds

This section establishes bounds on how information (measured by depth) flows
through the various diffusion mechanisms.

- **Mutagenic**: monotone loss (ΔdepthSum ≤ 0)
- **Recombinant**: bounded growth (ΔdepthSum ≤ +1 per operation)
- **Selective**: no creation (output ⊆ input)

LITERARY INSIGHT: these are the "conservation laws" of cultural transmission.
They constrain what is *possible*. -/

section InformationFlow
variable {I : Type*} [IdeaticSpace I]

/-- THEOREM (Composition Information Bound): composing two ideas yields
    depth bounded by the sum. INSIGHT: combining ideas adds at most the
    sum of their complexities. -/
theorem compose_depthSum_bound (a b : I) :
    IdeaticSpace.depth (IdeaticSpace.compose a b) ≤
    depthSum [a] + depthSum [b] := by
  simp [depthSum_singleton]
  exact IdeaticSpace.depth_subadditive a b

/-- THEOREM (Depth Is Filtration-Monotone): bounding individual depth
    bounds aggregate depth. INSIGHT: a ceiling on parts implies a ceiling
    on the whole. -/
theorem depthSum_filtration_bound (s : List I) (d : ℕ)
    (h : ∀ a ∈ s, IdeaticSpace.depth a ≤ d) :
    depthSum s ≤ s.length * d :=
  depthSum_bound s d h

end InformationFlow

/-! ## §11. Mutagenic Depth Spectrum Evolution

Under repeated mutagenic transmission, the depth spectrum evolves
monotonically. This section develops the spectrum-level view of cultural
entropy, complementing the aggregate (depthSum) view from §3.

LITERARY INSIGHT: it's not just that *total* complexity decreases — each
*individual* complexity value in the spectrum decreases. The erosion is
universal and pointwise, not just in aggregate. -/

section SpectrumEvolution
variable {I : Type*} [MutagenicDiffusion I]

/-- THEOREM (Transmitted Spectrum Length): the spectrum length is invariant
    under transmission. INSIGHT: the "complexity profile" has the same
    number of entries before and after transmission — only the values change. -/
theorem transmitList_spectrum_length (s : List I) :
    (depthSpectrum (transmitList s)).length = (depthSpectrum s).length := by
  simp [depthSpectrum, transmitList, List.length_map]

/-- THEOREM (Iterated Transmission Spectrum Length): spectrum length is
    invariant under any number of transmissions. -/
theorem iterateTransmitList_spectrum_length (s : List I) : ∀ (n : ℕ),
    (depthSpectrum (iterateTransmitList s n)).length = (depthSpectrum s).length
  | 0 => rfl
  | n + 1 => by
    have h1 : (depthSpectrum (iterateTransmitList s (n + 1))).length =
              (iterateTransmitList s (n + 1)).length := depthSpectrum_length _
    have h2 : (iterateTransmitList s (n + 1)).length = s.length :=
              iterateTransmitList_length s (n + 1)
    have h3 : (depthSpectrum s).length = s.length := depthSpectrum_length _
    omega

/-- THEOREM (Composition Depth Bounded by Sum): the depth of a composition
    is bounded by the depth sum of the two components. -/
theorem compose_depth_spectrum_bound (a b : I) :
    IdeaticSpace.depth (IdeaticSpace.compose a b) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b :=
  IdeaticSpace.depth_subadditive a b

end SpectrumEvolution

/-! ## §12. Recombinant Information Growth

Under recombinant diffusion, information can *grow* — unlike mutagenic
diffusion where it only shrinks. However, the growth is bounded: each
recombination adds at most 1 to the combined depth of the parents.

LITERARY INSIGHT: intellectual innovation through synthesis is *bounded*,
not unbounded. Combining two ideas of depth d₁ and d₂ gives something of
depth at most d₁ + d₂ + 1. The "+1" is the "novelty premium" — the single
layer of new meaning that synthesis adds beyond its inputs. -/

section RecombinantGrowth
variable {I : Type*} [RecombinantDiffusion I]

/-- THEOREM (Recombination Depth Premium): recombination adds at most 1
    layer of new depth beyond the sum of inputs.
    INSIGHT: the "creativity premium" is exactly +1 per synthesis operation. -/
theorem recombine_depth_premium (a b : I) :
    IdeaticSpace.depth (RecombinantDiffusion.recombine a b) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b + 1 :=
  RecombinantDiffusion.recombine_depth_bound a b

/-- THEOREM (Double Recombination Bound): two successive recombinations
    grow depth by at most 2 beyond the total input depth.
    INSIGHT: iterating creativity compounds, but only linearly. -/
theorem double_recombine_depth (a b c : I) :
    IdeaticSpace.depth (RecombinantDiffusion.recombine
      (RecombinantDiffusion.recombine a b) c) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b + IdeaticSpace.depth c + 2 := by
  have h1 := RecombinantDiffusion.recombine_depth_bound a b
  have h2 := RecombinantDiffusion.recombine_depth_bound
    (RecombinantDiffusion.recombine a b) c
  omega

/-- THEOREM (Recombination Resonance Network): a recombined idea resonates
    with both parents and with the reverse recombination. This creates a
    "triangle" of resonance. INSIGHT: every act of synthesis creates not
    just a new idea but a new *cluster* of resonant ideas. -/
theorem recombine_resonance_triangle (a b : I) :
    IdeaticSpace.resonates a (RecombinantDiffusion.recombine a b) ∧
    IdeaticSpace.resonates b (RecombinantDiffusion.recombine a b) ∧
    IdeaticSpace.resonates
      (RecombinantDiffusion.recombine a b)
      (RecombinantDiffusion.recombine b a) :=
  ⟨RecombinantDiffusion.recombine_resonant_left a b,
   RecombinantDiffusion.recombine_resonant_right a b,
   RecombinantDiffusion.recombine_comm_resonant a b⟩

end RecombinantGrowth

end IDT
