import FormalAnthropology.IDT_Foundations_v2

/-!
# IDT v2: Poetics — Theory of Aesthetic Form

Formalises core concepts from poetics (Aristotle, Jakobson, Shklovsky) within
the quantitative resonance framework of IDT v2.

**Verse** = a list of *lines* (ideas) whose composed meaning accumulates
through `compose`.  Resonance strength measures the degree of semantic
agreement between lines; it serves as the backbone for *rhyme*, *consonance*,
*parallelism*, and *defamiliarization*.

Key structural results:
- Verse meaning is a monoidal fold (`verseIdea_append`).
- Adding lines monotonically grows verse weight (`verseWeight_cons_ge`).
- Consonance is non-negative and bounded by Cauchy-Schwarz.
- Defamiliarization (orthogonality) maximises squared distance.
- Parallelism (alignment) composes constructively.

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT2.Poetics

variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2 IDT2

/-! ## §1. Verse Structure — Definitions -/

/-- A verse (poem) is a list of lines (ideas). -/
abbrev Verse (I : Type*) := List I

/-- The composed meaning of a verse: right fold over `compose`. -/
def verseIdea [IdeaticSpace2 I] : Verse I → I
  | [] => void
  | l :: rest => compose l (verseIdea rest)

/-- Verse weight: self-resonance of the composed meaning. -/
noncomputable def verseWeight (v : Verse I) : ℝ :=
  resonanceStrength (verseIdea v) (verseIdea v)

/-- Rhyme: two lines are aligned (positive resonance). -/
def rhymes (a b : I) : Prop := resonanceStrength a b > 0

/-- Consonance: the degree of resonance between two lines. -/
noncomputable def consonance (a b : I) : ℝ :=
  resonanceStrength a b

/-- Poetic distance: squared distance in the resonance kernel. -/
noncomputable def poeticDistance (a b : I) : ℝ :=
  squaredDistance a b

/-- Orthogonal (defamiliarizing): zero resonance. -/
def defamiliarizing (novel context : I) : Prop :=
  resonanceStrength novel context = 0

/-- Aligned (parallel): positive resonance. -/
def isParallel (a b : I) : Prop := resonanceStrength a b > 0

/-- Total consonance: sum of consecutive-pair resonances. -/
noncomputable def totalConsonance [IdeaticSpace2 I] : Verse I → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => consonance a b + totalConsonance (b :: rest)

/-! ## §2. Verse Theorems -/

/-- Theorem 1: The meaning of an empty verse is void. -/
theorem verseIdea_nil : verseIdea ([] : Verse I) = (void : I) := rfl

/-- Theorem 2: A single-line verse means just that line. -/
theorem verseIdea_singleton (l : I) : verseIdea [l] = l := by
  show compose l (void : I) = l
  exact IdeaticSpace2.void_right l

/-- Theorem 3: Recursive decomposition. -/
theorem verseIdea_cons (l : I) (rest : Verse I) :
    verseIdea (l :: rest) = compose l (verseIdea rest) := rfl

/-- Theorem 4: Verse meaning distributes over concatenation (monoid homomorphism). -/
theorem verseIdea_append (v1 v2 : Verse I) :
    verseIdea (v1 ++ v2) = compose (verseIdea v1) (verseIdea v2) := by
  induction v1 with
  | nil =>
    show verseIdea v2 = compose (void : I) (verseIdea v2)
    rw [IdeaticSpace2.void_left]
  | cons l rest ih =>
    show compose l (verseIdea (rest ++ v2)) =
         compose (compose l (verseIdea rest)) (verseIdea v2)
    rw [ih, IdeaticSpace2.compose_assoc]

/-- Theorem 5: Verse weight is strictly positive. -/
theorem verseWeight_pos (v : Verse I) : verseWeight v > 0 :=
  IdeaticSpace2.rs_self_pos _

/-- Theorem 6: Verse weight is at least 1 (void calibration). -/
theorem verseWeight_ge_one (v : Verse I) : verseWeight v ≥ 1 :=
  rs_self_ge_one _

/-- Theorem 7: Empty verse has unit weight. -/
theorem verseWeight_nil : verseWeight ([] : Verse I) = 1 := by
  show resonanceStrength (void : I) (void : I) = 1
  exact IdeaticSpace2.rs_void_self

/-- Theorem 8: Adding a line never decreases verse weight. -/
theorem verseWeight_cons_ge (l : I) (rest : Verse I) :
    verseWeight (l :: rest) ≥ verseWeight rest := by
  unfold verseWeight
  show resonanceStrength (compose l (verseIdea rest)) (compose l (verseIdea rest)) ≥
       resonanceStrength (verseIdea rest) (verseIdea rest)
  exact IdeaticSpace2.rs_compose_left_mono _ _ l

/-! ## §3. Rhyme and Consonance -/

/-- Theorem 9: Rhyme is symmetric. -/
theorem rhymes_symmetric {a b : I} (h : rhymes a b) : rhymes b a := by
  unfold rhymes at *; rwa [IdeaticSpace2.rs_symm]

/-- Theorem 10: Every idea rhymes with itself. -/
theorem rhymes_self (a : I) : rhymes a a :=
  IdeaticSpace2.rs_self_pos a

/-- Theorem 11: Consonance equals resonance strength. -/
theorem consonance_eq_rs (a b : I) :
    consonance a b = resonanceStrength a b := rfl

/-- Theorem 12: Consonance is non-negative. -/
theorem consonance_nonneg (a b : I) : consonance a b ≥ 0 :=
  IdeaticSpace2.rs_nonneg a b

/-- Theorem 13: Consonance is symmetric. -/
theorem consonance_symm (a b : I) : consonance a b = consonance b a :=
  IdeaticSpace2.rs_symm a b

/-- Theorem 14: Self-consonance is at least 1. -/
theorem consonance_self_ge_one (a : I) : consonance a a ≥ 1 :=
  rs_self_ge_one a

/-- Theorem 15: Consonance satisfies Cauchy-Schwarz. -/
theorem consonance_cauchy_schwarz (a b : I) :
    consonance a b * consonance a b ≤ consonance a a * consonance b b :=
  IdeaticSpace2.rs_cauchy_schwarz a b

/-! ## §4. Parallelism and Repetition -/

/-- Theorem 16: Total consonance of an empty verse is 0. -/
theorem totalConsonance_nil : totalConsonance ([] : Verse I) = 0 := rfl

/-- Theorem 17: Total consonance of a singleton is 0. -/
theorem totalConsonance_singleton (a : I) : totalConsonance [a] = 0 := rfl

/-- Theorem 18: Total consonance of a pair is the consonance. -/
theorem totalConsonance_pair (a b : I) :
    totalConsonance [a, b] = consonance a b := by
  show consonance a b + (0 : ℝ) = consonance a b
  linarith

/-- Theorem 19: Recursive decomposition of total consonance. -/
theorem totalConsonance_cons (a b : I) (rest : Verse I) :
    totalConsonance (a :: b :: rest) =
    consonance a b + totalConsonance (b :: rest) := rfl

/-- Theorem 20: Total consonance is non-negative. -/
theorem totalConsonance_nonneg : ∀ (v : Verse I), totalConsonance v ≥ 0
  | [] => le_refl _
  | [_] => le_refl _
  | a :: b :: rest => by
    show consonance a b + totalConsonance (b :: rest) ≥ 0
    linarith [consonance_nonneg (I := I) a b, totalConsonance_nonneg (b :: rest)]

/-- Theorem 21: Parallel lines give positive total consonance. -/
theorem parallel_pair_positive (a b : I) (h : isParallel a b) :
    totalConsonance [a, b] > 0 := by
  rw [totalConsonance_pair]
  exact h

/-! ## §5. Defamiliarization and Caesura -/

/-- Theorem 22: Defamiliarization is symmetric. -/
theorem defamiliarizing_symm {a b : I} (h : defamiliarizing a b) :
    defamiliarizing b a := by
  unfold defamiliarizing at *; rwa [IdeaticSpace2.rs_symm]

/-- Theorem 23: No idea defamiliarizes itself (self-resonance > 0). -/
theorem not_defamiliarizing_self (a : I) : ¬defamiliarizing a a := by
  unfold defamiliarizing
  linarith [IdeaticSpace2.rs_self_pos a]

/-- Theorem 24: Defamiliarizing ideas do not rhyme. -/
theorem defamiliarizing_not_rhymes {a b : I} (h : defamiliarizing a b) :
    ¬rhymes a b := by
  unfold defamiliarizing rhymes at *; linarith

/-- Theorem 25: Defamiliarization maximises poetic distance. -/
theorem defamiliarizing_max_distance {a b : I} (h : defamiliarizing a b) :
    poeticDistance a b = resonanceStrength a a + resonanceStrength b b := by
  unfold poeticDistance squaredDistance defamiliarizing at *
  linarith

/-- Theorem 26: Defamiliarization zeroes normalised resonance. -/
theorem defamiliarizing_normalizedRS {a b : I} (h : defamiliarizing a b) :
    normalizedRS a b = 0 := by
  unfold normalizedRS defamiliarizing at *
  rw [h]; simp

/-! ## §6. Verse Weight Growth -/

/-- Theorem 27: A verse's weight dominates each line's self-resonance. -/
theorem verseWeight_ge_head (l : I) (rest : Verse I) :
    verseWeight (l :: rest) ≥ resonanceStrength l l := by
  unfold verseWeight
  show resonanceStrength (compose l (verseIdea rest)) (compose l (verseIdea rest)) ≥
       resonanceStrength l l
  have h := IdeaticSpace2.rs_compose_right_mono l l (verseIdea rest)
  linarith [IdeaticSpace2.rs_symm (compose l (verseIdea rest)) (compose l (verseIdea rest))]

/-- Theorem 28: Appending a verse never decreases weight. -/
theorem verseWeight_append_ge_left (v1 v2 : Verse I) :
    verseWeight (v1 ++ v2) ≥ verseWeight v1 := by
  unfold verseWeight
  rw [verseIdea_append]
  exact rs_compose_self_right (verseIdea v1) (verseIdea v2)

/-- Theorem 29: Appending a verse preserves weight of the suffix. -/
theorem verseWeight_append_ge_right (v1 v2 : Verse I) :
    verseWeight (v1 ++ v2) ≥ verseWeight v2 := by
  unfold verseWeight
  rw [verseIdea_append]
  exact IdeaticSpace2.rs_compose_left_mono _ _ (verseIdea v1)

/-- Theorem 30: Verse concatenation respects associativity. -/
theorem verseIdea_append_assoc (v1 v2 v3 : Verse I) :
    verseIdea (v1 ++ v2 ++ v3) =
    compose (verseIdea v1) (compose (verseIdea v2) (verseIdea v3)) := by
  rw [verseIdea_append, verseIdea_append, IdeaticSpace2.compose_assoc]

/-! ## §7. Poetic Distance Properties -/

/-- Theorem 31: Poetic distance is non-negative. -/
theorem poeticDistance_nonneg (a b : I) : poeticDistance a b ≥ 0 :=
  squaredDistance_nonneg a b

/-- Theorem 32: Poetic distance is symmetric. -/
theorem poeticDistance_symm (a b : I) : poeticDistance a b = poeticDistance b a :=
  squaredDistance_symm a b

/-- Theorem 33: Identical ideas have zero poetic distance. -/
theorem poeticDistance_self (a : I) : poeticDistance a a = 0 :=
  squaredDistance_self a

/-- Theorem 34: Poetic distance is bounded by the sum of self-resonances. -/
theorem poeticDistance_le_sum (a b : I) :
    poeticDistance a b ≤ resonanceStrength a a + resonanceStrength b b := by
  unfold poeticDistance squaredDistance
  linarith [IdeaticSpace2.rs_nonneg a b]

/-! ## §8. Composition and Resonance Interaction -/

/-- Theorem 35: Composing two lines preserves rhyme with each component. -/
theorem compose_rhymes_right (a b c : I) (h : rhymes a b) :
    rhymes (compose a c) (compose b c) := by
  unfold rhymes at *
  linarith [IdeaticSpace2.rs_compose_right_mono a b c]

/-- Theorem 36: Composing on the left preserves rhyme. -/
theorem compose_rhymes_left (c : I) {a b : I} (h : rhymes a b) :
    rhymes (compose c a) (compose c b) := by
  unfold rhymes at *
  linarith [IdeaticSpace2.rs_compose_left_mono a b c]

/-- Theorem 37: Two-line verse weight is at least as large as either line's weight. -/
theorem verse_pair_weight_ge_second (a b : I) :
    verseWeight [a, b] ≥ resonanceStrength b b := by
  unfold verseWeight
  show resonanceStrength (compose a (verseIdea [b])) (compose a (verseIdea [b])) ≥
       resonanceStrength b b
  have hsing : verseIdea [b] = b := verseIdea_singleton b
  rw [hsing]
  exact IdeaticSpace2.rs_compose_left_mono b b a

/-- Theorem 38: A repeated line amplifies weight. -/
theorem repeated_line_weight (a : I) :
    verseWeight [a, a] ≥ resonanceStrength a a := by
  unfold verseWeight
  have h : verseIdea [a, a] = compose a a := by
    show compose a (verseIdea [a]) = compose a a
    rw [verseIdea_singleton]
  rw [h]
  exact rs_compose_self_right a a

/-- Theorem 39: Rhyme implies positive consonance (by definition). -/
theorem rhymes_consonance_pos {a b : I} (h : rhymes a b) :
    consonance a b > 0 := h

/-- Theorem 40: Consonance with a composed idea dominates original. -/
theorem consonance_compose_right_mono (a b c : I) :
    consonance (compose a c) (compose b c) ≥ consonance a b :=
  IdeaticSpace2.rs_compose_right_mono a b c

/-- Theorem 41: Verse weight of a three-line verse dominates all sub-weights. -/
theorem verse_triple_weight_ge (a b c : I) :
    verseWeight [a, b, c] ≥ resonanceStrength a a := by
  unfold verseWeight
  have h1 : verseIdea [a, b, c] = compose a (compose b c) := by
    show compose a (verseIdea [b, c]) = compose a (compose b c)
    congr 1
    show compose b (verseIdea [c]) = compose b c
    congr 1
    exact verseIdea_singleton c
  rw [h1]
  exact rs_compose_self_right a (compose b c)

end IDT2.Poetics
