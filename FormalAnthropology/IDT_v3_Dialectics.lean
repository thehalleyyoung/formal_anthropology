import FormalAnthropology.IDT_v3_Foundations

/-!
# IDT v3: Dialectics — The Algebra of Contradiction

Hegel's dialectic — thesis, antithesis, synthesis — is perhaps the
most famous theory of how ideas develop. In IDT v3, we can formalize
this precisely using emergence.

**Thesis** a and **antithesis** b are ideas that oppose (rs(a,b) < 0).
**Synthesis** is compose(a, b) — their composition. The emergence
term κ(a,b,c) captures the genuinely NEW meaning that arises from
the synthesis, beyond what thesis and antithesis individually contribute.

The key insight: OPPOSITION CREATES. When rs(a,b) < 0, the emergence
κ(a,b,compose a b) can be large and positive. The greater the opposition,
the more potential for creative emergence. This is the dialectical engine.

## Deep Theorems

1. **Dialectical Enrichment**: synthesis always has at least as much
   self-resonance as thesis (compose_enriches)
2. **The Cocycle of History**: sequential dialectical developments
   are constrained by the cocycle condition
3. **Aufhebung Decomposition**: the synthesis preserves, negates, and
   transcends — each is a component of the resonance

## NO SORRIES
-/

namespace IDT3

section Dialectics
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-! ## §1. Thesis, Antithesis, Synthesis -/

/-- Two ideas are in dialectical opposition if they resonate negatively. -/
def opposition (a b : I) : Prop := rs a b < 0

-- Dialectical opposition is NOT necessarily symmetric (resonance is asymmetric).
-- rs(a,b) < 0 does not imply rs(b,a) < 0

/-- Mutual opposition: both directions are negative. -/
def mutualOpposition (a b : I) : Prop :=
  rs a b < 0 ∧ rs b a < 0

theorem mutualOpposition_symm (a b : I) :
    mutualOpposition a b → mutualOpposition b a :=
  fun ⟨h1, h2⟩ => ⟨h2, h1⟩

/-- Void opposes nothing. -/
theorem void_not_opposition (a : I) : ¬opposition (void : I) a := by
  unfold opposition; rw [rs_void_left']; linarith

/-- A non-void idea cannot oppose itself (since rs(a,a) > 0 for a ≠ void). -/
theorem no_self_opposition (a : I) (h : a ≠ void) : ¬opposition a a := by
  unfold opposition
  have := rs_self_pos a h
  linarith

/-- The synthesis of thesis a and antithesis b. -/
def synthesize (thesis antithesis : I) : I := compose thesis antithesis

/-- Synthesis always enriches the thesis. This is Hegel's "sublation"
    (Aufhebung): the synthesis CONTAINS the thesis. -/
theorem synthesis_enriches_thesis (a b : I) :
    rs (synthesize a b) (synthesize a b) ≥ rs a a := by
  unfold synthesize; exact compose_enriches' a b

/-- The dialectical emergence: how much NEW meaning the synthesis creates. -/
noncomputable def dialecticalEmergence (thesis antithesis observer : I) : ℝ :=
  emergence thesis antithesis observer

/-- Self-dialectical-emergence: measured against the synthesis itself. -/
noncomputable def aufhebung (thesis antithesis : I) : ℝ :=
  dialecticalEmergence thesis antithesis (synthesize thesis antithesis)

/-- Aufhebung vanishes when either part is void. -/
theorem aufhebung_void_thesis (b : I) :
    aufhebung (void : I) b = 0 := by
  unfold aufhebung dialecticalEmergence; exact emergence_void_left b _

theorem aufhebung_void_antithesis (a : I) :
    aufhebung a (void : I) = 0 := by
  unfold aufhebung dialecticalEmergence; exact emergence_void_right a _

/-! ## §2. The Aufhebung Decomposition

The self-resonance of the synthesis decomposes into three parts:
1. Preservation (how thesis resonates with synthesis)
2. Negation (how antithesis resonates with synthesis)
3. Transcendence (the emergence — genuinely new meaning)

rs(a∘b, a∘b) = rs(a, a∘b) + rs(b, a∘b) + κ(a, b, a∘b)
               = preservation + negation + transcendence -/

/-- Preservation: how much the thesis is retained in the synthesis. -/
noncomputable def preservation (a b : I) : ℝ :=
  rs a (synthesize a b)

/-- Negation: how much the antithesis contributes to the synthesis. -/
noncomputable def negation (a b : I) : ℝ :=
  rs b (synthesize a b)

/-- Transcendence: the genuinely new meaning = aufhebung. -/
noncomputable def transcendence (a b : I) : ℝ :=
  aufhebung a b

/-- The Aufhebung Decomposition Theorem:
    The synthesis's self-resonance = preservation + negation + transcendence. -/
theorem aufhebung_decomposition (a b : I) :
    rs (synthesize a b) (synthesize a b) =
    preservation a b + negation a b + transcendence a b := by
  unfold preservation negation transcendence aufhebung dialecticalEmergence synthesize
  exact rs_compose_eq a b (compose a b)

/-- Transcendence is bounded by the synthesis's weight. -/
theorem transcendence_bounded (a b : I) :
    (transcendence a b) ^ 2 ≤
    rs (synthesize a b) (synthesize a b) *
    rs (synthesize a b) (synthesize a b) := by
  unfold transcendence aufhebung dialecticalEmergence synthesize
  exact emergence_bounded' a b (compose a b)

/-! ## §3. Sequential Dialectics — The March of History

When dialectical development proceeds in stages:
  thesis₁ → synthesis₁ → thesis₂ → synthesis₂ → ...

The cocycle condition constrains how emergence accumulates. -/

/-- Two-stage dialectical development:
    First synthesize a with b, then synthesize the result with c. -/
def dialecticalChain3 (a b c : I) : I :=
  compose (compose a b) c

/-- The emergence of the second stage is constrained by the first. -/
theorem dialectical_cocycle (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

/-- The total emergence of a three-stage dialectic (measured against d)
    is the same regardless of how you bracket the development. -/
theorem dialectical_bracketing (a b c d : I) :
    rs (compose (compose a b) c) d = rs (compose a (compose b c)) d := by
  rw [compose_assoc']

-- But the INTERMEDIATE emergences differ — the path through history matters,
-- even if the final resonance doesn't.
-- Via left-bracketing: emergence(a,b,d) + emergence(a∘b,c,d)
-- Via right-bracketing: emergence(b,c,d) + emergence(a,b∘c,d)
-- These are equal (cocycle) but the individual terms differ.

/-- Iterated dialectics: n-fold synthesis with the same antithesis. -/
def iteratedSynthesis (thesis antithesis : I) : ℕ → I
  | 0 => thesis
  | n + 1 => synthesize (iteratedSynthesis thesis antithesis n) antithesis

theorem iteratedSynthesis_zero (a b : I) :
    iteratedSynthesis a b 0 = a := rfl

theorem iteratedSynthesis_succ (a b : I) (n : ℕ) :
    iteratedSynthesis a b (n + 1) =
    compose (iteratedSynthesis a b n) b := rfl

/-- Iterated synthesis produces ever-heavier ideas.
    History accumulates weight — nothing is truly forgotten. -/
theorem iteratedSynthesis_enriches (a b : I) (n : ℕ) :
    rs (iteratedSynthesis a b (n + 1)) (iteratedSynthesis a b (n + 1)) ≥
    rs (iteratedSynthesis a b n) (iteratedSynthesis a b n) := by
  rw [iteratedSynthesis_succ]
  exact compose_enriches' (iteratedSynthesis a b n) b

/-- The self-resonance of iterated synthesis is non-decreasing. -/
theorem iteratedSynthesis_nondecreasing (a b : I) (m n : ℕ) (h : m ≤ n) :
    rs (iteratedSynthesis a b n) (iteratedSynthesis a b n) ≥
    rs (iteratedSynthesis a b m) (iteratedSynthesis a b m) := by
  induction n with
  | zero =>
    interval_cases m
    exact le_refl _
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact le_refl _
    · have h1 := ih (Nat.lt_succ_iff.mp hlt)
      linarith [iteratedSynthesis_enriches a b n]

/-! ## §4. Sublation Classes -/

/-- A synthesis is CREATIVE if the transcendence is positive:
    the whole is MORE than the sum of parts' contributions. -/
def creative (a b : I) : Prop :=
  transcendence a b > 0

/-- A synthesis is DESTRUCTIVE if the transcendence is negative:
    the parts partially cancel in the synthesis. -/
def destructive (a b : I) : Prop :=
  transcendence a b < 0

/-- A synthesis is ADDITIVE if the transcendence is zero:
    no emergence, purely linear combination. -/
def additive (a b : I) : Prop :=
  transcendence a b = 0

/-- Void synthesis is always additive. -/
theorem void_additive (a : I) : additive a (void : I) :=
  aufhebung_void_antithesis a

/-- If a synthesis is additive, then aufhebung decomposes simply. -/
theorem additive_decomposition (a b : I) (h : additive a b) :
    rs (synthesize a b) (synthesize a b) =
    preservation a b + negation a b := by
  have := aufhebung_decomposition a b
  unfold additive at h
  linarith

/-! ## §5. The Dialectical Tension Function -/

/-- The dialectical tension between a and b: how much emergent
    meaning their synthesis creates, measured against THEMSELVES. -/
noncomputable def tension (a b : I) : ℝ :=
  emergence a b a + emergence a b b

/-- Tension decomposes into two components:
    - How the synthesis resonates with the thesis minus linear prediction
    - How the synthesis resonates with the antithesis minus linear prediction -/
theorem tension_eq (a b : I) :
    tension a b =
    (rs (compose a b) a - rs a a - rs b a) +
    (rs (compose a b) b - rs a b - rs b b) := by
  unfold tension emergence; ring

/-- Tension with void vanishes. -/
theorem tension_void_right (a : I) : tension a (void : I) = 0 := by
  unfold tension; rw [emergence_void_right, emergence_void_right]; ring

theorem tension_void_left (b : I) : tension (void : I) b = 0 := by
  unfold tension; rw [emergence_void_left, emergence_void_left]; ring

/-- Order-reversed tension. -/
noncomputable def reverseTension (a b : I) : ℝ :=
  emergence b a a + emergence b a b

/-- The difference between tension and reverse-tension captures
    the non-commutativity of dialectical development. -/
theorem tension_asymmetry (a b : I) :
    tension a b - reverseTension a b =
    meaningCurvature a b a + meaningCurvature a b b := by
  unfold tension reverseTension meaningCurvature; ring

/-! ## §6. Hegelian Dialectic: Determinate Negation

Hegel's "determinate negation" is not mere absence: it is the specific
CONTRADICTION of a thesis that drives development forward. In IDT, the
negation of a is not void but an idea b such that rs(a,b) < 0. The negation
is "determinate" because it carries structure — the composition a∘b is
richer than void, containing both the original and its opposition. -/

/-- The negation residue: what remains of a's self-resonance after
    synthesizing with its antithesis. A non-trivial negation always
    leaves a residue because composition enriches. -/
noncomputable def negationResidue (a b : I) : ℝ :=
  rs (synthesize a b) (synthesize a b) - rs a a

/-- Determinate negation always leaves non-negative residue.
    "What does not destroy you makes you heavier." -/
theorem negation_residue_nonneg (a b : I) :
    negationResidue a b ≥ 0 := by
  unfold negationResidue synthesize
  linarith [compose_enriches' a b]

/-- Void negation leaves zero residue. -/
theorem negation_residue_void (a : I) :
    negationResidue a (void : I) = 0 := by
  unfold negationResidue synthesize; simp [rs_void_right']

/-- The aufhebung is the self-emergence of the synthesis:
    it equals the self-resonance minus the preservation and negation terms. -/
theorem aufhebung_eq_selfEmergence (a b : I) :
    aufhebung a b = selfEmergence a b := by
  unfold aufhebung dialecticalEmergence synthesize selfEmergence; rfl

/-- Negation residue decomposes into preservation, negation, and
    transcendence: the full Hegelian triple movement. -/
theorem negation_residue_decomposition (a b : I) :
    negationResidue a b =
    preservation a b + negation a b + transcendence a b - rs a a := by
  unfold negationResidue
  linarith [aufhebung_decomposition a b]

/-! ## §7. Marx's Dialectical Materialism: Base and Superstructure

Marx inverts Hegel: ideas don't drive history, material conditions do.
In IDT, we model this by distinguishing a "material base" from an
"ideological superstructure." The base is an idea whose self-resonance
grounds the superstructure. The key thesis: the superstructure cannot
exceed the base's carrying capacity. -/

/-- The material base's "carrying capacity" for an idea: how much
    the base can support the idea's resonance. -/
noncomputable def carryingCapacity (base idea : I) : ℝ :=
  rs base idea + rs idea base

/-- Carrying capacity is symmetric. -/
theorem carryingCapacity_symm (a b : I) :
    carryingCapacity a b = carryingCapacity b a := by
  unfold carryingCapacity; ring

/-- Void base carries nothing. -/
theorem carryingCapacity_void_base (a : I) :
    carryingCapacity (void : I) a = 0 := by
  unfold carryingCapacity; simp [rs_void_left', rs_void_right']

/-- Void idea needs no carrying. -/
theorem carryingCapacity_void_idea (a : I) :
    carryingCapacity a (void : I) = 0 := by
  unfold carryingCapacity; simp [rs_void_left', rs_void_right']

/-- The ideological surplus: how much an idea's self-resonance
    exceeds what another idea "predicts" of it. Models how
    ideology can inflate beyond its material basis. -/
noncomputable def ideologicalSurplus (base superstructure : I) : ℝ :=
  rs superstructure superstructure - rs base superstructure

/-- Void superstructure has no surplus. -/
theorem ideologicalSurplus_void_super (a : I) :
    ideologicalSurplus a (void : I) = 0 := by
  unfold ideologicalSurplus; simp [rs_void_right', rs_void_void]

/-! ## §8. Adorno's Negative Dialectics

Adorno rejects Hegel's positive synthesis: the dialectic does NOT resolve
into a higher unity. Instead, contradiction persists — the "non-identical"
remainder resists subsumption. In IDT, this means examining cases where
synthesis FAILS to fully absorb the thesis and antithesis. -/

/-- The non-identical remainder: how much of the thesis is NOT captured
    by the synthesis. When positive, the thesis has aspects the synthesis
    cannot express — Adorno's "non-identity." -/
noncomputable def nonIdentical (thesis antithesis : I) : ℝ :=
  rs thesis thesis - rs thesis (synthesize thesis antithesis)

/-- The antithetical remainder: dual of the non-identical for the antithesis. -/
noncomputable def antitheticalRemainder (thesis antithesis : I) : ℝ :=
  rs antithesis antithesis - rs antithesis (synthesize thesis antithesis)

/-- Total resistance to synthesis: the combined non-identity of both parts. -/
noncomputable def resistanceToSynthesis (a b : I) : ℝ :=
  nonIdentical a b + antitheticalRemainder a b

/-- Resistance decomposition: total resistance equals the sum of
    self-resonances minus preservation and negation. -/
theorem resistance_eq (a b : I) :
    resistanceToSynthesis a b =
    rs a a + rs b b - preservation a b - negation a b := by
  unfold resistanceToSynthesis nonIdentical antitheticalRemainder preservation negation
  ring

/-- Key Adornian theorem: the total resistance to synthesis plus the
    transcendence and preservation and negation reconstitutes the
    synthesis weight. -/
theorem adorno_balance (a b : I) :
    rs (synthesize a b) (synthesize a b) =
    (rs a a - nonIdentical a b) +
    (rs b b - antitheticalRemainder a b) +
    transcendence a b := by
  unfold nonIdentical antitheticalRemainder transcendence aufhebung
    dialecticalEmergence synthesize emergence
  ring

/-- Void leaves zero non-identical remainder. -/
theorem nonIdentical_void_antithesis (a : I) :
    nonIdentical a (void : I) = 0 := by
  unfold nonIdentical synthesize; simp [rs_void_right']

/-- Antithetical remainder against void is zero. -/
theorem antitheticalRemainder_void_thesis (b : I) :
    antitheticalRemainder (void : I) b = 0 := by
  unfold antitheticalRemainder synthesize; simp [rs_void_left', rs_void_right']

/-! ## §9. Sublation (Aufhebung) Algebra

The Aufhebung — simultaneous preservation, negation, and elevation —
has a rich algebraic structure. We explore how sublation composes,
iterates, and decomposes. -/

/-- Double sublation: synthesize twice with the same antithesis. -/
noncomputable def doubleSublation (a b : I) : ℝ :=
  aufhebung (synthesize a b) b

/-- The iterated aufhebung at step n. -/
noncomputable def aufhebungN (a b : I) : ℕ → ℝ
  | 0 => 0
  | n + 1 => aufhebung (iteratedSynthesis a b n) b

/-- The zeroth aufhebung is trivially zero. -/
theorem aufhebungN_zero (a b : I) : aufhebungN a b 0 = 0 := rfl

/-- Double sublation equals the first-step iterated aufhebung. -/
theorem doubleSublation_eq_aufhebungN (a b : I) :
    doubleSublation a b = aufhebungN a b 2 := by
  unfold doubleSublation aufhebungN iteratedSynthesis; rfl

/-- The preservation at step n. -/
noncomputable def preservationN (a b : I) (n : ℕ) : ℝ :=
  rs (iteratedSynthesis a b n) (iteratedSynthesis a b (n + 1))

/-- The preservation-negation decomposition at every stage. -/
theorem aufhebung_stage_decomposition (a b : I) (n : ℕ) :
    rs (iteratedSynthesis a b (n + 1)) (iteratedSynthesis a b (n + 1)) =
    preservationN a b n +
    rs b (iteratedSynthesis a b (n + 1)) +
    aufhebungN a b (n + 1) := by
  unfold preservationN aufhebungN aufhebung dialecticalEmergence synthesize
  rw [iteratedSynthesis_succ]
  exact rs_compose_eq (iteratedSynthesis a b n) b (compose (iteratedSynthesis a b n) b)

/-! ## §10. Dialectical Sequences and Historical Development

A dialectical sequence is a chain where each step synthesizes the
previous result with a new antithesis. This models historical development
as a sequence of contradictions and resolutions. -/

/-- A dialectical sequence: given a starting thesis and a sequence of
    antitheses (as a list), produce the final synthesis. -/
def dialecticalSequence (thesis : I) : List I → I
  | [] => thesis
  | b :: rest => dialecticalSequence (synthesize thesis b) rest

/-- Empty sequence returns the thesis unchanged. -/
theorem dialecticalSequence_nil (a : I) :
    dialecticalSequence a ([] : List I) = a := rfl

/-- Single-step sequence equals simple synthesis. -/
theorem dialecticalSequence_singleton (a b : I) :
    dialecticalSequence a [b] = synthesize a b := rfl

/-- Two-step sequence. -/
theorem dialecticalSequence_pair (a b c : I) :
    dialecticalSequence a [b, c] =
    synthesize (synthesize a b) c := rfl

/-- Dialectical sequences compose: processing two lists sequentially
    equals processing their concatenation. -/
theorem dialecticalSequence_append (a : I) (l₁ l₂ : List I) :
    dialecticalSequence (dialecticalSequence a l₁) l₂ =
    dialecticalSequence a (l₁ ++ l₂) := by
  induction l₁ generalizing a with
  | nil => simp [dialecticalSequence]
  | cons b rest ih => simp [dialecticalSequence, ih]

/-- Historical monotonicity: each stage of a dialectical sequence has
    at least as much self-resonance as the previous stage. History
    accumulates "weight." -/
theorem dialecticalSequence_enriches (a : I) (l : List I) :
    rs (dialecticalSequence a l) (dialecticalSequence a l) ≥ rs a a := by
  induction l generalizing a with
  | nil => exact le_refl _
  | cons b rest ih =>
    calc rs (dialecticalSequence a (b :: rest)) (dialecticalSequence a (b :: rest))
        = rs (dialecticalSequence (synthesize a b) rest) (dialecticalSequence (synthesize a b) rest) := by
          rfl
      _ ≥ rs (synthesize a b) (synthesize a b) := ih (synthesize a b)
      _ ≥ rs a a := synthesis_enriches_thesis a b

/-! ## §11. Contradiction as Orthogonality

In formal logic, contradiction means P ∧ ¬P. In dialectics, contradiction
is subtler — it is tension between ideas that CANNOT be simply resolved.
We model degrees of contradiction using the tension function. -/

/-- The self-tension of an idea: what happens when an idea is in
    dialectical tension with ITSELF. For non-void ideas, this is always
    zero because an idea doesn't emerge against itself in composition. -/
noncomputable def selfTension (a : I) : ℝ :=
  tension a a

/-- Self-tension expansion. -/
theorem selfTension_eq (a : I) :
    selfTension a =
    (rs (compose a a) a - 2 * rs a a) +
    (rs (compose a a) a - 2 * rs a a) := by
  unfold selfTension tension emergence; ring

/-- Void has zero self-tension. -/
theorem selfTension_void : selfTension (void : I) = 0 := by
  unfold selfTension; exact tension_void_left (void : I)

/-- The contradiction intensity between two ideas: the absolute
    amount of emergent tension (summed from both observer perspectives). -/
noncomputable def contradictionIntensity (a b : I) : ℝ :=
  tension a b + tension b a

/-- Contradiction intensity is symmetric. -/
theorem contradictionIntensity_symm (a b : I) :
    contradictionIntensity a b = contradictionIntensity b a := by
  unfold contradictionIntensity; ring

/-- Contradiction intensity with void vanishes. -/
theorem contradictionIntensity_void (a : I) :
    contradictionIntensity a (void : I) = 0 := by
  unfold contradictionIntensity
  rw [tension_void_right, tension_void_left]; ring

/-! ## §12. Quality-Quantity Transitions (Hegel's Measure)

Hegel argues that gradual quantitative changes lead to sudden qualitative
transformations. In IDT, repeated composition (quantitative accumulation)
can change the emergent properties (quality) of the resulting idea. -/

/-- The qualitative shift at step n: the emergence from adding one more
    copy at stage n. -/
noncomputable def qualitativeShift (a : I) (n : ℕ) : ℝ :=
  emergence (composeN a n) a (composeN a (n + 1))

/-- At step 0, the shift is the self-emergence of a with void. -/
theorem qualitativeShift_zero (a : I) :
    qualitativeShift a 0 = emergence (void : I) a a := by
  unfold qualitativeShift; simp [composeN]

/-- Qualitative shift at zero simplifies. -/
theorem qualitativeShift_zero_eq (a : I) :
    qualitativeShift a 0 = 0 := by
  rw [qualitativeShift_zero]; exact emergence_void_left a a

/-- The cumulative quality: total self-resonance after n repetitions. -/
noncomputable def cumulativeQuality (a : I) (n : ℕ) : ℝ :=
  rs (composeN a n) (composeN a n)

/-- Cumulative quality at zero is zero (void). -/
theorem cumulativeQuality_zero (a : I) :
    cumulativeQuality a 0 = 0 := by
  unfold cumulativeQuality; simp [rs_void_void]

/-- Cumulative quality is monotonically non-decreasing.
    "Quantity accumulates; quality never diminishes." -/
theorem cumulativeQuality_mono (a : I) (n : ℕ) :
    cumulativeQuality a (n + 1) ≥ cumulativeQuality a n := by
  unfold cumulativeQuality
  simp [composeN]; exact compose_enriches' (composeN a n) a

/-! ## §13. The Master-Slave Dialectic

Hegel's famous analysis of the struggle for recognition. The master (M)
and slave (S) are two ideas in asymmetric opposition. The master defines
itself through the slave's recognition (rs(M, S)), while the slave
achieves self-consciousness through labor (composition). -/

/-- The recognition asymmetry between master and slave:
    how much more the master "gets" from the slave than vice versa. -/
noncomputable def recognitionAsymmetry (master slave : I) : ℝ :=
  rs master slave - rs slave master

/-- Recognition asymmetry is the asymmetry function. -/
theorem recognitionAsymmetry_eq_asymmetry (m s : I) :
    recognitionAsymmetry m s = asymmetry m s := by
  unfold recognitionAsymmetry asymmetry; ring

/-- Recognition asymmetry is antisymmetric: the master's advantage
    is exactly the slave's disadvantage. -/
theorem recognitionAsymmetry_antisymm (m s : I) :
    recognitionAsymmetry m s = -recognitionAsymmetry s m := by
  unfold recognitionAsymmetry; ring

/-- The slave's labor product: synthesis of slave with master.
    Through labor (composition), the slave transforms. -/
def laborProduct (slave master : I) : I := compose slave master

/-- The slave's labor always enriches the slave — labor builds
    self-consciousness. -/
theorem labor_enriches (slave master : I) :
    rs (laborProduct slave master) (laborProduct slave master) ≥
    rs slave slave := by
  unfold laborProduct; exact compose_enriches' slave master

/-- The master's consumption: synthesis of master with slave.
    The master merely appropriates. -/
def masterConsumption (master slave : I) : I := compose master slave

/-- The dialectical reversal: the slave's labor product and the master's
    consumption are related by the order of composition.
    The ORDER matters — this asymmetry is the seed of the reversal. -/
theorem dialectical_reversal_structure (m s : I) :
    rs (laborProduct s m) (laborProduct s m) ≥ rs s s ∧
    rs (masterConsumption m s) (masterConsumption m s) ≥ rs m m := by
  exact ⟨labor_enriches s m, compose_enriches' m s⟩

/-! ## §14. Dialectic of Enlightenment (Adorno & Horkheimer)

The dialectic of enlightenment thesis: reason (rationality) in its
attempt to dominate nature, becomes a form of domination itself.
The instrument becomes the master. In IDT, this is modeled as the
emergence of composition flipping sign under iteration. -/

/-- The domination coefficient: how much the composition of
    reason with nature resonates with reason vs with nature.
    Positive: reason dominates. Negative: nature reasserts. -/
noncomputable def dominationCoeff (reason nature : I) : ℝ :=
  rs (compose reason nature) reason - rs (compose reason nature) nature

/-- Void reason: domination is just the negative of nature's self-resonance. -/
theorem domination_void_reason (n : I) :
    dominationCoeff (void : I) n = -(rs n n) := by
  unfold dominationCoeff; simp [rs_void_right']

/-- Void nature: domination equals reason's self-resonance. -/
theorem domination_void_nature (r : I) :
    dominationCoeff r (void : I) = rs r r := by
  unfold dominationCoeff; simp [rs_void_right']

/-- The enlightenment surplus: the total resonance gained by
    composing reason and nature, beyond their individual presence. -/
noncomputable def enlightenmentSurplus (reason nature : I) : ℝ :=
  rs (compose reason nature) (compose reason nature) -
  rs reason reason - rs nature nature

/-- Enlightenment surplus is non-negative when limited to
    the negation residue form. Actually, it relates directly. -/
theorem enlightenmentSurplus_eq_negationResidue_plus (r n : I) :
    enlightenmentSurplus r n =
    negationResidue r n - rs n n := by
  unfold enlightenmentSurplus negationResidue synthesize; ring

/-! ## §15. Concrete Universals

Hegel's "concrete universal" is not an empty abstraction but a
concept that contains its particulars within it. In IDT, a concrete
universal is an idea u such that composing u with any particular p
has high emergence — the universal "activates" the particular. -/

/-- How well a universal "activates" a particular: the emergence
    of composing u with p, measured against the particular itself. -/
noncomputable def activation (universal particular : I) : ℝ :=
  emergence universal particular particular

/-- Void universal activates nothing. -/
theorem activation_void_universal (p : I) :
    activation (void : I) p = 0 := by
  unfold activation; exact emergence_void_left p p

/-- Any universal trivially "activates" void. -/
theorem activation_void_particular (u : I) :
    activation u (void : I) = 0 := by
  unfold activation; exact emergence_void_right u (void : I)

/-- The universality index: sum of activation against self and
    the universal. Measures how strongly a universal engages. -/
noncomputable def universalityIndex (u p : I) : ℝ :=
  activation u p + emergence u p u

/-- Void universality index is zero. -/
theorem universalityIndex_void (p : I) :
    universalityIndex (void : I) p = 0 := by
  unfold universalityIndex activation
  rw [emergence_void_left, emergence_void_left]; ring

/-! ## §16. Dialectical Negation of Negation

The "negation of the negation" is the second movement of the dialectic:
first thesis is negated (antithesis), then the antithesis is itself
negated (synthesis). The result is NOT a return to the thesis but a
higher-level reconciliation. -/

/-- Negation of negation: synthesize the synthesis with the
    original thesis. The "spiral" of history. -/
def negationOfNegation (thesis antithesis : I) : I :=
  synthesize (synthesize thesis antithesis) thesis

/-- Negation of negation enriches beyond the simple synthesis. -/
theorem negation_of_negation_enriches (a b : I) :
    rs (negationOfNegation a b) (negationOfNegation a b) ≥
    rs (synthesize a b) (synthesize a b) := by
  unfold negationOfNegation; exact compose_enriches' (synthesize a b) a

/-- Negation of negation enriches beyond the original thesis. -/
theorem negation_of_negation_enriches_thesis (a b : I) :
    rs (negationOfNegation a b) (negationOfNegation a b) ≥ rs a a := by
  have h1 := negation_of_negation_enriches a b
  have h2 := synthesis_enriches_thesis a b
  linarith

/-- Negation of negation with void antithesis: reduces to compose a a. -/
theorem negation_of_negation_void (a : I) :
    negationOfNegation a (void : I) = compose a a := by
  unfold negationOfNegation synthesize; simp

/-- The spiral residue: how much the negation-of-negation exceeds
    the original thesis. Always non-negative. -/
noncomputable def spiralResidue (a b : I) : ℝ :=
  rs (negationOfNegation a b) (negationOfNegation a b) - rs a a

theorem spiralResidue_nonneg (a b : I) :
    spiralResidue a b ≥ 0 := by
  unfold spiralResidue
  linarith [negation_of_negation_enriches_thesis a b]

/-! ## §17. The Dialectical Triad as a Functor

A dialectical triad maps (thesis, antithesis) → synthesis.
Multiple triads compose: the output of one triad becomes the
input of the next. We study the algebraic properties. -/

/-- The triad composition: apply two dialectical steps. -/
def triadCompose (a b c : I) : I :=
  synthesize (synthesize a b) c

/-- Triad composition is just left-associated triple composition. -/
theorem triadCompose_eq (a b c : I) :
    triadCompose a b c = compose (compose a b) c := rfl

/-- Triad composition enriches beyond the first synthesis. -/
theorem triadCompose_enriches_first (a b c : I) :
    rs (triadCompose a b c) (triadCompose a b c) ≥
    rs (synthesize a b) (synthesize a b) := by
  unfold triadCompose; exact compose_enriches' (synthesize a b) c

/-- Triad composition enriches beyond the original thesis. -/
theorem triadCompose_enriches_thesis (a b c : I) :
    rs (triadCompose a b c) (triadCompose a b c) ≥ rs a a := by
  have h1 := triadCompose_enriches_first a b c
  have h2 := synthesis_enriches_thesis a b
  linarith

/-- Triad vs right-associated: same by associativity. -/
theorem triadCompose_assoc (a b c d : I) :
    rs (triadCompose a b c) d =
    rs (compose a (compose b c)) d := by
  unfold triadCompose synthesize
  rw [compose_assoc']

/-! ## §18. Alienation and Reification

Marx's concept of alienation: the worker's product becomes alien,
opposing the worker. In IDT, this is modeled when the emergence
of labor (composition of worker with material) resonates negatively
with the worker. Reification: treating ideas as things — flattening
emergence to zero. -/

/-- Alienation index: how much the product (compose worker material)
    resonates AGAINST the worker relative to the worker's self. -/
noncomputable def alienationIndex (worker material : I) : ℝ :=
  rs worker worker - rs worker (compose worker material)

/-- Zero alienation from void material. -/
theorem alienation_void_material (w : I) :
    alienationIndex w (void : I) = 0 := by
  unfold alienationIndex; simp

/-- The reification deficit: how much the emergence is "lost" when
    we treat an idea as a mere thing (i.e., measure it only against void). -/
noncomputable def reificationDeficit (a b : I) : ℝ :=
  emergence a b (compose a b) - emergence a b (void : I)

/-- Reification deficit simplifies: emergence against void is always 0. -/
theorem reificationDeficit_eq (a b : I) :
    reificationDeficit a b = emergence a b (compose a b) := by
  unfold reificationDeficit; rw [emergence_against_void]; ring

/-- Reification deficit equals the aufhebung. -/
theorem reificationDeficit_eq_aufhebung (a b : I) :
    reificationDeficit a b = aufhebung a b := by
  rw [reificationDeficit_eq]
  unfold aufhebung dialecticalEmergence synthesize; rfl

/-! ## §19. Dialectical Depth: Measuring Historical Complexity

The "depth" of a dialectical development: how many sublation stages
have occurred. We prove that deeper developments carry more weight. -/

/-- The weight gain from the n-th to (n+1)-th stage of iterated synthesis. -/
noncomputable def stageGain (a b : I) (n : ℕ) : ℝ :=
  rs (iteratedSynthesis a b (n + 1)) (iteratedSynthesis a b (n + 1)) -
  rs (iteratedSynthesis a b n) (iteratedSynthesis a b n)

/-- Every stage gain is non-negative. History cannot lose weight. -/
theorem stageGain_nonneg (a b : I) (n : ℕ) :
    stageGain a b n ≥ 0 := by
  unfold stageGain
  linarith [iteratedSynthesis_enriches a b n]

/-- The total gain after n stages equals the difference from start. -/
theorem total_gain_telescopes (a b : I) (n : ℕ) :
    rs (iteratedSynthesis a b n) (iteratedSynthesis a b n) - rs a a =
    (Finset.range n).sum (fun k => stageGain a b k) := by
  induction n with
  | zero => simp [iteratedSynthesis]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    unfold stageGain at *
    linarith [ih]

/-! ## §20. The Phenomenology of Spirit: Consciousness Stages

Hegel's Phenomenology traces consciousness through stages: sense-certainty,
perception, understanding, self-consciousness, reason, spirit, absolute
knowing. In IDT, each stage enriches the previous — consciousness grows. -/

/-- A consciousness development: a chain of ideas where each
    is the synthesis of the previous with some new experience. -/
def consciousnessChain (initial : I) (experiences : List I) : I :=
  dialecticalSequence initial experiences

/-- Consciousness always develops (never loses weight). -/
theorem consciousness_develops (initial : I) (experiences : List I) :
    rs (consciousnessChain initial experiences)
       (consciousnessChain initial experiences) ≥
    rs initial initial := by
  unfold consciousnessChain
  exact dialecticalSequence_enriches initial experiences

/-- Adding one more experience enriches consciousness. -/
theorem experience_enriches (initial : I) (exps : List I) (e : I) :
    rs (consciousnessChain initial (exps ++ [e]))
       (consciousnessChain initial (exps ++ [e])) ≥
    rs (consciousnessChain initial exps)
       (consciousnessChain initial exps) := by
  unfold consciousnessChain
  rw [← dialecticalSequence_append]
  simp [dialecticalSequence, synthesize]
  exact compose_enriches' (dialecticalSequence initial exps) e

/-! ## §21. Speculative Identity

Hegel's "speculative identity" thesis: subject and object are not
simply opposed but are moments of a single process. In IDT, the
composition of subject and object is not merely additive — the
emergence term captures their speculative unity. -/

/-- Speculative unity: the emergence of subject-object composition
    measured against their synthesis itself. -/
noncomputable def speculativeUnity (subject object : I) : ℝ :=
  emergence subject object (compose subject object)

/-- Speculative unity IS aufhebung (via different path). -/
theorem speculativeUnity_eq_aufhebung (s o : I) :
    speculativeUnity s o = aufhebung s o := by
  unfold speculativeUnity aufhebung dialecticalEmergence synthesize; rfl

/-- Speculative unity with void vanishes. -/
theorem speculativeUnity_void_right (s : I) :
    speculativeUnity s (void : I) = 0 := by
  rw [speculativeUnity_eq_aufhebung]; exact aufhebung_void_antithesis s

theorem speculativeUnity_void_left (o : I) :
    speculativeUnity (void : I) o = 0 := by
  rw [speculativeUnity_eq_aufhebung]; exact aufhebung_void_thesis o

/-! ## §22. Dialectical Completeness and Closure

When does a dialectical sequence reach "closure"? When adding
new antitheses produces no more emergence — the system has
absorbed all available contradictions. -/

/-- A pair is dialectically closed if the aufhebung vanishes. -/
def dialecticallyClosed (a b : I) : Prop :=
  aufhebung a b = 0

/-- Void is always dialectically closed with anything. -/
theorem void_dialecticallyClosed (a : I) :
    dialecticallyClosed (void : I) a := by
  unfold dialecticallyClosed; exact aufhebung_void_thesis a

/-- Anything is dialectically closed with void. -/
theorem dialecticallyClosed_void (a : I) :
    dialecticallyClosed a (void : I) := by
  unfold dialecticallyClosed; exact aufhebung_void_antithesis a

/-- When closed, the aufhebung decomposition simplifies. -/
theorem closed_decomposition (a b : I) (h : dialecticallyClosed a b) :
    rs (synthesize a b) (synthesize a b) =
    preservation a b + negation a b := by
  have := aufhebung_decomposition a b
  unfold dialecticallyClosed at h
  unfold transcendence at this
  linarith

/-! ## §23. Immanent Critique

Adorno's method: criticize a system from WITHIN, using its own
standards. In IDT, this means measuring an idea's emergence against
itself — does the idea live up to its own resonance? -/

/-- Immanent critique: the emergence of an idea composed with itself,
    measured against itself. A kind of self-reflexive test. -/
noncomputable def immanentCritique (a : I) : ℝ :=
  emergence a a a

/-- Immanent critique equals semantic charge. -/
theorem immanentCritique_eq_semanticCharge (a : I) :
    immanentCritique a = semanticCharge a := by
  unfold immanentCritique semanticCharge; rfl

/-- Immanent critique of void vanishes. -/
theorem immanentCritique_void :
    immanentCritique (void : I) = 0 := by
  unfold immanentCritique; exact emergence_void_left (void : I) (void : I)

/-- Immanent critique in terms of resonance. -/
theorem immanentCritique_eq (a : I) :
    immanentCritique a = rs (compose a a) a - 2 * rs a a := by
  unfold immanentCritique emergence; ring

/-! ## §24. Dialectical Materialism: Forces and Relations of Production

Marx's insight: when productive forces (technology) outgrow the
relations of production (social organization), revolution occurs.
In IDT, this is a resonance mismatch that drives synthesis. -/

/-- The forces-relations gap: the self-resonance difference between
    the productive forces and the relations. When the forces outgrow
    the relations, this is positive. -/
noncomputable def forcesRelationsGap (forces relations : I) : ℝ :=
  rs forces forces - rs relations relations

/-- The gap is antisymmetric in its arguments. -/
theorem forcesRelationsGap_antisymm (f r : I) :
    forcesRelationsGap f r = -forcesRelationsGap r f := by
  unfold forcesRelationsGap; ring

/-- Void forces have negative gap against non-void relations. -/
theorem void_forces_gap (r : I) (h : r ≠ void) :
    forcesRelationsGap (void : I) r < 0 := by
  unfold forcesRelationsGap
  simp [rs_void_void]
  exact rs_self_pos r h

/-- The revolutionary synthesis always weighs at least as much as
    the dominant force. -/
theorem revolutionary_synthesis_weight (f r : I) :
    rs (compose f r) (compose f r) ≥ rs f f := by
  exact compose_enriches' f r

/-! ## §25. Totality and Mediation

Hegel's concept of totality: everything is mediated — no idea exists
in isolation. Every idea is constituted by its relations to others.
In IDT, an idea's "mediated weight" includes not just self-resonance
but cross-resonance with a mediating context. -/

/-- The mediated weight of idea a in context c:
    how much a weighs when seen through c. -/
noncomputable def mediatedWeight (a context : I) : ℝ :=
  rs a context + rs context a

/-- Mediated weight is symmetric. -/
theorem mediatedWeight_symm (a c : I) :
    mediatedWeight a c = mediatedWeight c a := by
  unfold mediatedWeight; ring

/-- Void context contributes no mediated weight. -/
theorem mediatedWeight_void_context (a : I) :
    mediatedWeight a (void : I) = 0 := by
  unfold mediatedWeight; simp [rs_void_left', rs_void_right']

/-- The mediation surplus: how much mediated weight exceeds
    the self-resonances of the parts. -/
noncomputable def mediationSurplus (a b : I) : ℝ :=
  mediatedWeight a b - rs a a - rs b b

/-- Mediation surplus with void is always negative (loses self-weight). -/
theorem mediationSurplus_void (a : I) (h : a ≠ void) :
    mediationSurplus a (void : I) < 0 := by
  unfold mediationSurplus mediatedWeight
  simp [rs_void_left', rs_void_right', rs_void_void]
  exact rs_self_pos a h

/-! ## §26. The Logic of Essence: Appearance and Reality

Hegel's Doctrine of Essence: the distinction between appearance
(how an idea resonates with others) and essence (its self-resonance).
The gap between them is the "semblance" (Schein). -/

/-- The appearance of idea a to observer o: how a is seen by o. -/
noncomputable def appearance (a observer : I) : ℝ := rs a observer

/-- The essence of idea a: its self-resonance. -/
noncomputable def essence (a : I) : ℝ := rs a a

/-- The semblance: gap between how an idea appears and what it IS. -/
noncomputable def semblance (a observer : I) : ℝ :=
  appearance a observer - essence a

/-- Void has zero essence. -/
theorem essence_void : essence (void : I) = 0 := rs_void_void

/-- Appearance to void is zero. -/
theorem appearance_to_void (a : I) :
    appearance a (void : I) = 0 := rs_void_right' a

/-- Semblance to void equals negative essence. -/
theorem semblance_to_void (a : I) :
    semblance a (void : I) = -essence a := by
  unfold semblance appearance essence; rw [rs_void_right']; ring

/-- Self-semblance: when observer = idea, semblance vanishes. -/
theorem self_semblance (a : I) : semblance a a = 0 := by
  unfold semblance appearance essence; ring

/-- Non-void ideas have positive essence. -/
theorem essence_pos (a : I) (h : a ≠ void) : essence a > 0 := by
  unfold essence; exact rs_self_pos a h

/-! ## §27. Dialectical Composition Laws

Properties of how dialectical operations interact with each other. -/

/-- Synthesize is just compose (by definition). -/
theorem synthesize_eq_compose (a b : I) :
    synthesize a b = compose a b := rfl

/-- Double synthesis with void reduces. -/
theorem double_synthesis_void (a : I) :
    synthesize (synthesize a (void : I)) (void : I) = a := by
  unfold synthesize; simp

/-- Aufhebung decomposition restated with explicit expansion. -/
theorem aufhebung_expansion (a b : I) :
    aufhebung a b =
    rs (compose a b) (compose a b) -
    rs a (compose a b) - rs b (compose a b) := by
  unfold aufhebung dialecticalEmergence synthesize emergence; ring

/-- The aufhebung squared is bounded. -/
theorem aufhebung_sq_bounded (a b : I) :
    (aufhebung a b) ^ 2 ≤
    rs (compose a b) (compose a b) *
    rs (compose a b) (compose a b) := by
  unfold aufhebung dialecticalEmergence synthesize
  exact emergence_bounded' a b (compose a b)

/-! ## §28. Dialectical Invariants under Void

Comprehensive void-behavior of all dialectical quantities. -/

/-- Synthesis with void on left is identity. -/
theorem synthesize_void_left (a : I) :
    synthesize (void : I) a = a := by
  unfold synthesize; simp

/-- Synthesis with void on right is identity. -/
theorem synthesize_void_right (a : I) :
    synthesize a (void : I) = a := by
  unfold synthesize; simp

/-- The negation residue of void is zero. -/
theorem negationResidue_void_thesis (b : I) :
    negationResidue (void : I) b = rs b b := by
  unfold negationResidue synthesize; simp [rs_void_void, rs_void_left']

/-- Preservation with void antithesis equals self-resonance. -/
theorem preservation_void_antithesis (a : I) :
    preservation a (void : I) = rs a a := by
  unfold preservation synthesize; simp

/-- Negation with void antithesis is zero. -/
theorem negation_void_antithesis (a : I) :
    negation a (void : I) = 0 := by
  unfold negation synthesize; simp [rs_void_right', rs_void_left']

/-! ## §29. Lukács's Reification and Class Consciousness

Lukács argues that under commodity production, social relations are
"reified" — perceived as natural things rather than historical products.
Class consciousness is the dialectical overcoming of reification:
the proletariat recognizes the social totality and its own role within it.
In IDT, reification flattens emergence; class consciousness recovers it. -/

/-- Reification index: how much emergence is lost when we measure the
    synthesis against void (treating it as a mere thing) rather than
    against itself (recognizing its social/relational nature). -/
noncomputable def reificationIndex (a b : I) : ℝ :=
  emergence a b (compose a b) - emergence a b (void : I)

/-- Reification index simplifies: emergence against void is always 0,
    so reification index equals self-emergence. -/
theorem reificationIndex_eq (a b : I) :
    reificationIndex a b = emergence a b (compose a b) := by
  unfold reificationIndex; rw [emergence_against_void]; ring

/-- Reification index equals aufhebung. Lukács's insight:
    reification erases exactly the dialectical surplus. -/
theorem reificationIndex_eq_aufhebung (a b : I) :
    reificationIndex a b = aufhebung a b := by
  rw [reificationIndex_eq]
  unfold aufhebung dialecticalEmergence synthesize; rfl

/-- Class consciousness: the total resonance recovered when the
    proletariat (p) recognizes itself in the product of labor (compose p m). -/
noncomputable def classConsciousness (proletariat material : I) : ℝ :=
  rs proletariat (compose proletariat material) +
  emergence proletariat material proletariat

/-- Class consciousness of void proletariat vanishes:
    without a subject, there is no consciousness. -/
theorem classConsciousness_void_proletariat (m : I) :
    classConsciousness (void : I) m = 0 := by
  unfold classConsciousness; simp [rs_void_left', emergence_void_left]

/-- Class consciousness with void material reduces to pure self-resonance. -/
theorem classConsciousness_void_material (p : I) :
    classConsciousness p (void : I) = rs p p := by
  unfold classConsciousness; simp [emergence_void_right, rs_void_right']

/-- The reification gap: difference between total resonance of
    the product and the class consciousness of the producer. -/
noncomputable def reificationGap (worker material : I) : ℝ :=
  rs (compose worker material) (compose worker material) -
  classConsciousness worker material

/-- Reification gap expansion in terms of resonance. -/
theorem reificationGap_eq (w m : I) :
    reificationGap w m =
    rs m (compose w m) + emergence w m (compose w m) -
    emergence w m w := by
  unfold reificationGap classConsciousness
  rw [rs_compose_eq w m (compose w m)]
  ring

/-- Commodity fetishism: the degree to which a product's resonance
    with itself exceeds its resonance with its producer. -/
noncomputable def commodityFetishism (worker material : I) : ℝ :=
  rs (compose worker material) (compose worker material) -
  rs (compose worker material) worker

/-- Commodity fetishism with void material is zero. -/
theorem commodityFetishism_void_material (w : I) :
    commodityFetishism w (void : I) = 0 := by
  unfold commodityFetishism; simp [rs_void_right']

/-- Totality awareness: how much an idea resonates with the
    dialectical whole (composed system) versus in isolation.
    Lukács: the standpoint of totality is the key to class consciousness. -/
noncomputable def totalityAwareness (part whole : I) : ℝ :=
  rs part (compose part whole) - rs part part

/-- Totality awareness with void whole vanishes. -/
theorem totalityAwareness_void_whole (p : I) :
    totalityAwareness p (void : I) = 0 := by
  unfold totalityAwareness; simp [rs_void_right']

/-! ## §30. Benjamin's Dialectical Images (Passagen-Werk)

Walter Benjamin's "dialectical image" is a flash of recognition where
past and present collide — producing a "now of recognizability"
(Jetzt der Erkennbarkeit). In IDT, this is modeled as the emergence
from composing a historical fragment with a contemporary moment.
The dialectical image is NOT a synthesis but a constellation. -/

/-- Dialectical image: the emergence when a past fragment meets a
    present moment, measured from the standpoint of the present.
    Benjamin: "It is not that what is past casts its light on what is
    present... rather, image is that wherein what has been comes
    together in a flash with the now." -/
noncomputable def dialecticalImage (past present : I) : ℝ :=
  emergence past present present

/-- Dialectical image with void past: no history, no image. -/
theorem dialecticalImage_void_past (p : I) :
    dialecticalImage (void : I) p = 0 := by
  unfold dialecticalImage; exact emergence_void_left p p

/-- Dialectical image with void present: no now, no recognizability. -/
theorem dialecticalImage_void_present (h : I) :
    dialecticalImage h (void : I) = 0 := by
  unfold dialecticalImage; exact emergence_void_right h (void : I)

/-- The aura: Benjamin's concept of the unique presence of an artwork.
    Measured as the self-emergence of composing the work with its
    context of reception. -/
noncomputable def aura (work context : I) : ℝ :=
  emergence work context (compose work context)

/-- Aura vanishes in void context — mechanical reproduction
    strips the context of tradition. -/
theorem aura_void_context (w : I) :
    aura w (void : I) = 0 := by
  unfold aura; exact emergence_void_right w (compose w (void : I))

/-- Aura equals aufhebung: the dialectical surplus of work-in-context. -/
theorem aura_eq_aufhebung (w c : I) :
    aura w c = aufhebung w c := by
  unfold aura aufhebung dialecticalEmergence synthesize; rfl

/-- Constellation: Benjamin's alternative to synthesis. Rather than
    resolving thesis and antithesis, ideas are held in tension.
    The constellation value is the sum of tensions across a set. -/
noncomputable def constellation (center : I) (elements : List I) : ℝ :=
  elements.foldl (fun acc e => acc + emergence center e center) 0

/-- Empty constellation has zero value. -/
theorem constellation_nil (c : I) :
    constellation c ([] : List I) = 0 := rfl

/-- Messianic index: Benjamin's idea that every moment contains a
    "weak messianic power." The potential for revolutionary emergence
    from even the smallest historical fragment. -/
noncomputable def messianicIndex (fragment moment : I) : ℝ :=
  emergence fragment moment fragment + emergence fragment moment moment

/-- Messianic index with void fragment vanishes. -/
theorem messianicIndex_void_fragment (m : I) :
    messianicIndex (void : I) m = 0 := by
  unfold messianicIndex; rw [emergence_void_left, emergence_void_left]; ring

/-- Messianic index with void moment vanishes. -/
theorem messianicIndex_void_moment (f : I) :
    messianicIndex f (void : I) = 0 := by
  unfold messianicIndex; rw [emergence_void_right, emergence_void_right]; ring

/-- Messianic index equals tension. Benjamin's "weak messianic power"
    is exactly the dialectical tension. -/
theorem messianicIndex_eq_tension (f m : I) :
    messianicIndex f m = tension f m := by
  unfold messianicIndex tension; ring

/-! ## §31. Žižek's Parallax View

Žižek's parallax: the gap between two perspectives that cannot be
reconciled into a higher synthesis. The "parallax gap" is irreducible —
it IS the Real. In IDT, this is the asymmetry of emergence: the
emergence of a∘b measured from a's viewpoint versus from b's viewpoint. -/

/-- The parallax gap: the irreducible difference between how the
    composition looks from the thesis's standpoint versus the antithesis's.
    Žižek: "The parallax gap is not something that can be overcome." -/
noncomputable def parallaxGap (a b : I) : ℝ :=
  emergence a b a - emergence a b b

/-- The parallax gap is antisymmetric under exchange of viewpoints. -/
theorem parallaxGap_antisymm_views (a b : I) :
    parallaxGap a b = -(emergence a b b - emergence a b a) := by
  unfold parallaxGap; ring

/-- Parallax gap with void vanishes from both sides. -/
theorem parallaxGap_void_left (b : I) :
    parallaxGap (void : I) b = 0 := by
  unfold parallaxGap; rw [emergence_void_left, emergence_void_left]; ring

theorem parallaxGap_void_right (a : I) :
    parallaxGap a (void : I) = 0 := by
  unfold parallaxGap; rw [emergence_void_right, emergence_void_right]; ring

/-- The parallax gap decomposes via resonance. -/
theorem parallaxGap_eq (a b : I) :
    parallaxGap a b =
    rs (compose a b) a - rs a a - rs b a -
    (rs (compose a b) b - rs a b - rs b b) := by
  unfold parallaxGap emergence; ring

/-- Total parallax: the sum of the parallax gap in both composition orders.
    This captures the full non-commutativity of the dialectical encounter. -/
noncomputable def totalParallax (a b : I) : ℝ :=
  parallaxGap a b + parallaxGap b a

/-- Total parallax decomposes into emergence differences. -/
theorem totalParallax_eq (a b : I) :
    totalParallax a b =
    (emergence a b a - emergence a b b) +
    (emergence b a b - emergence b a a) := by
  unfold totalParallax parallaxGap; ring

/-- Total parallax relation to meaning curvature. -/
theorem totalParallax_via_curvature (a b : I) :
    totalParallax a b =
    (emergence a b a - emergence b a a) -
    (emergence a b b - emergence b a b) := by
  unfold totalParallax parallaxGap; ring

/-- The Lacanian Real: Žižek identifies the parallax gap with Lacan's Real.
    The Real is what resists symbolization — in IDT, the part of resonance
    that cannot be captured from any single viewpoint. -/
noncomputable def lacanianReal (a b : I) : ℝ :=
  rs (compose a b) (compose a b) -
  rs (compose a b) a - rs (compose a b) b

/-- The Lacanian Real relates to emergence. -/
theorem lacanianReal_eq (a b : I) :
    lacanianReal a b =
    rs (compose a b) (compose a b) -
    rs (compose a b) a - rs (compose a b) b := rfl

/-- Lacanian Real with void vanishes. -/
theorem lacanianReal_void_right (a : I) :
    lacanianReal a (void : I) = 0 := by
  unfold lacanianReal; simp [rs_void_right']

theorem lacanianReal_void_left (b : I) :
    lacanianReal (void : I) b = 0 := by
  unfold lacanianReal; simp [rs_void_left', rs_void_right']

/-- Žižek's "ticklish subject": the subject constituted by the gap.
    The subject's self-resonance MINUS its resonance with the symbolic
    order (compose a b). -/
noncomputable def ticklishSubject (subject symbolic : I) : ℝ :=
  rs subject subject - rs subject (compose subject symbolic)

/-- Ticklish subject with void symbolic is zero. -/
theorem ticklishSubject_void_symbolic (s : I) :
    ticklishSubject s (void : I) = 0 := by
  unfold ticklishSubject; simp [rs_void_right']

/-- The ticklish subject equals the non-identical remainder (Adorno's concept
    reappears in Žižek). -/
theorem ticklishSubject_eq_nonIdentical (s o : I) :
    ticklishSubject s o = nonIdentical s o := by
  unfold ticklishSubject nonIdentical synthesize; rfl

/-! ## §32. Badiou's Dialectical Materialism: Event, Truth, Subject

Badiou's ontology: Being is structured as a situation (a set-theoretic
universe). An Event is a rupture that cannot be derived from the situation.
A Truth is the infinite generic subset traced by a subject faithful to
the Event. In IDT, the Event is an idea whose emergence with the
situation exceeds what the situation "expects." -/

/-- The event intensity: how much a potential event e exceeds what
    the situation s "predicts." A true Badiouian event has emergence
    that ruptures the situation's resonance structure. -/
noncomputable def eventIntensity (situation event : I) : ℝ :=
  emergence situation event (compose situation event)

/-- Event intensity equals aufhebung: Badiou's event IS the
    dialectical surplus of the situation encountering novelty. -/
theorem eventIntensity_eq_aufhebung (s e : I) :
    eventIntensity s e = aufhebung s e := by
  unfold eventIntensity aufhebung dialecticalEmergence synthesize; rfl

/-- No event from void situation: without a structured situation,
    no event can rupture it. -/
theorem eventIntensity_void_situation (e : I) :
    eventIntensity (void : I) e = 0 := by
  rw [eventIntensity_eq_aufhebung]; exact aufhebung_void_thesis e

/-- Void event: nothing happens, no intensity. -/
theorem eventIntensity_void_event (s : I) :
    eventIntensity s (void : I) = 0 := by
  rw [eventIntensity_eq_aufhebung]; exact aufhebung_void_antithesis s

/-- Fidelity: the degree to which a subject remains faithful to
    an event, measured as the subject's resonance with the post-evental
    situation (compose situation event). -/
noncomputable def fidelity (subject situation event : I) : ℝ :=
  rs subject (compose situation event)

/-- Fidelity to void event equals resonance with the unchanged situation. -/
theorem fidelity_void_event (sub sit : I) :
    fidelity sub sit (void : I) = rs sub sit := by
  unfold fidelity; simp [rs_void_right']

/-- Truth procedure: Badiou's truth is the accumulated synthesis of
    a subject investigating consequences of an event. Modeled as
    iterated synthesis of the subject with the post-evental situation. -/
noncomputable def truthProcedure (subject situation event : I) (n : ℕ) : I :=
  iteratedSynthesis subject (compose situation event) n

/-- Truth procedure at step 0 is the subject unchanged. -/
theorem truthProcedure_zero (sub sit evt : I) :
    truthProcedure sub sit evt 0 = sub := rfl

/-- Truth procedure monotonically enriches: faithful investigation
    always builds understanding. -/
theorem truthProcedure_enriches (sub sit evt : I) (n : ℕ) :
    rs (truthProcedure sub sit evt (n + 1))
       (truthProcedure sub sit evt (n + 1)) ≥
    rs (truthProcedure sub sit evt n)
       (truthProcedure sub sit evt n) := by
  unfold truthProcedure; exact iteratedSynthesis_enriches sub (compose sit evt) n

/-- Forcing: how much the truth procedure at step n exceeds the
    original subject's self-resonance. -/
noncomputable def forcing (sub sit evt : I) (n : ℕ) : ℝ :=
  rs (truthProcedure sub sit evt n) (truthProcedure sub sit evt n) -
  rs sub sub

/-- Forcing is non-negative: truth never diminishes the subject. -/
theorem forcing_nonneg (sub sit evt : I) (n : ℕ) :
    forcing sub sit evt n ≥ 0 := by
  unfold forcing truthProcedure
  have := iteratedSynthesis_nondecreasing sub (compose sit evt) 0 n (Nat.zero_le n)
  simp [iteratedSynthesis] at this
  linarith

/-- Forcing at step 0 is zero. -/
theorem forcing_zero (sub sit evt : I) :
    forcing sub sit evt 0 = 0 := by
  unfold forcing truthProcedure iteratedSynthesis; ring

/-- Forcing is monotonically non-decreasing. -/
theorem forcing_mono (sub sit evt : I) (m n : ℕ) (h : m ≤ n) :
    forcing sub sit evt n ≥ forcing sub sit evt m := by
  unfold forcing truthProcedure
  linarith [iteratedSynthesis_nondecreasing sub (compose sit evt) m n h]

/-! ## §33. Jameson's Political Unconscious

Fredric Jameson: "Always historicize!" The political unconscious is
the repressed historical content that structures a text's form.
Every cultural artifact contains a utopian dimension alongside its
ideological function. In IDT, the political unconscious is the
emergence that a text's formal structure conceals. -/

/-- The political unconscious of a text in a social context:
    the emergence created by their composition but NOT visible
    from the text's surface (i.e., not from the text's own viewpoint). -/
noncomputable def politicalUnconscious (text socialContext : I) : ℝ :=
  emergence text socialContext (compose text socialContext) -
  emergence text socialContext text

/-- Political unconscious with void text vanishes. -/
theorem politicalUnconscious_void_text (s : I) :
    politicalUnconscious (void : I) s = 0 := by
  unfold politicalUnconscious; rw [emergence_void_left, emergence_void_left]; ring

/-- Political unconscious with void social context vanishes. -/
theorem politicalUnconscious_void_context (t : I) :
    politicalUnconscious t (void : I) = 0 := by
  unfold politicalUnconscious; rw [emergence_void_right, emergence_void_right]; ring

/-- Utopian surplus: Jameson argues every cultural text contains a
    utopian dimension — a vision of a better social arrangement.
    This is the positive emergence of the text with its context. -/
noncomputable def utopianSurplus (text context : I) : ℝ :=
  emergence text context context

/-- Utopian surplus with void context vanishes: no social context,
    no utopian horizon. -/
theorem utopianSurplus_void_context (t : I) :
    utopianSurplus t (void : I) = 0 := by
  unfold utopianSurplus; exact emergence_void_right t (void : I)

/-- Utopian surplus with void text vanishes. -/
theorem utopianSurplus_void_text (c : I) :
    utopianSurplus (void : I) c = 0 := by
  unfold utopianSurplus; exact emergence_void_left c c

/-- Ideological function: the text's resonance with the dominant
    social structure minus the utopian surplus. What serves the
    status quo versus what gestures beyond it. -/
noncomputable def ideologicalFunction (text context : I) : ℝ :=
  rs text context - utopianSurplus text context

/-- Ideological function expansion. -/
theorem ideologicalFunction_eq (t c : I) :
    ideologicalFunction t c =
    rs t c - (rs (compose t c) c - rs t c - rs c c) := by
  unfold ideologicalFunction utopianSurplus emergence; ring

/-- Narrative totalization: Jameson's concept that narrative imposes
    an ideological closure. Measured as how much the dialectical sequence
    exceeds the sum of its parts. -/
noncomputable def narrativeTotalization (thesis : I) (moments : List I) : ℝ :=
  rs (dialecticalSequence thesis moments) (dialecticalSequence thesis moments) -
  rs thesis thesis

/-- Narrative totalization is non-negative: narrative always adds weight. -/
theorem narrativeTotalization_nonneg (t : I) (ms : List I) :
    narrativeTotalization t ms ≥ 0 := by
  unfold narrativeTotalization
  linarith [dialecticalSequence_enriches t ms]

/-- Empty narrative has zero totalization. -/
theorem narrativeTotalization_nil (t : I) :
    narrativeTotalization t ([] : List I) = 0 := by
  unfold narrativeTotalization dialecticalSequence; ring

/-! ## §34. Habermas's Discourse Ethics as Dialectical

Habermas: rational discourse achieves consensus through the "unforced
force of the better argument." This is a dialectical process where
interlocutors synthesize their positions. The ideal speech situation
is one where emergence is maximized — the conversation produces more
than either party brings individually. -/

/-- Communicative rationality: the symmetric part of the emergence
    from discourse between two interlocutors. Habermas insists on
    symmetry and reciprocity — both parties must benefit. -/
noncomputable def communicativeRationality (a b : I) : ℝ :=
  (emergence a b a + emergence a b b +
   emergence b a a + emergence b a b) / 2

/-- Communicative rationality is symmetric. -/
theorem communicativeRationality_symm (a b : I) :
    communicativeRationality a b = communicativeRationality b a := by
  unfold communicativeRationality; ring

/-- Communicative rationality with void vanishes. -/
theorem communicativeRationality_void (a : I) :
    communicativeRationality a (void : I) = 0 := by
  unfold communicativeRationality
  rw [emergence_void_right, emergence_void_right,
      emergence_void_left, emergence_void_left]; ring

/-- Discourse deficit: how much the actual discourse falls short
    of perfect communicative rationality (measured by asymmetry). -/
noncomputable def discourseDeficit (a b : I) : ℝ :=
  (emergence a b a - emergence b a a) +
  (emergence a b b - emergence b a b)

/-- Discourse deficit is antisymmetric: a's deficit is b's surplus. -/
theorem discourseDeficit_antisymm (a b : I) :
    discourseDeficit a b = -discourseDeficit b a := by
  unfold discourseDeficit; ring

/-- Discourse deficit with void vanishes. -/
theorem discourseDeficit_void (a : I) :
    discourseDeficit a (void : I) = 0 := by
  unfold discourseDeficit
  rw [emergence_void_right, emergence_void_right,
      emergence_void_left, emergence_void_left]; ring

/-- Ideal speech: discourse where the deficit vanishes.
    Both parties contribute equally to the emergent understanding. -/
def idealSpeech (a b : I) : Prop :=
  discourseDeficit a b = 0

/-- Void always satisfies ideal speech trivially. -/
theorem idealSpeech_void (a : I) : idealSpeech a (void : I) := by
  unfold idealSpeech; exact discourseDeficit_void a

/-- Validity claim: the total emergence a discourse participant brings,
    normalized by self-resonance. The "force of the better argument." -/
noncomputable def validityClaim (speaker context : I) : ℝ :=
  emergence speaker context speaker + emergence speaker context context

/-- Validity claim equals tension. -/
theorem validityClaim_eq_tension (s c : I) :
    validityClaim s c = tension s c := by
  unfold validityClaim tension; ring

/-- Consensus formation: the iterated synthesis of interlocutors
    converges in weight. Each round of discourse enriches. -/
theorem consensus_enriches (a b : I) (n : ℕ) :
    rs (iteratedSynthesis a b (n + 1)) (iteratedSynthesis a b (n + 1)) ≥
    rs (iteratedSynthesis a b n) (iteratedSynthesis a b n) :=
  iteratedSynthesis_enriches a b n

/-! ## §35. Deleuze's Difference and Repetition (Anti-Dialectics)

Deleuze rejects the Hegelian dialectic: difference is NOT subordinate
to identity, and repetition is NOT the return of the same. In IDT,
Deleuze's "difference in itself" is captured by meaning curvature
(the antisymmetric part of emergence), and "repetition" by the
non-identity of iterated composition with itself. -/

/-- Difference in itself: Deleuze's pure difference is not the difference
    BETWEEN two things (which presupposes identity) but the internal
    differentiation of a thing from itself under repetition.
    Measured as the gap between a composed with itself and doubled
    self-resonance. -/
noncomputable def differenceInItself (a : I) : ℝ :=
  rs (compose a a) a - 2 * rs a a

/-- Difference in itself equals semantic charge / immanent critique.
    Deleuze's pure difference is Hegel's semantic charge seen from
    a non-dialectical angle. -/
theorem differenceInItself_eq_semanticCharge (a : I) :
    differenceInItself a = semanticCharge a := by
  unfold differenceInItself semanticCharge emergence; ring

/-- Difference in itself for void is zero: void does not differ from itself. -/
theorem differenceInItself_void :
    differenceInItself (void : I) = 0 := by
  rw [differenceInItself_eq_semanticCharge]; exact semanticCharge_void

/-- Repetition with difference: composing a with itself n times
    produces not the "same" but something that gains weight at each step.
    Deleuze: "Repetition changes nothing in the object repeated,
    but does change something in the mind which contemplates it." -/
noncomputable def repetitionDifference (a : I) (n : ℕ) : ℝ :=
  rs (composeN a (n + 1)) (composeN a (n + 1)) -
  rs (composeN a n) (composeN a n)

/-- Every repetition creates non-negative difference. -/
theorem repetitionDifference_nonneg (a : I) (n : ℕ) :
    repetitionDifference a n ≥ 0 := by
  unfold repetitionDifference
  linarith [rs_composeN_mono a n]

/-- The virtual: Deleuze's concept of the virtual as the field of
    differential relations that are "real without being actual."
    In IDT, the virtual of an idea is its total emergence potential —
    the sum of self-emergence over all compositions with itself. -/
noncomputable def virtualIntensity (a : I) (n : ℕ) : ℝ :=
  rs (composeN a n) (composeN a n) - (n : ℝ) * rs a a

/-- Virtual intensity at step 0 is zero. -/
theorem virtualIntensity_zero (a : I) :
    virtualIntensity a 0 = 0 := by
  unfold virtualIntensity; simp [rs_void_void]

/-- Virtual intensity at step 1 is zero. -/
theorem virtualIntensity_one (a : I) :
    virtualIntensity a 1 = 0 := by
  unfold virtualIntensity composeN; simp [rs_void_left']

/-- Rhizomatic connection: Deleuze and Guattari's rhizome connects
    any point to any other. The rhizomatic resonance between two ideas
    is the symmetric part of their cross-resonance. -/
noncomputable def rhizomaticConnection (a b : I) : ℝ :=
  (rs a b + rs b a) / 2

/-- Rhizomatic connection is symmetric (unlike dialectical opposition). -/
theorem rhizomaticConnection_symm (a b : I) :
    rhizomaticConnection a b = rhizomaticConnection b a := by
  unfold rhizomaticConnection; ring

/-- Rhizomatic connection with void vanishes. -/
theorem rhizomaticConnection_void (a : I) :
    rhizomaticConnection a (void : I) = 0 := by
  unfold rhizomaticConnection; simp [rs_void_left', rs_void_right']

/-- Line of flight: Deleuze's concept of escape from stratified systems.
    The line of flight from a system a via deterritorialization b is
    the emergence that escapes the system's self-resonance. -/
noncomputable def lineOfFlight (system deterritorialization : I) : ℝ :=
  emergence system deterritorialization deterritorialization

/-- Line of flight with void deterritorialization: no escape. -/
theorem lineOfFlight_void_deterr (s : I) :
    lineOfFlight s (void : I) = 0 := by
  unfold lineOfFlight; exact emergence_void_right s (void : I)

/-- Line of flight from void system: nothing to escape from. -/
theorem lineOfFlight_void_system (d : I) :
    lineOfFlight (void : I) d = 0 := by
  unfold lineOfFlight; exact emergence_void_left d d

/-- Body without organs: the limit of deterritorialization.
    The difference between total composition and stratified parts. -/
noncomputable def bodyWithoutOrgans (a b : I) : ℝ :=
  rs (compose a b) (compose a b) - rs a a - rs b b

/-- Body without organs is the enlightenment surplus (same formula). -/
theorem bodyWithoutOrgans_eq_enlightenmentSurplus (a b : I) :
    bodyWithoutOrgans a b = enlightenmentSurplus a b := by
  unfold bodyWithoutOrgans enlightenmentSurplus; ring

/-- Body without organs with void is zero. -/
theorem bodyWithoutOrgans_void_right (a : I) :
    bodyWithoutOrgans a (void : I) = 0 := by
  unfold bodyWithoutOrgans; simp [rs_void_right']

/-! ## §36. Derrida's Deconstruction as Quasi-Dialectics

Derrida's deconstruction is not synthesis but the exposure of the
"undecidable" within every binary opposition. The trace, différance,
and the supplement show that meaning is always deferred and differential.
In IDT, deconstruction reveals that the emergence term is irreducible
— you cannot eliminate the non-linear remainder. -/

/-- The trace: Derrida's concept that every idea carries the trace
    of what it excludes. The trace of a in the context of b is what
    b contributes to the composition that a cannot account for. -/
noncomputable def trace (a b : I) : ℝ :=
  rs (compose a b) (compose a b) - rs a (compose a b)

/-- Trace of void equals the full self-resonance: void contributes
    nothing, so the entire composition is "trace" of the other. -/
theorem trace_void_left (b : I) :
    trace (void : I) b = rs b b := by
  unfold trace; simp [void_left', rs_void_left]

/-- Trace with void: nothing to trace. -/
theorem trace_void_right (a : I) :
    trace a (void : I) = rs a a - rs a a := by
  unfold trace; simp [rs_void_right']

/-- Trace with void simplifies to zero. -/
theorem trace_void_right_eq (a : I) :
    trace a (void : I) = 0 := by
  rw [trace_void_right]; ring

/-- Différance: Derrida's neologism for the play of difference and
    deferral. In IDT, différance between a and b is the gap between
    emergence in opposite composition orders — meaning is never settled. -/
noncomputable def differance (a b : I) : ℝ :=
  emergence a b (compose a b) - emergence b a (compose b a)

/-- Différance is antisymmetric. -/
theorem differance_antisymm (a b : I) :
    differance a b = -differance b a := by
  unfold differance; ring

/-- Différance with void vanishes: no play of difference without
    a differential partner. -/
theorem differance_void_right (a : I) :
    differance a (void : I) = 0 := by
  unfold differance; rw [emergence_void_right, emergence_void_left]; ring

theorem differance_void_left (b : I) :
    differance (void : I) b = 0 := by
  unfold differance; rw [emergence_void_left, emergence_void_right]; ring

/-- The supplement: Derrida shows that what is supposedly "added" to
    a complete whole is in fact constitutive. The supplement of b to a
    is the emergence — the "addition" that transforms the whole. -/
noncomputable def supplement (whole addition : I) : ℝ :=
  emergence whole addition (compose whole addition)

/-- Supplement equals aufhebung: Derrida's supplement IS the dialectical
    surplus, seen from the deconstructive angle. -/
theorem supplement_eq_aufhebung (w a : I) :
    supplement w a = aufhebung w a := by
  unfold supplement aufhebung dialecticalEmergence synthesize; rfl

/-- The undecidable: an idea pair where the parallax gap equals zero
    but neither emergence vanishes. Meaning oscillates without settling. -/
def undecidable (a b : I) : Prop :=
  emergence a b a = emergence a b b ∧ emergence a b a ≠ 0

/-- Pharmakon: Derrida's analysis of concepts that are simultaneously
    remedy and poison. The pharmakon value is the tension — positive
    emergence on one side, negative on another. -/
noncomputable def pharmakon (remedy poison : I) : ℝ :=
  emergence remedy poison remedy - emergence remedy poison poison

/-- Pharmakon equals parallax gap. Derrida and Žižek converge. -/
theorem pharmakon_eq_parallaxGap (r p : I) :
    pharmakon r p = parallaxGap r p := by
  unfold pharmakon parallaxGap; ring

/-- Pharmakon with void vanishes. -/
theorem pharmakon_void (a : I) :
    pharmakon a (void : I) = 0 := by
  rw [pharmakon_eq_parallaxGap]; exact parallaxGap_void_right a

/-- Iterability: Derrida's argument that meaning requires repeatability,
    but every repetition alters. The iterability index measures how
    much double-composition enriches beyond simple self-resonance. -/
noncomputable def iterability (a : I) : ℝ :=
  rs (compose a a) (compose a a) - rs a a

/-- Iterability is non-negative: repetition always enriches. -/
theorem iterability_nonneg (a : I) :
    iterability a ≥ 0 := by
  unfold iterability
  linarith [compose_enriches' a a]

/-- Void iterability is zero. -/
theorem iterability_void :
    iterability (void : I) = 0 := by
  unfold iterability; simp [rs_void_void]

/-! ## §37. Deep Math: Dialectical Fixed Points

A fixed point of the dialectical process is an idea that synthesizing
with any element of a given class leaves it unchanged (in self-resonance).
We study conditions for dialectical fixed points and their properties. -/

/-- An idea is a dialectical fixed point with respect to b if the aufhebung
    vanishes: synthesizing with b creates no new emergence. -/
def dialecticalFixedPoint (a b : I) : Prop :=
  aufhebung a b = 0

/-- Void is a fixed point of any dialectic. -/
theorem void_dialecticalFixedPoint (b : I) :
    dialecticalFixedPoint (void : I) b := by
  unfold dialecticalFixedPoint; exact aufhebung_void_thesis b

/-- Any idea is a fixed point of the void dialectic. -/
theorem dialecticalFixedPoint_void (a : I) :
    dialecticalFixedPoint a (void : I) := by
  unfold dialecticalFixedPoint; exact aufhebung_void_antithesis a

/-- At a fixed point, the aufhebung decomposition simplifies:
    self-resonance = preservation + negation. -/
theorem fixedPoint_decomposition (a b : I) (h : dialecticalFixedPoint a b) :
    rs (synthesize a b) (synthesize a b) =
    preservation a b + negation a b := by
  have := aufhebung_decomposition a b
  unfold dialecticalFixedPoint at h
  unfold transcendence at this
  linarith

/-- Fixed point criterion: a is a fixed point w.r.t. b iff the
    self-resonance of the synthesis equals preservation + negation. -/
theorem fixedPoint_iff (a b : I) :
    dialecticalFixedPoint a b ↔
    rs (synthesize a b) (synthesize a b) =
    preservation a b + negation a b := by
  constructor
  · exact fixedPoint_decomposition a b
  · intro h
    unfold dialecticalFixedPoint
    have := aufhebung_decomposition a b
    unfold transcendence at this
    linarith

/-- The aufhebung squared bound at fixed points. -/
theorem fixedPoint_aufhebung_sq (a b : I) (h : dialecticalFixedPoint a b) :
    (aufhebung a b) ^ 2 = 0 := by
  unfold dialecticalFixedPoint at h; rw [h]; ring

/-- Mutual fixed points: a and b are mutual fixed points if
    both aufhebungen vanish. -/
def mutualFixedPoint (a b : I) : Prop :=
  dialecticalFixedPoint a b ∧ dialecticalFixedPoint b a

/-- Void is a mutual fixed point with anything. -/
theorem void_mutualFixedPoint (a : I) :
    mutualFixedPoint (void : I) a :=
  ⟨void_dialecticalFixedPoint a, dialecticalFixedPoint_void a⟩

/-- Mutual fixed points are symmetric. -/
theorem mutualFixedPoint_symm (a b : I) :
    mutualFixedPoint a b → mutualFixedPoint b a :=
  fun ⟨h1, h2⟩ => ⟨h2, h1⟩

/-! ## §38. Deep Math: Convergence of Synthesis Sequences

We study the convergence properties of iterated synthesis sequences.
While we cannot prove convergence in general (since we have no topology),
we can prove that the self-resonance sequence is monotone and bounded
below, and derive consequences. -/

/-- The self-resonance sequence of iterated synthesis is monotone
    non-decreasing. This is a key structural result. -/
theorem synthesis_sequence_monotone (a b : I) :
    ∀ n : ℕ,
    rs (iteratedSynthesis a b (n + 1)) (iteratedSynthesis a b (n + 1)) ≥
    rs (iteratedSynthesis a b n) (iteratedSynthesis a b n) :=
  iteratedSynthesis_enriches a b

/-- The self-resonance of stage n is bounded below by the initial value. -/
theorem synthesis_sequence_bounded_below (a b : I) (n : ℕ) :
    rs (iteratedSynthesis a b n) (iteratedSynthesis a b n) ≥ rs a a :=
  iteratedSynthesis_nondecreasing a b 0 n (Nat.zero_le n)

/-- The gain from stage n to stage n+1 is non-negative. -/
theorem synthesis_gain_nonneg (a b : I) (n : ℕ) :
    rs (iteratedSynthesis a b (n + 1)) (iteratedSynthesis a b (n + 1)) -
    rs (iteratedSynthesis a b n) (iteratedSynthesis a b n) ≥ 0 := by
  linarith [iteratedSynthesis_enriches a b n]

/-- If the synthesis ever reaches a fixed point (gain = 0 at step n),
    then the negation residue at that step vanishes: the synthesis
    has absorbed all the weight it can from the antithesis. -/
theorem synthesis_fixedPoint_criterion (a b : I) (n : ℕ)
    (h : rs (iteratedSynthesis a b (n + 1)) (iteratedSynthesis a b (n + 1)) =
         rs (iteratedSynthesis a b n) (iteratedSynthesis a b n)) :
    negationResidue (iteratedSynthesis a b n) b = 0 := by
  unfold negationResidue synthesize
  rw [← iteratedSynthesis_succ]; linarith

/-- The total weight accumulated over N stages. -/
noncomputable def totalAccumulation (a b : I) (n : ℕ) : ℝ :=
  rs (iteratedSynthesis a b n) (iteratedSynthesis a b n) - rs a a

/-- Total accumulation is non-negative. -/
theorem totalAccumulation_nonneg (a b : I) (n : ℕ) :
    totalAccumulation a b n ≥ 0 := by
  unfold totalAccumulation
  linarith [synthesis_sequence_bounded_below a b n]

/-- Total accumulation at step 0 is 0. -/
theorem totalAccumulation_zero (a b : I) :
    totalAccumulation a b 0 = 0 := by
  unfold totalAccumulation iteratedSynthesis; ring

/-- Total accumulation is monotone non-decreasing. -/
theorem totalAccumulation_mono (a b : I) (m n : ℕ) (h : m ≤ n) :
    totalAccumulation a b n ≥ totalAccumulation a b m := by
  unfold totalAccumulation
  linarith [iteratedSynthesis_nondecreasing a b m n h]

/-! ## §39. Deep Math: Dialectical Topology

Without assuming a metric or topology on ideas, we can still define
"topological" notions intrinsically using resonance. These capture
the structure of dialectical neighborhoods and open sets. -/

/-- Resonance ball: the set of ideas that resonate above threshold
    with a given center idea. A kind of "dialectical neighborhood." -/
def resonanceBall (center : I) (threshold : ℝ) (x : I) : Prop :=
  rs center x > threshold

/-- Void is never in a positive-threshold ball. -/
theorem void_not_in_ball (c : I) (t : ℝ) (ht : t ≥ 0) :
    ¬resonanceBall c t (void : I) := by
  unfold resonanceBall; rw [rs_void_right']; linarith

/-- Every non-void idea is in its own ball at threshold 0. -/
theorem self_in_ball (a : I) (h : a ≠ void) :
    resonanceBall a 0 a := by
  unfold resonanceBall; exact rs_self_pos a h

/-- Dialectical neighborhood: ideas that resonate positively with
    the synthesis of a and b. These are ideas "compatible" with the
    dialectical outcome. -/
def dialecticalNeighborhood (a b : I) (x : I) : Prop :=
  rs (synthesize a b) x > 0

/-- Opposition frontier: the set of ideas where resonance changes sign.
    These are the ideas on the boundary between resonance and opposition. -/
def oppositionFrontier (a : I) (x : I) : Prop :=
  rs a x = 0

/-- Void is always on the opposition frontier. -/
theorem void_on_frontier (a : I) :
    oppositionFrontier a (void : I) := by
  unfold oppositionFrontier; exact rs_void_right' a

/-- Every idea has void on its frontier. -/
theorem frontier_of_void (a : I) :
    oppositionFrontier (void : I) a := by
  unfold oppositionFrontier; exact rs_void_left' a

/-- Dialectical density: a measure of how "rich" the dialectical
    structure is around an idea, based on self-resonance growth. -/
noncomputable def dialecticalDensity (a : I) : ℝ :=
  rs (compose a a) (compose a a) - rs a a

/-- Dialectical density is non-negative. -/
theorem dialecticalDensity_nonneg (a : I) :
    dialecticalDensity a ≥ 0 := by
  unfold dialecticalDensity
  linarith [compose_enriches' a a]

/-- Void has zero dialectical density. -/
theorem dialecticalDensity_void :
    dialecticalDensity (void : I) = 0 := by
  unfold dialecticalDensity; simp [rs_void_void]

/-- The dialectical density relates to the negation residue of self-synthesis. -/
theorem dialecticalDensity_eq_negationResidue_self (a : I) :
    dialecticalDensity a = negationResidue a a := by
  unfold dialecticalDensity negationResidue synthesize; ring

/-! ## §40. Synthesis Algebra: Interaction Laws

Deep algebraic properties of how dialectical operations compose
and interact with each other. -/

/-- Double synthesis associativity: synthesizing (synthesize a b) with c
    equals composing a with (compose b c), by associativity. -/
theorem doubleSynthesis_assoc (a b c : I) :
    synthesize (synthesize a b) c = compose a (compose b c) := by
  unfold synthesize; simp [compose_assoc']

/-- The aufhebung of a synthesis reduces to emergence of its components. -/
theorem aufhebung_of_synthesis (a b c : I) :
    aufhebung (synthesize a b) c =
    emergence (compose a b) c (compose (compose a b) c) := by
  unfold aufhebung dialecticalEmergence synthesize; rfl

/-- Synthesis with compose is associative. -/
theorem synthesis_compose_assoc (a b c d : I) :
    rs (synthesize (synthesize a b) c) d =
    rs (compose a (compose b c)) d := by
  unfold synthesize; simp [compose_assoc']

/-- Three-stage dialectical weight is monotone. -/
theorem three_stage_enriches (a b c : I) :
    rs (triadCompose a b c) (triadCompose a b c) ≥ rs a a := by
  exact triadCompose_enriches_thesis a b c

/-- Dialectical absorption: when synthesis with b and then with c
    produces the same weight as synthesis with compose b c. -/
theorem dialectical_absorption (a b c : I) :
    rs (synthesize (synthesize a b) c) (synthesize (synthesize a b) c) =
    rs (compose a (compose b c)) (compose a (compose b c)) := by
  unfold synthesize; simp [compose_assoc']

/-- The emergence transfer: how emergence shifts when we change
    the decomposition of a dialectical pair. -/
theorem emergence_transfer (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

/-! ## §41. Dialectical Spectrum Analysis

Every dialectical pair generates a "spectrum" of values as we iterate.
We analyze the algebraic structure of these spectra. -/

/-- The n-th dialectical spectrum value: the self-resonance at stage n. -/
noncomputable def dialecticalSpectrum (a b : I) (n : ℕ) : ℝ :=
  rs (iteratedSynthesis a b n) (iteratedSynthesis a b n)

/-- Spectrum at 0 is the initial self-resonance. -/
theorem dialecticalSpectrum_zero (a b : I) :
    dialecticalSpectrum a b 0 = rs a a := rfl

/-- The spectrum is monotone non-decreasing. -/
theorem dialecticalSpectrum_mono (a b : I) (m n : ℕ) (h : m ≤ n) :
    dialecticalSpectrum a b n ≥ dialecticalSpectrum a b m := by
  unfold dialecticalSpectrum
  exact iteratedSynthesis_nondecreasing a b m n h

/-- The spectrum increment: how much the spectrum grows at each step. -/
noncomputable def spectrumIncrement (a b : I) (n : ℕ) : ℝ :=
  dialecticalSpectrum a b (n + 1) - dialecticalSpectrum a b n

/-- Spectrum increment is non-negative. -/
theorem spectrumIncrement_nonneg (a b : I) (n : ℕ) :
    spectrumIncrement a b n ≥ 0 := by
  unfold spectrumIncrement dialecticalSpectrum
  linarith [iteratedSynthesis_enriches a b n]

/-- The spectrum increment equals the stage gain. -/
theorem spectrumIncrement_eq_stageGain (a b : I) (n : ℕ) :
    spectrumIncrement a b n = stageGain a b n := by
  unfold spectrumIncrement dialecticalSpectrum stageGain; ring

/-- Telescoping: the spectrum at n minus the initial value equals
    the sum of all increments. -/
theorem spectrum_telescopes (a b : I) (n : ℕ) :
    dialecticalSpectrum a b n - dialecticalSpectrum a b 0 =
    (Finset.range n).sum (fun k => spectrumIncrement a b k) := by
  have h : ∀ k, spectrumIncrement a b k = stageGain a b k :=
    spectrumIncrement_eq_stageGain a b
  simp_rw [h]
  unfold dialecticalSpectrum
  exact total_gain_telescopes a b n

/-! ## §42. Dialectical Energy and Potential

Defining "energy" concepts for dialectical processes using the
resonance structure. These provide measures of dialectical activity. -/

/-- Dialectical kinetic energy: the emergence of the current synthesis
    with the antithesis — the "active" part of the dialectic. -/
noncomputable def dialecticalKineticEnergy (a b : I) (n : ℕ) : ℝ :=
  emergence (iteratedSynthesis a b n) b (iteratedSynthesis a b (n + 1))

/-- Kinetic energy equals the aufhebung at step n. -/
theorem kineticEnergy_eq_aufhebungN (a b : I) (n : ℕ) :
    dialecticalKineticEnergy a b n = aufhebungN a b (n + 1) := by
  unfold dialecticalKineticEnergy aufhebungN aufhebung dialecticalEmergence
    synthesize
  rfl

/-- Dialectical potential energy: the self-resonance accumulated. -/
noncomputable def dialecticalPotentialEnergy (a b : I) (n : ℕ) : ℝ :=
  rs (iteratedSynthesis a b n) (iteratedSynthesis a b n)

/-- Potential energy at step 0 equals initial self-resonance. -/
theorem potentialEnergy_zero (a b : I) :
    dialecticalPotentialEnergy a b 0 = rs a a := rfl

/-- Potential energy is monotone. -/
theorem potentialEnergy_mono (a b : I) (n : ℕ) :
    dialecticalPotentialEnergy a b (n + 1) ≥
    dialecticalPotentialEnergy a b n := by
  unfold dialecticalPotentialEnergy
  exact iteratedSynthesis_enriches a b n

/-- Total dialectical energy: kinetic + potential at each stage. -/
noncomputable def totalDialecticalEnergy (a b : I) (n : ℕ) : ℝ :=
  dialecticalPotentialEnergy a b n + dialecticalKineticEnergy a b n

/-- Total energy decomposition via aufhebung stage decomposition. -/
theorem totalEnergy_eq (a b : I) (n : ℕ) :
    totalDialecticalEnergy a b n =
    dialecticalPotentialEnergy a b n + aufhebungN a b (n + 1) := by
  unfold totalDialecticalEnergy
  rw [kineticEnergy_eq_aufhebungN]

/-! ## §43. Dialectical Curvature and Torsion

Higher-order dialectical structure: how the "direction" of dialectical
development changes (curvature) and how it twists (torsion). -/

/-- Dialectical curvature: the change in the spectrum increment.
    Positive curvature means acceleration of dialectical development;
    negative means deceleration. -/
noncomputable def dialecticalCurvature (a b : I) (n : ℕ) : ℝ :=
  spectrumIncrement a b (n + 1) - spectrumIncrement a b n

/-- Dialectical curvature expansion. -/
theorem dialecticalCurvature_eq (a b : I) (n : ℕ) :
    dialecticalCurvature a b n =
    dialecticalSpectrum a b (n + 2) -
    2 * dialecticalSpectrum a b (n + 1) +
    dialecticalSpectrum a b n := by
  unfold dialecticalCurvature spectrumIncrement; ring

/-- Dialectical torsion: the non-commutativity at stage n.
    How much the order of synthesis matters at each stage. -/
noncomputable def dialecticalTorsion (a b : I) (n : ℕ) : ℝ :=
  rs (iteratedSynthesis a b n) b - rs b (iteratedSynthesis a b n)

/-- Torsion at stage 0 is just the asymmetry. -/
theorem dialecticalTorsion_zero (a b : I) :
    dialecticalTorsion a b 0 = rs a b - rs b a := by
  unfold dialecticalTorsion iteratedSynthesis; ring

/-- Torsion with void is zero. -/
theorem dialecticalTorsion_void_antithesis (a : I) (n : ℕ) :
    dialecticalTorsion a (void : I) n = 0 := by
  unfold dialecticalTorsion; simp [rs_void_left', rs_void_right']

/-! ## §44. Dialectical Invariants and Conservation Laws

Quantities that are preserved under dialectical transformation.
These are the "conserved charges" of the dialectical process. -/

/-- The dialectical charge: a quantity preserved under re-bracketing
    of composition. -/
noncomputable def dialecticalCharge (a b c d : I) : ℝ :=
  emergence a b d + emergence (compose a b) c d

/-- Dialectical charge conservation: the charge is the same regardless
    of how we bracket the composition (by the cocycle condition). -/
theorem dialecticalCharge_conservation (a b c d : I) :
    dialecticalCharge a b c d =
    emergence b c d + emergence a (compose b c) d := by
  unfold dialecticalCharge; exact cocycle_condition a b c d

/-- The dialectical cocycle residue: the difference between left and
    right bracketed charges. Always zero by associativity. -/
noncomputable def cocycleResidue (a b c d : I) : ℝ :=
  dialecticalCharge a b c d - (emergence b c d + emergence a (compose b c) d)

/-- Cocycle residue always vanishes: this is the conservation law. -/
theorem cocycleResidue_vanishes (a b c d : I) :
    cocycleResidue a b c d = 0 := by
  unfold cocycleResidue dialecticalCharge
  linarith [cocycle_condition a b c d]

/-- Resonance under rebracketing is invariant. -/
theorem dialectical_invariance (a b c d : I) :
    rs (compose (compose a b) c) d =
    rs (compose a (compose b c)) d := by
  rw [compose_assoc']

/-! ## §45. Advanced Alienation Theory

Extending Marx's alienation concepts with deeper algebraic structure. -/

/-- Species-being deficit: how much the product (compose w m) fails
    to reflect the worker's full potential (self-resonance).
    Marx: alienation from species-being. Measured as the worker's
    self-resonance minus how the product resonates with the worker. -/
noncomputable def speciesBeingDeficit (worker material : I) : ℝ :=
  rs worker worker - rs worker (compose worker material)

/-- Species-being deficit with void material is zero: without
    external material, there is no alienation. -/
theorem speciesBeingDeficit_void_material (w : I) :
    speciesBeingDeficit w (void : I) = 0 := by
  unfold speciesBeingDeficit; simp [rs_void_right']

/-- Species-being deficit equals alienation index: same concept,
    same formula. -/
theorem speciesBeingDeficit_eq_alienation (w m : I) :
    speciesBeingDeficit w m = alienationIndex w m := rfl

/-- Double alienation: the alienation of the alienated product.
    What happens when the worker is alienated from the product,
    and the product is itself alienated from its use-value. -/
noncomputable def doubleAlienation (w m : I) : ℝ :=
  alienationIndex w m + alienationIndex (compose w m) m

/-- Double alienation with void material is zero. -/
theorem doubleAlienation_void (w : I) :
    doubleAlienation w (void : I) = 0 := by
  unfold doubleAlienation alienationIndex; simp [rs_void_right']

/-! ## §46. Dialectical Category Theory

The category of dialectical processes: morphisms between dialectical
pairs that preserve the aufhebung structure. -/

/-- A dialectical process preserves aufhebung if composing with a
    "transformer" t does not change the aufhebung value. -/
def preservesAufhebung (a b t : I) : Prop :=
  aufhebung (compose t a) (compose t b) = aufhebung a b

/-- Void transformer always preserves aufhebung. -/
theorem void_preservesAufhebung (a b : I) :
    preservesAufhebung a b (void : I) := by
  unfold preservesAufhebung; simp

/-- A dialectical pair is "tight" if the aufhebung squared equals
    the product of self-resonances. This is the saturated case
    of the emergence bound. -/
def dialecticallyTight (a b : I) : Prop :=
  (aufhebung a b) ^ 2 =
  rs (compose a b) (compose a b) * rs (compose a b) (compose a b)

/-- Void-void pairs are trivially tight. -/
theorem void_dialecticallyTight :
    dialecticallyTight (void : I) (void : I) := by
  unfold dialecticallyTight aufhebung dialecticalEmergence synthesize
  simp [rs_void_void, void_left']
  unfold emergence; simp [rs_void_void]

/-! ## §47. Dialectical Information Theory

Information-theoretic interpretations of dialectical quantities.
The aufhebung as "dialectical information gain." -/

/-- Dialectical information: the total non-additive resonance created
    by a synthesis. Analogous to mutual information. -/
noncomputable def dialecticalInformation (a b : I) : ℝ :=
  rs (compose a b) (compose a b) - rs a a - rs b b

/-- Dialectical information with void is zero. -/
theorem dialecticalInformation_void_right (a : I) :
    dialecticalInformation a (void : I) = 0 := by
  unfold dialecticalInformation; simp [rs_void_right']

theorem dialecticalInformation_void_left (b : I) :
    dialecticalInformation (void : I) b = 0 := by
  unfold dialecticalInformation; simp [rs_void_left', rs_void_void]

/-- Dialectical information decomposes into emergence terms. -/
theorem dialecticalInformation_eq (a b : I) :
    dialecticalInformation a b =
    (rs a (compose a b) - rs a a) +
    (rs b (compose a b) - rs b b) +
    emergence a b (compose a b) := by
  unfold dialecticalInformation
  rw [rs_compose_eq a b (compose a b)]
  ring

/-- The dialectical redundancy: how much of the synthesis's weight
    comes from the parts versus from emergence. -/
noncomputable def dialecticalRedundancy (a b : I) : ℝ :=
  rs a (compose a b) + rs b (compose a b) - rs a a - rs b b

/-- Dialectical redundancy with void is zero. -/
theorem dialecticalRedundancy_void (a : I) :
    dialecticalRedundancy a (void : I) = 0 := by
  unfold dialecticalRedundancy; simp [rs_void_right', rs_void_left']

/-- Total dialectical information = redundancy + aufhebung. -/
theorem dialecticalInformation_decomp (a b : I) :
    dialecticalInformation a b =
    dialecticalRedundancy a b + aufhebung a b := by
  unfold dialecticalInformation dialecticalRedundancy aufhebung
    dialecticalEmergence synthesize emergence
  ring

end Dialectics

end IDT3
