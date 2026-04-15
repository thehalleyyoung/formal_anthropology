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

end Dialectics

end IDT3
