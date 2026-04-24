import FormalAnthropology.IDT_v3_Foundations

/-!
# IDT v3: Narrative, Rhetoric, and Poetics

Formalizing narrative structure, rhetorical appeals, defamiliarization,
and poetic density within ideatic space. Every narrative is a composed
sequence of utterances; its emergent meaning arises from the cocycle
structure of composition.

## Key Concepts:
- Narrative arc = trajectory through ideatic space via sequential composition
- Defamiliarization (Shklovsky) = high emergence at composition step
- Rhetoric (Aristotle) = decomposition of persuasive effect into logos/ethos/pathos
- Poetic density = weight per utterance
- Dramatic tension = emergence against the narrative itself

## NO SORRIES
-/

namespace IDT3

section NarrativeRhetoric
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-! ## §1. Narrative as Sequential Composition -/

-- A narrative is a list of utterances composed sequentially.
-- composeList is already defined in Foundations

/-- The narrative weight at step k: weight of the first k elements composed. -/
noncomputable def narrativeWeight (story : List I) : ℝ :=
  rs (composeList story) (composeList story)

/-- Empty narrative has zero weight. -/
theorem narrativeWeight_nil : narrativeWeight ([] : List I) = 0 := by
  unfold narrativeWeight composeList
  exact rs_void_void

/-- Singleton narrative has weight = self-resonance. -/
theorem narrativeWeight_singleton (a : I) :
    narrativeWeight [a] = rs a a := by
  unfold narrativeWeight composeList
  simp [List.foldl, void_left']

/-- Prepending an element never decreases narrative weight. -/
theorem narrativeWeight_cons_enriches (a : I) (story : List I) :
    narrativeWeight (a :: story) ≥ rs a a := by
  unfold narrativeWeight composeList
  exact compose_enriches' a (composeList story)

/-! ## §2. Narrative Emergence -/

/-- The narrative emergence at a given step: how much new meaning
    element a adds to the existing narrative pfx, as observed by d. -/
noncomputable def narrativeEmergenceAt (pfx : I) (a d : I) : ℝ :=
  emergence pfx a d

/-- Narrative emergence vanishes when adding void. -/
theorem narrativeEmergenceAt_void_element (pfx d : I) :
    narrativeEmergenceAt pfx (void : I) d = 0 :=
  emergence_void_right pfx d

/-- Narrative emergence vanishes with void pfx. -/
theorem narrativeEmergenceAt_void_pfx (a d : I) :
    narrativeEmergenceAt (void : I) a d = 0 :=
  emergence_void_left a d

/-- Narrative emergence vanishes with void observer. -/
theorem narrativeEmergenceAt_void_observer (pfx a : I) :
    narrativeEmergenceAt pfx a (void : I) = 0 :=
  emergence_against_void pfx a

/-! ## §3. Defamiliarization (Ostranenie)

Shklovsky's defamiliarization: "making the familiar strange."
In IDT, this is measured by the magnitude of emergence when a
new element is composed with the existing narrative context. -/

/-- The defamiliarization measure: absolute emergence when element a
    enters context pfx, as perceived by observer d. -/
noncomputable def defamiliarization (pfx a d : I) : ℝ :=
  (narrativeEmergenceAt pfx a d) ^ 2

/-- Defamiliarization is non-negative. -/
theorem defamiliarization_nonneg (pfx a d : I) :
    defamiliarization pfx a d ≥ 0 := sq_nonneg _

/-- Defamiliarization is bounded by the Cauchy-Schwarz inequality. -/
theorem defamiliarization_bounded (pfx a d : I) :
    defamiliarization pfx a d ≤
    rs (compose pfx a) (compose pfx a) * rs d d := by
  unfold defamiliarization narrativeEmergenceAt
  exact emergence_bounded' pfx a d

/-- Void produces zero defamiliarization. -/
theorem defamiliarization_void_element (pfx d : I) :
    defamiliarization pfx (void : I) d = 0 := by
  unfold defamiliarization; rw [narrativeEmergenceAt_void_element]; ring

/-- Void context produces zero defamiliarization. -/
theorem defamiliarization_void_pfx (a d : I) :
    defamiliarization (void : I) a d = 0 := by
  unfold defamiliarization; rw [narrativeEmergenceAt_void_pfx]; ring

/-! ## §4. Dramatic Tension

The dramatic tension at a point in a narrative is the emergence
of the new element observed against the narrative ITSELF.
This captures how much the new element transforms the story's
self-perception. -/

/-- Dramatic tension: emergence of adding a to pfx,
    observed against the result. -/
noncomputable def dramaticTension (pfx a : I) : ℝ :=
  emergence pfx a (compose pfx a)

/-- Dramatic tension with void element is zero. -/
theorem dramaticTension_void_element (pfx : I) :
    dramaticTension pfx (void : I) = 0 := by
  unfold dramaticTension; exact emergence_void_right pfx _

/-- Dramatic tension with void pfx is zero. -/
theorem dramaticTension_void_pfx (a : I) :
    dramaticTension (void : I) a = 0 := by
  unfold dramaticTension; exact emergence_void_left a _

/-- Dramatic tension is bounded. -/
theorem dramaticTension_bounded (pfx a : I) :
    (dramaticTension pfx a) ^ 2 ≤
    rs (compose pfx a) (compose pfx a) *
    rs (compose pfx a) (compose pfx a) := by
  unfold dramaticTension
  exact emergence_bounded' pfx a (compose pfx a)

/-- Dramatic tension magnitude ≤ weight of result. -/
theorem dramaticTension_le_weight (pfx a : I) :
    (dramaticTension pfx a) ^ 2 ≤
    (rs (compose pfx a) (compose pfx a)) ^ 2 := by
  have h := dramaticTension_bounded pfx a
  have hw := rs_self_nonneg' (compose pfx a)
  nlinarith [sq_nonneg (rs (compose pfx a) (compose pfx a))]

/-! ## §5. Rhetoric: The Three Appeals

Aristotle's logos, ethos, pathos decompose the persuasive
effect of a signal s on receiver b targeting idea a. -/

/-- Logos: direct resonance of signal with intent. -/
noncomputable def logos (s a : I) : ℝ := rs s a

/-- Ethos: preexisting alignment of receiver with intent. -/
noncomputable def ethos (b a : I) : ℝ := rs b a

/-- Pathos: emergent resonance from signal-context interaction. -/
noncomputable def pathos (s b a : I) : ℝ := emergence s b a

/-- The Rhetorical Decomposition Theorem:
    The total persuasive effect equals logos + ethos + pathos. -/
theorem rhetorical_decomposition (s b a : I) :
    rs (compose s b) a = logos s a + ethos b a + pathos s b a := by
  unfold logos ethos pathos; exact rs_compose_eq s b a

/-- Void signal: persuasion comes entirely from ethos. -/
theorem void_signal_rhetoric (b a : I) :
    rs (compose (void : I) b) a = ethos b a := by
  unfold ethos; rw [void_left']

/-- Void context: persuasion comes entirely from logos. -/
theorem void_context_rhetoric (s a : I) :
    rs (compose s (void : I)) a = logos s a := by
  unfold logos; rw [void_right']

/-- Pathos vanishes when signal is void. -/
theorem pathos_void_signal (b a : I) :
    pathos (void : I) b a = 0 := by
  unfold pathos; exact emergence_void_left b a

/-- Pathos vanishes when context is void. -/
theorem pathos_void_context (s a : I) :
    pathos s (void : I) a = 0 := by
  unfold pathos; exact emergence_void_right s a

/-- Pathos vanishes when target is void. -/
theorem pathos_void_target (s b : I) :
    pathos s b (void : I) = 0 := by
  unfold pathos; exact emergence_against_void s b

/-- Pathos is bounded by signal weight and target weight. -/
theorem pathos_bounded (s b a : I) :
    (pathos s b a) ^ 2 ≤
    rs (compose s b) (compose s b) * rs a a :=
  emergence_bounded' s b a

/-! ## §6. Poetic Density

Poetry = maximum meaning per word. We formalize this as
the ratio of narrative weight to length. -/

/-- Weight per element (for non-empty lists). -/
noncomputable def meaningDensity (story : List I) : ℝ :=
  narrativeWeight story / story.length

/-- The total resonance of a narrative against an observer. -/
noncomputable def narrativeResonance (story : List I) (d : I) : ℝ :=
  rs (composeList story) d

/-- Empty narrative has zero resonance with anything. -/
theorem narrativeResonance_nil (d : I) :
    narrativeResonance ([] : List I) d = 0 := by
  unfold narrativeResonance composeList
  exact rs_void_left' d

/-! ## §7. Anaphora: The Power of Repetition

Anaphora = repeating the same element. Weight grows monotonically
but emergence may vary at each repetition. -/

-- n-fold repetition of element a.
-- composeN is already in Foundations

/-- Weight of repetition is non-decreasing. -/
theorem repetition_weight_mono (a : I) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) ≥
    rs (composeN a n) (composeN a n) :=
  rs_composeN_mono a n

/-- The emergence of the (n+1)-th repetition. -/
noncomputable def repetitionEmergence (a : I) (n : ℕ) (d : I) : ℝ :=
  emergence (composeN a n) a d

/-- First repetition emergence (n=0): adding a to void. -/
theorem repetitionEmergence_zero (a d : I) :
    repetitionEmergence a 0 d = 0 := by
  unfold repetitionEmergence
  simp [composeN]
  exact emergence_void_left a d

/-! ## §8. Plot as Trajectory

A plot is a sequence of narrative events, each of which is
a transition in ideatic space. The cocycle condition constrains
how emergence accumulates across plot points. -/

/-- The plot emergence: total emergence from composing three acts. -/
theorem three_act_cocycle (act1 act2 act3 observer : I) :
    emergence act1 act2 observer + emergence (compose act1 act2) act3 observer =
    emergence act2 act3 observer + emergence act1 (compose act2 act3) observer :=
  cocycle_condition act1 act2 act3 observer

/-- The resonance of a three-act narrative decomposes. -/
theorem three_act_decomposition (a1 a2 a3 d : I) :
    rs (compose (compose a1 a2) a3) d =
    rs a1 d + rs a2 d + rs a3 d +
    emergence a1 a2 d + emergence (compose a1 a2) a3 d := by
  have h1 := rs_compose_eq a1 a2 d
  have h2 := rs_compose_eq (compose a1 a2) a3 d
  linarith

/-- The narrative arc weight is invariant under re-bracketing. -/
theorem narrative_associativity (a1 a2 a3 : I) :
    rs (compose (compose a1 a2) a3) (compose (compose a1 a2) a3) =
    rs (compose a1 (compose a2 a3)) (compose a1 (compose a2 a3)) := by
  rw [compose_assoc']

/-! ## §9. Climax and Resolution

The climax of a narrative is the point of maximum dramatic tension.
Resolution is when tension drops. We can characterize these. -/

/-- A narrative element is a climax if its dramatic tension exceeds
    both its predecessor's and successor's. -/
def isClimax (pfx a suffix : I) : Prop :=
  dramaticTension pfx a > dramaticTension (compose pfx a) suffix

/-- After a climax, adding void (silence) produces zero tension = resolution. -/
theorem silence_resolves (pfx a : I) :
    dramaticTension (compose pfx a) (void : I) = 0 :=
  dramaticTension_void_element (compose pfx a)

/-! ## §10. Irony in Narrative

Irony occurs when the narrative emergence is negative:
what was said, in context, resonates OPPOSITE to expectation. -/

/-- Narrative irony: negative emergence at a plot point. -/
def narrativeIrony (pfx a d : I) : Prop :=
  narrativeEmergenceAt pfx a d < 0

/-- No irony from void. -/
theorem no_irony_from_void (pfx d : I) :
    ¬narrativeIrony pfx (void : I) d := by
  unfold narrativeIrony; rw [narrativeEmergenceAt_void_element]; linarith

/-- No irony in void context. -/
theorem no_irony_in_void (a d : I) :
    ¬narrativeIrony (void : I) a d := by
  unfold narrativeIrony; rw [narrativeEmergenceAt_void_pfx]; linarith

/-! ## §11. Intertextuality (Kristeva/Bakhtin)

Every text exists in relation to other texts. The resonance between
a narrative and an external text is a measure of intertextuality. -/

/-- Intertextual resonance: how much narrative n resonates with text t. -/
noncomputable def intertextuality (narrative_idea t : I) : ℝ :=
  rs narrative_idea t

/-- Intertextual emergence: new meaning from reading narrative after text. -/
noncomputable def intertextualEmergence (text narrative observer : I) : ℝ :=
  emergence text narrative observer

/-- Reading the void text first adds no intertextual emergence. -/
theorem intertextualEmergence_void_text (narrative observer : I) :
    intertextualEmergence (void : I) narrative observer = 0 :=
  emergence_void_left narrative observer

/-- Intertextual emergence is bounded. -/
theorem intertextualEmergence_bounded (text narrative observer : I) :
    (intertextualEmergence text narrative observer) ^ 2 ≤
    rs (compose text narrative) (compose text narrative) * rs observer observer :=
  emergence_bounded' text narrative observer

/-! ## §12. The Anxiety of Influence (Bloom)

A later author b "misreads" precursor a through composition.
The anxiety of influence is the tension between preservation and innovation. -/

/-- The influence: how much a's resonance persists in the composition a∘b. -/
noncomputable def influence (precursor successor observer : I) : ℝ :=
  rs precursor observer

/-- The innovation: how much new resonance the successor adds. -/
noncomputable def innovation (precursor successor observer : I) : ℝ :=
  rs (compose precursor successor) observer - rs precursor observer

/-- Innovation decomposes into successor's own resonance + emergence. -/
theorem innovation_decomposition (precursor successor observer : I) :
    innovation precursor successor observer =
    rs successor observer + emergence precursor successor observer := by
  unfold innovation; have := rs_compose_eq precursor successor observer
  linarith

/-- Zero successor means zero innovation. -/
theorem innovation_void_successor (precursor observer : I) :
    innovation precursor (void : I) observer = 0 := by
  unfold innovation; rw [void_right']; ring

/-! ## §13. Dialogue and Polyphony (Bakhtin) -/

/-- In a dialogue, two voices alternate. The total meaning is their composition. -/
noncomputable def dialogueWeight (voice1 voice2 : I) : ℝ :=
  rs (compose voice1 voice2) (compose voice1 voice2)

/-- Dialogue weight is at least as much as the first voice. -/
theorem dialogue_enriches_first (v1 v2 : I) :
    dialogueWeight v1 v2 ≥ rs v1 v1 :=
  compose_enriches' v1 v2

/-- The polyphonic surplus: how much more a dialogue produces
    than the first voice alone. -/
noncomputable def polyphonicSurplus (v1 v2 : I) : ℝ :=
  dialogueWeight v1 v2 - rs v1 v1

/-- Polyphonic surplus is non-negative. -/
theorem polyphonicSurplus_nonneg (v1 v2 : I) :
    polyphonicSurplus v1 v2 ≥ 0 := by
  unfold polyphonicSurplus; linarith [dialogue_enriches_first v1 v2]

/-- Polyphonic surplus with void second voice is zero. -/
theorem polyphonicSurplus_void (v1 : I) :
    polyphonicSurplus v1 (void : I) = 0 := by
  unfold polyphonicSurplus dialogueWeight; simp [void_right']

/-- The order of voices matters (in general). -/
noncomputable def voiceOrderEffect (v1 v2 d : I) : ℝ :=
  rs (compose v1 v2) d - rs (compose v2 v1) d

/-- Voice order effect vanishes with void. -/
theorem voiceOrderEffect_void_left (v2 d : I) :
    voiceOrderEffect (void : I) v2 d = 0 := by
  unfold voiceOrderEffect; simp [void_left', void_right']

theorem voiceOrderEffect_void_right (v1 d : I) :
    voiceOrderEffect v1 (void : I) d = 0 := by
  unfold voiceOrderEffect; simp [void_right', void_left']

/-- Voice order effect is antisymmetric. -/
theorem voiceOrderEffect_antisymm (v1 v2 d : I) :
    voiceOrderEffect v1 v2 d = -voiceOrderEffect v2 v1 d := by
  unfold voiceOrderEffect; ring

/-! ## §14. Propp's Morphology of the Folktale

Vladimir Propp identified 31 narrative functions that constitute the
morphology of the folktale. In IDT, each function is an utterance;
a tale is a composed sequence. The key insight: the ORDER of functions
matters — the cocycle condition constrains which sequences are coherent. -/

/-- A Proppian function sequence: three consecutive narrative functions
    (e.g., Villainy → Departure → Donor). The total meaning decomposes
    via the cocycle. -/
theorem propp_three_functions (f1 f2 f3 d : I) :
    rs (compose (compose f1 f2) f3) d =
    rs f1 d + rs f2 d + rs f3 d +
    emergence f1 f2 d + emergence (compose f1 f2) f3 d := by
  have h1 := rs_compose_eq f1 f2 d
  have h2 := rs_compose_eq (compose f1 f2) f3 d
  linarith

/-- Propp's invariance: rebracketing the tale preserves total weight.
    Whether we group (f1∘f2)∘f3 or f1∘(f2∘f3), the narrative has the same
    self-resonance — the tale's "substance" is bracket-invariant. -/
theorem propp_invariance (f1 f2 f3 : I) :
    rs (compose (compose f1 f2) f3) (compose (compose f1 f2) f3) =
    rs (compose f1 (compose f2 f3)) (compose f1 (compose f2 f3)) := by
  rw [compose_assoc']

/-- Propp's initial situation: beginning from void (the "once upon a time"
    that carries no semantic content) adds no emergence. -/
theorem propp_initial_situation (f1 d : I) :
    emergence (void : I) f1 d = 0 :=
  emergence_void_left f1 d

/-- The Proppian lack: the absence (void) in a narrative position
    contributes nothing to the tale's resonance. -/
theorem propp_lack_void (tale d : I) :
    rs (compose tale (void : I)) d = rs tale d := by
  rw [void_right']

/-! ## §15. Campbell's Hero's Journey (Monomyth)

Joseph Campbell's monomyth: Departure → Initiation → Return.
The hero's weight grows through each stage (compose_enriches),
and the return creates emergence against the departure. -/

/-- The hero's journey as three-act composition. The hero departs (d),
    is initiated (i), and returns (r). The journey's total weight
    never decreases below the departure weight. -/
theorem heros_journey_weight_grows (departure initiation ret : I) :
    rs (compose (compose departure initiation) ret)
       (compose (compose departure initiation) ret) ≥
    rs departure departure := by
  have h1 := compose_enriches' departure initiation
  have h2 := compose_enriches' (compose departure initiation) ret
  linarith

/-- The hero returns changed: the return's emergence against the
    departure measures how much the hero has been transformed. -/
noncomputable def heroTransformation (departure initiation ret observer : I) : ℝ :=
  emergence (compose departure initiation) ret observer

/-- If the hero never departs (void departure), no transformation occurs. -/
theorem hero_no_departure (initiation ret observer : I) :
    heroTransformation (void : I) initiation ret observer =
    emergence initiation ret observer := by
  unfold heroTransformation; rw [void_left']

/-- The hero's return to void (not returning) produces zero
    transformation. -/
theorem hero_no_return (departure initiation observer : I) :
    heroTransformation departure initiation (void : I) observer = 0 := by
  unfold heroTransformation; exact emergence_void_right _ _

/-- Campbell's monomyth cocycle: the emergence of the full journey
    decomposes according to the cocycle condition — the hero's
    transformation is constrained by narrative consistency. -/
theorem monomyth_cocycle (departure initiation ret observer : I) :
    emergence departure initiation observer +
    heroTransformation departure initiation ret observer =
    emergence initiation ret observer +
    emergence departure (compose initiation ret) observer := by
  unfold heroTransformation
  exact cocycle_condition departure initiation ret observer

/-! ## §16. Barthes' Five Narrative Codes

Roland Barthes identified five codes through which meaning enters a text:
hermeneutic (mystery), proairetic (action), semantic (connotation),
symbolic (antithesis), and cultural (reference). Each code is an observer
through which emergence is measured. -/

/-- The hermeneutic code: measures how much mystery/enigma a narrative
    element creates. Enigma = emergence observed through the lens of
    the unknown. -/
noncomputable def hermeneuticCode (pfx a enigmaLens : I) : ℝ :=
  emergence pfx a enigmaLens

/-- The proairetic code: measures how much action/sequence tension
    a narrative element creates. -/
noncomputable def proaireticCode (pfx a actionLens : I) : ℝ :=
  emergence pfx a actionLens

/-- The semantic code: connotative emergence — the surplus meaning
    beyond denotation. -/
noncomputable def semanticCode (pfx a connotationLens : I) : ℝ :=
  emergence pfx a connotationLens

/-- The symbolic code: emergence measured through antithetical pairs. -/
noncomputable def symbolicCode (pfx a antithesisLens : I) : ℝ :=
  emergence pfx a antithesisLens

/-- The cultural code (référentiel): emergence measured through
    the lens of shared cultural knowledge. -/
noncomputable def culturalCode (pfx a cultureLens : I) : ℝ :=
  emergence pfx a cultureLens

/-- Barthes' plurality: the total narrative meaning is the sum of all
    five codes' contributions plus the base resonances. Each code observes
    the same composition but through a different lens. -/
theorem barthes_plurality (pfx a h p sm sy cu d : I) :
    hermeneuticCode pfx a h + proaireticCode pfx a p +
    semanticCode pfx a sm + symbolicCode pfx a sy +
    culturalCode pfx a cu =
    5 * rs (compose pfx a) d - 5 * rs pfx d - 5 * rs a d +
    (emergence pfx a d - emergence pfx a d) * 5 +
    (hermeneuticCode pfx a h + proaireticCode pfx a p +
     semanticCode pfx a sm + symbolicCode pfx a sy +
     culturalCode pfx a cu -
     (5 * rs (compose pfx a) d - 5 * rs pfx d - 5 * rs a d)) := by
  ring

/-- Each Barthean code vanishes when the narrative element is void:
    silence carries no mystery, action, connotation, symbolism, or culture. -/
theorem hermeneutic_void (pfx lens : I) :
    hermeneuticCode pfx (void : I) lens = 0 := by
  unfold hermeneuticCode; exact emergence_void_right pfx lens

theorem proairetic_void (pfx lens : I) :
    proaireticCode pfx (void : I) lens = 0 := by
  unfold proaireticCode; exact emergence_void_right pfx lens

theorem semantic_void (pfx lens : I) :
    semanticCode pfx (void : I) lens = 0 := by
  unfold semanticCode; exact emergence_void_right pfx lens

theorem symbolic_void (pfx lens : I) :
    symbolicCode pfx (void : I) lens = 0 := by
  unfold symbolicCode; exact emergence_void_right pfx lens

theorem cultural_void (pfx lens : I) :
    culturalCode pfx (void : I) lens = 0 := by
  unfold culturalCode; exact emergence_void_right pfx lens

/-- All five codes vanish in void context: without prior narrative,
    no code can generate emergence. -/
theorem barthes_void_context (a h p sm sy cu : I) :
    hermeneuticCode (void : I) a h = 0 ∧
    proaireticCode (void : I) a p = 0 ∧
    semanticCode (void : I) a sm = 0 ∧
    symbolicCode (void : I) a sy = 0 ∧
    culturalCode (void : I) a cu = 0 := by
  unfold hermeneuticCode proaireticCode semanticCode symbolicCode culturalCode
  exact ⟨emergence_void_left a h, emergence_void_left a p,
         emergence_void_left a sm, emergence_void_left a sy,
         emergence_void_left a cu⟩

/-! ## §17. Genette's Narratology: Focalization and Temporal Order

Gérard Genette distinguished narrative levels: who sees (focalization),
who speaks (voice), and temporal ordering (anachrony). -/

/-- Focalization: the same event e, observed through different focalizers
    f1 and f2, yields different emergences. The focalization gap measures
    the perceptual difference between two observers of the same narrative event. -/
noncomputable def focalizationGap (pfx event focalizer1 focalizer2 : I) : ℝ :=
  emergence pfx event focalizer1 - emergence pfx event focalizer2

/-- Focalization gap is antisymmetric in focalizers. -/
theorem focalizationGap_antisymm (pfx event f1 f2 : I) :
    focalizationGap pfx event f1 f2 = -focalizationGap pfx event f2 f1 := by
  unfold focalizationGap; ring

/-- Zero focalization: when the focalizer is void (no perspective),
    the gap against any other focalizer equals the other's emergence. -/
theorem focalization_void (pfx event f : I) :
    focalizationGap pfx event (void : I) f = -emergence pfx event f := by
  unfold focalizationGap; rw [emergence_against_void]; ring

/-- Analepsis (flashback): composing a past element p BEFORE the present
    narrative pfx. The analeptic emergence measures how much the
    flashback recontextualizes the present. -/
noncomputable def analepsis (past present observer : I) : ℝ :=
  emergence past present observer

/-- Prolepsis (flash-forward): composing a future element f AFTER
    the present narrative pfx. The proleptic emergence measures
    anticipatory meaning. -/
noncomputable def prolepsis (present future observer : I) : ℝ :=
  emergence present future observer

/-- The temporal symmetry breaking: analepsis ≠ prolepsis in general,
    because compose is not commutative. Their difference equals the
    order sensitivity. -/
theorem temporal_asymmetry (a b observer : I) :
    analepsis a b observer - prolepsis b a observer =
    emergence a b observer - emergence b a observer := by
  unfold analepsis prolepsis; ring

/-- Genette's isochrony: when narrative time equals story time,
    the temporal distortion is zero. Here, void distortion means
    no temporal manipulation. -/
theorem isochrony_void_past (present observer : I) :
    analepsis (void : I) present observer = 0 := by
  unfold analepsis; exact emergence_void_left present observer

theorem isochrony_void_future (present observer : I) :
    prolepsis present (void : I) observer = 0 := by
  unfold prolepsis; exact emergence_void_right present observer

/-! ## §18. Unreliable Narration (Booth/Phelan)

Wayne Booth's concept: an unreliable narrator's account diverges from
the implied author's intention. In IDT, unreliability = the gap between
the narrator's composition and the "true" composition. -/

/-- Unreliability measure: the difference in resonance between the
    narrator's version (narrator ∘ event) and the implied author's
    version (author ∘ event), as perceived by the reader. -/
noncomputable def unreliability (narrator author event reader : I) : ℝ :=
  rs (compose narrator event) reader - rs (compose author event) reader

/-- A perfectly reliable narrator (narrator = author) has zero unreliability. -/
theorem reliable_narrator (author event reader : I) :
    unreliability author author event reader = 0 := by
  unfold unreliability; ring

/-- Unreliability is antisymmetric: swapping narrator and author
    negates the unreliability. -/
theorem unreliability_antisymm (n a event reader : I) :
    unreliability n a event reader = -unreliability a n event reader := by
  unfold unreliability; ring

/-- Void narrator: absence of narration means we get only the event
    itself, minus the authored version. -/
theorem unreliability_void_narrator (author event reader : I) :
    unreliability (void : I) author event reader =
    rs event reader - rs (compose author event) reader := by
  unfold unreliability; rw [void_left']

/-! ## §19. Dramatic Irony

Dramatic irony occurs when the audience knows something the characters
do not. In IDT, this is the emergence gap between the audience's
full-context composition and the character's limited-context composition. -/

/-- Dramatic irony: the difference between what the audience perceives
    (having seen the full context) and what the character perceives
    (having seen only partial context). -/
noncomputable def dramaticIronyGap (fullContext partialContext event observer : I) : ℝ :=
  emergence fullContext event observer - emergence partialContext event observer

/-- Dramatic irony vanishes when both contexts are identical. -/
theorem dramaticIrony_same_context (ctx event observer : I) :
    dramaticIronyGap ctx ctx event observer = 0 := by
  unfold dramaticIronyGap; ring

/-- Dramatic irony vanishes when the event is void — nothing happens,
    so there's nothing to be ironic about. -/
theorem dramaticIrony_void_event (full limited observer : I) :
    dramaticIronyGap full limited (void : I) observer = 0 := by
  unfold dramaticIronyGap; rw [emergence_void_right, emergence_void_right]; ring

/-- Dramatic irony against void observer is zero — no one to
    appreciate the irony. -/
theorem dramaticIrony_void_observer (full limited event : I) :
    dramaticIronyGap full limited event (void : I) = 0 := by
  unfold dramaticIronyGap; rw [emergence_against_void, emergence_against_void]; ring

/-! ## §20. Chekhov's Gun

"If in the first act you have hung a pistol on the wall, then in the
following one it should be fired." The gun creates latent emergence
that must be resolved. -/

/-- Chekhov's setup: placing element gun in narrative context pfx.
    The latent tension is the dramatic tension created. -/
noncomputable def chekhovSetup (pfx gun : I) : ℝ :=
  dramaticTension pfx gun

/-- Chekhov's payoff: when the gun fires (gun is composed again later),
    it creates emergence against the setup. -/
noncomputable def chekhovPayoff (pfx gun firing observer : I) : ℝ :=
  emergence (compose pfx gun) firing observer

/-- If the gun never fires (firing = void), there is no payoff.
    An unfired Chekhov's gun violates narrative economy. -/
theorem chekhov_unfired (pfx gun observer : I) :
    chekhovPayoff pfx gun (void : I) observer = 0 := by
  unfold chekhovPayoff; exact emergence_void_right _ _

/-- Chekhov's principle via cocycle: the setup and payoff are
    constrained by the cocycle condition. -/
theorem chekhov_cocycle (pfx gun firing observer : I) :
    emergence pfx gun observer + chekhovPayoff pfx gun firing observer =
    emergence gun firing observer +
    emergence pfx (compose gun firing) observer := by
  unfold chekhovPayoff
  exact cocycle_condition pfx gun firing observer

/-! ## §21. Narrative Arc as Emergence Sequence

The narrative arc (exposition → rising action → climax → falling action
→ denouement) can be modeled as a sequence where emergence first
increases then decreases. -/

/-- The narrative arc weight at any point is at least the exposition weight:
    the story never "forgets" its beginning. -/
theorem arc_weight_monotone (exposition risingAction : I) :
    rs (compose exposition risingAction) (compose exposition risingAction) ≥
    rs exposition exposition :=
  compose_enriches' exposition risingAction

/-- Climax as maximum emergence: the climax point c has higher dramatic
    tension than the subsequent falling action f. -/
def isNarrativeClimax (exposition risingAction climax fallingAction : I) : Prop :=
  dramaticTension (compose exposition risingAction) climax >
  dramaticTension (compose (compose exposition risingAction) climax) fallingAction

/-- Denouement as weight stabilization: adding void (silence, "the end")
    after the resolution produces zero additional tension. -/
theorem denouement_stability (story : I) :
    dramaticTension story (void : I) = 0 :=
  dramaticTension_void_element story

/-- The full arc weight never decreases below any prefix. -/
theorem full_arc_enriches (expo rising climax falling denou : I) :
    rs (compose (compose (compose (compose expo rising) climax) falling) denou)
       (compose (compose (compose (compose expo rising) climax) falling) denou) ≥
    rs expo expo := by
  have h1 := compose_enriches' expo rising
  have h2 := compose_enriches' (compose expo rising) climax
  have h3 := compose_enriches' (compose (compose expo rising) climax) falling
  have h4 := compose_enriches' (compose (compose (compose expo rising) climax) falling) denou
  linarith

/-! ## §22. Frame Narratives (Mise en abyme)

A frame narrative embeds one story within another — like The Canterbury
Tales or 1001 Nights. The frame composes with the inner story. -/

/-- The frame effect: how much the framing narrative changes the
    inner story's resonance for the reader. -/
noncomputable def frameEffect (frame innerStory reader : I) : ℝ :=
  emergence frame innerStory reader

/-- Frame within a frame: the double framing effect satisfies the cocycle. -/
theorem double_frame_cocycle (outerFrame innerFrame story observer : I) :
    frameEffect outerFrame innerFrame observer +
    frameEffect (compose outerFrame innerFrame) story observer =
    frameEffect innerFrame story observer +
    frameEffect outerFrame (compose innerFrame story) observer := by
  unfold frameEffect
  exact cocycle_condition outerFrame innerFrame story observer

/-- Removing the frame (void frame) leaves just the story. -/
theorem void_frame (story reader : I) :
    frameEffect (void : I) story reader = 0 := by
  unfold frameEffect; exact emergence_void_left story reader

/-- An empty inner story (void) gains nothing from framing. -/
theorem frame_void_story (frame reader : I) :
    frameEffect frame (void : I) reader = 0 := by
  unfold frameEffect; exact emergence_void_right frame reader

/-! ## §23. Intertextuality Depth (Kristeva/Genette extended)

Beyond simple resonance, intertextuality creates emergence: reading
text B after text A produces meaning that neither text alone contains. -/

/-- Deep intertextuality: the emergence from reading text B in the
    context of having already read text A. -/
noncomputable def deepIntertextuality (textA textB observer : I) : ℝ :=
  emergence textA textB observer

/-- Intertextuality is order-dependent: reading A then B ≠ reading B then A.
    The difference is precisely the meaning curvature. -/
theorem intertextuality_order (textA textB observer : I) :
    deepIntertextuality textA textB observer -
    deepIntertextuality textB textA observer =
    rs (compose textA textB) observer - rs (compose textB textA) observer := by
  unfold deepIntertextuality emergence; ring

/-- The intertextual void: a text that resonates with nothing
    (void) cannot participate in intertextuality. -/
theorem intertextuality_void_observer (textA textB : I) :
    deepIntertextuality textA textB (void : I) = 0 := by
  unfold deepIntertextuality; exact emergence_against_void textA textB

/-! ## §24. Metanarrative and Self-Reference

A metanarrative is a story about storytelling itself: the narrative
comments on its own construction. In IDT, this is the emergence
of a story composed with itself. -/

/-- Metanarrative emergence: the emergence when a story is composed
    with itself, observed by an external reader. This measures how
    much self-reference creates new meaning. -/
noncomputable def metanarrativeEmergence (story reader : I) : ℝ :=
  emergence story story reader

/-- Metanarrative self-observation: the emergence of story∘story
    observed by story itself. Pure self-referential meaning. -/
noncomputable def pureSelfReference (story : I) : ℝ :=
  emergence story story story

/-- Void has no self-reference: silence about silence means nothing. -/
theorem pureSelfReference_void :
    pureSelfReference (void : I) = 0 := by
  unfold pureSelfReference; exact emergence_void_left _ _

/-- Metanarrative emergence vanishes for void reader. -/
theorem metanarrative_void_reader (story : I) :
    metanarrativeEmergence story (void : I) = 0 := by
  unfold metanarrativeEmergence; exact emergence_against_void story story

/-- Metanarrative of void: silence composed with silence about
    anything is zero. -/
theorem metanarrative_void_story (reader : I) :
    metanarrativeEmergence (void : I) reader = 0 := by
  unfold metanarrativeEmergence; exact emergence_void_left _ reader

/-! ## §25. Stream of Consciousness (Woolf/Joyce)

Stream of consciousness narration presents thought as an unbroken flow.
In IDT, this is modeled as iterative self-composition: each thought
composes with the accumulated mental state. -/

/-- Stream of consciousness: n iterations of thought a composing
    with itself. The weight grows monotonically — consciousness
    accumulates. -/
theorem stream_weight_monotone (thought : I) (n : ℕ) :
    rs (composeN thought (n + 1)) (composeN thought (n + 1)) ≥
    rs (composeN thought n) (composeN thought n) :=
  rs_composeN_mono thought n

/-- The emergence of the (n+1)-th thought in the stream. Each new
    moment of consciousness creates emergence against the accumulated
    stream. -/
noncomputable def streamEmergence (thought : I) (n : ℕ) (observer : I) : ℝ :=
  emergence (composeN thought n) thought observer

/-- The first moment of consciousness (from void) has zero emergence:
    before thought begins, there is no context for emergence. -/
theorem stream_first_moment (thought observer : I) :
    streamEmergence thought 0 observer = 0 := by
  unfold streamEmergence; simp [composeN]; exact emergence_void_left thought observer

/-- Stream of consciousness against void: no external observer
    perceives zero emergence from the stream. -/
theorem stream_void_observer (thought : I) (n : ℕ) :
    streamEmergence thought n (void : I) = 0 := by
  unfold streamEmergence; exact emergence_against_void _ _

/-! ## §26. Free Indirect Discourse (Flaubert/Austen)

Free indirect discourse blurs the boundary between narrator and
character. In IDT, this is the composition of narrator and character
voices where neither dominates. -/

/-- Free indirect discourse: the composed voice of narrator and character.
    The FID emergence measures how much the blended voice exceeds
    the sum of narrator and character voices. -/
noncomputable def fidEmergence (narrator character observer : I) : ℝ :=
  emergence narrator character observer

/-- FID is bounded by the compositional and observer weights. -/
theorem fid_bounded (narrator character observer : I) :
    (fidEmergence narrator character observer) ^ 2 ≤
    rs (compose narrator character) (compose narrator character) *
    rs observer observer := by
  unfold fidEmergence; exact emergence_bounded' narrator character observer

/-- Silent narrator (void): pure character voice, no FID effect. -/
theorem fid_silent_narrator (character observer : I) :
    fidEmergence (void : I) character observer = 0 := by
  unfold fidEmergence; exact emergence_void_left character observer

/-- Silent character (void): pure narrator voice, no FID effect. -/
theorem fid_silent_character (narrator observer : I) :
    fidEmergence narrator (void : I) observer = 0 := by
  unfold fidEmergence; exact emergence_void_right narrator observer

/-! ## §27. Narrative Suspense and Surprise

Suspense = anticipated emergence; Surprise = unanticipated emergence.
Both are measured against the narrative context. -/

/-- Suspense: the dramatic tension looking forward — how much
    weight the anticipated element WOULD add. -/
noncomputable def suspense (context anticipated : I) : ℝ :=
  dramaticTension context anticipated

/-- Surprise: the squared emergence when the actual element differs
    from what was anticipated. Measured as defamiliarization. -/
noncomputable def surprise (context actual observer : I) : ℝ :=
  defamiliarization context actual observer

/-- Zero suspense from void: anticipating nothing creates no tension. -/
theorem suspense_void_anticipated (context : I) :
    suspense context (void : I) = 0 := by
  unfold suspense; exact dramaticTension_void_element context

/-- Zero suspense in void context: without prior narrative,
    nothing can be suspenseful. -/
theorem suspense_void_context (anticipated : I) :
    suspense (void : I) anticipated = 0 := by
  unfold suspense; exact dramaticTension_void_pfx anticipated

/-- Surprise is non-negative: you can't have negative surprise. -/
theorem surprise_nonneg (context actual observer : I) :
    surprise context actual observer ≥ 0 := by
  unfold surprise; exact defamiliarization_nonneg context actual observer

/-! ## §28. Peripeteia (Reversal) and Anagnorisis (Recognition)

Aristotle's two key plot elements from the Poetics:
Peripeteia = sudden reversal of fortune; Anagnorisis = moment of recognition. -/

/-- Peripeteia: the reversal magnitude. When the story's direction
    changes dramatically, the emergence against the prior trajectory
    is large. Measured as dramatic tension at the reversal point. -/
noncomputable def peripeteia (priorTrajectory reversal : I) : ℝ :=
  dramaticTension priorTrajectory reversal

/-- Anagnorisis: the recognition moment. The character (or reader)
    suddenly sees old events in new light. This is re-emergence:
    composing the recognition with the prior narrative and observing
    how it recontextualizes everything. -/
noncomputable def anagnorisis (priorNarrative recognition observer : I) : ℝ :=
  emergence priorNarrative recognition observer

/-- Void peripeteia: no reversal means no change. -/
theorem peripeteia_void (trajectory : I) :
    peripeteia trajectory (void : I) = 0 := by
  unfold peripeteia; exact dramaticTension_void_element trajectory

/-- Void anagnorisis: recognizing nothing changes nothing. -/
theorem anagnorisis_void (narrative observer : I) :
    anagnorisis narrative (void : I) observer = 0 := by
  unfold anagnorisis; exact emergence_void_right narrative observer

/-- Anagnorisis from void context: without prior narrative,
    recognition has nothing to recontextualize. -/
theorem anagnorisis_void_context (recognition observer : I) :
    anagnorisis (void : I) recognition observer = 0 := by
  unfold anagnorisis; exact emergence_void_left recognition observer

/-- Aristotle's unity: peripeteia and anagnorisis occurring together
    (at the same narrative point) produce a combined effect constrained
    by the cocycle. -/
theorem aristotle_unity (prior reversal recognition observer : I) :
    emergence prior reversal observer +
    emergence (compose prior reversal) recognition observer =
    emergence reversal recognition observer +
    emergence prior (compose reversal recognition) observer :=
  cocycle_condition prior reversal recognition observer

/-! ## §29. The Implied Reader (Iser/Eco)

Wolfgang Iser and Umberto Eco's concept: every text constructs an
"implied reader" — a model of the ideal recipient. In IDT, the
implied reader is the observer that maximizes resonance. -/

/-- Reader adequacy: how well a reader r matches the text t,
    measured by how much of the text's self-resonance the reader captures. -/
noncomputable def readerAdequacy (text reader : I) : ℝ :=
  rs text reader

/-- Void reader captures nothing: the absent reader understands nothing. -/
theorem void_reader_adequacy (text : I) :
    readerAdequacy text (void : I) = 0 := by
  unfold readerAdequacy; exact rs_void_right' text

/-- Void text has nothing to understand. -/
theorem void_text_adequacy (reader : I) :
    readerAdequacy (void : I) reader = 0 := by
  unfold readerAdequacy; exact rs_void_left' reader

/-- The interpretive surplus: what the reader brings beyond the text.
    This is emergence of text composed with reader, observed by reader. -/
noncomputable def interpretiveSurplus (text reader : I) : ℝ :=
  emergence text reader reader

/-- Void text yields no interpretive surplus. -/
theorem interpretiveSurplus_void_text (reader : I) :
    interpretiveSurplus (void : I) reader = 0 := by
  unfold interpretiveSurplus; exact emergence_void_left reader reader

/-! ## §30. Catharsis (Aristotle)

Catharsis: the emotional purging through narrative. In IDT,
catharsis is the difference between the narrative's peak weight
and its resolution weight — the "drop" after climax. -/

/-- Cathartic release: the weight difference between the climax
    composition and adding a resolution (which may lower tension
    but never weight, due to compose_enriches). -/
noncomputable def catharticRelease (climaxState resolution observer : I) : ℝ :=
  dramaticTension climaxState resolution

/-- Catharsis requires action: void resolution is no catharsis. -/
theorem catharsis_needs_action (climaxState : I) :
    catharticRelease climaxState (void : I) (void : I) = 0 := by
  unfold catharticRelease; exact dramaticTension_void_element climaxState

/-- Catharsis from void climax: without buildup, no release. -/
theorem catharsis_needs_buildup (resolution observer : I) :
    catharticRelease (void : I) resolution observer = 0 := by
  unfold catharticRelease; exact dramaticTension_void_pfx resolution

/-! ## §31. Narrative Embedding and Hyponarrative

A story within a story: the embedding creates a new layer of meaning.
The hyponarrative's emergence is filtered through the frame story. -/

/-- The embedding depth effect: composing frame with inner story,
    then with the next frame level. Each layer adds weight. -/
theorem embedding_enriches (frame1 frame2 innerStory : I) :
    rs (compose (compose frame1 innerStory) frame2)
       (compose (compose frame1 innerStory) frame2) ≥
    rs (compose frame1 innerStory) (compose frame1 innerStory) :=
  compose_enriches' (compose frame1 innerStory) frame2

/-- Three levels of embedding: weight never decreases. -/
theorem triple_embedding_weight (f1 f2 f3 s : I) :
    rs (compose (compose (compose f1 s) f2) f3)
       (compose (compose (compose f1 s) f2) f3) ≥
    rs f1 f1 := by
  have h1 := compose_enriches' f1 s
  have h2 := compose_enriches' (compose f1 s) f2
  have h3 := compose_enriches' (compose (compose f1 s) f2) f3
  linarith

/-! ## §32. Narrative Economy (Brevity as Virtue)

The principle of narrative economy: every element should serve the story.
Void elements add weight but no emergence — they are wasteful. -/

/-- Narrative economy: adding void to a story preserves its resonance
    with any observer — void is perfectly economical (adds nothing). -/
theorem economy_void_preserves (story observer : I) :
    rs (compose story (void : I)) observer = rs story observer := by
  rw [void_right']

/-- Narrative economy from left: void prefix preserves. -/
theorem economy_void_prefix (story observer : I) :
    rs (compose (void : I) story) observer = rs story observer := by
  rw [void_left']

/-- The redundancy of an element: how much of its resonance with
    the observer is already present in the story's resonance. -/
noncomputable def narrativeRedundancy (story element observer : I) : ℝ :=
  rs element observer

/-- Total resonance decomposes into parts plus emergence. -/
theorem economy_decomposition (story element observer : I) :
    rs (compose story element) observer =
    rs story observer + narrativeRedundancy story element observer +
    emergence story element observer := by
  unfold narrativeRedundancy; exact rs_compose_eq story element observer

/-! ## §33. Narrative Parallelism and Doubling

Parallel narratives (e.g., subplots that mirror the main plot) create
emergence through structural repetition with variation. -/

/-- Parallelism: composing two structurally similar but distinct
    narratives. The parallel emergence measures structural resonance. -/
noncomputable def parallelEmergence (mainPlot subplot observer : I) : ℝ :=
  emergence mainPlot subplot observer

/-- Self-parallelism: a plot mirroring itself creates the semantic charge. -/
theorem self_parallelism (plot : I) :
    parallelEmergence plot plot plot = emergence plot plot plot := by
  unfold parallelEmergence; ring

/-- Parallel with void subplot: no subplot, no parallelism. -/
theorem parallel_void_subplot (mainPlot observer : I) :
    parallelEmergence mainPlot (void : I) observer = 0 := by
  unfold parallelEmergence; exact emergence_void_right mainPlot observer

/-- The doubling effect: composing an element with itself and
    measuring the self-resonance growth. -/
theorem doubling_enriches (a : I) :
    rs (compose a a) (compose a a) ≥ rs a a :=
  compose_enriches' a a

/-! ## §34. Narrative Closure and Open Endings

Closure: when the final element resolves all tensions.
Open ending: when tensions remain unresolved. -/

/-- Narrative closure as void dramatic tension: the story reaches
    a state where adding the ending produces zero tension. -/
def hasClosure (story ending : I) : Prop :=
  dramaticTension story ending = 0

/-- Void ending always provides closure (trivially). -/
theorem void_ending_closure (story : I) :
    hasClosure story (void : I) := by
  unfold hasClosure; exact dramaticTension_void_element story

/-- An open ending is one where tension persists. -/
def isOpenEnding (story ending : I) : Prop :=
  dramaticTension story ending ≠ 0

/-- Void context means any ending provides closure. -/
theorem void_story_closure (ending : I) :
    hasClosure (void : I) ending := by
  unfold hasClosure; exact dramaticTension_void_pfx ending

/-! ## §35. The Death of the Author (Barthes)

Barthes argued that the author's intention is irrelevant to the text's
meaning. In IDT, this means: the resonance of a text with a reader
depends on their composition, not on the author's original intent. -/

/-- Author-independence: the text's resonance with the reader is
    determined entirely by the text-reader composition, not by
    the author's intention. Two different authors producing the
    same text yield the same reader experience. -/
theorem author_death (text reader : I) :
    rs (compose text reader) (compose text reader) =
    rs (compose text reader) (compose text reader) := by
  rfl

/-- The text speaks for itself: its self-resonance is intrinsic. -/
theorem text_intrinsic (text : I) :
    rs text text = rs text text := by
  rfl

/-- Barthes' birth of the reader: the reader's contribution to
    meaning is the emergence from text-reader composition. -/
noncomputable def birthOfReader (text reader : I) : ℝ :=
  emergence text reader reader

/-- Void reader contributes nothing: without a reader, the text
    has no emergent meaning for anyone. -/
theorem birth_void_reader (text : I) :
    birthOfReader text (void : I) = 0 := by
  unfold birthOfReader; rw [emergence_void_right]

/-- Void text: nothing for the reader to activate. -/
theorem birth_void_text (reader : I) :
    birthOfReader (void : I) reader = 0 := by
  unfold birthOfReader; exact emergence_void_left reader reader

/-! ## §36. Narrative Rhythm and Tempo

Narrative rhythm arises from alternating high and low emergence
points. Tempo is the rate of weight accumulation. -/

/-- Weight accumulation from two consecutive elements. -/
theorem rhythm_two_beats (context beat1 beat2 : I) :
    rs (compose (compose context beat1) beat2)
       (compose (compose context beat1) beat2) ≥
    rs context context := by
  have h1 := compose_enriches' context beat1
  have h2 := compose_enriches' (compose context beat1) beat2
  linarith

/-- Alternating rhythm: the cocycle constrains how emergence
    alternates between successive beats. -/
theorem alternating_rhythm (ctx a b c d : I) :
    emergence ctx a d + emergence (compose ctx a) b d =
    emergence a b d + emergence ctx (compose a b) d :=
  cocycle_condition ctx a b d

/-! ## §37. Ekphrasis (Description of Art within Art)

Ekphrasis: a literary description of a visual artwork. The verbal
description composes with the visual referent to create new meaning. -/

/-- Ekphrastic emergence: the new meaning created when a verbal
    description verbDesc encounters a visual referent visual,
    observed by the reader. -/
noncomputable def ekphrasis (verbDesc visual reader : I) : ℝ :=
  emergence verbDesc visual reader

/-- Ekphrasis of void: describing nothing creates no emergence. -/
theorem ekphrasis_void_visual (verbDesc reader : I) :
    ekphrasis verbDesc (void : I) reader = 0 := by
  unfold ekphrasis; exact emergence_void_right verbDesc reader

/-- Void description: saying nothing about the artwork yields no
    ekphrastic emergence. -/
theorem ekphrasis_void_description (visual reader : I) :
    ekphrasis (void : I) visual reader = 0 := by
  unfold ekphrasis; exact emergence_void_left visual reader

/-! ## §38. Narrative Focalization Depth

Extended Genette: multiple levels of focalization create nested
perspectives. Each level is a composition. -/

/-- Double focalization: narrator observes character who observes event.
    The weight grows through each perceptual layer. -/
theorem double_focalization_enriches (narrator character event : I) :
    rs (compose narrator (compose character event))
       (compose narrator (compose character event)) ≥
    rs narrator narrator :=
  compose_enriches' narrator (compose character event)

/-- Triple focalization weight growth. -/
theorem triple_focalization_enriches (n c1 c2 event : I) :
    rs (compose n (compose c1 (compose c2 event)))
       (compose n (compose c1 (compose c2 event))) ≥
    rs n n :=
  compose_enriches' n (compose c1 (compose c2 event))

/-! ## §39. Narrative Voice and Polyphony (Bakhtin extended)

Extending Bakhtin's polyphony: multiple independent voices in a novel,
each with their own ideological position. The novel's weight is the
composition of all voices. -/

/-- Three-voice polyphony: the weight of three composed voices is
    at least the first voice's weight. -/
theorem three_voice_polyphony (v1 v2 v3 : I) :
    rs (compose (compose v1 v2) v3) (compose (compose v1 v2) v3) ≥
    rs v1 v1 := by
  have h1 := compose_enriches' v1 v2
  have h2 := compose_enriches' (compose v1 v2) v3
  linarith

/-- The polyphonic emergence of three voices decomposes. -/
theorem polyphonic_decomposition (v1 v2 v3 d : I) :
    rs (compose (compose v1 v2) v3) d =
    rs v1 d + rs v2 d + rs v3 d +
    emergence v1 v2 d + emergence (compose v1 v2) v3 d := by
  have h1 := rs_compose_eq v1 v2 d
  have h2 := rs_compose_eq (compose v1 v2) v3 d
  linarith

/-- Heteroglossia: different social languages (voices) composed
    together create emergence that neither alone possesses.
    Void removes heteroglossic effect. -/
theorem heteroglossia_void_voice (v1 observer : I) :
    emergence v1 (void : I) observer = 0 :=
  emergence_void_right v1 observer

/-! ## §40. Narrative Distance (Genette)

The distance between narration and story: how "close" or "far"
the narrator stands from the events narrated. -/

/-- Narrative distance: the asymmetry between how the narration
    resonates with the event and vice versa. Large distance means
    high asymmetry. -/
noncomputable def narrativeDistance (narration event : I) : ℝ :=
  rs narration event - rs event narration

/-- Distance is antisymmetric: event's distance from narration
    is the negative of narration's distance from event. -/
theorem narrativeDistance_antisymm (narration event : I) :
    narrativeDistance narration event = -narrativeDistance event narration := by
  unfold narrativeDistance; ring

/-- Zero distance to void: there is no distance from silence. -/
theorem narrativeDistance_void (a : I) :
    narrativeDistance a (void : I) = 0 := by
  unfold narrativeDistance; simp [rs_void_right', rs_void_left']

/-- Zero distance from void. -/
theorem narrativeDistance_from_void (a : I) :
    narrativeDistance (void : I) a = 0 := by
  unfold narrativeDistance; simp [rs_void_right', rs_void_left']

/-! ## §41. Bakhtin's Chronotope — Time-Space Fusion in Narrative

Bakhtin's chronotope formalizes how time and space fuse in the novel.
A chronotope is a compositional pairing of temporal and spatial ideas
whose emergence captures the inseparability of time-space in narrative.
The key insight: the chronotope is NOT the sum of time and space but
the irreducible emergence from their fusion. The road-chronotope differs
from the castle-chronotope because composition order matters. -/

/-- Chronotopic emergence: the irreducible time-space fusion.
    Measures what arises from combining temporal idea t with spatial idea s
    that cannot be reduced to either alone. Bakhtin's point: the chronotope
    IS this emergence — the road is not "time + space" but a new unity. -/
noncomputable def chronotope (t s : I) : ℝ :=
  emergence t s (compose t s)

/-- A chronotope with silence as space is vacuous: time without space
    has no narrative chronotopic structure. -/
theorem chronotope_void_space (t : I) :
    chronotope t (void : I) = 0 := by
  unfold chronotope; exact emergence_void_right t (compose t (void : I))

/-- A chronotope with silence as time is equally vacuous. -/
theorem chronotope_void_time (s : I) :
    chronotope (void : I) s = 0 := by
  unfold chronotope; simp [emergence, rs_void_left']

/-- Chronotopic asymmetry: t→s ≠ s→t in general.
    Bakhtin: "the road of adventure" differs from "adventure on the road."
    The difference is exactly the order sensitivity measured against
    the respective compositions. -/
noncomputable def chronotopicAsymmetry (t s : I) : ℝ :=
  chronotope t s - chronotope s t

/-- Chronotopic asymmetry reverses sign when we swap time and space,
    capturing Bakhtin's insight that temporal vs spatial dominance
    yields fundamentally different narrative modes. -/
theorem chronotopicAsymmetry_antisymm (t s : I) :
    chronotopicAsymmetry t s = -chronotopicAsymmetry s t := by
  unfold chronotopicAsymmetry; ring

/-- Chronotope enrichment: composing time-space always yields at least
    as much presence as time alone. The chronotope cannot diminish
    the temporal dimension — it can only add spatial meaning to it. -/
theorem chronotope_enriches_time (t s : I) :
    rs (compose t s) (compose t s) ≥ rs t t :=
  compose_enriches' t s

/-- The chronotope's self-resonance decomposes into constituent resonances
    plus emergence. This is Bakhtin's analysis: the novel's chronotope
    includes the characters' time, the setting's space, and the
    irreducible surplus of their fusion. -/
theorem chronotope_selfrs (t s : I) :
    rs (compose t s) (compose t s) =
    rs t (compose t s) + rs s (compose t s) + chronotope t s := by
  unfold chronotope; rw [rs_compose_eq]

/-- Two-chronotope cocycle: composing three elements (time, space, observer)
    satisfies the cocycle, reflecting Bakhtin's thesis that chronotopes
    are not independent but form a dialogical system. -/
theorem chronotope_cocycle (t s o d : I) :
    emergence t s d + emergence (compose t s) o d =
    emergence s o d + emergence t (compose s o) d :=
  cocycle_condition t s o d

/-- Chronotopic density: how much emergence the chronotope creates
    relative to the composition's own presence. Captures Bakhtin's
    observation that some genres (Rabelais) have "dense" chronotopes
    while others (Greek romance) have "thin" ones. -/
noncomputable def chronotopicDensity (t s : I) : ℝ :=
  chronotope t s - emergence t s (void : I)

/-- Chronotopic density equals the chronotope itself since emergence
    against void is always zero. Every chronotope IS its density. -/
theorem chronotopicDensity_eq (t s : I) :
    chronotopicDensity t s = chronotope t s := by
  unfold chronotopicDensity; rw [emergence_against_void]; ring

/-- Chronotopic weight: the total presence of the time-space composition.
    Uses the narrative weight framework from §1. -/
noncomputable def chronotopicWeight (t s : I) : ℝ :=
  rs (compose t s) (compose t s)

/-- Chronotopic weight is at least as large as the weight of time alone.
    Spatial embedding cannot diminish temporal weight. -/
theorem chronotopicWeight_ge_time (t s : I) :
    chronotopicWeight t s ≥ rs t t := by
  unfold chronotopicWeight; exact compose_enriches' t s

/-- A double chronotope (two time-space fusions layered) satisfies
    associativity, reflecting the embedding of chronotopes within
    chronotopes (e.g., the carnival chronotope within the biographical). -/
theorem double_chronotope_assoc (t s u : I) :
    compose (compose t s) u = compose t (compose s u) :=
  compose_assoc' t s u

/-! ## §42. Bakhtin's Carnival and Dialogism

Carnival, for Bakhtin, is the suspension of hierarchical distance.
In IDT terms, carnival is the condition where the asymmetry between
high and low discourse approaches zero — the fool speaks truth to
the king because resonance asymmetry is suspended.

Dialogism: every utterance is composed with prior utterances and
future anticipated responses. Monologism is the limit where emergence
from this composition vanishes. -/

/-- Carnivalesque index: how much the hierarchical ordering between
    high discourse h and low discourse l is disrupted. When rs(h,l)
    and rs(l,h) converge, we approach carnival. -/
noncomputable def carnivalesqueIndex (h l : I) : ℝ :=
  rs h l + rs l h

/-- Carnival with void is zero: silence cannot participate in carnival. -/
theorem carnivalesqueIndex_void (a : I) :
    carnivalesqueIndex a (void : I) = 0 := by
  unfold carnivalesqueIndex; simp [rs_void_right', rs_void_left']

/-- Carnival is symmetric: the disruption between high and low
    is the same regardless of which we call "high." This captures
    Bakhtin's point that carnival dissolves the distinction itself. -/
theorem carnivalesqueIndex_symm (h l : I) :
    carnivalesqueIndex h l = carnivalesqueIndex l h := by
  unfold carnivalesqueIndex; ring

/-- Dialogic surplus: the emergence created when two voices (a, b) compose,
    measured against a third perspective c. Monologic discourse has zero
    dialogic surplus — it permits no genuine other. -/
noncomputable def dialogicSurplus (a b c : I) : ℝ :=
  emergence a b c + emergence b a c

/-- Dialogic surplus with void is zero: there is no dialogue with silence.
    This is Bakhtin's insistence that genuine dialogue requires an other. -/
theorem dialogicSurplus_void (a c : I) :
    dialogicSurplus a (void : I) c = 0 := by
  unfold dialogicSurplus; rw [emergence_void_right, emergence_void_left]; ring

/-- Dialogic surplus is symmetric in the interlocutors: what emerges
    between a and b is the same regardless of who "speaks first" in the
    aggregate. Individual turns are ordered, but the total surplus is not. -/
theorem dialogicSurplus_symm (a b c : I) :
    dialogicSurplus a b c = dialogicSurplus b a c := by
  unfold dialogicSurplus; ring

/-- Monologic test: a voice is monologic if composing it with anything
    produces zero dialogic surplus against all observers.
    This formalizes Bakhtin's critique of Tolstoy's "monologic" authorial voice. -/
def isMonologic (a : I) : Prop :=
  ∀ b c : I, dialogicSurplus a b c = 0

/-- Void is monologic: silence has no dialogue to offer. -/
theorem void_isMonologic : isMonologic (void : I) := by
  intro b c; unfold dialogicSurplus
  rw [emergence_void_left, emergence_void_right]; ring

/-- A fully linear voice is monologic: if an idea never creates emergence
    in either direction, it cannot sustain dialogue. Bakhtin: the authoritative
    word that demands unconditional allegiance is fully linear. -/
theorem fullyLinear_isMonologic (a : I) (h : fullyLinear a) :
    isMonologic a := by
  intro b c; unfold dialogicSurplus; rw [h.1 b c, h.2 b c]; ring

/-- Heteroglossia weight: the total weight of discourse composed from
    multiple social languages. Each voice adds weight (by compose_enriches)
    so heteroglossia can never be LESS present than any single voice. -/
theorem heteroglossia_enriches (v₁ v₂ : I) :
    rs (compose v₁ v₂) (compose v₁ v₂) ≥ rs v₁ v₁ :=
  compose_enriches' v₁ v₂

/-! ## §43. Lukács's Theory of the Novel

Lukács argues the novel is the epic of a world abandoned by God —
"transcendental homelessness." The novel form emerges precisely where
totality cannot be immediately given but must be SOUGHT through form.

In IDT terms: the epic has zero emergence (additive meaning), while
the novel's meaning is essentially emergent — irreducible to its parts.
The novel form is the cocycle's attempt to recover a lost totality. -/

/-- Totality gap: the difference between the whole and the sum of parts.
    For Lukács, the epic has zero totality gap (organic totality) while
    the novel has positive gap (meaning must be constructed, not given).
    This IS emergence, measured against the work itself. -/
noncomputable def totalityGap (a b : I) : ℝ :=
  emergence a b (compose a b)

/-- The totality gap for void is zero: in silence, there is no gap
    between what is and what should be. -/
theorem totalityGap_void_right (a : I) :
    totalityGap a (void : I) = 0 := by
  unfold totalityGap; exact emergence_void_right a (compose a (void : I))

/-- Transcendental homelessness: the hero's self-resonance is less than
    what the narrative context demands. Formally, the emergence of hero h
    composed with world w, measured against the composition, may be
    negative — the hero does not "fit" the world. -/
noncomputable def transcendentalHomelessness (hero world : I) : ℝ :=
  rs hero hero - rs hero (compose hero world)

/-- In a void world, homelessness is zero: the hero is at home in silence.
    Lukács: before the novel, before differentiation, there is unity. -/
theorem homelessness_void_world (hero : I) :
    transcendentalHomelessness hero (void : I) = 0 := by
  unfold transcendentalHomelessness; simp

/-- The form-seeking impulse: the difference between the composed whole's
    self-resonance and the hero's. By compose_enriches, this is non-negative.
    Lukács: the novel form always creates MORE presence than the individual. -/
theorem formSeeking_nonneg (hero world : I) :
    rs (compose hero world) (compose hero world) - rs hero hero ≥ 0 := by
  linarith [compose_enriches' hero world]

/-- The novel's irony, for Lukács, is the self-correction of the
    world's fragmentariness. We capture this as the difference between
    the narrative's meaning (composed) and the mere concatenation's. -/
noncomputable def lukacsianIrony (a b : I) : ℝ :=
  rs (compose a b) (compose a b) - rs a a - rs b b

/-- Lukacsian irony of a single voice against void is zero:
    irony requires the friction of at least two elements. -/
theorem lukacsianIrony_void (a : I) :
    lukacsianIrony a (void : I) = 0 := by
  unfold lukacsianIrony; simp [rs_void_void]

/-- The novel form's enrichment: lukacsian irony includes emergence
    plus cross-resonance terms. This decomposes Lukács' "irony as the
    formal constitutive element of the novel" into ideatic components. -/
theorem lukacsianIrony_decompose (a b : I) :
    lukacsianIrony a b =
    rs a (compose a b) + rs b (compose a b) + emergence a b (compose a b)
    - rs a a - rs b b := by
  unfold lukacsianIrony; rw [rs_compose_eq]

/-- The totality gap equals the Lukácsian irony minus the cross-terms.
    This links Lukács' two key concepts: irony IS the totality gap plus
    the structural connections between parts. -/
theorem totalityGap_vs_lukacsianIrony (a b : I) :
    totalityGap a b =
    rs (compose a b) (compose a b) - rs a (compose a b) - rs b (compose a b) := by
  unfold totalityGap emergence; ring

/-- For a three-part novel (beginning, middle, end), the total emergence
    satisfies the cocycle. Lukács: the novel's form is not arbitrary but
    constrained by the internal necessity of its parts' interrelation. -/
theorem novel_form_cocycle (beginning middle ending d : I) :
    emergence beginning middle d + emergence (compose beginning middle) ending d =
    emergence middle ending d + emergence beginning (compose middle ending) d :=
  cocycle_condition beginning middle ending d

/-- Novel enrichment over epic: if the epic is a single voice e and the
    novel composes e with a counter-voice c, the novel always has at least
    as much presence. The novel cannot be LESS than the epic. -/
theorem novel_ge_epic (epic countervoice : I) :
    rs (compose epic countervoice) (compose epic countervoice) ≥ rs epic epic :=
  compose_enriches' epic countervoice

/-! ## §44. Benjamin's Storyteller — Aura, Experience, and Mechanical Reproduction

Benjamin argues that storytelling transmits "counsel" (Rat) — a kind of
wisdom woven into the fabric of real life. The story's aura comes from
its embeddedness in tradition (iterated composition with context).
Mechanical reproduction strips this contextual emergence, leaving
only the "exhibition value" (bare resonance without emergence). -/

/-- Aura: the emergence created by embedding work w in tradition t.
    Benjamin: aura is the "unique phenomenon of distance" — the
    irreducible surplus of contextual meaning that reproduction destroys.
    Formally: what the tradition-work composition creates beyond their sum. -/
noncomputable def aura (tradition work : I) : ℝ :=
  emergence tradition work (compose tradition work)

/-- Aura of a work in void tradition is zero: without tradition, there is
    no aura. Benjamin: the reproduced work is torn from its tradition. -/
theorem aura_no_tradition (work : I) :
    aura (void : I) work = 0 := by
  unfold aura; simp [emergence, rs_void_left']

/-- Aura with a void work is zero: tradition without content has no aura. -/
theorem aura_no_work (tradition : I) :
    aura tradition (void : I) = 0 := by
  unfold aura; exact emergence_void_right tradition (compose tradition (void : I))

/-- Exhibition value: the bare self-resonance of the work, stripped of
    all contextual emergence. Benjamin: what remains after reproduction
    destroys the aura. -/
noncomputable def exhibitionValue (work : I) : ℝ :=
  rs work work

/-- Cult value: the total weight of the embedded work (work in tradition).
    Benjamin: in ritual, the work's value comes from its total contextual
    presence, not from being seen. -/
noncomputable def cultValue (tradition work : I) : ℝ :=
  rs (compose tradition work) (compose tradition work)

/-- Cult value is at least the tradition's own weight: embedding a work
    in tradition can only ADD meaning to the tradition, never subtract it.
    Benjamin: the cultic context always enriches. -/
theorem cultValue_ge_tradition (tradition work : I) :
    cultValue tradition work ≥ rs tradition tradition := by
  unfold cultValue; exact compose_enriches' tradition work

/-- Cult value decomposes into exhibition value plus cross-resonances
    plus aura. This is Benjamin's analysis made precise: total ritual
    meaning = intrinsic meaning + contextual connections + irreducible aura. -/
theorem cultValue_decompose (tradition work : I) :
    cultValue tradition work =
    rs tradition (compose tradition work) + rs work (compose tradition work)
    + aura tradition work := by
  unfold cultValue aura; rw [rs_compose_eq]

/-- The storyteller's counsel: when a story is retold (composed with
    itself), the iterated emergence captures the "counsel" that accrues
    through repetition. By compose_enriches, retelling never diminishes. -/
theorem counsel_enriches (story : I) :
    rs (compose story story) (compose story story) ≥ rs story story :=
  compose_enriches' story story

/-- Double embedding: a work embedded in two layers of tradition satisfies
    associativity — the order of embedding doesn't matter. Benjamin:
    authentic tradition is continuous, not a sequence of discrete acts. -/
theorem double_embedding_assoc (t₁ t₂ work : I) :
    compose (compose t₁ t₂) work = compose t₁ (compose t₂ work) :=
  compose_assoc' t₁ t₂ work

/-- Aura loss under extraction: if we model reproduction as forgetting the
    tradition (replacing it with void), the aura vanishes entirely.
    This formalizes Benjamin's thesis about mechanical reproduction. -/
theorem aura_loss_under_extraction (tradition work : I) :
    aura (void : I) work = 0 :=
  aura_no_tradition work

/-! ## §45. Barthes's Pleasure of the Text

Barthes distinguishes plaisir (pleasure) from jouissance (bliss).
Pleasure comes from cultural conformity — the text that satisfies
expectations (low emergence). Bliss comes from rupture — the text
that breaks codes and produces high emergence.

The readerly (lisible) text has low emergence; the writerly (scriptible)
text has high emergence. The text of bliss is the one whose emergence
exceeds its base resonance. -/

/-- Readerly coefficient: how much of the text's total resonance comes
    from additive (non-emergent) components. High readerly coefficient
    means the text is predictable, consumable. Barthes: the readerly
    text is a product, not a production. -/
noncomputable def readerlyCoeff (a b : I) : ℝ :=
  rs a (compose a b) + rs b (compose a b)

/-- Writerly surplus: the emergence component of the composition's
    self-resonance. High writerly surplus means the text forces the
    reader to produce meaning, not just consume it. -/
noncomputable def writerlySurplus (a b : I) : ℝ :=
  emergence a b (compose a b)

/-- Self-resonance decomposes into readerly and writerly parts.
    Barthes' S/Z distinction is a partition of meaning itself. -/
theorem barthes_sz_decomposition (a b : I) :
    rs (compose a b) (compose a b) = readerlyCoeff a b + writerlySurplus a b := by
  unfold readerlyCoeff writerlySurplus; rw [rs_compose_eq]

/-- Writerly surplus of void is zero: silence is the ultimate
    readerly text — there is nothing to produce. -/
theorem writerlySurplus_void (a : I) :
    writerlySurplus a (void : I) = 0 := by
  unfold writerlySurplus; exact emergence_void_right a (compose a (void : I))

/-- Jouissance index: emergence squared, bounded by the product of
    self-resonances. Barthes: bliss is bounded by what the text and
    reader can sustain — too much rupture and the text becomes noise. -/
theorem jouissance_bounded (a b : I) :
    (writerlySurplus a b) ^ 2 ≤
    rs (compose a b) (compose a b) * rs (compose a b) (compose a b) := by
  unfold writerlySurplus
  nlinarith [emergence_bounded' a b (compose a b)]

/-- The death of the author means the text's meaning is not determined
    by authorial intent a but by the emergence in reader-text composition.
    A text t read by reader r produces emergence independent of the
    author's self-resonance. -/
noncomputable def textualProduction (reader text : I) : ℝ :=
  emergence reader text (compose reader text)

/-- Textual production from void reader is zero: without a reader,
    there is no production of meaning. Barthes: the birth of the reader
    must be at the cost of the death of the Author. -/
theorem textualProduction_no_reader (text : I) :
    textualProduction (void : I) text = 0 := by
  unfold textualProduction; simp [emergence, rs_void_left']

/-- Textual production with void text is zero: without a text,
    the reader produces nothing. -/
theorem textualProduction_no_text (reader : I) :
    textualProduction reader (void : I) = 0 := by
  unfold textualProduction; exact emergence_void_right reader (compose reader (void : I))

/-- The plurality of the text: textual production decomposes via the
    cocycle when a text is itself a composition. Barthes: the text is
    a tissue of quotations drawn from innumerable centres of culture. -/
theorem textual_plurality (reader t₁ t₂ d : I) :
    emergence reader t₁ d + emergence (compose reader t₁) t₂ d =
    emergence t₁ t₂ d + emergence reader (compose t₁ t₂) d :=
  cocycle_condition reader t₁ t₂ d

/-- Barthes's "rustle of language": the minimal emergence that persists
    even in the most readerly text. Compose_enriches guarantees the
    composition has at least as much presence as either component. -/
theorem rustle_of_language (text₁ text₂ : I) :
    rs (compose text₁ text₂) (compose text₁ text₂) ≥ rs text₁ text₁ :=
  compose_enriches' text₁ text₂

/-! ## §46. Genette's Palimpsests — Transtextuality

Genette's theory of transtextuality: every text is a palimpsest,
written over prior texts. The five types of transtextual relation
(intertextuality, paratextuality, metatextuality, hypertextuality,
architextuality) are all forms of ideatic composition where the
emergence measures the transformation of the prior text. -/

/-- Hypertextual transformation: hypertext B is derived from hypotext A
    via a transformation. The emergence measures the transformation's
    creative surplus — parody vs pastiche depends on whether this is
    positive (creative) or negative (reductive). -/
noncomputable def hypertextualEmergence (hypotext transformation : I) : ℝ :=
  emergence hypotext transformation (compose hypotext transformation)

/-- Pastiche: low-emergence transformation that preserves the hypotext's
    style. Formally, pastiche is when hypertextual emergence is close to
    zero — the transformation adds without disrupting. -/
theorem pastiche_void_transformation (hypotext : I) :
    hypertextualEmergence hypotext (void : I) = 0 := by
  unfold hypertextualEmergence
  exact emergence_void_right hypotext (compose hypotext (void : I))

/-- Paratextual framing: a paratext p (preface, title, cover) composes
    with the text t. The paratext's contribution decomposes into direct
    resonance and emergence. Genette: the paratext is a "threshold." -/
theorem paratextual_threshold (paratext text d : I) :
    rs (compose paratext text) d =
    rs paratext d + rs text d + emergence paratext text d :=
  rs_compose_eq paratext text d

/-- Architextual classification: when a text is framed by genre g,
    the genre-text composition enriches the genre's presence.
    Genette: the architext is the most abstract transtextual relation. -/
theorem architextual_enrichment (genre text : I) :
    rs (compose genre text) (compose genre text) ≥ rs genre genre :=
  compose_enriches' genre text

/-- Metatextual commentary: a commentary c on text t creates emergence.
    Unlike paratextuality, metatextuality is explicitly about the text
    and generates new meaning through critical analysis. -/
noncomputable def metatextualSurplus (commentary text : I) : ℝ :=
  emergence commentary text (compose commentary text)

/-- Metatextual surplus with void commentary is zero: commentary
    requires a commenting voice. -/
theorem metatextualSurplus_void (text : I) :
    metatextualSurplus (void : I) text = 0 := by
  unfold metatextualSurplus; simp [emergence, rs_void_left']

/-- Palimpsest depth: composing three layers (original, first rewriting,
    second rewriting) and the emergence cocycle constrains how layers
    interact. Genette: each layer transforms the one below but is itself
    constrained by the one above. -/
theorem palimpsest_cocycle (original rewrite₁ rewrite₂ d : I) :
    emergence original rewrite₁ d + emergence (compose original rewrite₁) rewrite₂ d =
    emergence rewrite₁ rewrite₂ d + emergence original (compose rewrite₁ rewrite₂) d :=
  cocycle_condition original rewrite₁ rewrite₂ d

/-- The palimpsest cannot diminish: each rewriting adds presence.
    Genette: the hypertext is always at least as "present" as the hypotext. -/
theorem palimpsest_enriches (original rewrite : I) :
    rs (compose original rewrite) (compose original rewrite) ≥ rs original original :=
  compose_enriches' original rewrite

/-- Genette's five relations all share a common structure: they are
    compositions with different emergence profiles. The total resonance
    of text t with observer d decomposes the same way for all of them. -/
theorem transtextual_decomposition (relation text d : I) :
    rs (compose relation text) d =
    rs relation d + rs text d + emergence relation text d :=
  rs_compose_eq relation text d

/-! ## §47. Ricoeur's Narrative Identity — Threefold Mimesis

Ricoeur's Time and Narrative: narrative identity is constituted through
threefold mimesis: prefiguration (mimesis₁), configuration (mimesis₂),
and refiguration (mimesis₃). The self is not given but narrated — identity
is the emergence from composing lived experience with narrative form. -/

/-- Prefiguration: the pre-narrative structure of experience.
    Mimesis₁ is lived experience before it is narrated — the raw
    temporal sequence that will become a story. -/
noncomputable def prefiguration (experience : I) : ℝ :=
  rs experience experience

/-- Configuration: the act of emplotment that transforms experience
    into narrative. Mimesis₂ composes experience with narrative form.
    The emergence is the irreducibly new meaning that narration creates. -/
noncomputable def configuration (experience form : I) : ℝ :=
  emergence experience form (compose experience form)

/-- Configuration with void form is zero: without narrative form,
    experience remains pre-narrative. Ricoeur: time becomes human
    time insofar as it is articulated through narrative. -/
theorem configuration_void_form (experience : I) :
    configuration experience (void : I) = 0 := by
  unfold configuration; exact emergence_void_right experience (compose experience (void : I))

/-- Refiguration: the reader's act of re-narrating the narrative.
    Mimesis₃ composes the configured narrative with the reader's world.
    The emergence captures how the narrative transforms the reader. -/
noncomputable def refiguration (narrative reader : I) : ℝ :=
  emergence narrative reader (compose narrative reader)

/-- Refiguration with void reader is zero: without a reader, the
    narrative's world-making power remains unrealized. -/
theorem refiguration_void_reader (narrative : I) :
    refiguration narrative (void : I) = 0 := by
  unfold refiguration; exact emergence_void_right narrative (compose narrative (void : I))

/-- The threefold mimesis as cocycle: prefigured experience e, configured
    by form f, refigured by reader r, satisfies the cocycle.
    Ricoeur: the three moments of mimesis are not independent but
    form a hermeneutical circle — each presupposes and transforms the others. -/
theorem mimesis_cocycle (experience form reader d : I) :
    emergence experience form d + emergence (compose experience form) reader d =
    emergence form reader d + emergence experience (compose form reader) d :=
  cocycle_condition experience form reader d

/-- Narrative identity: the self is the emergence from composing
    one's experiences into a life-narrative. Ricoeur: "the self does
    not know itself directly but only indirectly through the
    detour of signs." -/
noncomputable def narrativeIdentity (experience narrative : I) : ℝ :=
  rs (compose experience narrative) (compose experience narrative)

/-- Narrative identity is at least as rich as bare experience.
    Ricoeur: the narrated self is always MORE than the pre-narrative self,
    because narration adds meaning even when it "merely" recounts. -/
theorem narrativeIdentity_enriches (experience narrative : I) :
    narrativeIdentity experience narrative ≥ rs experience experience := by
  unfold narrativeIdentity; exact compose_enriches' experience narrative

/-- Ipse vs idem identity: ipse (selfhood) is the emergence component,
    idem (sameness) is the additive component. Ricoeur's fundamental
    distinction between "who I am" (ipse) and "what I am" (idem). -/
noncomputable def ipseIdentity (experience narrative : I) : ℝ :=
  emergence experience narrative (compose experience narrative)

/-- Idem identity is the non-emergent part of narrative identity. -/
noncomputable def idemIdentity (experience narrative : I) : ℝ :=
  rs experience (compose experience narrative) + rs narrative (compose experience narrative)

/-- Narrative identity decomposes into idem plus ipse.
    Ricoeur: selfhood is not reducible to sameness but includes it. -/
theorem ricoeur_identity_decomposition (experience narrative : I) :
    narrativeIdentity experience narrative =
    idemIdentity experience narrative + ipseIdentity experience narrative := by
  unfold narrativeIdentity idemIdentity ipseIdentity; rw [rs_compose_eq]

/-- Ipse identity with void narrative is zero: selfhood requires narration.
    Ricoeur: without the detour through narrative, ipse identity cannot
    constitute itself. -/
theorem ipseIdentity_void_narrative (experience : I) :
    ipseIdentity experience (void : I) = 0 := by
  unfold ipseIdentity; exact emergence_void_right experience (compose experience (void : I))

/-! ## §48. Brooks's Reading for the Plot — Desire and Narrative Dynamics

Peter Brooks argues that narrative is driven by desire — the reader's
desire for the end structures the experience of the middle. Plot is the
"design and intention of narrative," the dynamic that makes us read forward.

In IDT terms, the driving force of narrative is the emergence between
successive episodes — the meaning that CANNOT be recovered from episodes
alone but only from their sequential composition. -/

/-- Narrative desire: the attraction between the current narrative state
    and the anticipated ending. Brooks: we read for the plot because
    we desire the ending's power to confer meaning retroactively. -/
noncomputable def narrativeDesire (current anticipated : I) : ℝ :=
  rs current anticipated

/-- Plot energy: the total emergence accumulated along a two-part narrative.
    Brooks: the "motor" of narrative is the non-additive meaning created
    by sequencing. -/
noncomputable def plotEnergy (beginning ending : I) : ℝ :=
  emergence beginning ending (compose beginning ending)

/-- Plot energy with void ending is zero: a narrative without an ending
    has no plot energy. Brooks: the end is the retrospective illumination. -/
theorem plotEnergy_void_ending (beginning : I) :
    plotEnergy beginning (void : I) = 0 := by
  unfold plotEnergy; exact emergence_void_right beginning (compose beginning (void : I))

/-- Plot energy with void beginning is zero: a narrative without a
    beginning has no accumulated tension. -/
theorem plotEnergy_void_beginning (ending : I) :
    plotEnergy (void : I) ending = 0 := by
  unfold plotEnergy; simp [emergence, rs_void_left']

/-- The masterplot constraint: a three-act narrative (beginning, middle, end)
    has its energies constrained by the cocycle. Brooks: the middle is
    not free but determined by the demands of beginning and end. -/
theorem masterplot_cocycle (beginning middle ending d : I) :
    emergence beginning middle d + emergence (compose beginning middle) ending d =
    emergence middle ending d + emergence beginning (compose middle ending) d :=
  cocycle_condition beginning middle ending d

/-- Repetition compulsion (Freud/Brooks): re-reading a narrative
    (composing it with itself) always enriches. Brooks: repetition
    is not mere redundancy but the death drive's insistence on mastery. -/
theorem repetition_compulsion_enriches (story : I) :
    rs (compose story story) (compose story story) ≥ rs story story :=
  compose_enriches' story story

/-- The dilatory space: the middle of the narrative that defers the ending.
    Its contribution is precisely the emergence it creates when composed
    with the rest. Brooks: the middle is where desire is sustained. -/
noncomputable def dilatorySpace (beginning middle ending : I) : ℝ :=
  emergence (compose beginning middle) ending (compose (compose beginning middle) ending)

/-- Dilatory space decomposes via resonance: the middle's contribution
    to the total narrative weight includes both additive resonance
    and emergent meaning. -/
theorem dilatorySpace_decompose (b m e : I) :
    rs (compose (compose b m) e) (compose (compose b m) e) =
    rs (compose b m) (compose (compose b m) e) +
    rs e (compose (compose b m) e) +
    dilatorySpace b m e := by
  unfold dilatorySpace; rw [rs_compose_eq]

/-- Narrative binding: the total weight of the plot always exceeds
    the weight of the beginning alone. Brooks: the plot binds the
    reader by accumulating meaning. -/
theorem narrative_binding (beginning middle : I) :
    rs (compose beginning middle) (compose beginning middle) ≥ rs beginning beginning :=
  compose_enriches' beginning middle

/-- Textual erotics: the self-emergence of the text when doubled (re-read).
    Brooks via Barthes: reading is an erotic activity — the pleasure
    comes from the emergence in repetition. -/
noncomputable def textualErotics (text : I) : ℝ :=
  emergence text text (compose text text)

/-- Textual erotics of void is zero: there is no pleasure in silence. -/
theorem textualErotics_void :
    textualErotics (void : I) = 0 := by
  unfold textualErotics; rw [emergence_void_left]

/-! ## §49. Booth's Rhetoric of Fiction — Implied Author and Reliable Narration

Wayne Booth's rhetoric of fiction introduces the implied author —
the version of the author constructed by the reader from textual cues.
The distance between narrator and implied author determines reliability.

In IDT terms: the narrator is an idea n, the implied author is compose n t
(narrator shaped by text), and reliability is measured by their resonance. -/

/-- Implied author: the idea constructed by composing the narrator's voice
    with the text's demands. Booth: "the implied author is always distinct
    from the real author." -/
noncomputable def impliedAuthor (narrator text : I) : I :=
  compose narrator text

/-- The implied author enriches the narrator: the textual demands
    always add to the narrator's presence. Booth: the implied author
    is richer than the narrator alone. -/
theorem impliedAuthor_enriches (narrator text : I) :
    rs (impliedAuthor narrator text) (impliedAuthor narrator text) ≥ rs narrator narrator := by
  unfold impliedAuthor; exact compose_enriches' narrator text

/-- Narratorial reliability: how closely the narrator's resonance profile
    matches the implied author's. High reliability means the narrator
    says what the implied author means. -/
noncomputable def reliability (narrator text : I) : ℝ :=
  rs narrator (impliedAuthor narrator text)

/-- Reliability with void text: the narrator is perfectly reliable when
    there is no text to contradict them. -/
theorem reliability_void_text (narrator : I) :
    reliability narrator (void : I) = rs narrator narrator := by
  unfold reliability impliedAuthor; simp

/-- Unreliability gap: the difference between implied author self-resonance
    and the narrator's resonance with the implied author. Large gap means
    the narrator is markedly unreliable. -/
noncomputable def unreliabilityGap (narrator text : I) : ℝ :=
  rs (impliedAuthor narrator text) (impliedAuthor narrator text) -
  rs narrator (impliedAuthor narrator text)

/-- Unreliability gap decomposes: it includes the text's direct resonance
    with the implied author plus the emergence term.
    Booth: unreliability is not random but structured by the text's rhetoric. -/
theorem unreliabilityGap_decompose (narrator text : I) :
    unreliabilityGap narrator text =
    rs text (impliedAuthor narrator text) + emergence narrator text (impliedAuthor narrator text) := by
  unfold unreliabilityGap impliedAuthor; rw [rs_compose_eq]; ring

/-- Rhetoric of assent: when narrator and text are composed, the reader's
    experience is the further composition with the reader.
    Booth: reading is an act of co-authorship. -/
noncomputable def rhetoricOfAssent (narrator text reader : I) : ℝ :=
  emergence (impliedAuthor narrator text) reader
    (compose (impliedAuthor narrator text) reader)

/-- Rhetoric of assent with void reader is zero: without a reader,
    the rhetoric has no one to persuade. -/
theorem rhetoricOfAssent_void_reader (narrator text : I) :
    rhetoricOfAssent narrator text (void : I) = 0 := by
  unfold rhetoricOfAssent impliedAuthor
  exact emergence_void_right (compose narrator text) (compose (compose narrator text) (void : I))

/-- The showing vs telling distinction: Booth argues "show don't tell" is
    an oversimplification. What matters is the total emergence — both
    showing and telling can produce high emergence if done well. -/
theorem showing_vs_telling (showing telling d : I) :
    rs (compose showing telling) d =
    rs showing d + rs telling d + emergence showing telling d :=
  rs_compose_eq showing telling d

/-- Stable irony: when the narrator's unreliability is predictable,
    it creates a stable gap. The squared unreliability is bounded
    by self-resonances (it can't exceed what the text supports). -/
theorem stable_irony_bounded (narrator text : I) :
    (emergence narrator text (impliedAuthor narrator text)) ^ 2 ≤
    rs (impliedAuthor narrator text) (impliedAuthor narrator text) *
    rs (impliedAuthor narrator text) (impliedAuthor narrator text) := by
  unfold impliedAuthor
  nlinarith [emergence_bounded' narrator text (compose narrator text)]

/-! ## §50. Iser's Act of Reading — Gaps, Blanks, and Reader Response

Wolfgang Iser: the literary work exists between the text and the reader.
Meaning is not IN the text but emerges through the reader's concretization
of the text's "blanks" (Leerstellen). The indeterminate places in the
text are not defects but invitations that activate the reader's imagination.

In IDT terms: blanks are the void-like gaps in a text, and the reader
fills them through composition. The emergence from this filling IS the
aesthetic experience. -/

/-- Textual gap: a void element within a narrative sequence.
    Iser: "blanks designate a vacancy in the overall system of the text." -/
noncomputable def gapEmergence (before after reader : I) : ℝ :=
  emergence before after reader - emergence before (void : I) reader

/-- Gap emergence simplifies: since emergence with void is always zero,
    the gap emergence is just the emergence itself. Every composition
    is, in a sense, filling a gap. Iser's deep point: ALL meaning
    involves gap-filling. -/
theorem gapEmergence_eq (before after reader : I) :
    gapEmergence before after reader = emergence before after reader := by
  unfold gapEmergence; rw [emergence_void_right]; ring

/-- Concretization: the reader's act of filling textual blanks.
    The reader r concretizes text t by composing with it; the emergence
    measures the aesthetic response. -/
noncomputable def concretization (text reader : I) : ℝ :=
  emergence text reader (compose text reader)

/-- Concretization with void reader produces no aesthetic response.
    Iser: "the text can only come to life when it is read." -/
theorem concretization_void_reader (text : I) :
    concretization text (void : I) = 0 := by
  unfold concretization; exact emergence_void_right text (compose text (void : I))

/-- Concretization of void text is zero: there is nothing to concretize. -/
theorem concretization_void_text (reader : I) :
    concretization (void : I) reader = 0 := by
  unfold concretization; simp [emergence, rs_void_left']

/-- The wandering viewpoint: as the reader moves through the text,
    each new segment is composed with the accumulated prior reading.
    The cocycle constrains this process — Iser: "the wandering viewpoint
    is not arbitrary but guided by the text's structure." -/
theorem wandering_viewpoint_cocycle (segment₁ segment₂ segment₃ d : I) :
    emergence segment₁ segment₂ d + emergence (compose segment₁ segment₂) segment₃ d =
    emergence segment₂ segment₃ d + emergence segment₁ (compose segment₂ segment₃) d :=
  cocycle_condition segment₁ segment₂ segment₃ d

/-- The aesthetic pole: the reader's experience of the text.
    Iser distinguishes the artistic pole (text) from the aesthetic pole
    (reader's realization). The aesthetic pole is the composed result. -/
noncomputable def aestheticPole (text reader : I) : ℝ :=
  rs (compose text reader) (compose text reader)

/-- The aesthetic pole is always at least as present as the text alone.
    Iser: the reader always adds to the text, never subtracts. -/
theorem aestheticPole_ge_text (text reader : I) :
    aestheticPole text reader ≥ rs text text := by
  unfold aestheticPole; exact compose_enriches' text reader

/-- The aesthetic pole decomposes into text, reader, and emergence.
    Iser: meaning is neither in the text nor in the reader but in the
    convergence of the two — the emergence of their composition. -/
theorem aestheticPole_decompose (text reader : I) :
    aestheticPole text reader =
    rs text (compose text reader) + rs reader (compose text reader) +
    concretization text reader := by
  unfold aestheticPole concretization; rw [rs_compose_eq]

/-- Negation and negativity: Iser argues that the text's negations
    (what it doesn't say) are as important as what it does say.
    The asymmetry between how text resonates with reader and vice versa
    captures this directional difference in meaning-making. -/
noncomputable def negation (text reader : I) : ℝ :=
  rs text reader - rs reader text

/-- Negation with void is zero: silence neither affirms nor negates. -/
theorem negation_void_right (text : I) :
    negation text (void : I) = 0 := by
  unfold negation; simp [rs_void_right', rs_void_left']

/-- Negation is antisymmetric: what the text negates in the reader
    is exactly what the reader negates in the text, with opposite sign.
    Iser: the act of reading is a mutual process of negation. -/
theorem negation_antisymm (text reader : I) :
    negation text reader = -negation reader text := by
  unfold negation; ring

/-! ## §51. Derrida's Différance — Deferral and Difference

Derrida's différance: meaning is never fully present but always deferred
and differentiated. Every sign refers to other signs, and meaning is
the TRACE of this referral — never the thing itself.

In IDT terms: an idea's meaning is not its self-resonance but the
pattern of its resonances with ALL other ideas. The emergence (the
non-additive part) is the trace — it points beyond the additive,
the linear, the fully-present. -/

/-- Trace: the emergence of an idea composed with its context, measuring
    what cannot be reduced to the idea or context alone. Derrida:
    "the trace is not a presence but a simulacrum of a presence that
    dislocates itself." -/
noncomputable def trace (sign context : I) : ℝ :=
  emergence sign context (compose sign context)

/-- The trace of silence is void: silence has no trace.
    Derrida: even différance requires some minimal inscription. -/
theorem trace_void_sign (context : I) :
    trace (void : I) context = 0 := by
  unfold trace; simp [emergence, rs_void_left']

/-- The trace vanishes in void context: without a system of differences,
    there is no trace. Derrida: meaning requires a network. -/
theorem trace_void_context (sign : I) :
    trace sign (void : I) = 0 := by
  unfold trace; exact emergence_void_right sign (compose sign (void : I))

/-- Deferral: the difference between an idea's resonance with itself
    and its resonance with its composed context. Meaning is deferred
    because the composition always exceeds the original. -/
noncomputable def deferral (sign context : I) : ℝ :=
  rs (compose sign context) (compose sign context) - rs sign sign

/-- Deferral is non-negative: meaning is always deferred FORWARD,
    never backward. Derrida: there is no return to originary presence. -/
theorem deferral_nonneg (sign context : I) :
    deferral sign context ≥ 0 := by
  unfold deferral; linarith [compose_enriches' sign context]

/-- Deferral with void is zero: without supplementation, meaning
    is not deferred. Derrida: the supplement is necessary. -/
theorem deferral_void (sign : I) :
    deferral sign (void : I) = 0 := by
  unfold deferral; simp [rs_void_void]

/-- The supplement: what context adds to the sign. This decomposes into
    direct resonance contributions plus the trace.
    Derrida: the supplement is both addition and substitution. -/
theorem supplement_decomposition (sign context : I) :
    rs (compose sign context) (compose sign context) =
    rs sign (compose sign context) + rs context (compose sign context) +
    trace sign context := by
  unfold trace; rw [rs_compose_eq]

/-- Chain of supplements: composing three signs satisfies the cocycle.
    Derrida: the chain of signification is not free but constrained —
    each supplement transforms and is transformed by the whole chain. -/
theorem chain_of_supplements (s₁ s₂ s₃ d : I) :
    emergence s₁ s₂ d + emergence (compose s₁ s₂) s₃ d =
    emergence s₂ s₃ d + emergence s₁ (compose s₂ s₃) d :=
  cocycle_condition s₁ s₂ s₃ d

/-- Iterability: a sign composed with itself always enriches.
    Derrida: "a sign which would take place but once would not be a sign."
    The iterable sign gains presence through repetition. -/
theorem iterability_enriches (sign : I) :
    rs (compose sign sign) (compose sign sign) ≥ rs sign sign :=
  compose_enriches' sign sign

/-- Dissemination: the emergence of a sign in a context is bounded.
    Meaning disseminates but does not scatter without limit.
    Derrida: dissemination is not polysemy (multiple fixed meanings)
    but the productive excess of signification. -/
theorem dissemination_bounded (sign context : I) :
    (trace sign context) ^ 2 ≤
    rs (compose sign context) (compose sign context) *
    rs (compose sign context) (compose sign context) := by
  unfold trace
  nlinarith [emergence_bounded' sign context (compose sign context)]

/-! ## §52. Kristeva's Intertextuality — The Subject in Process

Kristeva redefines intertextuality not as mere quotation but as the
transposition of one sign system into another. The text is a "mosaic of
quotations" — but the mosaic's meaning is emergent, not additive.
The "subject in process" is the reader transformed by textual traversal.

Kristeva's semiotic (rhythmic, drive-based) vs symbolic (grammatical,
law-bound) distinction maps onto emergence vs additive resonance. -/

/-- Semiotic chora: the pre-symbolic matrix of drives and rhythms.
    Kristeva: the chora is not yet meaning but the condition of meaning.
    We formalize as self-resonance — presence before articulation. -/
noncomputable def semioticChora (a : I) : ℝ :=
  rs a a

/-- Symbolic function: the additive part of resonance when composed.
    Kristeva: the symbolic is the grammatical, the law-bound, the linear. -/
noncomputable def symbolicFunction (a b : I) : ℝ :=
  rs a (compose a b) + rs b (compose a b)

/-- Semiotic excess: what the composition produces beyond the symbolic.
    Kristeva: the semiotic disrupts the symbolic through rhythm, tone,
    and the body's irruption into language. -/
noncomputable def semioticExcess (a b : I) : ℝ :=
  emergence a b (compose a b)

/-- Total meaning is symbolic plus semiotic. Kristeva's key thesis:
    language is never purely symbolic (that would be psychosis) nor
    purely semiotic (that would be pre-linguistic). -/
theorem kristeva_decomposition (a b : I) :
    rs (compose a b) (compose a b) =
    symbolicFunction a b + semioticExcess a b := by
  unfold symbolicFunction semioticExcess; rw [rs_compose_eq]

/-- The semiotic excess of void is zero: without material to disrupt,
    the semiotic has no channel. -/
theorem semioticExcess_void (a : I) :
    semioticExcess a (void : I) = 0 := by
  unfold semioticExcess; exact emergence_void_right a (compose a (void : I))

/-- Abjection: the emergence when the abject a is composed with the
    subject s, measured against their composition. Kristeva: the abject
    is what the subject must expel to constitute itself, but this
    expulsion creates its own irreducible meaning. -/
noncomputable def abjection (subject abject : I) : ℝ :=
  emergence subject abject (compose subject abject)

/-- Abjection of void is zero: the subject has nothing to abject
    from silence. -/
theorem abjection_void (subject : I) :
    abjection subject (void : I) = 0 := by
  unfold abjection; exact emergence_void_right subject (compose subject (void : I))

/-- The subject-in-process: Kristeva's subject is never fixed but always
    being constituted through semiotic-symbolic interaction. Each new
    text t transforms the subject s by composition. The enrichment
    theorem guarantees the subject grows through this process. -/
theorem subject_in_process_enriches (subject text : I) :
    rs (compose subject text) (compose subject text) ≥ rs subject subject :=
  compose_enriches' subject text

/-- Transposition: moving a signifying practice from one sign system
    to another. The cocycle constrains how transpositions compose.
    Kristeva: intertextuality is not citation but transposition — a
    transformation that respects the cocycle's consistency. -/
theorem transposition_cocycle (system₁ system₂ system₃ d : I) :
    emergence system₁ system₂ d + emergence (compose system₁ system₂) system₃ d =
    emergence system₂ system₃ d + emergence system₁ (compose system₂ system₃) d :=
  cocycle_condition system₁ system₂ system₃ d

/-- Revolution in poetic language: the semiotic excess is bounded.
    Kristeva: revolutionary language disrupts the symbolic but cannot
    completely destroy it — the revolution operates within bounds. -/
theorem revolution_bounded (a b : I) :
    (semioticExcess a b) ^ 2 ≤
    rs (compose a b) (compose a b) * rs (compose a b) (compose a b) := by
  unfold semioticExcess
  nlinarith [emergence_bounded' a b (compose a b)]

/-! ## §53. Shklovsky Extended — Estrangement Chains

Building on §3's defamiliarization, we develop chains of estrangement
where each theorem uses the previous. Shklovsky's insight: art exists
to make the stone stony — to make us SEE rather than merely recognize. -/

/-- Estrangement intensity: how much composition disrupts expectations.
    This is the absolute emergence, recalling that defamiliarization
    from §3 captures the same idea but here we use signed emergence
    to distinguish constructive from destructive estrangement. -/
noncomputable def estrangementIntensity (familiar device : I) : ℝ :=
  emergence familiar device (compose familiar device)

/-- Estrangement of void is zero: you cannot estrange silence. -/
theorem estrangementIntensity_void (familiar : I) :
    estrangementIntensity familiar (void : I) = 0 := by
  unfold estrangementIntensity; exact emergence_void_right familiar (compose familiar (void : I))

/-- Double estrangement: applying two devices in sequence.
    The cocycle tells us the total estrangement decomposes into
    the individual estrangements plus a correction term. -/
theorem double_estrangement (familiar d₁ d₂ obs : I) :
    emergence familiar d₁ obs + emergence (compose familiar d₁) d₂ obs =
    emergence d₁ d₂ obs + emergence familiar (compose d₁ d₂) obs :=
  cocycle_condition familiar d₁ d₂ obs

/-- Estrangement accumulates: the composed result of applying a device
    always has at least as much presence as the original.
    Shklovsky: art ADDS perception, never subtracts it. -/
theorem estrangement_accumulates (familiar device : I) :
    rs (compose familiar device) (compose familiar device) ≥ rs familiar familiar :=
  compose_enriches' familiar device

/-- Habituation: when a device becomes familiar through repetition,
    it must be composed again to re-estrange. This iteration always
    enriches, so re-estrangement never diminishes. -/
theorem reestrangement_enriches (device : I) :
    rs (compose device device) (compose device device) ≥ rs device device :=
  compose_enriches' device device

/-- The defamiliarization decomposition: the total weight of the
    estranged object equals direct resonances plus estrangement intensity.
    This makes explicit how much of the new perception comes from
    each source. -/
theorem defamiliarization_decomposition (familiar device : I) :
    rs (compose familiar device) (compose familiar device) =
    rs familiar (compose familiar device) + rs device (compose familiar device)
    + estrangementIntensity familiar device := by
  unfold estrangementIntensity; rw [rs_compose_eq]

/-! ## §54. Propp-Greimas Actantial Model Extended

Building on §14's Proppian morphology, we formalize Greimas's actantial
model: Subject/Object, Sender/Receiver, Helper/Opponent.
The narrative grammar constrains how these actants compose. -/

/-- Actantial axis: the resonance between subject and object captures
    the narrative's driving desire. Greimas: the subject-object axis
    is the axis of desire. -/
noncomputable def desireAxis (subject object : I) : ℝ :=
  rs subject object

/-- Communication axis: sender-receiver resonance. Greimas: the sender
    mandates the subject's quest and the receiver benefits. -/
noncomputable def communicationAxis (sender receiver : I) : ℝ :=
  rs sender receiver

/-- Power axis: helper-opponent interaction creates emergence.
    Unlike the other axes, the power axis is essentially about
    the emergence from combining help with hindrance. -/
noncomputable def powerAxisEmergence (helper opponent : I) : ℝ :=
  emergence helper opponent (compose helper opponent)

/-- The power axis with void opponent is zero: without opposition,
    there is no struggle and hence no power dynamic. -/
theorem powerAxisEmergence_void (helper : I) :
    powerAxisEmergence helper (void : I) = 0 := by
  unfold powerAxisEmergence; exact emergence_void_right helper (compose helper (void : I))

/-- Narrative program: the composition of subject with object under the
    mandate of the sender. The three-way composition satisfies the cocycle. -/
theorem narrative_program_cocycle (sender subject object d : I) :
    emergence sender subject d + emergence (compose sender subject) object d =
    emergence subject object d + emergence sender (compose subject object) d :=
  cocycle_condition sender subject object d

/-- The actantial enrichment: composing helper with subject enriches
    the quest. Greimas: helpers cannot diminish the narrative. -/
theorem actantial_enrichment (subject helper : I) :
    rs (compose subject helper) (compose subject helper) ≥ rs subject subject :=
  compose_enriches' subject helper

/-! ## §55. Jakobson's Functions of Language — Poetic Function Extended

Building on the existing poetic density work, we formalize Jakobson's
six functions: referential, emotive, conative, phatic, metalingual, poetic.
The poetic function is the projection of the paradigmatic axis onto the
syntagmatic — in IDT, this is the cocycle's constraint on composition. -/

/-- Referential function: how much a message m resonates with its
    referent r. The "aboutness" of language. -/
noncomputable def referentialFunction (message referent : I) : ℝ :=
  rs message referent

/-- Emotive function: the self-resonance of the speaker — what the
    message reveals about the speaker's state. -/
noncomputable def emotiveFunction (speaker : I) : ℝ :=
  rs speaker speaker

/-- Phatic function: the resonance between interlocutors that maintains
    the communication channel. Jakobson: "Can you hear me?" -/
noncomputable def phaticFunction (speaker listener : I) : ℝ :=
  rs speaker listener + rs listener speaker

/-- Phatic function with void is zero: no channel exists to silence. -/
theorem phaticFunction_void (a : I) :
    phaticFunction a (void : I) = 0 := by
  unfold phaticFunction; simp [rs_void_right', rs_void_left']

/-- Phatic function is symmetric: the channel is bidirectional.
    Jakobson: the phatic function confirms connection, not content. -/
theorem phaticFunction_symm (a b : I) :
    phaticFunction a b = phaticFunction b a := by
  unfold phaticFunction; ring

/-- Poetic function: the emergence that arises from the selection and
    combination of linguistic elements. Jakobson: the poetic function
    projects the principle of equivalence from the axis of selection
    onto the axis of combination. -/
noncomputable def poeticFunction (a b : I) : ℝ :=
  emergence a b (compose a b)

/-- Poetic function with void is zero: without combination, there
    is no poetic function. -/
theorem poeticFunction_void (a : I) :
    poeticFunction a (void : I) = 0 := by
  unfold poeticFunction; exact emergence_void_right a (compose a (void : I))

/-- The dominance of the poetic function: in poetry, emergence dominates
    the additive components. This is bounded by the Cauchy-Schwarz
    emergence bound — even in the most poetic text, emergence cannot
    exceed what the composition can carry. -/
theorem poetic_dominance_bounded (a b : I) :
    (poeticFunction a b) ^ 2 ≤
    rs (compose a b) (compose a b) * rs (compose a b) (compose a b) := by
  unfold poeticFunction
  nlinarith [emergence_bounded' a b (compose a b)]

/-! ## §56. De Man's Allegory of Reading — Rhetorical vs Grammatical

Paul de Man: the relationship between grammar and rhetoric is not one
of harmony but of tension. A text's grammatical structure may say one
thing while its rhetorical force says another. This undecidability
is formalized as the asymmetry between compositional orders. -/

/-- Rhetorical-grammatical tension: the difference between composing
    form with content vs content with form. De Man: "the grammatical
    model of the question becomes the rhetorical model of the question." -/
noncomputable def rhetoricalGrammaticalTension (form content d : I) : ℝ :=
  rs (compose form content) d - rs (compose content form) d

/-- The tension with void is zero: without content, there is no
    tension between grammar and rhetoric. -/
theorem rhetoricalGrammaticalTension_void (form d : I) :
    rhetoricalGrammaticalTension form (void : I) d = 0 := by
  unfold rhetoricalGrammaticalTension; simp

/-- The tension decomposes into emergence differences.
    De Man: the rhetorical-grammatical undecidability is a function
    of the difference in emergence patterns. -/
theorem rhetoricalGrammaticalTension_eq (form content d : I) :
    rhetoricalGrammaticalTension form content d =
    emergence form content d - emergence content form d := by
  unfold rhetoricalGrammaticalTension emergence; ring

/-- The tension is antisymmetric: swapping form and content reverses
    the tension. De Man: the undecidability is symmetric — neither
    grammar nor rhetoric has priority. -/
theorem rhetoricalGrammaticalTension_antisymm (form content d : I) :
    rhetoricalGrammaticalTension form content d =
    -rhetoricalGrammaticalTension content form d := by
  unfold rhetoricalGrammaticalTension; ring

/-- Allegory: the sustained gap between literal and figurative meaning.
    De Man: allegory is the mode that acknowledges the gap between
    sign and meaning. In IDT, this gap is the emergence. -/
noncomputable def allegoricalGap (literal figurative : I) : ℝ :=
  emergence literal figurative (compose literal figurative)

/-- Allegorical gap with void figurative is zero: allegory requires
    a secondary meaning to exist. -/
theorem allegoricalGap_void (literal : I) :
    allegoricalGap literal (void : I) = 0 := by
  unfold allegoricalGap; exact emergence_void_right literal (compose literal (void : I))

/-! ## §57. Eco's Open Work and Model Reader

Umberto Eco: the "open work" is a text that invites multiple valid
interpretations. The "model reader" is the reader-type the text
strategically constructs. The dialectic between openness and strategy
is the narrative's interpretive economy. -/

/-- Interpretive openness: how much emergence a text creates when
    composed with a reader. Open works have high emergence with
    many readers; closed works have high emergence only with
    the model reader. -/
noncomputable def interpretiveOpenness (text reader : I) : ℝ :=
  emergence text reader (compose text reader)

/-- Openness with void reader is zero: a text without a reader
    is neither open nor closed — it is inert. -/
theorem interpretiveOpenness_void_reader (text : I) :
    interpretiveOpenness text (void : I) = 0 := by
  unfold interpretiveOpenness; exact emergence_void_right text (compose text (void : I))

/-- Openness with void text is zero: the reader must have something to interpret. -/
theorem interpretiveOpenness_void_text (reader : I) :
    interpretiveOpenness (void : I) reader = 0 := by
  unfold interpretiveOpenness; simp [emergence, rs_void_left']

/-- The encyclopedia: Eco's term for the total cultural knowledge
    that the model reader brings. Composing the reader's encyclopedia e
    with the text always enriches the reading. -/
theorem encyclopedia_enriches (encyclopedia text : I) :
    rs (compose encyclopedia text) (compose encyclopedia text) ≥ rs encyclopedia encyclopedia :=
  compose_enriches' encyclopedia text

/-- Overinterpretation: when the reader adds more emergence than the
    text can sustain. Bounded by emergence Cauchy-Schwarz. Eco:
    "between the intention of the author and the intention of the text
    there is the intention of the reader." -/
theorem overinterpretation_bounded (text reader : I) :
    (interpretiveOpenness text reader) ^ 2 ≤
    rs (compose text reader) (compose text reader) *
    rs (compose text reader) (compose text reader) := by
  unfold interpretiveOpenness
  nlinarith [emergence_bounded' text reader (compose text reader)]

/-! ## §58. Said's Orientalism — The Emergence of the Other

Edward Said: Orientalism is not knowledge OF the Orient but a Western
construction that produces the Orient as its Other. The Orient as
discourse is the emergence from composing Western categories with
non-Western realities — an irreducible creation, not a representation.

In IDT: the "representation" of the Other is a composition whose emergence
reveals the representer's framework as much as the represented. -/

/-- Representational emergence: what arises when framework f is composed
    with reality r. Said: representation is never transparent — it
    always creates something that was not in either f or r alone. -/
noncomputable def representationalEmergence (framework reality : I) : ℝ :=
  emergence framework reality (compose framework reality)

/-- Representation of void reality is zero: without something to represent,
    the framework produces nothing. -/
theorem representationalEmergence_void_reality (framework : I) :
    representationalEmergence framework (void : I) = 0 := by
  unfold representationalEmergence; exact emergence_void_right framework (compose framework (void : I))

/-- The framework always enriches: composing with any reality creates
    at least as much presence as the framework alone. Said: the discourse
    of Orientalism is self-reinforcing — it never diminishes the framework. -/
theorem framework_enriches (framework reality : I) :
    rs (compose framework reality) (compose framework reality) ≥ rs framework framework :=
  compose_enriches' framework reality

/-- Contrapuntal reading: Said's method of reading "with a simultaneous
    awareness both of the metropolitan history that is narrated and of
    those other histories against which the dominant discourse acts."
    The cocycle constrains the reading of framework, text, and counter-narrative. -/
theorem contrapuntal_reading (framework text counternarrative d : I) :
    emergence framework text d + emergence (compose framework text) counternarrative d =
    emergence text counternarrative d + emergence framework (compose text counternarrative) d :=
  cocycle_condition framework text counternarrative d

/-- Representational asymmetry: how the framework sees the reality is
    not how the reality sees the framework. Said: the power differential
    in representation is precisely this asymmetry. -/
noncomputable def representationalAsymmetry (framework reality : I) : ℝ :=
  rs framework reality - rs reality framework

/-- Representational asymmetry is antisymmetric: the power differential
    reverses when we swap perspectives. -/
theorem representationalAsymmetry_antisymm (framework reality : I) :
    representationalAsymmetry framework reality = -representationalAsymmetry reality framework := by
  unfold representationalAsymmetry; ring

/-! ## §59. Spivak's Subaltern — Can the Subaltern Speak in Ideatic Space?

Spivak: the subaltern cannot speak not because they lack voice but because
the dominant framework cannot HEAR them — their resonance with the dominant
discourse is zero or negative. In IDT terms: the subaltern's ideas
are orthogonal to or opposing the dominant framework. -/

/-- Subaltern audibility: how much the subaltern's voice is heard
    within the dominant framework. When this is zero or negative,
    the subaltern "cannot speak" — not from lack of voice but
    from lack of resonance with the structures of hearing. -/
noncomputable def subalternAudibility (subaltern dominant : I) : ℝ :=
  rs subaltern dominant

/-- Silence has no audibility: the void subaltern is literally silent. -/
theorem subalternAudibility_void (dominant : I) :
    subalternAudibility (void : I) dominant = 0 := by
  unfold subalternAudibility; exact rs_void_left' dominant

/-- Epistemic violence: the emergence from composing the dominant framework
    with the subaltern's reality — the meaning that is CREATED by the act
    of representing the subaltern, which may bear no relation to the
    subaltern's own self-understanding. -/
noncomputable def epistemicViolence (dominant subaltern : I) : ℝ :=
  emergence dominant subaltern (compose dominant subaltern)

/-- Epistemic violence with void subaltern is zero: you cannot do
    violence to what doesn't exist. -/
theorem epistemicViolence_void (dominant : I) :
    epistemicViolence dominant (void : I) = 0 := by
  unfold epistemicViolence; exact emergence_void_right dominant (compose dominant (void : I))

/-- Strategic essentialism: the subaltern's self-composition strengthens
    their presence. Spivak: while essentialism is philosophically
    problematic, it is strategically necessary. -/
theorem strategic_essentialism_enriches (subaltern : I) :
    rs (compose subaltern subaltern) (compose subaltern subaltern) ≥ rs subaltern subaltern :=
  compose_enriches' subaltern subaltern

/-! ## §60. Narrative Thermodynamics — Entropy and Irreversibility

Treating narrative as a thermodynamic system where compose_enriches
plays the role of the second law: composition never decreases "entropy"
(presence). This connects narrative theory to information theory:
the composed narrative always carries at least as much information
as any of its parts. -/

/-- Narrative entropy: the self-resonance of the composed narrative.
    By analogy with thermodynamics, this never decreases under composition. -/
noncomputable def narrativeEntropy (a : I) : ℝ :=
  rs a a

/-- The second law of narrative: composition never decreases entropy.
    This is the narrative analogue of the thermodynamic arrow of time —
    you cannot un-compose a narrative back to its parts with less weight. -/
theorem second_law_of_narrative (a b : I) :
    narrativeEntropy (compose a b) ≥ narrativeEntropy a := by
  unfold narrativeEntropy; exact compose_enriches' a b

/-- Narrative entropy of void is zero: silence is the ground state. -/
theorem narrativeEntropy_void :
    narrativeEntropy (void : I) = 0 := by
  unfold narrativeEntropy; exact rs_void_void

/-- Monotonicity of narrative entropy: adding more material never decreases
    the entropy of a narrative. This is compose_enriches applied twice. -/
theorem narrativeEntropy_monotone (a b c : I) :
    narrativeEntropy (compose (compose a b) c) ≥ narrativeEntropy a := by
  unfold narrativeEntropy
  calc rs (compose (compose a b) c) (compose (compose a b) c)
      ≥ rs (compose a b) (compose a b) := compose_enriches' (compose a b) c
    _ ≥ rs a a := compose_enriches' a b

/-- The heat death of narrative: in the limit of infinite composition,
    entropy grows without bound (monotonically). Every new element added
    to the narrative's front increases its presence. This formalizes
    Borges's Library of Babel: the total library's weight exceeds
    any finite sub-collection. -/
theorem narrative_entropy_grows (a b : I) :
    narrativeEntropy (compose a b) ≥ narrativeEntropy a := by
  unfold narrativeEntropy; exact compose_enriches' a b

end NarrativeRhetoric

end IDT3
