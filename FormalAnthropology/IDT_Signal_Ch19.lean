import FormalAnthropology.IDT_Foundations

/-!
# Signalling Games in IDT — Chapter 19: Social Choice and Hermeneutic Aggregation

**Anthropological motivation.** When a sermon is preached, each congregant
interprets it through their own background. Jürgen Habermas's theory of
communicative action asks: how do multiple interpretations converge into
shared meaning? This is the hermeneutic aggregation problem.

In IDT, `n` agents with repertoire ideas `[r₁, ..., rₙ]` each interpret
signal `s` as `compose(rᵢ, s)`. The interpretations can then be aggregated
by sequential composition, modeling the process by which a community
distills collective meaning from individual understandings.

This chapter formalizes:

- **interpretations**: each agent's interpretation of a shared signal
- **aggregateCompose**: folding interpretations into collective meaning
- **coherentInterpretation**: when all interpretations pairwise resonate
- Depth bounds on aggregate interpretation
- Void signal produces self-resonant group
- Resonant backgrounds guarantee coherent interpretations

## 18 Theorems, 0 Sorries
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.Signal.Ch19

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- Interpretations: each agent interprets the signal by composing it
    with their own background idea. `reps` is the list of agents' repertoire
    ideas, `s` is the shared signal.

    *Gadamer*: Each interpreter brings their "horizon" (background) to
    the encounter with the text (signal). -/
def interpretations (reps : List I) (s : I) : List I :=
  reps.map (fun r => IdeaticSpace.compose r s)

/-- Aggregate composition: fold all ideas in a list via sequential composition.
    This models the process by which a community arrives at a single shared
    interpretation through successive dialogue.

    *Habermas*: The "ideal speech situation" produces consensus through
    iterative composition of individual perspectives. -/
def aggregateCompose : List I → I
  | [] => IdeaticSpace.void
  | a :: rest => IdeaticSpace.compose a (aggregateCompose rest)

/-- Coherent interpretation: all agents' interpretations pairwise resonate.
    This is the formal condition for "hermeneutic consensus."

    *Habermas*: Communicative rationality requires that all participants'
    interpretations be mutually comprehensible — they must resonate. -/
def coherentInterpretation (reps : List I) (s : I) : Prop :=
  ∀ x ∈ interpretations reps s, ∀ y ∈ interpretations reps s,
    IdeaticSpace.resonates x y

/-! ## §2. Fundamental Aggregation Theorems -/

/-- **Theorem 19.1 (Empty Group Has Void Interpretation).**
    No agents ⟹ no interpretation: the void.

    *Political theory*: An empty polity produces no collective meaning. -/
theorem empty_group_void (s : I) :
    aggregateCompose (interpretations [] s) = IdeaticSpace.void := by
  simp [interpretations, aggregateCompose, List.map]

/-- **Theorem 19.2 (Singleton = Individual Interpretation).**
    One agent's aggregate is just their individual interpretation.

    *Hermeneutics*: A solitary reader's interpretation IS the meaning. -/
theorem singleton_interpretation (r s : I) :
    aggregateCompose (interpretations [r] s) = IdeaticSpace.compose r s := by
  simp [interpretations, aggregateCompose, List.map]

/-- **Theorem 19.3 (Void Signal Preserves Repertoire).**
    When the signal is void, each interpretation equals the original repertoire idea.

    *Gadamer*: When there is no text to interpret, each interpreter is left
    with only their own pre-understanding — their horizon remains unchanged. -/
theorem void_signal_preserves (reps : List I) :
    interpretations reps IdeaticSpace.void = reps := by
  induction reps with
  | nil => simp [interpretations]
  | cons r rest ih =>
    simp [interpretations, List.map, void_right, ih]

/-- **Theorem 19.4 (Void Signal Yields Self-Resonant Group).**
    When the signal is void, every interpretation resonates with itself.

    *Durkheim*: In the absence of ritual content, mechanical solidarity
    (self-resonance) still holds — each individual remains coherent. -/
theorem void_signal_self_resonant (reps : List I) :
    ∀ x ∈ interpretations reps IdeaticSpace.void,
      IdeaticSpace.resonates x x := by
  rw [void_signal_preserves]
  intro x _
  exact resonance_refl x

/-- **Theorem 19.5 (Interpretation Count = Agent Count).**
    The number of interpretations equals the number of interpreters.

    *Methodological*: Every agent produces exactly one interpretation. -/
theorem interpretation_count (reps : List I) (s : I) :
    (interpretations reps s).length = reps.length := by
  simp [interpretations]

/-- **Theorem 19.6 (Aggregate Depth Bound — Singleton).**
    A single agent's aggregate depth ≤ agent depth + signal depth.

    *Hermeneutic bound*: One person's understanding adds at most their
    background depth to the signal's depth. -/
theorem singleton_aggregate_depth (r s : I) :
    IdeaticSpace.depth (aggregateCompose (interpretations [r] s)) ≤
    IdeaticSpace.depth r + IdeaticSpace.depth s := by
  rw [singleton_interpretation]
  exact depth_compose_le r s

/-- **Theorem 19.7 (Empty Interpretation List is Coherent).**
    The empty group trivially achieves consensus.

    *Unanimity without voters*: If no one interprets, there's no disagreement. -/
theorem empty_coherent (s : I) : coherentInterpretation [] s := by
  intro x hx
  simp [interpretations, List.map] at hx

/-- **Theorem 19.8 (Singleton Interpretation is Coherent).**
    A single interpreter always achieves coherence (with themselves).

    *Solipsism*: A lone reader always agrees with their own interpretation. -/
theorem singleton_coherent (r s : I) : coherentInterpretation [r] s := by
  intro x hx y hy
  simp [interpretations, List.map, List.mem_singleton] at hx hy
  rw [hx, hy]
  exact resonance_refl _

/-- **Theorem 19.9 (Aggregating Empty Yields Void).**
    Aggregating no ideas produces void.

    *Habermas*: Without any contributions to the discourse, the outcome is silence. -/
theorem aggregate_nil :
    aggregateCompose ([] : List I) = IdeaticSpace.void := rfl

/-- **Theorem 19.10 (Aggregate Cons Unfolding).**
    Adding an interpretation to the aggregate composes it with the rest.

    *Deliberation*: Each new voice adds their perspective on top of
    the existing consensus. -/
theorem aggregate_cons (a : I) (rest : List I) :
    aggregateCompose (a :: rest) = IdeaticSpace.compose a (aggregateCompose rest) := rfl

/-- **Theorem 19.11 (Void Aggregate Identity).**
    A void idea composed with the aggregate doesn't change it.

    *Silent participant*: A non-contributing member doesn't alter the collective meaning. -/
theorem void_aggregate (rest : List I) :
    aggregateCompose (IdeaticSpace.void :: rest) = aggregateCompose rest := by
  simp [aggregateCompose]

/-- **Theorem 19.12 (Self-Resonance of Aggregate).**
    Every aggregate resonates with itself.

    *Social coherence*: Any completed deliberation, however contentious,
    achieves internal self-consistency as a composite idea. -/
theorem aggregate_self_resonance (interps : List I) :
    IdeaticSpace.resonates (aggregateCompose interps) (aggregateCompose interps) :=
  resonance_refl _

/-- **Theorem 19.13 (Resonant Pair Coherence).**
    Two agents whose backgrounds resonate produce coherent interpretations
    of any signal.

    *Durkheim's conscience collective*: Agents who share deep cultural
    resonance will agree on any new information. -/
theorem resonant_pair_coherent {r₁ r₂ : I}
    (hr : IdeaticSpace.resonates r₁ r₂) (s : I) :
    coherentInterpretation [r₁, r₂] s := by
  intro x hx y hy
  simp [interpretations, List.map, List.mem_cons, List.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact resonance_refl _
  · exact resonance_compose_right hr s
  · exact resonance_symm (resonance_compose_right hr s)
  · exact resonance_refl _

/-- **Theorem 19.14 (Void Repertoire Interpretation).**
    An agent with void background just returns the signal.

    *Tabula rasa*: A mind with no pre-existing ideas interprets
    the signal as the signal itself, without transformation. -/
theorem void_background_interpretation (s : I) :
    interpretations [IdeaticSpace.void] s = [s] := by
  simp [interpretations, List.map]

/-- **Theorem 19.15 (Aggregate of Voids is Void).**
    If every agent has void background, the aggregate interpretation of void is void.

    *Nihilism*: Empty minds interpreting nothing produce nothing. -/
theorem void_aggregate_void (n : ℕ) :
    aggregateCompose (interpretations (List.replicate n (IdeaticSpace.void : I)) IdeaticSpace.void) =
    IdeaticSpace.void := by
  rw [void_signal_preserves]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [List.replicate_succ, aggregateCompose, ih]

/-- **Theorem 19.16 (Depth Sum of Interpretations Bound).**
    Total interpretation depth ≤ total repertoire depth + |reps| × depth(s).

    *Resource theory*: The total hermeneutic effort of a community is bounded
    by their collective background knowledge plus the signal's complexity
    distributed across all members. -/
theorem interpretation_depth_sum_bound (reps : List I) (s : I) :
    depthSum (interpretations reps s) ≤ depthSum reps + reps.length * IdeaticSpace.depth s := by
  induction reps with
  | nil => simp [interpretations, depthSum, List.map]
  | cons r rest ih =>
    simp only [interpretations, List.map]
    rw [depthSum_cons, depthSum_cons]
    have hcomp := depth_compose_le r s
    have hlen : (r :: rest).length = rest.length + 1 := rfl
    rw [hlen]
    have : (rest.length + 1) * IdeaticSpace.depth s =
           rest.length * IdeaticSpace.depth s + IdeaticSpace.depth s := by ring
    rw [this]
    have ih' := ih
    simp only [interpretations] at ih'
    linarith

/-- **Theorem 19.17 (Interpretation Map Preserves Nil).**
    Interpreting with an empty group yields empty interpretations.

    *Vacuous truth*: No agents, no interpretations. -/
theorem interpret_nil (s : I) :
    interpretations ([] : List I) s = [] := by
  simp [interpretations, List.map]

/-- **Theorem 19.18 (Aggregate Singleton Void Signal).**
    A single agent interpreting void = just that agent's idea.

    *Phenomenology*: In the absence of external stimuli, consciousness
    returns to its own content — pure self-reflection. -/
theorem aggregate_singleton_void (r : I) :
    aggregateCompose (interpretations [r] IdeaticSpace.void) = r := by
  rw [void_signal_preserves]
  simp [aggregateCompose]

end IDT.Signal.Ch19
