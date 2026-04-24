import FormalAnthropology.IDT_Signal_Ch01

/-!
# Signalling Games in IDT — Chapter 5: Misinterpretation and Cultural Distance

**Anthropological motivation.** The sender intends the receiver to compose
signal `s` with background `r*` (the "shared understanding"). But the
receiver actually composes with `r_actual` — their real, possibly different,
cultural background. The gap between `compose r* s` and `compose r_actual s`
is the formal measure of *misinterpretation*.

This chapter develops:

- **intendedInterp** vs **actualInterp**: the sender's hope vs reality
- **wellInterpreted**: when actual and intended interpretations resonate
- **iterateInterp**: iterated re-interpretation (echo chambers, rumination)
- **Cultural distance**: when backgrounds diverge, interpretations diverge
- **Telephone depth bound**: iterated interpretation has bounded depth

Connects to: Sapir-Whorf hypothesis (linguistic background shapes
interpretation), Gadamer's hermeneutic circle (understanding requires
pre-understanding), echo chambers (iterated self-interpretation).

## 18 Theorems, 0 Sorries
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.Signal.Ch5

open IDT IdeaticSpace IDT.Signal.Ch1

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. The Interpretation Gap -/

/-- The sender's *intended* interpretation: what they hope the receiver understands.
    The sender assumes the receiver has background `r_intended`. -/
def intendedInterp (r_intended s : I) : I :=
  IdeaticSpace.compose r_intended s

/-- The receiver's *actual* interpretation: what they actually understand,
    given their real background `r_actual`. -/
def actualInterp (r_actual s : I) : I :=
  IdeaticSpace.compose r_actual s

/-- An interpretation is *well-interpreted* if the actual and intended
    interpretations resonate — they may differ, but they evoke each other.
    This is weaker than equality but stronger than "no relation." -/
def wellInterpreted (r_intended r_actual s : I) : Prop :=
  IdeaticSpace.resonates (intendedInterp r_intended s) (actualInterp r_actual s)

/-- **Theorem 5.1 (Resonant Backgrounds Guarantee Well-Interpretation).**
    If the intended and actual backgrounds resonate, interpretation is well-interpreted.

    *Anthropological significance*: Members of the same culture (resonant
    backgrounds) always produce well-interpreted outcomes for any signal.
    This is the formal foundation of cultural understanding: shared background
    schemas guarantee mutual comprehension, even if interpretations aren't
    identical. Gadamer's "fusion of horizons" is guaranteed when horizons
    resonate. -/
theorem resonant_backgrounds_well_interpreted {r_intended r_actual : I} (s : I)
    (h : IdeaticSpace.resonates r_intended r_actual) :
    wellInterpreted r_intended r_actual s :=
  resonance_compose_right h s

/-- **Theorem 5.2 (Self-Interpretation Always Succeeds).**
    If the receiver IS the intended audience, interpretation is always well-interpreted.

    *Anthropological significance*: You always understand yourself. This is
    the formal basis of inner monologue — when sender and receiver share
    exactly the same background, perfect comprehension is tautological.
    Soliloquy is the degenerate case of communication. -/
theorem self_interpretation (r s : I) :
    wellInterpreted r r s :=
  resonance_compose_right (resonance_refl r) s

/-- **Theorem 5.3 (Well-Interpretation is Symmetric).**
    If A well-interprets B's signal, then B well-interprets A's signal.

    *Anthropological significance*: Mutual intelligibility is symmetric.
    If I can understand your ritual, you can understand mine (to the
    same degree of resonance). Cultural exchange is inherently bidirectional.
    This formalises the anthropological observation that first contact
    is always reciprocal. -/
theorem well_interpretation_symm {r₁ r₂ s : I}
    (h : wellInterpreted r₁ r₂ s) :
    wellInterpreted r₂ r₁ s :=
  resonance_symm h

/-! ## §2. The Void Background -/

/-- **Theorem 5.4 (Void Background Transparency).**
    If the intended background is void, the intended interpretation IS the
    signal itself. The gap is entirely on the receiver's side.

    *Anthropological significance*: A sender who assumes zero shared context
    (void background) intends the signal to be received "as is." Any
    deviation from the raw signal is the receiver's cultural contribution.
    This is the formal model of the "objective journalist" fantasy:
    "I just report the facts" assumes void background. -/
theorem void_intended_transparency (s : I) :
    intendedInterp (IdeaticSpace.void : I) s = s :=
  void_left s

/-- **Theorem 5.5 (Void Actual Background).**
    A receiver with void background interprets every signal as itself.

    *Anthropological significance*: The "naive receiver" — someone with
    no cultural preconceptions — takes every signal at face value.
    This is structurally impossible in practice (everyone has SOME
    background), but it defines the theoretical limit of "unmediated
    reception." -/
theorem void_actual_transparency (s : I) :
    actualInterp (IdeaticSpace.void : I) s = s :=
  void_left s

/-- **Theorem 5.6 (Void Background Always Well-Interpreted).**
    If sender and receiver both have void background, interpretation
    always succeeds perfectly (the interpretations are identical).

    *Anthropological significance*: In the (impossible) limit of zero
    culture, there is zero misinterpretation. Misunderstanding is
    entirely a product of cultural difference. -/
theorem void_void_perfect (s : I) :
    wellInterpreted (IdeaticSpace.void : I) (IdeaticSpace.void : I) s :=
  self_interpretation _ s

/-- **Theorem 5.7 (Signal to Self = Self-Resonance).**
    Interpreting with your own background always resonates with itself.

    *Philosophical significance*: The hermeneutic circle: understanding
    always loops back to self-resonance. You cannot escape your own
    interpretive framework — even when you try to "step outside,"
    the result still resonates with your starting point. -/
theorem hermeneutic_circle (r s : I) :
    IdeaticSpace.resonates (actualInterp r s) (actualInterp r s) :=
  resonance_refl _

/-! ## §3. Iterated Re-Interpretation -/

/-- Iterated re-interpretation: the receiver interprets, then re-interprets
    through their own background, n times. Models rumination, echo chambers,
    and iterative cultural processing. -/
def iterateInterp (r s : I) : ℕ → I
  | 0 => s
  | n + 1 => IdeaticSpace.compose r (iterateInterp r s n)

/-- **Theorem 5.8 (Zero Iteration = Raw Signal).**
    Zero iterations of re-interpretation yield the signal unchanged.

    *Anthropological significance*: Before any cultural processing occurs,
    the signal exists in its raw form. The "pre-interpretive" state is
    the signal itself — but in practice, interpretation begins immediately
    upon reception. -/
theorem iterate_zero (r s : I) : iterateInterp r s 0 = s := rfl

/-- **Theorem 5.9 (Single Iteration = Basic Interpretation).**
    One iteration of re-interpretation = basic interpretation.

    *Anthropological significance*: The first pass of cultural processing
    is simply composition — the fundamental interpretive act. All
    subsequent iterations are "reflections on reflections." -/
theorem iterate_one (r s : I) :
    iterateInterp r s 1 = IdeaticSpace.compose r s := rfl

/-- **Theorem 5.10 (Void Iteration Identity).**
    Iterating through a void background any number of times leaves the
    signal unchanged.

    *Anthropological significance*: An "empty mind" processing a signal
    repeatedly never changes it. Without cultural content, there is no
    interpretive drift. Echo chambers require content to echo. -/
theorem void_iterate (s : I) : ∀ (n : ℕ),
    iterateInterp (IdeaticSpace.void : I) s n = s
  | 0 => rfl
  | n + 1 => by
    simp only [iterateInterp]
    rw [void_iterate s n, void_left]

/-- **Theorem 5.11 (Iterated Interpretation Depth Bound).**
    `depth(iterateInterp r s n) ≤ n * depth(r) + depth(s)`.

    *Anthropological significance*: Echo chambers have linearly bounded
    complexity. Even infinite rumination through a fixed cultural lens
    can only add linear depth. This is why obsessive rumination is
    unproductive: each pass through the same background adds at most
    `depth(r)` more complexity, and the total is bounded. -/
theorem iterate_depth_bound (r s : I) : ∀ (n : ℕ),
    IdeaticSpace.depth (iterateInterp r s n) ≤ n * IdeaticSpace.depth r + IdeaticSpace.depth s
  | 0 => by simp [iterateInterp]
  | n + 1 => by
    simp only [iterateInterp]
    have ih := iterate_depth_bound r s n
    have hc := depth_compose_le r (iterateInterp r s n)
    calc IdeaticSpace.depth (IdeaticSpace.compose r (iterateInterp r s n))
        ≤ IdeaticSpace.depth r + IdeaticSpace.depth (iterateInterp r s n) := hc
      _ ≤ IdeaticSpace.depth r + (n * IdeaticSpace.depth r + IdeaticSpace.depth s) := by linarith
      _ = (n + 1) * IdeaticSpace.depth r + IdeaticSpace.depth s := by ring

/-- **Theorem 5.12 (Void Signal Single Iteration).**
    Processing void once through any background yields the background itself.

    *Anthropological significance*: Processing "nothing" through a cultural
    lens yields the lens itself. An empty news feed processed through
    conspiracy-theory schemas yields the conspiracy schema unchanged.
    The signal contributes nothing; the background does all the work. -/
theorem void_signal_iterate_one (r : I) :
    iterateInterp r (IdeaticSpace.void : I) 1 = r := by
  simp only [iterateInterp]
  exact void_right r

/-- Auxiliary: void iteration produces depth bounded by n * depth(r). -/
theorem void_iterate_depth (r : I) : ∀ (n : ℕ),
    IdeaticSpace.depth (iterateInterp r (IdeaticSpace.void : I) n) ≤
    n * IdeaticSpace.depth r
  | 0 => by simp [iterateInterp, depth_void]
  | n + 1 => by
    simp only [iterateInterp]
    have ih := void_iterate_depth r n
    have hc := depth_compose_le r (iterateInterp r IdeaticSpace.void n)
    calc IdeaticSpace.depth (IdeaticSpace.compose r (iterateInterp r IdeaticSpace.void n))
        ≤ IdeaticSpace.depth r + IdeaticSpace.depth (iterateInterp r IdeaticSpace.void n) := hc
      _ ≤ IdeaticSpace.depth r + n * IdeaticSpace.depth r := by linarith
      _ = (n + 1) * IdeaticSpace.depth r := by ring

/-! ## §4. Resonance Under Iteration -/

/-- **Theorem 5.13 (Resonant Iteration Step).**
    If interpretations at step n resonate (across two backgrounds),
    then interpretations at step n+1 also resonate (given resonant backgrounds).

    *Anthropological significance*: Resonant cultural processing preserves
    resonance at every step. If two people from similar cultures start
    with resonant interpretations, they STAY in resonant interpretive
    states no matter how many rounds of re-processing occur. Cultural
    consensus is dynamically stable. -/
theorem resonant_iteration_step {r₁ r₂ : I}
    (hr : IdeaticSpace.resonates r₁ r₂)
    {x₁ x₂ : I} (hx : IdeaticSpace.resonates x₁ x₂) :
    IdeaticSpace.resonates (IdeaticSpace.compose r₁ x₁) (IdeaticSpace.compose r₂ x₂) :=
  IdeaticSpace.resonance_compose r₁ r₂ x₁ x₂ hr hx

/-- **Theorem 5.14 (Full Resonant Iteration).**
    If backgrounds resonate, then ALL iterations resonate.

    *Anthropological significance*: Cultural similarity guarantees
    interpretive similarity at every stage of processing. Anthropologists
    observing two similar cultures can predict that their interpretations
    of the same event will resonate AT EVERY LEVEL of reflection.
    This is why "deep" cultural understanding between allied groups
    is possible — resonance propagates through all layers of interpretation. -/
theorem resonant_iteration {r₁ r₂ : I} (s : I)
    (hr : IdeaticSpace.resonates r₁ r₂) : ∀ (n : ℕ),
    IdeaticSpace.resonates (iterateInterp r₁ s n) (iterateInterp r₂ s n)
  | 0 => resonance_refl s
  | n + 1 => by
    simp only [iterateInterp]
    exact IdeaticSpace.resonance_compose r₁ r₂ _ _ hr (resonant_iteration s hr n)

/-- **Theorem 5.15 (Self-Iteration Self-Resonance).**
    Iterated self-interpretation always produces self-resonant results.

    *Philosophical significance*: Rumination through a single fixed
    background always resonates with itself. The echo chamber's output
    is always "consistent" in the sense of self-resonance — it just may
    not resonate with ANYTHING ELSE. This is the formal trap of
    intellectual isolation. -/
theorem self_iteration_resonance (r s : I) (n : ℕ) :
    IdeaticSpace.resonates (iterateInterp r s n) (iterateInterp r s n) :=
  resonance_refl _

/-! ## §5. Cultural Distance and Interpretation -/

/-- **Theorem 5.16 (Composition Preserves Well-Interpretation).**
    If signal `s₁` is well-interpreted and `s₂` is well-interpreted under
    the same background pair, then the compound signal `compose s₁ s₂` is
    also well-interpreted.

    *Anthropological significance*: If two cultures understand each other's
    simple signals, they understand compound signals too. Mutual intelligibility
    at the atomic level guarantees mutual intelligibility at the molecular level.
    This is why pidgins can bootstrap into creoles: basic mutual comprehension
    compounds into complex mutual comprehension. -/
theorem compound_well_interpreted {r₁ r₂ s₁ s₂ : I}
    (h₁ : wellInterpreted r₁ r₂ s₁)
    (h₂ : wellInterpreted r₁ r₂ s₂) :
    IdeaticSpace.resonates
      (IdeaticSpace.compose (intendedInterp r₁ s₁) (intendedInterp r₁ s₂))
      (IdeaticSpace.compose (actualInterp r₂ s₁) (actualInterp r₂ s₂)) :=
  IdeaticSpace.resonance_compose _ _ _ _ h₁ h₂

/-- **Theorem 5.17 (Interpretation Depth Gap).**
    The depth of the actual interpretation is bounded by
    `depth(r_actual) + depth(s)`, regardless of the intended background.

    *Anthropological significance*: Misinterpretation doesn't create
    unbounded complexity. Even the most "wrong" interpretation is bounded
    by the receiver's actual depth plus the signal's depth. Wildly wrong
    interpretations are not wildly complex — they're just differently
    complex. The "mad interpreter" is still bounded. -/
theorem interpretation_depth_gap (r_actual s : I) :
    IdeaticSpace.depth (actualInterp r_actual s) ≤
    IdeaticSpace.depth r_actual + IdeaticSpace.depth s :=
  depth_compose_le r_actual s

/-- **Theorem 5.18 (Iteration Composition / Ritual Accretion).**
    Processing n+m times = processing m times then n more times.
    `iterateInterp r s (n + m) = iterateInterp r (iterateInterp r s m) n`.

    *Anthropological significance*: A lifetime of cultural processing (n + m
    iterations) decomposes into childhood processing (m iterations) followed
    by adult processing (n iterations). Cultural development is *sequentially
    decomposable*: we can study "what did early formation contribute?" and
    "what did later experience add?" as separable phases. This is the
    formal basis of Bourdieu's distinction between primary and secondary
    habitus formation. -/
theorem iteration_composition (r s : I) (n m : ℕ) :
    iterateInterp r s (n + m) = iterateInterp r (iterateInterp r s m) n := by
  induction n with
  | zero => simp [iterateInterp]
  | succ n ih =>
    have : n + 1 + m = (n + m) + 1 := by omega
    rw [this]
    simp only [iterateInterp]
    rw [ih]

end IDT.Signal.Ch5
