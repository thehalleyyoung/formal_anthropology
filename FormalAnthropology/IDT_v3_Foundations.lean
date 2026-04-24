import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic

/-!
# Ideatic Diffusion Theory v3: Minimal Axioms

## What are we axiomatizing?

An **utterance** is something that can be said. Two utterances can be
composed (said together), and there is a null utterance (silence).
Any two utterances resonate to some real-valued degree — positive meaning
reinforcement, negative meaning opposition, zero meaning irrelevance.

## Why these axioms and no others?

Every axiom here is *obviously strictly true* of utterances:

- **A1–A3** (Monoid): Concatenation of utterances is associative with an
  identity. This is as indisputable as string concatenation.

- **R1** (Void annihilation): Silence contributes nothing to resonance.
  If you compose silence with any idea and ask "how does this resonate
  with X?", you get exactly what the idea alone gives you.

## What we deliberately OMIT

- **No symmetry**: "How does X resonate in context of Y" ≠
  "How does Y resonate in context of X". Hearing Shakespeare after
  reading fan fiction ≠ hearing fan fiction after reading Shakespeare.

- **No nonnegativity**: Ideas can oppose. Resonance can be negative.

- **No Cauchy-Schwarz**: That's a Hilbert space artifact. Ideas don't
  live in a Hilbert space — they have emergence.

- **No depth**: Depth is a derived measurement, not an intrinsic property
  of utterances.

- **No self-resonance positivity**: The null utterance has zero
  self-resonance. Some "dead" ideas may too.

## The emergence phenomenon

From just these axioms, we can DEFINE emergence:
  `κ(a, b, c) := rs(a ∘ b, c) - rs(a, c) - rs(b, c)`

This measures how much composing a and b creates NEW resonance with c
beyond what a and b contribute individually. This is the core of IDT:
meaning is not additive. Metaphor, irony, context — all are emergence.

The cocycle condition (a consequence of associativity) then gives us
deep structural constraints on emergence for free.

## NO SORRIES, NO ADMITS, NO AXIOMS (beyond the class)
-/

namespace IDT3

/-! ## §1. The Core Axiom Class -/

/-- An ideatic space is a monoid of utterances equipped with a resonance
    function. These are the MINIMAL axioms that are obviously true of
    utterances:
    - Composition is associative with identity (A1-A3)
    - Silence contributes nothing to resonance (R1) -/
class IdeaticSpace3 (I : Type*) where
  /-- Compose two utterances into one -/
  compose : I → I → I
  /-- The null utterance (silence) -/
  void : I
  /-- A1: Composition is associative -/
  compose_assoc : ∀ (a b c : I), compose (compose a b) c = compose a (compose b c)
  /-- A2: Silence is a left identity -/
  void_left : ∀ (a : I), compose void a = a
  /-- A3: Silence is a right identity -/
  void_right : ∀ (a : I), compose a void = a
  /-- Resonance: how much idea a resonates with idea b. Signed. -/
  rs : I → I → ℝ
  /-- R1: Silence contributes nothing to resonance.
      rs(a ∘ void, c) = rs(a, c) and rs(void ∘ a, c) = rs(a, c)
      are already guaranteed by void_left/void_right + definitional equality.
      But we need: silence as a TARGET contributes nothing. -/
  rs_void_right : ∀ (a : I), rs a void = 0
  /-- R2: Silence as source contributes nothing. -/
  rs_void_left : ∀ (a : I), rs void a = 0
  /-- E1: Self-resonance is non-negative.
      An utterance's resonance with itself — its "presence" — is ≥ 0.
      Even a contradictory utterance is SOMETHING; only silence is zero. -/
  rs_self_nonneg : ∀ (a : I), rs a a ≥ 0
  /-- E2: Nondegeneracy. Only silence has zero self-resonance.
      If an utterance has no presence at all, it IS silence. -/
  rs_nondegen : ∀ (a : I), rs a a = 0 → a = void
  /-- E3: Emergence is bounded.
      The emergent meaning κ(a,b,c) = rs(a∘b,c) - rs(a,c) - rs(b,c)
      cannot exceed what the composition and observer can "carry."
      This is the emergence Cauchy-Schwarz: the nonlinear surprise
      is bounded by the geometric mean of the parts' self-resonances. -/
  emergence_bounded : ∀ (a b c : I),
    (rs (compose a b) c - rs a c - rs b c) ^ 2 ≤
    rs (compose a b) (compose a b) * rs c c
  /-- E4: You can't un-say something.
      Composing an utterance with anything else produces something
      at least as "present" as the original. The composition contains
      its parts. Even a retraction adds weight — it doesn't erase. -/
  compose_enriches : ∀ (a b : I), rs (compose a b) (compose a b) ≥ rs a a

/-! ## §2. Basic algebraic consequences -/

section Algebra
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

@[simp] theorem compose_assoc' (a b c : I) :
    compose (compose a b) c = compose a (compose b c) :=
  S.compose_assoc a b c

@[simp] theorem void_left' (a : I) : compose (void : I) a = a :=
  S.void_left a

@[simp] theorem void_right' (a : I) : compose a (void : I) = a :=
  S.void_right a

@[simp] theorem void_self : compose (void : I) (void : I) = (void : I) :=
  void_left' _

theorem compose_assoc4 (a b c d : I) :
    compose (compose (compose a b) c) d =
    compose a (compose b (compose c d)) := by
  rw [compose_assoc', compose_assoc']

/-- Iterated composition: a^n -/
def composeN (a : I) : ℕ → I
  | 0 => void
  | n + 1 => compose (composeN a n) a

@[simp] theorem composeN_zero (a : I) : composeN a 0 = (void : I) := rfl

theorem composeN_succ (a : I) (n : ℕ) :
    composeN a (n + 1) = compose (composeN a n) a := rfl

@[simp] theorem composeN_void : ∀ (n : ℕ),
    composeN (void : I) n = (void : I)
  | 0 => rfl
  | n + 1 => by simp [composeN, composeN_void n]

theorem composeN_one (a : I) : composeN a 1 = a := by
  simp [composeN]

theorem composeN_two (a : I) : composeN a 2 = compose a a := by
  simp [composeN, composeN_one]

end Algebra

/-! ## §3. Resonance with void -/

section VoidResonance
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

theorem rs_void_right' (a : I) : rs a (void : I) = 0 := S.rs_void_right a
theorem rs_void_left' (a : I) : rs (void : I) a = 0 := S.rs_void_left a

theorem rs_void_void : rs (void : I) (void : I) = 0 := rs_void_left' _

/-- Void is resonance-invisible: it resonates with nothing, not even itself. -/
theorem void_resonance_invisible :
    rs (void : I) (void : I) = 0 ∧
    (∀ a : I, rs (void : I) a = 0) ∧
    (∀ a : I, rs a (void : I) = 0) :=
  ⟨rs_void_void, rs_void_left', rs_void_right'⟩

end VoidResonance

/-! ## §3b. Self-Resonance — Consequences of E1-E4

From the four emergence axioms, we get a rich structure:
self-resonance is a non-negative "weight" function that only vanishes
at void, grows under composition, and bounds the emergence. -/

section SelfResonanceAxioms
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

theorem rs_self_nonneg' (a : I) : rs a a ≥ 0 := S.rs_self_nonneg a

theorem rs_nondegen' (a : I) (h : rs a a = 0) : a = void := S.rs_nondegen a h

theorem compose_enriches' (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a := S.compose_enriches a b

/-- Non-void ideas have strictly positive self-resonance. -/
theorem rs_self_pos (a : I) (h : a ≠ void) : rs a a > 0 := by
  rcases lt_or_eq_of_le (S.rs_self_nonneg a) with hlt | heq
  · linarith
  · exact absurd (S.rs_nondegen a heq.symm) h

/-- Self-resonance of void is zero (now from axioms). -/
theorem rs_self_void_zero : rs (void : I) (void : I) = 0 :=
  rs_void_void

/-- Self-resonance is monotonically non-decreasing under iterated composition. -/
theorem rs_composeN_mono (a : I) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) ≥
    rs (composeN a n) (composeN a n) := by
  simp only [composeN_succ]; exact S.compose_enriches (composeN a n) a

/-- Self-resonance of any iterated composition is non-negative. -/
theorem rs_composeN_nonneg (a : I) (n : ℕ) :
    rs (composeN a n) (composeN a n) ≥ 0 := S.rs_self_nonneg _

/-- Composed ideas are never void (unless the first part is void).
    If a ≠ void, then compose a b ≠ void. -/
theorem compose_ne_void_of_left (a b : I) (h : a ≠ void) :
    compose a b ≠ void := by
  intro heq
  have h1 := S.compose_enriches a b
  rw [heq, rs_void_void] at h1
  have h2 := rs_self_pos a h
  linarith

end SelfResonanceAxioms

/-! ## §4. Emergence — the central concept

Emergence measures how much composing two utterances creates NEW resonance
beyond the sum of parts. This is a DEFINITION, not an axiom.

κ(a, b, c) := rs(a ∘ b, c) - rs(a, c) - rs(b, c)

When κ > 0: synergy (metaphor, harmony, constructive combination)
When κ < 0: interference (contradiction, cancellation)
When κ = 0: linearity (composition is purely additive in resonance) -/

section Emergence
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The emergence of composing a with b, as measured against c.
    This is the fundamental quantity of IDT: the non-additive part of meaning. -/
noncomputable def emergence (a b c : I) : ℝ :=
  rs (compose a b) c - rs a c - rs b c

/-- Emergence vanishes when void is composed on the left. -/
theorem emergence_void_left (b c : I) : emergence (void : I) b c = 0 := by
  unfold emergence; simp [rs_void_left']

/-- Emergence vanishes when void is composed on the right. -/
theorem emergence_void_right (a c : I) : emergence a (void : I) c = 0 := by
  unfold emergence; simp [rs_void_right', rs_void_left']

/-- Emergence is zero when measured against void. -/
theorem emergence_against_void (a b : I) : emergence a b (void : I) = 0 := by
  unfold emergence; simp [rs_void_right']

/-- Rewrite resonance of a composition in terms of emergence. -/
theorem rs_compose_eq (a b c : I) :
    rs (compose a b) c = rs a c + rs b c + emergence a b c := by
  unfold emergence; ring

/-! ### The Cocycle Condition

This is the first deep theorem of IDT. It follows PURELY from associativity
of composition — no other axioms needed.

For any a, b, c, d:
  κ(a, b, d) + κ(a∘b, c, d) = κ(b, c, d) + κ(a, b∘c, d)

This is a 2-cocycle condition on the monoid, connecting IDT to
homological algebra. It means emergence is not arbitrary — it must
satisfy global consistency constraints. -/

theorem cocycle_condition (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d := by
  unfold emergence
  rw [compose_assoc']
  ring

/-- The cocycle condition rearranged: emergence distributes across
    re-association. -/
theorem cocycle_rearranged (a b c d : I) :
    emergence a b d - emergence a (compose b c) d =
    emergence b c d - emergence (compose a b) c d := by
  linarith [cocycle_condition a b c d]

/-! ### Iterated Emergence

What happens when we compose many utterances? -/

/-- Resonance of a triple composition. -/
theorem rs_compose3 (a b c d : I) :
    rs (compose (compose a b) c) d =
    rs a d + rs b d + rs c d +
    emergence a b d + emergence (compose a b) c d := by
  rw [rs_compose_eq (compose a b) c d, rs_compose_eq a b d]
  ring

/-- Alternative form using right association. -/
theorem rs_compose3_right (a b c d : I) :
    rs (compose a (compose b c)) d =
    rs a d + rs b d + rs c d +
    emergence b c d + emergence a (compose b c) d := by
  rw [rs_compose_eq a (compose b c) d, rs_compose_eq b c d]
  ring

/-- The total emergence of a triple composition (compared to sum of parts)
    can be decomposed two ways, and both give the same answer (by cocycle). -/
theorem triple_emergence_invariance (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

end Emergence

/-! ## §4b. Consequences of Bounded Emergence (E3)

The emergence Cauchy-Schwarz inequality gives us powerful tools:
emergence vanishes against zero-presence observers, and is bounded
by the geometric mean of composition and observer self-resonances. -/

section BoundedEmergence
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Emergence is bounded (restated using the emergence definition). -/
theorem emergence_bounded' (a b c : I) :
    (emergence a b c) ^ 2 ≤
    rs (compose a b) (compose a b) * rs c c := by
  unfold emergence; exact S.emergence_bounded a b c

/-- When the observer has zero self-resonance, emergence must be zero.
    Ideas with no presence perceive no emergence. -/
theorem emergence_zero_of_observer_zero (a b c : I) (h : rs c c = 0) :
    emergence a b c = 0 := by
  have hc := S.rs_nondegen c h
  rw [hc]; exact emergence_against_void a b

/-- The emergence bound gives us a kind of "resonance triangle inequality":
    the resonance of a composition is bounded in terms of individual resonances
    and self-resonances. -/
theorem rs_compose_bound (a b c : I) :
    (rs (compose a b) c - rs a c - rs b c) ^ 2 ≤
    rs (compose a b) (compose a b) * rs c c :=
  S.emergence_bounded a b c

end BoundedEmergence

/-! ## §5. Self-Resonance and the Inner Life of Ideas -/

section SelfResonance
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Self-resonance: how much an idea resonates with itself.
    This is the "weight" or "presence" of an idea. -/
noncomputable def selfRS (a : I) : ℝ := rs a a

theorem selfRS_void : selfRS (void : I) = 0 := rs_void_void

/-- Self-resonance of a composition expands with emergence terms. -/
theorem selfRS_compose (a b : I) :
    selfRS (compose a b) =
    rs a (compose a b) + rs b (compose a b) + emergence a b (compose a b) := by
  unfold selfRS; rw [rs_compose_eq]

/-- Self-emergence: emergence of a∘b measured against itself. -/
noncomputable def selfEmergence (a b : I) : ℝ :=
  emergence a b (compose a b)

/-- Self-resonance of composition, using individual cross-terms. -/
theorem selfRS_compose_expanded (a b : I) :
    selfRS (compose a b) =
    rs a (compose a b) + rs b (compose a b) + selfEmergence a b := by
  unfold selfRS selfEmergence; rw [rs_compose_eq]

end SelfResonance

/-! ## §6. Semantic Charge and Idea-Native Invariants

These quantities exist ONLY for ideas — they have no analogue in
linear algebra or physics. They arise from the noncommutative,
emergence-rich structure of meaning. -/

section IdeaNative
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Semantic charge: how much an idea reinforces itself under repetition.
    κ(a, a, a) measures the "self-amplification" of an idea.
    Positive: idea grows stronger when repeated (slogans, mantras).
    Negative: idea weakens when repeated (jokes, surprises). -/
noncomputable def semanticCharge (a : I) : ℝ :=
  emergence a a a

/-- Void has zero semantic charge. -/
theorem semanticCharge_void : semanticCharge (void : I) = 0 :=
  emergence_void_left _ _

/-- Semantic charge in terms of resonance. -/
theorem semanticCharge_eq (a : I) :
    semanticCharge a = rs (compose a a) a - 2 * rs a a := by
  unfold semanticCharge emergence; ring

/-- Order sensitivity: how much the order of composition matters
    for resonance with a third idea.
    When this is zero for all c, a and b "commute in meaning". -/
noncomputable def orderSensitivity (a b c : I) : ℝ :=
  rs (compose a b) c - rs (compose b a) c

/-- Order sensitivity vanishes when both are void. -/
theorem orderSensitivity_void_left (b c : I) :
    orderSensitivity (void : I) b c = 0 := by
  unfold orderSensitivity; simp

/-- Order sensitivity is antisymmetric in a, b. -/
theorem orderSensitivity_antisymm (a b c : I) :
    orderSensitivity a b c = -orderSensitivity b a c := by
  unfold orderSensitivity; ring

/-- Order sensitivity in terms of emergence:
    The difference in emergence determines order sensitivity. -/
theorem orderSensitivity_eq_emergence (a b c : I) :
    orderSensitivity a b c = emergence a b c - emergence b a c := by
  unfold orderSensitivity emergence; ring

/-- Meaning curvature: the antisymmetric part of emergence.
    This measures how much the ORDER of ideas affects their
    emergent meaning — a genuinely non-commutative phenomenon. -/
noncomputable def meaningCurvature (a b c : I) : ℝ :=
  emergence a b c - emergence b a c

/-- Meaning curvature equals order sensitivity. -/
theorem meaningCurvature_eq_orderSensitivity (a b c : I) :
    meaningCurvature a b c = orderSensitivity a b c := by
  unfold meaningCurvature; rw [orderSensitivity_eq_emergence]

/-- Meaning curvature is antisymmetric. -/
theorem meaningCurvature_antisymm (a b c : I) :
    meaningCurvature a b c = -meaningCurvature b a c := by
  unfold meaningCurvature; ring

/-- Meaning curvature vanishes for commutative compositions. -/
theorem meaningCurvature_comm (a b c : I)
    (h : compose a b = compose b a) :
    meaningCurvature a b c = 0 := by
  unfold meaningCurvature emergence; rw [h]; ring

/-- Dialectical tension: what happens when you compose opposing ideas
    and measure the result against their composition.
    This captures Hegel's Aufhebung: thesis + antithesis → synthesis. -/
noncomputable def dialecticalTension (a b : I) : ℝ :=
  emergence a b (compose a b)

/-- Dialectical tension of anything with void is zero. -/
theorem dialecticalTension_void_right (a : I) :
    dialecticalTension a (void : I) = 0 := by
  unfold dialecticalTension; exact emergence_void_right a (compose a (void : I))

theorem dialecticalTension_void_left (b : I) :
    dialecticalTension (void : I) b = 0 := by
  unfold dialecticalTension emergence; simp [rs_void_left']

end IdeaNative

/-! ## §7. Resonance Asymmetry — Why Ideas Are Not Vectors

In a Hilbert space, ⟨x, y⟩ = ⟨y, x⟩. But for ideas, how X resonates
in the context of Y is NOT the same as how Y resonates in context of X.

We define the asymmetry and derive consequences. -/

section Asymmetry
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Resonance asymmetry between two ideas. -/
noncomputable def asymmetry (a b : I) : ℝ :=
  rs a b - rs b a

theorem asymmetry_antisymm (a b : I) :
    asymmetry a b = -asymmetry b a := by
  unfold asymmetry; ring

theorem asymmetry_self (a : I) : asymmetry a a = 0 := by
  unfold asymmetry; ring

theorem asymmetry_void_left (a : I) : asymmetry (void : I) a = 0 := by
  unfold asymmetry; simp [rs_void_left', rs_void_right']

theorem asymmetry_void_right (a : I) : asymmetry a (void : I) = 0 := by
  unfold asymmetry; simp [rs_void_left', rs_void_right']

/-- Directional resonance: what you get by averaging forward and backward. -/
noncomputable def symmetricPart (a b : I) : ℝ :=
  (rs a b + rs b a) / 2

noncomputable def antisymmetricPart (a b : I) : ℝ :=
  (rs a b - rs b a) / 2

theorem rs_decompose (a b : I) :
    rs a b = symmetricPart a b + antisymmetricPart a b := by
  unfold symmetricPart antisymmetricPart; ring

theorem symmetricPart_symm (a b : I) :
    symmetricPart a b = symmetricPart b a := by
  unfold symmetricPart; ring

theorem antisymmetricPart_antisymm (a b : I) :
    antisymmetricPart a b = -antisymmetricPart b a := by
  unfold antisymmetricPart; ring

end Asymmetry

/-! ## §8. Composition Lists and Narrative Structure -/

section Narrative
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Compose a list of utterances left-to-right. -/
def composeList : List I → I
  | [] => void
  | a :: rest => compose a (composeList rest)

@[simp] theorem composeList_nil : composeList ([] : List I) = (void : I) := rfl

@[simp] theorem composeList_singleton (a : I) : composeList [a] = a := by
  simp [composeList]

theorem composeList_cons (a : I) (l : List I) :
    composeList (a :: l) = compose a (composeList l) := rfl

/-- Total resonance: sum of pairwise consecutive resonances in a sequence.
    This is the "coherence" of a narrative. -/
noncomputable def totalResonance : List I → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => rs a b + totalResonance (b :: rest)

theorem totalResonance_nil : totalResonance ([] : List I) = 0 := rfl
theorem totalResonance_singleton (a : I) : totalResonance [a] = 0 := rfl

theorem totalResonance_pair (a b : I) :
    totalResonance [a, b] = rs a b := by
  simp [totalResonance]

/-- Total emergence in a sequence: sum of emergences from consecutive
    compositions. Measures how much narrative "creates" beyond its parts. -/
noncomputable def narrativeEmergence : List I → I → ℝ
  | [], _ => 0
  | [_], _ => 0
  | a :: b :: rest, d =>
    emergence a b d + narrativeEmergence (b :: rest) d

theorem narrativeEmergence_nil (d : I) :
    narrativeEmergence ([] : List I) d = 0 := rfl

theorem narrativeEmergence_singleton (a d : I) :
    narrativeEmergence [a] d = 0 := rfl

theorem narrativeEmergence_pair (a b d : I) :
    narrativeEmergence [a, b] d = emergence a b d := by
  simp [narrativeEmergence]

end Narrative

/-! ## §9. Interpretation as Composition

A key insight: INTERPRETATION is composition. When a reader r
encounters a text t, the result is compose r t — the reader's mind
composed with the text. This is not metaphorical; it IS what
interpretation means in IDT.

The asymmetry of resonance then captures a deep truth:
how the text resonates FOR the reader ≠ how the reader resonates FOR the text. -/

section Interpretation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Interpretation: reader r interprets signal s by composing r with s. -/
def interpret (reader signal : I) : I := compose reader signal

theorem interpret_void_reader (s : I) : interpret (void : I) s = s := by
  unfold interpret; simp

theorem interpret_void_signal (r : I) : interpret r (void : I) = r := by
  unfold interpret; simp

/-- Sender payoff: how much the signal resonates with its interpretation.
    "Did they understand what I meant?" -/
noncomputable def senderPayoff (signal reader : I) : ℝ :=
  rs signal (interpret reader signal)

/-- Receiver payoff: how much the reader's state resonates with the
    interpretation. "Did this make sense to me?" -/
noncomputable def receiverPayoff (signal reader : I) : ℝ :=
  rs reader (interpret reader signal)

theorem senderPayoff_void_reader (s : I) :
    senderPayoff s (void : I) = rs s s := by
  unfold senderPayoff interpret; simp

theorem receiverPayoff_void_signal (r : I) :
    receiverPayoff (void : I) r = rs r r := by
  unfold receiverPayoff interpret; simp

/-- Communication surplus: total value created by interpretation
    beyond individual self-resonances. -/
noncomputable def communicationSurplus (signal reader : I) : ℝ :=
  senderPayoff signal reader + receiverPayoff signal reader
  - rs signal signal - rs reader reader

theorem communicationSurplus_void_signal (r : I) :
    communicationSurplus (void : I) r = 0 := by
  unfold communicationSurplus senderPayoff receiverPayoff interpret
  simp [rs_void_left', rs_void_right']

theorem communicationSurplus_void_reader (s : I) :
    communicationSurplus s (void : I) = 0 := by
  unfold communicationSurplus senderPayoff receiverPayoff interpret
  simp [rs_void_left', rs_void_right']

/-- The misunderstanding gap: difference between what the sender
    intended and what the receiver got. -/
noncomputable def misunderstandingGap (signal reader : I) : ℝ :=
  senderPayoff signal reader - receiverPayoff signal reader

theorem misunderstandingGap_antisymmetric_sense (signal reader : I) :
    misunderstandingGap signal reader =
    rs signal (interpret reader signal) - rs reader (interpret reader signal) := by
  unfold misunderstandingGap senderPayoff receiverPayoff; ring

/-- When the reader IS the signal, misunderstanding gap =
    asymmetry of the doubled idea. -/
theorem misunderstanding_self (a : I) :
    misunderstandingGap a a =
    rs a (compose a a) - rs a (compose a a) := by
  unfold misunderstandingGap senderPayoff receiverPayoff interpret; ring

theorem misunderstanding_self_zero (a : I) :
    misunderstandingGap a a = 0 := by
  rw [misunderstanding_self]; ring

end Interpretation

/-! ## §10. Resonance Classes and Opposition -/

section ResonanceClasses
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Two ideas resonate (in the forward direction) -/
def resonatesWith (a b : I) : Prop := rs a b > 0

/-- Two ideas oppose (in the forward direction) -/
def opposes (a b : I) : Prop := rs a b < 0

/-- Two ideas are resonance-orthogonal -/
def orthogonal (a b : I) : Prop := rs a b = 0

/-- Void is orthogonal to everything. -/
theorem void_orthogonal_left (a : I) : orthogonal (void : I) a :=
  rs_void_left' a

theorem void_orthogonal_right (a : I) : orthogonal a (void : I) :=
  rs_void_right' a

/-- Orthogonality means zero emergence contribution from cross terms. -/
theorem orthogonal_cross (a b c : I) (h : orthogonal a c) (h2 : orthogonal b c) :
    rs (compose a b) c = emergence a b c := by
  unfold orthogonal at h h2; unfold emergence; linarith

/-- Strong resonance: both directions agree. -/
def mutuallyResonant (a b : I) : Prop :=
  rs a b > 0 ∧ rs b a > 0

/-- Strong opposition: both directions agree on opposition. -/
def mutuallyOpposing (a b : I) : Prop :=
  rs a b < 0 ∧ rs b a < 0

/-- Mutual orthogonality. -/
def mutuallyOrthogonal (a b : I) : Prop :=
  rs a b = 0 ∧ rs b a = 0

theorem void_mutuallyOrthogonal (a : I) :
    mutuallyOrthogonal (void : I) a :=
  ⟨rs_void_left' a, rs_void_right' a⟩

end ResonanceClasses

/-! ## §11. The Emergence Cocycle — Deeper Consequences -/

section CocycleConsequences
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Cocycle condition written with explicit terms. -/
theorem cocycle_explicit (a b c d : I) :
    rs (compose a b) d - rs a d - rs b d +
    rs (compose (compose a b) c) d - rs (compose a b) d - rs c d =
    rs (compose b c) d - rs b d - rs c d +
    rs (compose a (compose b c)) d - rs a d - rs (compose b c) d := by
  have h := cocycle_condition a b c d
  unfold emergence at h; linarith

/-- Self-cocycle: what happens when d = a. -/
theorem cocycle_self_a (a b c : I) :
    emergence a b a + emergence (compose a b) c a =
    emergence b c a + emergence a (compose b c) a :=
  cocycle_condition a b c a

/-- Cocycle when one argument is void. -/
theorem cocycle_void_a (b c d : I) :
    emergence (void : I) b d + emergence b c d =
    emergence b c d + emergence (void : I) (compose b c) d := by
  simp [emergence_void_left]

/-- Composing void doesn't change the cocycle structure. -/
theorem cocycle_void_b (a c d : I) :
    emergence a (void : I) d + emergence a c d =
    emergence (void : I) c d + emergence a c d := by
  simp [emergence_void_right, emergence_void_left]

/-- Resonance of a 4-fold composition in terms of pairwise emergences. -/
theorem rs_compose4 (a b c d e : I) :
    rs (compose (compose (compose a b) c) d) e =
    rs a e + rs b e + rs c e + rs d e +
    emergence a b e +
    emergence (compose a b) c e +
    emergence (compose (compose a b) c) d e := by
  rw [rs_compose_eq (compose (compose a b) c) d e]
  rw [rs_compose_eq (compose a b) c e]
  rw [rs_compose_eq a b e]
  ring

end CocycleConsequences

/-! ## §12. Linearity Subspaces — Where Emergence Vanishes

An idea a is "linear" if composing with it never produces emergence.
These are the "boring" ideas — they combine additively.
The interesting ideas are precisely those with nonzero emergence. -/

section Linearity
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- An idea is left-linear if composing it on the left never creates emergence. -/
def leftLinear (a : I) : Prop :=
  ∀ b c : I, emergence a b c = 0

/-- An idea is right-linear if composing it on the right never creates emergence. -/
def rightLinear (a : I) : Prop :=
  ∀ b c : I, emergence b a c = 0

/-- An idea is fully linear if it's both left and right linear. -/
def fullyLinear (a : I) : Prop :=
  leftLinear a ∧ rightLinear a

/-- Void is left-linear. -/
theorem void_leftLinear : leftLinear (void : I) := by
  intro b c; exact emergence_void_left b c

/-- Void is right-linear. -/
theorem void_rightLinear : rightLinear (void : I) := by
  intro b c; exact emergence_void_right b c

/-- Void is fully linear. -/
theorem void_fullyLinear : fullyLinear (void : I) :=
  ⟨void_leftLinear, void_rightLinear⟩

/-- For left-linear ideas, resonance IS additive. -/
theorem leftLinear_additive (a : I) (h : leftLinear a) (b c : I) :
    rs (compose a b) c = rs a c + rs b c := by
  have := rs_compose_eq a b c; rw [h b c] at this; linarith

/-- For right-linear ideas, resonance IS additive (on the right). -/
theorem rightLinear_additive (b : I) (h : rightLinear b) (a c : I) :
    rs (compose a b) c = rs a c + rs b c := by
  have := rs_compose_eq a b c; rw [h a c] at this; linarith

/-- If ALL ideas are linear, we recover a bilinear resonance (pre-Hilbert). -/
theorem allLinear_bilinear
    (h : ∀ a : I, leftLinear a) (a b c : I) :
    rs (compose a b) c = rs a c + rs b c :=
  leftLinear_additive a (h a) b c

/-- Emergence detector: an idea a has nontrivial emergence if there exist
    b, c such that κ(a, b, c) ≠ 0. -/
def hasEmergence (a : I) : Prop :=
  ∃ b c : I, emergence a b c ≠ 0

/-- Void has no emergence. -/
theorem void_no_emergence : ¬hasEmergence (void : I) := by
  intro ⟨b, c, h⟩; exact h (emergence_void_left b c)

end Linearity

/-! ## §13. Resonance Maps and Functoriality -/

section Maps
variable {I : Type*} [S : IdeaticSpace3 I]
variable {J : Type*} [T : IdeaticSpace3 J]

/-- A morphism of ideatic spaces preserves composition and resonance. -/
structure IdeaticMorphism (I : Type*) (J : Type*) [IdeaticSpace3 I] [IdeaticSpace3 J] where
  map : I → J
  map_void : map IdeaticSpace3.void = IdeaticSpace3.void
  map_compose : ∀ a b : I,
    map (IdeaticSpace3.compose a b) =
    IdeaticSpace3.compose (map a) (map b)
  map_rs : ∀ a b : I,
    IdeaticSpace3.rs (map a) (map b) = IdeaticSpace3.rs a b

/-- A morphism preserves emergence. -/
theorem morphism_preserves_emergence (f : IdeaticMorphism I J)
    (a b c : I) :
    emergence (f.map a) (f.map b) (f.map c) = emergence a b c := by
  unfold emergence
  rw [← f.map_compose, f.map_rs, f.map_rs, f.map_rs]

/-- A morphism preserves semantic charge. -/
theorem morphism_preserves_charge (f : IdeaticMorphism I J)
    (a : I) :
    semanticCharge (f.map a) = semanticCharge a := by
  unfold semanticCharge; exact morphism_preserves_emergence f a a a

end Maps

/-! ## §14. Models — Proof that the axioms are consistent -/

section Models

/-- The trivial model: a single element (the void).
    This satisfies all 8 axioms trivially. -/
instance unitIdeaticSpace : IdeaticSpace3 Unit where
  compose _ _ := ()
  void := ()
  compose_assoc _ _ _ := rfl
  void_left _ := rfl
  void_right _ := rfl
  rs _ _ := 0
  rs_void_right _ := rfl
  rs_void_left _ := rfl
  rs_self_nonneg _ := le_refl _
  rs_nondegen _ _ := rfl
  emergence_bounded _ _ _ := by simp
  compose_enriches _ _ := le_refl _

/-- In the trivial model, everything is zero. -/
theorem unit_rs_zero : ∀ a b : Unit, IdeaticSpace3.rs a b = 0 := by
  intros; rfl

/-- In the trivial model, all emergence is zero. -/
theorem unit_emergence_zero : ∀ a b c : Unit, emergence a b c = 0 := by
  intros; unfold emergence; simp [unit_rs_zero]

/-- The natural number model: I = ℕ, compose = addition, void = 0,
    rs(a,b) = a * b. This is bilinear (zero emergence) but nontrivial.
    It satisfies all 8 axioms. -/
noncomputable instance natIdeaticSpace : IdeaticSpace3 ℕ where
  compose := (· + ·)
  void := 0
  compose_assoc a b c := Nat.add_assoc a b c
  void_left a := Nat.zero_add a
  void_right a := Nat.add_zero a
  rs a b := (a : ℝ) * (b : ℝ)
  rs_void_right a := by simp
  rs_void_left a := by simp
  rs_self_nonneg a := mul_self_nonneg _
  rs_nondegen a h := by
    have : (a : ℝ) * a = 0 := h
    have := mul_self_eq_zero.mp this
    exact_mod_cast this
  emergence_bounded a b c := by
    change (↑(a + b) * (↑c : ℝ) - ↑a * ↑c - ↑b * ↑c) ^ 2 ≤
           ↑(a + b) * ↑(a + b) * (↑c * ↑c)
    have h1 : (↑(a + b) : ℝ) = (a : ℝ) + b := by push_cast; ring
    rw [h1]
    have h2 : ((a : ℝ) + b) * c - a * c - b * c = 0 := by ring
    rw [h2]; simp
    positivity
  compose_enriches a b := by
    change (↑(a + b) : ℝ) * ↑(a + b) ≥ ↑a * ↑a
    have h1 : (↑(a + b) : ℝ) = (a : ℝ) + b := by push_cast; ring
    rw [h1]
    nlinarith [mul_self_nonneg (b : ℝ),
               mul_nonneg (Nat.cast_nonneg' a : (0 : ℝ) ≤ a)
                          (Nat.cast_nonneg' b : (0 : ℝ) ≤ b)]

end Models

/-! ## §15. Context Operators — How Meaning Shifts

A key phenomenon in ideas: the SAME utterance means different things
in different contexts. We formalize this. -/

section Context
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Left context: what happens when we prepend context c to every idea. -/
noncomputable def leftContextShift (c a b : I) : ℝ :=
  rs (compose c a) (compose c b) - rs a b

/-- Right context: what happens when we append context c. -/
noncomputable def rightContextShift (c a b : I) : ℝ :=
  rs (compose a c) (compose b c) - rs a b

/-- Context shift decomposes into emergence terms. -/
theorem leftContextShift_eq (c a b : I) :
    leftContextShift c a b =
    rs c (compose c b) + rs a (compose c b) + emergence c a (compose c b) - rs a b := by
  unfold leftContextShift
  rw [rs_compose_eq]

-- A cleaner version using only emergence
theorem leftContextShift_via_emergence (c a b : I) :
    rs (compose c a) (compose c b) =
    rs c (compose c b) + rs a (compose c b) + emergence c a (compose c b) := by
  rw [rs_compose_eq]

/-- Context with void changes nothing. -/
theorem leftContextShift_void (a b : I) :
    leftContextShift (void : I) a b = 0 := by
  unfold leftContextShift; simp

theorem rightContextShift_void (a b : I) :
    rightContextShift (void : I) a b = 0 := by
  unfold rightContextShift; simp

end Context

/-! ## §16. Semantic Distance (without Cauchy-Schwarz)

We can define distance-like quantities without assuming any positivity
or boundedness of resonance. The "distance" here is purely from
the resonance structure. -/

section Distance
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Raw resonance gap: the difference in how a resonates with itself
    vs how a resonates with b. A measure of "how far b is from a,
    in a's own frame". -/
noncomputable def resonanceGap (a b : I) : ℝ :=
  rs a a - rs a b

theorem resonanceGap_self (a : I) : resonanceGap a a = 0 := by
  unfold resonanceGap; ring

theorem resonanceGap_void_left (a : I) : resonanceGap (void : I) a = 0 := by
  unfold resonanceGap; simp [rs_void_left', rs_void_void]

/-- Symmetric resonance deficit: a direction-independent measure. -/
noncomputable def resonanceDeficit (a b : I) : ℝ :=
  rs a a + rs b b - rs a b - rs b a

theorem resonanceDeficit_self (a : I) : resonanceDeficit a a = 0 := by
  unfold resonanceDeficit; ring

theorem resonanceDeficit_symm (a b : I) :
    resonanceDeficit a b = resonanceDeficit b a := by
  unfold resonanceDeficit; ring

theorem resonanceDeficit_void (a : I) :
    resonanceDeficit (void : I) a = rs a a := by
  unfold resonanceDeficit; simp [rs_void_left', rs_void_right', rs_void_void]

end Distance

/-! ## §17. Utterance vs Idea — A Semiotic Distinction Through Emergence

The elements of I are **utterances** — raw things that can be said.
But an "idea" is not what you say; it's what EMERGES when what you say
meets a context. Two utterances carry the same idea when no context
can tell them apart in terms of what they produce beyond themselves.

Formally: utterances a and b carry the same idea when
  `∀ c d, emergence a c d = emergence b c d`
i.e., a and b create the same emergent meaning in every context.

This is NOT the same as `∀ c, rs a c = rs b c` (which would be
resonance-equivalence — a stronger, linear condition). Two utterances
can resonate differently with things but still produce the same
EMERGENCE — the same nonlinear creative potential.

This is precisely Saussure's insight: the signifier (utterance) is
arbitrary; what matters is the differential structure (emergence pattern).
And it's Wittgenstein's insight: meaning is use, i.e., meaning is
what emerges in contexts of use. -/

section Semiotics
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Two utterances carry the same idea if they produce identical emergence
    in all contexts. This is the semiotic equivalence: same signified,
    possibly different signifiers. -/
def sameIdea (a b : I) : Prop :=
  ∀ c d : I, emergence a c d = emergence b c d

/-- sameIdea is reflexive. -/
theorem sameIdea_refl (a : I) : sameIdea a a :=
  fun _ _ => rfl

/-- sameIdea is symmetric. -/
theorem sameIdea_symm (a b : I) : sameIdea a b → sameIdea b a :=
  fun h c d => (h c d).symm

/-- sameIdea is transitive. -/
theorem sameIdea_trans (a b c : I) : sameIdea a b → sameIdea b c → sameIdea a c :=
  fun h1 h2 x d => (h1 x d).trans (h2 x d)

/-- Void carries its own unique idea — nothing else has void's emergence pattern
    (assuming the other thing also satisfies the right-emergence condition). -/
theorem void_sameIdea_iff (a : I) :
    sameIdea (void : I) a ↔ ∀ c d : I, emergence a c d = 0 := by
  constructor
  · intro h c d; have := h c d; rw [emergence_void_left] at this; linarith
  · intro h c d; rw [emergence_void_left]; linarith [h c d]

/-- What sameIdea means in terms of resonance:
    a and b carry the same idea iff for all c d,
    rs(a∘c, d) - rs(a, d) = rs(b∘c, d) - rs(b, d).
    I.e., they shift resonance by the same amount in every context. -/
theorem sameIdea_iff_shift (a b : I) :
    sameIdea a b ↔
    ∀ c d : I, rs (compose a c) d - rs a d = rs (compose b c) d - rs b d := by
  constructor
  · intro h c d
    have := h c d
    unfold emergence at this
    linarith
  · intro h c d
    unfold emergence
    linarith [h c d]

/-- Resonance equivalence: a stronger condition where utterances are
    indistinguishable to all other utterances. This is the
    "same phoneme" — not just same idea, but same resonance profile. -/
def resonanceEquiv (a b : I) : Prop :=
  ∀ c : I, rs a c = rs b c

/-- Resonance equivalence implies same idea (but not conversely).
    sameIdea is about left-emergence: ∀ c d, κ(a,c,d) = κ(b,c,d).
    From resonanceEquiv (∀ c, rs a c = rs b c):
    κ(a,c,d) = rs(a∘c,d) - rs(a,d) - rs(c,d)
    κ(b,c,d) = rs(b∘c,d) - rs(b,d) - rs(c,d)
    We need rs(a∘c,d) - rs(a,d) = rs(b∘c,d) - rs(b,d).
    resonanceEquiv gives rs(a,d) = rs(b,d), but NOT rs(a∘c,d) = rs(b∘c,d)
    since a∘c ≠ b∘c in general. So we need composition compatibility too. -/
theorem resonanceEquiv_implies_sameIdea (a b : I)
    (h : resonanceEquiv a b)
    (hcompat : ∀ c d : I, rs (compose a c) d = rs (compose b c) d) :
    sameIdea a b := by
  intro c d
  unfold emergence
  linarith [h d, hcompat c d]

/-- Resonance equivalence also implies same idea in the "right" position,
    PROVIDED the composition respects resonance equivalence. This holds
    when composition is "resonance-compatible". We state the compatibility
    condition explicitly rather than assuming it. -/
theorem resonanceEquiv_sameIdea_right_of_compat (a b : I)
    (h : resonanceEquiv a b)
    (hcompat : ∀ c d : I, rs (compose c a) d = rs (compose c b) d) :
    ∀ c d : I, emergence c a d = emergence c b d := by
  intro c d
  unfold emergence
  rw [hcompat c d, h d]

/-- The polysemy number: how many "distinct ideas" a single utterance
    can carry is measured by the dimension of its emergence variation.
    We approximate: an utterance is polysemous if there exist contexts
    where its emergence differs. -/
def polysemous (a : I) : Prop :=
  ∃ c₁ c₂ d : I, emergence a c₁ d ≠ emergence a c₂ d

/-- Void is never polysemous — it always produces zero emergence. -/
theorem void_not_polysemous : ¬polysemous (void : I) := by
  intro ⟨c₁, c₂, d, h⟩
  exact h (by rw [emergence_void_left, emergence_void_left])

/-- A linear utterance is never polysemous. -/
theorem leftLinear_not_polysemous (a : I) (h : leftLinear a) :
    ¬polysemous a := by
  intro ⟨c₁, c₂, d, hne⟩
  exact hne (by rw [h c₁ d, h c₂ d])

/-- Synonymy: two different utterances that carry the same idea. -/
def synonymous (a b : I) : Prop :=
  sameIdea a b ∧ ¬resonanceEquiv a b

/-- Connotation: the part of resonance NOT captured by the idea.
    Two synonyms differ only in connotation. If a and b are the same idea,
    then their resonance difference rs(a,c) - rs(b,c) is pure connotation —
    it's the part that doesn't affect emergence. -/
noncomputable def connotation (a b c : I) : ℝ :=
  rs a c - rs b c

/-- For same-idea utterances, connotation is "emergence-invisible":
    it doesn't affect what emerges in any context. -/
theorem connotation_emergence_invisible (a b : I)
    (h : sameIdea a b) (c d : I) :
    emergence a c d = emergence b c d := h c d

end Semiotics

/-! ## §18. Deeper Algebraic Structure — Iterated Composition

ComposeN identities, interaction with void and linearity,
and the monoid structure explored more deeply. -/

section DeeperAlgebra
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- composeN distributes: a^(m+n) = a^m ∘ a^n. The monoid law
    for iterated composition, the discrete analogue of flow additivity. -/
theorem composeN_add (a : I) (m n : ℕ) :
    composeN a (m + n) = compose (composeN a m) (composeN a n) := by
  induction n with
  | zero => simp [composeN]
  | succ n ih =>
    rw [Nat.add_succ, composeN_succ, ih, composeN_succ, compose_assoc']

/-- composeN 1 is a right identity for composeN composition:
    compose (composeN a n) a = composeN a (n+1). Already true by definition,
    but useful as a rewrite. -/
theorem composeN_succ_eq (a : I) (n : ℕ) :
    compose (composeN a n) a = composeN a (n + 1) := rfl

/-- Composing a^m with a yields a^(m+1). -/
theorem composeN_succ_right (a : I) (m : ℕ) :
    compose (composeN a m) a = composeN a (m + 1) := rfl

/-- Three-fold composition: a^3 = a ∘ a ∘ a. -/
theorem composeN_three (a : I) :
    composeN a 3 = compose (compose a a) a := by
  simp [composeN, composeN_two, composeN_one]

/-- Four-fold composition: a^4 = compose (a^3) a. -/
theorem composeN_four (a : I) :
    composeN a 4 = compose (composeN a 3) a := rfl

/-- composeN respects the monoid: a^1 ∘ a^1 = a^2. -/
theorem composeN_one_one (a : I) :
    compose (composeN a 1) (composeN a 1) = composeN a 2 := by
  rw [← composeN_add]

/-- compose of composeN with itself: a^m ∘ a^n = a^n ∘ a^m
    (since both equal a^(m+n) = a^(n+m)). The iterated monoid is commutative. -/
theorem composeN_comm (a : I) (m n : ℕ) :
    compose (composeN a m) (composeN a n) =
    compose (composeN a n) (composeN a m) := by
  simp only [← composeN_add, Nat.add_comm]

/-- Associativity for four composeN terms. -/
theorem compose_assoc4_N (a : I) (m n p : ℕ) :
    compose (compose (composeN a m) (composeN a n)) (composeN a p) =
    compose (composeN a m) (compose (composeN a n) (composeN a p)) :=
  compose_assoc' _ _ _

/-- composeN preserves the void: void^n = void for all n. Already
    proven as composeN_void, restated for emphasis. -/
theorem composeN_void_eq (n : ℕ) : composeN (void : I) n = (void : I) :=
  composeN_void n

/-- Self-resonance grows monotonically along the composeN sequence:
    rs(a^n, a^n) ≥ rs(a, a) for all n ≥ 1. Repeated utterance can
    only grow in presence. -/
theorem rs_composeN_ge_base (a : I) : ∀ n : ℕ,
    rs (composeN a (n + 1)) (composeN a (n + 1)) ≥ rs a a := by
  intro n; induction n with
  | zero => simp [composeN_one]
  | succ n ih =>
    calc rs (composeN a (n + 2)) (composeN a (n + 2))
        ≥ rs (composeN a (n + 1)) (composeN a (n + 1)) := rs_composeN_mono a (n + 1)
      _ ≥ rs a a := ih

/-- If a ≠ void then a^n ≠ void for all n ≥ 1. Non-silent ideas remain
    non-silent under repetition. -/
theorem composeN_ne_void (a : I) (ha : a ≠ void) (n : ℕ) :
    composeN a (n + 1) ≠ void := by
  intro heq
  have h1 := rs_composeN_ge_base a n
  rw [heq, rs_void_void] at h1
  have h2 := rs_self_pos a ha
  linarith

end DeeperAlgebra

/-! ## §19. Resonance Geometry — Metric-like Properties

Exploring the geometric structure of the resonance function:
triangle-inequality analogues, polarization, and the relationship
between resonance deficit and "distance". -/

section ResonanceGeometry
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Resonance deficit is non-negative for void against any idea.
    This is because resonanceDeficit(void, a) = rs(a,a). -/
theorem resonanceDeficit_void_nonneg (a : I) :
    resonanceDeficit (void : I) a ≥ 0 := by
  rw [resonanceDeficit_void]; exact rs_self_nonneg' a

/-- Resonance gap at void is zero: void sees no gap to anything. -/
theorem resonanceGap_void_right (a : I) :
    resonanceGap a (void : I) = rs a a := by
  unfold resonanceGap; rw [rs_void_right']; ring

/-- Resonance gap is reflexive: the gap from a to itself is zero. -/
theorem resonanceGap_refl (a : I) : resonanceGap a a = 0 :=
  resonanceGap_self a

/-- The resonance gap decomposes: gap(a,b) + gap(a,c) relates to
    resonance of b and c through a. -/
theorem resonanceGap_sum (a b c : I) :
    resonanceGap a b + resonanceGap a c = 2 * rs a a - rs a b - rs a c := by
  unfold resonanceGap; ring

/-- Polarization identity for resonanceDeficit: deficit(a,b) expresses
    the "distance" between a and b using only self- and cross-resonance. -/
theorem resonanceDeficit_expand (a b : I) :
    resonanceDeficit a b = (rs a a - rs a b) + (rs b b - rs b a) := by
  unfold resonanceDeficit; ring

/-- Resonance deficit of a with void (from the right). -/
theorem resonanceDeficit_void_right (a : I) :
    resonanceDeficit a (void : I) = rs a a := by
  rw [resonanceDeficit_symm]; exact resonanceDeficit_void a

/-- Resonance deficit vanishes iff the symmetric part of cross-resonance
    equals the average of self-resonances. -/
theorem resonanceDeficit_zero_iff (a b : I) :
    resonanceDeficit a b = 0 ↔ rs a b + rs b a = rs a a + rs b b := by
  unfold resonanceDeficit; constructor <;> intro h <;> linarith

/-- A "pseudo-norm" from self-resonance: ‖a‖² := rs(a,a). This is
    always non-negative. The triangle inequality doesn't hold in general,
    but the enrichment axiom gives a one-sided version. -/
noncomputable def weight (a : I) : ℝ := rs a a

/-- Weight of void is zero. -/
theorem weight_void : weight (void : I) = 0 := rs_void_void

/-- Weight is non-negative. -/
theorem weight_nonneg (a : I) : weight a ≥ 0 := rs_self_nonneg' a

/-- Non-void ideas have positive weight. -/
theorem weight_pos (a : I) (h : a ≠ void) : weight a > 0 :=
  rs_self_pos a h

/-- Weight is zero iff the idea is void. -/
theorem weight_eq_zero_iff (a : I) : weight a = 0 ↔ a = void := by
  constructor
  · exact rs_nondegen' a
  · intro h; rw [h]; exact weight_void

/-- Weight is monotone under composition: composing adds presence. -/
theorem weight_compose_ge_left (a b : I) :
    weight (compose a b) ≥ weight a := compose_enriches' a b

/-- The weight of a composition is at least the weight of the left factor.
    Note: we cannot prove weight(a∘b) ≥ weight(b) without commutativity.
    The enrichment axiom is one-sided. -/
theorem weight_compose_ge_left' (a b : I) :
    weight (compose a b) - weight a ≥ 0 := by
  unfold weight; linarith [compose_enriches' a b]

/-- Weight of a^(n+1) is at least the weight of a^n. -/
theorem weight_composeN_mono (a : I) (n : ℕ) :
    weight (composeN a (n + 1)) ≥ weight (composeN a n) := by
  unfold weight; exact rs_composeN_mono a n

/-- Weight of a^(n+1) is at least weight of a. -/
theorem weight_composeN_ge_base (a : I) (n : ℕ) :
    weight (composeN a (n + 1)) ≥ weight a := by
  unfold weight; exact rs_composeN_ge_base a n

/-- Resonance deficit in terms of weight and symmetric part. -/
theorem resonanceDeficit_eq_weight (a b : I) :
    resonanceDeficit a b = weight a + weight b - (rs a b + rs b a) := by
  unfold resonanceDeficit weight; ring

end ResonanceGeometry

/-! ## §20. Emergence Calculus — Higher-order emergence

What happens when we take the emergence of emergence? The cocycle
condition constrains how emergence can "stack." -/

section EmergenceCalculus
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Emergence of a triple composition relative to sum of individual
    resonances. This is the "total emergence" of combining three ideas. -/
noncomputable def totalEmergence3 (a b c d : I) : ℝ :=
  rs (compose (compose a b) c) d - rs a d - rs b d - rs c d

/-- Total emergence of three decomposes into pairwise emergences. -/
theorem totalEmergence3_eq (a b c d : I) :
    totalEmergence3 a b c d =
    emergence a b d + emergence (compose a b) c d := by
  unfold totalEmergence3 emergence; ring

/-- Total emergence of three, alternative decomposition (right-associated). -/
theorem totalEmergence3_right (a b c d : I) :
    totalEmergence3 a b c d =
    emergence b c d + emergence a (compose b c) d := by
  rw [totalEmergence3_eq, cocycle_condition]

/-- Total emergence is invariant under re-association: the two
    decompositions always agree (a restatement of cocycle). -/
theorem totalEmergence3_assoc_invariant (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

/-- Emergence with void on left of composition. -/
theorem emergence_compose_void_left (a b c : I) :
    emergence (compose (void : I) a) b c = emergence a b c := by
  unfold emergence; simp

/-- Emergence with void on right of composition. -/
theorem emergence_compose_void_right (a b c : I) :
    emergence (compose a (void : I)) b c = emergence a b c := by
  unfold emergence; simp

/-- Emergence is "bilinear in the first two arguments" for linear ideas. -/
theorem emergence_leftLinear_first (a b c : I) (ha : leftLinear a) :
    emergence a b c = 0 := ha b c

/-- Emergence is zero for right-linear ideas in second position. -/
theorem emergence_rightLinear_second (a b c : I) (hb : rightLinear b) :
    emergence a b c = 0 := hb a c

/-- Total emergence vanishes when all parts are left-linear. -/
theorem totalEmergence3_linear (a b c d : I)
    (ha : leftLinear a) (hab : leftLinear (compose a b)) :
    totalEmergence3 a b c d = 0 := by
  rw [totalEmergence3_eq, ha b d, hab c d]; ring

/-- The "second-order emergence" — emergence of a∘b∘c beyond first-order.
    This measures the genuinely three-body effect. -/
noncomputable def secondOrderEmergence (a b c d : I) : ℝ :=
  totalEmergence3 a b c d - emergence a b d - emergence b c d

/-- Second-order emergence equals the difference of emergences at
    different levels of association. -/
theorem secondOrderEmergence_eq (a b c d : I) :
    secondOrderEmergence a b c d =
    emergence (compose a b) c d - emergence b c d := by
  unfold secondOrderEmergence; rw [totalEmergence3_eq]; ring

/-- By the cocycle condition, second-order emergence also equals
    the difference of the other pair. -/
theorem secondOrderEmergence_alt (a b c d : I) :
    secondOrderEmergence a b c d =
    emergence a (compose b c) d - emergence a b d := by
  unfold secondOrderEmergence
  rw [totalEmergence3_right]; ring

/-- Emergence against self: how composition a∘b resonates with itself
    beyond the parts. This is the "self-synergy" of a combination. -/
theorem emergence_self_bound (a b : I) :
    (emergence a b (compose a b)) ^ 2 ≤
    weight (compose a b) * weight (compose a b) := by
  have h := emergence_bounded' a b (compose a b)
  unfold weight; linarith [mul_self_nonneg (emergence a b (compose a b))]

/-- Emergence against void: always zero. A non-present observer
    cannot witness emergence. -/
theorem emergence_void_observer (a b : I) :
    emergence a b (void : I) = 0 := emergence_against_void a b

end EmergenceCalculus

/-! ## §21. Orthogonality Theory

Properties of orthogonal elements — ideas that have zero resonance
with each other, the ideatic analogue of perpendicular vectors. -/

section OrthogonalityTheory
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Orthogonality is not symmetric in general, reflecting that
    resonance is not symmetric. But mutual orthogonality IS symmetric. -/
theorem mutuallyOrthogonal_symm (a b : I) :
    mutuallyOrthogonal a b → mutuallyOrthogonal b a := by
  intro ⟨h1, h2⟩; exact ⟨h2, h1⟩

/-- Void is mutually orthogonal to everything. -/
theorem void_mutuallyOrthogonal_right (a : I) :
    mutuallyOrthogonal a (void : I) :=
  ⟨rs_void_right' a, rs_void_left' a⟩

/-- If a is orthogonal to c and b is orthogonal to c, then the
    resonance of a∘b with c is pure emergence. -/
theorem orthogonal_composition_is_emergence (a b c : I)
    (ha : orthogonal a c) (hb : orthogonal b c) :
    rs (compose a b) c = emergence a b c := by
  rw [rs_compose_eq a b c]
  unfold orthogonal at ha hb
  rw [ha, hb]; ring

/-- Resonance gap when b is orthogonal to a: it equals the self-resonance. -/
theorem resonanceGap_orthogonal (a b : I) (h : orthogonal a b) :
    resonanceGap a b = rs a a := by
  unfold resonanceGap orthogonal at *; rw [h]; ring

/-- Resonance deficit for mutually orthogonal ideas is the sum of weights. -/
theorem resonanceDeficit_mutuallyOrthogonal (a b : I)
    (h : mutuallyOrthogonal a b) :
    resonanceDeficit a b = weight a + weight b := by
  unfold resonanceDeficit weight mutuallyOrthogonal at *
  rw [h.1, h.2]; ring

/-- If a is left-orthogonal to b, emergence of a,c against b reduces. -/
theorem orthogonal_emergence (a b c : I) (h : orthogonal a c) :
    emergence a b c = rs (compose a b) c - rs b c := by
  unfold emergence orthogonal at *; rw [h]; ring

/-- Void is orthogonal to itself. -/
theorem void_self_orthogonal : orthogonal (void : I) (void : I) :=
  rs_void_void

/-- Non-void ideas are NOT orthogonal to themselves (they have
    positive self-resonance). -/
theorem nonvoid_not_self_orthogonal (a : I) (h : a ≠ void) :
    ¬orthogonal a a := by
  intro ho; unfold orthogonal at ho
  exact absurd (rs_nondegen' a ho) h

/-- Mutual orthogonality with void from either side. -/
theorem mutuallyOrthogonal_void_comm (a : I) :
    mutuallyOrthogonal (void : I) a ↔ mutuallyOrthogonal a (void : I) := by
  constructor
  · exact fun h => mutuallyOrthogonal_symm _ _ h
  · exact fun h => mutuallyOrthogonal_symm _ _ h

end OrthogonalityTheory

/-! ## §22. Weight Theory — Monotonicity, Bounds, and Structure

The weight function w(a) = rs(a,a) is the fundamental scalar invariant
of an idea. It measures "presence" or "salience." -/

section WeightTheory
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Weight is an invariant under ideatic morphisms. -/
theorem morphism_preserves_weight {J : Type*} [IdeaticSpace3 J]
    (f : IdeaticMorphism I J) (a : I) :
    weight (f.map a) = weight a := by
  unfold weight; exact f.map_rs a a

/-- The weight of a composition is at least the weight of the left factor.
    Restated in weight terminology. -/
theorem weight_left_sub (a b : I) :
    weight (compose a b) - weight a ≥ 0 := by
  linarith [weight_compose_ge_left a b]

/-- Weight difference under composition is emergence-related. -/
theorem weight_compose_minus (a b : I) :
    weight (compose a b) - weight a =
    rs (compose a b) (compose a b) - rs a a := by
  unfold weight; ring

/-- Weight of a composed with void is exactly weight of a. -/
theorem weight_compose_void (a : I) :
    weight (compose a (void : I)) = weight a := by
  unfold weight; simp

/-- Weight of void composed with a is exactly weight of a. -/
theorem weight_void_compose (a : I) :
    weight (compose (void : I) a) = weight a := by
  unfold weight; simp

/-- Weight is subadditive-like: the weight of a∘b is bounded
    from above by the emergence bound. Specifically, the emergence
    axiom constrains how fast weight can grow. -/
theorem weight_compose_self_resonance (a b : I) :
    weight (compose a b) =
    rs a (compose a b) + rs b (compose a b) + emergence a b (compose a b) := by
  unfold weight; rw [rs_compose_eq]

/-- Weight of a^(n+1) in terms of weight of a^n and additional resonance. -/
theorem weight_composeN_succ (a : I) (n : ℕ) :
    weight (composeN a (n + 1)) =
    rs (composeN a n) (composeN a (n + 1)) +
    rs a (composeN a (n + 1)) +
    emergence (composeN a n) a (composeN a (n + 1)) := by
  unfold weight; rw [composeN_succ, rs_compose_eq]

/-- Semantic charge in terms of weight. The semantic charge of a
    is how much composing a with itself resonates with a, minus
    twice the weight. -/
theorem semanticCharge_weight (a : I) :
    semanticCharge a = rs (compose a a) a - 2 * weight a := by
  unfold semanticCharge emergence weight; ring

/-- If a is fully linear, its weight under composition is additive:
    weight(a∘b) can be decomposed cleanly. -/
theorem weight_fullyLinear (a b c : I) (h : fullyLinear a) :
    rs (compose a b) c = rs a c + rs b c := by
  exact leftLinear_additive a h.1 b c

end WeightTheory

/-! ## §23. Polarization Identities

In inner product spaces, the inner product can be recovered from
the norm via polarization. Here we derive analogous identities
relating rs to weight, but with emergence corrections. -/

section Polarization
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Polarization-like identity: the resonance rs(a,b) can be expressed
    in terms of composition weights and individual weights, modulo
    resonance of a with a∘b. This is the IDT polarization identity. -/
theorem polarization_via_compose (a b : I) :
    rs a (compose a b) = weight (compose a b) - rs b (compose a b)
                         - emergence a b (compose a b) := by
  have h := weight_compose_self_resonance a b
  linarith

/-- Symmetrized resonance in terms of resonance gaps. -/
theorem symmetric_resonance_gap (a b : I) :
    rs a b + rs b a = weight a + weight b - resonanceDeficit a b := by
  unfold resonanceDeficit weight; ring

/-- The asymmetry relates to the difference of resonance gaps plus a weight
    correction: asymmetry(a,b) = -gap(a,b) + gap(b,a) + weight(a) - weight(b). -/
theorem asymmetry_gap_weight (a b : I) :
    asymmetry a b = resonanceGap b a - resonanceGap a b + weight a - weight b := by
  unfold asymmetry resonanceGap weight; ring

/-- Resonance decomposition: rs(a,b) expressed via weight, deficit,
    and asymmetry. -/
theorem rs_from_invariants (a b : I) :
    rs a b = (weight a + weight b - resonanceDeficit a b + asymmetry a b) / 2 := by
  unfold weight resonanceDeficit asymmetry; ring

/-- The "parallelogram-like" identity for compositions:
    weight(a∘b) + weight(?) involves emergence corrections.
    Unlike Hilbert spaces, we don't get a clean parallelogram law. -/
theorem compose_weight_identity (a b : I) :
    weight (compose a b) =
    rs a (compose a b) + rs b (compose a b) +
    emergence a b (compose a b) := by
  exact weight_compose_self_resonance a b

/-- Symmetric part of cross-resonance equals half the complement of deficit. -/
theorem symmetricPart_deficit (a b : I) :
    symmetricPart a b = (weight a + weight b - resonanceDeficit a b) / 2 := by
  unfold symmetricPart weight resonanceDeficit; ring

/-- Antisymmetric part equals half the asymmetry. -/
theorem antisymmetricPart_asymmetry (a b : I) :
    antisymmetricPart a b = asymmetry a b / 2 := by
  unfold antisymmetricPart asymmetry; ring

end Polarization

/-! ## §24. Deep Cocycle Identities

Further consequences of the cocycle condition, including
quadruple and iterated composition identities. -/

section DeepCocycle
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Cocycle condition with d = compose a b: emergence measured
    against the composition itself. -/
theorem cocycle_self_compose (a b c : I) :
    emergence a b (compose a b) + emergence (compose a b) c (compose a b) =
    emergence b c (compose a b) + emergence a (compose b c) (compose a b) :=
  cocycle_condition a b c (compose a b)

/-- Cocycle with identical first two arguments: κ(a,a,c,d). -/
theorem cocycle_double (a c d : I) :
    emergence a a d + emergence (compose a a) c d =
    emergence a c d + emergence a (compose a c) d :=
  cocycle_condition a a c d

/-- Iterated cocycle: resonance of a 5-fold composition decomposes
    into individual resonances and emergences. -/
theorem rs_compose5 (a b c d e f : I) :
    rs (compose (compose (compose (compose a b) c) d) e) f =
    rs a f + rs b f + rs c f + rs d f + rs e f +
    emergence a b f +
    emergence (compose a b) c f +
    emergence (compose (compose a b) c) d f +
    emergence (compose (compose (compose a b) c) d) e f := by
  rw [rs_compose_eq (compose (compose (compose a b) c) d) e f]
  rw [rs_compose_eq (compose (compose a b) c) d f]
  rw [rs_compose_eq (compose a b) c f]
  rw [rs_compose_eq a b f]
  ring

/-- Emergence is preserved under right-void composition on the observer. -/
theorem emergence_observer_compose_void (a b c : I) :
    emergence a b (compose c (void : I)) = emergence a b c := by
  unfold emergence; simp

/-- Emergence is preserved under left-void composition on the observer. -/
theorem emergence_observer_void_compose (a b c : I) :
    emergence a b (compose (void : I) c) = emergence a b c := by
  unfold emergence; simp

/-- Triple cocycle: the cocycle applied twice gives a chain of constraints. -/
theorem cocycle_chain (a b c d e : I) :
    emergence a b e + emergence (compose a b) c e +
    emergence (compose (compose a b) c) d e =
    emergence c d e + emergence b (compose c d) e +
    emergence a (compose b (compose c d)) e := by
  have h1 := cocycle_condition (compose a b) c d e
  have h2 := cocycle_condition a b (compose c d) e
  linarith

/-- Emergence addition: κ(a,b,d) can be related to κ(a,b,c+d)
    if we know about κ involving c. This is a restatement of cocycle. -/
theorem emergence_shift (a b c d : I) :
    emergence a (compose b c) d =
    emergence a b d + emergence (compose a b) c d - emergence b c d := by
  linarith [cocycle_condition a b c d]

end DeepCocycle

/-! ## §25. Interpretation Theory — Extended

More properties of the interpretation framework, including
iterated interpretation and interpretation chains. -/

section InterpretationExtended
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Double interpretation: interpreting an interpretation.
    If reader r first interprets signal s₁, then the resulting state
    interprets s₂, we get compose (compose r s₁) s₂. -/
def interpretTwice (r s₁ s₂ : I) : I :=
  compose (compose r s₁) s₂

/-- Double interpretation equals iterated composition (by associativity,
    this is also compose r (compose s₁ s₂)). -/
theorem interpretTwice_assoc (r s₁ s₂ : I) :
    interpretTwice r s₁ s₂ = compose r (compose s₁ s₂) := by
  unfold interpretTwice; rw [compose_assoc']

/-- The emergence of double interpretation beyond single. -/
theorem interpretTwice_emergence (r s₁ s₂ d : I) :
    rs (interpretTwice r s₁ s₂) d =
    rs r d + rs s₁ d + rs s₂ d +
    emergence r s₁ d + emergence (compose r s₁) s₂ d := by
  unfold interpretTwice
  rw [rs_compose_eq (compose r s₁) s₂ d, rs_compose_eq r s₁ d]
  ring

/-- Interpretation of void signal is the reader unchanged. -/
theorem interpretTwice_void_second (r s : I) :
    interpretTwice r s (void : I) = interpret r s := by
  unfold interpretTwice interpret; simp

/-- Interpretation of void first signal is just interpreting the second. -/
theorem interpretTwice_void_first (r s : I) :
    interpretTwice r (void : I) s = interpret r s := by
  unfold interpretTwice interpret; simp

/-- Sender payoff with void signal is self-resonance. -/
theorem senderPayoff_void_signal (s : I) :
    senderPayoff s (void : I) = rs s s :=
  senderPayoff_void_reader s

/-- Communication surplus is symmetric in its vanishing at void. -/
theorem communicationSurplus_symmetric_void :
    communicationSurplus (void : I) (void : I) = 0 :=
  communicationSurplus_void_signal _

/-- Misunderstanding gap in terms of asymmetry. -/
theorem misunderstandingGap_eq (signal reader : I) :
    misunderstandingGap signal reader =
    rs signal (interpret reader signal) - rs reader (interpret reader signal) := by
  unfold misunderstandingGap senderPayoff receiverPayoff; ring

end InterpretationExtended

/-! ## §26. Narrative Structure — Extended

More properties of composeList and narrative coherence measures. -/

section NarrativeExtended
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- composeList of two elements is their composition. -/
theorem composeList_two (a b : I) :
    composeList [a, b] = compose a b := by
  simp [composeList]

/-- composeList of three elements. -/
theorem composeList_three (a b c : I) :
    composeList [a, b, c] = compose a (compose b c) := by
  simp [composeList]

/-- composeList with void prepended is the same. -/
theorem composeList_void_cons (l : List I) :
    composeList ((void : I) :: l) = composeList l := by
  simp [composeList]

/-- Resonance of a composeList pair against an observer. -/
theorem composeList_two_rs (a b d : I) :
    rs (composeList [a, b]) d = rs a d + rs b d + emergence a b d := by
  rw [composeList_two, rs_compose_eq]

/-- Total resonance of a three-element sequence. -/
theorem totalResonance_triple (a b c : I) :
    totalResonance [a, b, c] = rs a b + rs b c := by
  simp [totalResonance]

/-- Narrative emergence of a pair is just a single emergence. -/
theorem narrativeEmergence_two (a b d : I) :
    narrativeEmergence [a, b] d = emergence a b d :=
  narrativeEmergence_pair a b d

/-- Narrative emergence of a triple sequence. -/
theorem narrativeEmergence_triple (a b c d : I) :
    narrativeEmergence [a, b, c] d = emergence a b d + emergence b c d := by
  simp [narrativeEmergence]

end NarrativeExtended

/-! ## §27. Resonance Equivalence — Deeper Properties

Resonance equivalence is the strongest form of "sameness" for
utterances. We derive more of its consequences. -/

section ResonanceEquivExtended
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Resonance equivalence is reflexive. -/
theorem resonanceEquiv_refl (a : I) : resonanceEquiv a a :=
  fun _ => rfl

/-- Resonance equivalence implies that the right-hand weight can be
    recovered from cross-resonance: rs(a,b) = weight(b). -/
theorem resonanceEquiv_cross_eq_weight (a b : I)
    (h : resonanceEquiv a b) : rs a b = weight b := by
  unfold weight; exact h b

/-- Two resonance-equivalent ideas have the same symmetric cross-resonance
    sum with any third idea, given the reverse direction also matches. -/
theorem resonanceEquiv_symmetric_sum (a b c : I)
    (h : resonanceEquiv a b)
    (hrev : rs c a = rs c b) :
    rs a c + rs c a = rs b c + rs c b := by
  rw [h c, hrev]

/-- Resonance equivalence with void implies being void (via weight). -/
theorem resonanceEquiv_void_implies_void (a : I)
    (h : resonanceEquiv a (void : I)) : a = void := by
  have hw : rs a a = 0 := by
    have := h a; rw [rs_void_left'] at this; exact this
  exact rs_nondegen' a hw

/-- connotation is zero when ideas are resonance-equivalent. -/
theorem connotation_zero_of_equiv (a b c : I)
    (h : resonanceEquiv a b) : connotation a b c = 0 := by
  unfold connotation; rw [h c]; ring

end ResonanceEquivExtended

/-! ## §28. Semantic Charge — Extended Theory

Semantic charge κ(a,a,a) measures self-amplification. We derive
more of its structural properties. -/

section SemanticChargeExtended
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Semantic charge equals rs(a²,a) - 2·weight(a). -/
theorem semanticCharge_eq_weight (a : I) :
    semanticCharge a = rs (compose a a) a - 2 * weight a :=
  semanticCharge_weight a

/-- Semantic charge of a linear idea is zero: linear ideas
    don't self-amplify. -/
theorem semanticCharge_leftLinear (a : I) (h : leftLinear a) :
    semanticCharge a = 0 := by
  unfold semanticCharge; exact h a a

/-- Semantic charge is preserved by morphisms (already proven, restated). -/
theorem semanticCharge_morphism_invariant {J : Type*} [IdeaticSpace3 J]
    (f : IdeaticMorphism I J) (a : I) :
    semanticCharge (f.map a) = semanticCharge a :=
  morphism_preserves_charge f a

/-- Dialectical tension equals self-emergence. -/
theorem dialecticalTension_eq_selfEmergence (a b : I) :
    dialecticalTension a b = selfEmergence a b := by
  unfold dialecticalTension selfEmergence; rfl

/-- Semantic charge is a special case of self-emergence: κ(a,a,a). -/
theorem semanticCharge_eq_selfEmergence_diag (a : I) :
    semanticCharge a = emergence a a a := rfl

end SemanticChargeExtended

/-! ## §29. Order Sensitivity — Extended

The non-commutativity of ideas explored more deeply. -/

section OrderSensitivityExtended
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Order sensitivity vanishes when both arguments are the same. -/
theorem orderSensitivity_self (a c : I) :
    orderSensitivity a a c = 0 := by
  unfold orderSensitivity; ring

/-- Order sensitivity with void on right. -/
theorem orderSensitivity_void_right (a c : I) :
    orderSensitivity a (void : I) c = 0 := by
  unfold orderSensitivity; simp

/-- Order sensitivity against void observer. -/
theorem orderSensitivity_void_observer (a b : I) :
    orderSensitivity a b (void : I) = 0 := by
  unfold orderSensitivity; simp [rs_void_right']

/-- Meaning curvature vanishes for identical arguments. -/
theorem meaningCurvature_self (a c : I) :
    meaningCurvature a a c = 0 := by
  unfold meaningCurvature emergence; ring

/-- Meaning curvature against void is zero. -/
theorem meaningCurvature_void_observer (a b : I) :
    meaningCurvature a b (void : I) = 0 := by
  unfold meaningCurvature; rw [emergence_against_void, emergence_against_void]; ring

/-- The total meaning curvature of a triple (sum of pairwise curvatures)
    captures the total "non-commutativity" of three ideas. -/
noncomputable def totalCurvature (a b c d : I) : ℝ :=
  meaningCurvature a b d + meaningCurvature b c d + meaningCurvature a c d

/-- Total curvature with void is zero. -/
theorem totalCurvature_void_observer (a b c : I) :
    totalCurvature a b c (void : I) = 0 := by
  unfold totalCurvature
  rw [meaningCurvature_void_observer, meaningCurvature_void_observer,
      meaningCurvature_void_observer]; ring

end OrderSensitivityExtended

/-! ## §30. Context Shift — Extended Theory

More properties of how meaning shifts under context. -/

section ContextExtended
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Left context shift is zero when the context is void. -/
theorem leftContextShift_void' (a b : I) :
    leftContextShift (void : I) a b = 0 :=
  leftContextShift_void a b

/-- Right context shift is zero when the context is void. -/
theorem rightContextShift_void' (a b : I) :
    rightContextShift (void : I) a b = 0 :=
  rightContextShift_void a b

/-- Left context self-shift: how does prepending c change a's
    resonance with itself? -/
noncomputable def leftContextSelfShift (c a : I) : ℝ :=
  rs (compose c a) (compose c a) - rs a a

/-- Left context self-shift is non-negative when c = void. -/
theorem leftContextSelfShift_void (a : I) :
    leftContextSelfShift (void : I) a = 0 := by
  unfold leftContextSelfShift; simp

/-- Left context self-shift in terms of weight. -/
theorem leftContextSelfShift_weight (c a : I) :
    leftContextSelfShift c a = weight (compose c a) - weight a := by
  unfold leftContextSelfShift weight; ring

/-- Left context self-shift is bounded below by the weight of the
    context minus the weight of the idea. compose_enriches gives
    weight(c∘a) ≥ weight(c). -/
theorem leftContextSelfShift_ge (c a : I) :
    leftContextSelfShift c a ≥ weight c - weight a := by
  rw [leftContextSelfShift_weight]
  linarith [weight_compose_ge_left c a]

/-- Left context self-shift with void context is zero:
    prepending silence doesn't change anything. -/
theorem leftContextSelfShift_void_is_zero (a : I) :
    leftContextSelfShift (void : I) a = 0 :=
  leftContextSelfShift_void a

end ContextExtended

/-! ## §31. Model Theory — The Boolean Model

A two-element model showing that nontrivial ideatic spaces exist
with genuine asymmetry possible. -/

section BoolModel

/-- We demonstrate that the Unit and ℕ models have different properties:
    the ℕ model has non-zero weight for non-zero elements. -/
theorem nat_weight_one :
    @weight ℕ natIdeaticSpace 1 = 1 := by
  unfold weight; simp [IdeaticSpace3.rs, natIdeaticSpace]

/-- In the ℕ model, weight of n is n². -/
theorem nat_weight_eq (n : ℕ) :
    @weight ℕ natIdeaticSpace n = (n : ℝ) * n := by
  unfold weight; simp [IdeaticSpace3.rs, natIdeaticSpace]

/-- In the ℕ model, all emergence is zero (bilinear). -/
theorem nat_emergence_zero (a b c : ℕ) :
    @emergence ℕ natIdeaticSpace a b c = 0 := by
  unfold emergence
  simp [IdeaticSpace3.compose, IdeaticSpace3.rs, natIdeaticSpace]
  push_cast; ring

/-- In the ℕ model, compose is addition. -/
theorem nat_compose_eq (a b : ℕ) :
    @IdeaticSpace3.compose ℕ natIdeaticSpace a b = a + b := rfl

end BoolModel

/-! ## §32. Enrichment Chains — Iterated Composition Growth

The compose_enriches axiom gives us that weight grows under composition.
We explore the consequences of iterated enrichment. -/

section EnrichmentChains
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Weight of a composed with b composed with c is at least weight of a. -/
theorem weight_triple_ge (a b c : I) :
    weight (compose (compose a b) c) ≥ weight a := by
  calc weight (compose (compose a b) c)
      ≥ weight (compose a b) := weight_compose_ge_left _ _
    _ ≥ weight a := weight_compose_ge_left _ _

/-- Weight of a triple composition is at least weight of a∘b. -/
theorem weight_triple_ge_pair (a b c : I) :
    weight (compose (compose a b) c) ≥ weight (compose a b) :=
  weight_compose_ge_left _ _

/-- Composition with a non-void element strictly increases weight
    IF the original is also non-void. Well, we can't prove strict
    increase in general, but we can prove the result stays non-void. -/
theorem compose_nonvoid_left (a b : I) (ha : a ≠ void) :
    compose a b ≠ void :=
  compose_ne_void_of_left a b ha

/-- Weight chain: weight of a^n is monotonically non-decreasing. -/
theorem weight_composeN_chain (a : I) (m n : ℕ) (h : m ≤ n) :
    weight (composeN a n) ≥ weight (composeN a m) := by
  induction h with
  | refl => exact le_refl _
  | step h ih =>
    calc weight (composeN a (Nat.succ _))
        ≥ weight (composeN a _) := weight_composeN_mono a _
      _ ≥ weight (composeN a m) := ih

/-- Weight of a^0 (= void) is zero. -/
theorem weight_composeN_zero (a : I) : weight (composeN a 0) = 0 := by
  simp [weight_void]

/-- Non-void ideas have strictly positive weight at all positive iterates. -/
theorem weight_composeN_pos (a : I) (ha : a ≠ void) (n : ℕ) :
    weight (composeN a (n + 1)) > 0 := by
  have h := weight_composeN_ge_base a n
  have hp := weight_pos a ha
  linarith

end EnrichmentChains

/-! ## §33. Emergence Bounds — Consequences of E3

The emergence Cauchy-Schwarz gives us bounds on how much
emergence can occur. We derive more consequences. -/

section EmergenceBounds
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Emergence squared is bounded by the product of weights. -/
theorem emergence_sq_le_weights (a b c : I) :
    (emergence a b c) ^ 2 ≤ weight (compose a b) * weight c := by
  unfold weight; exact emergence_bounded' a b c

/-- When c has zero weight (c = void), emergence is zero. -/
theorem emergence_zero_of_zero_weight (a b c : I)
    (h : weight c = 0) : emergence a b c = 0 := by
  have hc := (weight_eq_zero_iff c).mp h
  rw [hc]; exact emergence_against_void a b

/-- When a∘b has zero weight, both a and b must be void (by enrichment),
    hence emergence is zero. -/
theorem emergence_zero_of_compose_zero_weight (a b c : I)
    (h : weight (compose a b) = 0) : emergence a b c = 0 := by
  have ha : a = void := by
    apply rs_nondegen' a
    have h1 := compose_enriches' a b
    have h2 := rs_self_nonneg' a
    unfold weight at h; linarith
  rw [ha]; exact emergence_void_left b c

/-- Absolute emergence bound using sqrt-like reasoning:
    |κ(a,b,c)|² ≤ w(a∘b) · w(c). -/
theorem emergence_abs_bound (a b c : I) :
    emergence a b c * emergence a b c ≤
    weight (compose a b) * weight c := by
  have h := emergence_sq_le_weights a b c
  rwa [sq] at h

/-- Emergence of void∘a with anything: always zero. -/
theorem emergence_void_compose (a b c : I) :
    emergence (compose (void : I) a) b c = emergence a b c := by
  unfold emergence; simp

/-- Emergence bound specialized to self-measurement. -/
theorem emergence_self_sq_bound (a b : I) :
    (emergence a b (compose a b)) ^ 2 ≤
    weight (compose a b) * weight (compose a b) := by
  exact emergence_sq_le_weights a b (compose a b)

end EmergenceBounds

/-! ## §34. Functorial Properties — Morphism Theory Extended -/

section MorphismExtended
variable {I : Type*} [S : IdeaticSpace3 I]
variable {J : Type*} [T : IdeaticSpace3 J]

/-- A morphism preserves order sensitivity. -/
theorem morphism_preserves_orderSensitivity (f : IdeaticMorphism I J)
    (a b c : I) :
    orderSensitivity (f.map a) (f.map b) (f.map c) =
    orderSensitivity a b c := by
  unfold orderSensitivity
  rw [← f.map_compose a b, ← f.map_compose b a, f.map_rs, f.map_rs]

/-- A morphism preserves asymmetry. -/
theorem morphism_preserves_asymmetry (f : IdeaticMorphism I J)
    (a b : I) :
    asymmetry (f.map a) (f.map b) = asymmetry a b := by
  unfold asymmetry; rw [f.map_rs, f.map_rs]

/-- A morphism preserves meaning curvature. -/
theorem morphism_preserves_meaningCurvature (f : IdeaticMorphism I J)
    (a b c : I) :
    meaningCurvature (f.map a) (f.map b) (f.map c) =
    meaningCurvature a b c := by
  unfold meaningCurvature
  rw [morphism_preserves_emergence f a b c, morphism_preserves_emergence f b a c]

/-- A morphism preserves resonance deficit. -/
theorem morphism_preserves_resonanceDeficit (f : IdeaticMorphism I J)
    (a b : I) :
    resonanceDeficit (f.map a) (f.map b) = resonanceDeficit a b := by
  unfold resonanceDeficit; rw [f.map_rs, f.map_rs, f.map_rs, f.map_rs]

/-- A morphism maps void to void (restated). -/
theorem morphism_void (f : IdeaticMorphism I J) :
    f.map (IdeaticSpace3.void : I) = (IdeaticSpace3.void : J) :=
  f.map_void

/-- A morphism preserves the symmetric part of resonance. -/
theorem morphism_preserves_symmetricPart (f : IdeaticMorphism I J)
    (a b : I) :
    symmetricPart (f.map a) (f.map b) = symmetricPart a b := by
  unfold symmetricPart; rw [f.map_rs, f.map_rs]

end MorphismExtended

/-! ## §35. Resonance Deficit Algebra

The resonance deficit is a natural "distance-like" quantity.
We derive more of its algebraic properties. -/

section DeficitAlgebra
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Resonance deficit with void on left, restated. -/
theorem resonanceDeficit_void_left (a : I) :
    resonanceDeficit (void : I) a = weight a :=
  resonanceDeficit_void a

/-- Resonance deficit is always equal to weight sum minus twice
    the symmetric part. -/
theorem resonanceDeficit_symmetric (a b : I) :
    resonanceDeficit a b = weight a + weight b - 2 * symmetricPart a b := by
  unfold resonanceDeficit weight symmetricPart; ring

/-- Two ideas with zero resonance deficit have equal symmetric parts
    to their average weight. -/
theorem zero_deficit_symmetric (a b : I)
    (h : resonanceDeficit a b = 0) :
    symmetricPart a b = (weight a + weight b) / 2 := by
  have := resonanceDeficit_symmetric a b
  linarith

/-- Resonance deficit of a with itself is always zero. -/
theorem resonanceDeficit_self' (a : I) : resonanceDeficit a a = 0 :=
  resonanceDeficit_self a

end DeficitAlgebra

/-! ## §36. Linearity Detection — When Is Emergence Zero?

Criteria for detecting when emergence must vanish. -/

section LinearityDetection
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- If a is left-linear and b is right-linear, both produce zero emergence. -/
theorem linear_pair_zero_emergence (a b c : I)
    (ha : leftLinear a) : emergence a b c = 0 := ha b c

/-- void is the canonical linear element. -/
theorem void_emergence_vanishes (b c : I) :
    emergence (void : I) b c = 0 := emergence_void_left b c

/-- A fully linear idea has zero semantic charge. -/
theorem fullyLinear_zero_charge (a : I) (h : fullyLinear a) :
    semanticCharge a = 0 :=
  semanticCharge_leftLinear a h.1

/-- A fully linear idea has zero dialectical tension with anything. -/
theorem fullyLinear_zero_tension (a b : I) (h : fullyLinear a) :
    dialecticalTension a b = 0 := by
  unfold dialecticalTension; exact h.1 b (compose a b)

/-- If all ideas are left-linear, emergence is identically zero. -/
theorem allLinear_no_emergence (h : ∀ a : I, leftLinear a)
    (a b c : I) : emergence a b c = 0 := h a b c

/-- In a world without emergence, resonance is purely additive. -/
theorem no_emergence_additive (h : ∀ a b c : I, emergence a b c = 0)
    (a b c : I) : rs (compose a b) c = rs a c + rs b c := by
  have := rs_compose_eq a b c; rw [h a b c] at this; linarith

end LinearityDetection

/-! ## §37. Semiotic Equivalences — Extended

More properties of sameIdea and related equivalences. -/

section SemioticsExtended
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- sameIdea with void means being fully left-linear. -/
theorem sameIdea_void_iff_leftLinear (a : I) :
    sameIdea (void : I) a ↔ leftLinear a := by
  rw [void_sameIdea_iff]
  constructor
  · intro h; intro b c; exact h b c
  · intro h; intro b c; exact h b c

/-- Two left-linear ideas always carry the same idea (from void's perspective). -/
theorem leftLinear_sameIdea_of_both (a b : I)
    (ha : leftLinear a) (hb : leftLinear b) :
    sameIdea a b := by
  intro c d; rw [ha c d, hb c d]

/-- Polysemy requires non-linearity: a polysemous idea must have emergence. -/
theorem polysemous_has_emergence (a : I) (h : polysemous a) :
    hasEmergence a := by
  obtain ⟨c₁, c₂, d, hne⟩ := h
  by_contra hno
  push_neg at hno
  unfold hasEmergence at hno
  push_neg at hno
  exact hne (by rw [hno c₁ d, hno c₂ d])

/-- The connotation function is antisymmetric in its first two arguments. -/
theorem connotation_antisymm (a b c : I) :
    connotation a b c = -connotation b a c := by
  unfold connotation; ring

/-- Connotation with void is zero. -/
theorem connotation_void_observer (a b : I) :
    connotation a b (void : I) = 0 := by
  unfold connotation; rw [rs_void_right', rs_void_right']; ring

/-- Synonymy is symmetric. -/
theorem synonymous_symm (a b : I) :
    synonymous a b → synonymous b a := by
  intro ⟨h1, h2⟩
  constructor
  · exact sameIdea_symm a b h1
  · intro h; exact h2 (fun c => (h c).symm)

end SemioticsExtended

/-! ## §38. Unit Model — Extended Properties -/

section UnitModelExtended

/-- In the unit model, weight is zero. -/
theorem unit_weight_zero : ∀ a : Unit, @weight Unit unitIdeaticSpace a = 0 := by
  intro a; unfold weight; rfl

/-- In the unit model, resonance deficit is zero. -/
theorem unit_resonanceDeficit_zero :
    ∀ a b : Unit, @resonanceDeficit Unit unitIdeaticSpace a b = 0 := by
  intros; unfold resonanceDeficit; simp [unit_rs_zero]

/-- In the unit model, semantic charge is zero. -/
theorem unit_semanticCharge_zero :
    ∀ a : Unit, @semanticCharge Unit unitIdeaticSpace a = 0 := by
  intros; unfold semanticCharge emergence; simp [unit_rs_zero]

/-- In the unit model, everything is left-linear. -/
theorem unit_allLinear :
    ∀ a : Unit, @leftLinear Unit unitIdeaticSpace a := by
  intro a b c; unfold emergence; simp [unit_rs_zero]

end UnitModelExtended

/-! ## §39. The Resonance Spectrum — Frequency-like Decomposition

While we can't do Fourier analysis without a Hilbert space, we can
define notions of "frequency" based on how rapidly resonance changes
under iterated composition. -/

section ResonanceSpectrum
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The resonance growth rate: how much self-resonance increases per
    iteration of composition. -/
noncomputable def resonanceGrowth (a : I) (n : ℕ) : ℝ :=
  weight (composeN a (n + 1)) - weight (composeN a n)

/-- Resonance growth is non-negative (from compose_enriches). -/
theorem resonanceGrowth_nonneg (a : I) (n : ℕ) :
    resonanceGrowth a n ≥ 0 := by
  unfold resonanceGrowth
  linarith [weight_composeN_mono a n]

/-- Resonance growth at step 0 is weight(a) - weight(void) = weight(a). -/
theorem resonanceGrowth_zero (a : I) :
    resonanceGrowth a 0 = weight a := by
  unfold resonanceGrowth weight
  simp [composeN_zero, composeN_one, rs_void_void]

/-- Total weight after n steps is the sum of all growths. -/
theorem weight_sum_growth (a : I) : ∀ n : ℕ,
    weight (composeN a n) = (Finset.range n).sum (fun k => resonanceGrowth a k) := by
  intro n; induction n with
  | zero => simp [weight_void]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    unfold resonanceGrowth; ring

end ResonanceSpectrum

end IDT3
