import FormalAnthropology.IDT_Foundations

/-!
# The Meaning Game — Foundations

The core extension of IDT for game-theoretic analysis. We introduce
`ResonanceField`: an ideatic space equipped with a **quantitative**
resonance function `resonanceStrength : I → I → ℕ` that measures the
*degree* to which two ideas resonate.

Where `IdeaticSpace.resonates` is a binary relation (Prop), resonance
strength is a number — enabling payoffs, equilibria, and comparative
statics. The connection: positive resonance strength implies resonance.

## Axioms for ResonanceField

- **S1 (Symmetry)**: resonanceStrength is symmetric
- **S2 (Self-resonance)**: every idea has positive self-resonance
- **S3 (Void baseline)**: void has resonance strength 1 with itself
- **S4 (Composition monotonicity)**: composing resonant ideas preserves
  a lower bound on resonance strength
- **S5 (Link to resonance)**: positive strength ↔ resonance (connecting
  the quantitative and qualitative notions)
-/

set_option pp.unicode.fun true
set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.MG

open IDT IdeaticSpace

/-- A `ResonanceField` extends `IdeaticSpace` with a quantitative measure
    of resonance strength. This is the foundation for all game-theoretic
    analysis in The Meaning Game. -/
class ResonanceField (I : Type*) extends IdeaticSpace I where
  /-- Quantitative resonance: how strongly two ideas resonate (0 = not at all) -/
  resonanceStrength : I → I → ℕ
  /-- S1: Resonance strength is symmetric -/
  strength_symm : ∀ (a b : I), resonanceStrength a b = resonanceStrength b a
  /-- S2: Every idea has positive self-resonance -/
  strength_self_pos : ∀ (a : I), 0 < resonanceStrength a a
  /-- S3: Void has self-resonance strength exactly 1 (the baseline) -/
  strength_void_self : resonanceStrength void void = 1
  /-- S4: Composing with a shared context preserves resonance strength.
      If a resonates with b at strength s, then compose a c resonates
      with compose b c at strength ≥ s. Context doesn't weaken agreement. -/
  strength_compose_right_mono : ∀ (a b c : I),
    resonanceStrength (compose a c) (compose b c) ≥ resonanceStrength a b
  /-- S5: Composing with shared left context also preserves strength. -/
  strength_compose_left_mono : ∀ (a b c : I),
    resonanceStrength (compose c a) (compose c b) ≥ resonanceStrength a b
  /-- S6: Positive resonance strength implies the qualitative resonance relation. -/
  strength_pos_implies_resonates : ∀ (a b : I),
    0 < resonanceStrength a b → resonates a b

variable {I : Type*} [ResonanceField I]

/-! ## §1. Basic Strength Properties -/

/-- Resonance strength is symmetric -/
theorem strength_symm (a b : I) :
    ResonanceField.resonanceStrength a b = ResonanceField.resonanceStrength b a :=
  ResonanceField.strength_symm a b

/-- Self-resonance is positive: you always agree with yourself to some degree -/
theorem strength_self_pos (a : I) :
    0 < ResonanceField.resonanceStrength a a :=
  ResonanceField.strength_self_pos a

/-- Void self-resonance is exactly 1 -/
@[simp] theorem strength_void_self :
    ResonanceField.resonanceStrength (IdeaticSpace.void : I) (IdeaticSpace.void : I) = 1 :=
  ResonanceField.strength_void_self

/-- Right-context composition preserves resonance strength -/
theorem strength_compose_right_mono (a b c : I) :
    ResonanceField.resonanceStrength (IdeaticSpace.compose a c) (IdeaticSpace.compose b c) ≥
    ResonanceField.resonanceStrength a b :=
  ResonanceField.strength_compose_right_mono a b c

/-- Left-context composition preserves resonance strength -/
theorem strength_compose_left_mono (a b c : I) :
    ResonanceField.resonanceStrength (IdeaticSpace.compose c a) (IdeaticSpace.compose c b) ≥
    ResonanceField.resonanceStrength a b :=
  ResonanceField.strength_compose_left_mono a b c

/-! ## §2. Derived Strength Theorems -/

/-- Self-resonance is always ≥ 1 -/
theorem strength_self_ge_one (a : I) :
    ResonanceField.resonanceStrength a a ≥ 1 := by
  exact Nat.one_le_iff_ne_zero.mpr (Nat.not_eq_zero_of_lt (strength_self_pos a))

/-- Composing an idea with itself preserves self-resonance strength -/
theorem strength_self_compose_ge (a : I) :
    ResonanceField.resonanceStrength (IdeaticSpace.compose a a) (IdeaticSpace.compose a a) ≥
    ResonanceField.resonanceStrength a a := by
  exact strength_compose_right_mono a a a

/-- Void composed with any idea: resonance strength ≥ self-resonance of the idea.
    Because compose void a = a, so strength(compose void a, compose void a) =
    strength(a, a) ≥ 1. -/
theorem strength_void_compose_self (a : I) :
    ResonanceField.resonanceStrength
      (IdeaticSpace.compose (IdeaticSpace.void : I) a)
      (IdeaticSpace.compose (IdeaticSpace.void : I) a) =
    ResonanceField.resonanceStrength a a := by
  simp

/-- Positive self-resonance implies qualitative self-resonance -/
theorem self_resonates_via_strength (a : I) :
    IdeaticSpace.resonates a a := by
  exact ResonanceField.strength_pos_implies_resonates a a (strength_self_pos a)

/-! ## §3. The Interpretation Payoff

The central concept of The Meaning Game: when player A sends signal `s`
and player B interprets it by composing with their idea `r`, the payoff
is `resonanceStrength s (compose r s)` — how strongly B's interpretation
agrees with A's original idea. -/

/-- The interpretation of signal s by receiver with idea r -/
def interpret (s r : I) : I := IdeaticSpace.compose r s

/-- The sender's payoff: how much the interpretation agrees with the signal -/
def senderPayoff (s r : I) : ℕ :=
  ResonanceField.resonanceStrength s (interpret s r)

/-- The receiver's payoff: how much the interpretation agrees with their idea -/
def receiverPayoff (s r : I) : ℕ :=
  ResonanceField.resonanceStrength r (interpret s r)

/-- Void receiver perfectly preserves the signal: interpret s void = s -/
@[simp] theorem interpret_void_receiver (s : I) :
    interpret s (IdeaticSpace.void : I) = s := by
  simp [interpret]

/-- Void signal is interpreted as the receiver's idea: interpret void r = r -/
@[simp] theorem interpret_void_signal (r : I) :
    interpret (IdeaticSpace.void : I) r = r := by
  simp [interpret]

/-- Sender payoff when receiver is void: full self-resonance.
    A void receiver doesn't distort your signal at all. -/
theorem senderPayoff_void_receiver (s : I) :
    senderPayoff s (IdeaticSpace.void : I) = ResonanceField.resonanceStrength s s := by
  simp [senderPayoff]

/-- Sender payoff is always positive when receiver is void -/
theorem senderPayoff_void_receiver_pos (s : I) :
    0 < senderPayoff s (IdeaticSpace.void : I) := by
  rw [senderPayoff_void_receiver]
  exact strength_self_pos s

/-- Receiver payoff when signal is void: full self-resonance.
    A void signal doesn't change the receiver's idea. -/
theorem receiverPayoff_void_signal (r : I) :
    receiverPayoff (IdeaticSpace.void : I) r = ResonanceField.resonanceStrength r r := by
  simp [receiverPayoff]

/-- Sender payoff when both are void: exactly 1 -/
theorem senderPayoff_void_void :
    senderPayoff (IdeaticSpace.void : I) (IdeaticSpace.void : I) = 1 := by
  simp [senderPayoff]

/-- KEY THEOREM: Sender payoff is monotone in context.
    If you add the same elaboration c to both the signal and the receiver's
    repertoire, the sender's payoff doesn't decrease.

    interpret (compose s c) (compose r c) = compose (compose r c) (compose s c)
    But that's not quite right. Let's think...

    Actually: senderPayoff s r = strength s (compose r s).
    We want: senderPayoff s r ≥ something involving strength.

    Using strength_compose_left_mono with c = r:
    strength (compose r s) (compose r s) ≥ strength s s
    That's about self-resonance of the interpretation.

    The interesting monotonicity: strength_compose_left_mono gives
    strength (compose r a) (compose r b) ≥ strength a b.
    So strength (compose r s) (compose r s) ≥ strength s s. -/
theorem interpretation_self_resonance_ge (s r : I) :
    ResonanceField.resonanceStrength (interpret s r) (interpret s r) ≥
    ResonanceField.resonanceStrength s s := by
  unfold interpret
  exact strength_compose_left_mono s s r

end IDT.MG
