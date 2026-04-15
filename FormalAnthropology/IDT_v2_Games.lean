import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.IDT_Foundations_v2

/-!
# IDT v2: Game Theory with Quantitative Resonance

Game-theoretic structures built on real-valued resonance strength.
Payoffs are real numbers, enabling optimization, dominance, and equilibrium.

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT2

section Games
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-! ## §1. Signaling Games -/

/-- A signaling game: sender chooses signal, receiver interprets -/
structure SignalingGame (I : Type*) [IdeaticSpace2 I] where
  sender : I
  receiver : I

/-- The signal-receiver interpretation -/
def SignalingGame.interpretation (g : SignalingGame I) : I :=
  interpret g.sender g.receiver

/-- Sender's payoff in a signaling game -/
noncomputable def SignalingGame.sPayoff (g : SignalingGame I) : ℝ :=
  senderPayoff g.sender g.receiver

/-- Receiver's payoff in a signaling game -/
noncomputable def SignalingGame.rPayoff (g : SignalingGame I) : ℝ :=
  receiverPayoff g.sender g.receiver

/-- Both payoffs are non-negative -/
theorem SignalingGame.sPayoff_nonneg (g : SignalingGame I) :
    g.sPayoff ≥ 0 := senderPayoff_nonneg g.sender g.receiver

theorem SignalingGame.rPayoff_nonneg (g : SignalingGame I) :
    g.rPayoff ≥ 0 := receiverPayoff_nonneg g.sender g.receiver

/-- Void receiver gives sender payoff = self-resonance -/
theorem sPayoff_void_receiver (s : I) :
    (SignalingGame.mk s (void : I)).sPayoff = resonanceStrength s s := by
  unfold SignalingGame.sPayoff; exact senderPayoff_void_receiver s

/-- Void signal gives receiver payoff = self-resonance -/
theorem rPayoff_void_signal (r : I) :
    (SignalingGame.mk (void : I) r).rPayoff = resonanceStrength r r := by
  unfold SignalingGame.rPayoff; exact receiverPayoff_void_signal r

/-! ## §2. Dominance Relations -/

/-- Signal s₁ dominates s₂ for sender if it gives higher payoff against all receivers -/
def senderDominates (s₁ s₂ : I) : Prop :=
  ∀ (r : I), senderPayoff s₁ r ≥ senderPayoff s₂ r

theorem senderDominates_refl (s : I) : senderDominates s s :=
  fun _ => le_refl _

theorem senderDominates_trans (s₁ s₂ s₃ : I) :
    senderDominates s₁ s₂ → senderDominates s₂ s₃ → senderDominates s₁ s₃ := by
  intro h12 h23 r; exact le_trans (h23 r) (h12 r)

/-- Receiver r₁ dominates r₂ if it gives higher payoff against all signals -/
def receiverDominates (r₁ r₂ : I) : Prop :=
  ∀ (s : I), receiverPayoff s r₁ ≥ receiverPayoff s r₂

theorem receiverDominates_refl (r : I) : receiverDominates r r :=
  fun _ => le_refl _

theorem receiverDominates_trans (r₁ r₂ r₃ : I) :
    receiverDominates r₁ r₂ → receiverDominates r₂ r₃ → receiverDominates r₁ r₃ := by
  intro h12 h23 s; exact le_trans (h23 s) (h12 s)

/-! ## §3. Best Response -/

/-- r is a best response receiver -/
def isBestResponseReceiver (s r : I) : Prop :=
  ∀ (r' : I), receiverPayoff s r ≥ receiverPayoff s r'

/-- s is a best response signal -/
def isBestResponseSender (s r : I) : Prop :=
  ∀ (s' : I), senderPayoff s r ≥ senderPayoff s' r

/-- Void receiver always gives sender payoff ≥ 1 -/
theorem void_receiver_ge_one (s : I) :
    senderPayoff s (void : I) ≥ 1 := senderPayoff_void_receiver_ge_one s

/-- Void signal always gives receiver payoff ≥ 1 -/
theorem void_signal_ge_one (r : I) :
    receiverPayoff (void : I) r ≥ 1 := receiverPayoff_void_signal_ge_one r

/-! ## §4. Nash Equilibrium -/

/-- A Nash equilibrium: neither player can improve by deviating -/
def isNashEquilibrium (s r : I) : Prop :=
  isBestResponseSender s r ∧ isBestResponseReceiver s r

/-- Total payoff (social welfare) -/
noncomputable def totalPayoff (s r : I) : ℝ :=
  senderPayoff s r + receiverPayoff s r

theorem totalPayoff_nonneg (s r : I) : totalPayoff s r ≥ 0 := by
  unfold totalPayoff
  linarith [senderPayoff_nonneg (I := I) s r, receiverPayoff_nonneg (I := I) s r]

/-- Void-void game has total payoff = 2 -/
theorem totalPayoff_void_void :
    totalPayoff (void : I) (void : I) = 2 := by
  unfold totalPayoff
  rw [senderPayoff_void_receiver, receiverPayoff_void_signal, IdeaticSpace2.rs_void_self]
  ring

/-! ## §5. Cooperative Games -/

/-- Cooperative payoff: total resonance from joint interpretation -/
noncomputable def cooperativePayoff (a b : I) : ℝ :=
  resonanceStrength (compose a b) (compose a b)

theorem cooperativePayoff_ge_left (a b : I) :
    cooperativePayoff a b ≥ resonanceStrength a a := by
  unfold cooperativePayoff; exact rs_compose_self_right a b

theorem cooperativePayoff_ge_right (a b : I) :
    cooperativePayoff a b ≥ resonanceStrength b b := by
  unfold cooperativePayoff; exact rs_compose_self_left b a

theorem cooperativePayoff_ge_one (a b : I) :
    cooperativePayoff a b ≥ 1 := rs_compose_ge_one a b

/-- Cooperation gain: how much joint interpretation exceeds solo -/
noncomputable def cooperationGain (a b : I) : ℝ :=
  cooperativePayoff a b - resonanceStrength a a

theorem cooperationGain_nonneg (a b : I) : cooperationGain a b ≥ 0 := by
  unfold cooperationGain; linarith [cooperativePayoff_ge_left (I := I) a b]

theorem cooperationGain_void (a : I) : cooperationGain a (void : I) = 0 := by
  unfold cooperationGain cooperativePayoff; rw [IdeaticSpace2.void_right]; linarith

/-! ## §6. Iterated Games -/

/-- Iterated interpretation: signal interpreted n times by same receiver -/
def iteratedInterpret (s r : I) : ℕ → I
  | 0 => s
  | n + 1 => interpret (iteratedInterpret s r n) r

theorem iteratedInterpret_one (s r : I) :
    iteratedInterpret s r 1 = interpret s r := rfl

theorem iteratedInterpret_void : ∀ (s : I) (n : ℕ),
    iteratedInterpret s (void : I) n = s
  | _, 0 => rfl
  | s, n + 1 => by
    simp [iteratedInterpret, interpret, iteratedInterpret_void s n]

/-- Self-resonance of iterated interpretations is non-decreasing -/
theorem iteratedInterpret_rs_mono (s r : I) (n : ℕ) :
    resonanceStrength (iteratedInterpret s r (n + 1))
                      (iteratedInterpret s r (n + 1)) ≥
    resonanceStrength (iteratedInterpret s r n)
                      (iteratedInterpret s r n) := by
  simp only [iteratedInterpret, interpret]
  exact rs_compose_self_left (iteratedInterpret s r n) r

/-! ## §7. Multi-Player Resonance -/

/-- Group resonance = total pairwise resonance -/
noncomputable def groupResonance (agents : List I) : ℝ :=
  totalResonance agents

theorem groupResonance_pair (a b : I) :
    groupResonance [a, b] = resonanceStrength a b :=
  totalResonance_pair a b

theorem groupResonance_nil : groupResonance ([] : List I) = 0 :=
  totalResonance_nil

theorem groupResonance_pair_nonneg (a b : I) :
    groupResonance [a, b] ≥ 0 := totalResonance_pair_nonneg a b

end Games
end IDT2
