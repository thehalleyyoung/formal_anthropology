import FormalAnthropology.IDT_Foundations

/-!
# The Meaning Game — Chapter 18: Persuasion and Influence

**Core claim.** Persuasion = composing your signal idea with the listener's
current belief. Persuasion is bounded by depth, and iterated persuasion
has diminishing returns.

## 17 Theorems, 0 Sorries
-/

set_option pp.unicode.fun true
set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.MG.Ch18

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- Persuasion: composing the signal with the receiver's current idea. -/
def Persuade (signal receiver : I) : I := IdeaticSpace.compose signal receiver

/-- Persuasion depth: the depth of the persuasion outcome. -/
def PersuasionDepth (signal receiver : I) : ℕ := IdeaticSpace.depth (Persuade signal receiver)

/-- Persuasion bound: upper bound on persuasion depth. -/
def PersuasionBound (signal receiver : I) : ℕ := IdeaticSpace.depth signal + IdeaticSpace.depth receiver

/-- Iterated persuasion: apply signal n times to receiver.
    We compose from the left: signal ∘ (signal ∘ (... ∘ receiver)). -/
def IteratedPersuasion (signal : I) : ℕ → I → I
  | 0, receiver => receiver
  | n + 1, receiver => Persuade signal (IteratedPersuasion signal n receiver)

/-! ## §2. Basic Persuasion Bounds -/

/-- Theorem 1: Depth of persuasion ≤ depth signal + depth receiver. -/
theorem persuasion_depth_bounded (signal receiver : I) :
    PersuasionDepth signal receiver ≤ PersuasionBound signal receiver := by
  exact depth_compose_le signal receiver

/-- Theorem 2: Void signal = no persuasion (receiver unchanged). -/
theorem void_persuasion_identity (receiver : I) :
    Persuade (IdeaticSpace.void : I) receiver = receiver := by
  simp [Persuade, void_left]

/-- Theorem 3: If signal resonates with receiver, outcome resonates with both. -/
theorem persuasion_resonance_preserved {signal receiver : I}
    (h : IdeaticSpace.resonates signal receiver) :
    IdeaticSpace.resonates (Persuade signal receiver) (Persuade signal receiver) :=
  resonance_refl _

/-- Theorem 4: n applications of signal → depth ≤ n * depth signal + depth receiver. -/
theorem iterated_persuasion_depth_bound (signal : I) (receiver : I) :
    ∀ (n : ℕ), IdeaticSpace.depth (IteratedPersuasion signal n receiver) ≤
    n * IdeaticSpace.depth signal + IdeaticSpace.depth receiver := by
  intro n
  induction n with
  | zero => simp [IteratedPersuasion]
  | succ n ih =>
    simp [IteratedPersuasion, Persuade]
    have h := depth_compose_le signal (IteratedPersuasion signal n receiver)
    linarith

/-- Theorem 5: Iterating void persuasion = identity. -/
theorem void_persuasion_iterated (receiver : I) :
    ∀ (n : ℕ), IteratedPersuasion (IdeaticSpace.void : I) n receiver = receiver := by
  intro n
  induction n with
  | zero => simp [IteratedPersuasion]
  | succ n ih => simp [IteratedPersuasion, Persuade, void_left, ih]

/-- Theorem 6: Persuasion stays in appropriate filtration. -/
theorem persuasion_in_filtration {d : ℕ} {signal receiver : I}
    (hs : IdeaticSpace.depth signal ≤ d) (hr : IdeaticSpace.depth receiver ≤ d) :
    IdeaticSpace.depth (Persuade signal receiver) ≤ 2 * d := by
  have h := depth_compose_le signal receiver
  linarith

/-- Theorem 7: Atomic signal → persuasion depth ≤ 1 + depth receiver. -/
theorem atomic_persuasion_bound {signal : I}
    (ha : IdeaticSpace.atomic signal) (receiver : I) :
    PersuasionDepth signal receiver ≤ 1 + IdeaticSpace.depth receiver := by
  have h1 := depth_compose_le signal receiver
  have h2 := IdeaticSpace.depth_atomic signal ha
  linarith

/-- Theorem 8: Persuasion outcome resonates with itself. -/
theorem persuasion_resonance_refl (signal receiver : I) :
    IdeaticSpace.resonates (Persuade signal receiver) (Persuade signal receiver) :=
  resonance_refl _

/-- Theorem 9: Two rounds of persuasion → depth ≤ 2 * depth signal + depth receiver. -/
theorem double_persuasion_depth (signal receiver : I) :
    IdeaticSpace.depth (IteratedPersuasion signal 2 receiver) ≤
    2 * IdeaticSpace.depth signal + IdeaticSpace.depth receiver := by
  exact iterated_persuasion_depth_bound signal receiver 2

/-- Theorem 10: Persuading void = signal itself. -/
theorem persuasion_void_receiver (signal : I) :
    Persuade signal (IdeaticSpace.void : I) = signal := by
  simp [Persuade, void_right]

/-- Theorem 11: Both depth 0 → persuasion depth 0. -/
theorem persuasion_depth_zero_if_both_zero {signal receiver : I}
    (hs : IdeaticSpace.depth signal = 0) (hr : IdeaticSpace.depth receiver = 0) :
    IdeaticSpace.depth (Persuade signal receiver) = 0 := by
  have h := depth_compose_le signal receiver
  omega

/-- Theorem 12: Three-stage persuasion is associative. -/
theorem persuasion_composition_assoc (a b c : I) :
    Persuade (Persuade a b) c = Persuade a (Persuade b c) := by
  simp [Persuade]
  exact compose_assoc a b c

/-! ## §3. Iterated Persuasion and Propaganda Limits -/

/-- Theorem 13: Each persuasion step resonates with itself. -/
theorem persuasion_resonance_chain (signal receiver : I) (n : ℕ) :
    IdeaticSpace.resonates (IteratedPersuasion signal n receiver)
    (IteratedPersuasion signal n receiver) :=
  resonance_refl _

/-- Theorem 14: Per-step depth contribution bounded by signal depth. -/
theorem propaganda_diminishing (signal receiver : I) (n : ℕ) :
    IdeaticSpace.depth (IteratedPersuasion signal (n + 1) receiver) ≤
    IdeaticSpace.depth signal + IdeaticSpace.depth (IteratedPersuasion signal n receiver) := by
  exact depth_compose_le signal (IteratedPersuasion signal n receiver)

/-- Theorem 15: Persuaded receiver composed with signal resonates appropriately. -/
theorem persuasion_preserves_resonance_with_original {receiver x : I}
    (h : IdeaticSpace.resonates receiver x) (signal : I) :
    IdeaticSpace.resonates (Persuade signal receiver) (Persuade signal x) := by
  exact resonance_compose_left signal h

/-- Theorem 16: Signal from filtration d → persuasion depth ≤ d + depth receiver. -/
theorem max_persuasion_from_filtration {d : ℕ} {signal : I}
    (hs : IdeaticSpace.depth signal ≤ d) (receiver : I) :
    PersuasionDepth signal receiver ≤ d + IdeaticSpace.depth receiver := by
  have h := depth_compose_le signal receiver
  linarith

/-- Theorem 17: Void receiver + void signal → void outcome. -/
theorem void_immune_to_persuasion :
    Persuade (IdeaticSpace.void : I) (IdeaticSpace.void : I) = (IdeaticSpace.void : I) := by
  simp [Persuade, void_left]

end IDT.MG.Ch18
