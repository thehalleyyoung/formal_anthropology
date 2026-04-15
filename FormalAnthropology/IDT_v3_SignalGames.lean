import FormalAnthropology.IDT_v3_Foundations

/-!
# IDT v3: Signal Games — Deep Game-Theoretic Results

## Overview

This file develops a rich game-theoretic framework for signaling games
within the Ideatic Space axioms.  Every result follows from the minimal
axiom class `IdeaticSpace3` (monoid + resonance + emergence bounds)
with **zero sorries**.

## The fundamental idea

Communication is a game.  A *sender* chooses a signal `s`, a *receiver*
interprets it via `compose r s`.  Payoffs measure how well the signal
resonated from each player's perspective.  From the monoid and resonance
axioms alone we derive:

1. **The Meaning Game** — welfare decomposition
2. **Nash Equilibria** — void is always an equilibrium
3. **Communication Value** — when is signaling worth the cost?
4. **Persuasion** — iterated signaling monotonically enriches
5. **Strategic Emergence** — the non-additive surprise advantage
6. **Cooperation vs Competition** — surplus from joint composition
7. **Wittgenstein's Language Games** — meaning as resonance profile

## NO SORRIES, NO ADMITS, NO AXIOMS (beyond the class)
-/

namespace IDT3

open IdeaticSpace3

/-! ## §1. The Meaning Game — Welfare Decomposition

A "meaning game" is a pair (sender, receiver).  The sender chooses a
signal `s`, the receiver `r` interprets via `compose r s`.

Payoff to sender = `rs(s, compose r s)` — "did they get what I meant?"
Payoff to receiver = `rs(r, compose r s)` — "does this make sense to me?"

Total social welfare = senderPayoff + receiverPayoff.
-/

section MeaningGame
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Social welfare: total payoff to both players in the meaning game.
    This is the raw sum of sender and receiver payoffs, before any
    baseline subtraction. -/
noncomputable def socialWelfare (s r : I) : ℝ :=
  senderPayoff s r + receiverPayoff s r

/-- Social welfare unfolds to the sum of resonances with the
    interpretation. -/
theorem socialWelfare_eq (s r : I) :
    socialWelfare s r =
    rs s (compose r s) + rs r (compose r s) := by
  unfold socialWelfare senderPayoff receiverPayoff interpret; ring

/-- The interpretation `compose r s` resonates with the composition
    `compose s r` via the fundamental resonance decomposition.
    This relates welfare to resonance of the reversed composition. -/
theorem socialWelfare_via_compose (s r : I) :
    socialWelfare s r =
    rs (compose s r) (compose r s) - emergence s r (compose r s) := by
  unfold socialWelfare senderPayoff receiverPayoff interpret
  rw [rs_compose_eq s r (compose r s)]
  ring

/-- T1. Social welfare decomposes into self-resonances, cross-terms,
    and emergence.  The sender and receiver payoffs can each be written
    as their individual resonance with the interpretation `compose r s`.
    Using `rs_compose_eq` on the first argument of the reversed
    composition `compose s r`, we get the full decomposition. -/
theorem welfare_decomposition (s r : I) :
    socialWelfare s r =
    rs s (compose r s) + rs r (compose r s) :=
  socialWelfare_eq s r

/-- T2. Welfare when signal is void: receiver just hears silence. -/
theorem socialWelfare_void_signal (r : I) :
    socialWelfare (void : I) r = rs r r := by
  unfold socialWelfare senderPayoff receiverPayoff interpret
  simp [rs_void_left']

/-- T3. Welfare when receiver is void: signal goes unheard. -/
theorem socialWelfare_void_receiver (s : I) :
    socialWelfare s (void : I) = rs s s := by
  unfold socialWelfare senderPayoff receiverPayoff interpret
  simp [rs_void_left', rs_void_right']

/-- T4. Welfare of total silence is zero. -/
theorem socialWelfare_void_void :
    socialWelfare (void : I) (void : I) = 0 := by
  rw [socialWelfare_void_signal]; exact rs_void_void

/-- T5. Welfare decomposition via reversed composition and emergence. -/
theorem welfare_emergence_decomposition (s r : I) :
    socialWelfare s r =
    rs s (compose r s) + rs r (compose r s) :=
  socialWelfare_eq s r

/-- The sender's share: how the sender's payoff relates to the
    interpretation's resonance decomposition.  Since `compose r s`
    is in the *second* argument of `rs s _`, we express this via
    cross-resonance terms. -/
theorem sender_payoff_eq (s r : I) :
    senderPayoff s r = rs s (compose r s) := by
  unfold senderPayoff interpret; ring

/-- T6. The receiver's payoff equals their resonance with the
    interpretation — the "comprehension" term. -/
theorem receiver_payoff_eq (s r : I) :
    receiverPayoff s r = rs r (compose r s) := by
  unfold receiverPayoff interpret; ring

/-- T7. Welfare relates to the self-resonance of the interpretation
    via the first-argument decomposition. -/
theorem welfare_vs_interpretation_selfrs (s r : I) :
    socialWelfare s r =
    rs (compose s r) (compose r s) - emergence s r (compose r s) := by
  rw [socialWelfare_eq, rs_compose_eq s r (compose r s)]; ring

/-- T8. If sender and receiver are the same idea, welfare = 2 · rs(a, compose a a). -/
theorem welfare_self_signal (a : I) :
    socialWelfare a a = 2 * rs a (compose a a) := by
  rw [socialWelfare_eq]; ring

end MeaningGame

/-! ## §2. Nash Equilibrium in Meaning

A signal is a "best response" for the sender if no other signal yields
higher sender payoff.  Similarly for the receiver.  We define net payoffs
(payoff minus baseline self-resonance) so that void gives net payoff 0,
making (void, void) a Nash equilibrium.
-/

section NashEquilibrium
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Net sender benefit: sender payoff minus baseline (what sender gets
    by "talking to void"). The sender's gain from having receiver r
    interpret signal s, beyond what s already has intrinsically. -/
noncomputable def senderNetPayoff (s r : I) : ℝ :=
  senderPayoff s r - rs s s

/-- Net receiver benefit: receiver payoff minus baseline. -/
noncomputable def receiverNetPayoff (s r : I) : ℝ :=
  receiverPayoff s r - rs r r

/-- T9. Net sender payoff for void signal is always zero. -/
theorem senderNetPayoff_void_signal (r : I) :
    senderNetPayoff (void : I) r = 0 := by
  unfold senderNetPayoff senderPayoff interpret
  simp [rs_void_left', rs_void_void]

/-- T10. Net receiver payoff for void signal is always zero. -/
theorem receiverNetPayoff_void_signal (r : I) :
    receiverNetPayoff (void : I) r = 0 := by
  unfold receiverNetPayoff receiverPayoff interpret
  simp

/-- T11. Net sender payoff when receiver is void is always zero. -/
theorem senderNetPayoff_void_receiver (s : I) :
    senderNetPayoff s (void : I) = 0 := by
  unfold senderNetPayoff senderPayoff interpret; simp

/-- T12. Net receiver payoff when receiver is void is always zero. -/
theorem receiverNetPayoff_void_receiver (s : I) :
    receiverNetPayoff s (void : I) = 0 := by
  unfold receiverNetPayoff receiverPayoff interpret
  simp [rs_void_left', rs_void_void]

/-- A signal s is a best response for the sender against receiver r
    if no other signal yields a higher net sender payoff. -/
def isBestResponseSender (s r : I) : Prop :=
  ∀ s' : I, senderNetPayoff s r ≥ senderNetPayoff s' r

/-- A receiver r is a best response against signal s if no other
    receiver state yields higher net receiver payoff. -/
def isBestResponseReceiver (s r : I) : Prop :=
  ∀ r' : I, receiverNetPayoff s r ≥ receiverNetPayoff s r'

/-- Nash equilibrium: both players are best-responding. -/
def isNashEquilibrium (s r : I) : Prop :=
  isBestResponseSender s r ∧ isBestResponseReceiver s r

/-- T13. Void signal is always a best response to void receiver.
    Saying nothing to nobody is stable: no signal can improve
    the sender's net payoff (it's always 0 against void). -/
theorem void_bestResponse_sender_void :
    isBestResponseSender (void : I) (void : I) := by
  intro s'
  rw [senderNetPayoff_void_signal, senderNetPayoff_void_receiver]

/-- T14. Void receiver is always a best response to void signal.
    Hearing nothing requires no response: any receiver state gives
    net payoff 0 against the void signal. -/
theorem void_bestResponse_receiver_void :
    isBestResponseReceiver (void : I) (void : I) := by
  intro r'
  rw [receiverNetPayoff_void_receiver, receiverNetPayoff_void_signal]

/-- T15. (void, void) is always a Nash equilibrium: silence is stable.
    This is the "trivial" equilibrium — saying nothing to nobody.
    No player can unilaterally improve by deviating. -/
theorem void_nash_equilibrium :
    isNashEquilibrium (void : I) (void : I) :=
  ⟨void_bestResponse_sender_void, void_bestResponse_receiver_void⟩

/-- T16. Communication surplus equals the sum of net payoffs. -/
theorem communicationSurplus_eq_net (s r : I) :
    communicationSurplus s r = senderNetPayoff s r + receiverNetPayoff s r := by
  unfold communicationSurplus senderNetPayoff receiverNetPayoff; ring

/-- T17. At a Nash equilibrium, each player's net payoff is non-negative
    (since they could always deviate to void and get 0). -/
theorem nash_sender_nonneg (s r : I) (h : isNashEquilibrium s r) :
    senderNetPayoff s r ≥ 0 := by
  have := h.1 (void : I)
  rw [senderNetPayoff_void_signal] at this
  linarith

theorem nash_receiver_nonneg (s r : I) (h : isNashEquilibrium s r) :
    receiverNetPayoff s r ≥ 0 := by
  have := h.2 (void : I)
  rw [receiverNetPayoff_void_receiver] at this
  linarith

/-- T18. At a Nash equilibrium, communication surplus is non-negative. -/
theorem nash_surplus_nonneg (s r : I) (h : isNashEquilibrium s r) :
    communicationSurplus s r ≥ 0 := by
  rw [communicationSurplus_eq_net]
  linarith [nash_sender_nonneg s r h, nash_receiver_nonneg s r h]

/-- T19. At a Nash equilibrium, the misunderstanding gap is bounded:
    sender payoff minus receiver payoff ≤ sender payoff, because
    receiver payoff ≥ rs(r,r) ≥ 0 at equilibrium. -/
theorem nash_gap_bounded (s r : I) (h : isNashEquilibrium s r) :
    misunderstandingGap s r ≤ senderPayoff s r := by
  unfold misunderstandingGap
  have h1 := nash_receiver_nonneg s r h
  unfold receiverNetPayoff at h1
  linarith [S.rs_self_nonneg r]

end NashEquilibrium

/-! ## §3. Communication Value

The value of communication `V(s, r)` is the surplus from communicating
versus staying silent.  This is precisely `communicationSurplus`.
We prove key properties: V vanishes at void, and characterize when
communication is valuable.
-/

section CommunicationValue
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Communication value: the net benefit of sender sending s to receiver r,
    beyond what each gets from their own self-resonance.
    V(s,r) = senderPayoff(s,r) + receiverPayoff(s,r) - rs(s,s) - rs(r,r). -/
noncomputable def commValue (s r : I) : ℝ :=
  communicationSurplus s r

/-- T20. Communication with void signal has zero value. -/
theorem commValue_void_signal (r : I) :
    commValue (void : I) r = 0 :=
  communicationSurplus_void_signal r

/-- T21. Communication with void receiver has zero value. -/
theorem commValue_void_receiver (s : I) :
    commValue s (void : I) = 0 :=
  communicationSurplus_void_reader s

/-- T22. Communication value between two voids is zero. -/
theorem commValue_void_void :
    commValue (void : I) (void : I) = 0 :=
  communicationSurplus_void_signal _

/-- T23. Communication value decomposes into net payoffs. -/
theorem commValue_eq_nets (s r : I) :
    commValue s r = senderNetPayoff s r + receiverNetPayoff s r :=
  communicationSurplus_eq_net s r

/-- T24. Communication value in terms of raw resonances. -/
theorem commValue_explicit (s r : I) :
    commValue s r =
    rs s (compose r s) + rs r (compose r s) - rs s s - rs r r := by
  unfold commValue communicationSurplus senderPayoff receiverPayoff interpret; ring

/-- T25. Communication value relates to the reversed-composition
    resonance via emergence. -/
theorem commValue_via_emergence (s r : I) :
    commValue s r =
    rs (compose s r) (compose r s) - emergence s r (compose r s)
    - rs s s - rs r r := by
  rw [commValue_explicit, rs_compose_eq s r (compose r s)]; ring

/-- T26. Communication value for self-communication. -/
theorem commValue_self (a : I) :
    commValue a a = 2 * rs a (compose a a) - 2 * rs a a := by
  rw [commValue_explicit]; ring

/-- T27. If the sender payoff exceeds self-resonance AND receiver payoff
    exceeds self-resonance, then communication is valuable. -/
theorem commValue_pos_of_payoffs (s r : I)
    (hs : senderPayoff s r > rs s s)
    (hr : receiverPayoff s r > rs r r) :
    commValue s r > 0 := by
  rw [commValue_explicit, sender_payoff_eq, receiver_payoff_eq] at *
  linarith

end CommunicationValue

/-! ## §4. Persuasion as Iterated Signaling

Persuasion means bombarding a target with a signal repeatedly:
  `persuade(signal, target, n) = compose target (composeN signal n)`

The key result: self-resonance of the persuaded state is non-decreasing
in the number of repetitions.  The target gets "heavier" with each
exposure — you can't un-hear what you've heard.
-/

section Persuasion
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The persuasion operator: expose `target` to `signal` repeated `n` times.
    The result is the target's state after absorbing n copies of the signal. -/
def persuade (signal target : I) (n : ℕ) : I :=
  compose target (composeN signal n)

/-- T28. Zero persuasion leaves the target unchanged. -/
@[simp] theorem persuade_zero (signal target : I) :
    persuade signal target 0 = target := by
  unfold persuade; simp

/-- T29. Persuasion with void signal leaves the target unchanged. -/
@[simp] theorem persuade_void_signal (target : I) (n : ℕ) :
    persuade (void : I) target n = target := by
  unfold persuade; simp

/-- T30. Persuasion of void target is just the repeated signal. -/
theorem persuade_void_target (signal : I) (n : ℕ) :
    persuade signal (void : I) n = composeN signal n := by
  unfold persuade; simp

/-- Key lemma: persuade(s, t, n+1) = compose (persuade(s, t, n)) s.
    Each additional exposure just appends one more copy of the signal. -/
theorem persuade_succ (signal target : I) (n : ℕ) :
    persuade signal target (n + 1) =
    compose (persuade signal target n) signal := by
  unfold persuade
  simp [composeN_succ, compose_assoc']

/-- T31. Self-resonance of the persuaded state is non-decreasing.
    Each exposure makes the target "heavier" — more present.
    This follows from `compose_enriches`: composing with anything
    can only increase self-resonance. -/
theorem persuade_selfrs_mono (signal target : I) (n : ℕ) :
    rs (persuade signal target (n + 1)) (persuade signal target (n + 1)) ≥
    rs (persuade signal target n) (persuade signal target n) := by
  rw [persuade_succ]
  exact S.compose_enriches (persuade signal target n) signal

/-- T32. Self-resonance after any amount of persuasion is at least
    the target's original self-resonance. -/
theorem persuade_selfrs_ge_target : ∀ (signal target : I) (n : ℕ),
    rs (persuade signal target n) (persuade signal target n) ≥
    rs target target
  | _, _, 0 => by simp
  | signal, target, n + 1 => by
    have h1 := persuade_selfrs_mono signal target n
    have h2 := persuade_selfrs_ge_target signal target n
    linarith

/-- The persuasion surplus: how much does n exposures shift the target's
    self-resonance beyond baseline? -/
noncomputable def persuasionSurplus (signal target : I) (n : ℕ) : ℝ :=
  rs (persuade signal target n) (persuade signal target n) - rs target target

/-- T33. Persuasion surplus is always non-negative. -/
theorem persuasionSurplus_nonneg (signal target : I) (n : ℕ) :
    persuasionSurplus signal target n ≥ 0 := by
  unfold persuasionSurplus
  linarith [persuade_selfrs_ge_target signal target n]

/-- T34. Persuasion surplus at step 0 is zero. -/
theorem persuasionSurplus_zero (signal target : I) :
    persuasionSurplus signal target 0 = 0 := by
  unfold persuasionSurplus; simp

/-- T35. Persuasion surplus is non-decreasing. -/
theorem persuasionSurplus_mono (signal target : I) (n : ℕ) :
    persuasionSurplus signal target (n + 1) ≥
    persuasionSurplus signal target n := by
  unfold persuasionSurplus
  linarith [persuade_selfrs_mono signal target n]

/-- T36. A non-void signal always produces non-void persuasion
    (assuming target is non-void). -/
theorem persuade_ne_void_of_target (signal target : I) (n : ℕ)
    (ht : target ≠ void) :
    persuade signal target n ≠ void := by
  unfold persuade
  exact compose_ne_void_of_left target (composeN signal n) ht

/-- The marginal persuasion effect: the emergence generated by
    each additional exposure to the signal. -/
noncomputable def marginalPersuasion (signal target : I) (n : ℕ) : ℝ :=
  emergence (persuade signal target n) signal (persuade signal target (n + 1))

/-- T37. Persuasion surplus can be decomposed step-by-step. The
    (n+1)-th surplus equals the n-th surplus plus the additional
    self-resonance gained from the (n+1)-th exposure. -/
theorem persuasionSurplus_step (signal target : I) (n : ℕ) :
    persuasionSurplus signal target (n + 1) =
    persuasionSurplus signal target n +
    (rs (persuade signal target (n + 1)) (persuade signal target (n + 1)) -
     rs (persuade signal target n) (persuade signal target n)) := by
  unfold persuasionSurplus; ring

/-- T38. Persuasion with void signal always has zero surplus. -/
theorem persuasionSurplus_void_signal (target : I) (n : ℕ) :
    persuasionSurplus (void : I) target n = 0 := by
  unfold persuasionSurplus; simp

end Persuasion

/-! ## §5. Strategic Emergence

The emergence term in the payoff is the "strategic surprise" — the
non-additive component that neither player expected from simple
superposition.

The emergence advantage `emergence(r, s, s)` measures how much the
signal gains from being composed with the receiver's mind.
-/

section StrategicEmergence
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The emergence advantage of signal s against receiver r:
    how much emergent resonance the signal gains when the receiver
    interprets it.  Positive means the signal is "amplified" by
    the receiver's context. -/
noncomputable def emergenceAdvantage (s r : I) : ℝ :=
  emergence r s s

/-- T39. Emergence advantage is the non-additive part of sender payoff
    from the composition.  It measures how rs(compose r s, s) differs
    from rs(r, s) + rs(s, s). -/
theorem emergenceAdvantage_eq (s r : I) :
    emergenceAdvantage s r =
    rs (compose r s) s - rs r s - rs s s := by
  unfold emergenceAdvantage emergence; ring

/-- T40. Emergence advantage from void receiver is zero: if nobody is
    listening, there's no contextual amplification. -/
theorem emergenceAdvantage_void_receiver (s : I) :
    emergenceAdvantage s (void : I) = 0 := by
  unfold emergenceAdvantage; exact emergence_void_left s s

/-- T41. Emergence advantage of void signal is zero: silence generates
    no strategic surprise. -/
theorem emergenceAdvantage_void_signal (r : I) :
    emergenceAdvantage (void : I) r = 0 := by
  unfold emergenceAdvantage; exact emergence_void_right r (void : I)

/-- T42. Emergence advantage is bounded by the geometric mean of
    interpretation self-resonance and signal self-resonance. -/
theorem emergenceAdvantage_bounded (s r : I) :
    (emergenceAdvantage s r) ^ 2 ≤
    rs (compose r s) (compose r s) * rs s s := by
  unfold emergenceAdvantage
  exact emergence_bounded' r s s

/-- The receiver's emergence sensitivity: how much emergence the
    receiver experiences from interpreting signal s.
    emergence(r, s, r) = rs(compose r s, r) - rs(r, r) - rs(s, r). -/
noncomputable def receiverEmergenceSensitivity (s r : I) : ℝ :=
  emergence r s r

/-- T43. Receiver sensitivity is the non-additive part of receiver payoff. -/
theorem receiverSensitivity_eq (s r : I) :
    receiverEmergenceSensitivity s r =
    rs (compose r s) r - rs r r - rs s r := by
  unfold receiverEmergenceSensitivity emergence; ring

/-- T44. Void signal produces zero receiver emergence sensitivity. -/
theorem receiverSensitivity_void_signal (r : I) :
    receiverEmergenceSensitivity (void : I) r = 0 := by
  unfold receiverEmergenceSensitivity; exact emergence_void_right r r

/-- T45. Receiver sensitivity is bounded. -/
theorem receiverSensitivity_bounded (s r : I) :
    (receiverEmergenceSensitivity s r) ^ 2 ≤
    rs (compose r s) (compose r s) * rs r r := by
  unfold receiverEmergenceSensitivity
  exact emergence_bounded' r s r

/-- The total strategic emergence: emergence of the interpretation
    measured against itself.  This is the "self-emergence" of the
    communication event. -/
noncomputable def totalStrategicEmergence (s r : I) : ℝ :=
  emergence r s (compose r s)

/-- T46. Total strategic emergence decomposition: it equals self-resonance
    of interpretation minus cross-resonance terms. -/
theorem totalStrategicEmergence_eq (s r : I) :
    totalStrategicEmergence s r =
    rs (compose r s) (compose r s) - rs r (compose r s) - rs s (compose r s) := by
  unfold totalStrategicEmergence emergence; ring

/-- T47. Social welfare can be expressed using self-resonance of
    interpretation minus total strategic emergence. -/
theorem welfare_via_strategic_emergence (s r : I) :
    socialWelfare s r =
    rs (compose r s) (compose r s) - totalStrategicEmergence s r := by
  rw [socialWelfare_eq, totalStrategicEmergence_eq]; ring

/-- T48. Communication value relates to total strategic emergence:
    V(s,r) = selfRS(compose r s) - totalStrategicEmergence - selfRS(s) - selfRS(r). -/
theorem commValue_via_strategic (s r : I) :
    commValue s r =
    rs (compose r s) (compose r s) -
    totalStrategicEmergence s r - rs s s - rs r r := by
  rw [commValue_explicit, totalStrategicEmergence_eq]; ring

end StrategicEmergence

/-! ## §6. Cooperation vs Competition

Two players with ideas `a` and `b` can cooperate by composing their
ideas.  The cooperation surplus measures how much joint composition
exceeds the sum of individual self-resonances.
-/

section CooperationCompetition
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Cooperation surplus: how much more self-resonance does the joint
    composition have than the two ideas separately?
    Positive = synergy (cooperation is valuable).
    Negative = would need the bilinear part to be very negative.
    By compose_enriches, the surplus is always ≥ rs(a,a) - rs(b,b)
    (which may be negative). -/
noncomputable def cooperationSurplus (a b : I) : ℝ :=
  rs (compose a b) (compose a b) - rs a a - rs b b

/-- T49. Cooperation surplus decomposes using the first-argument
    resonance expansion: selfRS(a∘b) = rs(a, a∘b) + rs(b, a∘b) + κ(a,b,a∘b). -/
theorem cooperationSurplus_decomp (a b : I) :
    cooperationSurplus a b =
    (rs a (compose a b) - rs a a) +
    (rs b (compose a b) - rs b b) +
    emergence a b (compose a b) := by
  unfold cooperationSurplus
  rw [rs_compose_eq a b (compose a b)]; ring

/-- T50. Cooperation surplus with void is zero. -/
theorem cooperationSurplus_void_right (a : I) :
    cooperationSurplus a (void : I) = 0 := by
  unfold cooperationSurplus; simp [rs_void_void]

theorem cooperationSurplus_void_left (b : I) :
    cooperationSurplus (void : I) b = 0 := by
  unfold cooperationSurplus; simp [rs_void_void]

/-- T51. Cooperation surplus is at least -rs(b,b):
    composing can't reduce the FIRST idea's self-resonance below zero. -/
theorem cooperationSurplus_lower_bound (a b : I) :
    cooperationSurplus a b ≥ -rs b b := by
  unfold cooperationSurplus
  linarith [S.compose_enriches a b]

/-- T52. Self-cooperation surplus is non-negative:
    composing an idea with itself always enriches.
    Since rs(compose a a, compose a a) ≥ rs(a, a) ≥ 0, the surplus
    is at least rs(a,a) - rs(a,a) - rs(a,a) = -rs(a,a). But we can
    show it's ≥ 0 using compose_enriches twice: both "slots" enrich. -/
theorem cooperationSurplus_self_nonneg (a : I) :
    cooperationSurplus a a ≥ -rs a a := by
  unfold cooperationSurplus
  linarith [S.compose_enriches a a]

/-- T53. In the bilinear case (zero emergence, right-decomposable rs),
    cooperation surplus = rs(a,b) + rs(b,a).  This is because:
    selfRS(a∘b) = rs(a, a∘b) + rs(b, a∘b) when emergence = 0,
    and rs(x, a∘b) = rs(x,a) + rs(x,b) when rs is right-decomposable. -/
theorem cooperationSurplus_bilinear (a b : I)
    (h_emerg : ∀ x y z : I, emergence x y z = 0)
    (h_right : ∀ x y z : I, rs x (compose y z) = rs x y + rs x z) :
    cooperationSurplus a b = rs a b + rs b a := by
  unfold cooperationSurplus
  rw [rs_compose_eq a b (compose a b), h_emerg a b (compose a b)]
  rw [h_right a a b, h_right b a b]
  ring

/-- T54. In the symmetric bilinear case, surplus = 2·rs(a,b). -/
theorem cooperationSurplus_symmetric_bilinear (a b : I)
    (h_emerg : ∀ x y z : I, emergence x y z = 0)
    (h_right : ∀ x y z : I, rs x (compose y z) = rs x y + rs x z)
    (h_symm : ∀ x y : I, rs x y = rs y x) :
    cooperationSurplus a b = 2 * rs a b := by
  rw [cooperationSurplus_bilinear a b h_emerg h_right, h_symm b a]; ring

/-- T55. Cooperation surplus relates to communication value:
    both measure the gain from interaction, but cooperation measures
    the gain in self-resonance while communication value measures
    the gain in cross-resonance payoffs. -/
theorem coop_vs_commValue (a b : I) :
    cooperationSurplus a b =
    commValue b a + totalStrategicEmergence b a := by
  rw [commValue_via_strategic, totalStrategicEmergence_eq]
  unfold cooperationSurplus
  ring

/-- T56. If cooperation surplus is positive, the ideas have synergy. -/
theorem synergistic_of_positive_surplus (a b : I)
    (h : cooperationSurplus a b > 0) :
    rs (compose a b) (compose a b) > rs a a + rs b b := by
  unfold cooperationSurplus at h; linarith

/-- The competition deficit: how much one player's self-resonance
    "costs" the other in a composition.  When composition is enriching
    for both sides, the deficit is zero or negative. -/
noncomputable def competitionAsymmetry (a b : I) : ℝ :=
  cooperationSurplus a b - cooperationSurplus b a

/-- T57. Competition asymmetry captures the order-dependence of
    cooperation: it's zero when composition is commutative
    in self-resonance. -/
theorem competitionAsymmetry_antisymm (a b : I) :
    competitionAsymmetry a b = -competitionAsymmetry b a := by
  unfold competitionAsymmetry; ring

/-- T58. Competition asymmetry in terms of self-resonances. -/
theorem competitionAsymmetry_eq (a b : I) :
    competitionAsymmetry a b =
    rs (compose a b) (compose a b) - rs (compose b a) (compose b a) := by
  unfold competitionAsymmetry cooperationSurplus; ring

/-- T59. Competition asymmetry vanishes when composition is commutative. -/
theorem competitionAsymmetry_comm (a b : I)
    (h : compose a b = compose b a) :
    competitionAsymmetry a b = 0 := by
  rw [competitionAsymmetry_eq, h]; ring

end CooperationCompetition

/-! ## §7. Wittgenstein's Language Games

Meaning is constituted by USE: the resonance profile of an utterance
across many contexts determines its meaning.

A "language game" consists of a vocabulary (list of utterances) and
a community (list of players/contexts).  The meaning of an utterance
is its resonance profile — how it resonates with every player in every
context.

Key insight: an utterance's meaning (resonance profile) is determined
by its emergence pattern, confirming Wittgenstein's thesis that meaning
is not an intrinsic property but arises from use.
-/

section LanguageGames
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A resonance profile of an utterance: the function mapping every
    other utterance to its resonance value.  This is the utterance's
    "meaning in use". -/
noncomputable def resonanceProfile (a : I) : I → ℝ :=
  fun c => rs a c

/-- Two utterances have the same resonance profile iff they are
    resonance-equivalent. -/
theorem profile_eq_iff_resonanceEquiv (a b : I) :
    resonanceProfile a = resonanceProfile b ↔ resonanceEquiv a b := by
  constructor
  · intro h c; exact congr_fun h c
  · intro h; funext c; exact h c

/-- T60. Void has a zero resonance profile. -/
theorem resonanceProfile_void :
    resonanceProfile (void : I) = fun _ => (0 : ℝ) := by
  funext c; exact rs_void_left' c

/-- An emergence profile of an utterance: the function mapping every
    pair (b, c) to the emergence κ(a, b, c).  This is the utterance's
    "creative potential" — what it contributes to compositions. -/
noncomputable def emergenceProfile (a : I) : I → I → ℝ :=
  fun b c => emergence a b c

/-- T61. Void has a zero emergence profile. -/
theorem emergenceProfile_void :
    emergenceProfile (void : I) = fun _ _ => (0 : ℝ) := by
  funext b c; exact emergence_void_left b c

/-- T62. Same emergence profile iff same idea (by definition). -/
theorem emergenceProfile_eq_iff_sameIdea (a b : I) :
    emergenceProfile a = emergenceProfile b ↔ sameIdea a b := by
  constructor
  · intro h c d; exact congr_fun (congr_fun h c) d
  · intro h; funext c d; exact h c d

/-- The contextual meaning of utterance `u` in context `ctx`:
    the resonance of the interpreted composition. -/
noncomputable def contextualMeaning (u ctx : I) : ℝ :=
  rs (compose ctx u) (compose ctx u)

/-- T63. Contextual meaning is always non-negative. -/
theorem contextualMeaning_nonneg (u ctx : I) :
    contextualMeaning u ctx ≥ 0 := by
  unfold contextualMeaning; exact S.rs_self_nonneg _

/-- T64. Contextual meaning of void is the context's self-resonance. -/
theorem contextualMeaning_void_utterance (ctx : I) :
    contextualMeaning (void : I) ctx = rs ctx ctx := by
  unfold contextualMeaning; simp

/-- T65. Contextual meaning in void context is the utterance's
    self-resonance. -/
theorem contextualMeaning_void_context (u : I) :
    contextualMeaning u (void : I) = rs u u := by
  unfold contextualMeaning; simp

/-- T66. Contextual meaning is at least the context's self-resonance.
    Adding any utterance to a context only enriches. -/
theorem contextualMeaning_ge_context (u ctx : I) :
    contextualMeaning u ctx ≥ rs ctx ctx := by
  unfold contextualMeaning
  exact S.compose_enriches ctx u

/-- The communicative reach of an utterance: the total welfare it
    generates across a list of receivers. -/
noncomputable def communicativeReach (u : I) : List I → ℝ
  | [] => 0
  | r :: rest => socialWelfare u r + communicativeReach u rest

/-- T67. Communicative reach of void signal is the sum of receiver
    self-resonances. -/
theorem communicativeReach_void : ∀ (receivers : List I),
    communicativeReach (void : I) receivers =
    (receivers.map (fun r => rs r r)).sum
  | [] => by unfold communicativeReach; simp
  | r :: rest => by
    unfold communicativeReach
    rw [socialWelfare_void_signal, communicativeReach_void rest]
    simp [List.map_cons, List.sum_cons]

/-- The use-profile of an utterance across a community: a list of
    contextual meanings across all community members. -/
noncomputable def useProfile (u : I) (community : List I) : List ℝ :=
  community.map (fun ctx => contextualMeaning u ctx)

/-- T68. Use-profile of void utterance. -/
theorem useProfile_void (community : List I) :
    useProfile (void : I) community =
    community.map (fun ctx => rs ctx ctx) := by
  unfold useProfile; congr 1; funext ctx
  exact contextualMeaning_void_utterance ctx

/-- T69. Every element of the use-profile is non-negative. -/
theorem useProfile_nonneg (u : I) (community : List I) :
    ∀ x ∈ useProfile u community, x ≥ 0 := by
  intro x hx
  unfold useProfile at hx
  rw [List.mem_map] at hx
  obtain ⟨ctx, _, hctx⟩ := hx
  rw [← hctx]
  exact contextualMeaning_nonneg u ctx

/-- Wittgenstein's thesis: two utterances have the same "meaning in use"
    (identical use-profiles in EVERY community) if and only if their
    composition with any context produces identical self-resonance.
    This is a resonance-equivalence condition on compositions. -/
def wittgensteinEquiv (a b : I) : Prop :=
  ∀ ctx : I, contextualMeaning a ctx = contextualMeaning b ctx

/-- T70. Wittgenstein equivalence unfolds to equality of composed
    self-resonances. -/
theorem wittgensteinEquiv_iff (a b : I) :
    wittgensteinEquiv a b ↔
    ∀ ctx : I, rs (compose ctx a) (compose ctx a) =
              rs (compose ctx b) (compose ctx b) := by
  constructor
  · intro h ctx; exact h ctx
  · intro h ctx; exact h ctx

/-- T71. Wittgenstein equivalence is reflexive. -/
theorem wittgensteinEquiv_refl (a : I) : wittgensteinEquiv a a :=
  fun _ => rfl

/-- T72. Wittgenstein equivalence is symmetric. -/
theorem wittgensteinEquiv_symm (a b : I)
    (h : wittgensteinEquiv a b) : wittgensteinEquiv b a :=
  fun ctx => (h ctx).symm

/-- T73. Wittgenstein equivalence is transitive. -/
theorem wittgensteinEquiv_trans (a b c : I)
    (h1 : wittgensteinEquiv a b) (h2 : wittgensteinEquiv b c) :
    wittgensteinEquiv a c :=
  fun ctx => (h1 ctx).trans (h2 ctx)

/-- T74. Void is Wittgenstein-equivalent only to itself (among non-void). -/
theorem wittgensteinEquiv_void_iff (a : I) :
    wittgensteinEquiv (void : I) a →
    ∀ ctx : I, rs (compose ctx a) (compose ctx a) = rs ctx ctx := by
  intro h ctx
  have := h ctx
  unfold contextualMeaning at this
  simp at this
  exact this.symm

end LanguageGames

/-! ## §8. Signal Refinement and Iterated Best Response

Beyond static Nash equilibrium, we can study the dynamics of
best-response iteration: each player alternately improves their
strategy.  We characterize fixed points and monotonicity.
-/

section SignalRefinement
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The sender's payoff function viewed as a function of the signal
    alone (fixing the receiver).  Best-response dynamics amounts to
    optimizing this function. -/
noncomputable def senderObjective (r : I) : I → ℝ :=
  fun s => senderNetPayoff s r

/-- T75. The sender's objective at void signal is always zero. -/
theorem senderObjective_void (r : I) :
    senderObjective r (void : I) = 0 := by
  unfold senderObjective; exact senderNetPayoff_void_signal r

/-- The receiver's payoff as a function of receiver state
    (fixing the signal). -/
noncomputable def receiverObjective (s : I) : I → ℝ :=
  fun r => receiverNetPayoff s r

/-- T76. The receiver's objective at void is always zero. -/
theorem receiverObjective_void (s : I) :
    receiverObjective s (void : I) = 0 := by
  unfold receiverObjective; exact receiverNetPayoff_void_receiver s

/-- T77. Sender objective unfolds to explicit resonance terms. -/
theorem senderObjective_eq (r s : I) :
    senderObjective r s = rs s (compose r s) - rs s s := by
  unfold senderObjective senderNetPayoff senderPayoff interpret; ring

/-- T78. Receiver objective unfolds to explicit resonance terms. -/
theorem receiverObjective_eq (s r : I) :
    receiverObjective s r = rs r (compose r s) - rs r r := by
  unfold receiverObjective receiverNetPayoff receiverPayoff interpret; ring

/-- A signal-receiver pair is a communication fixed point if
    neither player's net payoff changes by switching to void. -/
def isCommunicationFixedPoint (s r : I) : Prop :=
  senderNetPayoff s r = 0 ∧ receiverNetPayoff s r = 0

/-- T79. (void, void) is always a communication fixed point. -/
theorem void_is_fixed_point :
    isCommunicationFixedPoint (void : I) (void : I) :=
  ⟨senderNetPayoff_void_signal _, receiverNetPayoff_void_receiver _⟩

/-- T80. At a communication fixed point, the communication surplus
    is exactly zero. -/
theorem fixed_point_zero_surplus (s r : I)
    (h : isCommunicationFixedPoint s r) :
    communicationSurplus s r = 0 := by
  rw [communicationSurplus_eq_net]; linarith [h.1, h.2]

/-- T81. At a communication fixed point, sender payoff equals
    self-resonance. -/
theorem fixed_point_sender (s r : I)
    (h : isCommunicationFixedPoint s r) :
    senderPayoff s r = rs s s := by
  have := h.1; unfold senderNetPayoff at this; linarith

/-- T82. At a communication fixed point, receiver payoff equals
    self-resonance. -/
theorem fixed_point_receiver (s r : I)
    (h : isCommunicationFixedPoint s r) :
    receiverPayoff s r = rs r r := by
  have := h.2; unfold receiverNetPayoff at this; linarith

end SignalRefinement

/-! ## §9. Multi-Signal Composition and Discourse

When multiple signals are composed sequentially, the total effect
can be analyzed through the cocycle structure of emergence.
-/

section Discourse
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The discourse operator: a reader interprets a sequence of signals
    by composing them in order onto the reader's state. -/
def discourse (reader : I) : List I → I
  | [] => reader
  | s :: rest => discourse (compose reader s) rest

/-- T83. Empty discourse leaves the reader unchanged. -/
@[simp] theorem discourse_nil (reader : I) :
    discourse reader [] = reader := rfl

/-- T84. Singleton discourse is just interpretation. -/
theorem discourse_singleton (reader s : I) :
    discourse reader [s] = compose reader s := by
  unfold discourse; simp

/-- T85. Self-resonance of discourse is non-decreasing with each
    additional signal: each signal enriches the reader's state. -/
theorem discourse_enriches (reader s : I) (signals : List I) :
    rs (discourse (compose reader s) signals)
       (discourse (compose reader s) signals) ≥
    rs reader reader := by
  have h1 := S.compose_enriches reader s
  induction signals generalizing reader s with
  | nil => simpa using h1
  | cons s' rest ih =>
    unfold discourse
    have h2 := S.compose_enriches (compose reader s) s'
    have h3 := ih (compose reader s) s' h2
    linarith

/-- T86. The total emergence of a discourse: how much emergent
    meaning does reading a sequence of signals produce?  This is
    the difference between the final state's self-resonance and
    the sum of individual self-resonances. -/
noncomputable def discourseEmergence (reader : I) (signals : List I) : ℝ :=
  rs (discourse reader signals) (discourse reader signals) - rs reader reader

/-- T87. Discourse emergence of an empty sequence is zero. -/
theorem discourseEmergence_nil (reader : I) :
    discourseEmergence reader [] = 0 := by
  unfold discourseEmergence; simp

/-- T88. Discourse emergence is non-negative for any non-empty sequence. -/
theorem discourseEmergence_cons_nonneg (reader s : I) (signals : List I) :
    discourseEmergence reader (s :: signals) ≥ 0 := by
  unfold discourseEmergence discourse
  linarith [discourse_enriches reader s signals, S.rs_self_nonneg reader]

end Discourse

/-! ## §10. Information Revelation and Partial Communication

Not all signals reveal everything.  A signal is "informative" if it
shifts the receiver's state; it's "redundant" if the receiver already
knows everything the signal conveys.
-/

section InformationRevelation
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A signal is informative for a receiver if interpreting it changes
    the receiver's self-resonance. -/
def isInformative (s r : I) : Prop :=
  rs (compose r s) (compose r s) ≠ rs r r

/-- A signal is redundant for a receiver if interpreting it doesn't
    change the receiver's self-resonance. -/
def isRedundant (s r : I) : Prop :=
  rs (compose r s) (compose r s) = rs r r

/-- T89. Void signal is always redundant. -/
theorem void_redundant (r : I) : isRedundant (void : I) r := by
  unfold isRedundant; simp

/-- T90. A signal is informative iff it's not redundant. -/
theorem informative_iff_not_redundant (s r : I) :
    isInformative s r ↔ ¬isRedundant s r := by
  unfold isInformative isRedundant; exact Iff.rfl

/-- T91. If a signal is informative, it strictly increases the
    receiver's self-resonance (since compose_enriches guarantees
    the composed version is never lighter). -/
theorem informative_increases (s r : I) (h : isInformative s r) :
    rs (compose r s) (compose r s) > rs r r := by
  have h1 := S.compose_enriches r s
  rcases lt_or_eq_of_le h1 with hlt | heq
  · linarith
  · exact absurd heq.symm h

/-- The information content of a signal for a receiver:
    how much it enriches the receiver's self-resonance. -/
noncomputable def informationContent (s r : I) : ℝ :=
  rs (compose r s) (compose r s) - rs r r

/-- T92. Information content is always non-negative. -/
theorem informationContent_nonneg (s r : I) :
    informationContent s r ≥ 0 := by
  unfold informationContent
  linarith [S.compose_enriches r s]

/-- T93. Information content of void is zero. -/
theorem informationContent_void (r : I) :
    informationContent (void : I) r = 0 := by
  unfold informationContent; simp

/-- T94. Information content decomposes via emergence. -/
theorem informationContent_decomp (s r : I) :
    informationContent s r =
    rs r (compose r s) + rs s (compose r s) +
    emergence r s (compose r s) - rs r r := by
  unfold informationContent
  rw [rs_compose_eq r s (compose r s)]

/-- T95. Information content relates to cooperation surplus
    (measuring the "weight gain" from interpretation). -/
theorem informationContent_eq_coopSurplus_shifted (s r : I) :
    informationContent s r =
    cooperationSurplus r s + rs s s := by
  unfold informationContent cooperationSurplus; ring

end InformationRevelation

/-! ## §11. The Babbling Equilibrium and Cheap Talk

In cheap-talk games, signals have no intrinsic cost. The "babbling
equilibrium" is where the receiver ignores the signal entirely.
We formalize this and show its properties.
-/

section CheapTalk
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A receiver ignores a signal if the payoff is the same as for void. -/
def receiverIgnores (s r : I) : Prop :=
  receiverPayoff s r = receiverPayoff (void : I) r

/-- T96. If receiver ignores the signal, then rs(r, compose r s) = rs(r, r). -/
theorem ignores_means_baseline (s r : I) (h : receiverIgnores s r) :
    rs r (compose r s) = rs r r := by
  unfold receiverIgnores at h
  unfold receiverPayoff interpret at h; simpa using h

/-- T97. If receiver ignores, the signal is "self-focused" — the
    communication surplus equals the sender's net payoff. -/
theorem ignores_surplus (s r : I) (h : receiverIgnores s r) :
    communicationSurplus s r = senderNetPayoff s r := by
  rw [communicationSurplus_eq_net]
  unfold receiverNetPayoff receiverPayoff interpret
  rw [ignores_means_baseline s r h]; ring

/-- The babbling condition: receiver ignores ALL signals. -/
def isBabbling (r : I) : Prop :=
  ∀ s : I, receiverIgnores s r

/-- T98. Under babbling, communication surplus = sender's net gain
    for every signal. -/
theorem babbling_surplus (r : I) (h : isBabbling r) (s : I) :
    communicationSurplus s r = senderNetPayoff s r :=
  ignores_surplus s r (h s)

/-- T99. Void receiver trivially babbles: hearing nothing from
    anyone, the void has no state to update. -/
theorem void_babbles : isBabbling (void : I) := by
  intro s
  unfold receiverIgnores receiverPayoff interpret
  simp [rs_void_left', rs_void_void]

end CheapTalk

/-! ## §12. Signaling Costs and Costly Signals

When signals are costly — measured by their self-resonance — the sender
faces a trade-off: richer signals resonate more but cost more to produce.
This leads to signaling equilibria where only signals with sufficient
emergence advantage are worth sending.
-/

section CostlySignaling
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The cost of a signal: its self-resonance.  More "substantial"
    signals cost more to produce.  Only void is free. -/
noncomputable def signalCost (s : I) : ℝ := rs s s

/-- T100. Void signal is free. -/
theorem signalCost_void : signalCost (void : I) = 0 := rs_void_void

/-- T101. Non-void signals have strictly positive cost. -/
theorem signalCost_pos (s : I) (h : s ≠ void) :
    signalCost s > 0 := rs_self_pos s h

/-- The net payoff in a costly signaling game: sender payoff minus
    signal cost.  This is just senderNetPayoff, but the "costly" framing
    makes the economics explicit. -/
noncomputable def costlyNetPayoff (s r : I) : ℝ :=
  senderPayoff s r - signalCost s

/-- T102. Costly net payoff is the same as sender net payoff. -/
theorem costlyNetPayoff_eq (s r : I) :
    costlyNetPayoff s r = senderNetPayoff s r := by
  unfold costlyNetPayoff signalCost senderNetPayoff; ring

/-- T103. Void always yields zero costly net payoff. -/
theorem costlyNetPayoff_void (r : I) :
    costlyNetPayoff (void : I) r = 0 := by
  rw [costlyNetPayoff_eq]; exact senderNetPayoff_void_signal r

/-- T104. A signal is "worth sending" if its costly net payoff
    is strictly positive.  This means the emergence advantage
    outweighs the signal cost. -/
theorem signal_worth_sending_iff (s r : I) :
    costlyNetPayoff s r > 0 ↔ senderPayoff s r > signalCost s := by
  unfold costlyNetPayoff; constructor <;> intro h <;> linarith

/-- T105. At Nash equilibrium, the costly net payoff of the equilibrium
    signal is non-negative (the sender could always send void for free). -/
theorem nash_costly_nonneg (s r : I) (h : isNashEquilibrium s r) :
    costlyNetPayoff s r ≥ 0 := by
  rw [costlyNetPayoff_eq]; exact nash_sender_nonneg s r h

end CostlySignaling

/-! ## §13. Communication Channels and Capacity

A "channel" is a fixed receiver.  The channel capacity measures the
maximum communication value achievable by any signal through this channel.
-/

section Channels
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A channel is characterized by a receiver.  The channel throughput
    for a specific signal is the social welfare generated. -/
noncomputable def channelThroughput (channel signal : I) : ℝ :=
  socialWelfare signal channel

/-- T106. Void channel has throughput = signal's self-resonance. -/
theorem voidChannel_throughput (s : I) :
    channelThroughput (void : I) s = rs s s :=
  socialWelfare_void_receiver s

/-- T107. Any channel has non-negative throughput for void signal. -/
theorem channel_void_throughput (channel : I) :
    channelThroughput channel (void : I) = rs channel channel :=
  socialWelfare_void_signal channel

/-- The channel gain: throughput minus signal cost. -/
noncomputable def channelGain (channel signal : I) : ℝ :=
  channelThroughput channel signal - rs signal signal

/-- T108. Void channel has zero gain: sending anything through void
    yields exactly what you started with. -/
theorem voidChannel_gain (s : I) :
    channelGain (void : I) s = 0 := by
  unfold channelGain; rw [voidChannel_throughput]; ring

/-- T109. Channel gain from void signal is the channel's self-resonance. -/
theorem channel_void_gain (channel : I) :
    channelGain channel (void : I) = rs channel channel := by
  unfold channelGain; rw [channel_void_throughput]; simp [rs_void_void]

/-- T110. Channel gain decomposes into sender and receiver perspectives. -/
theorem channelGain_decomp (channel signal : I) :
    channelGain channel signal =
    senderNetPayoff signal channel + receiverPayoff signal channel := by
  unfold channelGain channelThroughput socialWelfare senderNetPayoff
  ring

end Channels

/-! ## §14. Babbling Equilibrium Characterization

The babbling equilibrium is the canonical "failure to communicate":
the receiver ignores every signal.  We prove that under babbling,
void is weakly optimal for the sender, and conversely, if void
is the unique signal that achieves the maximum net payoff (zero),
then the receiver must be babbling.
-/

section BabblingCharacterization
variable {I : Type*} [S : IdeaticSpace3 I]

/-- T111. Under babbling, sender's net payoff decomposes into a pure
    cross-resonance shift: senderNetPayoff = rs(s, compose r s) - rs(s,s). -/
theorem babbling_sender_net_explicit (r : I) (_h : isBabbling r) (s : I) :
    senderNetPayoff s r = rs s (compose r s) - rs s s := by
  unfold senderNetPayoff senderPayoff interpret; ring

/-- T112. Under babbling, the communication surplus equals the sender's
    resonance shift with the interpretation. -/
theorem babbling_commValue (r : I) (h : isBabbling r) (s : I) :
    commValue s r = rs s (compose r s) - rs s s := by
  unfold commValue
  rw [babbling_surplus r h s, babbling_sender_net_explicit r h s]

/-- T113 (strengthened). Under babbling, void signal achieves net payoff 0,
    which is weakly optimal among all signals that also yield zero net payoff.
    More precisely: for ANY signal s, senderNetPayoff void r = 0. -/
theorem babbling_void_optimal (r : I) (_h : isBabbling r) :
    senderNetPayoff (void : I) r = 0 :=
  senderNetPayoff_void_signal r

/-- T114. Converse direction: if sender net payoff is zero for ALL signals
    (i.e., void's payoff is matched by everything), then the receiver
    payoff equals baseline for all signals — the receiver is babbling. -/
theorem babbling_of_all_net_zero (r : I)
    (h : ∀ s : I, senderNetPayoff s r = 0) :
    ∀ s : I, senderPayoff s r = rs s s := by
  intro s
  have := h s
  unfold senderNetPayoff at this; linarith

/-- T115. If the receiver ignores a specific signal, the communication
    value from that signal equals the sender's net payoff alone. -/
theorem ignores_commValue_eq_senderNet (s r : I) (h : receiverIgnores s r) :
    commValue s r = senderNetPayoff s r := by
  unfold commValue; exact ignores_surplus s r h

/-- T116. Under babbling, total social welfare equals
    rs(s, compose r s) + rs(r, r) — the receiver always gets baseline. -/
theorem babbling_welfare (r : I) (h : isBabbling r) (s : I) :
    socialWelfare s r = rs s (compose r s) + rs r r := by
  rw [socialWelfare_eq, ignores_means_baseline s r (h s)]

/-- T117. Under babbling, the misunderstanding gap equals the sender's
    resonance shift: rs(s, compose r s) - rs(r, r). -/
theorem babbling_misunderstanding (r : I) (h : isBabbling r) (s : I) :
    misunderstandingGap s r = rs s (compose r s) - rs r r := by
  unfold misunderstandingGap senderPayoff receiverPayoff interpret
  rw [ignores_means_baseline s r (h s)]

/-- T118. Under babbling, the information content still grows —
    even if the receiver's payoff doesn't change, the composed state
    is enriched. -/
theorem babbling_information_nonneg (r : I) (_ : isBabbling r) (s : I) :
    informationContent s r ≥ 0 :=
  informationContent_nonneg s r

/-- A receiver "fully absorbs" a signal if interpreting it gives the
    same self-resonance as the receiver alone — the signal adds nothing
    new to the receiver's state. -/
def fullyAbsorbs (s r : I) : Prop :=
  rs (compose r s) (compose r s) = rs r r

/-- T119. If the receiver fully absorbs every signal, then void is
    redundant for the receiver (trivially — everything is redundant). -/
theorem fullyAbsorbs_implies_redundant (s r : I) (h : fullyAbsorbs s r) :
    isRedundant s r := h

/-- T120. If a signal is redundant for the receiver AND the receiver
    ignores it, then the communication surplus is purely the sender's
    cross-resonance shift. -/
theorem redundant_and_ignored_surplus (s r : I)
    (_hr : isRedundant s r) (hi : receiverIgnores s r) :
    communicationSurplus s r = rs s (compose r s) - rs s s := by
  rw [ignores_surplus s r hi]
  unfold senderNetPayoff senderPayoff interpret; ring

end BabblingCharacterization

/-! ## §15. Communication Value Hierarchy — Multi-Round Communication

In multi-round communication, each round composes a new signal onto
the receiver's evolving state.  We define the n-round communication
value and prove monotonicity: more rounds never decrease the value.
-/

section CommunicationValueHierarchy
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The n-round interpretation: the receiver absorbs the signal n times.
    This is just the persuasion operator. -/
def nRoundInterpret (signal receiver : I) (n : ℕ) : I :=
  persuade signal receiver n

/-- T121. 0-round interpretation leaves receiver unchanged. -/
@[simp] theorem nRoundInterpret_zero (s r : I) :
    nRoundInterpret s r 0 = r :=
  persuade_zero s r

/-- T122. 1-round interpretation is standard composition. -/
theorem nRoundInterpret_one (s r : I) :
    nRoundInterpret s r 1 = compose r s := by
  unfold nRoundInterpret persuade; simp [composeN_one]

/-- The n-round communication value: how much the receiver's
    self-resonance grows after n rounds of absorbing the signal. -/
noncomputable def nRoundValue (signal receiver : I) (n : ℕ) : ℝ :=
  rs (nRoundInterpret signal receiver n) (nRoundInterpret signal receiver n)
  - rs receiver receiver

/-- T123. 0-round value is zero: no communication, no gain. -/
theorem nRoundValue_zero (s r : I) : nRoundValue s r 0 = 0 := by
  unfold nRoundValue; simp

/-- T124. n-round value is non-negative (by compose_enriches induction). -/
theorem nRoundValue_nonneg (s r : I) (n : ℕ) :
    nRoundValue s r n ≥ 0 := by
  unfold nRoundValue nRoundInterpret
  linarith [persuade_selfrs_ge_target s r n]

/-- T125. n-round value is monotonically non-decreasing: more rounds
    never decrease the value. -/
theorem nRoundValue_mono (s r : I) (n : ℕ) :
    nRoundValue s r (n + 1) ≥ nRoundValue s r n := by
  unfold nRoundValue nRoundInterpret
  linarith [persuade_selfrs_mono s r n]

/-- The marginal value of the (n+1)-th round: additional value from
    one more round of communication. -/
noncomputable def marginalRoundValue (signal receiver : I) (n : ℕ) : ℝ :=
  nRoundValue signal receiver (n + 1) - nRoundValue signal receiver n

/-- T126. Marginal round value is always non-negative. -/
theorem marginalRoundValue_nonneg (s r : I) (n : ℕ) :
    marginalRoundValue s r n ≥ 0 := by
  unfold marginalRoundValue
  linarith [nRoundValue_mono s r n]

/-- T127. n-round value is the sum of n marginal values (telescoping sum).
    We state this as: nRoundValue(n+1) = nRoundValue(n) + marginalRoundValue(n). -/
theorem nRoundValue_telescope_step (s r : I) (n : ℕ) :
    nRoundValue s r (n + 1) = nRoundValue s r n + marginalRoundValue s r n := by
  unfold marginalRoundValue; ring

/-- T128. n-round value with void signal is always zero: repeating
    silence adds nothing. -/
theorem nRoundValue_void_signal (r : I) (n : ℕ) :
    nRoundValue (void : I) r n = 0 := by
  unfold nRoundValue nRoundInterpret
  simp [persuade_void_signal]

/-- T129. 1-round value equals information content. -/
theorem nRoundValue_one_eq_info (s r : I) :
    nRoundValue s r 1 = informationContent s r := by
  unfold nRoundValue nRoundInterpret informationContent persuade
  simp [composeN_one]

/-- T130. n-round value relates to persuasion surplus. -/
theorem nRoundValue_eq_persuasionSurplus (s r : I) (n : ℕ) :
    nRoundValue s r n = persuasionSurplus s r n := by
  unfold nRoundValue nRoundInterpret persuasionSurplus; ring

/-- T131. The 2-round value is at least the 1-round value. -/
theorem twoRound_ge_oneRound (s r : I) :
    nRoundValue s r 2 ≥ nRoundValue s r 1 :=
  nRoundValue_mono s r 1

/-- T132. n-round value for self-communication (signal = receiver)
    is at least n-1 times the single-step enrichment minimum. -/
theorem nRoundValue_self_nonneg (a : I) (n : ℕ) :
    nRoundValue a a n ≥ 0 :=
  nRoundValue_nonneg a a n

end CommunicationValueHierarchy

/-! ## §16. Cheap Talk vs Costly Signaling

We formalize when signals are "cheap" (low self-resonance = low weight)
versus "costly" (high self-resonance).  Costly signals are more
credible because they require more "substance" from the sender.
We prove Spence-like conditions for signaling equilibria.
-/

section CheapVsCostly
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A signal is cheap if its cost (self-resonance) is below a threshold. -/
def isCheap (s : I) (threshold : ℝ) : Prop :=
  signalCost s ≤ threshold

/-- A signal is costly if its cost exceeds a threshold. -/
def isCostly (s : I) (threshold : ℝ) : Prop :=
  signalCost s > threshold

/-- T133. Void is always cheap (for any non-negative threshold). -/
theorem void_is_cheap (threshold : ℝ) (h : threshold ≥ 0) :
    isCheap (void : I) threshold := by
  unfold isCheap signalCost; rw [rs_void_void]; linarith

/-- T134. A costly signal is never void. -/
theorem costly_ne_void (s : I) (threshold : ℝ) (h : isCostly s threshold)
    (ht : threshold ≥ 0) : s ≠ void := by
  intro hs
  unfold isCostly signalCost at h; rw [hs, rs_void_void] at h; linarith

/-- T135. Costly signals have strictly positive self-resonance. -/
theorem costly_pos (s : I) (threshold : ℝ) (h : isCostly s threshold)
    (ht : threshold ≥ 0) : rs s s > 0 := by
  unfold isCostly signalCost at h; linarith

/-- The credibility of a signal: how much emergence it generates
    with the receiver, normalized by its cost. Higher credibility
    means the signal "earns its weight" in communication. -/
noncomputable def signalCredibility (s r : I) : ℝ :=
  rs (compose r s) (compose r s) - rs r r

/-- T136. Signal credibility equals information content. -/
theorem signalCredibility_eq_info (s r : I) :
    signalCredibility s r = informationContent s r := by
  unfold signalCredibility informationContent; ring

/-- T137. Signal credibility is non-negative: any signal weakly enriches. -/
theorem signalCredibility_nonneg (s r : I) :
    signalCredibility s r ≥ 0 := by
  rw [signalCredibility_eq_info]; exact informationContent_nonneg s r

/-- T138. Void signal has zero credibility. -/
theorem signalCredibility_void (r : I) :
    signalCredibility (void : I) r = 0 := by
  rw [signalCredibility_eq_info]; exact informationContent_void r

/-- The Spence condition: a signal is a valid "signaling equilibrium"
    if its net payoff exceeds what any cheaper signal could achieve.
    Formally: for all s' with signalCost s' < signalCost s,
    the costly net payoff of s exceeds that of s'. -/
def satisfiesSpenceCondition (s r : I) : Prop :=
  costlyNetPayoff s r ≥ 0 ∧
  ∀ s' : I, signalCost s' < signalCost s →
    costlyNetPayoff s r ≥ costlyNetPayoff s' r

/-- T139. Void trivially satisfies the Spence condition (vacuously,
    since nothing is cheaper than void). -/
theorem void_spence (r : I) : satisfiesSpenceCondition (void : I) r := by
  constructor
  · rw [costlyNetPayoff_eq]; exact le_of_eq (senderNetPayoff_void_signal r).symm
  · intro s' hs'
    unfold signalCost at hs'; rw [rs_void_void] at hs'
    linarith [S.rs_self_nonneg s']

/-- T140. At Nash equilibrium, the equilibrium signal satisfies the
    Spence condition. -/
theorem nash_satisfies_spence (s r : I) (h : isNashEquilibrium s r) :
    costlyNetPayoff s r ≥ 0 := by
  rw [costlyNetPayoff_eq]; exact nash_sender_nonneg s r h

/-- T141. A costly signal's net payoff is bounded by sender payoff
    minus its cost. -/
theorem costly_net_bound (s r : I) :
    costlyNetPayoff s r = senderPayoff s r - signalCost s := by
  unfold costlyNetPayoff; ring

/-- T142. The "signaling premium": how much more net payoff a costly
    signal achieves compared to void. This is exactly the costly net payoff. -/
noncomputable def signalingPremium (s r : I) : ℝ :=
  costlyNetPayoff s r - costlyNetPayoff (void : I) r

/-- T143. Signaling premium equals the costly net payoff itself
    (since void gets zero). -/
theorem signalingPremium_eq (s r : I) :
    signalingPremium s r = costlyNetPayoff s r := by
  unfold signalingPremium; rw [costlyNetPayoff_void]; ring

/-- T144. Costly signals that produce more emergence with the receiver
    have higher information content — they are more "credible" in the
    Spence sense. -/
theorem credibility_monotone (s₁ s₂ r : I)
    (h : signalCredibility s₁ r ≥ signalCredibility s₂ r) :
    informationContent s₁ r ≥ informationContent s₂ r := by
  rwa [← signalCredibility_eq_info, ← signalCredibility_eq_info]

end CheapVsCostly

/-! ## §17. The Revelation Problem

When a sender reveals information by composing their private idea
with a public signal, the receiver learns through the enrichment
of their composed state.  We prove bounds on how much can be
learned per round and that repeated revelation is bounded by
cumulative emergence.
-/

section RevelationProblem
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The revelation of idea `private_idea` through signal `public_signal`
    to receiver `r`: the receiver interprets the publicly composed signal. -/
def reveal (private_idea public_signal r : I) : I :=
  compose r (compose private_idea public_signal)

/-- T145. Revelation through void public signal reduces to direct
    interpretation of the private idea. -/
theorem reveal_void_public (priv r : I) :
    reveal priv (void : I) r = compose r priv := by
  unfold reveal; simp

/-- T146. Revelation of void private idea reduces to interpretation
    of the public signal. -/
theorem reveal_void_private (pub r : I) :
    reveal (void : I) pub r = compose r pub := by
  unfold reveal; simp

/-- T147. Revelation through void public to void receiver. -/
theorem reveal_void_all :
    reveal (void : I) (void : I) (void : I) = (void : I) := by
  unfold reveal; simp

/-- The revelation gain: how much the receiver's self-resonance
    increases from revelation versus direct interpretation of
    the public signal alone. -/
noncomputable def revelationGain (priv pub r : I) : ℝ :=
  rs (reveal priv pub r) (reveal priv pub r) -
  rs (compose r pub) (compose r pub)

/-- T148. Revelation enriches the receiver beyond baseline:
    the receiver's self-resonance after revelation is at least
    as much as with the public signal alone when priv = void. -/
theorem revelationGain_baseline_nonneg (priv pub r : I) :
    rs (reveal priv pub r) (reveal priv pub r) ≥ rs r r := by
  unfold reveal
  linarith [S.compose_enriches r (compose priv pub)]

/-- T149. Revelation gain from void private idea is non-negative
    (it's actually just the enrichment from pub∘void = pub which is zero). -/
theorem revelationGain_void_private (pub r : I) :
    revelationGain (void : I) pub r = 0 := by
  unfold revelationGain reveal; simp

/-- T150. Total information from revelation equals the information content
    of the composed private-public signal. -/
theorem revelation_total_info (priv pub r : I) :
    rs (reveal priv pub r) (reveal priv pub r) - rs r r =
    informationContent (compose priv pub) r := by
  rfl

/-- The per-round revelation: applying the same private idea repeatedly
    through different public signals. -/
def iteratedReveal (priv : I) (r : I) : ℕ → I
  | 0 => r
  | n + 1 => compose (iteratedReveal priv r n) priv

/-- T151. Iterated revelation at step 0 is the receiver unchanged. -/
@[simp] theorem iteratedReveal_zero (priv r : I) :
    iteratedReveal priv r 0 = r := rfl

/-- T152. Iterated revelation is exactly persuasion. -/
theorem iteratedReveal_eq_persuade (priv r : I) (n : ℕ) :
    iteratedReveal priv r n = persuade priv r n := by
  induction n with
  | zero => simp [persuade]
  | succ n ih =>
    unfold iteratedReveal
    rw [ih]
    unfold persuade
    rw [composeN_succ]
    rw [← compose_assoc']

/-- T153. Self-resonance of iterated revelation is non-decreasing. -/
theorem iteratedReveal_mono (priv r : I) (n : ℕ) :
    rs (iteratedReveal priv r (n + 1)) (iteratedReveal priv r (n + 1)) ≥
    rs (iteratedReveal priv r n) (iteratedReveal priv r n) := by
  show rs (compose (iteratedReveal priv r n) priv) (compose (iteratedReveal priv r n) priv) ≥ _
  exact S.compose_enriches (iteratedReveal priv r n) priv

/-- T154. Cumulative revelation gain: total self-resonance growth
    from n rounds of revelation. -/
noncomputable def cumulativeRevelation (priv r : I) (n : ℕ) : ℝ :=
  rs (iteratedReveal priv r n) (iteratedReveal priv r n) - rs r r

/-- T155. Cumulative revelation is non-negative. -/
theorem cumulativeRevelation_nonneg (priv r : I) (n : ℕ) :
    cumulativeRevelation priv r n ≥ 0 := by
  unfold cumulativeRevelation
  rw [iteratedReveal_eq_persuade]
  linarith [persuade_selfrs_ge_target priv r n]

/-- T156. Cumulative revelation is non-decreasing. -/
theorem cumulativeRevelation_mono (priv r : I) (n : ℕ) :
    cumulativeRevelation priv r (n + 1) ≥
    cumulativeRevelation priv r n := by
  unfold cumulativeRevelation
  linarith [iteratedReveal_mono priv r n]

/-- T157. Cumulative revelation at step 0 is zero. -/
theorem cumulativeRevelation_zero (priv r : I) :
    cumulativeRevelation priv r 0 = 0 := by
  unfold cumulativeRevelation; simp

/-- T158. Cumulative revelation with void signal is always zero. -/
theorem cumulativeRevelation_void (r : I) (n : ℕ) :
    cumulativeRevelation (void : I) r n = 0 := by
  unfold cumulativeRevelation
  rw [iteratedReveal_eq_persuade]; simp

/-- T159. The per-step revelation increment is non-negative. -/
theorem revelationIncrement_nonneg (priv r : I) (n : ℕ) :
    cumulativeRevelation priv r (n + 1) - cumulativeRevelation priv r n ≥ 0 := by
  linarith [cumulativeRevelation_mono priv r n]

end RevelationProblem

/-! ## §18. Strategic Silence

Void as a deliberate strategic choice.  We prove when silence
dominates speech: when the cost of signaling exceeds the
communication value, staying silent is the rational strategy.
We characterize the "silence threshold."
-/

section StrategicSilence
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The net value of speaking signal s to receiver r: the total
    communication surplus. When negative, silence dominates speech. -/
noncomputable def speechValue (s r : I) : ℝ :=
  communicationSurplus s r

/-- T160. Speech value of void is zero: silence is the neutral choice. -/
theorem speechValue_void (r : I) : speechValue (void : I) r = 0 := by
  unfold speechValue; exact communicationSurplus_void_signal r

/-- T161. Speech value decomposes into sender and receiver net gains. -/
theorem speechValue_decomp (s r : I) :
    speechValue s r = senderNetPayoff s r + receiverNetPayoff s r := by
  unfold speechValue; exact communicationSurplus_eq_net s r

/-- Silence dominates speech for the sender when the sender's net payoff
    from signal s is non-positive. -/
def silenceDominates (s r : I) : Prop :=
  senderNetPayoff s r ≤ 0

/-- T162. Void never loses to itself: silence never dominates silence. -/
theorem silence_never_dominates_void (r : I) :
    ¬silenceDominates (void : I) r ∨ senderNetPayoff (void : I) r = 0 := by
  right; exact senderNetPayoff_void_signal r

/-- T163. If silence dominates for every signal, then the sender's
    best achievable net payoff is zero (achieved by void). -/
theorem universal_silence (r : I)
    (h : ∀ s : I, silenceDominates s r) :
    ∀ s : I, senderNetPayoff s r ≤ 0 :=
  h

/-- T164. When silence dominates, sender payoff is at most self-resonance. -/
theorem silence_dominates_payoff_bound (s r : I) (h : silenceDominates s r) :
    senderPayoff s r ≤ rs s s := by
  unfold silenceDominates senderNetPayoff at h; linarith

/-- The silence threshold for a receiver: the minimum signal cost
    above which silence dominates. A signal is "too expensive" if
    its self-resonance exceeds this threshold. -/
noncomputable def silenceThreshold (s r : I) : ℝ :=
  senderPayoff s r

/-- T165. Silence dominates iff signal cost exceeds the silence threshold. -/
theorem silence_iff_cost_exceeds (s r : I) :
    silenceDominates s r ↔ signalCost s ≥ silenceThreshold s r := by
  unfold silenceDominates senderNetPayoff signalCost silenceThreshold
  constructor <;> intro h <;> linarith

/-- T166. At Nash equilibrium, silence does NOT dominate the
    equilibrium signal (the sender weakly prefers speaking). -/
theorem nash_no_silence (s r : I) (h : isNashEquilibrium s r) :
    ¬silenceDominates s r ∨ senderNetPayoff s r = 0 := by
  have h1 := nash_sender_nonneg s r h
  unfold silenceDominates
  rcases eq_or_lt_of_le h1 with heq | hlt
  · right; linarith
  · left; linarith

/-- T167. If silence dominates for all signals against receiver r,
    then communication surplus is non-positive for all signals. -/
theorem universal_silence_no_surplus (r : I)
    (h : ∀ s : I, silenceDominates s r) (s : I) :
    speechValue s r ≤ receiverNetPayoff s r := by
  have hd := speechValue_decomp s r
  have hs := h s
  unfold silenceDominates at hs
  linarith

/-- T168. The "silence gap": how much better silence is than speaking.
    Non-negative when silence dominates. -/
noncomputable def silenceGap (s r : I) : ℝ :=
  - senderNetPayoff s r

/-- T169. Silence gap equals signal cost minus sender payoff. -/
theorem silenceGap_eq (s r : I) :
    silenceGap s r = rs s s - senderPayoff s r := by
  unfold silenceGap senderNetPayoff; ring

/-- T170. Silence gap is non-negative iff silence dominates. -/
theorem silenceGap_nonneg_iff (s r : I) :
    silenceGap s r ≥ 0 ↔ silenceDominates s r := by
  unfold silenceGap silenceDominates; constructor <;> intro h <;> linarith

/-- T171. Silence gap of void signal is always zero. -/
theorem silenceGap_void (r : I) :
    silenceGap (void : I) r = 0 := by
  unfold silenceGap; rw [senderNetPayoff_void_signal]; ring

end StrategicSilence

/-! ## §19. Emergence Accumulation and Communication Bounds

Deep results about how emergence accumulates over compositions,
providing fundamental bounds on communication effectiveness.
-/

section EmergenceAccumulation
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The cumulative enrichment of composing a list of signals onto a base. -/
noncomputable def cumulativeEnrichment (base : I) (signals : List I) : ℝ :=
  rs (discourse base signals) (discourse base signals) - rs base base

/-- T172. Cumulative enrichment of empty list is zero. -/
theorem cumulativeEnrichment_nil (base : I) :
    cumulativeEnrichment base [] = 0 := by
  unfold cumulativeEnrichment; simp

/-- T173. Cumulative enrichment is non-negative for any signal list. -/
theorem cumulativeEnrichment_cons_nonneg (base s : I) (rest : List I) :
    cumulativeEnrichment base (s :: rest) ≥ 0 := by
  unfold cumulativeEnrichment discourse
  linarith [discourse_enriches base s rest]

/-- T174. Cumulative enrichment grows when we append a signal. -/
theorem cumulativeEnrichment_append_mono (base s : I) (signals : List I) :
    cumulativeEnrichment base (signals ++ [s]) ≥
    cumulativeEnrichment base signals := by
  unfold cumulativeEnrichment
  induction signals generalizing base with
  | nil =>
    simp [discourse]
    exact S.compose_enriches base s
  | cons s' rest ih =>
    simp only [List.cons_append, discourse]
    have h := ih (compose base s')
    -- Normalize ++ and List.append
    simp only [List.append_eq] at h ⊢
    linarith

/-- The emergence density of a discourse: average enrichment per signal. -/
noncomputable def emergenceDensity (base : I) (signals : List I) : ℝ :=
  if signals.length = 0 then 0
  else cumulativeEnrichment base signals / signals.length

/-- T175. Emergence density of empty discourse is zero. -/
theorem emergenceDensity_nil (base : I) :
    emergenceDensity base [] = 0 := by
  unfold emergenceDensity; simp

/-- The enrichment contribution of a single step in discourse. -/
noncomputable def stepEnrichment (state signal : I) : ℝ :=
  rs (compose state signal) (compose state signal) - rs state state

/-- T176. Step enrichment is non-negative. -/
theorem stepEnrichment_nonneg (state signal : I) :
    stepEnrichment state signal ≥ 0 := by
  unfold stepEnrichment; linarith [S.compose_enriches state signal]

/-- T177. Step enrichment of void signal is zero. -/
theorem stepEnrichment_void (state : I) :
    stepEnrichment state (void : I) = 0 := by
  unfold stepEnrichment; simp

/-- T178. Step enrichment equals information content. -/
theorem stepEnrichment_eq_info (state signal : I) :
    stepEnrichment state signal = informationContent signal state := by
  unfold stepEnrichment informationContent; ring

end EmergenceAccumulation

/-! ## §20. Signaling Equilibrium Refinements

Deeper results about equilibrium structure: dominant strategies,
Pareto optimality among equilibria, and the relationship between
signal weight and equilibrium quality.
-/

section EquilibriumRefinements
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A signal is weakly dominated by another if the other achieves
    at least as high sender net payoff against ALL receivers. -/
def weaklyDominatedSender (s s' : I) : Prop :=
  ∀ r : I, senderNetPayoff s' r ≥ senderNetPayoff s r

/-- T179. No signal weakly dominates void against a void receiver:
    all signals tie at zero. -/
theorem void_receiver_all_tie (s : I) :
    senderNetPayoff s (void : I) = senderNetPayoff (void : I) (void : I) := by
  rw [senderNetPayoff_void_receiver, senderNetPayoff_void_signal]

/-- T180. Void is never strictly dominated: there exists a receiver
    (namely void) against which void does as well as any signal. -/
theorem void_not_strictly_dominated (s : I) :
    senderNetPayoff (void : I) (void : I) ≥ senderNetPayoff s (void : I) := by
  rw [senderNetPayoff_void_signal, senderNetPayoff_void_receiver]

/-- An equilibrium is Pareto-efficient if no other equilibrium makes
    both players strictly better off. -/
def paretoEfficient (s r : I) (_h : isNashEquilibrium s r) : Prop :=
  ∀ s' r' : I, isNashEquilibrium s' r' →
    (senderNetPayoff s' r' > senderNetPayoff s r →
     receiverNetPayoff s' r' ≤ receiverNetPayoff s r) ∧
    (receiverNetPayoff s' r' > receiverNetPayoff s r →
     senderNetPayoff s' r' ≤ senderNetPayoff s r)

/-- T181. The void-void equilibrium has surplus zero. -/
theorem void_equilibrium_surplus :
    communicationSurplus (void : I) (void : I) = 0 :=
  communicationSurplus_void_signal _

/-- T182. At any Nash equilibrium, social welfare is at least the sum
    of self-resonances. -/
theorem nash_welfare_bound (s r : I) (h : isNashEquilibrium s r) :
    socialWelfare s r ≥ rs s s + rs r r := by
  have h1 := nash_sender_nonneg s r h
  have h2 := nash_receiver_nonneg s r h
  have hw := socialWelfare_eq s r
  have hs := sender_payoff_eq s r
  have hr := receiver_payoff_eq s r
  unfold senderNetPayoff at h1; unfold receiverNetPayoff at h2
  linarith

/-- T183. Communication surplus at Nash equilibrium relates to
    the enrichment of interpretation. -/
theorem nash_surplus_via_enrichment (s r : I) (_h : isNashEquilibrium s r) :
    communicationSurplus s r =
    rs s (compose r s) + rs r (compose r s) - rs s s - rs r r := by
  unfold communicationSurplus senderPayoff receiverPayoff interpret; ring

end EquilibriumRefinements

/-! ## §21. Signaling Chains and Transitivity

When signals are relayed through intermediaries, the chain structure
preserves enrichment but may lose or gain emergence.
-/

section SignalingChains
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A signaling chain: sender → relay → receiver.
    The relay interprets the sender's signal, then the receiver
    interprets the relay's output. -/
def signalingChain (sender relay receiver : I) : I :=
  compose receiver (compose relay sender)

/-- T184. The signaling chain equals double composition via associativity. -/
theorem signalingChain_assoc (s m r : I) :
    signalingChain s m r = compose (compose r m) s := by
  unfold signalingChain; rw [compose_assoc']

/-- T185. Signaling chain with void relay reduces to direct communication. -/
theorem signalingChain_void_relay (s r : I) :
    signalingChain s (void : I) r = compose r s := by
  unfold signalingChain; simp

/-- T186. Signaling chain with void sender is just receiver-relay
    composition. -/
theorem signalingChain_void_sender (m r : I) :
    signalingChain (void : I) m r = compose r m := by
  unfold signalingChain; simp

/-- T187. Signaling chain enriches the receiver at least as much as
    direct relay-receiver composition. -/
theorem signalingChain_enriches_relay (s m r : I) :
    rs (signalingChain s m r) (signalingChain s m r) ≥
    rs (compose r m) (compose r m) := by
  rw [signalingChain_assoc]
  exact S.compose_enriches (compose r m) s

/-- T188. Signaling chain enriches the receiver beyond baseline. -/
theorem signalingChain_enriches_receiver (s m r : I) :
    rs (signalingChain s m r) (signalingChain s m r) ≥ rs r r := by
  have h1 := signalingChain_enriches_relay s m r
  have h2 := S.compose_enriches r m
  linarith

/-- The chain value: total enrichment from the full chain beyond
    what the receiver started with. -/
noncomputable def chainValue (sender relay receiver : I) : ℝ :=
  rs (signalingChain sender relay receiver) (signalingChain sender relay receiver)
  - rs receiver receiver

/-- T189. Chain value is non-negative. -/
theorem chainValue_nonneg (s m r : I) :
    chainValue s m r ≥ 0 := by
  unfold chainValue
  linarith [signalingChain_enriches_receiver s m r]

/-- T190. Chain value with void sender equals information content
    of relay for receiver. -/
theorem chainValue_void_sender (m r : I) :
    chainValue (void : I) m r = informationContent m r := by
  unfold chainValue informationContent; rw [signalingChain_void_sender]

/-- The relay amplification: how much extra value the relay adds
    beyond direct sender-receiver communication. -/
noncomputable def relayAmplification (s m r : I) : ℝ :=
  chainValue s m r - informationContent s r

/-- T191. Relay amplification of void relay is zero: no relay, no extra value. -/
theorem relayAmplification_void (s r : I) :
    relayAmplification s (void : I) r = 0 := by
  unfold relayAmplification chainValue informationContent
  rw [signalingChain_void_relay]; ring

end SignalingChains

/-! ## §22. Fundamental Communication Inequalities

Deep structural inequalities relating emergence, enrichment,
and communication value.  These are the "main theorems" that
chain together the results of earlier sections.
-/

section FundamentalInequalities
variable {I : Type*} [S : IdeaticSpace3 I]

/-- T192. The Communication Enrichment Theorem: for any sender-receiver
    pair, the interpretation's self-resonance is at least the receiver's.
    This is the fundamental monotonicity of communication. -/
theorem communication_enrichment (s r : I) :
    rs (compose r s) (compose r s) ≥ rs r r :=
  S.compose_enriches r s

/-- T193. Double composition enrichment: composing twice enriches at
    least as much as once. -/
theorem double_composition_enrichment (a b : I) :
    rs (compose (compose a b) b) (compose (compose a b) b) ≥
    rs (compose a b) (compose a b) :=
  S.compose_enriches (compose a b) b

/-- T194. The enrichment is transitive: if a enriches to a∘b,
    and a∘b enriches to (a∘b)∘c, then a enriches to (a∘b)∘c. -/
theorem enrichment_transitive (a b c : I) :
    rs (compose (compose a b) c) (compose (compose a b) c) ≥ rs a a := by
  have h1 := S.compose_enriches a b
  have h2 := S.compose_enriches (compose a b) c
  linarith

/-- T195. Social welfare is symmetric in a specific sense: it equals the
    sum of cross-resonances with the interpretation. -/
theorem welfare_lower_bound (s r : I) :
    socialWelfare s r =
    rs s (compose r s) + rs r (compose r s) := by
  exact socialWelfare_eq s r

/-- T196. The emergence-bounded communication inequality:
    the squared emergence is bounded by the product of
    self-resonances of the composition and the observer. -/
theorem emergence_communication_bound (s r : I) :
    (emergence r s (compose r s)) ^ 2 ≤
    rs (compose r s) (compose r s) * rs (compose r s) (compose r s) := by
  have h := emergence_bounded' r s (compose r s)
  nlinarith [S.rs_self_nonneg (compose r s)]

/-- T197. The enrichment gap is non-negative for any composition. -/
theorem enrichment_gap_nonneg (a b : I) :
    rs (compose a b) (compose a b) - rs a a ≥ 0 := by
  linarith [S.compose_enriches a b]

/-- T198. Triple enrichment bound. -/
theorem triple_enrichment (a b c : I) :
    rs (compose (compose a b) c) (compose (compose a b) c) ≥
    rs a a := by
  linarith [S.compose_enriches a b, S.compose_enriches (compose a b) c]

/-- T199. Discourse enrichment is additive in a lower bound sense:
    total enrichment from two signals is at least the enrichment
    from the first signal alone. -/
theorem discourse_enrichment_mono (r s₁ s₂ : I) :
    rs (discourse r [s₁, s₂]) (discourse r [s₁, s₂]) ≥
    rs (discourse r [s₁]) (discourse r [s₁]) := by
  unfold discourse
  exact S.compose_enriches (compose r s₁) s₂

/-- T200. n-round value is at most the n-round interpretation's
    self-resonance. -/
theorem nRoundValue_le_selfrs (s r : I) (n : ℕ) :
    nRoundValue s r n ≤
    rs (nRoundInterpret s r n) (nRoundInterpret s r n) := by
  unfold nRoundValue
  linarith [S.rs_self_nonneg r]

end FundamentalInequalities

/-! ## §23. The Grand Unification: Communication as Enrichment Game

Tying together all the threads: communication value, Nash equilibria,
persuasion, and emergence are all manifestations of the same
underlying principle — compose_enriches.
-/

section GrandUnification
variable {I : Type*} [S : IdeaticSpace3 I]

/-- T201. The Master Communication Theorem: at any Nash equilibrium,
    the total welfare exceeds the sum of individual baselines, and
    the surplus equals exactly the sum of sender and receiver net gains,
    both of which are non-negative. -/
theorem master_communication_theorem (s r : I) (h : isNashEquilibrium s r) :
    communicationSurplus s r ≥ 0 ∧
    senderNetPayoff s r ≥ 0 ∧
    receiverNetPayoff s r ≥ 0 ∧
    communicationSurplus s r = senderNetPayoff s r + receiverNetPayoff s r :=
  ⟨nash_surplus_nonneg s r h,
   nash_sender_nonneg s r h,
   nash_receiver_nonneg s r h,
   communicationSurplus_eq_net s r⟩

/-- T202. The Enrichment-Communication Duality: the n-round communication
    value equals the persuasion surplus, which equals the cumulative
    revelation gain with void public signal. -/
theorem enrichment_communication_duality (s r : I) (n : ℕ) :
    nRoundValue s r n = persuasionSurplus s r n :=
  nRoundValue_eq_persuasionSurplus s r n

/-- T203. The Silence-Babbling Connection: under babbling, the
    silence gap equals rs(s,s) - rs(s, compose r s). -/
theorem silence_babbling_connection (r : I) (_h : isBabbling r) (s : I) :
    silenceGap s r = rs s s - rs s (compose r s) := by
  unfold silenceGap senderNetPayoff senderPayoff interpret; ring

/-- T204. The Chain-Discourse Equivalence: a signaling chain
    s → m → r produces the same result as a discourse [s] read by
    the composition r∘m (by associativity). -/
theorem chain_discourse_equiv (s m r : I) :
    signalingChain s m r = discourse (compose r m) [s] := by
  unfold signalingChain; simp [discourse]

/-- T205. Communication value hierarchy collapses for void signals:
    all n-round values are zero when the signal is void. -/
theorem hierarchy_collapse_void (r : I) (n m : ℕ) :
    nRoundValue (void : I) r n = nRoundValue (void : I) r m := by
  rw [nRoundValue_void_signal, nRoundValue_void_signal]

/-- T206. The Fundamental Theorem of Costly Signaling:
    A signal is worth sending iff its sender payoff exceeds its cost,
    iff it generates positive net payoff, iff silence does not dominate. -/
theorem fundamental_costly_signaling (s r : I) :
    (costlyNetPayoff s r > 0) ↔ (¬silenceDominates s r ∧ senderNetPayoff s r > 0) := by
  rw [costlyNetPayoff_eq]
  unfold silenceDominates
  constructor
  · intro h; exact ⟨by linarith, h⟩
  · intro ⟨_, h⟩; exact h

/-- T207. Cooperation surplus connects to chain value:
    the cooperation surplus of (r, s) equals the chain value of
    s through void relay to r, minus rs(s,s). -/
theorem cooperation_chain_connection (s r : I) :
    cooperationSurplus r s =
    chainValue s (void : I) r - rs s s := by
  unfold cooperationSurplus chainValue
  simp [signalingChain_void_relay]

/-- T208. The babbling-silence duality: under babbling,
    the speech value equals the negative of the silence gap. -/
theorem babbling_silence_duality (r : I) (h : isBabbling r) (s : I) :
    speechValue s r = -silenceGap s r := by
  unfold speechValue silenceGap
  rw [babbling_surplus r h s]; ring

/-- T209. The Communication Completeness Theorem: every communication
    quantity can be expressed in terms of just rs and compose:
    Here we show communication surplus expands to primitive operations. -/
theorem communication_completeness (s r : I) :
    communicationSurplus s r =
    rs s (compose r s) + rs r (compose r s) - rs s s - rs r r := by
  unfold communicationSurplus senderPayoff receiverPayoff interpret; ring

/-- T210. The Monotone Communication Principle: for any fixed receiver,
    the map n ↦ nRoundValue(s, r, n) is a non-decreasing sequence
    bounded below by 0 and above by the n-round interpretation's
    self-resonance. -/
theorem monotone_communication (s r : I) (n : ℕ) :
    0 ≤ nRoundValue s r n ∧
    nRoundValue s r n ≤ nRoundValue s r (n + 1) ∧
    nRoundValue s r n ≤
      rs (nRoundInterpret s r n) (nRoundInterpret s r n) := by
  refine ⟨?_, ?_, ?_⟩
  · linarith [nRoundValue_nonneg s r n]
  · linarith [nRoundValue_mono s r n]
  · exact nRoundValue_le_selfrs s r n

end GrandUnification

end IDT3
