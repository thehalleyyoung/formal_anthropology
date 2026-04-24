import FormalAnthropology.IDT_Foundations_v2
import FormalAnthropology.IDT_v2_SignalGames

/-!
# IDT v2: Payoff Analysis

Deeper analysis of the payoff structure in signal games. Introduces
**self-conviction** (how strongly an idea resonates with itself) and
**agreement** (resonance between two ideas) as primitives, then derives
consequences for payoffs, social welfare, and idea distances.

## Key Insight

In IdeaticSpace2, every idea has self-conviction ≥ 1 (void calibrates to 1),
and agreement is always nonneg. Payoffs decompose as:
  senderPayoff s r = agreement(s, interpret(s,r))
where interpret(s,r) = compose(r,s). Context enrichment monotonically
increases payoffs.

## NO SORRIES
-/

namespace IDT2

section Payoffs

variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-! ## §1. Core Definitions -/

/-- Self-conviction: how strongly an idea resonates with itself -/
noncomputable def selfConviction (a : I) : ℝ :=
  resonanceStrength a a

/-- Agreement: resonance between two ideas (always nonneg in IdeaticSpace2) -/
noncomputable def agreement (a b : I) : ℝ :=
  resonanceStrength a b

/-- Self-conviction of the interpretation -/
noncomputable def interpretSelfConviction (s r : I) : ℝ :=
  selfConviction (interpret s r)

/-! ## §2. Self-Conviction Properties -/

/-- T1. Self-conviction is strictly positive -/
theorem selfConviction_pos (a : I) : selfConviction a > 0 := by
  unfold selfConviction; exact rs_self_pos' a

/-- T2. Self-conviction ≥ 1 -/
theorem selfConviction_ge_one (a : I) : selfConviction a ≥ 1 := by
  unfold selfConviction; exact rs_self_ge_one a

/-- T3. Void has unit self-conviction -/
theorem selfConviction_void : selfConviction (void : I) = 1 := by
  unfold selfConviction; exact rs_void_unit

/-- T4. Void has minimal self-conviction -/
theorem selfConviction_void_minimal (a : I) :
    selfConviction (void : I) ≤ selfConviction a := by
  rw [selfConviction_void]; exact selfConviction_ge_one a

/-- T5. Composition increases conviction (left component) -/
theorem selfConviction_compose_ge_left (a b : I) :
    selfConviction (compose a b) ≥ selfConviction a := by
  unfold selfConviction; exact rs_compose_self_right a b

/-- T6. Composition increases conviction (right component) -/
theorem selfConviction_compose_ge_right (a b : I) :
    selfConviction (compose a b) ≥ selfConviction b := by
  unfold selfConviction; exact rs_compose_self_left b a

/-- T7. Composed conviction ≥ 1 -/
theorem selfConviction_compose_ge_one (a b : I) :
    selfConviction (compose a b) ≥ 1 := by
  linarith [selfConviction_compose_ge_left a b, selfConviction_ge_one a]

/-- T8. Conviction monotonically increases with iterated composition -/
theorem selfConviction_composeN_mono (a : I) (n : ℕ) :
    selfConviction (composeN a (n + 1)) ≥ selfConviction (composeN a n) := by
  unfold selfConviction; exact rs_self_composeN_mono a n

/-! ## §3. Agreement Properties -/

/-- T9. Agreement is symmetric -/
theorem agreement_symmetric (a b : I) : agreement a b = agreement b a := by
  unfold agreement; exact rs_symm' a b

/-- T10. Agreement is nonnegative -/
theorem agreement_nonneg (a b : I) : agreement a b ≥ 0 := by
  unfold agreement; exact rs_nonneg' a b

/-- T11. Self-agreement equals self-conviction -/
theorem agreement_self_eq_conviction (a : I) :
    agreement a a = selfConviction a := rfl

/-- T12. Cauchy-Schwarz for agreement -/
theorem agreement_cauchy_schwarz (a b : I) :
    agreement a b * agreement a b ≤ selfConviction a * selfConviction b := by
  unfold agreement selfConviction
  exact IdeaticSpace2.rs_cauchy_schwarz a b

/-- T13. Agreement with void is nonneg -/
theorem agreement_void_nonneg (a : I) : agreement (void : I) a ≥ 0 := by
  unfold agreement; exact rs_nonneg' _ _

/-- T14. Composition monotonicity for agreement (right context) -/
theorem agreement_compose_right_mono (a b c : I) :
    agreement (compose a c) (compose b c) ≥ agreement a b := by
  unfold agreement; exact IdeaticSpace2.rs_compose_right_mono a b c

/-- T15. Composition monotonicity for agreement (left context) -/
theorem agreement_compose_left_mono (a b c : I) :
    agreement (compose c a) (compose c b) ≥ agreement a b := by
  unfold agreement; exact IdeaticSpace2.rs_compose_left_mono a b c

/-! ## §4. Payoff-Conviction Connection -/

/-- T16. Sender payoff = agreement with interpretation -/
theorem senderPayoff_eq_agreement (s r : I) :
    senderPayoff s r = agreement s (interpret s r) := rfl

/-- T17. Receiver payoff = agreement with interpretation -/
theorem receiverPayoff_eq_agreement (s r : I) :
    receiverPayoff s r = agreement r (interpret s r) := rfl

/-- T18. Sender payoff with void receiver = self-conviction -/
theorem senderPayoff_eq_selfConviction (s : I) :
    senderPayoff s (void : I) = selfConviction s := by
  unfold selfConviction; exact senderPayoff_void_receiver s

/-- T19. Receiver payoff with void signal = self-conviction -/
theorem receiverPayoff_eq_selfConviction (r : I) :
    receiverPayoff (void : I) r = selfConviction r := by
  unfold selfConviction; exact receiverPayoff_void_signal r

/-- T20. Self-conviction of interpretation = interpretationStrength -/
theorem selfConviction_interpret_eq_strength (s r : I) :
    selfConviction (interpret s r) = interpretationStrength s r := rfl

/-- T21. Self-conviction of interpretation ≥ sender conviction -/
theorem selfConviction_interpret_ge_sender (s r : I) :
    selfConviction (interpret s r) ≥ selfConviction s := by
  rw [selfConviction_interpret_eq_strength]
  exact interpretationStrength_ge_sender s r

/-- T22. Self-conviction of interpretation ≥ receiver conviction -/
theorem selfConviction_interpret_ge_receiver (s r : I) :
    selfConviction (interpret s r) ≥ selfConviction r := by
  rw [selfConviction_interpret_eq_strength]
  exact interpretationStrength_ge_receiver s r

/-! ## §5. Distance via Conviction -/

/-- T23. Squared distance decomposes via conviction and agreement -/
theorem squaredDistance_eq_conviction_agreement (a b : I) :
    squaredDistance a b =
    selfConviction a + selfConviction b - 2 * agreement a b := rfl

/-- T24. Squared distance from void -/
theorem squaredDistance_void_eq (a : I) :
    squaredDistance (void : I) a =
    1 + selfConviction a - 2 * agreement (void : I) a := by
  rw [squaredDistance_eq_conviction_agreement]
  rw [selfConviction_void]

/-! ## §6. Social Welfare via Agreement -/

/-- T25. Social welfare = sum of agreements with interpretation -/
theorem socialWelfare_eq_agreements (s r : I) :
    socialWelfare s r =
    agreement s (interpret s r) + agreement r (interpret s r) := by
  unfold socialWelfare
  rw [senderPayoff_eq_agreement, receiverPayoff_eq_agreement]

/-- T26. Social welfare with void receiver = conviction + agreement -/
theorem socialWelfare_void_receiver_eq (s : I) :
    socialWelfare s (void : I) =
    selfConviction s + agreement (void : I) s := by
  unfold socialWelfare senderPayoff receiverPayoff selfConviction agreement
  rw [interpret_void_receiver]

/-- T27. Social welfare with void sender = agreement + conviction -/
theorem socialWelfare_void_sender_eq (r : I) :
    socialWelfare (void : I) r =
    agreement (void : I) r + selfConviction r := by
  unfold socialWelfare senderPayoff receiverPayoff selfConviction agreement
  rw [interpret_void_signal]

/-! ## §7. Advanced Conviction Theorems -/

/-- T28. Sender payoff is bounded by CS in terms of conviction -/
theorem senderPayoff_conviction_bound (s r : I) :
    senderPayoff s r * senderPayoff s r ≤
    selfConviction s * selfConviction (interpret s r) := by
  unfold selfConviction
  exact IdeaticSpace2.rs_cauchy_schwarz s (interpret s r)

/-- T29. Receiver payoff is bounded by CS in terms of conviction -/
theorem receiverPayoff_conviction_bound (s r : I) :
    receiverPayoff s r * receiverPayoff s r ≤
    selfConviction r * selfConviction (interpret s r) := by
  unfold selfConviction
  exact IdeaticSpace2.rs_cauchy_schwarz r (interpret s r)

end Payoffs

end IDT2
