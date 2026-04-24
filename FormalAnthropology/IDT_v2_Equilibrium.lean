import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.IDT_Foundations_v2

/-!
# IDT v2: Nash Equilibrium in Meaning Games

Nash equilibrium theory for ideatic signaling games with real-valued
resonance payoffs. A strategy profile (s, r) is a Nash equilibrium
if neither player can improve by unilateral deviation.

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT2.Equilibrium

variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-! ## §1. Nash Equilibrium — Core Definitions -/

/-- A strategy profile (s, r) is a Nash equilibrium if both players play
    best responses from their respective strategy sets. -/
def IsNashEquilibrium (s r : I) (S1 S2 : List I) (u1 u2 : I → I → ℝ) : Prop :=
  s ∈ S1 ∧ r ∈ S2 ∧
  (∀ t ∈ S1, u1 t r ≤ u1 s r) ∧
  (∀ t ∈ S2, u2 s t ≤ u2 s r)

/-- Pareto improvement: both weakly better, one strictly. -/
def ParetoImproves (s' r' s r : I) (u1 u2 : I → I → ℝ) : Prop :=
  u1 s' r' ≥ u1 s r ∧ u2 s' r' ≥ u2 s r ∧
  (u1 s' r' > u1 s r ∨ u2 s' r' > u2 s r)

/-- Weak Pareto improvement (both weakly better). -/
def WeakParetoImproves (s' r' s r : I) (u1 u2 : I → I → ℝ) : Prop :=
  u1 s' r' ≥ u1 s r ∧ u2 s' r' ≥ u2 s r

/-- A profile is Pareto optimal if no Pareto improvement exists in the sets. -/
def IsParetoOptimal (s r : I) (S1 S2 : List I) (u1 u2 : I → I → ℝ) : Prop :=
  s ∈ S1 ∧ r ∈ S2 ∧
  ¬∃ s' ∈ S1, ∃ r' ∈ S2, ParetoImproves s' r' s r u1 u2

/-! ## §2. Structural NE Theorems -/

/-- Theorem 1: Singleton strategy sets always yield a Nash equilibrium. -/
theorem singleton_is_ne (s r : I) (u1 u2 : I → I → ℝ) :
    IsNashEquilibrium s r [s] [r] u1 u2 := by
  refine ⟨List.mem_cons_self _ _, List.mem_cons_self _ _, ?_, ?_⟩
  · intro t ht; simp [List.mem_singleton] at ht; rw [ht]
  · intro t ht; simp [List.mem_singleton] at ht; rw [ht]

/-- Theorem 2: NE implies membership in strategy sets. -/
theorem ne_implies_membership (s r : I) (S1 S2 : List I) (u1 u2 : I → I → ℝ)
    (h : IsNashEquilibrium s r S1 S2 u1 u2) : s ∈ S1 ∧ r ∈ S2 :=
  ⟨h.1, h.2.1⟩

/-- Theorem 3: Player 1 plays a best response at NE. -/
theorem ne_player1_best_response (s r : I) (S1 S2 : List I) (u1 u2 : I → I → ℝ)
    (h : IsNashEquilibrium s r S1 S2 u1 u2) :
    ∀ t ∈ S1, u1 t r ≤ u1 s r :=
  h.2.2.1

/-- Theorem 4: Player 2 plays a best response at NE. -/
theorem ne_player2_best_response (s r : I) (S1 S2 : List I) (u1 u2 : I → I → ℝ)
    (h : IsNashEquilibrium s r S1 S2 u1 u2) :
    ∀ t ∈ S2, u2 s t ≤ u2 s r :=
  h.2.2.2

/-- Theorem 5: Void vs void in singletons is always a NE. -/
theorem void_void_singleton_ne (u1 u2 : I → I → ℝ) :
    IsNashEquilibrium (void : I) (void : I) [void] [void] u1 u2 :=
  singleton_is_ne _ _ u1 u2

/-- Theorem 6: NE is preserved when payoff functions agree pointwise. -/
theorem ne_preserved_under_payoff_equiv
    (s r : I) (S1 S2 : List I) (u1 u2 u1' u2' : I → I → ℝ)
    (h : IsNashEquilibrium s r S1 S2 u1 u2)
    (h1 : ∀ a b, u1 a b = u1' a b) (h2 : ∀ a b, u2 a b = u2' a b) :
    IsNashEquilibrium s r S1 S2 u1' u2' := by
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · intro t ht; rw [← h1, ← h1]; exact h.2.2.1 t ht
  · intro t ht; rw [← h2, ← h2]; exact h.2.2.2 t ht

/-- Theorem 7: Constant payoffs make every valid profile a NE. -/
theorem constant_payoff_all_ne (s r : I) (S1 S2 : List I)
    (hs : s ∈ S1) (hr : r ∈ S2) (c1 c2 : ℝ) :
    IsNashEquilibrium s r S1 S2 (fun _ _ => c1) (fun _ _ => c2) := by
  exact ⟨hs, hr, fun _ _ => le_refl _, fun _ _ => le_refl _⟩

/-- Theorem 8: Symmetric singleton NE — (s,s) in ([s],[s]). -/
theorem symmetric_singleton_ne (s : I) (u1 u2 : I → I → ℝ) :
    IsNashEquilibrium s s [s] [s] u1 u2 :=
  singleton_is_ne s s u1 u2

/-- Theorem 9: NE in a supergame restricts to a subgame when strategies belong. -/
theorem ne_restricts_to_subgame
    (s r : I) (S1 S2 S1' S2' : List I) (u1 u2 : I → I → ℝ)
    (h : IsNashEquilibrium s r S1 S2 u1 u2)
    (hS1 : S1' ⊆ S1) (hS2 : S2' ⊆ S2)
    (hs : s ∈ S1') (hr : r ∈ S2') :
    IsNashEquilibrium s r S1' S2' u1 u2 := by
  exact ⟨hs, hr,
    fun t ht => h.2.2.1 t (hS1 ht),
    fun t ht => h.2.2.2 t (hS2 ht)⟩

/-- Theorem 10: NE is unique when strategy sets are singletons. -/
theorem ne_unique_in_singletons (s r s' r' : I) (u1 u2 : I → I → ℝ)
    (h : IsNashEquilibrium s' r' [s] [r] u1 u2) :
    s' = s ∧ r' = r := by
  constructor
  · exact List.eq_of_mem_singleton h.1
  · exact List.eq_of_mem_singleton h.2.1

/-! ## §3. Pareto Theorems -/

/-- Theorem 11: Pareto improvement is irreflexive. -/
theorem pareto_improvement_irrefl (s r : I) (u1 u2 : I → I → ℝ) :
    ¬ParetoImproves s r s r u1 u2 := by
  intro ⟨_, _, h3⟩
  rcases h3 with h | h <;> exact absurd h (lt_irrefl _)

/-- Theorem 12: Weak Pareto improvement is reflexive. -/
theorem weak_pareto_refl (s r : I) (u1 u2 : I → I → ℝ) :
    WeakParetoImproves s r s r u1 u2 :=
  ⟨le_refl _, le_refl _⟩

/-- Theorem 13: Pareto improvement implies weak Pareto improvement. -/
theorem pareto_implies_weak (s' r' s r : I) (u1 u2 : I → I → ℝ)
    (h : ParetoImproves s' r' s r u1 u2) :
    WeakParetoImproves s' r' s r u1 u2 :=
  ⟨h.1, h.2.1⟩

/-- Theorem 14: Pareto improvement is asymmetric. -/
theorem pareto_asymmetric (s' r' s r : I) (u1 u2 : I → I → ℝ)
    (h : ParetoImproves s' r' s r u1 u2) :
    ¬ParetoImproves s r s' r' u1 u2 := by
  intro ⟨h1', h2', _⟩
  have h1 := h.1; have h2 := h.2.1
  rcases h.2.2 with hgt | hgt
  · linarith
  · linarith

/-! ## §4. Resonance-Based Payoff Theorems -/

/-- The resonance sender payoff: how much the sender resonates with the interpretation. -/
noncomputable def rsSenderPayoff (s r : I) : ℝ :=
  resonanceStrength s (compose r s)

/-- The resonance receiver payoff: how much the receiver resonates with interpretation. -/
noncomputable def rsReceiverPayoff (s r : I) : ℝ :=
  resonanceStrength r (compose r s)

/-- Theorem 15: Sender payoff is always non-negative. -/
theorem rsSenderPayoff_nonneg (s r : I) : rsSenderPayoff s r ≥ 0 := by
  unfold rsSenderPayoff; exact IdeaticSpace2.rs_nonneg _ _

/-- Theorem 16: Receiver payoff is always non-negative. -/
theorem rsReceiverPayoff_nonneg (s r : I) : rsReceiverPayoff s r ≥ 0 := by
  unfold rsReceiverPayoff; exact IdeaticSpace2.rs_nonneg _ _

/-- Theorem 17: Void signal gives receiver payoff = self-resonance. -/
theorem rsReceiverPayoff_void_signal (r : I) :
    rsReceiverPayoff (void : I) r = resonanceStrength r r := by
  unfold rsReceiverPayoff; rw [IdeaticSpace2.void_right]

/-- Theorem 18: Void receiver gives sender payoff = self-resonance. -/
theorem rsSenderPayoff_void_receiver (s : I) :
    rsSenderPayoff s (void : I) = resonanceStrength s s := by
  unfold rsSenderPayoff; rw [IdeaticSpace2.void_left]

/-- Theorem 19: Receiver payoff with void signal is at least 1. -/
theorem rsReceiverPayoff_void_signal_ge_one (r : I) :
    rsReceiverPayoff (void : I) r ≥ 1 := by
  rw [rsReceiverPayoff_void_signal]; exact rs_self_ge_one r

/-- Theorem 20: Sender payoff with void receiver is at least 1. -/
theorem rsSenderPayoff_void_receiver_ge_one (s : I) :
    rsSenderPayoff s (void : I) ≥ 1 := by
  rw [rsSenderPayoff_void_receiver]; exact rs_self_ge_one s

/-- Theorem 21: Void-void is NE for resonance payoffs in singletons. -/
theorem void_void_resonance_ne :
    IsNashEquilibrium (void : I) (void : I) [void] [void]
      rsSenderPayoff rsReceiverPayoff :=
  singleton_is_ne _ _ _ _

/-- Theorem 22: Self-resonance of interpretation exceeds receiver's self-resonance. -/
theorem interpretation_self_rs_ge_receiver (s r : I) :
    resonanceStrength (compose r s) (compose r s) ≥ resonanceStrength r r :=
  rs_compose_self_right r s

/-- Theorem 22b: Self-resonance of interpretation exceeds sender's self-resonance. -/
theorem interpretation_self_rs_ge_sender (s r : I) :
    resonanceStrength (compose r s) (compose r s) ≥ resonanceStrength s s :=
  rs_compose_self_left s r

/-- Theorem 23: Depth of interpretation is bounded. -/
theorem interpret_depth_bound (s r : I) :
    depth (compose r s) ≤ depth r + depth s :=
  IdeaticSpace2.depth_subadditive r s

/-- Theorem 24: At any NE, sender payoff is maximal over the strategy set. -/
theorem ne_sender_payoff_maximal (s r : I) (S1 S2 : List I)
    (h : IsNashEquilibrium s r S1 S2 rsSenderPayoff rsReceiverPayoff) :
    ∀ t ∈ S1, rsSenderPayoff t r ≤ rsSenderPayoff s r :=
  h.2.2.1

/-- Theorem 25: At any NE, receiver payoff is maximal over the strategy set. -/
theorem ne_receiver_payoff_maximal (s r : I) (S1 S2 : List I)
    (h : IsNashEquilibrium s r S1 S2 rsSenderPayoff rsReceiverPayoff) :
    ∀ t ∈ S2, rsReceiverPayoff s t ≤ rsReceiverPayoff s r :=
  h.2.2.2

/-! ## §5. Dominance -/

/-- Strategy s1 weakly dominates s2 for the sender. -/
def WeaklyDominates (s1 s2 : I) (S2 : List I) (u : I → I → ℝ) : Prop :=
  (∀ r ∈ S2, u s1 r ≥ u s2 r) ∧ (∃ r ∈ S2, u s1 r > u s2 r)

/-- Strategy s1 strongly dominates s2 for the sender. -/
def StronglyDominates (s1 s2 : I) (S2 : List I) (u : I → I → ℝ) : Prop :=
  ∀ r ∈ S2, u s1 r > u s2 r

/-- Theorem 26: Strong dominance implies weak dominance (nonempty opponent set). -/
theorem strong_implies_weak (s1 s2 : I) (S2 : List I) (u : I → I → ℝ)
    (hne : S2 ≠ []) (h : StronglyDominates s1 s2 S2 u) :
    WeaklyDominates s1 s2 S2 u := by
  constructor
  · intro r hr; exact le_of_lt (h r hr)
  · obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil S2 hne
    exact ⟨r, hr, h r hr⟩

/-- Theorem 27: Strong dominance is irreflexive. -/
theorem strong_dominance_irrefl (s : I) (S2 : List I) (u : I → I → ℝ)
    (hne : S2 ≠ []) :
    ¬StronglyDominates s s S2 u := by
  intro h
  obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil S2 hne
  exact absurd (h r hr) (lt_irrefl _)

/-- Theorem 28: A strongly dominated strategy cannot be part of a NE. -/
theorem dominated_not_in_ne (s s' r : I) (S1 S2 : List I) (u1 u2 : I → I → ℝ)
    (hne : IsNashEquilibrium s r S1 S2 u1 u2)
    (hs' : s' ∈ S1) (hdom : StronglyDominates s' s S2 u1)
    (hr : r ∈ S2) :
    False := by
  have h1 := hne.2.2.1 s' hs'
  have h2 := hdom r hr
  linarith

/-! ## §6. Equilibrium Composition -/

/-- Theorem 29: Composing both strategies preserves NE structure in singletons. -/
theorem compose_singleton_ne (s r c : I) (u1 u2 : I → I → ℝ) :
    IsNashEquilibrium (compose c s) (compose c r)
      [compose c s] [compose c r] u1 u2 :=
  singleton_is_ne _ _ u1 u2

/-- Theorem 30: NE existence in nonempty sets with constant payoffs. -/
theorem ne_exists_constant_payoff (S1 S2 : List I) (c1 c2 : ℝ)
    (h1 : S1 ≠ []) (h2 : S2 ≠ []) :
    ∃ s r, IsNashEquilibrium s r S1 S2 (fun _ _ => c1) (fun _ _ => c2) := by
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil S1 h1
  obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil S2 h2
  exact ⟨s, r, constant_payoff_all_ne s r S1 S2 hs hr c1 c2⟩

end IDT2.Equilibrium
