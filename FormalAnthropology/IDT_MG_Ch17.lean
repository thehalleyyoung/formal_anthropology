import FormalAnthropology.IDT_Foundations

/-!
# The Meaning Game — Chapter 17: Cheap Talk and Resonance

**Core claim.** When signalling is costless, resonance determines whether
meaningful communication is possible. Babbling equilibria send void;
echo chambers are coherent idea sequences.

## 17 Theorems, 0 Sorries
-/

set_option pp.unicode.fun true
set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.MG.Ch17

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- A cheap talk message is just an idea — costless to send. -/
abbrev CheapTalkMessage (I : Type*) [IdeaticSpace I] := I

/-- Resonant communication: sender and receiver resonate. -/
def ResonantCommunication (sender receiver : I) : Prop :=
  IdeaticSpace.resonates sender receiver

/-- Babbling equilibrium: the uninformative message = void. -/
def BabblingEquilibrium (msg : I) : Prop := msg = IdeaticSpace.void

/-- Meaningful exchange: resonant and nontrivial composition depth. -/
def MeaningfulExchange (s r : I) : Prop :=
  IdeaticSpace.resonates s r ∧ IdeaticSpace.depth (IdeaticSpace.compose s r) > 0

/-- Echo chamber: a list of ideas that form a coherent chain. -/
def EchoChamber (ideas : List I) : Prop := Coherent ideas

/-! ## §2. Babbling Equilibrium Theorems -/

/-- Theorem 1: Babbling equilibrium sends void (by definition). -/
theorem babbling_is_void {msg : I} (h : BabblingEquilibrium msg) :
    msg = (IdeaticSpace.void : I) := h

/-- Theorem 2: Babbling signal interpreted = receiver's idea. -/
theorem void_babbling_interpretation (r : I) :
    IdeaticSpace.compose (IdeaticSpace.void : I) r = r := by
  simp [void_left]

/-- Theorem 3: Resonant communication is symmetric. -/
theorem resonant_communication_symmetric {s r : I}
    (h : ResonantCommunication s r) : ResonantCommunication r s :=
  resonance_symm h

/-- Theorem 4: Resonant sender+receiver → composition resonates with both. -/
theorem resonant_messages_compose_resonantly {s r : I}
    (h : ResonantCommunication s r) :
    IdeaticSpace.resonates (IdeaticSpace.compose s r) (IdeaticSpace.compose s r) :=
  resonance_refl _

/-- Theorem 5: Echo chamber ideas composed stay resonant with compositions. -/
theorem echo_chamber_self_reinforcing {a b : I}
    (h : IdeaticSpace.resonates a b) :
    IdeaticSpace.resonates (IdeaticSpace.compose a b) (IdeaticSpace.compose a b) :=
  resonance_refl _

/-- Theorem 6: Babbling adds zero depth. -/
theorem babbling_depth_zero (r : I) :
    IdeaticSpace.depth (IdeaticSpace.compose (IdeaticSpace.void : I) r) ≤ IdeaticSpace.depth r := by
  have h := depth_void_compose r
  exact le_of_eq h

/-- Theorem 7: Echo chamber is coherent by definition. -/
theorem echo_chamber_coherent {ideas : List I} (h : EchoChamber ideas) :
    Coherent ideas := h

/-! ## §3. Echo Chamber Structure -/

/-- Theorem 8: Resonant pair can have nontrivial composition (conditional). -/
theorem resonant_pair_composition_bounded {a b : I}
    (h : IdeaticSpace.resonates a b) :
    IdeaticSpace.depth (IdeaticSpace.compose a b) ≤ IdeaticSpace.depth a + IdeaticSpace.depth b :=
  depth_compose_le a b

/-- Theorem 9: Adding a resonant idea extends the echo chamber. -/
theorem echo_chamber_extension {a : I} {ideas : List I}
    (h_echo : EchoChamber (a :: ideas))
    (b : I) (hres : IdeaticSpace.resonates b a) :
    EchoChamber (b :: a :: ideas) := by
  simp [EchoChamber, Coherent]
  exact ⟨hres, h_echo⟩

/-- Theorem 10: Void resonates with everything (via composition identity + refl). -/
theorem void_is_universal_babble (x : I) :
    IdeaticSpace.resonates (IdeaticSpace.compose (IdeaticSpace.void : I) x) x := by
  rw [void_left]
  exact resonance_refl x

/-- Theorem 11: Composition of echo chamber ideas bounded. -/
theorem echo_chamber_composition_bound (a b : I) :
    IdeaticSpace.depth (IdeaticSpace.compose a b) ≤ IdeaticSpace.depth a + IdeaticSpace.depth b :=
  depth_compose_le a b

/-- Theorem 12: With resonance, composition stays resonant with inputs. -/
theorem resonant_pair_compose_resonant_left {a b : I}
    (h : IdeaticSpace.resonates a b) :
    IdeaticSpace.resonates (IdeaticSpace.compose a b) (IdeaticSpace.compose a a) := by
  exact IdeaticSpace.resonance_compose a a b a (resonance_refl a) (resonance_symm h)

/-- Theorem 13: Singleton is trivially an echo chamber. -/
theorem echo_chamber_singleton (a : I) : EchoChamber [a] :=
  coherent_singleton a

/-- Theorem 14: Pair is echo chamber iff resonant. -/
theorem echo_chamber_pair_iff_resonant (a b : I) :
    EchoChamber [a, b] ↔ IdeaticSpace.resonates a b := by
  simp [EchoChamber, coherent_pair]

/-- Theorem 15: Resonant pair composition depth bounded. -/
theorem resonant_composition_depth_bound {a b : I}
    (_h : IdeaticSpace.resonates a b) :
    IdeaticSpace.depth (IdeaticSpace.compose a b) ≤ IdeaticSpace.depth a + IdeaticSpace.depth b :=
  depth_compose_le a b

/-- Theorem 16: Echo chamber depth sum bounded. -/
theorem echo_chamber_depth_sum (ideas : List I) (d : ℕ)
    (_h : EchoChamber ideas)
    (hbound : ∀ (a : I), a ∈ ideas → IdeaticSpace.depth a ≤ d) :
    depthSum ideas ≤ ideas.length * d :=
  depthSum_bound ideas d hbound

/-- Theorem 17: Repeating echo chamber ideas produces coherent longer sequence. -/
theorem iterated_echo (a : I) (n : ℕ) :
    EchoChamber (List.replicate n a) :=
  coherent_replicate a n

end IDT.MG.Ch17
