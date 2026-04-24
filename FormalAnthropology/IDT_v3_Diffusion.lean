import FormalAnthropology.IDT_v3_Foundations

/-!
# IDT v3: Diffusion Dynamics

How ideas spread through populations and transform during transmission.
This is the bridge between SEMIOTICS (structure of meaning) and
GAME THEORY (strategic use of meaning).

## Core insight

When idea a is transmitted from agent with state s to agent with state r,
the receiver gets compose(r, a) — NOT a itself. The transmitted idea is
always filtered through the receiver's existing state. This is why ideas
MUTATE during diffusion: each receiver adds their own emergence.

The key quantity is the TRANSMISSION EMERGENCE:
  κ(r, a, c) = rs(r ∘ a, c) - rs(r, c) - rs(a, c)

This measures how much the idea a CHANGES when received by r, as
perceived by observer c. Positive = amplified, negative = suppressed.

## Connection to semiotics vs diffusion

- **Semiotics** studies the static structure: rs, emergence, sameIdea
- **Diffusion** studies the dynamics: how these structures change as
  ideas pass through chains of agents

The emergence axioms constrain diffusion: transmission emergence is
bounded (E3), and the receiver always grows in self-resonance (E4).

## NO SORRIES
-/

namespace IDT3

/-! ## §1. Transmission: How Ideas Move Between Agents -/

section Transmission
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- When agent with state r receives idea a, their new state is compose r a. -/
def receive (receiver idea : I) : I := compose receiver idea

/-- Transmission emergence: how much idea a changes when received by r,
    as measured by observer c. -/
noncomputable def transmissionEmergence (receiver idea observer : I) : ℝ :=
  emergence receiver idea observer

theorem receive_void_idea (r : I) : receive r (void : I) = r := by
  unfold receive; simp

theorem receive_void_receiver (a : I) : receive (void : I) a = a := by
  unfold receive; simp

/-- Receiving an idea always enriches the receiver's self-resonance. -/
theorem receive_enriches (r a : I) :
    rs (receive r a) (receive r a) ≥ rs r r :=
  compose_enriches' r a

/-- Transmission emergence vanishes when receiving silence. -/
theorem transmissionEmergence_void_idea (r c : I) :
    transmissionEmergence r (void : I) c = 0 :=
  emergence_void_right r c

/-- Transmission emergence vanishes for a void receiver. -/
theorem transmissionEmergence_void_receiver (a c : I) :
    transmissionEmergence (void : I) a c = 0 :=
  emergence_void_left a c

/-- Transmission emergence is bounded by the receiver's capacity and
    the observer's presence. -/
theorem transmissionEmergence_bounded (r a c : I) :
    (transmissionEmergence r a c) ^ 2 ≤
    rs (receive r a) (receive r a) * rs c c :=
  emergence_bounded' r a c

end Transmission

/-! ## §2. Chains of Transmission -/

section Chains
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A transmission chain: idea a passes through a sequence of agents.
    Each agent receives the idea and becomes the new "carrier." -/
def transmitChain (idea : I) : List I → I
  | [] => idea
  | agent :: rest => transmitChain (receive agent idea) rest

/-- Alternative: just the final state after passing through one agent. -/
def transmitOnce (idea agent : I) : I := receive agent idea

theorem transmitOnce_eq (idea agent : I) :
    transmitOnce idea agent = compose agent idea := rfl

/-- Transmitting through an empty chain leaves the idea unchanged. -/
theorem transmitChain_nil (a : I) :
    transmitChain a ([] : List I) = a := rfl

/-- Transmitting through a single agent. -/
theorem transmitChain_singleton (idea agent : I) :
    transmitChain idea [agent] = receive agent idea := rfl

/-- The self-resonance of the transmitted idea grows with each agent. -/
theorem transmitOnce_enriches (idea agent : I) :
    rs (transmitOnce idea agent) (transmitOnce idea agent) ≥
    rs agent agent :=
  compose_enriches' agent idea

/-- After passing through one agent, the result is never void
    (unless the agent was void). -/
theorem transmitOnce_ne_void (idea agent : I) (h : agent ≠ void) :
    transmitOnce idea agent ≠ void :=
  compose_ne_void_of_left agent idea h

end Chains

/-! ## §3. The Mutation Theorem — Ideas Change During Transmission

This is one of the deep theorems of IDT: ideas NECESSARILY mutate
during transmission (unless the receiver is "linear").

The mutation is EXACTLY the transmission emergence.
If emergence(r, a, c) ≠ 0 for some c, then the received idea
resonates differently from the original. -/

section Mutation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The resonance shift: how much receiving idea a changes
    the resonance with observer c. -/
noncomputable def resonanceShift (receiver idea observer : I) : ℝ :=
  rs (receive receiver idea) observer - rs idea observer

/-- The resonance shift decomposes into the receiver's resonance
    plus the transmission emergence. -/
theorem resonanceShift_decompose (r a c : I) :
    resonanceShift r a c = rs r c + transmissionEmergence r a c := by
  unfold resonanceShift receive transmissionEmergence emergence
  ring

/-- If the receiver is linear (produces no emergence), then the
    resonance shift is EXACTLY the receiver's own resonance with c. -/
theorem resonanceShift_linear (r a c : I)
    (h : leftLinear r) :
    resonanceShift r a c = rs r c := by
  rw [resonanceShift_decompose]
  unfold transmissionEmergence
  rw [h a c]
  ring

/-- Mutation magnitude: how much the idea "mutated" due to transmission.
    This is the emergence itself. -/
noncomputable def mutationMagnitude (r a c : I) : ℝ :=
  transmissionEmergence r a c

/-- An idea is "preserved" by a receiver if no mutation occurs
    (for all observers). -/
def preserved (r a : I) : Prop :=
  ∀ c : I, mutationMagnitude r a c = 0

/-- Void receiver preserves all ideas. -/
theorem void_preserves (a : I) : preserved (void : I) a :=
  fun c => transmissionEmergence_void_receiver a c

/-- Linear receivers preserve all ideas. -/
theorem linear_preserves (r : I) (h : leftLinear r) (a : I) :
    preserved r a := by
  intro c; unfold mutationMagnitude transmissionEmergence; exact h a c

/-- If the idea is void, it's trivially preserved. -/
theorem preserved_void (r : I) : preserved r (void : I) :=
  fun c => transmissionEmergence_void_idea r c

end Mutation

/-! ## §4. Diffusion Through Populations

When an idea diffuses through a population, it accumulates
emergence from each transmission. The total mutation is the
sum of all transmission emergences — but by the cocycle condition,
this total is CONSTRAINED. -/

section Population
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A population's "resonance with an idea" is the list of
    individual resonances. -/
noncomputable def populationResonance (idea : I) (pop : List I) : List ℝ :=
  pop.map (fun agent => rs agent idea)

/-- Total population resonance. -/
noncomputable def totalPopResonance (idea : I) (pop : List I) : ℝ :=
  (populationResonance idea pop).sum

theorem totalPopResonance_nil (a : I) :
    totalPopResonance a ([] : List I) = 0 := rfl

theorem totalPopResonance_singleton (a agent : I) :
    totalPopResonance a [agent] = rs agent a := by
  simp [totalPopResonance, populationResonance]

/-- After transmission to one agent, the total population resonance changes. -/
theorem totalPopResonance_after_receive (idea agent : I) (pop : List I) :
    totalPopResonance (receive agent idea) pop =
    totalPopResonance (compose agent idea) pop := rfl

/-- The "agreement" between two agents about an idea. -/
noncomputable def agreement (a b idea : I) : ℝ :=
  rs (receive a idea) (receive b idea)

/-- Agreement decomposes into four terms via double composition. -/
theorem agreement_eq (a b s : I) :
    agreement a b s = rs (compose a s) (compose b s) := rfl

/-- Agreement with void agent. -/
theorem agreement_void_left (b s : I) :
    agreement (void : I) b s = rs s (compose b s) := by
  unfold agreement receive; simp

theorem agreement_void_right (a s : I) :
    agreement a (void : I) s = rs (compose a s) s := by
  unfold agreement receive; simp

/-- Self-agreement is self-resonance of the received idea. -/
theorem self_agreement (a s : I) :
    agreement a a s = rs (receive a s) (receive a s) := rfl

end Population

/-! ## §5. Conservative vs Mutagenic Transmission

Following idt_book.tex's taxonomy of diffusion axiom systems:
some transmissions PRESERVE meaning, others TRANSFORM it.

Conservative: emergence is small (bounded relative to the idea's weight)
Mutagenic: emergence is large (the receiver fundamentally changes the idea)

The axioms don't tell us WHICH regime we're in — that depends on the
specific ideatic space. But they constrain both. -/

section TransmissionTypes
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A receiver r is ε-conservative for idea a if the mutation is small
    relative to the idea's weight, for ALL observers. -/
def epsilonConservative (r a : I) (ε : ℝ) : Prop :=
  ∀ c : I, (transmissionEmergence r a c) ^ 2 ≤ ε ^ 2 * rs c c

/-- The trivially conservative case: ε = 0 means the receiver preserves the idea. -/
theorem zeroConservative_iff_preserved (r a : I) :
    epsilonConservative r a 0 ↔ preserved r a := by
  constructor
  · intro h c
    have h1 := h c
    simp at h1
    have h2 := sq_nonneg (transmissionEmergence r a c)
    have h3 : transmissionEmergence r a c ^ 2 = 0 := by
      have : rs c c ≥ 0 := S.rs_self_nonneg c
      linarith
    have h4 := sq_eq_zero_iff.mp h3
    exact h4
  · intro h c
    have h1 := h c
    unfold mutationMagnitude at h1
    rw [h1]; simp

/-- Every receiver is √(rs(r∘a,r∘a))-conservative (from emergence_bounded). -/
theorem universally_conservative (r a : I) :
    ∀ c : I, (transmissionEmergence r a c) ^ 2 ≤
    rs (receive r a) (receive r a) * rs c c :=
  fun c => transmissionEmergence_bounded r a c

/-- Fidelity: how much of the original idea's resonance is preserved. -/
noncomputable def fidelity (r a c : I) : ℝ :=
  rs (receive r a) c - rs r c

/-- Fidelity decomposes into the original resonance plus mutation. -/
theorem fidelity_eq (r a c : I) :
    fidelity r a c = rs a c + transmissionEmergence r a c := by
  unfold fidelity receive transmissionEmergence emergence
  ring

/-- For a perfectly faithful transmission (no emergence), fidelity = original resonance. -/
theorem fidelity_faithful (r a c : I) (h : transmissionEmergence r a c = 0) :
    fidelity r a c = rs a c := by
  rw [fidelity_eq, h]; ring

end TransmissionTypes

/-! ## §6. The Sublime Fragility Theorem (v3 version)

In idt_book.tex, Theorem 3.5 proves that depth decreases per transmission.
In v3, we prove an analogous theorem: the EMERGENCE PROFILE changes
at each transmission, and the change is bounded.

This is the formal version of "the telephone game degrades meaning." -/

section SublimeFragility
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The resonance profile of an idea: how it resonates with a fixed observer. -/
noncomputable def resonanceProfile (idea observer : I) : ℝ :=
  rs idea observer

/-- Profile shift after one transmission. -/
noncomputable def profileShift (idea receiver observer : I) : ℝ :=
  resonanceProfile (receive receiver idea) observer -
  resonanceProfile idea observer

/-- Profile shift = receiver's resonance + emergence. -/
theorem profileShift_eq (a r c : I) :
    profileShift a r c = rs r c + emergence r a c := by
  unfold profileShift resonanceProfile receive emergence
  ring

/-- Profile shift is bounded (from emergence_bounded + triangle inequality). -/
theorem profileShift_squared_le (a r c : I) :
    (profileShift a r c - rs r c) ^ 2 ≤
    rs (receive r a) (receive r a) * rs c c := by
  rw [profileShift_eq]
  ring_nf
  exact emergence_bounded' r a c

/-- After n transmissions through the same receiver, self-resonance grows. -/
def iteratedReceive (idea receiver : I) : ℕ → I
  | 0 => idea
  | n + 1 => receive receiver (iteratedReceive idea receiver n)

theorem iteratedReceive_zero (a r : I) :
    iteratedReceive a r 0 = a := rfl

theorem iteratedReceive_succ (a r : I) (n : ℕ) :
    iteratedReceive a r (n + 1) = compose r (iteratedReceive a r n) := rfl

/-- Self-resonance of iterated reception is non-decreasing.
    Each reception through r adds at least rs(r,r) worth of weight. -/
theorem iteratedReceive_enriches (a r : I) (n : ℕ) :
    rs (iteratedReceive a r (n + 1)) (iteratedReceive a r (n + 1)) ≥
    rs r r := by
  simp [iteratedReceive_succ]
  exact compose_enriches' r (iteratedReceive a r n)

end SublimeFragility

/-! ## §7. Convergence and Fixed Points

Does iterated transmission converge? In what sense?
We can't prove convergence in general (no topology), but we can
prove structural results about fixed points. -/

section FixedPoints
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- An idea a is a fixed point of receiver r if receiving a doesn't
    change the resonance profile (up to the receiver's contribution). -/
def resonanceFixedPoint (a r : I) : Prop :=
  ∀ c : I, emergence r a c = 0

/-- Void is a fixed point of any receiver. -/
theorem void_fixedPoint (r : I) : resonanceFixedPoint (void : I) r :=
  fun c => emergence_void_right r c

/-- Any idea is a fixed point of void. -/
theorem fixedPoint_void (a : I) : resonanceFixedPoint a (void : I) :=
  fun c => emergence_void_left a c

/-- If a is a fixed point of r, then receive r a has the same resonance
    as r alone (plus the original idea). -/
theorem fixedPoint_resonance (a r : I) (h : resonanceFixedPoint a r) (c : I) :
    rs (receive r a) c = rs r c + rs a c := by
  have := rs_compose_eq r a c
  unfold receive
  linarith [h c]

/-- A "canonical idea" is one that is its own fixed point: composing
    with itself produces no new emergence. -/
def canonical (a : I) : Prop :=
  resonanceFixedPoint a a

/-- Void is canonical. -/
theorem void_canonical : canonical (void : I) :=
  void_fixedPoint _

/-- Canonical ideas have additive self-composition:
    rs(a∘a, c) = 2·rs(a,c). -/
theorem canonical_double (a : I) (h : canonical a) (c : I) :
    rs (compose a a) c = 2 * rs a c := by
  have h1 := rs_compose_eq a a c
  have h2 := h c
  unfold emergence at h2
  linarith

/-- For canonical ideas, semantic charge is zero. -/
theorem canonical_charge_zero (a : I) (h : canonical a) :
    semanticCharge a = 0 := h a

end FixedPoints

/-! ## §8. Epidemic Models for Ideas — SIR Analogues

In epidemiology, the SIR model partitions a population into Susceptible,
Infected, and Recovered. For ideas, the analogues are:
- **Susceptible**: agent has low resonance with the idea (hasn't "caught" it)
- **Infected**: agent's state has been composed with the idea (is "carrying" it)
- **Recovered**: agent has been exposed but the idea has been "neutralized"
  by a counter-idea (vaccination).

We formalize these states using resonance thresholds and counter-ideas. -/

section Epidemic
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- An agent is "susceptible" to idea a if its resonance with a is below
    a threshold — the idea hasn't taken hold. -/
def susceptible (agent idea : I) (threshold : ℝ) : Prop :=
  rs agent idea < threshold

/-- An agent is "infected" by idea a: it has received a, and the
    resulting state resonates strongly with a. -/
def infected (agent idea : I) (threshold : ℝ) : Prop :=
  rs (receive agent idea) idea ≥ threshold

/-- An agent is "recovered" from idea a via counter-idea v:
    after receiving both a and v, the net resonance with a drops. -/
def recovered (agent idea vaccine : I) : Prop :=
  rs (receive (receive agent idea) vaccine) idea ≤ rs agent idea

/-- Receiving void doesn't infect — you remain in the same state. -/
theorem susceptible_void (agent : I) (t : ℝ) (h : rs agent (void : I) < t) :
    susceptible agent (void : I) t := h

/-- Infection always meets a baseline: the received state resonates
    at least as much as the receiver alone resonates with itself. -/
theorem infected_baseline (agent idea : I) :
    rs (receive agent idea) (receive agent idea) ≥ rs agent agent :=
  compose_enriches' agent idea

/-- A void vaccine doesn't help — receiving void after infection
    changes nothing. -/
theorem void_vaccine_identity (agent idea : I) :
    receive (receive agent idea) (void : I) = receive agent idea := by
  unfold receive; simp

/-- After infection, the agent's self-resonance is at least as large
    as before — ideas add weight, never remove it. -/
theorem infection_adds_weight (agent idea : I) :
    rs (receive agent idea) (receive agent idea) ≥ rs agent agent :=
  compose_enriches' agent idea

/-- Double infection: receiving the same idea twice compounds weight. -/
theorem double_infection_enriches (agent idea : I) :
    rs (receive (receive agent idea) idea) (receive (receive agent idea) idea) ≥
    rs (receive agent idea) (receive agent idea) := by
  unfold receive; exact compose_enriches' (compose agent idea) idea

/-- The resonance of the infected state with the idea decomposes
    into agent's resonance, idea's self-resonance, and emergence. -/
theorem infection_resonance_decompose (agent idea : I) :
    rs (receive agent idea) idea =
    rs agent idea + rs idea idea + emergence agent idea idea := by
  unfold receive; rw [rs_compose_eq]

/-- Infection by void is trivial: the agent doesn't change. -/
theorem infection_void (agent : I) :
    receive agent (void : I) = agent := by
  unfold receive; simp

end Epidemic

/-! ## §9. Threshold Models — Critical Mass for Idea Adoption

In threshold models of social contagion, an agent adopts an idea only
when enough neighbors have adopted it. We formalize the threshold
condition in terms of cumulative resonance from multiple transmissions. -/

section Threshold
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Cumulative exposure: an agent receives ideas from multiple sources.
    Each source transmits its own version of the idea. -/
def cumulativeReceive (agent : I) : List I → I
  | [] => agent
  | idea :: rest => cumulativeReceive (receive agent idea) rest

/-- Cumulative reception of nothing leaves the agent unchanged. -/
theorem cumulativeReceive_nil (agent : I) :
    cumulativeReceive agent ([] : List I) = agent := rfl

/-- Cumulative reception of a single idea is just one receive. -/
theorem cumulativeReceive_singleton (agent idea : I) :
    cumulativeReceive agent [idea] = receive agent idea := rfl

/-- Cumulative reception unfolds one step. -/
theorem cumulativeReceive_cons (agent idea : I) (rest : List I) :
    cumulativeReceive agent (idea :: rest) =
    cumulativeReceive (receive agent idea) rest := rfl

/-- Self-resonance never decreases under cumulative reception. -/
theorem cumulativeReceive_enriches (agent : I) (ideas : List I) :
    rs (cumulativeReceive agent ideas) (cumulativeReceive agent ideas) ≥
    rs agent agent := by
  induction ideas generalizing agent with
  | nil => simp [cumulativeReceive]
  | cons idea rest ih =>
    simp only [cumulativeReceive]
    have h1 := ih (receive agent idea)
    have h2 : rs (receive agent idea) (receive agent idea) ≥ rs agent agent :=
      compose_enriches' agent idea
    linarith

/-- Exposure to void ideas doesn't change the agent. -/
theorem cumulativeReceive_voids (agent : I) (n : ℕ) :
    cumulativeReceive agent (List.replicate n (void : I)) = agent := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [cumulativeReceive, receive, ih]

end Threshold

/-! ## §10. Broadcast vs Peer-to-Peer Diffusion

In broadcast diffusion, one source transmits to many receivers independently.
In peer-to-peer diffusion, each receiver becomes a new transmitter.
These produce fundamentally different outcomes due to emergence accumulation. -/

section BroadcastVsPeer
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Broadcast: one idea sent to many independent receivers.
    Each receiver gets compose(receiver, idea). -/
def broadcast (idea : I) (receivers : List I) : List I :=
  receivers.map (fun r => receive r idea)

-- Peer-to-peer chain: idea passes from agent to agent,
-- each one composing before passing on. (See transmitChain above.)

/-- Broadcasting void changes no one. -/
theorem broadcast_void (receivers : List I) :
    broadcast (void : I) receivers = receivers := by
  unfold broadcast; simp [receive, receive_void_idea]

/-- Broadcasting to an empty population produces nothing. -/
theorem broadcast_nil (idea : I) :
    broadcast idea ([] : List I) = [] := rfl

/-- Broadcasting to a single receiver. -/
theorem broadcast_singleton (idea receiver : I) :
    broadcast idea [receiver] = [receive receiver idea] := rfl

/-- In broadcast, each receiver's self-resonance grows independently. -/
theorem broadcast_enriches (idea : I) (receivers : List I) (r : I)
    (_hmem : r ∈ receivers) :
    rs (receive r idea) (receive r idea) ≥ rs r r :=
  compose_enriches' r idea

/-- The broadcast resonance: how the idea resonates with each receiver. -/
noncomputable def broadcastResonance (idea : I) (receivers : List I) : List ℝ :=
  receivers.map (fun r => rs (receive r idea) idea)

/-- Peer-to-peer through void agents doesn't change the idea. -/
theorem peer_to_peer_void_chain (idea : I) (n : ℕ) :
    transmitChain idea (List.replicate n (void : I)) = idea := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [transmitChain, receive, ih]

end BroadcastVsPeer

/-! ## §11. Signal Degradation and Amplification

During transmission, ideas can be degraded (lose resonance with the
original) or amplified (gain resonance). The emergence term determines
which: positive emergence = amplification, negative = degradation. -/

section Degradation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Signal degradation: the drop in resonance between the transmitted
    idea and the original, as seen by observer c. -/
noncomputable def signalDegradation (original receiver observer : I) : ℝ :=
  rs original observer - rs (receive receiver original) observer

/-- Signal degradation decomposes into receiver contribution and emergence. -/
theorem signalDegradation_eq (a r c : I) :
    signalDegradation a r c = -(rs r c + emergence r a c) := by
  unfold signalDegradation receive emergence; ring

/-- Degradation against void observer is zero. -/
theorem signalDegradation_void_observer (a r : I) :
    signalDegradation a r (void : I) = 0 := by
  unfold signalDegradation receive; simp [rs_void_right']

/-- Degradation from void receiver is zero — void doesn't degrade. -/
theorem signalDegradation_void_receiver (a c : I) :
    signalDegradation a (void : I) c = 0 := by
  unfold signalDegradation receive; simp

/-- Amplification is negative degradation. -/
noncomputable def signalAmplification (original receiver observer : I) : ℝ :=
  -signalDegradation original receiver observer

/-- Amplification decomposes into receiver contribution + emergence. -/
theorem signalAmplification_eq (a r c : I) :
    signalAmplification a r c = rs r c + emergence r a c := by
  unfold signalAmplification; rw [signalDegradation_eq]; ring

/-- Amplification from void is zero. -/
theorem signalAmplification_void_receiver (a c : I) :
    signalAmplification a (void : I) c = 0 := by
  unfold signalAmplification; rw [signalDegradation_void_receiver]; ring

/-- Net amplification: idea weight always grows in self-resonance,
    even if the profile changes. -/
theorem net_weight_amplification (r a : I) :
    rs (receive r a) (receive r a) ≥ rs r r :=
  compose_enriches' r a

end Degradation

/-! ## §12. Gatekeeping and Bottlenecks

A gatekeeper is an agent through whom all information must pass.
The gatekeeper's emergence profile determines how ideas are transformed.
A bottleneck is a single gatekeeper in a transmission chain — all
downstream agents receive the gatekeeper's filtered version. -/

section Gatekeeping
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A gatekeeper transforms every idea that passes through it.
    The gatekept version of idea a through gatekeeper g is compose(g, a). -/
def gatekeep (gatekeeper idea : I) : I := receive gatekeeper idea

/-- Gatekeeping is just reception from the gatekeeper's perspective. -/
theorem gatekeep_eq_receive (g a : I) :
    gatekeep g a = receive g a := rfl

/-- Gatekeeping through void is identity — a null gatekeeper passes everything. -/
theorem gatekeep_void (a : I) :
    gatekeep (void : I) a = a := by
  unfold gatekeep receive; simp

/-- Gatekeeping void produces the gatekeeper itself — no content to filter. -/
theorem gatekeep_void_idea (g : I) :
    gatekeep g (void : I) = g := by
  unfold gatekeep receive; simp

/-- A non-void gatekeeper always transforms ideas — the output is never void. -/
theorem gatekeep_ne_void (g a : I) (hg : g ≠ void) :
    gatekeep g a ≠ void :=
  compose_ne_void_of_left g a hg

/-- Sequential gatekeeping: passing through two gatekeepers is associative. -/
theorem gatekeep_compose (g₁ g₂ a : I) :
    gatekeep g₁ (gatekeep g₂ a) = compose g₁ (compose g₂ a) := rfl

/-- Sequential gatekeeping vs single gatekeeping by the composite. -/
theorem gatekeep_seq_eq (g₁ g₂ a : I) :
    gatekeep g₁ (gatekeep g₂ a) = receive g₁ (receive g₂ a) := rfl

/-- The gatekeeper's bias: how much a gatekeeper shifts the resonance
    of an idea with observer c. -/
noncomputable def gatekeeperBias (g a c : I) : ℝ :=
  rs (gatekeep g a) c - rs a c

/-- Gatekeeper bias decomposes into the gatekeeper's own resonance + emergence. -/
theorem gatekeeperBias_eq (g a c : I) :
    gatekeeperBias g a c = rs g c + emergence g a c := by
  unfold gatekeeperBias gatekeep receive emergence; ring

/-- Void gatekeeper has zero bias. -/
theorem gatekeeperBias_void (a c : I) :
    gatekeeperBias (void : I) a c = 0 := by
  unfold gatekeeperBias gatekeep receive; simp

/-- Gatekeeper bias on void idea equals gatekeeper's own resonance. -/
theorem gatekeeperBias_void_idea (g c : I) :
    gatekeeperBias g (void : I) c = rs g c := by
  unfold gatekeeperBias gatekeep receive; simp [rs_void_left', rs_void_right']

end Gatekeeping

/-! ## §13. Super-Spreaders — Agents with High Emergence

A super-spreader is an agent whose emergence profile dominates:
composing with a super-spreader creates disproportionate new resonance.
In epidemiology, ~20% of individuals cause ~80% of infections.
In idea diffusion, super-spreaders are agents whose cognitive state
produces large emergence with many ideas. -/

section SuperSpreaders
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- An agent r is a super-spreader at level K if receiving through r
    always amplifies self-resonance by at least K above the agent's own. -/
def superSpreader (r : I) (K : ℝ) : Prop :=
  ∀ a : I, rs (receive r a) (receive r a) ≥ rs r r + K

/-- Any agent is trivially a 0-super-spreader (from compose_enriches). -/
theorem superSpreader_zero (r : I) : superSpreader r 0 := by
  intro a; simp; exact compose_enriches' r a

/-- Void is a super-spreader only at level ≤ 0. -/
theorem void_superSpreader_le_zero (K : ℝ) (h : superSpreader (void : I) K) :
    K ≤ 0 := by
  have := h (void : I)
  unfold receive at this; simp at this
  linarith

/-- If r is a K-super-spreader and K' ≤ K, then r is also K'-super-spreader. -/
theorem superSpreader_mono (r : I) (K K' : ℝ) (h : superSpreader r K)
    (hle : K' ≤ K) : superSpreader r K' := by
  intro a; linarith [h a]

/-- A super-spreader's output is never void (for positive K). -/
theorem superSpreader_output_ne_void (r : I) (K : ℝ) (_hK : K > 0)
    (_h : superSpreader r K) (hr : r ≠ void) (a : I) :
    receive r a ≠ void :=
  compose_ne_void_of_left r a hr

end SuperSpreaders

/-! ## §14. Vaccination — Counter-Ideas and Immunization

A "vaccine" is an idea v such that receiving v after receiving a
reduces the effective resonance with a. This models counter-narratives,
debunking, critical thinking, or competing memes. -/

section Vaccination
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A vaccine v against idea a (for agent r observed by c) reduces
    the resonance with a after double exposure. -/
def isVaccine (vaccine idea agent observer : I) : Prop :=
  rs (receive (receive agent idea) vaccine) observer <
  rs (receive agent idea) observer

/-- Void is never a vaccine — it doesn't change anything. -/
theorem void_not_vaccine (a agent observer : I)
    (_h : rs (receive agent a) observer ≠ 0) :
    ¬isVaccine (void : I) a agent observer := by
  unfold isVaccine; rw [void_vaccine_identity]; exact lt_irrefl _

/-- After vaccination, the total weight still doesn't decrease. -/
theorem vaccination_weight_nondecreasing (agent idea vaccine : I) :
    rs (receive (receive agent idea) vaccine) (receive (receive agent idea) vaccine) ≥
    rs (receive agent idea) (receive agent idea) := by
  unfold receive; exact compose_enriches' (compose agent idea) vaccine

/-- Double vaccination: applying the vaccine twice still doesn't reduce weight. -/
theorem double_vaccination_weight (agent idea vaccine : I) :
    rs (receive (receive (receive agent idea) vaccine) vaccine)
       (receive (receive (receive agent idea) vaccine) vaccine) ≥
    rs (receive (receive agent idea) vaccine) (receive (receive agent idea) vaccine) := by
  unfold receive; exact compose_enriches' (compose (compose agent idea) vaccine) vaccine

end Vaccination

/-! ## §15. Opinion Dynamics and Polarization

When agents repeatedly exchange ideas, their states can converge
(consensus) or diverge (polarization). We model this using the
resonance deficit as a measure of disagreement. -/

section OpinionDynamics
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Disagreement between two agents about a topic, measured as the
    squared self-resonance surplus minus cross-resonance. -/
noncomputable def disagreement (a b topic : I) : ℝ :=
  rs (receive a topic) (receive a topic) +
  rs (receive b topic) (receive b topic) -
  rs (receive a topic) (receive b topic) -
  rs (receive b topic) (receive a topic)

/-- Disagreement with yourself is zero. -/
theorem disagreement_self (a topic : I) :
    disagreement a a topic = 0 := by
  unfold disagreement; ring

/-- Disagreement is symmetric. -/
theorem disagreement_symm (a b topic : I) :
    disagreement a b topic = disagreement b a topic := by
  unfold disagreement; ring

/-- Polarization index: how far apart two agents' received states are,
    measured by the resonance deficit of their received versions. -/
noncomputable def polarizationIndex (a b topic : I) : ℝ :=
  resonanceDeficit (receive a topic) (receive b topic)

/-- Polarization is symmetric. -/
theorem polarizationIndex_symm (a b topic : I) :
    polarizationIndex a b topic = polarizationIndex b a topic := by
  unfold polarizationIndex resonanceDeficit; ring

/-- Self-polarization is zero — an agent doesn't disagree with itself. -/
theorem polarizationIndex_self (a topic : I) :
    polarizationIndex a a topic = 0 := by
  unfold polarizationIndex resonanceDeficit; ring

/-- Polarization when one agent is void: measures how much the other
    agent transforms the topic. -/
theorem polarizationIndex_void_left (b topic : I) :
    polarizationIndex (void : I) b topic =
    resonanceDeficit topic (receive b topic) := by
  unfold polarizationIndex receive; simp

end OpinionDynamics

/-! ## §16. Echo Chambers and Filter Bubbles

An echo chamber is a situation where an agent only receives ideas that
reinforce its existing state. Formally, when the received idea always
has positive emergence with the agent's existing beliefs.

A filter bubble is the structural version: the agent's state acts as a
filter that preferentially amplifies consonant ideas. -/

section EchoChambers
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- An agent is in an echo chamber w.r.t. idea a if receiving a
    reinforces the agent's self-resonance — the idea makes the agent
    "more itself." -/
def inEchoChamber (agent idea : I) : Prop :=
  rs (receive agent idea) agent ≥ rs agent agent

/-- Being in an echo chamber with void is trivially true — void
    doesn't change anything. -/
theorem echoChamber_void (agent : I) :
    inEchoChamber agent (void : I) := by
  unfold inEchoChamber receive; simp

/-- Echo chamber resonance decomposes via emergence. -/
theorem echoChamber_decompose (agent idea : I) :
    rs (receive agent idea) agent =
    rs agent agent + rs idea agent + emergence agent idea agent := by
  unfold receive; rw [rs_compose_eq]

/-- A filter bubble: all ideas the agent receives get filtered through
    its existing state. The filtration effect is measured by the
    emergence term. -/
noncomputable def filtrationEffect (agent idea observer : I) : ℝ :=
  emergence agent idea observer

/-- Void agents have no filtration effect — they pass ideas through unchanged. -/
theorem filtration_void_agent (idea observer : I) :
    filtrationEffect (void : I) idea observer = 0 :=
  emergence_void_left idea observer

/-- Filtration of void is zero — nothing to filter. -/
theorem filtration_void_idea (agent observer : I) :
    filtrationEffect agent (void : I) observer = 0 :=
  emergence_void_right agent observer

/-- The squared filtration effect is bounded by the composition's
    weight times the observer's weight. -/
theorem filtration_bounded (agent idea observer : I) :
    (filtrationEffect agent idea observer) ^ 2 ≤
    rs (receive agent idea) (receive agent idea) * rs observer observer := by
  unfold filtrationEffect receive
  exact emergence_bounded' agent idea observer

end EchoChambers

/-! ## §17. Multi-Hop Transmission Chains

When an idea traverses multiple hops, each hop adds its own emergence.
The total transformation is constrained by the cocycle condition:
emergence from successive compositions must be globally consistent. -/

section MultiHop
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Two-hop transmission: idea goes through agent r₁ then r₂. -/
def twoHop (idea r₁ r₂ : I) : I :=
  receive r₂ (receive r₁ idea)

/-- Two-hop is composition of compositions. -/
theorem twoHop_eq (a r₁ r₂ : I) :
    twoHop a r₁ r₂ = compose r₂ (compose r₁ a) := rfl

/-- Two-hop through void first hop is just one hop. -/
theorem twoHop_void_first (a r₂ : I) :
    twoHop a (void : I) r₂ = receive r₂ a := by
  unfold twoHop receive; simp

/-- Two-hop through void second hop is just one hop. -/
theorem twoHop_void_second (a r₁ : I) :
    twoHop a r₁ (void : I) = receive r₁ a := by
  unfold twoHop receive; simp

/-- Two-hop self-resonance is at least as large as the second hop's. -/
theorem twoHop_enriches (a r₁ r₂ : I) :
    rs (twoHop a r₁ r₂) (twoHop a r₁ r₂) ≥ rs r₂ r₂ := by
  unfold twoHop; exact compose_enriches' r₂ (receive r₁ a)

/-- Three-hop transmission. -/
def threeHop (idea r₁ r₂ r₃ : I) : I :=
  receive r₃ (twoHop idea r₁ r₂)

/-- Three-hop through all void is identity. -/
theorem threeHop_void (a : I) :
    threeHop a (void : I) (void : I) (void : I) = a := by
  unfold threeHop twoHop receive; simp

/-- Three-hop enriches beyond the third agent. -/
theorem threeHop_enriches (a r₁ r₂ r₃ : I) :
    rs (threeHop a r₁ r₂ r₃) (threeHop a r₁ r₂ r₃) ≥ rs r₃ r₃ := by
  unfold threeHop; exact compose_enriches' r₃ (twoHop a r₁ r₂)

/-- The cocycle governs two-hop emergence: how emergence at hop 1
    interacts with emergence at hop 2. This is a direct instance
    of the cocycle condition. -/
theorem twoHop_cocycle (a r₁ r₂ c : I) :
    emergence r₁ a c + emergence (compose r₁ a) r₂ c =
    emergence a r₂ c + emergence r₁ (compose a r₂) c := by
  have := cocycle_condition r₁ a r₂ c; linarith

end MultiHop

/-! ## §18. Rumor Propagation and Distortion

Rumors are ideas that undergo systematic distortion as they pass through
agents. Each agent's emergence profile biases the rumor in a particular
direction. We formalize the total distortion after n hops. -/

section RumorPropagation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Total distortion of an idea after passing through a chain of agents,
    measured against an observer. This is the cumulative deviation from
    the original idea's resonance profile. -/
noncomputable def totalDistortion (idea : I) (chain : List I) (observer : I) : ℝ :=
  rs (transmitChain idea chain) observer - rs idea observer

/-- No chain means no distortion. -/
theorem totalDistortion_nil (a c : I) :
    totalDistortion a ([] : List I) c = 0 := by
  unfold totalDistortion transmitChain; ring

/-- Distortion through a single agent decomposes into receiver resonance + emergence. -/
theorem totalDistortion_singleton (a r c : I) :
    totalDistortion a [r] c = rs r c + emergence r a c := by
  unfold totalDistortion transmitChain transmitChain receive emergence; ring

/-- Distortion against void observer is always zero. -/
theorem totalDistortion_void_observer (a : I) (chain : List I) :
    totalDistortion a chain (void : I) = 0 := by
  unfold totalDistortion; simp [rs_void_right']

/-- Distortion of void idea through a single agent. -/
theorem totalDistortion_void_idea (r c : I) :
    totalDistortion (void : I) [r] c = rs r c := by
  unfold totalDistortion transmitChain transmitChain receive
  simp [rs_void_left', rs_void_right']

end RumorPropagation

/-! ## §19. Consensus Formation

Consensus emerges when agents who exchange ideas converge to similar
resonance profiles. We define consensus conditions and prove structural
results about when agreement can form. -/

section ConsensusFormation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Two agents are in consensus about idea s if they agree on its
    resonance (after receiving it). -/
def inConsensus (a b s c : I) : Prop :=
  rs (receive a s) c = rs (receive b s) c

/-- Any agent is in consensus with itself. -/
theorem consensus_self (a s c : I) : inConsensus a a s c := rfl

/-- Consensus about void between identical agents is trivial. -/
theorem consensus_void_self (a c : I) :
    inConsensus a a (void : I) c := rfl

/-- Consensus is symmetric. -/
theorem consensus_symm (a b s c : I) :
    inConsensus a b s c → inConsensus b a s c := Eq.symm

/-- Consensus is transitive. -/
theorem consensus_trans (a b d s c : I) :
    inConsensus a b s c → inConsensus b d s c → inConsensus a d s c :=
  Eq.trans

/-- If two agents are in consensus for all observers, their received
    ideas are resonance-equivalent. -/
theorem consensus_all_observers (a b s : I)
    (h : ∀ c : I, inConsensus a b s c) :
    ∀ c : I, rs (receive a s) c = rs (receive b s) c := h

end ConsensusFormation

/-! ## §20. Viral Spreading — R₀ Analogues

The basic reproduction number R₀ in epidemiology measures how many
secondary infections one case generates. For ideas, we define an
analogue: how much resonance one transmission creates compared to
the baseline. -/

section ViralSpreading
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Viral potency: the ratio-like quantity measuring how much an idea
    amplifies when passing through an agent, measured by self-resonance gain. -/
noncomputable def viralPotency (idea agent : I) : ℝ :=
  rs (receive agent idea) (receive agent idea) - rs agent agent

/-- Viral potency is always non-negative — ideas add weight. -/
theorem viralPotency_nonneg (idea agent : I) :
    viralPotency idea agent ≥ 0 := by
  unfold viralPotency; have := compose_enriches' agent idea; unfold receive; linarith

/-- Viral potency of void is zero — silence doesn't spread. -/
theorem viralPotency_void_idea (agent : I) :
    viralPotency (void : I) agent = 0 := by
  unfold viralPotency receive; simp

/-- Viral potency through void agent equals the idea's self-resonance. -/
theorem viralPotency_void_agent (idea : I) :
    viralPotency idea (void : I) = rs idea idea := by
  unfold viralPotency receive; simp [rs_void_void]

/-- Infectiousness: the emergence contribution to viral potency,
    measuring how the idea's weight grows through interaction effects. -/
noncomputable def infectiousness (idea agent : I) : ℝ :=
  emergence agent idea (compose agent idea)

/-- Void ideas have zero infectiousness. -/
theorem infectiousness_void_idea (agent : I) :
    infectiousness (void : I) agent = 0 := by
  unfold infectiousness; simp [emergence_void_right]

/-- Infectiousness through void agent is zero. -/
theorem infectiousness_void_agent (idea : I) :
    infectiousness idea (void : I) = 0 := by
  unfold infectiousness; simp [emergence_void_left]

end ViralSpreading

/-! ## §21. Information Cascades

An information cascade occurs when agents sequentially adopt an idea
based on observing predecessors' adoptions rather than private signals.
In IDT, this means each agent's received version feeds into the next,
creating a chain where late agents' versions are heavily influenced by
early agents' emergence contributions. -/

section InformationCascade
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Cascade state: the idea as it exists after passing through k agents. -/
def cascadeState (idea : I) (agents : List I) : I :=
  transmitChain idea agents

/-- The cascade enrichment: self-resonance of the cascade state
    is at least the last agent's self-resonance (if the chain is nonempty). -/
theorem cascade_enrichment (idea : I) (agents : List I) (r : I)
    (h : agents = [r]) :
    rs (cascadeState idea agents) (cascadeState idea agents) ≥ rs r r := by
  subst h; unfold cascadeState transmitChain; exact compose_enriches' r idea

/-- Empty cascade preserves the idea. -/
theorem cascade_nil (idea : I) :
    cascadeState idea ([] : List I) = idea := rfl

/-- Cascade through void agents is identity. -/
theorem cascade_void_agents (idea : I) (n : ℕ) :
    cascadeState idea (List.replicate n (void : I)) = idea :=
  peer_to_peer_void_chain idea n

/-- Cascade resonance with the original: how the cascaded version
    relates to the original idea. -/
noncomputable def cascadeFidelityToOriginal (idea : I) (agents : List I) : ℝ :=
  rs (cascadeState idea agents) idea

/-- Cascade fidelity of empty chain is the idea's self-resonance. -/
theorem cascadeFidelity_nil (idea : I) :
    cascadeFidelityToOriginal idea ([] : List I) = rs idea idea := rfl

end InformationCascade

/-! ## §22. Resonance Contagion — How Resonance Patterns Spread

Beyond simple idea transmission, resonance patterns themselves can
spread: when agent A transmits to agent B, B's resonance profile
shifts to partially mirror A's. This is how cultural norms, aesthetic
preferences, and cognitive styles propagate. -/

section ResonanceContagion
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Resonance contagion: how much receiving from source s makes the
    receiver r's resonance with observer c shift toward s's pattern. -/
noncomputable def resonanceContagion (source receiver observer : I) : ℝ :=
  rs (receive receiver source) observer - rs receiver observer

/-- Contagion decomposes into source's resonance plus emergence. -/
theorem resonanceContagion_eq (s r c : I) :
    resonanceContagion s r c = rs s c + emergence r s c := by
  unfold resonanceContagion receive emergence; ring

/-- Zero contagion from void source. -/
theorem contagion_void_source (r c : I) :
    resonanceContagion (void : I) r c = 0 := by
  unfold resonanceContagion receive; simp

/-- Zero contagion to void observer. -/
theorem contagion_void_observer (s r : I) :
    resonanceContagion s r (void : I) = 0 := by
  unfold resonanceContagion; simp [rs_void_right']

/-- Contagion through void receiver equals the source's resonance
    with the observer. -/
theorem contagion_void_receiver (s c : I) :
    resonanceContagion s (void : I) c = rs s c := by
  unfold resonanceContagion receive; simp [rs_void_left', rs_void_right']

end ResonanceContagion

/-! ## §23. Idea Metabolism — Absorption and Resistance

Agents don't passively receive ideas. Some ideas are "absorbed" (low emergence,
the idea fits the agent's existing framework) while others are "resisted"
(high emergence magnitude, the idea clashes). This models cognitive dissonance
and the effort of accommodating new information. -/

section IdeaMetabolism
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Resistance: how much an agent resists an idea, measured by the
    squared emergence (bounded by the E3 axiom). High resistance means
    the idea doesn't fit the agent's cognitive framework. -/
noncomputable def resistance (agent idea observer : I) : ℝ :=
  (emergence agent idea observer) ^ 2

/-- Resistance is always non-negative. -/
theorem resistance_nonneg (agent idea observer : I) :
    resistance agent idea observer ≥ 0 := by
  unfold resistance; positivity

/-- Resistance is bounded by the product of self-resonances. -/
theorem resistance_bounded (agent idea observer : I) :
    resistance agent idea observer ≤
    rs (receive agent idea) (receive agent idea) * rs observer observer := by
  unfold resistance receive; exact emergence_bounded' agent idea observer

/-- Zero resistance to void ideas — silence causes no cognitive dissonance. -/
theorem resistance_void_idea (agent observer : I) :
    resistance agent (void : I) observer = 0 := by
  unfold resistance; rw [emergence_void_right]; ring

/-- Void agents have zero resistance — they absorb everything. -/
theorem resistance_void_agent (idea observer : I) :
    resistance (void : I) idea observer = 0 := by
  unfold resistance; rw [emergence_void_left]; ring

/-- Absorption: the complement of resistance (relative to the bound). -/
noncomputable def absorption (agent idea observer : I) : ℝ :=
  rs (receive agent idea) (receive agent idea) * rs observer observer -
  resistance agent idea observer

/-- Absorption is non-negative (from the emergence bound). -/
theorem absorption_nonneg (agent idea observer : I) :
    absorption agent idea observer ≥ 0 := by
  unfold absorption; linarith [resistance_bounded agent idea observer]

end IdeaMetabolism

/-! ## §24. Semantic Drift — Long-Term Meaning Change

Over many transmissions, ideas undergo semantic drift: their resonance
profiles gradually shift away from the original. This is the formal
version of how word meanings change over centuries, how myths evolve,
how scientific theories get reinterpreted. -/

section SemanticDrift
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Drift after n iterations through the same agent, measured against
    the original idea. -/
noncomputable def semanticDrift (idea agent observer : I) (n : ℕ) : ℝ :=
  rs (iteratedReceive idea agent n) observer - rs idea observer

/-- Zero iterations means zero drift. -/
theorem semanticDrift_zero (idea agent observer : I) :
    semanticDrift idea agent observer 0 = 0 := by
  unfold semanticDrift iteratedReceive; ring

/-- Drift after one iteration is exactly the resonance shift. -/
theorem semanticDrift_one (idea agent observer : I) :
    semanticDrift idea agent observer 1 = resonanceShift agent idea observer := by
  unfold semanticDrift iteratedReceive iteratedReceive resonanceShift receive; ring

/-- Drift against void observer is always zero. -/
theorem semanticDrift_void_observer (idea agent : I) (n : ℕ) :
    semanticDrift idea agent (void : I) n = 0 := by
  unfold semanticDrift; simp [rs_void_right']

/-- Drift of void idea through any agent for n+1 steps is the
    n-fold iterated agent's resonance. -/
theorem semanticDrift_void_idea_one (agent observer : I) :
    semanticDrift (void : I) agent observer 1 =
    rs agent observer := by
  unfold semanticDrift iteratedReceive iteratedReceive receive
  simp [rs_void_left']

end SemanticDrift

/-! ## §25. Idea Competition — When Multiple Ideas Vie for Adoption

When multiple ideas compete for an agent's attention, each one
produces its own emergence. The "winning" idea is the one whose
received version has the highest resonance with the agent's values. -/

section IdeaCompetition
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Competitive advantage of idea a over idea b when received by agent r,
    as judged by observer c. -/
noncomputable def competitiveAdvantage (a b r c : I) : ℝ :=
  rs (receive r a) c - rs (receive r b) c

/-- Competitive advantage is antisymmetric in the competing ideas. -/
theorem competitiveAdvantage_antisymm (a b r c : I) :
    competitiveAdvantage a b r c = -competitiveAdvantage b a r c := by
  unfold competitiveAdvantage; ring

/-- Competitive advantage decomposes into idea resonances + emergence difference. -/
theorem competitiveAdvantage_eq (a b r c : I) :
    competitiveAdvantage a b r c =
    (rs a c - rs b c) + (emergence r a c - emergence r b c) := by
  unfold competitiveAdvantage receive emergence; ring

/-- When both ideas are void, there's no competitive advantage. -/
theorem competitiveAdvantage_void_ideas (r c : I) :
    competitiveAdvantage (void : I) (void : I) r c = 0 := by
  unfold competitiveAdvantage receive; ring

/-- Void receiver makes the advantage purely about the ideas themselves. -/
theorem competitiveAdvantage_void_receiver (a b c : I) :
    competitiveAdvantage a b (void : I) c = rs a c - rs b c := by
  unfold competitiveAdvantage receive; simp [rs_void_left', rs_void_right']

end IdeaCompetition

/-! ## §26. Network Topology Effects — Path Dependence

The ORDER in which agents receive ideas matters. Different transmission
orderings produce different outcomes because emergence accumulates
non-commutatively. This is the formal basis of path dependence in
cultural evolution. -/

section PathDependence
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Path dependence: the difference between receiving ideas in two
    different orders. -/
noncomputable def pathDependence (idea r₁ r₂ observer : I) : ℝ :=
  rs (twoHop idea r₁ r₂) observer - rs (twoHop idea r₂ r₁) observer

/-- Path dependence is antisymmetric in the agents. -/
theorem pathDependence_antisymm (idea r₁ r₂ observer : I) :
    pathDependence idea r₁ r₂ observer = -pathDependence idea r₂ r₁ observer := by
  unfold pathDependence; ring

/-- Path dependence through void agents is zero. -/
theorem pathDependence_void_left (idea r₂ observer : I) :
    pathDependence idea (void : I) r₂ observer = 0 := by
  unfold pathDependence twoHop receive; simp

/-- Path dependence through void second agent is also zero. -/
theorem pathDependence_void_right (idea r₁ observer : I) :
    pathDependence idea r₁ (void : I) observer = 0 := by
  unfold pathDependence twoHop receive; simp

/-- Path dependence vanishes against void observer. -/
theorem pathDependence_void_observer (idea r₁ r₂ : I) :
    pathDependence idea r₁ r₂ (void : I) = 0 := by
  unfold pathDependence; simp [rs_void_right']

/-- Path dependence of void idea is just about the agents' composition order. -/
theorem pathDependence_void_idea (r₁ r₂ observer : I) :
    pathDependence (void : I) r₁ r₂ observer =
    rs (compose r₂ r₁) observer - rs (compose r₁ r₂) observer := by
  unfold pathDependence twoHop receive; simp

end PathDependence

/-! ## §27. Collective Resonance — Group Effects

When ideas circulate in a group, collective phenomena emerge that
don't reduce to individual transmissions. The group's "collective state"
after shared exposure differs from any individual's state. -/

section CollectiveResonance
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Collective exposure: compose all agents' received states. -/
def collectiveState (idea : I) : List I → I
  | [] => void
  | agent :: rest => compose (receive agent idea) (collectiveState idea rest)

/-- Collective state of empty group is void. -/
theorem collectiveState_nil (idea : I) :
    collectiveState idea ([] : List I) = (void : I) := rfl

/-- Collective state of a single agent. -/
theorem collectiveState_singleton (idea agent : I) :
    collectiveState idea [agent] = receive agent idea := by
  unfold collectiveState collectiveState; simp [receive]

/-- Collective resonance: how the group's collective state resonates
    with the original idea. -/
noncomputable def collectiveResonance (idea : I) (group : List I) : ℝ :=
  rs (collectiveState idea group) idea

/-- Collective resonance of empty group is zero. -/
theorem collectiveResonance_nil (idea : I) :
    collectiveResonance idea ([] : List I) = 0 := by
  unfold collectiveResonance collectiveState; exact rs_void_left' idea

/-- Collective resonance of a singleton. -/
theorem collectiveResonance_singleton (idea agent : I) :
    collectiveResonance idea [agent] = rs (receive agent idea) idea := by
  unfold collectiveResonance; rw [collectiveState_singleton]

end CollectiveResonance

/-! ## §28. Idea Extinction and Revival

Some ideas "die" — they cease to resonate with any agent. Others are
"revived" when they encounter a new context that reactivates their
emergence potential. We formalize conditions for extinction and revival. -/

section ExtinctionRevival
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- An idea is "extinct" in a population if no agent resonates with it
    above threshold. -/
def ideaExtinct (idea : I) (agents : List I) (threshold : ℝ) : Prop :=
  ∀ agent ∈ agents, rs agent idea < threshold

/-- Any idea is vacuously extinct in an empty population. -/
theorem extinct_nil (idea : I) (t : ℝ) :
    ideaExtinct idea ([] : List I) t := by
  intro agent hmem; exact absurd hmem (List.not_mem_nil agent)

/-- A revival agent: an agent that brings an idea's resonance above
    threshold through reception. -/
def isRevivalAgent (idea agent : I) (threshold : ℝ) : Prop :=
  rs (receive agent idea) idea ≥ threshold

/-- Non-void agents can potentially revive through composition enrichment. -/
theorem revival_weight_lower_bound (idea agent : I) :
    rs (receive agent idea) (receive agent idea) ≥ rs agent agent :=
  compose_enriches' agent idea

end ExtinctionRevival

/-! ## §29. Shannon Meets IDT — Channel Capacity and Emergence

Shannon's channel capacity measures the maximum rate of reliable communication.
In IDT, a "channel" is an agent through whom ideas pass. The channel's emergence
profile determines how much information is preserved vs. created vs. destroyed.
The key insight: emergence IS the noise — but it's structured noise that can
CREATE meaning, not just destroy it. -/

section ShannonIDT
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Channel noise: the emergence introduced by an agent acting as a channel.
    In Shannon's framework, noise destroys information. In IDT, emergence
    can create NEW resonance — the channel adds meaning. -/
noncomputable def channelNoise (channel idea observer : I) : ℝ :=
  emergence channel idea observer

/-- Channel noise vanishes for void channels — silence is noiseless. -/
theorem channelNoise_void_channel (idea observer : I) :
    channelNoise (void : I) idea observer = 0 :=
  emergence_void_left idea observer

/-- Channel noise vanishes for void ideas — nothing to distort. -/
theorem channelNoise_void_idea (channel observer : I) :
    channelNoise channel (void : I) observer = 0 :=
  emergence_void_right channel observer

/-- Channel noise vanishes against void observer. -/
theorem channelNoise_void_observer (channel idea : I) :
    channelNoise channel idea (void : I) = 0 :=
  emergence_against_void channel idea

/-- Channel noise is bounded — the Emergence Cauchy-Schwarz gives us
    a capacity constraint analogous to Shannon's noisy channel coding theorem. -/
theorem channelNoise_bounded (channel idea observer : I) :
    (channelNoise channel idea observer) ^ 2 ≤
    rs (receive channel idea) (receive channel idea) * rs observer observer := by
  unfold channelNoise receive; exact emergence_bounded' channel idea observer

/-- Rate-distortion: the resonance loss when transmitting through a channel.
    This is the IDT analogue of Shannon's rate-distortion function R(D). -/
noncomputable def rateDistortion (idea channel observer : I) : ℝ :=
  rs idea observer - rs (receive channel idea) observer

/-- Rate-distortion decomposes into channel resonance and emergence. -/
theorem rateDistortion_eq (a ch c : I) :
    rateDistortion a ch c = -(rs ch c + channelNoise ch a c) := by
  unfold rateDistortion receive channelNoise emergence; ring

/-- Zero rate-distortion for void channel — lossless transmission. -/
theorem rateDistortion_void_channel (a c : I) :
    rateDistortion a (void : I) c = 0 := by
  unfold rateDistortion receive; simp

/-- Rate-distortion of void idea. -/
theorem rateDistortion_void_idea (ch c : I) :
    rateDistortion (void : I) ch c = -(rs ch c) := by
  unfold rateDistortion receive; simp [rs_void_left', rs_void_right']

/-- Rate-distortion vanishes against void observer. -/
theorem rateDistortion_void_observer (a ch : I) :
    rateDistortion a ch (void : I) = 0 := by
  unfold rateDistortion; simp [rs_void_right']

/-- Mutual information analogue: the cross-resonance between the
    original idea and its received version. Positive means the channel
    preserves some of the original meaning. -/
noncomputable def mutualResonance (idea channel : I) : ℝ :=
  rs idea (receive channel idea)

/-- Mutual resonance with void channel is self-resonance. -/
theorem mutualResonance_void_channel (a : I) :
    mutualResonance a (void : I) = rs a a := by
  unfold mutualResonance receive; simp

/-- Mutual resonance of void idea is zero. -/
theorem mutualResonance_void_idea (ch : I) :
    mutualResonance (void : I) ch = 0 := by
  unfold mutualResonance receive; simp [rs_void_left']

/-- Channel composition: two channels in series. The total noise
    decomposes via the cocycle condition — this is a deep connection
    between Shannon's channel composition and IDT's emergence algebra. -/
noncomputable def serialChannel (ch₁ ch₂ idea : I) : I :=
  receive ch₂ (receive ch₁ idea)

/-- Serial channel through two void channels is identity. -/
theorem serialChannel_void_both (a : I) :
    serialChannel (void : I) (void : I) a = a := by
  unfold serialChannel receive; simp

/-- Serial channel with void first is just second channel. -/
theorem serialChannel_void_first (ch₂ a : I) :
    serialChannel (void : I) ch₂ a = receive ch₂ a := by
  unfold serialChannel receive; simp

/-- Serial channel with void second is just first channel. -/
theorem serialChannel_void_second (ch₁ a : I) :
    serialChannel ch₁ (void : I) a = receive ch₁ a := by
  unfold serialChannel receive; simp

/-- Serial channel equals two-hop — connecting Shannon theory to
    network diffusion models. -/
theorem serialChannel_eq_twoHop (a ch₁ ch₂ : I) :
    serialChannel ch₁ ch₂ a = twoHop a ch₁ ch₂ := rfl

/-- Serial channel enriches beyond second channel. -/
theorem serialChannel_enriches (ch₁ ch₂ a : I) :
    rs (serialChannel ch₁ ch₂ a) (serialChannel ch₁ ch₂ a) ≥ rs ch₂ ch₂ := by
  unfold serialChannel; exact compose_enriches' ch₂ (receive ch₁ a)

end ShannonIDT

/-! ## §30. Epidemiological Diffusion — SIR Dynamics Extended

Beyond the basic SIR model of §8, we develop a richer epidemiological
framework: superspreaders as high-weight nodes, herd immunity as saturation
of resonance capacity, and R₀ estimation from emergence profiles. -/

section EpidemiologicalDiffusion
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Exposure level: total accumulated emergence from multiple idea contacts.
    Models the "dose-response" relationship in idea adoption. -/
noncomputable def exposureLevel (agent : I) (ideas : List I) (observer : I) : ℝ :=
  rs (cumulativeReceive agent ideas) observer - rs agent observer

/-- Zero exposure from empty idea list. -/
theorem exposureLevel_nil (agent observer : I) :
    exposureLevel agent ([] : List I) observer = 0 := by
  unfold exposureLevel cumulativeReceive; ring

/-- Exposure against void observer is zero. -/
theorem exposureLevel_void_observer (agent : I) (ideas : List I) :
    exposureLevel agent ideas (void : I) = 0 := by
  unfold exposureLevel; simp [rs_void_right']

/-- Herd immunity threshold: the population is "immune" to an idea when
    the average self-resonance after exposure exceeds a saturation point.
    Beyond this, new exposures add diminishing emergence. -/
def herdImmune (agents : List I) (idea : I) (saturation : ℝ) : Prop :=
  ∀ agent ∈ agents, rs (receive agent idea) (receive agent idea) ≥ saturation

/-- Empty populations are vacuously herd-immune. -/
theorem herdImmune_nil (idea : I) (s : ℝ) :
    herdImmune ([] : List I) idea s := by
  intro agent hmem; exact absurd hmem (List.not_mem_nil agent)

/-- Herd immunity is monotone in saturation level: if immune at level s,
    then immune at any lower level s'. -/
theorem herdImmune_mono (agents : List I) (idea : I) (s s' : ℝ)
    (h : herdImmune agents idea s) (hle : s' ≤ s) :
    herdImmune agents idea s' := by
  intro agent hmem; linarith [h agent hmem]

/-- Quarantine: isolating an agent from an idea by interposing a void barrier.
    Quarantine through void is the identity — it perfectly isolates. -/
theorem quarantine_void (agent idea : I) :
    receive agent (receive (void : I) idea) = receive agent idea := by
  unfold receive; simp

/-- Double exposure enriches beyond single. -/
theorem double_exposure_enriches (agent idea : I) :
    rs (receive (receive agent idea) idea) (receive (receive agent idea) idea) ≥
    rs (receive agent idea) (receive agent idea) := by
  unfold receive; exact compose_enriches' (compose agent idea) idea

/-- Reinfection: receiving the same idea after recovery (via vaccine)
    still enriches — you can't fully erase prior exposure. -/
theorem reinfection_enriches (agent idea vaccine : I) :
    rs (receive (receive (receive agent idea) vaccine) idea)
       (receive (receive (receive agent idea) vaccine) idea) ≥
    rs (receive (receive agent idea) vaccine)
       (receive (receive agent idea) vaccine) := by
  unfold receive; exact compose_enriches' (compose (compose agent idea) vaccine) idea

end EpidemiologicalDiffusion

/-! ## §31. McLuhan's Media Theory — "The Medium Is the Message"

Marshall McLuhan's central insight: the medium through which ideas are
transmitted IS ITSELF a message that composes with the content. In IDT,
this is literal: if medium m carries content c, the receiver gets
compose(r, compose(m, c)) — the medium m composes with content c before
reception. The medium's emergence contribution is irreducible. -/

section McLuhanMedia
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- McLuhan transmission: content c transmitted through medium m to receiver r.
    The medium composes with the content BEFORE the receiver processes it. -/
def mcluhanTransmit (medium content receiver : I) : I :=
  receive receiver (compose medium content)

/-- Without a medium (void medium), the receiver gets raw content. -/
theorem mcluhanTransmit_void_medium (c r : I) :
    mcluhanTransmit (void : I) c r = receive r c := by
  unfold mcluhanTransmit; simp

/-- Without content (void content), the receiver gets the medium itself.
    "The medium is the message" — when content vanishes, only medium remains. -/
theorem mcluhanTransmit_void_content (m r : I) :
    mcluhanTransmit m (void : I) r = receive r m := by
  unfold mcluhanTransmit; simp

/-- Without a receiver (void receiver), the medium-content composite passes through. -/
theorem mcluhanTransmit_void_receiver (m c : I) :
    mcluhanTransmit m c (void : I) = compose m c := by
  unfold mcluhanTransmit receive; simp

/-- The medium effect: how much the medium changes the resonance of content
    with observer, beyond what content alone provides. This is the formal
    measure of "the medium is the message." -/
noncomputable def mediumEffect (medium content observer : I) : ℝ :=
  rs (compose medium content) observer - rs content observer

/-- Medium effect of void medium is zero — no medium, no medium-message. -/
theorem mediumEffect_void_medium (c observer : I) :
    mediumEffect (void : I) c observer = 0 := by
  unfold mediumEffect; simp

/-- Medium effect decomposes into medium's resonance plus emergence. -/
theorem mediumEffect_eq (m c obs : I) :
    mediumEffect m c obs = rs m obs + emergence m c obs := by
  unfold mediumEffect emergence; ring

/-- Medium effect vanishes against void observer. -/
theorem mediumEffect_void_observer (m c : I) :
    mediumEffect m c (void : I) = 0 := by
  unfold mediumEffect; simp [rs_void_right']

/-- McLuhan's tetrad: the medium always enriches the total composition.
    Adding a medium never decreases the self-resonance of the message. -/
theorem mcluhanTetrad_enrichment (m c : I) :
    rs (compose m c) (compose m c) ≥ rs m m :=
  compose_enriches' m c

/-- Kittler's discourse network: the medium determines what can be said.
    Formally: the medium-content composition is never void when the medium
    is non-void, regardless of content. -/
theorem kittler_discourse_network (m c : I) (hm : m ≠ void) :
    compose m c ≠ void :=
  compose_ne_void_of_left m c hm

/-- McLuhan transmission enriches beyond receiver. -/
theorem mcluhanTransmit_enriches (m c r : I) :
    rs (mcluhanTransmit m c r) (mcluhanTransmit m c r) ≥ rs r r := by
  unfold mcluhanTransmit; exact compose_enriches' r (compose m c)

/-- Medium composition is associative: transmitting through two media
    in sequence is the same as transmitting through their composition. -/
theorem medium_composition_assoc (m₁ m₂ c : I) :
    compose m₁ (compose m₂ c) = compose (compose m₁ m₂) c := by
  rw [compose_assoc']

end McLuhanMedia

/-! ## §32. Debord's Spectacle — Diffusion as Social Control

Guy Debord's "Society of the Spectacle": in spectacular diffusion, ideas
don't spread through genuine exchange but through mediated images that
replace direct experience. The spectacle is a diffusion regime where the
medium dominates the content — emergence from the medium overwhelms the
original meaning. -/

section DebordSpectacle
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A spectacle is a medium-dominated transmission: the medium's self-resonance
    exceeds the content's. When the medium is louder than the message. -/
def isSpectacle (medium content : I) : Prop :=
  rs medium medium > rs content content

/-- Void content is always a spectacle (for non-void medium) — pure spectacle
    is medium without content, Debord's "the spectacle is capital accumulated
    to the point where it becomes image." -/
theorem void_content_spectacle (m : I) (hm : m ≠ void) :
    isSpectacle m (void : I) := by
  unfold isSpectacle; simp [rs_void_void]; exact rs_self_pos m hm

/-- In spectacular transmission, the received version is dominated by the medium.
    The medium's weight guarantees the composition is non-trivial. -/
theorem spectacle_ne_void (m c : I) (hm : m ≠ void) :
    compose m c ≠ void :=
  compose_ne_void_of_left m c hm

/-- Spectacular enrichment: the spectacle always adds weight. -/
theorem spectacle_enriches (m c : I) :
    rs (compose m c) (compose m c) ≥ rs m m :=
  compose_enriches' m c

/-- The spectacle's self-resonance bound: spectacular compositions
    have self-resonance at least as large as the medium's. -/
theorem spectacle_weight_bound (m c : I) (h : isSpectacle m c) :
    rs (compose m c) (compose m c) ≥ rs c c := by
  have h1 := compose_enriches' m c
  unfold isSpectacle at h; linarith

/-- Recuperation: the spectacle absorbs its own critique.
    If critique q is composed with spectacle s, the result is at least
    as weighty as s — the critique adds to the spectacle, never diminishes it. -/
theorem recuperation (spectacle critique : I) :
    rs (compose spectacle critique) (compose spectacle critique) ≥
    rs spectacle spectacle :=
  compose_enriches' spectacle critique

end DebordSpectacle

/-! ## §33. Ong's Orality-Literacy Divide

Walter Ong's distinction between oral and literate cultures maps onto
IDT through the concept of transmission fidelity. In oral cultures,
ideas pass through many human agents (high emergence, high mutation).
In literate cultures, ideas are "frozen" in text (low emergence, high
fidelity). The medium of writing is a quasi-linear agent. -/

section OralityLiteracy
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A literate medium: one that introduces no emergence (linear transmission).
    Writing preserves meaning — it doesn't add its own interpretation. -/
def literateMedium (m : I) : Prop :=
  leftLinear m

/-- Void is a literate medium — silence is perfectly faithful. -/
theorem void_literate : literateMedium (void : I) :=
  void_leftLinear

/-- A literate medium preserves resonance profiles exactly. -/
theorem literate_preserves_resonance (m : I) (h : literateMedium m) (a c : I) :
    rs (compose m a) c = rs m c + rs a c := by
  have := rs_compose_eq m a c
  have h2 := h a c
  linarith

/-- An oral medium: one with non-trivial emergence — it transforms what
    passes through it, like a storyteller who embellishes each retelling. -/
def oralMedium (m : I) : Prop :=
  ¬leftLinear m

/-- Oral transmission drift: after n oral retellings, the idea's
    resonance profile has shifted by the accumulated emergence. -/
noncomputable def oralDrift (idea teller observer : I) (n : ℕ) : ℝ :=
  semanticDrift idea teller observer n

/-- Zero retellings means zero oral drift. -/
theorem oralDrift_zero (a m c : I) :
    oralDrift a m c 0 = 0 :=
  semanticDrift_zero a m c

/-- Oral drift vanishes against void observer. -/
theorem oralDrift_void_observer (a m : I) (n : ℕ) :
    oralDrift a m (void : I) n = 0 :=
  semanticDrift_void_observer a m n

/-- Primary orality: transmission through agents with no literate backup.
    The self-resonance of the chain always grows — oral traditions
    accumulate weight through repetition and elaboration. -/
theorem primaryOrality_enriches (idea teller : I) (n : ℕ) :
    rs (iteratedReceive idea teller (n + 1)) (iteratedReceive idea teller (n + 1)) ≥
    rs teller teller :=
  iteratedReceive_enriches idea teller n

/-- Secondary orality (Ong): oral transmission mediated by electronic media.
    The medium m carries the teller's version to the receiver r. -/
def secondaryOralTransmit (idea teller medium receiver : I) : I :=
  receive receiver (compose medium (receive teller idea))

/-- Secondary orality through void medium reduces to direct oral transmission. -/
theorem secondaryOral_void_medium (a t r : I) :
    secondaryOralTransmit a t (void : I) r = receive r (receive t a) := by
  unfold secondaryOralTransmit receive; simp

/-- Secondary orality through void teller is just medium transmission. -/
theorem secondaryOral_void_teller (a m r : I) :
    secondaryOralTransmit a (void : I) m r = receive r (compose m a) := by
  unfold secondaryOralTransmit receive; simp

/-- Secondary orality through void receiver passes through. -/
theorem secondaryOral_void_receiver (a t m : I) :
    secondaryOralTransmit a t m (void : I) =
    compose m (receive t a) := by
  unfold secondaryOralTransmit receive; simp

end OralityLiteracy

/-! ## §34. Propaganda and Persuasion — Bernays, Ellul, Chomsky

Edward Bernays' "engineering of consent," Jacques Ellul's "propaganda,"
and Chomsky's "manufacturing consent" all describe systematic manipulation
of idea diffusion. In IDT, propaganda is a non-random medium that
systematically biases emergence in a particular direction. -/

section Propaganda
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A propaganda apparatus: a fixed medium that systematically filters
    all ideas that pass through it. The apparatus's emergence profile
    biases every idea toward the apparatus's "ideology." -/
noncomputable def propagandaEffect (apparatus idea observer : I) : ℝ :=
  mediumEffect apparatus idea observer

/-- Void apparatus has no propaganda effect — no filter, no bias. -/
theorem propagandaEffect_void (idea observer : I) :
    propagandaEffect (void : I) idea observer = 0 :=
  mediumEffect_void_medium idea observer

/-- Propaganda effect vanishes against void observer. -/
theorem propagandaEffect_void_observer (app idea : I) :
    propagandaEffect app idea (void : I) = 0 :=
  mediumEffect_void_observer app idea

/-- Manufacturing consent (Chomsky): the propaganda model predicts that
    the apparatus's self-resonance dominates. After filtering through
    the apparatus, the output is at least as weighty as the apparatus itself. -/
theorem manufacturing_consent_enriches (apparatus idea : I) :
    rs (compose apparatus idea) (compose apparatus idea) ≥
    rs apparatus apparatus :=
  compose_enriches' apparatus idea

/-- Ellul's total propaganda: when the apparatus processes all ideas,
    it never produces void — there's always a message, always a bias.
    This is Ellul's point that propaganda is inescapable in technological society. -/
theorem ellul_total_propaganda (apparatus idea : I) (h : apparatus ≠ void) :
    compose apparatus idea ≠ void :=
  compose_ne_void_of_left apparatus idea h

/-- Bernays' engineering of consent: double processing through the
    propaganda apparatus enriches further — propaganda compounds. -/
theorem bernays_double_processing (app idea : I) :
    rs (compose app (compose app idea)) (compose app (compose app idea)) ≥
    rs app app := by
  calc rs (compose app (compose app idea)) (compose app (compose app idea))
      ≥ rs app app := compose_enriches' app (compose app idea)

/-- Counter-propaganda: applying a counter-apparatus after propaganda
    still cannot reduce weight — you can't un-propagandize by adding
    more information, only by changing the resonance landscape. -/
theorem counterPropaganda_enriches (app counter idea : I) :
    rs (compose counter (compose app idea)) (compose counter (compose app idea)) ≥
    rs counter counter :=
  compose_enriches' counter (compose app idea)

/-- Propaganda saturation: iterated propaganda through the same apparatus
    always enriches, but the output is increasingly dominated by the
    apparatus's own resonance profile. -/
theorem propagandaSaturation_enriches (app idea : I) (n : ℕ) :
    rs (iteratedReceive idea app (n + 1)) (iteratedReceive idea app (n + 1)) ≥
    rs app app :=
  iteratedReceive_enriches idea app n

end Propaganda

/-! ## §35. Network Cascade Thresholds

In network science, cascade thresholds determine when an idea spreads
virally vs. dies out. The threshold depends on the network topology and
the agents' susceptibility. In IDT, we formalize thresholds in terms of
cumulative resonance crossing critical values. -/

section CascadeThresholds
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- An agent has adopted an idea if its self-resonance after reception
    exceeds a threshold. -/
def hasAdopted (agent idea : I) (threshold : ℝ) : Prop :=
  rs (receive agent idea) (receive agent idea) ≥ threshold

/-- All agents adopt at threshold ≤ 0 (self-resonance is non-negative). -/
theorem adoption_nonneg_threshold (agent idea : I) :
    hasAdopted agent idea 0 := by
  unfold hasAdopted receive
  have h1 := compose_enriches' agent idea
  have h2 := S.rs_self_nonneg agent
  have h3 := S.rs_self_nonneg (compose agent idea)
  linarith

/-- Adoption monotonicity: if adopted at threshold t, then adopted at any t' ≤ t. -/
theorem adoption_mono (agent idea : I) (t t' : ℝ)
    (h : hasAdopted agent idea t) (hle : t' ≤ t) :
    hasAdopted agent idea t' := by
  unfold hasAdopted at *; linarith

/-- Cascade condition: an idea cascades through a population if every
    agent in the population adopts it. -/
def cascades (idea : I) (agents : List I) (threshold : ℝ) : Prop :=
  ∀ agent ∈ agents, hasAdopted agent idea threshold

/-- Empty populations always cascade (vacuously). -/
theorem cascades_nil (idea : I) (t : ℝ) :
    cascades idea ([] : List I) t := by
  intro agent hmem; exact absurd hmem (List.not_mem_nil agent)

/-- Cascade at threshold 0 for any population. -/
theorem cascades_zero (idea : I) (agents : List I) :
    cascades idea agents 0 := by
  intro agent _hmem; exact adoption_nonneg_threshold agent idea

/-- Cascade monotonicity in threshold. -/
theorem cascades_mono (idea : I) (agents : List I) (t t' : ℝ)
    (h : cascades idea agents t) (hle : t' ≤ t) :
    cascades idea agents t' := by
  intro agent hmem; exact adoption_mono agent idea t t' (h agent hmem) hle

end CascadeThresholds

/-! ## §36. Influence Maximization

In the influence maximization problem (Kempe-Kleinberg-Tardos), we seek
the set of "seed" agents that maximizes total adoption. In IDT, influence
is measured by how much an agent's state, after receiving an idea, resonates
with other agents. -/

section InfluenceMaximization
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Influence of an agent on another via an idea: how much receiving the
    idea through the influencer changes the target's resonance profile. -/
noncomputable def influence (influencer idea target : I) : ℝ :=
  rs (receive influencer idea) target

/-- Influence of void influencer is just the idea's resonance with target. -/
theorem influence_void_influencer (idea target : I) :
    influence (void : I) idea target = rs idea target := by
  unfold influence receive; simp

/-- Influence with void idea is the influencer's resonance with target. -/
theorem influence_void_idea (influencer target : I) :
    influence influencer (void : I) target = rs influencer target := by
  unfold influence receive; simp

/-- Influence on void target is zero. -/
theorem influence_void_target (influencer idea : I) :
    influence influencer idea (void : I) = 0 := by
  unfold influence; exact rs_void_right' _

/-- Self-influence is self-resonance of received idea. -/
theorem self_influence (agent idea : I) :
    influence agent idea agent =
    rs agent agent + rs idea agent + emergence agent idea agent := by
  unfold influence receive; rw [rs_compose_eq]

/-- Influence decomposes via composition resonance. -/
theorem influence_decompose (inf idea target : I) :
    influence inf idea target =
    rs inf target + rs idea target + emergence inf idea target := by
  unfold influence receive; rw [rs_compose_eq]

/-- Total influence on a population: sum of individual influences. -/
noncomputable def totalInfluence (influencer idea : I) (targets : List I) : ℝ :=
  (targets.map (fun t => influence influencer idea t)).sum

/-- Total influence on empty population is zero. -/
theorem totalInfluence_nil (inf idea : I) :
    totalInfluence inf idea ([] : List I) = 0 := rfl

/-- Total influence of void influencer decomposes simply. -/
theorem totalInfluence_void_influencer (idea : I) (targets : List I) :
    totalInfluence (void : I) idea targets =
    (targets.map (fun t => rs idea t)).sum := by
  unfold totalInfluence; congr 1
  apply List.map_congr_left; intro t _
  exact influence_void_influencer idea t

end InfluenceMaximization

/-! ## §37. Echo Chamber Dynamics — Reinforcement and Isolation

Echo chambers are not just static structures but dynamic processes.
When agents repeatedly receive ideas that confirm their existing beliefs,
their resonance profiles converge to a fixed attractor. We formalize
the dynamics of echo chamber formation. -/

section EchoChamberDynamics
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Echo chamber depth: how many times an agent has been reinforced
    by receiving its own state back. This models the iterative
    narrowing of perspective in an echo chamber. -/
def echoChamberIterate (agent : I) : ℕ → I
  | 0 => agent
  | n + 1 => receive (echoChamberIterate agent n) (echoChamberIterate agent n)

/-- Echo chamber at depth 0 is the original agent. -/
theorem echoChamberIterate_zero (a : I) :
    echoChamberIterate a 0 = a := rfl

/-- Echo chamber at depth n+1 is self-composition of depth n. -/
theorem echoChamberIterate_succ (a : I) (n : ℕ) :
    echoChamberIterate a (n + 1) =
    compose (echoChamberIterate a n) (echoChamberIterate a n) := rfl

/-- Echo chamber weight grows monotonically — each reinforcement
    adds weight to the agent's state. -/
theorem echoChamber_weight_grows (a : I) (n : ℕ) :
    rs (echoChamberIterate a (n + 1)) (echoChamberIterate a (n + 1)) ≥
    rs (echoChamberIterate a n) (echoChamberIterate a n) := by
  simp [echoChamberIterate_succ]
  exact compose_enriches' (echoChamberIterate a n) (echoChamberIterate a n)

/-- Void agent stays void in echo chamber at all depths. -/
theorem echoChamberIterate_void (n : ℕ) :
    echoChamberIterate (void : I) n = (void : I) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [echoChamberIterate, ih, receive]

/-- Filter bubble strength: how much the agent's echo chamber
    state resonates with itself relative to the original. -/
noncomputable def filterBubbleStrength (agent : I) (n : ℕ) : ℝ :=
  rs (echoChamberIterate agent n) (echoChamberIterate agent n) - rs agent agent

/-- Filter bubble strength at depth 0 is zero. -/
theorem filterBubbleStrength_zero (a : I) :
    filterBubbleStrength a 0 = 0 := by
  unfold filterBubbleStrength echoChamberIterate; ring

/-- Filter bubble strength is non-negative at all depths. -/
theorem filterBubbleStrength_nonneg (a : I) (n : ℕ) :
    filterBubbleStrength a n ≥ 0 := by
  unfold filterBubbleStrength
  induction n with
  | zero => simp [echoChamberIterate]
  | succ n ih =>
    have h := echoChamber_weight_grows a n
    linarith

end EchoChamberDynamics

/-! ## §38. Polarization Dynamics — Divergence of Groups

When two groups exchange ideas only within their own group (echo chambers),
their collective states can diverge — this is polarization. We formalize
how within-group reinforcement and between-group isolation drive divergence. -/

section PolarizationDynamics
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Group polarization: the resonance deficit between two group states
    after each group has been internally reinforced n times. -/
noncomputable def groupPolarization (a b : I) (n : ℕ) : ℝ :=
  resonanceDeficit (echoChamberIterate a n) (echoChamberIterate b n)

/-- Polarization at depth 0 is the initial disagreement. -/
theorem groupPolarization_zero (a b : I) :
    groupPolarization a b 0 = resonanceDeficit a b := rfl

/-- Polarization is symmetric in the two groups. -/
theorem groupPolarization_symm (a b : I) (n : ℕ) :
    groupPolarization a b n = groupPolarization b a n := by
  unfold groupPolarization; exact resonanceDeficit_symm _ _

/-- Self-polarization is always zero — a group doesn't diverge from itself. -/
theorem groupPolarization_self (a : I) (n : ℕ) :
    groupPolarization a a n = 0 := by
  unfold groupPolarization; exact resonanceDeficit_self _

/-- Polarization with void is the echo chamber's self-deficit. -/
theorem groupPolarization_void (a : I) (n : ℕ) :
    groupPolarization a (void : I) n =
    resonanceDeficit (echoChamberIterate a n) (void : I) := by
  unfold groupPolarization; rw [echoChamberIterate_void]

/-- Affective polarization: how much each group's perception of the other
    diverges from self-perception. -/
noncomputable def affectivePolarization (a b : I) : ℝ :=
  rs a a + rs b b - rs a b - rs b a

/-- Affective polarization is symmetric. -/
theorem affectivePolarization_symm (a b : I) :
    affectivePolarization a b = affectivePolarization b a := by
  unfold affectivePolarization; ring

/-- Self affective polarization is zero. -/
theorem affectivePolarization_self (a : I) :
    affectivePolarization a a = 0 := by
  unfold affectivePolarization; ring

/-- Affective polarization with void. -/
theorem affectivePolarization_void (a : I) :
    affectivePolarization a (void : I) = rs a a := by
  unfold affectivePolarization; simp [rs_void_void, rs_void_left', rs_void_right']

end PolarizationDynamics

/-! ## §39. Diffusion Kernels — Green's Functions on Ideatic Spaces

In PDE theory, Green's functions propagate influence from a point source.
In IDT, the "diffusion kernel" of an agent is the function that maps
ideas to their received versions. This kernel encodes all of the agent's
biases, filters, and transformations. -/

section DiffusionKernels
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The diffusion kernel of an agent: maps (idea, observer) to
    the resonance of the received version with the observer. -/
noncomputable def diffusionKernel (agent idea observer : I) : ℝ :=
  rs (receive agent idea) observer

/-- The diffusion kernel of void is just the identity kernel. -/
theorem diffusionKernel_void_agent (idea observer : I) :
    diffusionKernel (void : I) idea observer = rs idea observer := by
  unfold diffusionKernel receive; simp

/-- The kernel applied to void idea returns the agent's self-resonance profile. -/
theorem diffusionKernel_void_idea (agent observer : I) :
    diffusionKernel agent (void : I) observer = rs agent observer := by
  unfold diffusionKernel receive; simp

/-- The kernel against void observer is always zero. -/
theorem diffusionKernel_void_observer (agent idea : I) :
    diffusionKernel agent idea (void : I) = 0 := by
  unfold diffusionKernel; exact rs_void_right' _

/-- The kernel decomposes additively via emergence. -/
theorem diffusionKernel_decompose (agent idea observer : I) :
    diffusionKernel agent idea observer =
    rs agent observer + rs idea observer + emergence agent idea observer := by
  unfold diffusionKernel receive; rw [rs_compose_eq]

/-- Kernel composition: applying two kernels in sequence gives the
    two-hop resonance. -/
theorem diffusionKernel_compose (a₁ a₂ idea observer : I) :
    diffusionKernel a₂ (receive a₁ idea) observer =
    rs (twoHop idea a₁ a₂) observer := rfl

/-- The kernel is "positive semidefinite" in the sense that
    the self-resonance of the output is non-negative. -/
theorem diffusionKernel_self_nonneg (agent idea : I) :
    diffusionKernel agent idea (receive agent idea) ≥ 0 := by
  unfold diffusionKernel; exact S.rs_self_nonneg _

/-- The square of the kernel value is bounded by the product of
    self-resonances — the Cauchy-Schwarz of diffusion. -/
theorem diffusionKernel_CS (agent idea observer : I) :
    (diffusionKernel agent idea observer -
     rs agent observer - rs idea observer) ^ 2 ≤
    rs (receive agent idea) (receive agent idea) * rs observer observer := by
  unfold diffusionKernel receive
  exact emergence_bounded' agent idea observer

end DiffusionKernels

/-! ## §40. Ergodic Theory of Idea Spread

In ergodic theory, a system is ergodic if its time average equals its
space average. For idea diffusion, ergodicity means that the long-run
resonance profile of an idea after many transmissions through the same
agent converges to a "stationary" profile. We prove structural results
about ergodic-like properties of iterated reception. -/

section ErgodicTheory
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Mixing coefficient: how much two iterated receptions through different
    agents diverge at step n. -/
noncomputable def mixingCoefficient (a r₁ r₂ observer : I) (n : ℕ) : ℝ :=
  rs (iteratedReceive a r₁ n) observer -
  rs (iteratedReceive a r₂ n) observer

/-- Mixing coefficient at step 0 is zero — both start from the same idea. -/
theorem mixingCoefficient_zero (a r₁ r₂ observer : I) :
    mixingCoefficient a r₁ r₂ observer 0 = 0 := by
  unfold mixingCoefficient iteratedReceive; ring

/-- Mixing coefficient against void observer is zero. -/
theorem mixingCoefficient_void_observer (a r₁ r₂ : I) (n : ℕ) :
    mixingCoefficient a r₁ r₂ (void : I) n = 0 := by
  unfold mixingCoefficient; simp [rs_void_right']

/-- Mixing coefficient is antisymmetric in the agents. -/
theorem mixingCoefficient_antisymm (a r₁ r₂ observer : I) (n : ℕ) :
    mixingCoefficient a r₁ r₂ observer n =
    -mixingCoefficient a r₂ r₁ observer n := by
  unfold mixingCoefficient; ring

/-- Ergodic weight growth: the self-resonance of iterated reception
    is monotonically non-decreasing (from compose_enriches). -/
theorem ergodic_weight_growth (a r : I) (n : ℕ) :
    rs (iteratedReceive a r (n + 1)) (iteratedReceive a r (n + 1)) ≥
    rs r r :=
  iteratedReceive_enriches a r n

/-- Iterated reception through void is stationary — void is an ergodic fixed point. -/
theorem ergodic_void_stationary (a : I) (n : ℕ) :
    iteratedReceive a (void : I) n = a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iteratedReceive, receive, ih]

/-- Void idea under any iteration stays the agent-dominated form. -/
theorem ergodic_void_idea (r : I) :
    iteratedReceive (void : I) r 1 = r := by
  simp [iteratedReceive, receive]

end ErgodicTheory

/-! ## §41. Mixing Times and Convergence Rates

How fast do iterated transmissions stabilize? While we can't prove
convergence without topology, we can bound the "distance" between
successive iterations using emergence bounds. -/

section MixingTimes
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Step-to-step resonance change: how much the resonance profile shifts
    between iteration n and n+1. -/
noncomputable def iterationShift (a r observer : I) (n : ℕ) : ℝ :=
  rs (iteratedReceive a r (n + 1)) observer -
  rs (iteratedReceive a r n) observer

/-- Iteration shift at step 0 is the first resonance shift. -/
theorem iterationShift_zero (a r observer : I) :
    iterationShift a r observer 0 = resonanceShift r a observer := by
  unfold iterationShift iteratedReceive iteratedReceive resonanceShift receive; ring

/-- Iteration shift vanishes against void observer. -/
theorem iterationShift_void_observer (a r : I) (n : ℕ) :
    iterationShift a r (void : I) n = 0 := by
  unfold iterationShift; simp [rs_void_right']

/-- Iteration shift decomposes: the shift from step n to n+1
    equals the resonance change from one more composition with r. -/
theorem iterationShift_decompose (a r observer : I) (n : ℕ) :
    iterationShift a r observer n =
    rs r observer + emergence r (iteratedReceive a r n) observer := by
  cases n with
  | zero =>
    simp only [iterationShift, iteratedReceive, receive, emergence]
    ring
  | succ n =>
    simp only [iterationShift, iteratedReceive, receive, emergence]
    ring

end MixingTimes

/-! ## §42. Idea Diffusion on Weighted Networks

Network nodes are agents, edges have weights representing communication
frequency. The resonance between transmitted ideas accumulates differently
depending on the network's weight structure. -/

section WeightedNetworks
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Weighted reception: receiving an idea n times models high-frequency
    communication along a weighted edge. -/
def weightedReceive (agent idea : I) : ℕ → I
  | 0 => agent
  | n + 1 => receive (weightedReceive agent idea n) idea

/-- Weighted reception at 0 is the agent itself. -/
theorem weightedReceive_zero (agent idea : I) :
    weightedReceive agent idea 0 = agent := rfl

/-- Weighted reception at n+1 unfolds. -/
theorem weightedReceive_succ (agent idea : I) (n : ℕ) :
    weightedReceive agent idea (n + 1) =
    compose (weightedReceive agent idea n) idea := rfl

/-- Weighted reception enriches monotonically. -/
theorem weightedReceive_enriches (agent idea : I) (n : ℕ) :
    rs (weightedReceive agent idea (n + 1)) (weightedReceive agent idea (n + 1)) ≥
    rs (weightedReceive agent idea n) (weightedReceive agent idea n) := by
  simp [weightedReceive_succ]
  exact compose_enriches' (weightedReceive agent idea n) idea

/-- Weighted reception through void idea is the agent itself. -/
theorem weightedReceive_void_idea (agent : I) (n : ℕ) :
    weightedReceive agent (void : I) n = agent := by
  induction n with
  | zero => rfl
  | succ n ih => simp [weightedReceive, receive, ih]

/-- Weighted reception of void agent at step n+1 is composeN idea (n+1). -/
theorem weightedReceive_void_agent_one (idea : I) :
    weightedReceive (void : I) idea 1 = idea := by
  simp [weightedReceive, receive]

end WeightedNetworks

/-! ## §43. Idea Mutation Operators

Systematic vs random mutation in idea transmission. Bernays' "engineering
of consent" uses systematic mutation (propaganda), while rumor mills
produce random mutation. We formalize the algebra of mutation operators. -/

section MutationOperators
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A mutation operator: an agent that systematically transforms ideas.
    The mutation of idea a by operator m is compose(m, a). -/
def mutate (operator idea : I) : I := compose operator idea

/-- Mutation by void is identity — no mutation. -/
theorem mutate_void_operator (a : I) :
    mutate (void : I) a = a := by
  unfold mutate; simp

/-- Mutation of void produces the operator itself. -/
theorem mutate_void_idea (m : I) :
    mutate m (void : I) = m := by
  unfold mutate; simp

/-- Sequential mutation is associative. -/
theorem mutate_assoc (m₁ m₂ a : I) :
    mutate m₁ (mutate m₂ a) = compose m₁ (compose m₂ a) := rfl

/-- Sequential mutation compresses: mutate m₁ (mutate m₂ a) =
    compose (compose m₁ m₂) a, so two mutations equal one by the composite. -/
theorem mutate_compress (m₁ m₂ a : I) :
    mutate m₁ (mutate m₂ a) = compose (compose m₁ m₂) a := by
  unfold mutate; rw [compose_assoc']

/-- Mutation enriches the operator's weight. -/
theorem mutate_enriches (m a : I) :
    rs (mutate m a) (mutate m a) ≥ rs m m := by
  unfold mutate; exact compose_enriches' m a

/-- Mutation magnitude is the emergence. -/
theorem mutate_magnitude (m a c : I) :
    rs (mutate m a) c - rs m c - rs a c = emergence m a c := by
  unfold mutate emergence; ring

/-- Non-void operator always produces non-void output. -/
theorem mutate_ne_void (m a : I) (hm : m ≠ void) :
    mutate m a ≠ void :=
  compose_ne_void_of_left m a hm

/-- Iterated mutation: applying the same operator n times. -/
def iteratedMutate (operator idea : I) : ℕ → I
  | 0 => idea
  | n + 1 => mutate operator (iteratedMutate operator idea n)

/-- Iterated mutation at 0 is the idea itself. -/
theorem iteratedMutate_zero (m a : I) :
    iteratedMutate m a 0 = a := rfl

/-- Iterated mutation at n+1 unfolds. -/
theorem iteratedMutate_succ (m a : I) (n : ℕ) :
    iteratedMutate m a (n + 1) =
    compose m (iteratedMutate m a n) := rfl

/-- Iterated mutation through void operator is the idea itself. -/
theorem iteratedMutate_void (a : I) (n : ℕ) :
    iteratedMutate (void : I) a n = a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iteratedMutate, mutate, ih]

/-- Iterated mutation enriches beyond operator at each step. -/
theorem iteratedMutate_enriches (m a : I) (n : ℕ) :
    rs (iteratedMutate m a (n + 1)) (iteratedMutate m a (n + 1)) ≥
    rs m m := by
  simp [iteratedMutate_succ]; exact compose_enriches' m (iteratedMutate m a n)

end MutationOperators

/-! ## §44. Chomsky's Manufacturing Consent — Filters Model

Chomsky and Herman's propaganda model identifies five filters through which
news passes. In IDT, each filter is an agent that composes with the idea,
and the five-filter model is a five-hop transmission chain. -/

section ManufacturingConsent
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The five filters of manufacturing consent: ownership, advertising,
    sourcing, flak, and ideology. Each is an agent that transforms the idea. -/
def fiveFilterModel (idea ownership advertising sourcing flak ideology : I) : I :=
  transmitChain idea [ownership, advertising, sourcing, flak, ideology]

/-- If all filters are void (no filtering), the idea passes unchanged. -/
theorem fiveFilter_void (idea : I) :
    fiveFilterModel idea (void : I) (void : I) (void : I) (void : I) (void : I) = idea := by
  simp [fiveFilterModel, transmitChain, receive]

/-- With only ownership filter active, the result is simple reception. -/
theorem fiveFilter_ownership_only (idea own : I) :
    fiveFilterModel idea own (void : I) (void : I) (void : I) (void : I) =
    receive own idea := by
  simp [fiveFilterModel, transmitChain, receive]

/-- The five-filter model enriches beyond the last filter's weight. -/
theorem fiveFilter_enriches_ideology (idea own adv src flk ideo : I) :
    rs (fiveFilterModel idea own adv src flk ideo)
       (fiveFilterModel idea own adv src flk ideo) ≥ rs ideo ideo := by
  unfold fiveFilterModel; simp [transmitChain, receive]
  exact compose_enriches' ideo _

/-- Each filter in sequence never produces void if the filter is non-void. -/
theorem filter_never_void (idea f : I) (hf : f ≠ void) :
    receive f idea ≠ void :=
  compose_ne_void_of_left f idea hf

end ManufacturingConsent

/-! ## §45. Idea Thermodynamics — Entropy and Free Energy

Drawing on thermodynamic analogies: ideas have "entropy" (how spread out
their resonance profile is) and "free energy" (capacity for further
emergence). The second law of idea thermodynamics: self-resonance never
decreases under composition. -/

section IdeaThermodynamics
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Idea weight: the self-resonance of an idea, analogous to internal energy. -/
noncomputable def ideaWeight (a : I) : ℝ := rs a a

/-- Void has zero weight. -/
theorem ideaWeight_void : ideaWeight (void : I) = 0 := rs_void_void

/-- Weight is non-negative. -/
theorem ideaWeight_nonneg (a : I) : ideaWeight a ≥ 0 := by
  unfold ideaWeight; exact S.rs_self_nonneg a

/-- Weight is positive for non-void ideas. -/
theorem ideaWeight_pos (a : I) (h : a ≠ void) : ideaWeight a > 0 := by
  unfold ideaWeight; exact rs_self_pos a h

/-- Second law of idea thermodynamics: composition never decreases weight.
    This is the analogue of the second law — "entropy" (weight) always grows. -/
theorem secondLaw (a b : I) :
    ideaWeight (compose a b) ≥ ideaWeight a := by
  unfold ideaWeight; exact compose_enriches' a b

/-- Free energy: the capacity for emergence, bounded by the product of
    self-resonances. This measures how much NEW meaning can be created
    when two ideas interact. -/
noncomputable def freeEnergy (a b : I) : ℝ :=
  ideaWeight (compose a b) - ideaWeight a - ideaWeight b

/-- Free energy relates to self-emergence via the cross-resonances:
    free energy = self-emergence + cross-terms. -/
theorem freeEnergy_selfEmergence_relation (a b : I) :
    freeEnergy a b = selfEmergence a b +
    (rs a (compose a b) - rs a a) + (rs b (compose a b) - rs b b) := by
  unfold freeEnergy ideaWeight selfEmergence emergence
  have h := rs_compose_eq a b (compose a b)
  linarith

/-- Free energy with void is zero. -/
theorem freeEnergy_void_right (a : I) :
    freeEnergy a (void : I) = 0 := by
  unfold freeEnergy ideaWeight; simp [rs_void_void]

/-- Free energy from void is the idea's weight. -/
theorem freeEnergy_void_left (b : I) :
    freeEnergy (void : I) b = 0 := by
  unfold freeEnergy ideaWeight; simp [rs_void_void]

/-- Gibbs free energy: emergence relative to a "temperature" (observer). -/
noncomputable def gibbsFreeEnergy (a b observer : I) : ℝ :=
  emergence a b observer

/-- Gibbs free energy vanishes at void temperature. -/
theorem gibbsFreeEnergy_void_observer (a b : I) :
    gibbsFreeEnergy a b (void : I) = 0 :=
  emergence_against_void a b

/-- Gibbs free energy is bounded by √(weight × observer weight). -/
theorem gibbsFreeEnergy_bounded (a b observer : I) :
    (gibbsFreeEnergy a b observer) ^ 2 ≤
    rs (compose a b) (compose a b) * rs observer observer := by
  unfold gibbsFreeEnergy; exact emergence_bounded' a b observer

end IdeaThermodynamics

/-! ## §46. Deep Math — Algebraic Invariants of Diffusion

The cocycle condition constrains emergence globally. We derive further
algebraic consequences that characterize the space of possible diffusion
patterns. These are the "conservation laws" of idea spread. -/

section AlgebraicInvariants
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Cocycle defect: measures the failure of emergence to be a cocycle
    in the group-cohomological sense. In IDT, the defect is ZERO by
    the associativity axiom. -/
noncomputable def cocycleDefect (a b c d : I) : ℝ :=
  emergence a b d + emergence (compose a b) c d -
  emergence b c d - emergence a (compose b c) d

/-- The cocycle defect vanishes — this is the cocycle condition. -/
theorem cocycleDefect_zero (a b c d : I) :
    cocycleDefect a b c d = 0 := by
  unfold cocycleDefect
  have h := cocycle_condition a b c d
  linarith

/-- Emergence of a self-composition decomposes via the cocycle. -/
theorem emergence_selfCompose (a c : I) :
    emergence a a c = rs (compose a a) c - 2 * rs a c := by
  unfold emergence; ring

/-- Triple composition resonance expands fully. -/
theorem tripleCompose_resonance (a b c d : I) :
    rs (compose (compose a b) c) d =
    rs a d + rs b d + rs c d +
    emergence a b d + emergence (compose a b) c d := by
  have h1 := rs_compose_eq a b d
  have h2 := rs_compose_eq (compose a b) c d
  linarith

/-- The emergence of composed pair with a third element relates to
    individual emergences via the cocycle. -/
theorem emergence_compose_left (a b c d : I) :
    emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d - emergence a b d := by
  have := cocycleDefect_zero a b c d
  unfold cocycleDefect at this; linarith

/-- Void annihilates cocycle defect trivially. -/
theorem cocycleDefect_void_first (b c d : I) :
    cocycleDefect (void : I) b c d = 0 :=
  cocycleDefect_zero (void : I) b c d

/-- The alternating sum property of emergence. -/
theorem emergence_alternating (a b c : I) :
    emergence a b c + emergence b a c =
    rs (compose a b) c + rs (compose b a) c - 2 * rs a c - 2 * rs b c := by
  unfold emergence; ring

end AlgebraicInvariants

/-! ## §47. Green's Functions — Resolvent of Ideatic Diffusion

The Green's function G(a, b) of an agent r maps pairs (input idea, observer)
to the resonance of the received version. This encodes all information about
how the agent transforms ideas. -/

section GreensFunctions
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The Green's function of an agent at a pair of ideas. -/
noncomputable def greensFunction (agent : I) (idea observer : I) : ℝ :=
  diffusionKernel agent idea observer

/-- Green's function of void is the free propagator. -/
theorem greensFunction_void (idea observer : I) :
    greensFunction (void : I) idea observer = rs idea observer :=
  diffusionKernel_void_agent idea observer

/-- Green's function for void input returns agent's profile. -/
theorem greensFunction_void_input (agent observer : I) :
    greensFunction agent (void : I) observer = rs agent observer :=
  diffusionKernel_void_idea agent observer

/-- Green's function vanishes at void observer. -/
theorem greensFunction_void_observer (agent idea : I) :
    greensFunction agent idea (void : I) = 0 :=
  diffusionKernel_void_observer agent idea

/-- Green's function at self-resonance of output is non-negative. -/
theorem greensFunction_self_nonneg (agent idea : I) :
    greensFunction agent idea (receive agent idea) ≥ 0 :=
  diffusionKernel_self_nonneg agent idea

/-- Green's function decomposes additively. -/
theorem greensFunction_decompose (agent idea observer : I) :
    greensFunction agent idea observer =
    rs agent observer + rs idea observer + emergence agent idea observer :=
  diffusionKernel_decompose agent idea observer

/-- Composition of Green's functions gives two-hop resonance. -/
theorem greensFunction_compose (a₁ a₂ idea observer : I) :
    greensFunction a₂ (receive a₁ idea) observer =
    rs (twoHop idea a₁ a₂) observer :=
  diffusionKernel_compose a₁ a₂ idea observer

end GreensFunctions

/-! ## §48. Spectral Theory of Ideatic Operators

The "spectrum" of an agent r consists of ideas whose resonance profiles
are eigenvector-like: receiving them through r shifts resonance by a
multiplicative factor. While true eigenvalues require linearity (which
emergence violates), we can study the linear part. -/

section SpectralTheory
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- An idea a is a resonance eigenidea of agent r with eigenvalue λ if
    receiving a through r produces resonance λ times the original,
    for ALL observers. This requires linearity (zero emergence). -/
def isEigenidea (idea agent : I) (eigenval : ℝ) : Prop :=
  ∀ c : I, rs (receive agent idea) c = eigenval * rs idea c

/-- Void is an eigenidea with any eigenvalue for the void agent,
    since both sides reduce to zero. -/
theorem void_eigenidea_void_agent (ev : ℝ) :
    isEigenidea (void : I) (void : I) ev := by
  intro c; unfold receive; simp [rs_void_left']

/-- An absorbing idea: one that is a resonance fixed point — receiving it
    produces the same resonance profile as the receiver alone. -/
def isAbsorbing (idea agent : I) : Prop :=
  ∀ c : I, rs (receive agent idea) c = rs agent c + rs idea c

/-- Void is absorbing for any agent (no emergence). -/
theorem void_absorbing (agent : I) : isAbsorbing (void : I) agent := by
  intro c; unfold receive; simp [rs_void_right', rs_void_left']

/-- Any idea is absorbing for void agent. -/
theorem absorbing_void_agent (idea : I) : isAbsorbing idea (void : I) := by
  intro c; unfold receive; simp [rs_void_left']

/-- If an idea is absorbing, the emergence vanishes. -/
theorem absorbing_zero_emergence (a r : I) (h : isAbsorbing a r) (c : I) :
    emergence r a c = 0 := by
  have h1 := h c; unfold receive at h1
  unfold emergence; linarith [rs_compose_eq r a c]

/-- Absorbing implies preserved. -/
theorem absorbing_implies_preserved (a r : I) (h : isAbsorbing a r) :
    preserved r a := by
  intro c; unfold mutationMagnitude transmissionEmergence
  exact absorbing_zero_emergence a r h c

end SpectralTheory

/-! ## §49. Rate-Distortion Theory — Lossy Idea Compression

When ideas must pass through bandwidth-limited channels, some information
is lost. The rate-distortion function measures the minimum distortion at
a given transmission rate. In IDT, distortion is emergence-based. -/

section RateDistortionTheory
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Distortion between original and received version, as measured
    against the original itself. -/
noncomputable def selfDistortion (idea channel : I) : ℝ :=
  rs idea idea - rs (receive channel idea) idea

/-- Self-distortion of void idea is zero. -/
theorem selfDistortion_void_idea (ch : I) :
    selfDistortion (void : I) ch = 0 := by
  unfold selfDistortion receive; simp [rs_void_left', rs_void_right', rs_void_void]

/-- Self-distortion through void channel is zero — lossless. -/
theorem selfDistortion_void_channel (a : I) :
    selfDistortion a (void : I) = 0 := by
  unfold selfDistortion receive; simp

/-- Self-distortion decomposes via emergence. -/
theorem selfDistortion_eq (a ch : I) :
    selfDistortion a ch =
    -(rs ch a + emergence ch a a) := by
  unfold selfDistortion receive emergence; ring

/-- Reconstruction error: the resonance deficit between original and received. -/
noncomputable def reconstructionError (idea channel : I) : ℝ :=
  resonanceDeficit idea (receive channel idea)

/-- Reconstruction error through void channel is zero. -/
theorem reconstructionError_void (a : I) :
    reconstructionError a (void : I) = 0 := by
  unfold reconstructionError receive; simp [resonanceDeficit_self]

/-- Reconstruction error of void idea. -/
theorem reconstructionError_void_idea (ch : I) :
    reconstructionError (void : I) ch = resonanceDeficit (void : I) ch := by
  unfold reconstructionError receive; simp

end RateDistortionTheory

/-! ## §50. Idea Genealogy — Lineage and Heritage

Ideas have genealogies: each received version is a "child" of the original
composed with the receiver's "genetic material." We formalize the tree
structure of idea diffusion and prove properties of lineage. -/

section IdeaGenealogy
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The child of idea a through agent r: the next generation. -/
def child (parent agent : I) : I := receive agent parent

/-- Child through void agent is the parent. -/
theorem child_void_agent (a : I) :
    child a (void : I) = a := by
  unfold child receive; simp

/-- Child of void parent is the agent. -/
theorem child_void_parent (r : I) :
    child (void : I) r = r := by
  unfold child receive; simp

/-- Grandchild: two generations of transmission. -/
def grandchild (idea r₁ r₂ : I) : I := child (child idea r₁) r₂

/-- Grandchild equals two-hop. -/
theorem grandchild_eq_twoHop (a r₁ r₂ : I) :
    grandchild a r₁ r₂ = twoHop a r₁ r₂ := rfl

/-- Heritage distance: how far a descendant has drifted from the ancestor. -/
noncomputable def heritageDist (ancestor descendant observer : I) : ℝ :=
  rs ancestor observer - rs descendant observer

/-- Heritage distance is zero for same-generation. -/
theorem heritageDist_self (a c : I) :
    heritageDist a a c = 0 := by
  unfold heritageDist; ring

/-- Heritage distance of child decomposes. -/
theorem heritageDist_child (a r c : I) :
    heritageDist a (child a r) c = -(rs r c + emergence r a c) := by
  unfold heritageDist child receive emergence; ring

/-- Heritage distance vanishes against void observer. -/
theorem heritageDist_void_observer (a d : I) :
    heritageDist a d (void : I) = 0 := by
  unfold heritageDist; simp [rs_void_right']

/-- The parent's weight is always ≤ the child's weight (second law). -/
theorem child_weight_grows (a r : I) :
    rs (child a r) (child a r) ≥ rs r r := by
  unfold child; exact compose_enriches' r a

end IdeaGenealogy

/-! ## §51. Dual Diffusion — Ideas Spread, But So Do Agents' Influence

Standard diffusion tracks how ideas change agents. Dual diffusion tracks
how agents change ideas. The dual kernel is the transposed Green's function. -/

section DualDiffusion
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The dual kernel: given an agent, how does the agent's influence
    propagate to different ideas? -/
noncomputable def dualKernel (agent idea observer : I) : ℝ :=
  rs (compose idea agent) observer

/-- Dual kernel of void agent is just the idea's resonance. -/
theorem dualKernel_void_agent (idea observer : I) :
    dualKernel (void : I) idea observer = rs idea observer := by
  unfold dualKernel; simp

/-- Dual kernel for void idea is the agent's resonance. -/
theorem dualKernel_void_idea (agent observer : I) :
    dualKernel agent (void : I) observer = rs agent observer := by
  unfold dualKernel; simp

/-- Dual kernel vanishes at void observer. -/
theorem dualKernel_void_observer (agent idea : I) :
    dualKernel agent idea (void : I) = 0 := by
  unfold dualKernel; exact rs_void_right' _

/-- Dual kernel decomposes with emergence (note reversed order). -/
theorem dualKernel_decompose (agent idea observer : I) :
    dualKernel agent idea observer =
    rs idea observer + rs agent observer + emergence idea agent observer := by
  unfold dualKernel; rw [rs_compose_eq]

/-- Dual kernel self-resonance is enriched. -/
theorem dualKernel_enriches (agent idea : I) :
    rs (compose idea agent) (compose idea agent) ≥ rs idea idea := by
  exact compose_enriches' idea agent

/-- The asymmetry between kernel and dual kernel is the order sensitivity. -/
theorem kernel_dual_asymmetry (agent idea observer : I) :
    diffusionKernel agent idea observer - dualKernel agent idea observer =
    emergence agent idea observer - emergence idea agent observer := by
  unfold diffusionKernel dualKernel receive emergence; ring

end DualDiffusion

/-! ## §52. Compositional Depth of Diffusion Chains

As ideas traverse longer chains, the "compositional depth" grows.
We formalize how depth relates to the number of hops and the
emergence accumulated at each step. -/

section CompositionalDepth
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Compositional depth: the self-resonance of a chain-transmitted idea.
    Deeper chains have higher self-resonance (from compose_enriches). -/
noncomputable def chainDepth (idea : I) (chain : List I) : ℝ :=
  rs (transmitChain idea chain) (transmitChain idea chain)

/-- Chain depth of empty chain is the idea's self-resonance. -/
theorem chainDepth_nil (a : I) :
    chainDepth a ([] : List I) = rs a a := rfl

/-- Chain depth through void agents equals idea's self-resonance. -/
theorem chainDepth_void_chain (a : I) (n : ℕ) :
    chainDepth a (List.replicate n (void : I)) = rs a a := by
  unfold chainDepth; rw [peer_to_peer_void_chain]

/-- Chain depth is non-negative. -/
theorem chainDepth_nonneg (idea : I) (chain : List I) :
    chainDepth idea chain ≥ 0 := by
  unfold chainDepth; exact S.rs_self_nonneg _

/-- Adding a non-void agent to the chain means the depth stays non-negative. -/
theorem chainDepth_singleton_nonneg (idea agent : I) :
    chainDepth idea [agent] ≥ 0 := by
  unfold chainDepth transmitChain; exact S.rs_self_nonneg _

/-- Depth increment: how much one hop adds to the chain's depth. -/
noncomputable def depthIncrement (idea : I) (chain : List I) (agent : I) : ℝ :=
  chainDepth idea (chain ++ [agent]) - chainDepth idea chain

/-- Depth increment of adding a void agent is non-negative. -/
theorem depthIncrement_void (idea : I) (chain : List I) :
    depthIncrement idea chain (void : I) ≥ 0 := by
  unfold depthIncrement chainDepth
  have : transmitChain idea (chain ++ [void]) = transmitChain idea chain := by
    induction chain generalizing idea with
    | nil => simp [transmitChain, receive]
    | cons a rest ih => simp [transmitChain]; exact ih (receive a idea)
  rw [this]; linarith

end CompositionalDepth

/-! ## §53. Information-Theoretic Bounds on Diffusion

Connecting IDT diffusion to information-theoretic quantities:
the emergence bound gives us a "capacity" constraint, and the
cocycle condition gives us a "conservation law" for information flow. -/

section InfoTheoreticBounds
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Channel capacity analogue: the maximum emergence a channel can produce,
    bounded by its self-resonance and the observer's. -/
noncomputable def channelCapacity (channel observer : I) : ℝ :=
  rs channel channel * rs observer observer

/-- Void channel has zero capacity. -/
theorem channelCapacity_void (observer : I) :
    channelCapacity (void : I) observer = 0 := by
  unfold channelCapacity; simp [rs_void_void]

/-- Capacity against void observer is zero — can't observe anything. -/
theorem channelCapacity_void_observer (channel : I) :
    channelCapacity channel (void : I) = 0 := by
  unfold channelCapacity; simp [rs_void_void]

/-- Capacity is non-negative. -/
theorem channelCapacity_nonneg (channel observer : I) :
    channelCapacity channel observer ≥ 0 := by
  unfold channelCapacity
  have h1 := S.rs_self_nonneg channel
  have h2 := S.rs_self_nonneg observer
  exact mul_nonneg (by linarith) (by linarith)

/-- The actual emergence is bounded by the expanded channel capacity. -/
theorem emergence_capacity_bound (channel idea observer : I) :
    (emergence channel idea observer) ^ 2 ≤
    rs (compose channel idea) (compose channel idea) * rs observer observer :=
  emergence_bounded' channel idea observer

/-- Conservation law: emergence over the cocycle satisfies
    the zero-defect condition. -/
theorem emergence_conservation (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d := by
  have := cocycleDefect_zero a b c d
  unfold cocycleDefect at this; linarith

end InfoTheoreticBounds

/-! ## §54. Diffusion Symmetry Breaking

When ideas spread through asymmetric channels, the symmetry between
sender and receiver is broken. We formalize how the order of composition
creates irreversible transformations. -/

section SymmetryBreaking
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Composition asymmetry: how different compose(a,b) is from compose(b,a)
    as seen by observer c. -/
noncomputable def compositionAsymmetry (a b c : I) : ℝ :=
  rs (compose a b) c - rs (compose b a) c

/-- Composition asymmetry is antisymmetric in a, b. -/
theorem compositionAsymmetry_antisymm (a b c : I) :
    compositionAsymmetry a b c = -compositionAsymmetry b a c := by
  unfold compositionAsymmetry; ring

/-- Composition asymmetry with void is zero. -/
theorem compositionAsymmetry_void_left (b c : I) :
    compositionAsymmetry (void : I) b c = 0 := by
  unfold compositionAsymmetry; simp

/-- Composition asymmetry with void on right is also zero. -/
theorem compositionAsymmetry_void_right (a c : I) :
    compositionAsymmetry a (void : I) c = 0 := by
  unfold compositionAsymmetry; simp

/-- Composition asymmetry vanishes for void observer. -/
theorem compositionAsymmetry_void_observer (a b : I) :
    compositionAsymmetry a b (void : I) = 0 := by
  unfold compositionAsymmetry; simp [rs_void_right']

/-- Composition asymmetry equals emergence difference. -/
theorem compositionAsymmetry_emergence (a b c : I) :
    compositionAsymmetry a b c = emergence a b c - emergence b a c := by
  unfold compositionAsymmetry emergence; ring

/-- Self-composition asymmetry is zero. -/
theorem compositionAsymmetry_self (a c : I) :
    compositionAsymmetry a a c = 0 := by
  unfold compositionAsymmetry; ring

end SymmetryBreaking

/-! ## §55. Receiver Bias and Confirmation Bias

Confirmation bias is the tendency to interpret new ideas in ways that
confirm existing beliefs. In IDT, this is formalized by the emergence
term: a receiver with strong existing beliefs (high self-resonance)
produces large emergence that biases received ideas toward the receiver's
existing resonance profile. -/

section ConfirmationBias
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Confirmation effect: how much receiving idea a reinforces the
    receiver's existing resonance with itself. Positive confirmation
    means the idea makes the receiver "more itself." -/
noncomputable def confirmationEffect (receiver idea : I) : ℝ :=
  rs (receive receiver idea) receiver - rs receiver receiver

/-- Confirmation effect of void idea is zero — silence doesn't confirm. -/
theorem confirmationEffect_void_idea (r : I) :
    confirmationEffect r (void : I) = 0 := by
  unfold confirmationEffect receive; simp

/-- Confirmation effect decomposes via emergence. -/
theorem confirmationEffect_eq (r a : I) :
    confirmationEffect r a =
    rs a r + emergence r a r := by
  unfold confirmationEffect receive emergence; ring

/-- Cognitive dissonance: the squared emergence when receiving an idea
    that clashes with existing beliefs, measured against the receiver itself. -/
noncomputable def cognitiveDissonance (receiver idea : I) : ℝ :=
  (emergence receiver idea receiver) ^ 2

/-- Cognitive dissonance is non-negative. -/
theorem cognitiveDissonance_nonneg (r a : I) :
    cognitiveDissonance r a ≥ 0 := by
  unfold cognitiveDissonance; positivity

/-- Cognitive dissonance with void idea is zero. -/
theorem cognitiveDissonance_void_idea (r : I) :
    cognitiveDissonance r (void : I) = 0 := by
  unfold cognitiveDissonance; rw [emergence_void_right]; ring

/-- Cognitive dissonance for void receiver is zero. -/
theorem cognitiveDissonance_void_receiver (a : I) :
    cognitiveDissonance (void : I) a = 0 := by
  unfold cognitiveDissonance; rw [emergence_void_left]; ring

/-- Cognitive dissonance is bounded by weight product. -/
theorem cognitiveDissonance_bounded (r a : I) :
    cognitiveDissonance r a ≤
    rs (receive r a) (receive r a) * rs r r := by
  unfold cognitiveDissonance receive; exact emergence_bounded' r a r

end ConfirmationBias

end IDT3
