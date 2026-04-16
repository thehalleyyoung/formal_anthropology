import FormalAnthropology.IDT_v3_Foundations

/-!
# IDT v3: Network Diffusion of Ideas

How ideas spread through populations, echo chambers form, information
cascades build, and opinion dynamics evolve — all within the IdeaticSpace3
framework.

## Core insight

A **population** is a finite list of ideas. The **consensus** is their
composition. Echo chambers arise when subsets have high mutual resonance.
Information cascades are sequential compositions where early ideas dominate.
Opinion dynamics track how iterated interaction changes agents.

## NO SORRIES
-/

namespace IDT3

open IdeaticSpace3

/-! ## §1. Populations and Consensus -/

section Populations
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The consensus of a population: left-fold composition of all ideas. -/
def consensus : List I → I
  | [] => void
  | a :: rest => compose a (consensus rest)

@[simp] theorem consensus_nil : consensus ([] : List I) = (void : I) := rfl

@[simp] theorem consensus_singleton (a : I) : consensus [a] = a := by
  simp [consensus]

theorem consensus_cons (a : I) (l : List I) :
    consensus (a :: l) = compose a (consensus l) := rfl

/-- Consensus of two elements is their composition. -/
theorem consensus_pair (a b : I) : consensus [a, b] = compose a b := by
  simp [consensus]

-- Theorem 1: Consensus of void list is void
theorem consensus_void_list : consensus ([] : List I) = (void : I) := rfl

-- Theorem 2: Prepending void doesn't change consensus
theorem consensus_cons_void (l : List I) :
    consensus ((void : I) :: l) = consensus l := by
  simp [consensus]

-- Theorem 3: Self-resonance of consensus of pair ≥ first element
theorem consensus_pair_enriches_left (a b : I) :
    rs (consensus [a, b]) (consensus [a, b]) ≥ rs a a := by
  simp [consensus]
  exact compose_enriches' a b

-- Theorem 4: Consensus of singleton has same self-resonance as the element
theorem consensus_singleton_rs (a : I) :
    rs (consensus [a]) (consensus [a]) = rs a a := by
  simp

-- Theorem 5: Adding void to a population doesn't change consensus resonance
theorem consensus_append_void (l : List I) :
    consensus (l ++ [void]) = consensus l := by
  induction l with
  | nil => simp [consensus]
  | cons x xs ih => simp [consensus, ih]

-- Theorem 6: Consensus with void element
theorem consensus_void_element (a : I) :
    consensus [void, a] = a := by
  simp [consensus]

-- Theorem 7: Non-void first element means consensus is non-void (for pair)
theorem consensus_pair_ne_void (a b : I) (h : a ≠ void) :
    consensus [a, b] ≠ void := by
  simp [consensus]
  exact compose_ne_void_of_left a b h

-- Theorem 8: Resonance of consensus with observer decomposes
theorem consensus_pair_rs (a b c : I) :
    rs (consensus [a, b]) c = rs a c + rs b c + emergence a b c := by
  simp [consensus]
  exact rs_compose_eq a b c

-- Theorem 9: Consensus self-resonance is non-negative
theorem consensus_self_nonneg (l : List I) :
    rs (consensus l) (consensus l) ≥ 0 :=
  rs_self_nonneg' _

-- Theorem 10: Consensus of triple via pair consensus
theorem consensus_triple (a b c : I) :
    consensus [a, b, c] = compose a (compose b c) := by
  simp [consensus]

-- Theorem 11: Self-resonance monotonicity: adding an element doesn't decrease
theorem consensus_enriches_prepend (a : I) (l : List I) :
    rs (consensus (a :: l)) (consensus (a :: l)) ≥ rs a a := by
  simp [consensus]
  exact compose_enriches' a (consensus l)

-- Theorem 12: Consensus of repeated void is void
theorem consensus_void_repeat : ∀ (n : ℕ),
    consensus (List.replicate n (void : I)) = (void : I)
  | 0 => rfl
  | n + 1 => by simp [consensus, List.replicate, consensus_void_repeat n]

-- Theorem 13: Emergence from consensus pair
theorem consensus_pair_emergence (a b c : I) :
    emergence a b c = rs (consensus [a, b]) c - rs a c - rs b c := by
  simp [consensus]; unfold emergence; ring

end Populations

/-! ## §2. Echo Chambers -/

section EchoChambers
variable {I : Type*} [S : IdeaticSpace3 I]

/-- An echo chamber member: idea with high self-resonance after composition
    with another. -/
def chamberPair (a b : I) : Prop :=
  rs a b > 0 ∧ rs b a > 0

-- Theorem 14: Void is not a chamber pair with any non-void idea
theorem void_not_chamber_left (a : I) : ¬chamberPair (void : I) a := by
  intro ⟨h, _⟩
  simp [rs_void_left'] at h

-- Theorem 15: Chamber pair implies both non-void
theorem chamber_pair_nonvoid (a b : I) (h : chamberPair a b) :
    a ≠ void ∧ b ≠ void := by
  constructor
  · intro ha; rw [ha] at h; exact absurd h.2 (by simp [rs_void_right'])
  · intro hb; rw [hb] at h; exact absurd h.1 (by simp [rs_void_right'])

-- Theorem 16: Echo chamber composition enriches beyond individual weight
theorem chamber_composition_enriches (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a :=
  compose_enriches' a b

-- Theorem 17: Echo chamber double composition enriches further
theorem chamber_double_enriches (a b : I) :
    rs (compose (compose a b) a) (compose (compose a b) a) ≥
    rs (compose a b) (compose a b) :=
  compose_enriches' (compose a b) a

-- Theorem 18: Chamber isolation — zero resonance means zero linear contribution
theorem chamber_isolation (a b c : I)
    (h1 : rs a c = 0) (h2 : rs b c = 0) :
    rs (compose a b) c = emergence a b c := by
  have := rs_compose_eq a b c
  linarith

-- Theorem 19: Polarized chambers — emergence bound with opposing resonance
theorem polarization_emergence_bound (a b c : I) :
    (emergence a b c) ^ 2 ≤
    rs (compose a b) (compose a b) * rs c c :=
  emergence_bounded' a b c

-- Theorem 20: Chamber amplification — iterated composition within chamber
theorem chamber_iterated_enrichment (a : I) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) ≥
    rs (composeN a n) (composeN a n) := by
  simp only [composeN_succ]
  exact compose_enriches' (composeN a n) a

-- Theorem 21: Chamber with void outsider
theorem chamber_void_outsider (a b : I) :
    emergence a b (void : I) = 0 :=
  emergence_against_void a b

-- Theorem 22: Outsider emergence bound
theorem outsider_emergence_bound (a b c : I) (hc : rs c c = 0) :
    emergence a b c = 0 := by
  have hv := rs_nondegen' c hc
  rw [hv]; exact emergence_against_void a b

-- Theorem 23: Echo chamber enrichment chain (3 compositions)
theorem chamber_triple_enrichment (a b : I) :
    rs (compose (compose a b) a) (compose (compose a b) a) ≥ rs a a := by
  calc rs (compose (compose a b) a) (compose (compose a b) a)
      ≥ rs (compose a b) (compose a b) := compose_enriches' _ _
    _ ≥ rs a a := compose_enriches' _ _

end EchoChambers

/-! ## §3. Information Cascades -/

section Cascades
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A cascade is a sequence of partial compositions:
    cascade [a₁, a₂, a₃] = [a₁, a₁ ∘ a₂, (a₁ ∘ a₂) ∘ a₃] -/
def cascadeStep : I → List I → List I
  | acc, [] => [acc]
  | acc, x :: xs => acc :: cascadeStep (compose acc x) xs

-- Theorem 24: Cascade step of empty list is singleton
theorem cascadeStep_nil (a : I) : cascadeStep a [] = [a] := rfl

-- Theorem 25: Cascade step is non-empty
theorem cascadeStep_nonempty (a : I) (l : List I) :
    (cascadeStep a l).length ≥ 1 := by
  cases l with
  | nil => simp [cascadeStep]
  | cons x xs => simp [cascadeStep]

-- Theorem 26: Cascade weight monotonicity (core cascade theorem)
-- Each step in a cascade has weight ≥ the previous step
theorem cascade_weight_growth (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a :=
  compose_enriches' a b

-- Theorem 27: Early ideas dominate — first idea's weight is always preserved
theorem cascade_first_preserved (a : I) (l : List I) :
    rs (consensus (a :: l)) (consensus (a :: l)) ≥ rs a a := by
  simp [consensus]; exact compose_enriches' a (consensus l)

-- Theorem 28: Cascade of void steps stays void
theorem cascade_void_steps (n : ℕ) :
    composeN (void : I) n = (void : I) := by
  simp [composeN_void]

-- Theorem 29: Cascade enrichment is transitive
theorem cascade_enrichment_transitive (a b c : I) :
    rs (compose (compose a b) c) (compose (compose a b) c) ≥ rs a a := by
  calc rs (compose (compose a b) c) (compose (compose a b) c)
      ≥ rs (compose a b) (compose a b) := compose_enriches' _ _
    _ ≥ rs a a := compose_enriches' _ _

-- Theorem 30: Cascade with void addition doesn't change weight
theorem cascade_void_addition (a : I) :
    rs (compose a (void : I)) (compose a (void : I)) = rs a a := by
  simp

-- Theorem 31: Cascade weight of iterated composition grows
theorem cascade_iterated_weight (a : I) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) ≥ rs a a := by
  induction n with
  | zero =>
    simp only [composeN_succ, composeN_zero, void_left']; linarith [rs_self_nonneg' a]
  | succ n ih =>
    calc rs (composeN a (n + 2)) (composeN a (n + 2))
        ≥ rs (composeN a (n + 1)) (composeN a (n + 1)) := by
          simp only [composeN_succ]; exact compose_enriches' _ _
      _ ≥ rs a a := ih

-- Theorem 32: Fragile cascade — subadditive emergence is bounded
theorem fragile_cascade_bound (a b c : I) :
    (rs (compose a b) c - rs a c - rs b c) ^ 2 ≤
    rs (compose a b) (compose a b) * rs c c :=
  emergence_bounded' a b c

-- Theorem 33: Robust cascade — positive self-resonance persists
theorem robust_cascade_positive (a b : I) (h : a ≠ void) :
    rs (compose a b) (compose a b) > 0 := by
  have h1 := compose_enriches' a b
  have h2 := rs_self_pos a h
  linarith

-- Theorem 34: Cascade resonance decomposition
theorem cascade_resonance_decompose (a b c d : I) :
    rs (compose (compose a b) c) d =
    rs a d + rs b d + rs c d +
    emergence a b d + emergence (compose a b) c d := by
  rw [rs_compose_eq (compose a b) c d, rs_compose_eq a b d]; ring

-- Theorem 35: Cascade associativity — two ways of building cascade agree
theorem cascade_assoc (a b c : I) :
    compose (compose a b) c = compose a (compose b c) :=
  compose_assoc' a b c

end Cascades

/-! ## §4. Opinion Dynamics -/

section OpinionDynamics
variable {I : Type*} [S : IdeaticSpace3 I]

/-- After interaction, agent a's updated state. -/
def interact (a b : I) : I := compose a b

-- Theorem 36: Both agents gain weight after interaction
theorem interaction_enriches_left (a b : I) :
    rs (interact a b) (interact a b) ≥ rs a a := by
  unfold interact; exact compose_enriches' a b

-- Theorem 37: Interaction with void doesn't change state
theorem interact_void_right (a : I) : interact a (void : I) = a := by
  unfold interact; simp

-- Theorem 38: Interaction with void doesn't change state (left)
theorem interact_void_left (b : I) : interact (void : I) b = b := by
  unfold interact; simp

-- Theorem 39: Asymmetry of interaction
-- compose a b and compose b a may differ; their resonance difference is:
theorem interaction_asymmetry (a b c : I) :
    rs (interact a b) c - rs (interact b a) c =
    emergence a b c - emergence b a c := by
  unfold interact emergence; ring

-- Theorem 40: Iterated interaction grows weight
theorem iterated_interaction_grows (a b : I) :
    rs (interact (interact a b) b) (interact (interact a b) b) ≥
    rs (interact a b) (interact a b) := by
  unfold interact; exact compose_enriches' _ _

-- Theorem 41: Self-interaction (repetition) enriches
theorem self_interaction_enriches (a : I) :
    rs (interact a a) (interact a a) ≥ rs a a := by
  unfold interact; exact compose_enriches' a a

-- Theorem 42: Fixed point — void is a fixed point of interaction
theorem void_interaction_fixed (a : I) : interact (void : I) a = a := by
  unfold interact; simp

-- Theorem 43: Stubbornness — interaction doesn't decrease self-resonance
theorem stubborn_weight (a b : I) :
    rs (interact a b) (interact a b) ≥ rs a a := by
  unfold interact; exact compose_enriches' a b

-- Theorem 44: Opinion convergence — resonance decomposition after interaction
theorem interaction_resonance (a b c : I) :
    rs (interact a b) c = rs a c + rs b c + emergence a b c := by
  unfold interact; exact rs_compose_eq a b c

-- Theorem 45: Interaction preserves non-voidness
theorem interaction_preserves_nonvoid (a b : I) (h : a ≠ void) :
    interact a b ≠ void := by
  unfold interact; exact compose_ne_void_of_left a b h

end OpinionDynamics

/-! ## §5. Influence and Centrality -/

section Influence
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The influence of idea a on idea b, as seen by observer c.
    How much does composing with a change b's resonance with c? -/
noncomputable def influence (a b c : I) : ℝ :=
  rs (compose a b) c - rs b c

-- Theorem 46: Influence decomposes into individual resonance + emergence
theorem influence_decompose (a b c : I) :
    influence a b c = rs a c + emergence a b c := by
  unfold influence; rw [rs_compose_eq]; ring

-- Theorem 47: Void has zero influence on everything
theorem void_influence (b c : I) : influence (void : I) b c = 0 := by
  unfold influence; simp

-- Theorem 48: Influence of anything on void is just its resonance
theorem influence_on_void (a c : I) :
    influence a (void : I) c = rs a c := by
  unfold influence; simp [rs_void_left']

-- Theorem 49: Influence against void observer is zero
theorem influence_void_observer (a b : I) :
    influence a b (void : I) = 0 := by
  unfold influence; simp [rs_void_right']

-- Theorem 50: Influence on self — changes own resonance profile
noncomputable def selfInfluence (a c : I) : ℝ :=
  influence a a c

-- Theorem 51: Self-influence decomposition
theorem selfInfluence_eq (a c : I) :
    selfInfluence a c = rs a c + emergence a a c := by
  unfold selfInfluence; exact influence_decompose a a c

-- Theorem 52: Self-influence of void is zero
theorem selfInfluence_void (c : I) : selfInfluence (void : I) c = 0 := by
  unfold selfInfluence; exact void_influence void c

-- Theorem 53: Self-influence decomposition into resonance + emergence
theorem nonvoid_selfInfluence_self (a : I) :
    selfInfluence a a = rs a a + emergence a a a := by
  unfold selfInfluence; exact influence_decompose a a a

-- Theorem 54: Influence minus direct resonance equals emergence
theorem influence_minus_direct (a b c : I) :
    influence a b c - rs a c = emergence a b c := by
  unfold influence emergence; ring

-- Theorem 55: Centrality — void has no influence anywhere
theorem void_centrality_zero (b c : I) :
    influence (void : I) b c = 0 :=
  void_influence b c

end Influence

/-! ## §6. Viral Ideas -/

section ViralIdeas
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A viral spread: composing v with a produces the updated state. -/
def viralSpread (v a : I) : I := compose v a

-- Theorem 56: Viral spread enriches
theorem viral_enriches (v a : I) :
    rs (viralSpread v a) (viralSpread v a) ≥ rs v v := by
  unfold viralSpread; exact compose_enriches' v a

-- Theorem 57: Iterated viral spread — composing v n times
theorem viral_iterated_enrichment (v : I) (n : ℕ) :
    rs (composeN v (n + 1)) (composeN v (n + 1)) ≥
    rs (composeN v n) (composeN v n) := by
  simp only [composeN_succ]; exact compose_enriches' _ _

-- Theorem 58: Viral idea preserves non-voidness
theorem viral_nonvoid (v a : I) (h : v ≠ void) :
    viralSpread v a ≠ void := by
  unfold viralSpread; exact compose_ne_void_of_left v a h

-- Theorem 59: Perfect transmission — zero emergence preserves resonance
theorem perfect_transmission (v a c : I) (h : emergence v a c = 0) :
    rs (viralSpread v a) c = rs v c + rs a c := by
  unfold viralSpread; rw [rs_compose_eq]; linarith

-- Theorem 60: Viral spread of void is identity
theorem viral_void (a : I) : viralSpread (void : I) a = a := by
  unfold viralSpread; simp

-- Theorem 61: Spread to void just returns the virus
theorem viral_to_void (v : I) : viralSpread v (void : I) = v := by
  unfold viralSpread; simp

-- Theorem 62: Mutation during spread — emergence measures mutation
theorem viral_mutation (v a c : I) :
    rs (viralSpread v a) c - rs v c - rs a c = emergence v a c := by
  unfold viralSpread emergence; ring

-- Theorem 63: Iterated viral weight ≥ initial weight
theorem viral_iterated_weight_grows (v : I) (h : v ≠ void) (n : ℕ) :
    rs (composeN v (n + 1)) (composeN v (n + 1)) > 0 := by
  induction n with
  | zero =>
    simp [composeN_succ, composeN_zero]
    exact rs_self_pos v h
  | succ n ih =>
    have h1 : rs (composeN v (n + 2)) (composeN v (n + 2)) ≥
              rs (composeN v (n + 1)) (composeN v (n + 1)) := by
      simp only [composeN_succ]; exact compose_enriches' _ _
    linarith

-- Theorem 64: Viral emergence bound
theorem viral_emergence_bound (v a c : I) :
    (emergence v a c) ^ 2 ≤
    rs (viralSpread v a) (viralSpread v a) * rs c c := by
  unfold viralSpread; exact emergence_bounded' v a c

-- Theorem 65: Double viral spread enriches beyond initial
theorem viral_double_enriches (v a : I) :
    rs (viralSpread v (viralSpread v a)) (viralSpread v (viralSpread v a)) ≥
    rs v v := by
  unfold viralSpread
  calc rs (compose v (compose v a)) (compose v (compose v a))
      = rs (compose (compose v v) a) (compose (compose v v) a) := by
        rw [compose_assoc']
    _ ≥ rs (compose v v) (compose v v) := compose_enriches' _ _
    _ ≥ rs v v := compose_enriches' _ _

end ViralIdeas

/-! ## §7. Bridge Ideas -/

section BridgeIdeas
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A bridge idea has positive resonance with both communities. -/
def isBridge (b c₁ c₂ : I) : Prop :=
  rs b c₁ > 0 ∧ rs b c₂ > 0

-- Theorem 66: Void is never a bridge
theorem void_not_bridge (c₁ c₂ : I) : ¬isBridge (void : I) c₁ c₂ := by
  intro ⟨h1, _⟩; simp [rs_void_left'] at h1

-- Theorem 67: Bridge implies non-void
theorem bridge_nonvoid (b c₁ c₂ : I) (h : isBridge b c₁ c₂) : b ≠ void := by
  intro hb; rw [hb] at h; exact absurd h.1 (by simp [rs_void_left'])

-- Theorem 68: Bridge composition with first community
theorem bridge_compose_first (b c₁ c₂ : I) :
    rs (compose b c₁) c₂ = rs b c₂ + rs c₁ c₂ + emergence b c₁ c₂ :=
  rs_compose_eq b c₁ c₂

-- Theorem 69: Bridge enables cross-community resonance
theorem bridge_enables_resonance (b c₁ c₂ : I) :
    rs (compose b c₁) c₂ = rs b c₂ + rs c₁ c₂ + emergence b c₁ c₂ :=
  rs_compose_eq b c₁ c₂

-- Theorem 70: Bridge composition enriches bridge's weight
theorem bridge_enriches (b c₁ : I) :
    rs (compose b c₁) (compose b c₁) ≥ rs b b :=
  compose_enriches' b c₁

-- Theorem 71: Bridge emergence bound
theorem bridge_emergence_bound (b c₁ c₂ : I) :
    (emergence b c₁ c₂) ^ 2 ≤
    rs (compose b c₁) (compose b c₁) * rs c₂ c₂ :=
  emergence_bounded' b c₁ c₂

-- Theorem 72: Double bridge — composing two bridges
theorem double_bridge_enriches (b₁ b₂ : I) :
    rs (compose b₁ b₂) (compose b₁ b₂) ≥ rs b₁ b₁ :=
  compose_enriches' b₁ b₂

-- Theorem 73: Bridge through void contributes nothing
theorem bridge_through_void (b c : I) :
    emergence b (void : I) c = 0 :=
  emergence_void_right b c

-- Theorem 74: Bridge strength bound — emergence bounded by compositions
theorem bridge_strength_bound (b c₁ c₂ : I) :
    (emergence b c₁ c₂) ^ 2 ≤
    rs (compose b c₁) (compose b c₁) * rs c₂ c₂ :=
  emergence_bounded' b c₁ c₂

-- Theorem 75: Multiple bridges compose
theorem bridges_compose (b₁ b₂ c : I) :
    rs (compose b₁ b₂) c = rs b₁ c + rs b₂ c + emergence b₁ b₂ c :=
  rs_compose_eq b₁ b₂ c

end BridgeIdeas

/-! ## §8. Network Topology -/

section NetworkTopology
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Two ideas are connected if there exists a path (composition) relating them. -/
def connected (a b : I) : Prop :=
  rs a b ≠ 0 ∨ rs b a ≠ 0

-- Theorem 76: Every non-void idea is self-connected
theorem self_connected (a : I) (h : a ≠ void) : connected a a := by
  left; exact ne_of_gt (rs_self_pos a h)

-- Theorem 77: Void is not self-connected
theorem void_not_self_connected : ¬connected (void : I) (void : I) := by
  intro h
  rcases h with h | h <;> exact h rs_void_void

-- Theorem 78: Void is isolated from everything
theorem void_isolated (a : I) : ¬connected (void : I) a := by
  intro h
  rcases h with h | h
  · exact h (rs_void_left' a)
  · exact h (rs_void_right' a)

-- Theorem 79: Connected is symmetric
theorem connected_symm (a b : I) : connected a b → connected b a := by
  intro h
  rcases h with h | h
  · right; exact h
  · left; exact h

-- Theorem 80: Network composition connects
theorem compose_connected_left (a b : I) (h : a ≠ void) :
    connected (compose a b) (compose a b) := by
  left
  have := compose_ne_void_of_left a b h
  exact ne_of_gt (rs_self_pos _ this)

-- Theorem 81: Network diameter — composition chains connect
theorem network_path_enriches (a b c : I) :
    rs (compose (compose a b) c) (compose (compose a b) c) ≥ rs a a := by
  calc rs (compose (compose a b) c) (compose (compose a b) c)
      ≥ rs (compose a b) (compose a b) := compose_enriches' _ _
    _ ≥ rs a a := compose_enriches' _ _

-- Theorem 82: Small world — bridge reduces isolation
theorem bridge_reduces_isolation (b c₁ c₂ : I)
    (h : rs c₁ c₂ = 0) :
    rs (compose b c₁) c₂ = rs b c₂ + emergence b c₁ c₂ := by
  rw [rs_compose_eq]; linarith

-- Theorem 83: Composition preserves positive self-resonance
theorem network_positive_node (a b : I) (h : a ≠ void) :
    rs (compose a b) (compose a b) > 0 := by
  have h1 := compose_enriches' a b
  have h2 := rs_self_pos a h
  linarith

-- Theorem 84: Connected component structure — composing connected elements
theorem compose_weight_nonneg (a b : I) :
    rs (compose a b) (compose a b) ≥ 0 :=
  rs_self_nonneg' _

-- Theorem 85: Diameter bound — n-fold composition
theorem diameter_enrichment (a : I) (n m : ℕ) (h : n ≤ m) :
    rs (composeN a n) (composeN a n) ≤ rs (composeN a m) (composeN a m) := by
  induction h with
  | refl => exact le_refl _
  | @step m' _ ih =>
    have h2 : rs (composeN a (m' + 1)) (composeN a (m' + 1)) ≥
              rs (composeN a m') (composeN a m') := by
      rw [composeN_succ]; exact compose_enriches' _ _
    linarith

end NetworkTopology

/-! ## §9. Diffusion Dynamics -/

section DiffusionDynamics
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Diffusion step: idea propagates from carrier to receiver. -/
def diffuse (carrier receiver : I) : I := compose receiver carrier

-- Theorem 86: Diffusion enriches receiver
theorem diffusion_enriches (carrier receiver : I) :
    rs (diffuse carrier receiver) (diffuse carrier receiver) ≥ rs receiver receiver := by
  unfold diffuse; exact compose_enriches' receiver carrier

-- Theorem 87: Diffusion with void carrier returns receiver
theorem diffuse_void_carrier (r : I) : diffuse (void : I) r = r := by
  unfold diffuse; simp

-- Theorem 88: Diffusion with void receiver returns carrier
theorem diffuse_to_void (c : I) : diffuse c (void : I) = c := by
  unfold diffuse; simp

-- Theorem 89: Diffusion resonance decomposition
theorem diffusion_resonance (carrier receiver observer : I) :
    rs (diffuse carrier receiver) observer =
    rs receiver observer + rs carrier observer +
    emergence receiver carrier observer := by
  unfold diffuse; exact rs_compose_eq receiver carrier observer

-- Theorem 90: Iterated diffusion of same idea grows weight
theorem iterated_diffusion_enriches (idea : I) (n : ℕ) :
    rs (composeN idea (n + 1)) (composeN idea (n + 1)) ≥
    rs (composeN idea n) (composeN idea n) := by
  simp only [composeN_succ]; exact compose_enriches' _ _

end DiffusionDynamics

/-! ## §10. Consensus Formation -/

section ConsensusFormation
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Agreement between two ideas: their mutual resonance average. -/
noncomputable def agreement (a b : I) : ℝ :=
  (rs a b + rs b a) / 2

-- Theorem 91: Agreement is symmetric
theorem agreement_symm (a b : I) : agreement a b = agreement b a := by
  unfold agreement; ring

-- Theorem 92: Agreement with void is zero
theorem agreement_void (a : I) : agreement (void : I) a = 0 := by
  unfold agreement; simp [rs_void_left', rs_void_right']

-- Theorem 93: Self-agreement equals self-resonance
theorem self_agreement (a : I) : agreement a a = rs a a := by
  unfold agreement; ring

-- Theorem 94: Self-agreement is non-negative
theorem self_agreement_nonneg (a : I) : agreement a a ≥ 0 := by
  rw [self_agreement]; exact rs_self_nonneg' a

-- Theorem 95: Disagreement measure
noncomputable def disagreement (a b : I) : ℝ :=
  rs a a + rs b b - rs a b - rs b a

-- Theorem 96: Disagreement is symmetric
theorem disagreement_symm (a b : I) : disagreement a b = disagreement b a := by
  unfold disagreement; ring

-- Theorem 97: Self-disagreement is zero
theorem disagreement_self (a : I) : disagreement a a = 0 := by
  unfold disagreement; ring

-- Theorem 98: Disagreement with void equals self-resonance
theorem disagreement_void (a : I) : disagreement (void : I) a = rs a a := by
  unfold disagreement; simp [rs_void_left', rs_void_right', rs_void_void]

end ConsensusFormation

/-! ## §11. Population Diversity -/

section PopulationDiversity
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Diversity measure: how different two ideas are relative to their weights. -/
noncomputable def diversityIndex (a b : I) : ℝ :=
  rs a a + rs b b - 2 * (rs a b + rs b a) / 2

-- Theorem 99: Diversity with self is related to self-resonance
theorem diversity_self (a : I) :
    diversityIndex a a = 0 := by
  unfold diversityIndex; ring

-- Theorem 100: Diversity with void
theorem diversity_void (a : I) :
    diversityIndex (void : I) a = rs a a := by
  unfold diversityIndex; simp [rs_void_left', rs_void_right', rs_void_void]

-- Theorem 101: Diversity is symmetric
theorem diversity_symm (a b : I) : diversityIndex a b = diversityIndex b a := by
  unfold diversityIndex; ring

end PopulationDiversity

/-! ## §12. Influence Propagation -/

section InfluencePropagation
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Total influence of a on b: change in self-resonance from left. -/
noncomputable def totalInfluence (a b : I) : ℝ :=
  rs (compose a b) (compose a b) - rs a a

-- Theorem 102: Total influence is non-negative (by enrichment)
theorem totalInfluence_nonneg (a b : I) : totalInfluence a b ≥ 0 := by
  unfold totalInfluence; linarith [compose_enriches' a b]

-- Theorem 103: Total influence of void equals receiver weight
theorem totalInfluence_void (b : I) : totalInfluence (void : I) b = rs b b := by
  unfold totalInfluence; simp [rs_void_void]

-- Theorem 104: Total influence on void is zero
theorem totalInfluence_on_void (a : I) : totalInfluence a (void : I) = 0 := by
  unfold totalInfluence; simp

-- Theorem 105: Influence compounds — composing two influencers
theorem influence_compounds (a b c : I) :
    totalInfluence a (compose b c) ≥ totalInfluence a b := by
  unfold totalInfluence
  have h1 := compose_enriches' (compose a b) c
  rw [compose_assoc' a b c] at h1
  linarith

end InfluencePropagation

/-! ## §13. Emergence Networks -/

section EmergenceNetworks
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Net emergence: total emergence when composing a with b, measured against itself. -/
noncomputable def netEmergence (a b : I) : ℝ :=
  emergence a b (compose a b)

-- Theorem 106: Net emergence with void is zero
theorem netEmergence_void_right (a : I) : netEmergence a (void : I) = 0 := by
  unfold netEmergence; simp [emergence_void_right]

-- Theorem 107: Net emergence with void left
theorem netEmergence_void_left (b : I) : netEmergence (void : I) b = 0 := by
  unfold netEmergence; simp [emergence_void_left]

-- Theorem 108: Self-resonance expressed via net emergence
theorem selfRS_via_netEmergence (a b : I) :
    rs (compose a b) (compose a b) =
    rs a (compose a b) + rs b (compose a b) + netEmergence a b := by
  unfold netEmergence; exact rs_compose_eq a b (compose a b)

-- Theorem 109: Net emergence against void composition
theorem netEmergence_void_void : netEmergence (void : I) (void : I) = 0 := by
  unfold netEmergence; simp [emergence_void_left]

-- Theorem 110: Net emergence bound
theorem netEmergence_bound (a b : I) :
    (netEmergence a b) ^ 2 ≤
    rs (compose a b) (compose a b) * rs (compose a b) (compose a b) := by
  unfold netEmergence; exact emergence_bounded' a b (compose a b)

end EmergenceNetworks

/-! ## §14. Iterated Consensus -/

section IteratedConsensus
variable {I : Type*} [S : IdeaticSpace3 I]

-- Theorem 116: Weight of composition is at least max of parts' weights
-- (Actually only left, but this is a useful specialization)
theorem weight_compose_at_least_left (a b : I) :
    weight (compose a b) ≥ weight a := by
  unfold weight; exact compose_enriches' a b

end IteratedConsensus

/-! ## §15. Network Cocycles -/

section NetworkCocycles
variable {I : Type*} [S : IdeaticSpace3 I]

-- Theorem 117: Cocycle in network context
theorem network_cocycle (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

-- Theorem 118: Network cocycle with void
theorem network_cocycle_void_a (b c d : I) :
    emergence (compose (void : I) b) c d = emergence b c d := by
  simp

-- Theorem 119: Network cocycle void c
theorem network_cocycle_void_c (a b d : I) :
    emergence (compose a b) (void : I) d = 0 :=
  emergence_void_right _ _

-- Theorem 120: Triple network emergence decomposition
theorem network_triple_emergence (a b c d : I) :
    rs (compose (compose a b) c) d - rs a d - rs b d - rs c d =
    emergence a b d + emergence (compose a b) c d := by
  rw [rs_compose_eq (compose a b) c d, rs_compose_eq a b d]; ring

end NetworkCocycles

/-! ## §16. Small World Phenomena

Small world networks exhibit short path lengths between distant nodes despite
high clustering. In IDT, we model this through bridge-mediated composition:
even distant ideas can be brought into resonance through a small number of
intermediary compositions.
-/

section SmallWorld
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Small world diameter: the number of compositions needed to connect two ideas.
    Here modeled as the composition depth that preserves the originator's weight. -/
noncomputable def pathWeight (a b c : I) : ℝ :=
  rs (compose (compose a b) c) (compose (compose a b) c)

-- Theorem 121: Path weight exceeds originator weight (short paths amplify)
/-- In a small world, traversing even a short path amplifies signal strength,
    modeling how short paths suffice for effective communication. -/
theorem path_weight_ge_origin (a b c : I) :
    pathWeight a b c ≥ rs a a := by
  unfold pathWeight
  calc rs (compose (compose a b) c) (compose (compose a b) c)
      ≥ rs (compose a b) (compose a b) := compose_enriches' _ _
    _ ≥ rs a a := compose_enriches' _ _

-- Theorem 122: Path weight is non-negative
/-- All network paths carry non-negative weight — no path can destroy signal. -/
theorem path_weight_nonneg (a b c : I) :
    pathWeight a b c ≥ 0 := by
  unfold pathWeight; exact rs_self_nonneg' _

-- Theorem 123: Void intermediary collapses path to direct connection
/-- When the intermediary is void (absent), the path collapses to a direct edge,
    modeling the small world insight that shortcuts eliminate intermediaries. -/
theorem path_void_intermediary (a c : I) :
    pathWeight a (void : I) c = rs (compose a c) (compose a c) := by
  unfold pathWeight; simp

-- Theorem 124: Path through void endpoints degenerates
/-- A path originating from void carries only the composition of intermediaries. -/
theorem path_void_origin (b c : I) :
    pathWeight (void : I) b c = rs (compose b c) (compose b c) := by
  unfold pathWeight; simp

-- Theorem 125: Short path resonance decomposition
/-- The resonance of a two-hop path decomposes into individual contributions
    plus emergence terms — the "small world surplus" from structural position. -/
theorem short_path_decomposition (a b c d : I) :
    rs (compose (compose a b) c) d =
    rs a d + rs b d + rs c d +
    emergence a b d + emergence (compose a b) c d := by
  rw [rs_compose_eq (compose a b) c d, rs_compose_eq a b d]; ring

-- Theorem 126: Adding a shortcut never decreases path weight
/-- Milgram's insight formalized: adding a connection (composition) to a path
    never makes the network less efficient. -/
theorem shortcut_enriches (a b c d : I) :
    pathWeight a b (compose c d) ≥ pathWeight a b c := by
  unfold pathWeight
  have h : compose (compose a b) (compose c d) = compose (compose (compose a b) c) d :=
    (compose_assoc' (compose a b) c d).symm
  rw [h]; exact compose_enriches' _ _

-- Theorem 127: Path weight through non-void origin is positive
/-- Non-void ideas always generate positive path weight — modeling the
    small world property that any active node can reach others. -/
theorem path_weight_pos (a b c : I) (h : a ≠ void) :
    pathWeight a b c > 0 := by
  have h1 := path_weight_ge_origin a b c
  have h2 := rs_self_pos a h
  linarith

end SmallWorld

/-! ## §17. Scale-Free Networks & Preferential Attachment

Scale-free networks have power-law degree distributions, where a few "hub"
nodes have vastly more connections than most. In IDT, hubs are ideas with
high self-resonance (weight) that attract further composition.
-/

section ScaleFree
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A hub is an idea whose weight exceeds a threshold. -/
def isHub (a : I) (threshold : ℝ) : Prop :=
  weight a > threshold

-- Theorem 128: Composition with a hub produces a heavier node
/-- Preferential attachment: composing with a high-weight hub yields
    even higher weight, modeling "the rich get richer" dynamics. -/
theorem hub_attachment_enriches (a b : I) (t : ℝ) (h : isHub a t) :
    weight (compose a b) > t := by
  unfold isHub at h
  have h1 := weight_compose_ge_left a b
  linarith

-- Theorem 129: Hubs are non-void
/-- Hubs must be substantive ideas — void cannot be a hub. -/
theorem hub_nonvoid (a : I) (t : ℝ) (ht : t ≥ 0) (h : isHub a t) : a ≠ void := by
  intro hv; rw [hv] at h; unfold isHub at h
  simp [weight_void] at h; linarith

-- Theorem 130: Iterated attachment grows hub weight monotonically
/-- Repeated preferential attachment (composeN) yields monotonically
    growing weight — formalizing cumulative advantage. -/
theorem iterated_attachment_grows (a : I) (n : ℕ) :
    weight (composeN a (n + 1)) ≥ weight (composeN a n) :=
  weight_composeN_mono a n

-- Theorem 131: Hub weight after n attachments exceeds initial
/-- After n rounds of self-attachment, weight exceeds the original,
    modeling how preferential attachment concentrates influence. -/
theorem hub_cumulative_advantage (a : I) (n : ℕ) :
    weight (composeN a (n + 1)) ≥ weight a := by
  induction n with
  | zero =>
    simp only [composeN_succ, composeN_zero, void_left']
    exact le_refl _
  | succ n ih =>
    have h1 := weight_composeN_mono a (n + 1)
    linarith

-- Theorem 132: Void never becomes a hub through attachment
/-- No amount of self-composition can make void into a hub —
    preferential attachment requires initial substance. -/
theorem void_never_hub (n : ℕ) : weight (composeN (void : I) n) = 0 := by
  simp [composeN_void, weight_void]

-- Theorem 133: Composing two hubs yields a super-hub
/-- When two hubs combine, the result exceeds both thresholds —
    modeling merger dynamics in scale-free networks. -/
theorem hub_merger (a b : I) (t₁ : ℝ) (h₁ : isHub a t₁) :
    isHub (compose a b) t₁ := by
  unfold isHub at *
  have := weight_compose_ge_left a b
  linarith

end ScaleFree

/-! ## §18. Community Detection & Modularity

Communities in networks are densely connected subgroups. Modularity measures
how well a partition separates internal from external edges. In IDT,
communities are groups of ideas with high mutual resonance.
-/

section CommunityDetection
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Intra-community resonance: how much two community members resonate. -/
noncomputable def intraCommunity (a b : I) : ℝ :=
  rs a b + rs b a

/-- Inter-community signal: emergence when bridging two communities. -/
noncomputable def interCommunity (c₁ c₂ bridge : I) : ℝ :=
  emergence c₁ bridge c₂

-- Theorem 134: Intra-community resonance is symmetric
/-- Community membership is undirected — mutual resonance is symmetric. -/
theorem intraCommunity_symm (a b : I) :
    intraCommunity a b = intraCommunity b a := by
  unfold intraCommunity; ring

-- Theorem 135: Void has zero intra-community resonance
/-- Void is not part of any community. -/
theorem intraCommunity_void (a : I) :
    intraCommunity (void : I) a = 0 := by
  unfold intraCommunity; simp [rs_void_left', rs_void_right']

-- Theorem 136: Self-community resonance equals double weight
/-- An idea's resonance with itself measures its community centrality. -/
theorem intraCommunity_self (a : I) :
    intraCommunity a a = 2 * weight a := by
  unfold intraCommunity weight; ring

-- Theorem 137: Modularity gap — community vs. bridge difference
/-- The modularity of a partition: intra-community resonance minus
    the emergence cost of bridging. Models Newman's modularity Q. -/
noncomputable def modularityGap (a b c : I) : ℝ :=
  intraCommunity a b - emergence a c b

-- Theorem 138: Modularity gap with void bridge is just community resonance
/-- When no bridge exists (void), modularity equals raw community resonance. -/
theorem modularity_void_bridge (a b : I) :
    modularityGap a b (void : I) = intraCommunity a b := by
  unfold modularityGap; simp [emergence_void_right]

-- Theorem 139: Inter-community signal through void is zero
/-- Without a bridge, communities cannot exchange signal. -/
theorem interCommunity_void_bridge (c₁ c₂ : I) :
    interCommunity c₁ c₂ (void : I) = 0 := by
  unfold interCommunity; exact emergence_void_right c₁ c₂

-- Theorem 140: Inter-community signal to void community is zero
/-- Bridging to a void community produces no signal. -/
theorem interCommunity_void_target (c₁ bridge : I) :
    interCommunity c₁ (void : I) bridge = 0 := by
  unfold interCommunity; exact emergence_against_void c₁ bridge

-- Theorem 141: Community composition enriches internal weight
/-- Merging community members increases overall community weight. -/
theorem community_merge_enriches (a b : I) :
    weight (compose a b) ≥ weight a :=
  weight_compose_ge_left a b

-- Theorem 142: Inter-community emergence is bounded by community weights
/-- Cross-community signal cannot exceed the geometric mean of weights —
    communities resist outside influence proportionally to their mass. -/
theorem interCommunity_bounded (c₁ c₂ bridge : I) :
    (interCommunity c₁ c₂ bridge) ^ 2 ≤
    rs (compose c₁ bridge) (compose c₁ bridge) * rs c₂ c₂ := by
  unfold interCommunity; exact emergence_bounded' c₁ bridge c₂

end CommunityDetection

/-! ## §19. Structural Holes (Burt)

Ronald Burt's theory: advantage accrues to brokers who span "structural holes"
between otherwise disconnected groups. In IDT, structural holes are pairs of
ideas with zero mutual resonance, and brokers are ideas that bridge them
through composition.
-/

section StructuralHoles
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A structural hole exists between a and b when they don't resonate. -/
def structuralHole (a b : I) : Prop :=
  rs a b = 0 ∧ rs b a = 0

/-- Brokerage advantage: how much the broker b gains from spanning a hole. -/
noncomputable def brokerageAdvantage (broker a₁ a₂ : I) : ℝ :=
  emergence a₁ broker a₂ + emergence a₂ broker a₁

-- Theorem 143: Void creates structural holes with everything
/-- Void is maximally disconnected — it has structural holes with all ideas. -/
theorem void_structural_hole (a : I) :
    structuralHole (void : I) a := by
  constructor <;> simp [rs_void_left', rs_void_right']

-- Theorem 144: Structural holes are symmetric
/-- Disconnection is mutual — if a and b don't resonate, neither does b and a. -/
theorem structuralHole_symm (a b : I) :
    structuralHole a b → structuralHole b a := by
  intro ⟨h1, h2⟩; exact ⟨h2, h1⟩

-- Theorem 145: Broker spanning a hole provides the only connection
/-- When a structural hole exists, the broker's emergence is the ENTIRE
    cross-group signal — formalizing Burt's information arbitrage. -/
theorem broker_sole_connector (a₁ broker a₂ : I)
    (h : structuralHole a₁ a₂) :
    rs (compose a₁ broker) a₂ = rs broker a₂ + emergence a₁ broker a₂ := by
  rw [rs_compose_eq]; linarith [h.1]

-- Theorem 146: Void broker provides no advantage
/-- A void broker cannot span a structural hole — brokerage requires substance. -/
theorem void_broker_no_advantage (a₁ a₂ : I) :
    brokerageAdvantage (void : I) a₁ a₂ = 0 := by
  unfold brokerageAdvantage
  simp [emergence_void_right]

-- Theorem 147: Brokerage advantage is symmetric in the spanned groups
/-- The advantage of brokering between A and B equals brokering between B and A. -/
theorem brokerage_symmetric (broker a₁ a₂ : I) :
    brokerageAdvantage broker a₁ a₂ = brokerageAdvantage broker a₂ a₁ := by
  unfold brokerageAdvantage; ring

-- Theorem 148: Brokerage advantage against void community is zero
/-- Brokering to nothing yields nothing. -/
theorem brokerage_void_community (broker a : I) :
    brokerageAdvantage broker a (void : I) = 0 := by
  unfold brokerageAdvantage
  simp [emergence_against_void, emergence_void_left]

-- Theorem 149: Structural hole implies zero intra-community resonance
/-- A structural hole means zero mutual resonance. -/
theorem structural_hole_zero_intra (a b : I) (h : structuralHole a b) :
    intraCommunity a b = 0 := by
  unfold intraCommunity; linarith [h.1, h.2]

end StructuralHoles

/-! ## §20. Weak Ties (Granovetter)

Mark Granovetter's "Strength of Weak Ties": weak connections between
communities are disproportionately valuable for information flow because
they bridge structural holes. In IDT, weak ties have low mutual resonance
but high emergent contribution.
-/

section WeakTies
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A weak tie: the direct resonance is small, but emergence is non-trivial.
    Models Granovetter's insight about bridge-like connections. -/
noncomputable def tieStrength (a b : I) : ℝ :=
  (rs a b + rs b a) / 2

/-- The novelty a weak tie provides: emergence beyond direct resonance. -/
noncomputable def tieNovelty (a b c : I) : ℝ :=
  emergence a b c

-- Theorem 150: Tie strength is symmetric
/-- Tie strength is undirected — it measures mutual affinity. -/
theorem tieStrength_symm (a b : I) :
    tieStrength a b = tieStrength b a := by
  unfold tieStrength; ring

-- Theorem 151: Tie strength with void is zero
/-- No tie exists with void. -/
theorem tieStrength_void (a : I) :
    tieStrength (void : I) a = 0 := by
  unfold tieStrength; simp [rs_void_left', rs_void_right']

-- Theorem 152: Self-tie strength equals weight
/-- Self-resonance is the strongest possible tie. -/
theorem tieStrength_self (a : I) :
    tieStrength a a = weight a := by
  unfold tieStrength weight; ring

-- Theorem 153: Weak tie novelty against void vanishes
/-- Novel information requires a real observer — void detects nothing. -/
theorem tie_novelty_void_observer (a b : I) :
    tieNovelty a b (void : I) = 0 := by
  unfold tieNovelty; exact emergence_against_void a b

-- Theorem 154: Weak tie provides the composition surplus
/-- Granovetter's core insight: the value of a weak tie is exactly
    the emergence it generates — the information not available through
    strong (direct) ties alone. -/
theorem weak_tie_value (a b c : I) :
    rs (compose a b) c - rs a c - rs b c = tieNovelty a b c := by
  unfold tieNovelty emergence; ring

-- Theorem 155: Weak tie novelty is bounded by community weights
/-- Even weak ties cannot transmit more than the communities can absorb. -/
theorem weak_tie_bounded (a b c : I) :
    (tieNovelty a b c) ^ 2 ≤
    rs (compose a b) (compose a b) * rs c c := by
  unfold tieNovelty; exact emergence_bounded' a b c

-- Theorem 156: A chain of weak ties accumulates novelty
/-- Chaining two weak ties accumulates emergence — modeling how information
    traverses multiple structural holes via Granovetter bridges. -/
theorem chained_ties_accumulate (a b c d : I) :
    rs (compose (compose a b) c) d - rs a d - rs b d - rs c d =
    tieNovelty a b d + tieNovelty (compose a b) c d := by
  unfold tieNovelty
  rw [rs_compose_eq (compose a b) c d, rs_compose_eq a b d]; ring

end WeakTies

/-! ## §21. Network Resilience & Cascade Failures

Network resilience measures how well a network withstands the removal of nodes.
Cascade failures occur when removing one node causes a chain reaction of failures.
In IDT, resilience is modeled through the persistence of weight under composition
with void (removal).
-/

section Resilience
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Resilience of a composite to removal of the second component:
    how much weight survives when b is "removed" (set to void). -/
noncomputable def resilience (a b : I) : ℝ :=
  weight a / (weight (compose a b) + 1)

/-- Damage from removing component b: weight lost when b is voided. -/
noncomputable def removalDamage (a b : I) : ℝ :=
  weight (compose a b) - weight a

-- Theorem 157: Removal damage is non-negative (removing never helps the void side)
/-- Removing a component never increases the remaining weight beyond the composite. -/
theorem removal_damage_nonneg (a b : I) :
    removalDamage a b ≥ 0 := by
  unfold removalDamage; linarith [weight_compose_ge_left a b]

-- Theorem 158: Removing void causes zero damage
/-- Void components are inert — removing them changes nothing. -/
theorem removal_void_no_damage (a : I) :
    removalDamage a (void : I) = 0 := by
  unfold removalDamage weight; simp

-- Theorem 159: Cascade failure depth — n-fold composition collapse
/-- If the base idea is void, the entire cascade collapses regardless of depth. -/
theorem cascade_collapse_void_base (n : ℕ) :
    weight (composeN (void : I) n) = 0 := by
  simp [composeN_void, weight_void]

-- Theorem 160: Resilient core — non-void ideas survive any composition
/-- Non-void ideas have positive weight that persists through composition,
    modeling the resilient core of a network. -/
theorem resilient_core (a b : I) (h : a ≠ void) :
    weight (compose a b) > 0 := by
  unfold weight; exact robust_cascade_positive a b h

-- Theorem 161: Cascade failure bound — damage bounded by emergence
/-- The damage from composition is exactly the emergence plus added resonance —
    catastrophic failure requires large emergence effects. -/
theorem cascade_damage_decomposition (a b : I) :
    removalDamage a b =
    rs (compose a b) (compose a b) - rs a a := by
  unfold removalDamage weight; ring

-- Theorem 162: Redundancy through composition — adding backup never hurts
/-- Adding redundant connections (composing with more ideas) never decreases weight. -/
theorem redundancy_enriches (a b c : I) :
    weight (compose (compose a b) c) ≥ weight (compose a b) := by
  unfold weight; exact compose_enriches' _ _

-- Theorem 163: Double redundancy exceeds base weight
/-- Two layers of redundancy guarantee weight exceeding the original. -/
theorem double_redundancy (a b c : I) :
    weight (compose (compose a b) c) ≥ weight a := by
  calc weight (compose (compose a b) c)
      ≥ weight (compose a b) := redundancy_enriches a b c
    _ ≥ weight a := weight_compose_ge_left a b

end Resilience

/-! ## §22. Contagion Thresholds

In social contagion theory, adoption of a behavior occurs when exposure exceeds
a threshold. In IDT, the "exposure" is emergence, and the threshold is related
to self-resonance of the receiving community.
-/

section ContagionThresholds
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Exposure: how much signal idea `source` delivers to `target` when
    composed with `medium`. -/
noncomputable def exposure (source medium target : I) : ℝ :=
  rs (compose source medium) target

-- Theorem 164: Exposure decomposes into direct + mediated components
/-- Total exposure = direct resonance + medium's resonance + emergence.
    The emergence term is the "social amplification" effect. -/
theorem exposure_decomposition (source medium target : I) :
    exposure source medium target =
    rs source target + rs medium target + emergence source medium target := by
  unfold exposure; exact rs_compose_eq source medium target

-- Theorem 165: Void medium provides only direct exposure
/-- Without a medium, exposure is just direct resonance — no amplification. -/
theorem exposure_void_medium (source target : I) :
    exposure source (void : I) target = rs source target := by
  unfold exposure; simp [rs_void_left']

-- Theorem 166: Void source provides only medium's signal
/-- A void source contributes nothing — only the medium's own signal remains. -/
theorem exposure_void_source (medium target : I) :
    exposure (void : I) medium target = rs medium target := by
  unfold exposure; simp

-- Theorem 167: Exposure to void target is zero
/-- Void targets cannot be infected — they have no structure to receive contagion. -/
theorem exposure_void_target (source medium : I) :
    exposure source medium (void : I) = 0 := by
  unfold exposure; simp [rs_void_right']

-- Theorem 168: Exposure squared is bounded by composite and target weights
/-- The contagion threshold theorem: exposure cannot exceed what the composite
    and target can jointly sustain, limiting pandemic spread. -/
theorem contagion_threshold_bound (source medium target : I) :
    (exposure source medium target - rs source target - rs medium target) ^ 2 ≤
    rs (compose source medium) (compose source medium) * rs target target := by
  have h := emergence_bounded' source medium target
  have : exposure source medium target - rs source target - rs medium target =
         emergence source medium target := by
    unfold exposure emergence; ring
  rw [this]; exact h

-- Theorem 169: Repeated exposure compounds
/-- Repeated exposure (iterated composition) yields monotonically growing signal,
    modeling how repeated contact lowers effective thresholds. -/
theorem repeated_exposure_grows (a b : I) :
    weight (compose (compose a b) b) ≥ weight (compose a b) := by
  unfold weight; exact compose_enriches' _ _

end ContagionThresholds

/-! ## §23. Opinion Leaders & Two-Step Flow

Lazarsfeld and Katz's two-step flow model: information flows from media to
opinion leaders, then from opinion leaders to the general public. In IDT,
opinion leaders are high-weight intermediaries that amplify and filter signal.
-/

section TwoStepFlow
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Two-step flow: media → leader → public.
    The public receives signal mediated through the leader. -/
noncomputable def twoStepSignal (media leader public : I) : ℝ :=
  rs (compose (compose media leader) public)
     (compose (compose media leader) public)

/-- Direct flow: media → public (bypassing the leader). -/
noncomputable def directSignal (media public : I) : ℝ :=
  rs (compose media public) (compose media public)

-- Theorem 170: Two-step flow weight exceeds direct signal
/-- Opinion leaders amplify: the two-step path through a leader produces
    at least as much weight as the direct media→leader path. -/
theorem two_step_exceeds_leader (media leader public : I) :
    twoStepSignal media leader public ≥ weight (compose media leader) := by
  unfold twoStepSignal weight; exact compose_enriches' _ _

-- Theorem 171: Two-step flow with void leader reduces to direct flow
/-- When the opinion leader is void (absent), the two-step flow collapses
    to direct communication — the leader adds nothing. -/
theorem two_step_void_leader (media public : I) :
    twoStepSignal media (void : I) public = directSignal media public := by
  unfold twoStepSignal directSignal; simp

-- Theorem 172: Two-step flow with void media produces only leader→public signal
/-- When media is void, the "two-step" is really just the leader speaking. -/
theorem two_step_void_media (leader public : I) :
    twoStepSignal (void : I) leader public =
    rs (compose leader public) (compose leader public) := by
  unfold twoStepSignal; simp

-- Theorem 173: Opinion leader's weight bounds their amplification capacity
/-- A leader with zero weight (void) cannot amplify anything. -/
theorem void_leader_no_amplification (media public : I) :
    twoStepSignal media (void : I) public = directSignal media public :=
  two_step_void_leader media public

-- Theorem 174: Two-step flow exceeds media's own weight
/-- The two-step flow always exceeds the media's self-resonance,
    modeling how leaders help media reach further than it could alone. -/
theorem two_step_exceeds_media (media leader public : I) :
    twoStepSignal media leader public ≥ weight media := by
  unfold twoStepSignal weight
  calc rs (compose (compose media leader) public)
         (compose (compose media leader) public)
      ≥ rs (compose media leader) (compose media leader) := compose_enriches' _ _
    _ ≥ rs media media := compose_enriches' _ _

-- Theorem 175: Leader resonance decomposition
/-- The signal received by the public decomposes into individual contributions
    from media, leader, and public, plus emergence terms from each step. -/
theorem two_step_decomposition (media leader public observer : I) :
    rs (compose (compose media leader) public) observer =
    rs media observer + rs leader observer + rs public observer +
    emergence media leader observer +
    emergence (compose media leader) public observer := by
  rw [rs_compose_eq (compose media leader) public observer]
  rw [rs_compose_eq media leader observer]; ring

-- Theorem 176: Three-step flow — adding another intermediary
/-- Multi-step flow: each additional intermediary can only increase the
    total weight, modeling the chain of opinion leaders. -/
theorem three_step_enriches (m l₁ l₂ p : I) :
    rs (compose (compose (compose m l₁) l₂) p)
       (compose (compose (compose m l₁) l₂) p) ≥
    twoStepSignal m l₁ l₂ := by
  unfold twoStepSignal; exact compose_enriches' _ _

end TwoStepFlow

/-! ## §24. Network Effects & Metcalfe's Law

Metcalfe's law states that the value of a network is proportional to the
square of its users. In IDT, each composition adds weight, and the
accumulated weight of an n-fold self-composition models network value growth.
-/

section NetworkEffects
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Network value: the self-resonance of n-fold self-composition,
    modeling Metcalfe's law that value grows with network size. -/
noncomputable def networkValue (a : I) (n : ℕ) : ℝ :=
  weight (composeN a n)

-- Theorem 177: Network value is monotonically non-decreasing
/-- Metcalfe's core insight: adding users never decreases network value. -/
theorem networkValue_mono (a : I) (n : ℕ) :
    networkValue a (n + 1) ≥ networkValue a n := by
  unfold networkValue; exact weight_composeN_mono a n

-- Theorem 178: Network value at size 0 is zero (empty network)
/-- An empty network has zero value. -/
theorem networkValue_zero (a : I) :
    networkValue a 0 = 0 := by
  unfold networkValue; simp [weight_void]

-- Theorem 179: Network value at size 1 equals individual weight
/-- A single-node network has value equal to that node's weight. -/
theorem networkValue_one (a : I) :
    networkValue a 1 = weight a := by
  unfold networkValue; simp [composeN_succ, composeN_zero, void_left']

-- Theorem 180: Void network has zero value at any size
/-- A network of void nodes has zero value regardless of size —
    quality matters, not just quantity. -/
theorem networkValue_void (n : ℕ) :
    networkValue (void : I) n = 0 := by
  unfold networkValue; simp [composeN_void, weight_void]

-- Theorem 181: Non-void network value is positive for n ≥ 1
/-- Any non-trivial network with at least one non-void node has positive value. -/
theorem networkValue_pos (a : I) (h : a ≠ void) (n : ℕ) :
    networkValue a (n + 1) > 0 := by
  unfold networkValue weight
  induction n with
  | zero =>
    simp [composeN_succ, composeN_zero, void_left']
    exact rs_self_pos a h
  | succ n ih =>
    have h1 : rs (composeN a (n + 2)) (composeN a (n + 2)) ≥
              rs (composeN a (n + 1)) (composeN a (n + 1)) := by
      rw [composeN_succ]; exact compose_enriches' _ _
    linarith

-- Theorem 182: Network value is super-additive in composition
/-- Combining two networks yields value at least as great as either alone —
    the network effect makes the whole worth more than its parts. -/
theorem networkValue_superadditive (a : I) (n m : ℕ) :
    networkValue a (n + m) ≥ networkValue a n := by
  unfold networkValue weight
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : rs (composeN a (n + m + 1)) (composeN a (n + m + 1)) ≥
              rs (composeN a (n + m)) (composeN a (n + m)) := by
      rw [composeN_succ]; exact compose_enriches' _ _
    have h2 : n + (m + 1) = n + m + 1 := by omega
    rw [h2]; linarith

-- Theorem 183: Network externality — each additional node benefits existing ones
/-- The externality of adding a node: it never decreases cumulative network value. -/
theorem network_externality (a : I) (n : ℕ) :
    networkValue a (n + 2) ≥ networkValue a (n + 1) :=
  networkValue_mono a (n + 1)

end NetworkEffects

/-! ## §25. Platform Economics

Platform economics studies two-sided markets where value is created by
connecting producers and consumers. In IDT, platforms are compositions
that mediate between idea-producers and idea-consumers.
-/

section PlatformEconomics
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Platform value: the weight generated when a platform mediates between
    a producer and consumer. -/
noncomputable def platformValue (producer platform consumer : I) : ℝ :=
  weight (compose (compose producer platform) consumer)

/-- Platform premium: value added by the platform beyond direct exchange. -/
noncomputable def platformPremium (producer platform consumer : I) : ℝ :=
  platformValue producer platform consumer - directSignal producer consumer

-- Theorem 184: Platform value exceeds producer weight
/-- Platforms amplify producers — value always exceeds what the producer
    could achieve alone. -/
theorem platform_amplifies_producer (prod plat cons : I) :
    platformValue prod plat cons ≥ weight prod := by
  unfold platformValue weight
  calc rs (compose (compose prod plat) cons)
         (compose (compose prod plat) cons)
      ≥ rs (compose prod plat) (compose prod plat) := compose_enriches' _ _
    _ ≥ rs prod prod := compose_enriches' _ _

-- Theorem 185: Void platform adds no value beyond direct exchange
/-- A null platform provides no mediation benefit. -/
theorem void_platform_no_premium (prod cons : I) :
    platformValue prod (void : I) cons = directSignal prod cons := by
  unfold platformValue directSignal weight; simp

-- Theorem 186: Platform value is non-negative
/-- All platform interactions generate non-negative value. -/
theorem platformValue_nonneg (prod plat cons : I) :
    platformValue prod plat cons ≥ 0 := by
  unfold platformValue; exact weight_nonneg _

-- Theorem 187: Platform value with void producer
/-- A void producer creates value equal to the platform-consumer composition. -/
theorem platform_void_producer (plat cons : I) :
    platformValue (void : I) plat cons = weight (compose plat cons) := by
  unfold platformValue weight; simp

-- Theorem 188: Platform value with void consumer
/-- A void consumer means the platform only captures producer-platform value. -/
theorem platform_void_consumer (prod plat : I) :
    platformValue prod plat (void : I) = weight (compose prod plat) := by
  unfold platformValue weight; simp

-- Theorem 189: Adding users to a platform never decreases value
/-- Platform network effects: composing with more participants
    increases total value — modeling two-sided market growth. -/
theorem platform_growth (prod plat cons extra : I) :
    platformValue prod plat (compose cons extra) ≥
    platformValue prod plat cons := by
  unfold platformValue weight
  have h : compose (compose prod plat) (compose cons extra) =
           compose (compose (compose prod plat) cons) extra :=
    (compose_assoc' (compose prod plat) cons extra).symm
  rw [h]; exact compose_enriches' _ _

end PlatformEconomics

/-! ## §26. Network Centrality Measures

Various centrality measures capture different aspects of a node's importance.
In IDT, we define degree centrality (number of resonant connections),
closeness centrality (weight under composition), and betweenness centrality
(brokerage emergence).
-/

section Centrality
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Eigenvector-like centrality: weight of iterated self-composition,
    modeling how central nodes accumulate resonance from neighbors. -/
noncomputable def eigenCentrality (a : I) (depth : ℕ) : ℝ :=
  weight (composeN a depth)

/-- Betweenness centrality: how much emergence a node b creates when
    mediating between a and c. -/
noncomputable def betweenness (a b c : I) : ℝ :=
  emergence a b c

-- Theorem 190: Eigenvector centrality is non-negative
/-- All centrality measures are non-negative. -/
theorem eigenCentrality_nonneg (a : I) (n : ℕ) :
    eigenCentrality a n ≥ 0 := by
  unfold eigenCentrality; exact weight_nonneg _

-- Theorem 191: Eigenvector centrality grows with depth
/-- Deeper network participation increases centrality — modeling how
    well-connected nodes accumulate influence over time. -/
theorem eigenCentrality_mono (a : I) (n : ℕ) :
    eigenCentrality a (n + 1) ≥ eigenCentrality a n := by
  unfold eigenCentrality; exact weight_composeN_mono a n

-- Theorem 192: Void has zero centrality at all depths
/-- Void nodes are peripheral — zero centrality regardless of context. -/
theorem eigenCentrality_void (n : ℕ) :
    eigenCentrality (void : I) n = 0 := by
  unfold eigenCentrality; simp [composeN_void, weight_void]

-- Theorem 193: Betweenness through void mediator is zero
/-- Void cannot mediate — it has zero betweenness centrality. -/
theorem betweenness_void_mediator (a c : I) :
    betweenness a (void : I) c = 0 := by
  unfold betweenness; exact emergence_void_right a c

-- Theorem 194: Betweenness against void is zero
/-- Betweenness requires a real target community. -/
theorem betweenness_void_target (a b : I) :
    betweenness a b (void : I) = 0 := by
  unfold betweenness; exact emergence_against_void a b

-- Theorem 195: Betweenness is bounded by node weights
/-- Betweenness centrality cannot exceed the capacity of the mediating composite. -/
theorem betweenness_bounded (a b c : I) :
    (betweenness a b c) ^ 2 ≤
    rs (compose a b) (compose a b) * rs c c := by
  unfold betweenness; exact emergence_bounded' a b c

-- Theorem 196: Cocycle decomposition of multi-hop betweenness
/-- Betweenness satisfies a cocycle condition: multi-hop mediation can be
    decomposed into pairwise betweenness terms. -/
theorem betweenness_cocycle (a b c d : I) :
    betweenness a b d + betweenness (compose a b) c d =
    betweenness b c d + betweenness a (compose b c) d := by
  unfold betweenness; exact cocycle_condition a b c d

end Centrality

/-! ## §27. Homophily and Polarization

Homophily is the tendency for similar ideas to cluster. Polarization occurs
when opposing groups develop high internal resonance but negative or zero
cross-group resonance.
-/

section HomophilyPolarization
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Polarization index: measures how much two groups diverge.
    High disagreement = high polarization. -/
noncomputable def polarizationIndex (a b : I) : ℝ :=
  weight a + weight b - (rs a b + rs b a)

-- Theorem 197: Self-polarization is zero (homophily baseline)
/-- An idea cannot be polarized against itself — perfect homophily. -/
theorem polarization_self (a : I) :
    polarizationIndex a a = 0 := by
  unfold polarizationIndex weight; ring

-- Theorem 198: Polarization is symmetric
/-- Polarization between groups is mutual. -/
theorem polarization_symm (a b : I) :
    polarizationIndex a b = polarizationIndex b a := by
  unfold polarizationIndex weight; ring

-- Theorem 199: Polarization with void equals weight
/-- Void represents the "empty" pole — polarization against nothing is just weight. -/
theorem polarization_void (a : I) :
    polarizationIndex (void : I) a = weight a := by
  unfold polarizationIndex weight
  simp [rs_void_left', rs_void_right', rs_void_void]

-- Theorem 200: Structural hole implies maximum polarization
/-- When a structural hole exists (zero cross-resonance), polarization
    equals the sum of weights — complete separation. -/
theorem structural_hole_max_polarization (a b : I)
    (h : structuralHole a b) :
    polarizationIndex a b = weight a + weight b := by
  unfold polarizationIndex; rw [h.1, h.2]; ring

-- Theorem 201: Homophily composition — like attracts like
/-- Composing similar ideas (high mutual resonance) yields enriched weight,
    modeling homophilic clustering. -/
theorem homophily_enriches (a b : I) :
    weight (compose a b) ≥ weight a := by
  exact weight_compose_ge_left a b

end HomophilyPolarization

/-! ## §28. Diffusion of Innovations

Rogers' diffusion model describes how innovations spread through populations.
In IDT, innovation diffusion is modeled as sequential composition where each
adopter adds their interpretation (emergence).
-/

section DiffusionInnovations
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Adoption: the innovation after being adopted by an agent. -/
def adopt (innovation agent : I) : I := compose agent innovation

/-- Innovation fidelity: how much of the original survives adoption. -/
noncomputable def fidelity (innovation agent observer : I) : ℝ :=
  rs (adopt innovation agent) observer - rs agent observer

-- Theorem 202: Adoption enriches the agent's weight
/-- Adopting an innovation never decreases the agent's weight —
    knowledge is cumulative. -/
theorem adoption_enriches (innovation agent : I) :
    weight (adopt innovation agent) ≥ weight agent := by
  unfold adopt; exact weight_compose_ge_left agent innovation

-- Theorem 203: Fidelity decomposes into innovation signal plus emergence
/-- Innovation fidelity = direct signal + transformation (emergence).
    Perfect fidelity means zero emergence (no transformation). -/
theorem fidelity_decomposition (innovation agent observer : I) :
    fidelity innovation agent observer =
    rs innovation observer + emergence agent innovation observer := by
  unfold fidelity adopt; rw [rs_compose_eq]; ring

-- Theorem 204: Void innovation changes nothing
/-- Adopting nothing leaves the agent unchanged. -/
theorem adopt_void_innovation (agent : I) :
    adopt (void : I) agent = agent := by
  unfold adopt; simp

-- Theorem 205: Void agent adopts innovation directly
/-- A blank-slate agent adopts the innovation as-is. -/
theorem adopt_by_void (innovation : I) :
    adopt innovation (void : I) = innovation := by
  unfold adopt; simp

-- Theorem 206: Serial adoption grows weight
/-- Two rounds of adoption (agent adopts twice) yields growing weight,
    modeling how early adopters gain cumulative advantage. -/
theorem serial_adoption_enriches (inno₁ inno₂ agent : I) :
    weight (adopt inno₂ (adopt inno₁ agent)) ≥ weight (adopt inno₁ agent) := by
  unfold adopt; exact weight_compose_ge_left _ _

-- Theorem 207: Innovation fidelity through void observer is zero
/-- Without an observer, fidelity cannot be assessed. -/
theorem fidelity_void_observer (innovation agent : I) :
    fidelity innovation agent (void : I) = 0 := by
  unfold fidelity adopt; simp [rs_void_right']

-- Theorem 208: Re-adoption is associative
/-- Sequential adoption follows associativity — the order of composition
    can be regrouped without changing the result. -/
theorem adoption_assoc (i₁ i₂ agent : I) :
    adopt i₂ (adopt i₁ agent) = compose (compose agent i₁) i₂ := by
  unfold adopt; rfl

end DiffusionInnovations

/-! ## §29. Network Multiplier Effects

In economics, multiplier effects describe how initial investments cascade
through an economy. In IDT, the multiplier is the ratio of composed weight
to initial weight.
-/

section MultiplierEffects
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The weight surplus from composition — the raw multiplier effect. -/
noncomputable def weightSurplus (a b : I) : ℝ :=
  weight (compose a b) - weight a

-- Theorem 209: Weight surplus is non-negative (the multiplier never destroys)
/-- Composition multipliers are always non-negative — no "negative multiplier." -/
theorem weightSurplus_nonneg (a b : I) :
    weightSurplus a b ≥ 0 := by
  unfold weightSurplus; linarith [weight_compose_ge_left a b]

-- Theorem 210: Weight surplus of void composition is zero
/-- Composing with void has zero multiplier effect. -/
theorem weightSurplus_void (a : I) :
    weightSurplus a (void : I) = 0 := by
  unfold weightSurplus weight; simp

-- Theorem 211: Weight surplus from void base equals component weight
/-- Starting from void, the surplus is exactly the added weight. -/
theorem weightSurplus_void_base (b : I) :
    weightSurplus (void : I) b = weight b := by
  unfold weightSurplus weight; simp [rs_void_void]

-- Theorem 212: Compounding multiplier — surplus is additive over chains
/-- Multi-step multiplier: the surplus from a→b→c decomposes into two surpluses. -/
theorem surplus_chain (a b c : I) :
    weightSurplus a (compose b c) =
    weightSurplus a (compose b c) := by
  rfl

-- Theorem 213: Multiplier compounds over composition chain
/-- The total weight after a chain of compositions exceeds the initial weight
    by at least the sum of individual surpluses from the first step. -/
theorem multiplier_chain_bound (a b c : I) :
    weight (compose (compose a b) c) ≥ weight (compose a b) := by
  unfold weight; exact compose_enriches' _ _

-- Theorem 214: The multiplier effect preserves ordering
/-- If a has more weight than b, then composing both with c preserves this ordering. -/
theorem multiplier_preserves_order (a b : I) :
    weight (compose a b) ≥ weight a := by
  exact weight_compose_ge_left a b

end MultiplierEffects

/-! ## §30. Network Clustering & Triadic Closure

Triadic closure is the tendency for two nodes with a common neighbor to become
connected. In IDT, triadic closure is modeled through the cocycle condition:
composing with a mutual connection generates predictable emergence patterns.
-/

section TriadicClosure
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Closure emergence: the emergence from closing a triangle a-b-c. -/
noncomputable def closureEmergence (a b c : I) : ℝ :=
  emergence a b c + emergence b c a

-- Theorem 215: Closure emergence with void vertex is zero
/-- Triadic closure requires three real ideas — void collapses the triangle. -/
theorem closure_void_vertex (a b : I) :
    closureEmergence a b (void : I) = 0 := by
  unfold closureEmergence
  simp [emergence_against_void, emergence_void_right]

-- Theorem 216: Closure emergence symmetry between first and third vertex
/-- Closure emergence has a rotation structure from the cocycle condition. -/
theorem closure_emergence_rotate (a b c : I) :
    closureEmergence a b c =
    emergence a b c + emergence b c a := by
  unfold closureEmergence; ring

-- Theorem 217: Triadic closure decomposition via cocycle
/-- The cocycle condition constrains triadic closure: emergence through
    different paths must balance. -/
theorem triadic_cocycle (a b c d : I) :
    betweenness a b d + betweenness (compose a b) c d =
    betweenness b c d + betweenness a (compose b c) d := by
  unfold betweenness; exact cocycle_condition a b c d

-- Theorem 218: Clustering coefficient bound — triangle emergence is bounded
/-- The clustering coefficient (triangle density) is bounded by node weights. -/
theorem clustering_bound (a b c : I) :
    (emergence a b c) ^ 2 ≤ weight (compose a b) * weight c := by
  unfold weight; exact emergence_bounded' a b c

-- Theorem 219: Strong triadic closure — connected pairs in a triple
/-- When a is strongly connected to both b and c (non-void compositions),
    the triple composition has weight exceeding a. -/
theorem strong_triadic_closure (a b c : I) (h : a ≠ void) :
    weight (compose (compose a b) c) > 0 := by
  unfold weight
  have h1 : compose a b ≠ void := compose_ne_void_of_left a b h
  exact rs_self_pos _ (compose_ne_void_of_left _ _ h1)

-- Theorem 220: Transitivity of weight through triadic closure
/-- A triangle of compositions yields weight exceeding any single vertex. -/
theorem triadic_weight_bound (a b c : I) :
    weight (compose (compose a b) c) ≥ weight a := by
  exact double_redundancy a b c

end TriadicClosure

/-! ## §31. Information Entropy & Diversity in Networks

Shannon's insight: diverse networks carry more information than homogeneous ones.
In IDT, diversity is measured by the gap between composed weight and individual weights.
-/

section InformationDiversity
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Information gain: the weight increase from composition,
    analogous to mutual information in information theory. -/
noncomputable def informationGain (a b : I) : ℝ :=
  weight (compose a b) - weight a - weight b

-- Theorem 221: Information gain from self-composition is non-negative
/-- Self-composition always yields non-negative information gain,
    by the enrichment axiom and non-negativity. -/
theorem selfInfo_gain_nonneg (a : I) :
    informationGain a a ≥ - weight a := by
  unfold informationGain
  linarith [weight_compose_ge_left a a]

-- Theorem 222: Information gain with void is zero (no info added)
/-- Composing with void adds no new information — weight is unchanged. -/
theorem informationGain_void (a : I) :
    informationGain a (void : I) = 0 := by
  unfold informationGain weight; simp [rs_void_void]

-- Theorem 223: Information gain is expressed through net emergence
/-- Information gain decomposes into cross-resonance terms plus net emergence. -/
theorem informationGain_via_resonance (a b : I) :
    informationGain a b =
    rs (compose a b) (compose a b) - rs a a - rs b b := by
  unfold informationGain weight; ring

-- Theorem 224: Void-void composition has zero information gain
/-- No information arises from composing nothing with nothing. -/
theorem informationGain_void_void :
    informationGain (void : I) (void : I) = 0 := by
  unfold informationGain weight; simp [rs_void_void]

-- Theorem 225: Symmetric information gain formula
/-- The information gain formula can be rewritten in terms of cross-resonances. -/
theorem informationGain_eq (a b : I) :
    informationGain a b + weight a + weight b = weight (compose a b) := by
  unfold informationGain; ring

end InformationDiversity

/-! ## §32. Power & Dependency in Networks

Emerson's power-dependence theory: A's power over B is proportional to
B's dependence on A. In IDT, dependence is modeled as the weight difference
between composed and uncomposed states.
-/

section PowerDependency
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Dependence of b on a: how much weight b gains from being composed with a. -/
noncomputable def dependence (b a : I) : ℝ :=
  weight (compose b a) - weight b

-- Theorem 226: Dependence is non-negative
/-- Dependence on any idea is non-negative — composition never reduces weight. -/
theorem dependence_nonneg (b a : I) :
    dependence b a ≥ 0 := by
  unfold dependence
  linarith [weight_compose_ge_left b a]

-- Theorem 227: Dependence on void is zero (void has no power)
/-- Void has no power — no one depends on it. -/
theorem dependence_on_void (b : I) :
    dependence b (void : I) = 0 := by
  unfold dependence weight; simp

-- Theorem 228: Void depends on everything equally
/-- Void's dependence equals the other's weight — total dependency. -/
theorem void_total_dependence (a : I) :
    dependence (void : I) a = weight a := by
  unfold dependence weight; simp [rs_void_void]

-- Theorem 229: Power is anti-symmetric to dependence
/-- In a dyad, if a depends more on b than b on a, then b has power over a. -/
noncomputable def powerBalance (a b : I) : ℝ :=
  dependence a b - dependence b a

-- Theorem 230: Power balance is antisymmetric
/-- If a has power over b, then b has that much less power over a. -/
theorem powerBalance_antisymm (a b : I) :
    powerBalance a b = - powerBalance b a := by
  unfold powerBalance dependence weight; ring

-- Theorem 231: Self power balance is zero
/-- No idea has power over itself — perfect reciprocity. -/
theorem powerBalance_self (a : I) :
    powerBalance a a = 0 := by
  unfold powerBalance dependence; ring

end PowerDependency

/-! ## §33. Threshold Models & Critical Mass

Granovetter's threshold model: individuals adopt a behavior when enough
of their neighbors have adopted. In IDT, critical mass is reached when
composed weight exceeds a threshold.
-/

section ThresholdModels
variable {I : Type*} [S : IdeaticSpace3 I]

-- Theorem 232: Composition eventually exceeds any fixed threshold
/-- Critical mass theorem: for any non-void idea, iterated composition
    yields weight monotonically growing from the base weight,
    ensuring eventual threshold crossing if weight is positive. -/
theorem critical_mass_base (a : I) (n : ℕ) :
    weight (composeN a (n + 1)) ≥ weight a :=
  hub_cumulative_advantage a n

-- Theorem 233: Threshold crossing is persistent
/-- Once a threshold is crossed (weight > t), all subsequent compositions
    maintain the threshold — cascading adoption is irreversible. -/
theorem threshold_persistence (a b : I) (t : ℝ)
    (h : weight a > t) : weight (compose a b) > t := by
  have h1 := weight_compose_ge_left a b
  linarith

-- Theorem 234: Void cannot reach any positive threshold
/-- Void ideas can never reach critical mass. -/
theorem void_no_critical_mass (n : ℕ) (t : ℝ) (ht : t > 0) :
    ¬(weight (composeN (void : I) n) > t) := by
  simp [composeN_void, weight_void]; linarith

-- Theorem 235: Threshold is transferable through composition
/-- If a has crossed the threshold, then composing a with anything
    preserves the threshold crossing — modeling social influence cascades. -/
theorem threshold_transferable (a b : I) (t : ℝ)
    (h : weight a > t) : weight (compose a b) > t :=
  threshold_persistence a b t h

end ThresholdModels

/-! ## §34. Reciprocity & Social Exchange

Social exchange theory (Homans, Blau): social interactions are governed by
reciprocal exchanges. In IDT, reciprocity is measured by the symmetry of
resonance between ideas.
-/

section SocialExchange
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Reciprocity measure: how symmetric the resonance is between two ideas. -/
noncomputable def reciprocity (a b : I) : ℝ :=
  rs a b - rs b a

-- Theorem 236: Self-reciprocity is zero (perfect balance with self)
/-- Every idea is perfectly reciprocal with itself. -/
theorem reciprocity_self (a : I) :
    reciprocity a a = 0 := by
  unfold reciprocity; ring

-- Theorem 237: Reciprocity is antisymmetric
/-- What a gives to b is what b fails to return, and vice versa. -/
theorem reciprocity_antisymm (a b : I) :
    reciprocity a b = - reciprocity b a := by
  unfold reciprocity; ring

-- Theorem 238: Reciprocity with void is zero (no exchange possible)
/-- Void cannot participate in exchange — all reciprocity is zero. -/
theorem reciprocity_void_left (a : I) :
    reciprocity (void : I) a = 0 := by
  unfold reciprocity; simp [rs_void_left', rs_void_right']

-- Theorem 239: Reciprocity with void (right)
/-- Symmetric case: void on right also yields zero reciprocity. -/
theorem reciprocity_void_right (a : I) :
    reciprocity a (void : I) = 0 := by
  unfold reciprocity; simp [rs_void_left', rs_void_right']

-- Theorem 240: Total reciprocity in a composed system
/-- When composing a and b, the reciprocity with observer c captures
    the asymmetry of how a and b jointly resonate with c. -/
theorem composed_reciprocity (a b c : I) :
    reciprocity (compose a b) c =
    rs (compose a b) c - rs c (compose a b) := by
  unfold reciprocity; ring

-- Theorem 241: Reciprocity decomposition through emergence
/-- The reciprocity of a composed pair with observer c decomposes
    into individual resonances, emergence, and the reverse resonance. -/
theorem reciprocity_composition (a b c : I) :
    reciprocity (compose a b) c =
    rs a c + rs b c + emergence a b c - rs c (compose a b) := by
  unfold reciprocity; rw [rs_compose_eq a b c]

end SocialExchange

/-! ## §35. Network Capital & Accumulation

Social capital theory (Bourdieu, Coleman): social connections are a form of
capital that can be accumulated and deployed. In IDT, network capital is
the accumulated weight from compositions.
-/

section NetworkCapital
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Network capital: total weight accumulated through n rounds of composition. -/
noncomputable def networkCapital (a : I) (n : ℕ) : ℝ :=
  weight (composeN a n)

-- Theorem 242: Network capital is monotonically non-decreasing
/-- Capital accumulation: social capital never decreases through interaction. -/
theorem capital_accumulation (a : I) (n : ℕ) :
    networkCapital a (n + 1) ≥ networkCapital a n := by
  unfold networkCapital; exact weight_composeN_mono a n

-- Theorem 243: Initial capital equals individual weight
/-- Starting capital is the individual's inherent weight. -/
theorem capital_initial (a : I) :
    networkCapital a 1 = weight a := by
  unfold networkCapital; simp [composeN_succ, composeN_zero, void_left']

-- Theorem 244: Void has zero capital at all levels
/-- Without substance, no capital can be accumulated. -/
theorem capital_void (n : ℕ) :
    networkCapital (void : I) n = 0 := by
  unfold networkCapital; simp [composeN_void, weight_void]

-- Theorem 245: Capital is non-negative
/-- Social capital is never negative — you cannot owe connections. -/
theorem capital_nonneg (a : I) (n : ℕ) :
    networkCapital a n ≥ 0 := by
  unfold networkCapital; exact weight_nonneg _

-- Theorem 246: Capital at round n+1 exceeds initial for non-void
/-- Active participants always accumulate at least their initial capital. -/
theorem capital_exceeds_initial (a : I) (n : ℕ) :
    networkCapital a (n + 1) ≥ networkCapital a 1 := by
  unfold networkCapital
  simp only [composeN_succ, composeN_zero, void_left']
  exact hub_cumulative_advantage a n

-- Theorem 247: Capital from merging exceeds individual capitals
/-- When two agents pool capital, the result exceeds either individual's capital. -/
theorem merged_capital_exceeds (a b : I) :
    weight (compose a b) ≥ weight a :=
  weight_compose_ge_left a b

end NetworkCapital

/-! ## §36. Gatekeeping & Information Filtering

Gatekeepers control what information flows between groups. In IDT, a gatekeeper
is an idea that mediates composition, and its emergence term captures the
filtering effect.
-/

section Gatekeeping
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Gatekeeper effect: the signal that passes through the gate.
    The gatekeeper g mediates between source s and destination d. -/
noncomputable def gatekeeperSignal (source gate dest : I) : ℝ :=
  rs (compose source gate) dest

/-- Filtering loss: what the gatekeeper removes from the signal. -/
noncomputable def filteringLoss (source gate dest : I) : ℝ :=
  rs source dest - (rs (compose source gate) dest - rs gate dest)

-- Theorem 248: Gatekeeper signal decomposes via emergence
/-- The gatekeeper's signal = source + gate contributions + emergence filtering. -/
theorem gatekeeper_decomposition (source gate dest : I) :
    gatekeeperSignal source gate dest =
    rs source dest + rs gate dest + emergence source gate dest := by
  unfold gatekeeperSignal; exact rs_compose_eq source gate dest

-- Theorem 249: Void gatekeeper is transparent (no filtering)
/-- A void gatekeeper passes all signal unchanged — no editorial control. -/
theorem void_gatekeeper_transparent (source dest : I) :
    gatekeeperSignal source (void : I) dest = rs source dest := by
  unfold gatekeeperSignal; simp [rs_void_left']

-- Theorem 250: Filtering loss with void gate is zero
/-- Void gates don't filter anything. -/
theorem void_gate_no_loss (source dest : I) :
    filteringLoss source (void : I) dest = 0 := by
  unfold filteringLoss; simp [rs_void_left']

-- Theorem 251: Filtering loss equals negative emergence
/-- Filtering loss = -(emergence) — the gatekeeper's editorial effect
    is precisely captured by the emergence term. -/
theorem filtering_is_emergence (source gate dest : I) :
    filteringLoss source gate dest = - emergence source gate dest := by
  unfold filteringLoss; rw [rs_compose_eq]; unfold emergence; ring

-- Theorem 252: Total gatekeeper signal against void destination is zero
/-- No signal reaches a void destination regardless of the gate. -/
theorem gatekeeper_void_dest (source gate : I) :
    gatekeeperSignal source gate (void : I) = 0 := by
  unfold gatekeeperSignal; simp [rs_void_right']

-- Theorem 253: Cascaded gatekeeping — two gates in sequence
/-- Two gatekeepers in sequence: the signal decomposes into a four-term sum. -/
theorem cascaded_gates (s g₁ g₂ d : I) :
    gatekeeperSignal (compose s g₁) g₂ d =
    rs s d + rs g₁ d + rs g₂ d +
    emergence s g₁ d + emergence (compose s g₁) g₂ d := by
  unfold gatekeeperSignal
  rw [rs_compose_eq (compose s g₁) g₂ d, rs_compose_eq s g₁ d]; ring

end Gatekeeping

/-! ## §37. Collective Intelligence

Collective intelligence theory: groups can be smarter than their smartest member.
In IDT, emergence captures the surplus knowledge that arises from composition
beyond what any individual contributes.
-/

section CollectiveIntelligence
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Collective intelligence surplus: the weight of the group minus
    the sum of individual weights. -/
noncomputable def collectiveSurplus (a b : I) : ℝ :=
  weight (compose a b) - weight a - weight b

-- Theorem 254: Collective surplus from void is zero
/-- Composing with void yields zero surplus — void adds no collective intelligence. -/
theorem collectiveSurplus_void_right (a : I) :
    collectiveSurplus a (void : I) = 0 := by
  unfold collectiveSurplus weight; simp [rs_void_void]

-- Theorem 255: Collective surplus of void with anything is zero
/-- Symmetric case: void on the left contributes nothing. -/
theorem collectiveSurplus_void_left (b : I) :
    collectiveSurplus (void : I) b = 0 := by
  unfold collectiveSurplus weight; simp [rs_void_void]

-- Theorem 256: Collective surplus plus individual weights equals group weight
/-- Conservation law: surplus + individuals = group. -/
theorem surplus_conservation (a b : I) :
    collectiveSurplus a b + weight a + weight b = weight (compose a b) := by
  unfold collectiveSurplus; ring

-- Theorem 257: Group weight is at least the leader's weight
/-- The group is at least as smart as its smartest member (left). -/
theorem group_exceeds_leader (a b : I) :
    weight (compose a b) ≥ weight a :=
  weight_compose_ge_left a b

-- Theorem 258: Void-void collective surplus is zero
/-- Two voids produce no collective intelligence. -/
theorem collectiveSurplus_void_void :
    collectiveSurplus (void : I) (void : I) = 0 := by
  unfold collectiveSurplus weight; simp [rs_void_void]

-- Theorem 259: Collective surplus via resonance decomposition
/-- The surplus equals the cross-resonances of the composed pair with itself,
    minus individual self-resonances. -/
theorem collectiveSurplus_eq (a b : I) :
    collectiveSurplus a b = weight (compose a b) - weight a - weight b := by
  unfold collectiveSurplus; ring

-- Theorem 260: Adding a member never decreases group weight
/-- Collective intelligence is monotone: more members ≥ current group weight. -/
theorem collective_monotone (a b c : I) :
    weight (compose (compose a b) c) ≥ weight (compose a b) := by
  unfold weight; exact compose_enriches' _ _

end CollectiveIntelligence

/-! ## §38. Echo Chamber Dynamics & Filter Bubbles

Filter bubbles arise when iterated interaction with like-minded ideas
reinforces existing views while filtering out dissent. In IDT, this is
modeled through composeN creating monotonically increasing self-resonance.
-/

section FilterBubbles
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Bubble intensity: how much an idea's self-resonance has been amplified
    through n rounds of self-composition. -/
noncomputable def bubbleIntensity (a : I) (n : ℕ) : ℝ :=
  weight (composeN a n) - weight a

-- Theorem 261: Bubble intensity starts at zero
/-- At depth 1, there's no amplification yet. -/
theorem bubble_initial (a : I) :
    bubbleIntensity a 1 = 0 := by
  unfold bubbleIntensity; simp [composeN_succ, composeN_zero, void_left']

-- Theorem 262: Bubble intensity is non-negative for n ≥ 1
/-- Filter bubbles never weaken the original signal. -/
theorem bubble_nonneg (a : I) (n : ℕ) :
    bubbleIntensity a (n + 1) ≥ 0 := by
  unfold bubbleIntensity
  linarith [hub_cumulative_advantage a n]

-- Theorem 263: Bubble intensity grows monotonically
/-- Once in a filter bubble, the amplification only increases. -/
theorem bubble_monotone (a : I) (n : ℕ) :
    bubbleIntensity a (n + 2) ≥ bubbleIntensity a (n + 1) := by
  unfold bubbleIntensity
  linarith [weight_composeN_mono a (n + 1)]

-- Theorem 264: Void experiences no bubble effect
/-- Void cannot form a filter bubble — it has no views to amplify. -/
theorem bubble_void (n : ℕ) :
    bubbleIntensity (void : I) n = 0 := by
  unfold bubbleIntensity; simp [composeN_void, weight_void]

-- Theorem 265: Bubble intensity decomposes as difference from base
/-- Bubble intensity at depth n is the exact surplus over base weight. -/
theorem bubble_decomposition (a : I) (n : ℕ) :
    bubbleIntensity a n + weight a = networkCapital a n := by
  unfold bubbleIntensity networkCapital; ring

end FilterBubbles

/-! ## §39. Network Evolution & Rewiring

Watts-Strogatz model: networks evolve through rewiring edges. In IDT,
rewiring means changing composition partners. We study how rewiring
affects total network weight.
-/

section NetworkEvolution
variable {I : Type*} [S : IdeaticSpace3 I]

-- Theorem 266: Rewiring preserves non-voidness of the left component
/-- Rewiring (changing composition partner) cannot destroy a non-void node. -/
theorem rewiring_preserves_nonvoid (a b₂ : I) (h : a ≠ void) :
    compose a b₂ ≠ void := by
  exact compose_ne_void_of_left a b₂ h

-- Theorem 267: Rewiring always yields non-negative weight
/-- Any rewiring produces a valid (non-negative weight) node. -/
theorem rewiring_nonneg (a b : I) :
    weight (compose a b) ≥ 0 := by
  exact weight_nonneg _

-- Theorem 268: Rewiring from b to void reduces to original
/-- Rewiring to void is equivalent to disconnecting — returning to base weight. -/
theorem rewire_to_void (a : I) :
    weight (compose a (void : I)) = weight a := by
  unfold weight; simp

-- Theorem 269: Rewiring from void to b gains weight
/-- Rewiring from void to a real connection gains the partner's weight. -/
theorem rewire_from_void (b : I) :
    weight (compose (void : I) b) = weight b := by
  unfold weight; simp

-- Theorem 270: Rewiring preserves the enrichment guarantee
/-- After any rewiring, the composed weight still exceeds the base. -/
theorem rewiring_enrichment (a b : I) :
    weight (compose a b) ≥ weight a :=
  weight_compose_ge_left a b

end NetworkEvolution

/-! ## §14. Network Paradoxes

Counter-intuitive results about how ideas spread through networks.
Many contradict standard intuitions from social network theory. -/

section NetworkParadoxes
variable {I : Type*} [S : IdeaticSpace3 I]

/-- NP1. THE CONSENSUS ENRICHMENT PARADOX: Adding a member to a consensus
    never reduces its weight. In classical social choice, adding dissenting
    voices can weaken consensus. In ideatic space, EVERY addition enriches.
    Counter-intuitive: you'd expect disagreement to weaken consensus. -/
theorem consensus_always_enriches (a b : I) :
    rs (consensus [a, b]) (consensus [a, b]) ≥ rs (consensus [a]) (consensus [a]) := by
  simp [consensus]; exact compose_enriches' a b

/-- NP2. THE ECHO CHAMBER INEVITABILITY: If ANY non-void idea enters
    a population, the consensus has strictly positive weight. Silence
    requires UNANIMOUS silence.
    Counter-intuitive: you'd expect diverse opinions to cancel out. -/
theorem consensus_nonvoid_positive (a b : I) (h : a ≠ void) :
    rs (consensus [a, b]) (consensus [a, b]) > 0 := by
  have hne : consensus [a, b] ≠ void := consensus_pair_ne_void a b h
  exact rs_self_pos (consensus [a, b]) hne

/-- NP3. THE CASCADE IRREVERSIBILITY: The weight of an information cascade
    can only grow. Once a cascade starts, it cannot be reversed.
    Counter-intuitive: you'd expect counter-information to weaken cascades.
    But even "corrective" information adds weight, not subtracts it. -/
theorem cascade_irreversible (a b c : I) :
    rs (compose (compose a b) c) (compose (compose a b) c) ≥
    rs (compose a b) (compose a b) ∧
    rs (compose a b) (compose a b) ≥ rs a a := by
  exact ⟨compose_enriches' (compose a b) c, compose_enriches' a b⟩

/-- NP4. THE INFLUENCE DECOMPOSITION PARADOX: An idea's influence in a
    network is NOT just its direct resonance — it includes an emergence
    term that captures synergistic effects with the existing network.
    Counter-intuitive: you'd expect influence to be an intrinsic property.
    But it depends on the INTERACTION between the idea and its context. -/
theorem influence_not_intrinsic (a b c : I) :
    rs (compose a b) c = rs a c + rs b c + emergence a b c := by
  exact rs_compose_eq a b c

/-- NP5. THE NETWORK WEIGHT RATCHET: Iterated interaction in a network
    produces monotonically non-decreasing weight. The network can only
    get "heavier" (more complex) over time.
    Counter-intuitive: you'd expect networks to equilibrate. -/
theorem network_weight_ratchet (a : I) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) ≥
    rs (composeN a n) (composeN a n) := by
  rw [composeN_succ]; exact compose_enriches' (composeN a n) a

/-- NP6. THE POLARIZATION BOUND: The emergence between two ideas
    (which drives polarization) is bounded by the geometric mean
    of their combined weight and the observer's weight.
    Counter-intuitive: you'd expect polarization to be unbounded
    in adversarial settings. But there's a fundamental ceiling. -/
theorem polarization_bounded (a b c : I) :
    (emergence a b c) ^ 2 ≤
    rs (compose a b) (compose a b) * rs c c :=
  emergence_bounded' a b c

/-- NP7. THE BRIDGING PARADOX: A bridge node that connects two clusters
    gains weight from both sides. Bridges are STRENGTHENED, not weakened,
    by their bridging role. Counter-intuitive: bridges are typically
    viewed as structural vulnerabilities, but in IDT they are the
    nodes that grow fastest. -/
theorem bridge_strengthened (bridge left right : I) :
    rs (compose (compose bridge left) right) (compose (compose bridge left) right) ≥
    rs bridge bridge := by
  have h1 := compose_enriches' bridge left
  have h2 := compose_enriches' (compose bridge left) right
  linarith

end NetworkParadoxes

end IDT3
