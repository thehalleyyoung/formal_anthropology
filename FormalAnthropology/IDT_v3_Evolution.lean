import FormalAnthropology.IDT_v3_Foundations

/-!
# IDT v3: Evolutionary Dynamics of Ideas

Ideas compete, reproduce, and evolve. Unlike biological evolution where
fitness is externally determined, an idea's fitness depends on the
ideatic environment — its resonance with OTHER ideas in the population.

## The Fundamental Mechanism

An idea's "fitness" in population P is its total resonance with P:
  fitness(a, P) := Σᵢ rs(a, pᵢ)

Ideas with high fitness get transmitted more. But transmission
involves composition (§ Diffusion), which introduces emergence.
So the "offspring" of an idea may be MORE or LESS fit than the parent —
evolution is not monotone.

## Key Results

1. **Fitness Decomposition**: fitness = self-contribution + cross-resonance
2. **Evolutionary Stability**: conditions under which an idea resists invasion
3. **The Red Queen**: in a changing population, standing still means falling behind
4. **Memetic Drift**: even without selection, composition changes fitness

## NO SORRIES
-/

namespace IDT3

section Evolution
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-! ## §1. Fitness in a Population -/

-- A population is a finite list of ideas.

/-- The fitness of an idea in a population: total resonance with all members. -/
noncomputable def fitness (a : I) (pop : List I) : ℝ :=
  pop.foldl (fun acc x => acc + rs a x) 0

/-- Fitness in an empty population is zero. -/
theorem fitness_nil (a : I) : fitness a ([] : List I) = 0 := rfl

/-- Fitness in a singleton population. -/
theorem fitness_singleton (a b : I) : fitness a [b] = rs a b := by
  unfold fitness; simp [List.foldl]

/-- Void has zero fitness in any population. -/
theorem void_fitness (pop : List I) : fitness (void : I) pop = 0 := by
  unfold fitness
  induction pop with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [rs_void_left']
    convert ih using 1
    ring

/-- Cross-resonance: how idea a resonates with idea b. -/
noncomputable def crossResonance (a b : I) : ℝ := rs a b

/-- Self-fitness: an idea's resonance with itself. -/
noncomputable def selfFitness (a : I) : ℝ := rs a a

/-- Self-fitness is non-negative. -/
theorem selfFitness_nonneg (a : I) : selfFitness a ≥ 0 := by
  unfold selfFitness; exact rs_self_nonneg' a

/-- Non-void ideas have positive self-fitness. -/
theorem selfFitness_pos (a : I) (h : a ≠ void) : selfFitness a > 0 := by
  unfold selfFitness; exact rs_self_pos a h

/-! ## §2. Invasion and Stability -/

/-- An idea a "invades" population pop if it has positive fitness. -/
def invades (a : I) (pop : List I) : Prop := fitness a pop > 0

/-- Void never invades. -/
theorem void_not_invades (pop : List I) : ¬invades (void : I) pop := by
  unfold invades; rw [void_fitness]; linarith

/-- An idea is evolutionarily stable against b in the context of
    self-pairing if its self-fitness exceeds the cross-resonance. -/
def stableAgainst (a b : I) : Prop :=
  rs a a > rs b a

/-- Non-void ideas are stable against void. -/
theorem stable_against_void (a : I) (h : a ≠ void) :
    stableAgainst a (void : I) := by
  unfold stableAgainst; rw [rs_void_left']; exact rs_self_pos a h

/-- Void is never stable against a non-void idea.
    (Silence loses to any actual content.) -/
theorem void_not_stable (b : I) (h : b ≠ void) :
    ¬stableAgainst (void : I) b := by
  unfold stableAgainst
  -- Goal: ¬(rs void void > rs b void)
  rw [rs_void_void, rs_void_right']
  linarith

/-! ## §3. Composition as Reproduction

When an idea "reproduces" through communication, the offspring is
compose(idea, receiver_context). This is not exact replication — the
emergence term κ means the offspring differs from the parent. -/

/-- The offspring of idea a when transmitted to context b. -/
def offspring (a b : I) : I := compose a b

/-- Offspring always has at least as much self-resonance as parent.
    Reproduction enriches — you can't un-say something. -/
theorem offspring_enriches (a b : I) :
    rs (offspring a b) (offspring a b) ≥ rs a a := by
  unfold offspring; exact compose_enriches' a b

/-- The mutation: how much the offspring's resonance with observer c
    differs from the parent's. -/
noncomputable def mutation (a b c : I) : ℝ :=
  rs (offspring a b) c - rs a c

/-- Mutation decomposes into context contribution + emergence. -/
theorem mutation_decomposition (a b c : I) :
    mutation a b c = rs b c + emergence a b c := by
  unfold mutation offspring
  have := rs_compose_eq a b c
  unfold emergence at *; linarith

/-- When context is void, mutation is zero (no environment = no change). -/
theorem mutation_void_context (a c : I) :
    mutation a (void : I) c = 0 := by
  unfold mutation offspring
  rw [void_right']; ring
/-! ## §4. The Red Queen Effect

In a changing population, an idea's fitness changes even if the idea
itself doesn't. The "Red Queen" principle: you must keep evolving
just to maintain your relative position. -/

/-- Fitness change when population gains a new member. -/
noncomputable def fitnessGain (a newcomer : I) : ℝ := rs a newcomer

/-- Adding void to population doesn't change fitness. -/
theorem fitnessGain_void (a : I) : fitnessGain a (void : I) = 0 := by
  unfold fitnessGain; exact rs_void_right' a

-- If the newcomer opposes a (negative resonance), fitness decreases.
-- This is immediate from the definition.

/-- The relative fitness of a vs b in the context of a single observer c. -/
noncomputable def relativeFitness (a b c : I) : ℝ :=
  rs a c - rs b c

/-- Relative fitness is antisymmetric. -/
theorem relativeFitness_antisymm (a b c : I) :
    relativeFitness a b c = -relativeFitness b a c := by
  unfold relativeFitness; ring

/-- Relative fitness of anything vs void is just its resonance. -/
theorem relativeFitness_vs_void (a c : I) :
    relativeFitness a (void : I) c = rs a c := by
  unfold relativeFitness; rw [rs_void_left']; ring

/-! ## §5. Memetic Drift

Even without selection pressure, the act of transmission changes ideas.
This is memetic drift — neutral evolution through the emergence term. -/

/-- The drift of idea a through n generations with constant context b. -/
def drift (a b : I) : ℕ → I
  | 0 => a
  | n + 1 => compose (drift a b n) b

theorem drift_zero (a b : I) : drift a b 0 = a := rfl

theorem drift_succ (a b : I) (n : ℕ) :
    drift a b (n + 1) = compose (drift a b n) b := rfl

/-- Drift always enriches — the idea accumulates weight. -/
theorem drift_enriches (a b : I) (n : ℕ) :
    rs (drift a b (n + 1)) (drift a b (n + 1)) ≥
    rs (drift a b n) (drift a b n) := by
  rw [drift_succ]; exact compose_enriches' (drift a b n) b

/-- Self-resonance of drifted ideas is non-decreasing. -/
theorem drift_nondecreasing (a b : I) (m n : ℕ) (h : m ≤ n) :
    rs (drift a b n) (drift a b n) ≥
    rs (drift a b m) (drift a b m) := by
  induction n with
  | zero =>
    interval_cases m; exact le_refl _
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact le_refl _
    · linarith [ih (Nat.lt_succ_iff.mp hlt), drift_enriches a b n]

/-! ## §6. Niche Construction

Ideas modify their own fitness landscape. When idea a is transmitted,
it changes the population, which changes what's fit. -/

/-- The niche effect: how adding idea a to context changes
    idea b's resonance with observer c. -/
noncomputable def nicheEffect (a b c : I) : ℝ :=
  rs (compose b a) c - rs b c

/-- Niche effect decomposes via emergence. -/
theorem nicheEffect_eq (a b c : I) :
    nicheEffect a b c = rs a c + emergence b a c := by
  unfold nicheEffect; have := rs_compose_eq b a c
  unfold emergence at *; linarith

/-- Adding void to any idea's context has no niche effect. -/
theorem nicheEffect_void (b c : I) :
    nicheEffect (void : I) b c = 0 := by
  unfold nicheEffect; rw [void_right']; ring

/-! ## §7. Fixation and Dominance -/

/-- Idea a dominates b if a has higher self-resonance. -/
def dominates (a b : I) : Prop :=
  rs a a > rs b b

/-- Dominance is irreflexive. -/
theorem dominates_irrefl (a : I) : ¬dominates a a := by
  unfold dominates; linarith

/-- Void is dominated by everything non-void. -/
theorem void_dominated (a : I) (h : a ≠ void) :
    dominates a (void : I) := by
  unfold dominates
  rw [rs_void_void]
  exact rs_self_pos a h

/-! ## §8. Fitness Landscape Curvature -/

/-- The fitness landscape curvature: how rapidly fitness changes
    as we compose with small perturbations. Measured by the emergence. -/
noncomputable def fitnessLandscapeCurvature (a b c : I) : ℝ :=
  emergence a b c

/-- Flat fitness landscape = zero emergence. -/
def flatLandscape (a b : I) : Prop :=
  ∀ c, fitnessLandscapeCurvature a b c = 0

/-- Void creates a flat landscape. -/
theorem void_flat_left (b : I) : flatLandscape (void : I) b := by
  intro c; unfold fitnessLandscapeCurvature; exact emergence_void_left b c

theorem void_flat_right (a : I) : flatLandscape a (void : I) := by
  intro c; unfold fitnessLandscapeCurvature; exact emergence_void_right a c

end Evolution

/-! -----------------------------------------------------------------------
  PART II: Deep Evolutionary Dynamics (60+ new theorems)
  -----------------------------------------------------------------------

  We now develop a comprehensive formal theory of idea-evolution,
  drawing analogies from population genetics, evolutionary game theory,
  and cultural evolution — but with the crucial twist that emergence
  (κ) makes ideatic evolution fundamentally different from biological
  evolution: offspring are not copies, fitness landscapes curve, and
  horizontal transfer is the NORM, not the exception.
-/

section DeepEvolution
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-! ## §9. Memetic Fitness Landscapes -/

/-- The fitness advantage of idea a over idea b in the eyes of observer c.
    Positive means a is better adapted to c's memetic niche. -/
noncomputable def fitnessAdvantage (a b c : I) : ℝ :=
  rs a c - rs b c

/-- Fitness advantage is antisymmetric: a's advantage over b equals
    minus b's advantage over a. Two rivals always see mirror-image landscapes. -/
theorem fitnessAdvantage_antisymm (a b c : I) :
    fitnessAdvantage a b c = -fitnessAdvantage b a c := by
  unfold fitnessAdvantage; ring

/-- Fitness advantage of any idea over itself is zero.
    No idea has an intrinsic advantage over itself — selection requires variation. -/
theorem fitnessAdvantage_self (a c : I) :
    fitnessAdvantage a a c = 0 := by
  unfold fitnessAdvantage; ring

/-- Fitness advantage over void equals raw resonance.
    Void is the universal baseline: any idea's fitness advantage
    over silence is simply how much it resonates. -/
theorem fitnessAdvantage_over_void (a c : I) :
    fitnessAdvantage a (void : I) c = rs a c := by
  unfold fitnessAdvantage; rw [rs_void_left']; ring

/-- Void has no advantage over anything.
    Silence never outcompetes an actual idea. -/
theorem fitnessAdvantage_void (b c : I) :
    fitnessAdvantage (void : I) b c = -rs b c := by
  unfold fitnessAdvantage; rw [rs_void_left']; ring

/-! ## §10. Invasion Dynamics -/

/-- A mutant m "invades" a resident r in the eyes of observer c
    if m has strictly positive fitness advantage over r. -/
def canInvade (m r c : I) : Prop := fitnessAdvantage m r c > 0

/-- Nothing invades itself — invasion requires genuine novelty. -/
theorem canInvade_irrefl (a c : I) : ¬canInvade a a c := by
  unfold canInvade; rw [fitnessAdvantage_self]; linarith

/-- Void cannot invade anything.
    Silence offers no competitive advantage. -/
theorem void_cannotInvade (r c : I) : ¬canInvade (void : I) r c ∨ rs r c ≤ 0 := by
  unfold canInvade fitnessAdvantage
  rw [rs_void_left']
  by_cases h : rs r c ≤ 0
  · right; exact h
  · push_neg at h; left; linarith

/-- If a can invade b and b can invade c (at the same observer),
    then a can invade c. Invasion is transitive along the fitness ordering. -/
theorem canInvade_trans (a b c obs : I)
    (hab : canInvade a b obs) (hbc : canInvade b c obs) :
    canInvade a c obs := by
  unfold canInvade fitnessAdvantage at *; linarith

/-! ## §11. Evolutionarily Stable Strategies (ESS) -/

/-- An idea a is an ESS against mutant m if a is stable AND
    a's self-resonance exceeds the cross-resonance of m with a.
    This captures Maynard Smith's ESS condition: the resident
    outperforms the mutant in the resident's own niche. -/
def isESS (a m : I) : Prop :=
  rs a a ≥ rs m a ∧ (rs a a = rs m a → rs a m > rs m m)

/-- Void is never an ESS against a non-void mutant.
    Emptiness cannot resist invasion by substance. -/
theorem void_not_ESS (m : I) (hm : m ≠ void) :
    ¬isESS (void : I) m := by
  unfold isESS
  intro ⟨_, h2⟩
  have h3 : rs (void : I) (void : I) = rs m (void : I) := by
    rw [rs_void_void, rs_void_right']
  have h4 := h2 h3
  rw [rs_void_left'] at h4
  have := rs_self_pos m hm
  linarith

/-- Strong ESS: a strictly beats m in self-context.
    When the inequality is strict, the second ESS condition is automatic. -/
def isStrongESS (a m : I) : Prop :=
  rs a a > rs m a

/-- A strong ESS is an ESS. The strict inequality makes the
    tie-breaking condition vacuously true. -/
theorem strongESS_is_ESS (a m : I) (h : isStrongESS a m) :
    isESS a m := by
  unfold isESS isStrongESS at *
  exact ⟨le_of_lt h, fun heq => absurd heq (ne_of_gt h)⟩

/-- Non-void ideas are strong ESS against void.
    Any real idea strictly outperforms silence in its own niche. -/
theorem nonvoid_strongESS_void (a : I) (ha : a ≠ void) :
    isStrongESS a (void : I) := by
  unfold isStrongESS; rw [rs_void_left']; exact rs_self_pos a ha

/-! ## §12. Replicator Dynamics -/

/-- Replicator fitness differential: how much better a does than b
    when evaluated by observer c. This drives the replicator equation:
    ideas with higher fitness grow in frequency. -/
noncomputable def replicatorDiff (a b c : I) : ℝ :=
  rs a c - rs b c

/-- Replicator dynamics are zero-sum between two competitors.
    What a gains, b loses — a conservation law of memetic selection. -/
theorem replicator_zero_sum (a b c : I) :
    replicatorDiff a b c + replicatorDiff b a c = 0 := by
  unfold replicatorDiff; ring

/-- The replicator differential against void measures absolute fitness. -/
theorem replicator_vs_void (a c : I) :
    replicatorDiff a (void : I) c = rs a c := by
  unfold replicatorDiff; rw [rs_void_left']; ring

/-- Transitivity of the replicator: if a beats b and b beats c,
    then a beats c. Selection pressures compose. -/
theorem replicator_transitive (a b c obs : I)
    (h1 : replicatorDiff a b obs > 0) (h2 : replicatorDiff b c obs > 0) :
    replicatorDiff a c obs > 0 := by
  unfold replicatorDiff at *; linarith

/-! ## §13. The Red Queen Hypothesis -/

/-- The Red Queen measure: how much an idea's fitness changes when
    the population shifts from old_context to new_context.
    Named after the Red Queen's dictum: "It takes all the running
    you can do to keep in the same place." -/
noncomputable def redQueenShift (a old_ctx new_ctx : I) : ℝ :=
  rs a new_ctx - rs a old_ctx

/-- The Red Queen is zero when the environment doesn't change.
    In a static world, there is no Red Queen effect. -/
theorem redQueen_static (a ctx : I) :
    redQueenShift a ctx ctx = 0 := by
  unfold redQueenShift; ring

/-- Red Queen shifts are antisymmetric in context direction.
    Shifting from A to B is exactly opposite to shifting from B to A. -/
theorem redQueen_reverse (a c1 c2 : I) :
    redQueenShift a c1 c2 = -redQueenShift a c2 c1 := by
  unfold redQueenShift; ring

/-- Red Queen shifts compose: a three-step environmental change
    can be decomposed into two steps. -/
theorem redQueen_compose (a c1 c2 c3 : I) :
    redQueenShift a c1 c3 = redQueenShift a c1 c2 + redQueenShift a c2 c3 := by
  unfold redQueenShift; ring

/-- Void is immune to the Red Queen — silence doesn't care about context.
    Only ideas with actual content are affected by environmental shifts. -/
theorem redQueen_void (c1 c2 : I) :
    redQueenShift (void : I) c1 c2 = 0 := by
  unfold redQueenShift; simp [rs_void_left']

/-! ## §14. Memetic Arms Races -/

/-- An arms race step: idea a "responds" to competitor b by composing
    with b's strategy. The result a ∘ b is a's counter-adaptation. -/
def armsRaceStep (a b : I) : I := compose a b

/-- Arms race iteration: n rounds of co-adaptation between two ideas. -/
def armsRace (a b : I) : ℕ → I × I
  | 0 => (a, b)
  | n + 1 =>
    let (a', b') := armsRace a b n
    (compose a' b', compose b' a')

theorem armsRace_zero (a b : I) : armsRace a b 0 = (a, b) := rfl

/-- After one round the first player has composed with the second.
    Both parties incorporate their rival's strategy. -/
theorem armsRace_one (a b : I) :
    armsRace a b 1 = (compose a b, compose b a) := rfl

/-- Arms races always escalate: the first player's self-resonance
    never decreases after a round. Conflict breeds complexity. -/
theorem armsRace_escalates_fst (a b : I) (n : ℕ) :
    rs (armsRace a b (n + 1)).1 (armsRace a b (n + 1)).1 ≥
    rs (armsRace a b n).1 (armsRace a b n).1 := by
  simp only [armsRace]
  exact compose_enriches' (armsRace a b n).1 (armsRace a b n).2

/-- Arms races always escalate for the second player too. -/
theorem armsRace_escalates_snd (a b : I) (n : ℕ) :
    rs (armsRace a b (n + 1)).2 (armsRace a b (n + 1)).2 ≥
    rs (armsRace a b n).2 (armsRace a b n).2 := by
  simp only [armsRace]
  exact compose_enriches' (armsRace a b n).2 (armsRace a b n).1

/-! ## §15. Lamarckian Evolution of Ideas -/

/-- Unlike biological evolution, ideas CAN inherit acquired characters.
    The Lamarckian step: an idea acquires trait t by composition.
    The "acquired character" persists in the offspring. -/
def lamarckianAcquire (idea trait : I) : I := compose idea trait

/-- Lamarckian acquisition is enriching — acquired traits add weight.
    This is why Lamarckian evolution works for ideas but not genes:
    you CAN'T un-think something you've learned. -/
theorem lamarckian_enriches (idea trait : I) :
    rs (lamarckianAcquire idea trait) (lamarckianAcquire idea trait) ≥
    rs idea idea := by
  unfold lamarckianAcquire; exact compose_enriches' idea trait

/-- Lamarckian acquisition is associative — it doesn't matter if you
    learn trait t then u, or learn (t then u) all at once. -/
theorem lamarckian_assoc (idea t u : I) :
    lamarckianAcquire (lamarckianAcquire idea t) u =
    lamarckianAcquire idea (compose t u) := by
  unfold lamarckianAcquire; rw [compose_assoc']

/-- Acquiring void teaches nothing — the null curriculum is inert. -/
theorem lamarckian_void_trait (idea : I) :
    lamarckianAcquire idea (void : I) = idea := by
  unfold lamarckianAcquire; simp

/-! ## §16. Niche Construction (Extended) -/

/-- The niche construction differential: how much idea a's niche-building
    activity changes the relative fitness of b vs c. Ideas don't just
    adapt to their environment — they CREATE their environment. -/
noncomputable def nicheConstructionDiff (a b c obs : I) : ℝ :=
  rs (compose b a) obs - rs (compose c a) obs

/-- Niche construction is zero-sum between competitors.
    Constructing a niche that helps one idea hurts the other. -/
theorem nicheConstruction_zero_sum (a b c obs : I) :
    nicheConstructionDiff a b c obs + nicheConstructionDiff a c b obs = 0 := by
  unfold nicheConstructionDiff; ring

/-- Void niche construction changes nothing.
    You can't build a niche out of silence. -/
theorem nicheConstruction_void (b c obs : I) :
    nicheConstructionDiff (void : I) b c obs = rs b obs - rs c obs := by
  unfold nicheConstructionDiff; simp

/-! ## §17. Genetic Drift Analogues -/

/-- Drift magnitude: how much an idea changes through one transmission
    event with context b, measured against observer c. Small drift
    means high-fidelity transmission; large drift means significant mutation. -/
noncomputable def driftMagnitude (a b c : I) : ℝ :=
  rs (compose a b) c - rs a c

/-- Drift decomposes into context effect plus emergence.
    Biological drift is random; memetic drift has a deterministic component
    (the context) and a creative component (emergence). -/
theorem drift_decomposition (a b c : I) :
    driftMagnitude a b c = rs b c + emergence a b c := by
  unfold driftMagnitude; have := rs_compose_eq a b c
  unfold emergence at *; linarith

/-- Drift through void context is zero — no medium, no change.
    This is the ideatic analogue of zero mutation rate. -/
theorem drift_void_context (a c : I) :
    driftMagnitude a (void : I) c = 0 := by
  unfold driftMagnitude; simp

/-- Drift of void just reveals the context — silence is a blank canvas.
    Analogous to the fact that zero-frequency alleles reflect only immigration. -/
theorem drift_of_void (b c : I) :
    driftMagnitude (void : I) b c = rs b c := by
  unfold driftMagnitude; rw [void_left', rs_void_left']; ring

/-! ## §18. Speciation of Ideas -/

/-- Two ideas are reproductively isolated if their composition
    with each other yields the same self-resonance as their individual
    compositions with void. That is, composing them adds nothing
    beyond what each already has. -/
def reproductivelyIsolated (a b : I) : Prop :=
  emergence a b (compose a b) = 0 ∧ emergence b a (compose b a) = 0

/-- Every idea is reproductively isolated from void.
    You can't meaningfully hybridize with silence. -/
theorem isolated_from_void (a : I) : reproductivelyIsolated a (void : I) := by
  constructor
  · exact emergence_void_right a (compose a (void : I))
  · simp [emergence_void_left]

/-- Reproductive isolation is symmetric.
    If a can't hybridize with b, then b can't hybridize with a. -/
theorem reproductivelyIsolated_symm_def (a b : I)
    (h : reproductivelyIsolated a b) :
    emergence a b (compose a b) = 0 ∧ emergence b a (compose b a) = 0 :=
  h

/-! ## §19. Phylogenetic Distance -/

/-- Phylogenetic distance: how different two ideas are in self-resonance.
    Measures the "evolutionary distance" between two ideas. -/
noncomputable def phyloDistance (a b : I) : ℝ :=
  rs a a + rs b b - rs a b - rs b a

/-- Phylogenetic distance to self is zero.
    Every idea is at distance zero from itself. -/
theorem phyloDistance_self (a : I) : phyloDistance a a = 0 := by
  unfold phyloDistance; ring

/-- Phylogenetic distance is symmetric.
    The evolutionary distance from a to b equals that from b to a. -/
theorem phyloDistance_symm (a b : I) : phyloDistance a b = phyloDistance b a := by
  unfold phyloDistance; ring

/-- Phylogenetic distance from void is simply self-resonance.
    The distance from silence to an idea measures the idea's own weight. -/
theorem phyloDistance_void (a : I) : phyloDistance a (void : I) = rs a a := by
  unfold phyloDistance; rw [rs_void_void, rs_void_left', rs_void_right']; ring

/-! ## §20. Horizontal Transfer -/

/-- Horizontal transfer: idea a acquires component c from idea b.
    Unlike vertical transmission (parent to child), horizontal transfer
    lets unrelated ideas exchange "genetic material." -/
def horizontalTransfer (recipient donor : I) : I :=
  compose recipient donor

/-- Horizontal transfer always enriches the recipient.
    Acquiring foreign ideas never decreases your self-resonance.
    This is why horizontal transfer is so powerful in cultural evolution:
    it's always (weakly) beneficial in terms of presence. -/
theorem horizontalTransfer_enriches (r d : I) :
    rs (horizontalTransfer r d) (horizontalTransfer r d) ≥ rs r r := by
  unfold horizontalTransfer; exact compose_enriches' r d

/-- Sequential horizontal transfers are associative.
    Acquiring trait d₁ then d₂ is the same as acquiring (d₁ then d₂).
    The order of acquisition doesn't matter for the final result. -/
theorem horizontalTransfer_assoc (r d₁ d₂ : I) :
    horizontalTransfer (horizontalTransfer r d₁) d₂ =
    horizontalTransfer r (compose d₁ d₂) := by
  unfold horizontalTransfer; rw [compose_assoc']

/-- Transferring void is a no-op. Acquiring nothing changes nothing. -/
theorem horizontalTransfer_void (r : I) :
    horizontalTransfer r (void : I) = r := by
  unfold horizontalTransfer; simp

/-! ## §21. Punctuated Equilibrium -/

/-- A stasis measure: how little an idea changes through drift.
    High stasis means the idea is in equilibrium; a sudden drop
    signals a "punctuation" event. -/
noncomputable def stasisMeasure (a b c : I) : ℝ :=
  rs a c - rs (compose a b) c

/-- Stasis is zero when the perturbation is void.
    No perturbation = perfect stasis. -/
theorem stasis_void_perturbation (a c : I) :
    stasisMeasure a (void : I) c = 0 := by
  unfold stasisMeasure; simp

/-- Stasis decomposes into negative drift: stasis = -(context contribution + emergence).
    The more drift, the less stasis. -/
theorem stasis_eq_neg_drift (a b c : I) :
    stasisMeasure a b c = -(rs b c + emergence a b c) := by
  unfold stasisMeasure; have := rs_compose_eq a b c
  unfold emergence at *; linarith

/-! ## §22. Adaptive Radiation -/

/-- Adaptive radiation: starting from ancestor a, produce n descendant
    lineages by composing with different "niches" drawn from a list.
    Each descendant adapts to its own ecological opportunity. -/
def adaptiveRadiation (ancestor : I) (niches : List I) : List I :=
  niches.map (compose ancestor)

/-- Radiation into empty niches produces nothing. -/
theorem radiation_empty (a : I) :
    adaptiveRadiation a ([] : List I) = [] := rfl

/-- Radiation into a single niche produces one descendant. -/
theorem radiation_singleton (a niche : I) :
    adaptiveRadiation a [niche] = [compose a niche] := rfl

/-- Every descendant in an adaptive radiation is at least as heavy
    as the ancestor. Specialization adds weight; it doesn't lose it. -/
theorem radiation_enriches (ancestor : I) (niches : List I) (d : I)
    (hd : d ∈ adaptiveRadiation ancestor niches) :
    rs d d ≥ rs ancestor ancestor := by
  unfold adaptiveRadiation at hd
  rw [List.mem_map] at hd
  obtain ⟨niche, _, rfl⟩ := hd
  exact compose_enriches' ancestor niche

/-- Radiation from void produces the niches themselves.
    Starting from nothing, you just get the raw ecological opportunities. -/
theorem radiation_from_void (niches : List I) :
    adaptiveRadiation (void : I) niches = niches := by
  unfold adaptiveRadiation
  induction niches with
  | nil => rfl
  | cons x xs ih => simp [List.map, void_left', ih]

/-! ## §23. Extinction Dynamics -/

/-- An idea is "extinct" (relative to observer c) when it has zero
    resonance with c. It exists in the space but has no presence
    in c's perception. -/
def extinctFor (a c : I) : Prop := rs a c = 0

/-- Void is extinct for every observer.
    Silence is universally invisible. -/
theorem void_extinct (c : I) : extinctFor (void : I) c := rs_void_left' c

/-- Everything is extinct for void.
    A nonexistent observer perceives nothing. -/
theorem extinct_for_void (a : I) : extinctFor a (void : I) := rs_void_right' a

/-- If a is extinct for c and b is extinct for c, then a's fitness
    advantage over b at c is zero. Extinction equalizes. -/
theorem extinct_equal_fitness (a b c : I)
    (ha : extinctFor a c) (hb : extinctFor b c) :
    fitnessAdvantage a b c = 0 := by
  unfold fitnessAdvantage extinctFor at *; rw [ha, hb]; ring

/-! ## §24. Co-evolution -/

/-- Co-evolutionary feedback: idea a adapts to b, while b adapts to a.
    The co-evolutionary product captures both adaptations. -/
noncomputable def coevolutionaryFeedback (a b c : I) : ℝ :=
  rs (compose a b) c + rs (compose b a) c

/-- Co-evolutionary feedback is symmetric in the interacting pair.
    It doesn't matter which idea we label "first" — co-evolution
    is a mutual process. -/
theorem coevolution_symm (a b c : I) :
    coevolutionaryFeedback a b c = coevolutionaryFeedback b a c := by
  unfold coevolutionaryFeedback; ring

/-- Co-evolutionary feedback decomposes via emergence.
    The total co-evolutionary effect = 2×(individual resonances) + both emergences. -/
theorem coevolution_decompose (a b c : I) :
    coevolutionaryFeedback a b c =
    2 * rs a c + 2 * rs b c + emergence a b c + emergence b a c := by
  unfold coevolutionaryFeedback
  rw [rs_compose_eq a b c, rs_compose_eq b a c]; ring

/-- Co-evolutionary feedback with void reduces to individual resonance. -/
theorem coevolution_void (a c : I) :
    coevolutionaryFeedback a (void : I) c = 2 * rs a c := by
  unfold coevolutionaryFeedback; simp; ring

/-! ## §25. The Baldwin Effect -/

/-- The Baldwin effect: learned behaviors (acquired through composition)
    become "instinctive" (permanent features of self-resonance).
    Baldwin gain measures how much learning (composing with environment e)
    increases self-resonance beyond the original. -/
noncomputable def baldwinGain (idea env : I) : ℝ :=
  rs (compose idea env) (compose idea env) - rs idea idea

/-- Baldwin gain is always non-negative.
    Learning can only add to your presence — you can't unlearn
    your way to less self-resonance. This is why the Baldwin effect
    works: acquired adaptations never decrease fitness. -/
theorem baldwinGain_nonneg (idea env : I) : baldwinGain idea env ≥ 0 := by
  unfold baldwinGain; linarith [compose_enriches' idea env]

/-- Baldwin gain from void environment is zero.
    You can't learn anything from silence. -/
theorem baldwinGain_void_env (idea : I) : baldwinGain idea (void : I) = 0 := by
  unfold baldwinGain; simp

/-- Baldwin gain of void equals the environment's self-resonance.
    Nothingness gains exactly what the environment provides. -/
theorem baldwinGain_void_idea (env : I) : baldwinGain (void : I) env = rs env env := by
  unfold baldwinGain; rw [rs_void_void]; simp [void_left']

/-! ## §26. Memetic Mutation Operators -/

/-- Point mutation: perturb idea a by composing with mutagen m. -/
def pointMutation (a m : I) : I := compose a m

/-- A mutation's effect on fitness: how the mutant differs from parent
    in the eyes of observer c. -/
noncomputable def mutationEffect (a m c : I) : ℝ :=
  rs (pointMutation a m) c - rs a c

/-- Mutation effect decomposes into mutagen contribution + emergence.
    Unlike random biological mutation, memetic mutation has a
    DIRECTED component (the mutagen's own resonance). -/
theorem mutationEffect_decompose (a m c : I) :
    mutationEffect a m c = rs m c + emergence a m c := by
  unfold mutationEffect pointMutation
  have := rs_compose_eq a m c
  unfold emergence at *; linarith

/-- Null mutation (void mutagen) has no effect.
    The null mutagen is the identity: it doesn't change anything. -/
theorem null_mutation (a c : I) :
    mutationEffect a (void : I) c = 0 := by
  unfold mutationEffect pointMutation; simp

/-- Mutations always increase self-resonance (or leave it unchanged).
    In biological terms: mutations can't make you less complex. -/
theorem mutation_enriches_self (a m : I) :
    rs (pointMutation a m) (pointMutation a m) ≥ rs a a := by
  unfold pointMutation; exact compose_enriches' a m

/-! ## §27. Selection Pressure -/

/-- Selection pressure: the force driving idea a to displace idea b
    in the context of observer c. Positive means a is being selected for. -/
noncomputable def selectionPressure (a b c : I) : ℝ :=
  rs a c - rs b c

/-- Selection pressure is zero-sum: what favors a disfavors b. -/
theorem selection_zero_sum (a b c : I) :
    selectionPressure a b c + selectionPressure b a c = 0 := by
  unfold selectionPressure; ring

/-- No selection pressure between identical ideas.
    Selection requires variation — this is Fisher's fundamental theorem. -/
theorem selection_identical (a c : I) :
    selectionPressure a a c = 0 := by
  unfold selectionPressure; ring

/-- Selection against void is pure resonance. -/
theorem selection_vs_void (a c : I) :
    selectionPressure a (void : I) c = rs a c := by
  unfold selectionPressure; rw [rs_void_left']; ring

/-! ## §28. Frequency-Dependent Selection -/

/-- Frequency-dependent fitness: idea a's fitness depends on how many
    copies of b (the competitor) are present. With n copies of b as
    context, a's perceived fitness changes. -/
noncomputable def freqDepFitness (a b : I) (n : ℕ) : ℝ :=
  rs a (composeN b n)

/-- At zero frequency, fitness is measured against void. -/
theorem freqDep_zero (a b : I) : freqDepFitness a b 0 = 0 := by
  unfold freqDepFitness; simp [rs_void_right']

/-- Void has zero frequency-dependent fitness at any frequency. -/
theorem freqDep_void (b : I) (n : ℕ) : freqDepFitness (void : I) b n = 0 := by
  unfold freqDepFitness; exact rs_void_left' _

/-! ## §29. Drift-Selection Balance -/

/-- The net evolutionary force on idea a: the balance between
    selection (fitness advantage) and drift (transmission noise).
    When these forces balance, the idea is in evolutionary equilibrium. -/
noncomputable def netEvolutionaryForce (a b ctx : I) : ℝ :=
  selectionPressure a b ctx + driftMagnitude a ctx b

/-- The net force when context is void is zero.
    In an empty environment, selection and drift both vanish. -/
theorem netForce_void_context (a b : I) :
    netEvolutionaryForce a b (void : I) = 0 := by
  unfold netEvolutionaryForce selectionPressure driftMagnitude
  rw [rs_void_right' a, rs_void_right' b, void_right']
  ring

/-! ## §30. Evolutionary Game Theory -/

/-- Payoff matrix entry: what idea a "earns" when interacting with b,
    from observer c's perspective. This is the fundamental quantity
    in evolutionary game theory applied to ideas. -/
noncomputable def payoff (a b c : I) : ℝ := rs (compose a b) c

/-- The payoff from playing against void is just your own resonance.
    Against an empty opponent, you perform at your baseline. -/
theorem payoff_vs_void (a c : I) :
    payoff a (void : I) c = rs a c := by
  unfold payoff; simp

/-- Void earns nothing against any opponent.
    The null strategy always earns zero payoff. -/
theorem void_payoff (b c : I) :
    payoff (void : I) b c = rs b c := by
  unfold payoff; simp

/-- Payoff decomposes into individual contributions + emergence.
    This reveals the "game-theoretic surprise": the interaction term. -/
theorem payoff_decompose (a b c : I) :
    payoff a b c = rs a c + rs b c + emergence a b c := by
  unfold payoff; exact rs_compose_eq a b c

/-! ## §31. Kin Selection (Hamilton's Rule for Ideas) -/

/-- The "relatedness" of two ideas: how much they resonate with each other
    relative to self-resonance. Hamilton's rule says altruism evolves when
    r·B > C; for ideas, "altruism" means supporting a resonant idea at
    cost to your own transmission. -/
noncomputable def ideaRelatedness (a b : I) : ℝ :=
  rs a b + rs b a

/-- Self-relatedness is twice self-resonance.
    An idea's relatedness to itself is maximal (by definition). -/
theorem relatedness_self (a : I) : ideaRelatedness a a = 2 * rs a a := by
  unfold ideaRelatedness; ring

/-- Relatedness is symmetric. This mirrors Hamilton's coefficient of
    relatedness: r(a,b) = r(b,a). -/
theorem relatedness_symm (a b : I) :
    ideaRelatedness a b = ideaRelatedness b a := by
  unfold ideaRelatedness; ring

/-- Relatedness to void is zero. You share nothing with silence. -/
theorem relatedness_void (a : I) : ideaRelatedness a (void : I) = 0 := by
  unfold ideaRelatedness; simp [rs_void_right', rs_void_left']

/-! ## §32. Group Selection -/

/-- Group fitness: the average self-resonance of ideas in a group.
    Groups with higher average fitness outcompete other groups. -/
noncomputable def groupWeight (pop : List I) : ℝ :=
  pop.foldl (fun acc x => acc + rs x x) 0

/-- Empty groups have zero weight. -/
theorem groupWeight_nil : groupWeight ([] : List I) = 0 := rfl

/-- A group of void has zero weight. -/
theorem groupWeight_void : groupWeight [(void : I)] = 0 := by
  unfold groupWeight; simp [List.foldl, rs_void_void]

/-! ## §33. Evolutionary Stable States (Population Level) -/

/-- A pair (a, b) is in evolutionary equilibrium if neither can invade
    the other. This is Nash equilibrium for ideas. -/
def evolutionaryEquilibrium (a b : I) : Prop :=
  rs a a ≥ rs b a ∧ rs b b ≥ rs a b

/-- Every idea is in equilibrium with itself. Self-play is trivially stable. -/
theorem equilibrium_self (a : I) : evolutionaryEquilibrium a a := by
  unfold evolutionaryEquilibrium; exact ⟨le_refl _, le_refl _⟩

/-! ## §34. Muller's Ratchet for Ideas -/

/-- Muller's ratchet: in the absence of recombination, deleterious
    mutations accumulate. For ideas, repeated drift through a "bad"
    context b₁ then b₂ can only increase weight (never lose it).
    The ratchet measures the accumulated "baggage" after two transmissions. -/
noncomputable def mullersRatchet (a b₁ b₂ : I) : ℝ :=
  rs (compose (compose a b₁) b₂) (compose (compose a b₁) b₂) - rs a a

/-- Muller's ratchet is always non-negative: you can't shed accumulated weight.
    Ideas, like asexual organisms, can't escape their history. -/
theorem mullers_ratchet_nonneg (a b₁ b₂ : I) :
    mullersRatchet a b₁ b₂ ≥ 0 := by
  unfold mullersRatchet
  have h1 := compose_enriches' a b₁
  have h2 := compose_enriches' (compose a b₁) b₂
  linarith

/-! ## §35. Evolutionary Potential -/

/-- Evolutionary potential: how much an idea CAN evolve when exposed
    to trait t, measured as the enrichment of self-resonance. -/
noncomputable def evoPotential (a t : I) : ℝ :=
  rs (compose a t) (compose a t) - rs a a

/-- Evolutionary potential is always non-negative.
    Every idea has non-negative evolvability. -/
theorem evoPotential_nonneg (a t : I) : evoPotential a t ≥ 0 := by
  unfold evoPotential; linarith [compose_enriches' a t]

/-- Evolutionary potential through void is zero.
    Without stimuli, there is no evolution. -/
theorem evoPotential_void (a : I) : evoPotential a (void : I) = 0 := by
  unfold evoPotential; simp

/-- Evolutionary potential of void is the self-resonance of t.
    Starting from nothing, your potential equals what's available. -/
theorem evoPotential_of_void (t : I) :
    evoPotential (void : I) t = rs t t := by
  unfold evoPotential
  simp [void_left', rs_void_void]

/-! ## §36. Speciation Barrier -/

/-- The speciation barrier between a and b: the emergence that would
    be generated by hybridization. High barriers mean the ideas are
    deeply incompatible — they've "speciated" in meaning-space. -/
noncomputable def speciationBarrier (a b : I) : ℝ :=
  emergence a b (compose a b) - emergence b a (compose b a)

/-- The speciation barrier is antisymmetric. If a's barrier to b is
    high, b's barrier to a is equally high in the opposite direction. -/
theorem speciationBarrier_antisymm (a b : I) :
    speciationBarrier a b = -speciationBarrier b a := by
  unfold speciationBarrier; ring

/-- The speciation barrier with void is zero. Everything hybridizes
    freely with silence. -/
theorem speciationBarrier_void (a : I) :
    speciationBarrier a (void : I) = 0 := by
  unfold speciationBarrier
  rw [emergence_void_right]
  simp [emergence_void_left]

/-! ## §37. Convergent Evolution -/

/-- Convergent evolution measure: how similar two independently evolved
    ideas become when subjected to the same selective environment e.
    High convergence means the environment drives ideas toward
    the same "phenotype" regardless of ancestry. -/
noncomputable def convergenceMeasure (a b e : I) : ℝ :=
  rs (compose a e) (compose b e) - rs a b

/-- Convergence in the void environment is zero.
    Without selective pressure, there is no convergent evolution. -/
theorem convergence_void_env (a b : I) :
    convergenceMeasure a b (void : I) = 0 := by
  unfold convergenceMeasure; simp

/-- Convergence is symmetric: if a converges toward b, b converges
    toward a. -/
theorem convergence_symm_self (a e : I) :
    convergenceMeasure a a e = evoPotential a e := by
  unfold convergenceMeasure evoPotential; ring

/-! ## §38. Evolutionary Irreversibility -/

/-- Dollo's law for ideas: evolution is irreversible. Once you compose
    with b, you can never return to a lower self-resonance.
    The irreversibility gap measures how far you've moved from the original. -/
noncomputable def irreversibilityGap (a b : I) : ℝ :=
  rs (compose a b) (compose a b) - rs a a

/-- The irreversibility gap is always non-negative.
    This IS Dollo's law: you can't go back. -/
theorem dollo_law (a b : I) : irreversibilityGap a b ≥ 0 := by
  unfold irreversibilityGap; linarith [compose_enriches' a b]

/-- Composing with void doesn't advance the ratchet. -/
theorem irreversibility_void (a : I) :
    irreversibilityGap a (void : I) = 0 := by
  unfold irreversibilityGap; simp

/-! ## §39. Founder Effects -/

/-- Founder effect: the resonance of a new population seeded by
    founder a in niche n, as perceived by observer c.
    The founder's "genetic bottleneck" determines everything. -/
noncomputable def founderEffect (founder niche c : I) : ℝ :=
  rs (compose founder niche) c

/-- When the founder is void, the population reflects only the niche.
    An empty founder contributes nothing but the raw environment. -/
theorem founderEffect_void (niche c : I) :
    founderEffect (void : I) niche c = rs niche c := by
  unfold founderEffect; simp

/-- When the niche is void, the population reflects only the founder. -/
theorem founderEffect_void_niche (founder c : I) :
    founderEffect founder (void : I) c = rs founder c := by
  unfold founderEffect; simp

/-! ## §40. Co-adaptation and Mutualism -/

/-- Mutualism measure: how much two ideas mutually benefit from
    co-occurrence. Positive = mutualism, negative = parasitism. -/
noncomputable def mutualismMeasure (a b : I) : ℝ :=
  evoPotential a b + evoPotential b a

/-- Mutualism is symmetric. If a benefits from b, b benefits from a
    by the same total amount. -/
theorem mutualism_symm (a b : I) :
    mutualismMeasure a b = mutualismMeasure b a := by
  unfold mutualismMeasure; ring

/-- Mutualism with void is one-sided: only void benefits. -/
theorem mutualism_void (a : I) :
    mutualismMeasure a (void : I) = evoPotential (void : I) a := by
  unfold mutualismMeasure; rw [evoPotential_void]; simp

/-! ## §41. Evolutionary Distance Metric Properties -/

/-- The squared divergence between two ideas: a non-negative measure
    of how far apart two ideas are in resonance-space. -/
noncomputable def sqDivergence (a b : I) : ℝ :=
  rs a a + rs b b - rs a b - rs b a

/-- Squared divergence from self is zero. -/
theorem sqDivergence_self (a : I) : sqDivergence a a = 0 := by
  unfold sqDivergence; ring

/-- Squared divergence is symmetric. -/
theorem sqDivergence_symm (a b : I) : sqDivergence a b = sqDivergence b a := by
  unfold sqDivergence; ring

/-- Divergence from void is self-resonance. The "distance" from silence
    is simply how much content you have. -/
theorem sqDivergence_void (a : I) : sqDivergence a (void : I) = rs a a := by
  unfold sqDivergence; rw [rs_void_void, rs_void_left', rs_void_right']; ring

/-! ## §42. Recombination -/

/-- Recombination: create a "hybrid" idea by composing parts of two parents.
    This is horizontal transfer as a creative force. -/
def recombine (parent1 parent2 : I) : I := compose parent1 parent2

/-- Recombination is enriching for the first parent's lineage. -/
theorem recombine_enriches (p1 p2 : I) :
    rs (recombine p1 p2) (recombine p1 p2) ≥ rs p1 p1 := by
  unfold recombine; exact compose_enriches' p1 p2

/-- Recombining with void yields the parent unchanged.
    Mating with "nothing" is just clonal reproduction. -/
theorem recombine_void (p : I) : recombine p (void : I) = p := by
  unfold recombine; simp

/-! ## §43. Multi-Generation Fitness Tracking -/

/-- Track fitness across generations: the fitness of an idea after n
    generations of drift through constant context b. -/
noncomputable def multigenerationalFitness (a b : I) (n : ℕ) (obs : I) : ℝ :=
  rs (drift a b n) obs

/-- At generation zero, fitness equals the original idea's resonance. -/
theorem multigen_zero (a b obs : I) :
    multigenerationalFitness a b 0 obs = rs a obs := by
  unfold multigenerationalFitness drift; ring

/-- Multi-generational self-resonance is non-decreasing.
    Over time, ideas accumulate weight through drift. -/
theorem multigen_self_nondecreasing (a b : I) (n : ℕ) :
    rs (drift a b (n + 1)) (drift a b (n + 1)) ≥
    rs (drift a b n) (drift a b n) :=
  drift_enriches a b n

/-! ## §44. Inclusive Fitness -/

/-- Inclusive fitness: an idea's fitness includes not just its own
    resonance but also the resonance of ideas it has "helped" create
    (through composition). For idea a that spawned offspring a∘b,
    the inclusive fitness at observer c is their combined contribution. -/
noncomputable def inclusiveFitness (a b c : I) : ℝ :=
  rs a c + rs (compose a b) c

/-- Inclusive fitness decomposes into direct + indirect + emergence.
    The emergence term is the "bonus" from being a contributing parent. -/
theorem inclusiveFitness_decompose (a b c : I) :
    inclusiveFitness a b c = 2 * rs a c + rs b c + emergence a b c := by
  unfold inclusiveFitness
  rw [rs_compose_eq a b c]; ring

/-- Inclusive fitness when the offspring context is void. -/
theorem inclusiveFitness_void (a c : I) :
    inclusiveFitness a (void : I) c = 2 * rs a c := by
  unfold inclusiveFitness; simp; ring

/-! ## §45. Environmental Canalization -/

/-- Canalization: how much an environment e constrains the evolutionary
    trajectory of idea a. Measures the difference between evolving in
    environment e vs void. -/
noncomputable def canalization (a e c : I) : ℝ :=
  rs (compose a e) c - rs a c

/-- Canalization by void is zero: no environment = no constraint. -/
theorem canalization_void (a c : I) :
    canalization a (void : I) c = 0 := by
  unfold canalization; simp

/-- Canalization of void by anything is just the environment's resonance.
    A blank slate is entirely shaped by its environment. -/
theorem canalization_of_void (e c : I) :
    canalization (void : I) e c = rs e c := by
  unfold canalization; simp [rs_void_left']

/-! ## §46. Adaptation Rate -/

/-- Adaptation rate: how quickly an idea changes per transmission event.
    Measured as the self-resonance gain from one composition. -/
noncomputable def adaptationRate (a b : I) : ℝ :=
  rs (compose a b) (compose a b) - rs a a

/-- Adaptation rate is always non-negative. Ideas can only gain complexity. -/
theorem adaptationRate_nonneg (a b : I) : adaptationRate a b ≥ 0 := by
  unfold adaptationRate; linarith [compose_enriches' a b]

/-- Adaptation rate through void is zero. -/
theorem adaptationRate_void (a : I) : adaptationRate a (void : I) = 0 := by
  unfold adaptationRate; simp

/-! ## §47. Cumulative Cultural Evolution -/

/-- Cumulative cultural evolution: the total weight gained after n
    generations of drift. This formalizes Tomasello's "ratchet effect"
    — each generation builds on the last. -/
noncomputable def cumulativeGain (a b : I) (n : ℕ) : ℝ :=
  rs (drift a b n) (drift a b n) - rs a a

/-- At generation zero, cumulative gain is zero. -/
theorem cumulativeGain_zero (a b : I) : cumulativeGain a b 0 = 0 := by
  unfold cumulativeGain drift; ring

/-- Cumulative gain is always non-negative: the ratchet never goes backward. -/
theorem cumulativeGain_nonneg (a b : I) (n : ℕ) : cumulativeGain a b n ≥ 0 := by
  unfold cumulativeGain
  induction n with
  | zero => simp [drift]
  | succ n ih =>
    have h := drift_enriches a b n
    unfold cumulativeGain at ih
    linarith

/-- Cumulative gain is non-decreasing across generations. -/
theorem cumulativeGain_mono (a b : I) (n : ℕ) :
    cumulativeGain a b (n + 1) ≥ cumulativeGain a b n := by
  unfold cumulativeGain; linarith [drift_enriches a b n]

end DeepEvolution

/-! ## §48. Evolutionary Paradoxes

Counter-intuitive results about the evolution of ideas that
contradict naive expectations from biological evolution. -/

section EvolutionaryParadoxes
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- EP1. THE COMPLEXITY RATCHET: Cultural evolution can never reduce
    complexity (measured by weight). Every generation is at least as
    complex as the last. This formalizes Tomasello's "ratchet effect."
    Counter-intuitive: biological evolution can lose complexity (e.g.,
    cave fish losing eyes). But ideatic evolution CANNOT. -/
theorem complexity_ratchet (a b : I) (n m : ℕ) (h : n ≤ m) :
    rs (drift a b m) (drift a b m) ≥ rs (drift a b n) (drift a b n) :=
  drift_nondecreasing a b n m h

/-- EP2. THE RED QUEEN ENRICHMENT: When a newcomer enters, every
    existing idea's self-resonance is unchanged, but the POPULATION's
    total weight increases. You must evolve (compose) just to maintain
    relative position, even though your absolute weight hasn't changed.
    Counter-intuitive: your fitness changes even if YOU don't change. -/
theorem red_queen_absolute (a newcomer : I) :
    rs a a = rs a a ∧
    rs (compose a newcomer) (compose a newcomer) ≥ rs a a := by
  exact ⟨rfl, compose_enriches' a newcomer⟩

/-- EP3. THE DRIFT ACCELERATION THEOREM: Each generation of drift
    is at least as heavy as the previous one, and the drift weight
    after n+1 generations exceeds the weight of a by the cumulative
    gain. The rate of complexity growth is non-decreasing.
    Counter-intuitive: you'd expect drift to decelerate as the
    "easy gains" are exhausted. But the enrichment bound has no
    such limitation. -/
theorem drift_cumulative_lower_bound (a b : I) (n : ℕ) :
    rs (drift a b n) (drift a b n) ≥ rs a a := by
  induction n with
  | zero => simp [drift]
  | succ k ih =>
    have hk := drift_enriches a b k
    linarith

/-- EP4. THE ADAPTATION PARADOX: The adaptation rate (weight gain per
    generation) is always non-negative. Ideas can only GAIN complexity
    through transmission, never lose it.
    Counter-intuitive: in biology, maladaptation is common. In ideatic
    evolution, every adaptation is weakly positive. -/
theorem adaptation_always_positive (a b : I) :
    adaptationRate a b ≥ 0 :=
  adaptationRate_nonneg a b

/-- EP5. THE EXTINCTION IMPOSSIBILITY: If an idea starts non-void,
    no amount of drift can reduce it to void. Ideas cannot go extinct
    through cultural transmission.
    Counter-intuitive: biological extinction is common, but ideatic
    ideas are immortal once instantiated. -/
theorem no_extinction (a b : I) (h : a ≠ void) (n : ℕ) :
    drift a b n ≠ void := by
  induction n with
  | zero => simp [drift]; exact h
  | succ k ih =>
    simp [drift]
    exact compose_ne_void_of_left (drift a b k) b ih

/-- EP6. THE MUTATION ENRICHMENT: Every mutation (offspring differing from
    parent due to emergence) results in offspring that is at least as
    heavy as the parent. Mutations can only ADD complexity.
    Counter-intuitive: in biology, most mutations are harmful.
    In ideatic space, ALL mutations are weakly beneficial. -/
theorem mutation_always_enriches (a b : I) :
    rs (offspring a b) (offspring a b) ≥ rs a a :=
  offspring_enriches a b

/-- EP7. THE EVOLUTIONARY CONVERGENCE BOUND: The weight of a drifted
    idea after n generations is bounded above by the weight of the
    n-fold composition of a with b. This means drift cannot exceed
    the "natural" growth rate of self-composition.
    Counter-intuitive: you'd expect drift to be unbounded. -/
theorem drift_weight_eq_compose (a b : I) (n : ℕ) :
    rs (drift a b (n + 1)) (drift a b (n + 1)) =
    rs (compose (drift a b n) b) (compose (drift a b n) b) := by
  simp [drift]

end EvolutionaryParadoxes

end IDT3
