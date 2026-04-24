import FormalAnthropology.IDT_Foundations_v2

/-!
# IDT v2: Evolutionary Dynamics

Evolutionary dynamics in the ideatic space. Ideas compete, mutate, and spread.
Evolutionary stability is defined via resonance-based fitness payoffs.

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT2.Evolution

open IDT2
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-! ## §1. Iterated Ideas -/

/-- Iterated self-composition: repeating an idea n times -/
def iterateIdea (a : I) (n : ℕ) : I := composeN a n

@[simp] theorem iterateIdea_zero (a : I) : iterateIdea a 0 = (void : I) := rfl

theorem iterateIdea_one (a : I) : iterateIdea a 1 = a := composeN_one a

theorem iterateIdea_succ (a : I) (n : ℕ) :
    iterateIdea a (n + 1) = compose (iterateIdea a n) a := rfl

@[simp] theorem iterateIdea_void (n : ℕ) :
    iterateIdea (void : I) n = (void : I) := composeN_void n

theorem iterateIdea_depth_bound (a : I) (n : ℕ) :
    depth (iterateIdea a n) ≤ n * depth a := depth_composeN_le a n

theorem iterate_compose_add (a : I) (m n : ℕ) :
    iterateIdea a (m + n) = compose (iterateIdea a m) (iterateIdea a n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    show compose (iterateIdea a (m + n)) a =
         compose (iterateIdea a m) (compose (iterateIdea a n) a)
    rw [ih, compose_assoc]

/-! ## §2. Fitness and Invasion -/

/-- A strategy's fitness against an opponent: how well strategy resonates
    with its own composition against the opponent -/
noncomputable def fitness (strategy opponent : I) : ℝ :=
  resonanceStrength strategy (compose strategy opponent)

/-- A mutant invades if it has higher fitness against the resident -/
def invades (mutant resident : I) : Prop :=
  fitness mutant resident > fitness resident resident

/-- Evolutionarily stable: no mutant can invade -/
def ESS (resident : I) : Prop :=
  ∀ (mutant : I), ¬invades mutant resident

/-- The fitness gap between mutant and resident -/
noncomputable def fitnessGap (mutant resident : I) : ℝ :=
  fitness mutant resident - fitness resident resident

/-- Neutral interaction: neither can invade the other -/
def isNeutral (a b : I) : Prop :=
  ¬invades a b ∧ ¬invades b a

/-- Combined fitness of a pair -/
noncomputable def mutualFitness (a b : I) : ℝ :=
  fitness a b + fitness b a

/-! ## §3. Basic Fitness Properties -/

theorem fitness_nonneg (s r : I) : fitness s r ≥ 0 :=
  IdeaticSpace2.rs_nonneg s _

theorem fitness_void_opponent (s : I) :
    fitness s (void : I) = resonanceStrength s s := by
  unfold fitness; simp

theorem void_fitness (r : I) :
    fitness (void : I) r = resonanceStrength (void : I) r := by
  unfold fitness; simp

theorem void_self_fitness :
    fitness (void : I) (void : I) = 1 := by
  rw [void_fitness]; exact rs_void_unit

theorem fitness_void_opponent_ge_one (s : I) :
    fitness s (void : I) ≥ 1 := by
  rw [fitness_void_opponent]; exact rs_self_ge_one s

/-- Fitness of any strategy against any opponent is at least rs(void, opponent) -/
theorem fitness_lower_bound (s r : I) :
    fitness s r ≥ resonanceStrength (void : I) r := by
  unfold fitness
  have key := IdeaticSpace2.rs_compose_left_mono (void : I) r s
  simp at key
  exact key

/-! ## §4. Invasion and ESS -/

theorem invades_irrefl (a : I) : ¬invades a a := by
  unfold invades; linarith

theorem fitnessGap_self (a : I) : fitnessGap a a = 0 := by
  unfold fitnessGap; linarith

theorem fitnessGap_pos_iff_invades (m r : I) :
    fitnessGap m r > 0 ↔ invades m r := by
  unfold fitnessGap invades; constructor <;> intro h <;> linarith

theorem isNeutral_refl (a : I) : isNeutral a a :=
  ⟨invades_irrefl a, invades_irrefl a⟩

theorem isNeutral_symm (a b : I) : isNeutral a b → isNeutral b a := by
  intro ⟨h1, h2⟩; exact ⟨h2, h1⟩

theorem ESS_iff_nonpositive_gap (r : I) :
    ESS r ↔ ∀ (m : I), fitnessGap m r ≤ 0 := by
  constructor
  · intro h m
    by_contra hc
    push_neg at hc
    exact h m ((fitnessGap_pos_iff_invades m r).mp hc)
  · intro h m hm
    have hg := (fitnessGap_pos_iff_invades m r).mpr hm
    linarith [h m]

theorem ESS_implies_maximal (r : I) (h : ESS r) (m : I) :
    fitness m r ≤ fitness r r := by
  have hg := (ESS_iff_nonpositive_gap r).mp h m
  unfold fitnessGap at hg; linarith

/-! ## §5. Void and ESS -/

/-- Any idea with self-resonance > 1 invades the void -/
theorem void_invaded_by_strong (m : I) (h : resonanceStrength m m > 1) :
    invades m (void : I) := by
  unfold invades
  have h1 := fitness_void_opponent (I := I) m
  have h2 := void_self_fitness (I := I)
  linarith

/-- Void is ESS iff all ideas have self-resonance ≤ 1 -/
theorem ESS_void_iff :
    ESS (void : I) ↔ ∀ (m : I), resonanceStrength m m ≤ 1 := by
  constructor
  · intro h m
    by_contra hc
    push_neg at hc
    exact h m (void_invaded_by_strong m hc)
  · intro h m hm
    have h1 := fitness_void_opponent (I := I) m
    have h2 := void_self_fitness (I := I)
    unfold invades at hm; linarith [h m]

/-! ## §6. Iterated Resonance -/

theorem iterate_rs_mono (a : I) (n : ℕ) :
    resonanceStrength (iterateIdea a (n + 1)) (iterateIdea a (n + 1)) ≥
    resonanceStrength (iterateIdea a n) (iterateIdea a n) :=
  rs_self_composeN_mono a n

theorem iterate_rs_ge_one (a : I) (n : ℕ) :
    resonanceStrength (iterateIdea a n) (iterateIdea a n) ≥ 1 :=
  rs_composeN_ge_one a n

theorem iterate_rs_ge_base (a : I) : ∀ (n : ℕ),
    resonanceStrength (iterateIdea a n) (iterateIdea a n) ≥
    resonanceStrength (iterateIdea a 0) (iterateIdea a 0)
  | 0 => le_refl _
  | n + 1 => by linarith [iterate_rs_mono (I := I) a n, iterate_rs_ge_base a n]

/-! ## §7. Fitness Composition -/

/-- Composing more structure into a strategy increases its fitness against void -/
theorem fitness_compose_void_mono (a b : I) :
    fitness (compose a b) (void : I) ≥ fitness a (void : I) := by
  rw [fitness_void_opponent, fitness_void_opponent]
  exact rs_compose_self_right a b

/-- Fitness against void grows with iteration -/
theorem fitness_iterate_void_mono (a : I) (n : ℕ) :
    fitness (iterateIdea a (n + 1)) (void : I) ≥
    fitness (iterateIdea a n) (void : I) := by
  rw [fitness_void_opponent, fitness_void_opponent]
  exact iterate_rs_mono a n

/-! ## §8. Mutual Fitness -/

theorem mutualFitness_comm (a b : I) : mutualFitness a b = mutualFitness b a := by
  unfold mutualFitness; ring

theorem mutualFitness_nonneg (a b : I) : mutualFitness a b ≥ 0 := by
  unfold mutualFitness
  linarith [fitness_nonneg (I := I) a b, fitness_nonneg (I := I) b a]

theorem mutualFitness_void (a : I) :
    mutualFitness a (void : I) =
    resonanceStrength a a + resonanceStrength (void : I) a := by
  unfold mutualFitness
  rw [fitness_void_opponent, void_fitness]

theorem mutualFitness_void_ge_one (a : I) :
    mutualFitness a (void : I) ≥ 1 := by
  rw [mutualFitness_void]
  linarith [rs_self_ge_one (I := I) a, rs_nonneg' (I := I) (void : I) a]

end IDT2.Evolution
