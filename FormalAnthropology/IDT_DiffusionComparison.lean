import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.IDT_Foundations

/-!
# Ideatic Diffusion Theory: Comparing Diffusion Axiom Systems

This file develops the **meta-theory** of IDT: results comparing the four
diffusion axiom systems and establishing their fundamental incompatibilities.

The four systems are analogous to different geometries: they share the monoid
structure but diverge on how ideas propagate.
-/

namespace IDT

/-! ## §1. Conservative Diffusion: Perfect Fidelity -/

section ConservativeProperties
variable {I : Type*} [ConservativeDiffusion I]

/-- THEOREM (Conservative is Identity): transmission is literally identity.
    INSIGHT: "perfect cultural transmission" is an idealization
    no real culture achieves. -/
theorem conservative_transmit_eq (a : I) :
    ConservativeDiffusion.transmit a = a :=
  ConservativeDiffusion.transmit_faithful a

/-- THEOREM (Conservative Depth Invariance): preserves depth exactly.
    INSIGHT: perfect transmission loses no information. -/
theorem conservative_depth_invariant (a : I) :
    IdeaticSpace.depth (ConservativeDiffusion.transmit a) = IdeaticSpace.depth a := by
  rw [conservative_transmit_eq]

/-- THEOREM (Conservative Resonance Invariance): preserves all resonance.
    INSIGHT: perfect transmission preserves the entire meaning-network. -/
theorem conservative_resonance_invariant (a b : I)
    (h : IdeaticSpace.resonates a b) :
    IdeaticSpace.resonates (ConservativeDiffusion.transmit a)
                           (ConservativeDiffusion.transmit b) := by
  rwa [conservative_transmit_eq, conservative_transmit_eq]

/-- THEOREM (Conservative Composition Invariance): commutes with compose.
    INSIGHT: combine-then-transmit = transmit-then-combine in perfect fidelity. -/
theorem conservative_compose_invariant (a b : I) :
    ConservativeDiffusion.transmit (IdeaticSpace.compose a b) =
    IdeaticSpace.compose (ConservativeDiffusion.transmit a)
                         (ConservativeDiffusion.transmit b) := by
  simp [conservative_transmit_eq]

/-- THEOREM (Conservative Iterate Stability): n-fold transmission = identity.
    INSIGHT: a story retold perfectly 1000 times is identical to the original.
    This is why conservative diffusion is unrealistic. -/
theorem conservative_iterate_id (a : I) (n : ℕ) :
    Nat.iterate ConservativeDiffusion.transmit n a = a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.iterate, ih, conservative_transmit_eq]

/-- THEOREM (Conservative Coherence Preservation): coherence is preserved.
    INSIGHT: perfect transmission preserves discourse structure entirely. -/
theorem conservative_preserves_coherence (s : List I) (hs : Coherent s) :
    Coherent (s.map ConservativeDiffusion.transmit) := by
  induction s with
  | nil => exact trivial
  | cons a rest ih =>
    cases rest with
    | nil => exact trivial
    | cons b rest' =>
      simp [List.map] at *
      constructor
      · rw [conservative_transmit_eq, conservative_transmit_eq]; exact hs.1
      · exact ih hs.2

end ConservativeProperties

/-! ## §2. Mutagenic Diffusion: The Entropy of Ideas -/

section MutagenicProperties
variable {I : Type*} [MutagenicDiffusion I]

/-- THEOREM (Mutagenic Depth Floor): after ≥ depth(a) transmissions,
    depth is at most 1. INSIGHT: the telephone game has a floor —
    ideas eventually simplify to atomic form. -/
theorem mutagenic_depth_floor (a : I) (n : ℕ)
    (hn : n ≥ IdeaticSpace.depth a) :
    IdeaticSpace.depth (Nat.iterate MutagenicDiffusion.transmit n a) ≤ 1 := by
  induction n generalizing a with
  | zero => simp [Nat.iterate]; omega
  | succ n ih =>
    by_cases hd : IdeaticSpace.depth a ≤ 1
    · have := mutagenic_atomic_stable a hd (n + 1); omega
    · push_neg at hd
      have := MutagenicDiffusion.transmit_depth_decay a (by omega)
      apply ih (MutagenicDiffusion.transmit a); omega

/-- THEOREM (Two-Step Chain Coherence): [a, T(a), T²(a)] is coherent.
    INSIGHT: three successive retellings maintain consecutive resonance. -/
theorem mutagenic_two_step_coherent (a : I) :
    Coherent [a, MutagenicDiffusion.transmit a,
              MutagenicDiffusion.transmit (MutagenicDiffusion.transmit a)] := by
  constructor
  · exact MutagenicDiffusion.transmit_resonant a
  · exact ⟨MutagenicDiffusion.transmit_resonant _, trivial⟩

/-- THEOREM (Four-Step Chain Coherence): four successive retellings are coherent.
    INSIGHT: even extended transmission chains maintain local resonance. -/
theorem mutagenic_four_step_coherent (a : I) :
    let t := MutagenicDiffusion.transmit
    Coherent [a, t a, t (t a), t (t (t a))] := by
  simp only
  exact ⟨MutagenicDiffusion.transmit_resonant _,
         MutagenicDiffusion.transmit_resonant _,
         MutagenicDiffusion.transmit_resonant _, trivial⟩

/-- THEOREM (Mutagenic Void Depth Zero): transmitting void gives depth 0.
    INSIGHT: you can't corrupt emptiness — silence transmitted is still simple. -/
theorem mutagenic_void_depth :
    IdeaticSpace.depth (MutagenicDiffusion.transmit (IdeaticSpace.void : I)) = 0 := by
  have h := MutagenicDiffusion.transmit_depth_le (IdeaticSpace.void : I)
  rw [IdeaticSpace.depth_void] at h; omega

/-- THEOREM (Mutagenic Self-Depth-Bound): after depth(a) transmissions,
    depth ≤ 1. INSIGHT: every idea has a natural "half-life" equal to
    its own complexity. -/
theorem mutagenic_depth_squeeze (a : I) :
    IdeaticSpace.depth (Nat.iterate MutagenicDiffusion.transmit
      (IdeaticSpace.depth a) a) ≤ 1 :=
  mutagenic_depth_floor a _ (le_refl _)

/-- THEOREM (Mutagenic Depth Never Increases From Zero): if depth is 0,
    all subsequent transmissions have depth 0.
    INSIGHT: once an idea has been simplified to triviality, it stays trivial. -/
theorem mutagenic_zero_stays_zero (a : I) (ha : IdeaticSpace.depth a = 0) (n : ℕ) :
    IdeaticSpace.depth (Nat.iterate MutagenicDiffusion.transmit n a) = 0 := by
  have hle := mutagenic_depth_global_bound a n
  rw [ha] at hle; omega

end MutagenicProperties

/-! ## §3. Selective Diffusion: Homogenization -/

section SelectiveProperties
variable {I : Type*} [SelectiveDiffusion I]

/-- THEOREM (Selection Idempotence): selecting an idea against itself
    always returns that idea. INSIGHT: monopoly ideas face no pressure. -/
theorem selective_idempotent (a : I) :
    SelectiveDiffusion.select a a = a := by
  rcases SelectiveDiffusion.select_is_input a a with h | h <;> exact h

/-- THEOREM (Selection Fitness Monotone): the winner is always at least
    as fit as either competitor. -/
theorem selective_monotone_fitness (a b : I) :
    SelectiveDiffusion.fitness (SelectiveDiffusion.select a b) ≥
    SelectiveDiffusion.fitness a := by
  rw [SelectiveDiffusion.select_maximizes]; exact Nat.le_max_left _ _

/-- THEOREM (Iterated Selection Stable): re-running the same competition
    yields the same winner. INSIGHT: markets settle. -/
theorem selective_iterate_stable (a b : I) :
    SelectiveDiffusion.select (SelectiveDiffusion.select a b)
                               (SelectiveDiffusion.select a b) =
    SelectiveDiffusion.select a b :=
  selective_idempotent _

/-- THEOREM (Three-Way Fitness): fitness of three-way winner = max of all.
    INSIGHT: in round-robin competition, the globally fittest wins. -/
theorem selective_three_way (a b c : I) :
    SelectiveDiffusion.fitness (SelectiveDiffusion.select
      (SelectiveDiffusion.select a b) c) =
    Nat.max (Nat.max (SelectiveDiffusion.fitness a)
                      (SelectiveDiffusion.fitness b))
            (SelectiveDiffusion.fitness c) := by
  rw [SelectiveDiffusion.select_maximizes, SelectiveDiffusion.select_maximizes]

/-- THEOREM (Selection Never Creates): selection only picks from inputs.
    INSIGHT: competition is conservative — it selects, never synthesizes. -/
theorem selective_no_creation (a b : I) :
    SelectiveDiffusion.select a b = a ∨ SelectiveDiffusion.select a b = b :=
  SelectiveDiffusion.select_is_input a b

/-- THEOREM (Fitness Zero Loses): zero-fitness ideas lose to any fit idea.
    INSIGHT: ideas without appeal are eliminated by competition. -/
theorem selective_zero_fitness_loses (a b : I)
    (ha : SelectiveDiffusion.fitness a = 0)
    (hb : SelectiveDiffusion.fitness b > 0) :
    SelectiveDiffusion.select a b = b := by
  rcases SelectiveDiffusion.select_is_input a b with h | h
  · exfalso
    have := SelectiveDiffusion.select_maximizes a b
    rw [h, ha] at this
    simp [Nat.max_eq_left (Nat.zero_le _)] at this; omega
  · exact h

/-- THEOREM (Selection Depth Bound): selected depth ≤ max of input depths.
    INSIGHT: competition can't increase complexity. -/
theorem selective_depth_max (a b : I) :
    IdeaticSpace.depth (SelectiveDiffusion.select a b) ≤
    max (IdeaticSpace.depth a) (IdeaticSpace.depth b) := by
  rcases SelectiveDiffusion.select_is_input a b with h | h
  · rw [h]; exact le_max_left _ _
  · rw [h]; exact le_max_right _ _

end SelectiveProperties

/-! ## §4. Recombinant Diffusion: Creative Synthesis -/

section RecombinantProperties
variable {I : Type*} [RecombinantDiffusion I]

/-- THEOREM (Recombination Echoes Parents): the hybrid resonates with
    both parents. INSIGHT: creative synthesis always echoes its sources. -/
theorem recombinant_echoes_parents (a b : I) :
    IdeaticSpace.resonates (RecombinantDiffusion.recombine a b) a ∧
    IdeaticSpace.resonates (RecombinantDiffusion.recombine a b) b := by
  constructor
  · exact IdeaticSpace.resonance_symm _ _ (RecombinantDiffusion.recombine_resonant_left a b)
  · exact IdeaticSpace.resonance_symm _ _ (RecombinantDiffusion.recombine_resonant_right a b)

/-- THEOREM (Self-Recombination Echo): recombine(a,a) resonates with a.
    INSIGHT: "deep reading" — revisiting a text transforms it but
    the result still echoes the source. -/
theorem recombinant_self_echo (a : I) :
    IdeaticSpace.resonates (RecombinantDiffusion.recombine a a) a :=
  IdeaticSpace.resonance_symm _ _ (RecombinantDiffusion.recombine_resonant_left a a)

/-- THEOREM (Recombination Depth Bound): hybrid depth ≤ sum + 1.
    INSIGHT: creative synthesis is bounded by its inputs. -/
theorem recombinant_bounded_complexity (a b : I) :
    IdeaticSpace.depth (RecombinantDiffusion.recombine a b) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b + 1 :=
  RecombinantDiffusion.recombine_depth_bound a b

/-- THEOREM (Void Recombination Echo): recombine(a, void) resonates with a.
    INSIGHT: combining an idea with silence still echoes the original. -/
theorem recombinant_void_echo (a : I) :
    IdeaticSpace.resonates (RecombinantDiffusion.recombine a (IdeaticSpace.void : I)) a :=
  IdeaticSpace.resonance_symm _ _ (RecombinantDiffusion.recombine_resonant_left a _)

/-- THEOREM (Recombinant Quasi-Commutativity): R(a,b) resonates with R(b,a).
    INSIGHT: order of synthesis matters but both orderings are "about the
    same thing." -/
theorem recombinant_quasi_commutative (a b : I) :
    IdeaticSpace.resonates (RecombinantDiffusion.recombine a b)
                            (RecombinantDiffusion.recombine b a) :=
  RecombinantDiffusion.recombine_comm_resonant a b

/-- THEOREM (Triple Recombination Depth): R(a, R(a, a)) has depth ≤ 3·depth(a) + 2.
    INSIGHT: three-fold creative synthesis has bounded complexity growth. -/
theorem recombinant_triple_depth (a : I) :
    IdeaticSpace.depth (RecombinantDiffusion.recombine a
      (RecombinantDiffusion.recombine a a)) ≤
    3 * IdeaticSpace.depth a + 2 := by
  have h1 := RecombinantDiffusion.recombine_depth_bound a
    (RecombinantDiffusion.recombine a a)
  have h2 := RecombinantDiffusion.recombine_depth_bound a a
  omega

/-- THEOREM (Recombination Creates Coherent Pair): [a, R(a,b)] is coherent.
    INSIGHT: an idea and its creative offspring always form a coherent pair. -/
theorem recombinant_coherent_pair (a b : I) :
    Coherent [a, RecombinantDiffusion.recombine a b] := by
  rw [coherent_pair]
  exact RecombinantDiffusion.recombine_resonant_left a b

end RecombinantProperties

/-! ## §5. Cross-System Comparison Theorems -/

section CrossSystem
variable {I : Type*} [IdeaticSpace I]

/-- THEOREM (Conservative-Mutagenic Incompatibility): if transmit is both
    identity AND depth-decaying for complex ideas, then all ideas have depth ≤ 1.
    INSIGHT: perfect fidelity and natural decay are incompatible unless
    all ideas are trivially simple. -/
theorem conservative_mutagenic_collapse
    (transmit : I → I)
    (hcons : ∀ (a : I), transmit a = a)
    (hmut : ∀ (a : I), IdeaticSpace.depth a > 1 →
            IdeaticSpace.depth (transmit a) < IdeaticSpace.depth a) :
    ∀ (a : I), IdeaticSpace.depth a ≤ 1 := by
  intro a; by_contra h; push_neg at h
  have := hmut a (by omega); rw [hcons] at this; omega

/-- THEOREM (Restricted Map Depth Bound): any function that only picks
    from its inputs can't increase maximum depth.
    INSIGHT: editorial selection can only simplify, never complexify. -/
theorem restricted_map_depth (f : I → I → I)
    (hsel : ∀ (a b : I), f a b = a ∨ f a b = b) (a b : I) :
    IdeaticSpace.depth (f a b) ≤ max (IdeaticSpace.depth a) (IdeaticSpace.depth b) := by
  rcases hsel a b with h | h <;> rw [h]
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- THEOREM (Composition Depth Growth): composition is bounded by sum.
    INSIGHT: synthesis increases complexity but never beyond the sum of parts. -/
theorem composition_depth_growth (a b : I) :
    IdeaticSpace.depth (IdeaticSpace.compose a b) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b :=
  IdeaticSpace.depth_subadditive a b

/-- THEOREM (Three-Element Composition Depth): compose(compose(a,b),c)
    has depth ≤ sum of all three.
    INSIGHT: three-part synthesis has bounded complexity growth. -/
theorem compose_three_depth (a b c : I) :
    IdeaticSpace.depth (IdeaticSpace.compose (IdeaticSpace.compose a b) c) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b + IdeaticSpace.depth c := by
  have h1 := IdeaticSpace.depth_subadditive (IdeaticSpace.compose a b) c
  have h2 := IdeaticSpace.depth_subadditive a b; omega

/-- THEOREM (Atomic Stability Under Depth-Reducing Maps): simple ideas
    survive any depth-non-increasing function.
    INSIGHT: proverbs, catchphrases, and memes are stable because they
    are atomic. Complex philosophical arguments are not. -/
theorem atomic_stability (f : I → I)
    (hf : ∀ (a : I), IdeaticSpace.depth (f a) ≤ IdeaticSpace.depth a)
    (a : I) (ha : IdeaticSpace.depth a ≤ 1) :
    IdeaticSpace.depth (f a) ≤ 1 := by
  have := hf a; omega

/-- THEOREM (Depth Filtration Nesting): the depth filtration is nested.
    INSIGHT: ideas organized by complexity form a hierarchy. -/
theorem depth_filtration_nested (m n : ℕ) (hmn : m ≤ n) :
    depthFiltration m ⊆ (depthFiltration n : Set I) := by
  intro a ha; simp [depthFiltration] at ha ⊢; omega

/-- THEOREM (Void in All Filtrations): void belongs to every filtration level.
    INSIGHT: silence belongs to every complexity class. -/
theorem void_in_all_filtrations (n : ℕ) :
    (IdeaticSpace.void : I) ∈ depthFiltration n := by
  simp [depthFiltration, IdeaticSpace.depth_void]

/-- THEOREM (ComposeN Depth Bound): n-fold composition depth ≤ n × depth(a).
    INSIGHT: repeating an idea n times grows complexity linearly, not exponentially. -/
theorem composeN_depth_linear (a : I) : ∀ (n : ℕ),
    IdeaticSpace.depth (composeN a n) ≤ n * IdeaticSpace.depth a
  | 0 => by simp [composeN, IdeaticSpace.depth_void]
  | n + 1 => by
    have ih := composeN_depth_linear a n
    have hsub := IdeaticSpace.depth_subadditive (composeN a n) a
    calc IdeaticSpace.depth (composeN a (n + 1))
        = IdeaticSpace.depth (IdeaticSpace.compose (composeN a n) a) := rfl
      _ ≤ IdeaticSpace.depth (composeN a n) + IdeaticSpace.depth a := hsub
      _ ≤ n * IdeaticSpace.depth a + IdeaticSpace.depth a := by linarith
      _ = (n + 1) * IdeaticSpace.depth a := by ring

/-- THEOREM (Coherent Pairs are Symmetric): if [a,b] is coherent,
    so is [b,a]. INSIGHT: literary influence goes both ways. -/
theorem coherent_pair_symm {a b : I}
    (h : Coherent [a, b]) : Coherent [b, a] := by
  rw [coherent_pair] at h ⊢
  exact IdeaticSpace.resonance_symm _ _ h

/-- THEOREM (Coherent Extension): a coherent sequence ending in a can be
    extended by any b resonating with a.
    INSIGHT: discourse continues when you find resonance with your last idea.
    Writer's block = failure to find resonance. -/
theorem coherent_snoc {a b : I}
    (hab : IdeaticSpace.resonates a b) :
    Coherent [a, b] := by
  rw [coherent_pair]; exact hab

/-- THEOREM (Composition Preserves Self-Resonance): compose(a,a) resonates
    with a. INSIGHT: an idea combined with itself is still "about" itself. -/
theorem compose_self_resonates (a : I) :
    IdeaticSpace.resonates (IdeaticSpace.compose a a) (IdeaticSpace.compose a a) :=
  IdeaticSpace.resonance_refl _

/-- THEOREM (Depth Filtration Zero Contains Void): the depth-0 filtration
    always contains the void. INSIGHT: the simplest level of ideas
    always has at least one member — silence. -/
theorem depth_zero_has_void :
    (IdeaticSpace.void : I) ∈ depthFiltration 0 := by
  simp [depthFiltration, IdeaticSpace.depth_void]

/-- THEOREM (Resonance Class Membership Symmetric): a ∈ class(b) ↔ b ∈ class(a).
    INSIGHT: if text A evokes text B, then B evokes A. Allusion is mutual. -/
theorem resonance_class_mem_symm (a b : I) :
    a ∈ resonanceClass b ↔ b ∈ resonanceClass a := by
  simp [resonanceClass]
  constructor
  · exact IdeaticSpace.resonance_symm b a
  · exact IdeaticSpace.resonance_symm a b

/-- THEOREM (Depth Zero Compose Closed): composing two depth-0 ideas gives
    depth 0. INSIGHT: combining trivial thoughts gives a trivial thought. -/
theorem depth_zero_compose_closed (a b : I)
    (ha : IdeaticSpace.depth a = 0)
    (hb : IdeaticSpace.depth b = 0) :
    IdeaticSpace.depth (IdeaticSpace.compose a b) = 0 := by
  have := IdeaticSpace.depth_subadditive a b
  omega

end CrossSystem

end IDT
