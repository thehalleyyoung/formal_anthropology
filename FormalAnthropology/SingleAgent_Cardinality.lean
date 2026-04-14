/-
AUTO-AUDIT 2026-02-08
Current assumptions summary:
- Theorems in this file use explicit binder hypotheses/typeclass assumptions in their signatures.
- Global axiom declarations: none.
- sorry/admit occurrences: none.
Potential weakening targets:
- No non-derivable assumptions were found beyond explicit theorem hypotheses.
-/

/-
# Single-Agent Ideogenesis: Cardinality Theorems

From FORMAL_ANTHROPOLOGY++ Chapter 4.2 (Theorems 4.5-4.7):
- Theorem 4.5: Finitary Bound - finitary systems with finite seeds have countable closures
- Theorem 4.6: Uncountable Generation conditions
- Theorem 4.7: Diagonal Uncountability - injective enumeration implies infinite closure

These theorems establish the cardinality constraints on ideogenetic systems,
showing when closures remain countable and when they can become uncountable.
-/

import FormalAnthropology.SingleAgent_Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Card
import Mathlib.Tactic

namespace SingleAgentIdeogenesis

/-! ## Theorem 4.5: Finitary Bound -/

/-- In a finitary system, genStep of a finite set is finite -/
theorem genStep_finite (S : IdeogeneticSystem) (hS : isFinitary S) 
    (A : Set S.Idea) (hA : A.Finite) : (genStep S A).Finite := by
  unfold genStep
  apply Set.Finite.biUnion hA
  intro a _
  exact hS a

/-- In a finitary system with finite seed, each generation stage is finite (Theorem 4.5, part 1) -/
theorem genCumulative_finite (S : IdeogeneticSystem) (hS : isFinitary S) 
    (A : Set S.Idea) (hA : A.Finite) (n : ℕ) : (genCumulative S n A).Finite := by
  induction n with
  | zero => exact hA
  | succ n ih =>
    unfold genCumulative
    exact Set.Finite.union ih (genStep_finite S hS (genCumulative S n A) ih)

/-- In a finitary system with finite seed, the closure is at most countable (Theorem 4.5, part 3) -/
theorem closure_countable (S : IdeogeneticSystem) (hS : isFinitary S) 
    (A : Set S.Idea) (hA : A.Finite) : (closure S A).Countable := by
  unfold closure
  apply Set.countable_iUnion
  intro n
  exact Set.Finite.countable (genCumulative_finite S hS A hA n)

/-- Finitary with singleton primordial has countable primordial closure (Theorem 4.5 corollary) -/
theorem primordialClosure_countable (S : IdeogeneticSystem) (hS : isFinitary S) :
    (primordialClosure S).Countable := by
  apply closure_countable S hS
  exact Set.finite_singleton _

/-- The cardinality of each generation stage is bounded -/
theorem genCumulative_card_bound (S : IdeogeneticSystem) (hS : isFinitary S)
    (A : Set S.Idea) (hA : A.Finite) (n : ℕ) :
    (genCumulative S n A).Finite := genCumulative_finite S hS A hA n

/-! ## Theorem 4.6: Uncountable Generation Conditions -/

/-- If closure is uncountable, then either the seed is infinite, or the system is not finitary.
    Contrapositive: finitary + finite seed implies countable. -/
theorem uncountable_requires_infinite_or_nonfinitary (S : IdeogeneticSystem)
    (A : Set S.Idea) (huncountable : ¬(closure S A).Countable) :
    ¬A.Finite ∨ ¬isFinitary S := by
  by_contra h
  push_neg at h
  obtain ⟨hAfin, hSfin⟩ := h
  exact huncountable (closure_countable S hSfin A hAfin)

/-- A system with bounded branching factor: each idea generates at most k successors -/
def hasBoundedBranching (S : IdeogeneticSystem) (k : ℕ) : Prop :=
  ∀ a, (S.generate a).Finite ∧ (S.generate a).encard ≤ k

/-- Bounded branching implies finitary -/
theorem bounded_branching_finitary (S : IdeogeneticSystem) (k : ℕ) 
    (hbnd : hasBoundedBranching S k) : isFinitary S := by
  intro a
  exact (hbnd a).1

/-- A system with bounded branching has generation stages with bounded growth -/
theorem bounded_branching_stage_bound (S : IdeogeneticSystem) (k : ℕ) 
    (hbnd : hasBoundedBranching S k) (A : Set S.Idea) (hA : A.Finite) (n : ℕ) :
    (genCumulative S n A).Finite := by
  exact genCumulative_finite S (bounded_branching_finitary S k hbnd) A hA n

/-! ## Theorem 4.7: Diagonal Uncountability -/

/-- Systems with injection from ℕ to closure have infinite closure -/
theorem injection_implies_infinite (S : IdeogeneticSystem)
    (f : ℕ → S.Idea) (hf : Function.Injective f) 
    (hfin : ∀ n, f n ∈ primordialClosure S) :
    (primordialClosure S).Infinite := by
  apply Set.infinite_of_injective_forall_mem hf hfin

/-- A stronger diagonal capability: an injective enumeration where all elements are reachable -/
def hasInjectiveEnumeration (S : IdeogeneticSystem) : Prop :=
  ∃ (f : ℕ → S.Idea), Function.Injective f ∧ ∀ n, f n ∈ primordialClosure S

/-- If a system has an injective enumeration, its closure is infinite (Theorem 4.7) -/
theorem diagonal_infinite (S : IdeogeneticSystem) 
    (hdiag : hasInjectiveEnumeration S) : 
    (primordialClosure S).Infinite := by
  obtain ⟨f, hf_inj, hf_mem⟩ := hdiag
  exact injection_implies_infinite S f hf_inj hf_mem

/-! ## Example: Natural Number Successor System -/

/-- The natural number successor system: ℕ with successor operation -/
def natSuccSystem : IdeogeneticSystem where
  Idea := ℕ
  generate := fun n => {n + 1}
  primordial := (0 : ℕ)

/-- Each natural number is reachable at stage n -/
theorem nat_reachable_at_n (n : ℕ) : n ∈ genCumulative natSuccSystem n {natSuccSystem.primordial} := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold genCumulative genStep
    right
    simp only [Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨n, ih, rfl⟩

/-- natSuccSystem has infinite closure (Theorem 4.7 example) -/
theorem natSuccSystem_infinite : (primordialClosure natSuccSystem).Infinite := by
  apply diagonal_infinite
  use _root_.id
  constructor
  · exact fun _ _ h => h
  · intro n
    simp only [primordialClosure, closure, Set.mem_iUnion, _root_.id]
    exact ⟨n, nat_reachable_at_n n⟩

/-- natSuccSystem is finitary (generates exactly one successor) -/
theorem natSuccSystem_finitary : isFinitary natSuccSystem := by
  intro a
  exact Set.finite_singleton _

/-- Even finitary systems can have infinite closures if the seed leads to infinite growth -/
theorem finitary_can_be_infinite :
    isFinitary natSuccSystem ∧ (primordialClosure natSuccSystem).Infinite :=
  ⟨natSuccSystem_finitary, natSuccSystem_infinite⟩

/-! ## Cardinality Dichotomy -/

/-- Either a system has finite closure, or it has an infinite closure -/
theorem closure_finite_or_infinite (S : IdeogeneticSystem) (A : Set S.Idea) :
    (closure S A).Finite ∨ (closure S A).Infinite := by
  by_cases h : (closure S A).Finite
  · left; exact h
  · right; exact h

/-- If closure is infinite and countable, there exists an injection from ℕ.
    This is a direct consequence of the fact that infinite countable sets
    are equinumerous with ℕ. -/
theorem infinite_countable_has_injection (S : IdeogeneticSystem) (A : Set S.Idea)
    (hinf : (closure S A).Infinite) (_hcount : (closure S A).Countable) :
    ∃ (f : ℕ → S.Idea), Function.Injective f ∧ ∀ n, f n ∈ closure S A := by
  -- From infinite + countable, the subtype is denumerable
  haveI : Infinite (closure S A) := Set.infinite_coe_iff.mpr hinf
  haveI : Countable (closure S A) := Set.Countable.to_subtype _hcount
  -- Countable.exists_injective_nat gives an injection
  have : ∃ f : ℕ → (closure S A), Function.Injective f := by
    -- Infinite countable types have injections from ℕ
    -- Actually use that Infinite implies embedding from ℕ
    have hemb := Infinite.natEmbedding (closure S A)
    exact ⟨hemb, hemb.injective⟩
  obtain ⟨f, hf⟩ := this
  use fun n => (f n).val
  constructor
  · intro m n hmn
    have heq : f m = f n := Subtype.val_injective hmn
    exact hf heq
  · intro n
    exact (f n).prop

/-- Countably infinite systems are "maximally infinite" among finitary systems -/
theorem finitary_at_most_countable (S : IdeogeneticSystem) (hS : isFinitary S)
    (A : Set S.Idea) (hA : A.Finite) :
    (closure S A).Finite ∨ ((closure S A).Countable ∧ (closure S A).Infinite) := by
  by_cases hfin : (closure S A).Finite
  · left; exact hfin
  · right
    exact ⟨closure_countable S hS A hA, hfin⟩

/-! ## Depth and Cardinality -/

/-- In a finitary system, ideas at each depth form a finite set -/
def ideasAtDepth (S : IdeogeneticSystem) (A : Set S.Idea) (d : ℕ) : Set S.Idea :=
  {a ∈ closure S A | depth S A a = d}

/-- The set of ideas at depth 0 is exactly the seed elements with depth 0 -/
theorem ideasAtDepth_zero (S : IdeogeneticSystem) (A : Set S.Idea) :
    ideasAtDepth S A 0 = {a ∈ A | depth S A a = 0} := by
  ext a
  simp only [ideasAtDepth, Set.mem_sep_iff]
  constructor
  · intro ⟨ha_closure, ha_depth⟩
    constructor
    · -- If depth is 0, then a ∈ genCumulative 0 A = A
      have hcum : a ∈ genCumulative S 0 A := by
        rw [← ha_depth]
        exact mem_genCumulative_depth S A a ha_closure
      exact hcum
    · exact ha_depth
  · intro ⟨ha_A, ha_depth⟩
    constructor
    · exact seed_in_closure S A ha_A
    · exact ha_depth

/-- Ideas at depth d+1 come from generation of ideas at depth ≤ d -/
theorem ideasAtDepth_succ_subset (S : IdeogeneticSystem) (A : Set S.Idea) (d : ℕ) :
    ideasAtDepth S A (d + 1) ⊆ 
    {a | ∃ b ∈ closure S A, depth S A b ≤ d ∧ a ∈ S.generate b} := by
  intro a ⟨ha_closure, ha_depth⟩
  -- a has depth d+1, so it first appears at stage d+1
  have hmem : a ∈ genCumulative S (d + 1) A := by
    rw [← ha_depth]
    exact mem_genCumulative_depth S A a ha_closure
  -- But it's not in stage d
  have hnotmem : a ∉ genCumulative S d A := by
    intro h
    have hle : depth S A a ≤ d := depth_le_of_mem S A a d h
    omega
  -- So it must come from genStep at stage d+1
  unfold genCumulative at hmem
  cases hmem with
  | inl h => exact absurd h hnotmem
  | inr h =>
    unfold genStep at h
    simp only [Set.mem_iUnion] at h
    obtain ⟨b, hb_cum, hab⟩ := h
    use b
    constructor
    · simp only [closure, Set.mem_iUnion]
      exact ⟨d, hb_cum⟩
    constructor
    · exact depth_le_of_mem S A b d hb_cum
    · exact hab

/-! ## Cardinality Preservation Under Morphisms -/

/-- A morphism between ideogenetic systems -/
structure IdeogeneticMorphism (S T : IdeogeneticSystem) where
  /-- The underlying function on ideas -/
  mapIdea : S.Idea → T.Idea
  /-- Maps primordial to primordial -/
  map_primordial : mapIdea S.primordial = T.primordial
  /-- Preserves generation -/
  map_generate : ∀ a b, b ∈ S.generate a → mapIdea b ∈ T.generate (mapIdea a)

/-- A morphism maps closure to closure -/
theorem morphism_maps_closure (S T : IdeogeneticSystem)
    (φ : IdeogeneticMorphism S T) :
    ∀ a ∈ primordialClosure S, φ.mapIdea a ∈ primordialClosure T := by
  intro a ha
  simp only [primordialClosure, closure, Set.mem_iUnion] at ha ⊢
  obtain ⟨n, hn⟩ := ha
  induction n generalizing a with
  | zero => 
    simp only [genCumulative, Set.mem_singleton_iff] at hn
    use 0
    simp only [genCumulative, Set.mem_singleton_iff]
    rw [hn, φ.map_primordial]
  | succ n ih =>
    unfold genCumulative at hn
    cases hn with
    | inl h => exact ih a h
    | inr h =>
      unfold genStep at h
      simp only [Set.mem_iUnion] at h
      obtain ⟨b, hb, hab⟩ := h
      obtain ⟨m, hm⟩ := ih b hb
      use m + 1
      unfold genCumulative genStep
      right
      simp only [Set.mem_iUnion]
      exact ⟨φ.mapIdea b, hm, φ.map_generate b a hab⟩

/-- An injective morphism reflects finiteness -/
theorem injective_morphism_reflects_finite (S T : IdeogeneticSystem)
    (φ : IdeogeneticMorphism S T) (hinj : Function.Injective φ.mapIdea)
    (hfin : (primordialClosure T).Finite) :
    (primordialClosure S).Finite := by
  -- The morphism maps S's closure into T's closure
  -- Since φ is injective and maps S's closure into a finite set
  have himg : φ.mapIdea '' primordialClosure S ⊆ primordialClosure T := by
    intro x hx
    simp only [Set.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact morphism_maps_closure S T φ a ha
  have himg_fin : (φ.mapIdea '' primordialClosure S).Finite := Set.Finite.subset hfin himg
  have hinj_on : Set.InjOn φ.mapIdea (primordialClosure S) := fun x _ y _ h => hinj h
  exact Set.Finite.of_finite_image himg_fin hinj_on

/-- An injective morphism preserves infinite cardinality -/
theorem injective_morphism_preserves_infinite (S T : IdeogeneticSystem)
    (φ : IdeogeneticMorphism S T) (hinj : Function.Injective φ.mapIdea)
    (hinf : (primordialClosure S).Infinite) :
    (primordialClosure T).Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  have := injective_morphism_reflects_finite S T φ hinj hfin
  exact hinf this

end SingleAgentIdeogenesis
