import FormalAnthropology.IDT_Foundations

/-!
# Literary Influence Theory in IDT

Formalizes Harold Bloom's "anxiety of influence," Julia Kristeva's intertextuality,
canon formation under mutagenic diffusion, and translation theory using Ideatic
Diffusion Theory.

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

set_option autoImplicit false

namespace IDT

/-! ## §1. The Influence Relation -/

section Influence
variable {I : Type*} [IdeaticSpace I]

/-- **Influence**: idea `a` influences idea `b` when `b` resonates with `a`
    and `b` is at least as deep.
    LITERARY INSIGHT: influence = resonance + growth in complexity. -/
def Influences (a b : I) : Prop :=
  IdeaticSpace.resonates a b ∧ IdeaticSpace.depth a ≤ IdeaticSpace.depth b

/-- Every idea influences itself.
    LITERARY INSIGHT: every text is its own precursor in the weakest sense. -/
theorem influences_refl (a : I) : Influences a a :=
  ⟨IdeaticSpace.resonance_refl a, le_refl _⟩

/-- Influence depth is transitive.
    LITERARY INSIGHT: through a lineage Homer to Virgil to Dante,
    depth can only accumulate. -/
theorem influences_depth_trans {a b c : I}
    (hab : Influences a b) (hbc : Influences b c) :
    IdeaticSpace.depth a ≤ IdeaticSpace.depth c :=
  le_trans hab.2 hbc.2

/-- Influence implies a depth ordering. -/
theorem influences_depth_le {a b : I} (h : Influences a b) :
    IdeaticSpace.depth a ≤ IdeaticSpace.depth b := h.2

/-- Influence implies resonance: the precursor's echo is always detectable.
    LITERARY INSIGHT: influence leaves traces. -/
theorem influences_resonance {a b : I} (h : Influences a b) :
    IdeaticSpace.resonates a b := h.1

/-- Mutual influence implies equal depth.
    LITERARY INSIGHT: mutual influence implies equal complexity —
    "peer influence" vs. "master-student." -/
theorem mutual_influence_depth_eq {a b : I}
    (hab : Influences a b) (hba : Influences b a) :
    IdeaticSpace.depth a = IdeaticSpace.depth b := by
  have h1 := hab.2; have h2 := hba.2; omega

/-- Composing with void preserves influence (right). -/
theorem influences_void_compose_right {a b : I} (h : Influences a b) :
    Influences a (IdeaticSpace.compose b (IdeaticSpace.void : I)) := by
  constructor
  · rw [IdeaticSpace.void_right]; exact h.1
  · rw [IdeaticSpace.void_right]; exact h.2

/-- Composing with void preserves influence (left). -/
theorem influences_void_compose_left {a b : I} (h : Influences a b) :
    Influences a (IdeaticSpace.compose (IdeaticSpace.void : I) b) := by
  constructor
  · rw [IdeaticSpace.void_left]; exact h.1
  · rw [IdeaticSpace.void_left]; exact h.2

/-- Void influences void.
    LITERARY INSIGHT: silence influences silence — trivially. -/
theorem void_influences_void : Influences (IdeaticSpace.void : I) (IdeaticSpace.void : I) :=
  influences_refl _

/-- If a influences b, composing both with the same idea c on the right
    preserves the resonance part.
    LITERARY INSIGHT: adding the same context preserves evocative structure. -/
theorem influences_compose_context {a b : I} (h : Influences a b) (c : I) :
    IdeaticSpace.resonates (IdeaticSpace.compose a c) (IdeaticSpace.compose b c) :=
  IdeaticSpace.resonance_compose a b c c h.1 (IdeaticSpace.resonance_refl c)

end Influence

/-! ## §2. Anxiety of Influence (Harold Bloom) -/

section AnxietyOfInfluence
variable {I : Type*} [IdeaticSpace I]

/-- A **strong misreading** (Bloom) transforms ideas while maintaining resonance
    and strictly increasing depth.
    LITERARY INSIGHT: the strong poet transforms the precursor into something
    more complex — the anxiety is that excess complexity is necessary. -/
def IsStrongMisreading (phi : I -> I) : Prop :=
  forall (a : I), IdeaticSpace.resonates a (phi a) ∧ IdeaticSpace.depth (phi a) > IdeaticSpace.depth a

/-- Strong misreadings always increase depth.
    LITERARY INSIGHT: this is why strong poets are rare. -/
theorem strong_misreading_increases_depth {phi : I -> I} (hphi : IsStrongMisreading phi) (a : I) :
    IdeaticSpace.depth (phi a) > IdeaticSpace.depth a :=
  (hphi a).2

/-- A strong misreading establishes influence. -/
theorem strong_misreading_is_influence {phi : I -> I} (hphi : IsStrongMisreading phi) (a : I) :
    Influences a (phi a) :=
  ⟨(hphi a).1, le_of_lt (hphi a).2⟩

/-- Iterating a strong misreading strictly increases depth at each step.
    LITERARY INSIGHT: each generation of strong poets adds complexity. -/
theorem strong_misreading_iterated_depth {phi : I -> I} (hphi : IsStrongMisreading phi)
    (a : I) : forall (n : Nat),
    IdeaticSpace.depth (Nat.iterate phi (n + 1) a) >
    IdeaticSpace.depth (Nat.iterate phi n a)
  | 0 => (hphi a).2
  | n + 1 => strong_misreading_iterated_depth hphi (phi a) n

/-- After n strong misreadings, depth has increased by at least n.
    LITERARY INSIGHT: "standing on the shoulders of giants." -/
theorem strong_misreading_depth_growth {phi : I -> I} (hphi : IsStrongMisreading phi)
    (a : I) : forall (n : Nat),
    IdeaticSpace.depth (Nat.iterate phi n a) >= IdeaticSpace.depth a + n
  | 0 => by simp [Nat.iterate]
  | n + 1 => by
    have ih := strong_misreading_depth_growth hphi (phi a) n
    have step := (hphi a).2
    simp [Nat.iterate] at ih ⊢
    omega

/-- Strong misreadings form chains of influence. -/
theorem strong_misreading_chain_influences {phi : I -> I} (hphi : IsStrongMisreading phi)
    (a : I) : forall (n : Nat),
    Influences (Nat.iterate phi n a) (Nat.iterate phi (n + 1) a)
  | 0 => strong_misreading_is_influence hphi a
  | n + 1 => strong_misreading_chain_influences hphi (phi a) n

/-- Strong misreadings preserve resonance with the original. -/
theorem strong_misreading_resonance {phi : I -> I} (hphi : IsStrongMisreading phi) (a : I) :
    IdeaticSpace.resonates a (phi a) :=
  (hphi a).1

/-- Consecutive strong misreadings produce resonant neighbors.
    LITERARY INSIGHT: the chain of strong poets is coherent. -/
theorem strong_misreading_chain_resonance {phi : I -> I} (hphi : IsStrongMisreading phi)
    (a : I) : forall (n : Nat),
    IdeaticSpace.resonates (Nat.iterate phi n a) (Nat.iterate phi (n + 1) a)
  | 0 => (hphi a).1
  | n + 1 => strong_misreading_chain_resonance hphi (phi a) n

/-- Strong misreadings produce ideas of depth at least 1.
    LITERARY INSIGHT: the strong poet's response is always substantial. -/
theorem strong_misreading_nontrivial {phi : I -> I} (hphi : IsStrongMisreading phi) (a : I) :
    IdeaticSpace.depth (phi a) >= 1 := by
  have := (hphi a).2; omega

end AnxietyOfInfluence

/-! ## §3. Canon Formation Under Mutagenic Diffusion -/

section Canon
variable {I : Type*} [MutagenicDiffusion I]

/-- A **canonical idea** is a fixed point of mutagenic transmission.
    LITERARY INSIGHT: the canon consists of ideas that survive unchanged. -/
def IsCanonical (a : I) : Prop :=
  MutagenicDiffusion.transmit a = a

/-- Canonical ideas have depth at most 1.
    LITERARY INSIGHT: only ideas simple enough to resist erosion survive.
    What endures is not the most complex but the most robust. -/
theorem canonical_depth_le_one {a : I} (hcan : IsCanonical a) :
    IdeaticSpace.depth a <= 1 := by
  by_contra h
  push_neg at h
  have hdecay := MutagenicDiffusion.transmit_depth_decay a (by omega)
  rw [hcan] at hdecay
  omega

/-- A **depth-stable** idea is one whose depth does not change under transmission. -/
def IsDepthStable (a : I) : Prop :=
  IdeaticSpace.depth (MutagenicDiffusion.transmit a) = IdeaticSpace.depth a

/-- Depth-stable ideas have depth at most 1.
    LITERARY INSIGHT: only simple ideas maintain their depth. -/
theorem depth_stable_le_one {a : I} (hstab : IsDepthStable a) :
    IdeaticSpace.depth a <= 1 := by
  by_contra h
  push_neg at h
  have hdecay := MutagenicDiffusion.transmit_depth_decay a (by omega)
  rw [hstab] at hdecay
  omega

/-- After depth(a) transmissions, any idea reaches depth at most 1.
    LITERARY INSIGHT: the long run of cultural transmission always
    produces simple ideas — canonization through simplification. -/
theorem eventual_canonization (a : I) :
    IdeaticSpace.depth (Nat.iterate MutagenicDiffusion.transmit (IdeaticSpace.depth a) a) <= 1 := by
  cases h : IdeaticSpace.depth a with
  | zero =>
    simp [Nat.iterate]
    omega
  | succ n =>
    show IdeaticSpace.depth (Nat.iterate MutagenicDiffusion.transmit n
      (MutagenicDiffusion.transmit a)) <= 1
    apply mutagenic_eventual_shallow
    have := MutagenicDiffusion.transmit_depth_le a
    omega

/-- Canonical implies depth-stable. -/
theorem canonical_is_depth_stable {a : I} (h : IsCanonical a) : IsDepthStable a := by
  unfold IsDepthStable; rw [h]

/-- Ideas at depth at most 1 stay at depth at most 1 forever.
    LITERARY INSIGHT: once simplified, ideas remain simple. -/
theorem canonized_stays_shallow {a : I} (h : IdeaticSpace.depth a <= 1) (n : Nat) :
    IdeaticSpace.depth (Nat.iterate MutagenicDiffusion.transmit n a) <= 1 :=
  mutagenic_atomic_stable a h n

/-- Mutagenic transmission always resonates with the original. -/
theorem canon_resonance (a : I) :
    IdeaticSpace.resonates a (MutagenicDiffusion.transmit a) :=
  MutagenicDiffusion.transmit_resonant a

/-- Each step in a transmission chain resonates with the next. -/
theorem canon_chain_resonance (a : I) (n : Nat) :
    IdeaticSpace.resonates
      (Nat.iterate MutagenicDiffusion.transmit n a)
      (Nat.iterate MutagenicDiffusion.transmit (n + 1) a) :=
  mutagenic_chain_resonance a n

end Canon

/-! ## §4. Intertextuality (Julia Kristeva) -/

section Intertextuality
variable {I : Type*} [IdeaticSpace I]

/-- Two ideas are **intertextual** if their compositions in either order resonate.
    LITERARY INSIGHT: intertextuality means the order of quotation does not
    fundamentally change the evocative structure. -/
def Intertextual (a b : I) : Prop :=
  IdeaticSpace.resonates (IdeaticSpace.compose a b) (IdeaticSpace.compose b a)

/-- Every idea is intertextual with itself.
    LITERARY INSIGHT: a text is trivially its own mosaic. -/
theorem intertextual_self (a : I) : Intertextual a a :=
  IdeaticSpace.resonance_refl _

/-- Intertextuality is symmetric.
    LITERARY INSIGHT: if text A quotes text B, then B participates in A. -/
theorem intertextual_symm {a b : I} (h : Intertextual a b) : Intertextual b a :=
  IdeaticSpace.resonance_symm _ _ h

/-- The void is intertextual with everything.
    LITERARY INSIGHT: silence is compatible with any text. -/
theorem intertextual_void_left (a : I) :
    Intertextual (IdeaticSpace.void : I) a := by
  unfold Intertextual
  simp [IdeaticSpace.void_left, IdeaticSpace.void_right]
  exact IdeaticSpace.resonance_refl a

/-- If a and b resonate, they are intertextual.
    LITERARY INSIGHT: resonance is sufficient for intertextuality. -/
theorem resonant_implies_intertextual {a b : I}
    (h : IdeaticSpace.resonates a b) : Intertextual a b :=
  IdeaticSpace.resonance_compose a b b a h (IdeaticSpace.resonance_symm _ _ h)

/-- Intertextual composition is depth-bounded.
    LITERARY INSIGHT: Kristeva's mosaic has bounded complexity. -/
theorem intertextual_depth_bound (a b : I) :
    IdeaticSpace.depth (IdeaticSpace.compose a b) <=
    IdeaticSpace.depth a + IdeaticSpace.depth b :=
  IdeaticSpace.depth_subadditive a b

/-- Atomic ideas produce bounded intertextual compositions. -/
theorem intertextual_atomic_bound {a b : I}
    (ha : IdeaticSpace.atomic a) (hb : IdeaticSpace.atomic b) :
    IdeaticSpace.depth (IdeaticSpace.compose a b) <= 2 := by
  have h1 := IdeaticSpace.depth_atomic a ha
  have h2 := IdeaticSpace.depth_atomic b hb
  have h3 := IdeaticSpace.depth_subadditive a b
  omega

/-- Extending an intertextual pair preserves resonance structure. -/
theorem intertextual_compose_self {a b : I} (h : Intertextual a b) :
    IdeaticSpace.resonates
      (IdeaticSpace.compose (IdeaticSpace.compose a b) a)
      (IdeaticSpace.compose (IdeaticSpace.compose b a) a) :=
  IdeaticSpace.resonance_compose _ _ a a h (IdeaticSpace.resonance_refl a)

/-- The void is intertextual with everything (right variant). -/
theorem intertextual_void_right (a : I) :
    Intertextual a (IdeaticSpace.void : I) :=
  intertextual_symm (intertextual_void_left a)

end Intertextuality

/-! ## §5. Translation Theory -/

section Translation
variable {I J K : Type*} [IdeaticSpace I] [IdeaticSpace J] [IdeaticSpace K]

/-- Translations preserve resonance.
    LITERARY INSIGHT: faithful translation preserves evocative structure. -/
theorem translation_preserves_resonance (f : IdeaticMorphism I J) {a b : I}
    (h : IdeaticSpace.resonates a b) :
    IdeaticSpace.resonates (f.toFun a) (f.toFun b) :=
  f.map_resonance a b h

/-- Translations map resonance classes into resonance classes.
    LITERARY INSIGHT: the cluster of associations is preserved. -/
theorem translation_maps_resonance_class (f : IdeaticMorphism I J) (a : I)
    {b : I} (hb : b ∈ resonanceClass a) :
    f.toFun b ∈ resonanceClass (f.toFun a) :=
  f.map_resonance a b hb

/-- Translations preserve void.
    LITERARY INSIGHT: silence translates to silence. -/
theorem translation_preserves_void (f : IdeaticMorphism I J) :
    f.toFun (IdeaticSpace.void : I) = (IdeaticSpace.void : J) := f.map_void

/-- Translations preserve composition.
    LITERARY INSIGHT: thought combination mirrors across languages. -/
theorem translation_preserves_compose (f : IdeaticMorphism I J) (a b : I) :
    f.toFun (IdeaticSpace.compose a b) =
    IdeaticSpace.compose (f.toFun a) (f.toFun b) := f.map_compose a b

/-- Translations preserve coherent sequences.
    LITERARY INSIGHT: if the original flows, the translation flows. -/
theorem translation_preserves_coherence (f : IdeaticMorphism I J) (s : List I)
    (h : Coherent s) : Coherent (s.map f.toFun) :=
  morphism_coherent f s h

/-- The identity is a valid translation. -/
theorem identity_translation (a : I) :
    (IdeaticMorphism.id : IdeaticMorphism I I).toFun a = a := rfl

/-- Translation preserves influence when depth is preserved. -/
theorem translation_preserves_influence (f : IdeaticMorphism I J)
    {a b : I} (hinf : Influences a b)
    (hda : IdeaticSpace.depth (f.toFun a) <= IdeaticSpace.depth (f.toFun b)) :
    Influences (f.toFun a) (f.toFun b) :=
  ⟨f.map_resonance a b hinf.1, hda⟩

/-- Composing translations preserves resonance.
    LITERARY INSIGHT: translating through an intermediate language preserves
    evocative structure if each step is faithful. -/
theorem translation_composition (f : IdeaticMorphism I J) (g : IdeaticMorphism J K)
    (a b : I) (h : IdeaticSpace.resonates a b) :
    IdeaticSpace.resonates (g.toFun (f.toFun a)) (g.toFun (f.toFun b)) :=
  g.map_resonance _ _ (f.map_resonance _ _ h)

/-- Translation preserves iterated composition. -/
theorem translation_preserves_composeN (f : IdeaticMorphism I J) (a : I) (n : Nat) :
    f.toFun (composeN a n) = composeN (f.toFun a) n :=
  morphism_composeN f a n

end Translation

/-! ## §6. The Epigone Theorem -/

section Epigone
variable {I : Type*} [MutagenicDiffusion I]

/-- An **epigonic map** reduces or preserves depth while maintaining resonance.
    LITERARY INSIGHT: the epigone can transmit but never adds depth. -/
def IsEpigonicMap (phi : I -> I) : Prop :=
  forall (a : I), IdeaticSpace.depth (phi a) <= IdeaticSpace.depth a ∧
             IdeaticSpace.resonates a (phi a)

/-- Mutagenic transmit is an epigonic map.
    LITERARY INSIGHT: cultural transmission under noise is inherently epigonic. -/
theorem transmit_is_epigonic :
    IsEpigonicMap (MutagenicDiffusion.transmit : I -> I) :=
  fun a => ⟨MutagenicDiffusion.transmit_depth_le a, MutagenicDiffusion.transmit_resonant a⟩

/-- Iterated epigonic maps have depth bounded by the original.
    LITERARY INSIGHT: epigones can only lose depth, never gain it. -/
theorem epigonic_depth_bound {phi : I -> I} (hphi : IsEpigonicMap phi)
    (b : I) (n : Nat) : IdeaticSpace.depth (Nat.iterate phi n b) <= IdeaticSpace.depth b := by
  induction n generalizing b with
  | zero => simp [Nat.iterate]
  | succ n ih =>
    show IdeaticSpace.depth (Nat.iterate phi n (phi b)) <= IdeaticSpace.depth b
    have h1 := ih (phi b)
    have h2 := (hphi b).1
    omega

/-- The **Epigone Theorem**: iterated mutagenic transmission reduces any
    idea to depth at most 1.
    LITERARY INSIGHT: T.S. Eliot's observation that tradition decays through
    "the damage done by bad poets." Enough transmission trivializes anything. -/
theorem epigone_theorem (a : I) :
    IdeaticSpace.depth
      (Nat.iterate MutagenicDiffusion.transmit (IdeaticSpace.depth a) a) <= 1 :=
  eventual_canonization a

/-- Each epigonic transmission step maintains resonance with the previous step.
    LITERARY INSIGHT: degradation is gradual, not catastrophic. -/
theorem epigonic_chain_resonance {phi : I -> I} (hphi : IsEpigonicMap phi)
    (a : I) : forall (n : Nat),
    IdeaticSpace.resonates (Nat.iterate phi n a) (Nat.iterate phi (n + 1) a)
  | 0 => (hphi a).2
  | n + 1 => epigonic_chain_resonance hphi (phi a) n

/-- Complex ideas strictly decay under mutagenic transmission.
    LITERARY INSIGHT: deep ideas are fragile — even one transmission simplifies. -/
theorem epigone_strict_decay {a : I} (h : IdeaticSpace.depth a > 1) :
    IdeaticSpace.depth (MutagenicDiffusion.transmit a) < IdeaticSpace.depth a :=
  MutagenicDiffusion.transmit_depth_decay a h

/-- Epigonic maps applied to atomic ideas stay atomic.
    LITERARY INSIGHT: simple ideas are the bedrock of cultural survival. -/
theorem epigonic_atomic_stable {phi : I -> I} (hphi : IsEpigonicMap phi)
    {a : I} (h : IdeaticSpace.depth a <= 1) (n : Nat) :
    IdeaticSpace.depth (Nat.iterate phi n a) <= 1 := by
  have := epigonic_depth_bound hphi a n; omega

end Epigone

/-! ## §7. Precursor Chains -/

section PrecursorChains
variable {I : Type*} [IdeaticSpace I]

/-- An **influence chain** is a list where each consecutive pair satisfies
    the influence relation.
    LITERARY INSIGHT: this formalizes a "lineage" of literary influence. -/
def IsInfluenceChain : List I -> Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => Influences a b ∧ IsInfluenceChain (b :: rest)

/-- The empty chain is an influence chain. -/
theorem influence_chain_nil : IsInfluenceChain ([] : List I) := trivial

/-- A single idea forms a trivial influence chain. -/
theorem influence_chain_singleton (a : I) : IsInfluenceChain [a] := trivial

/-- A pair forms an influence chain iff the first influences the second. -/
theorem influence_chain_pair {a b : I} :
    IsInfluenceChain [a, b] <-> Influences a b := by
  simp [IsInfluenceChain]

/-- The tail of an influence chain is an influence chain. -/
theorem influence_chain_tail {a : I} {rest : List I}
    (h : IsInfluenceChain (a :: rest)) : IsInfluenceChain rest := by
  cases rest with
  | nil => exact trivial
  | cons b rest' => exact h.2

/-- Extending an influence chain by prepending a new precursor. -/
theorem influence_chain_cons {a b : I} {rest : List I}
    (hab : Influences a b) (hrest : IsInfluenceChain (b :: rest)) :
    IsInfluenceChain (a :: b :: rest) :=
  ⟨hab, hrest⟩

/-- Self-referential chain: repeating the same idea forms a trivial chain.
    LITERARY INSIGHT: a tradition that repeats itself is a degenerate
    influence chain — no real evolution. -/
theorem influence_chain_replicate (a : I) : forall (n : Nat),
    IsInfluenceChain (List.replicate n a)
  | 0 => trivial
  | 1 => trivial
  | n + 2 => by
    simp [List.replicate, IsInfluenceChain]
    exact ⟨influences_refl a, influence_chain_replicate a (n + 1)⟩

/-- In a two-step influence chain, depth is non-decreasing. -/
theorem two_step_depth_le {a b c : I}
    (hab : Influences a b) (hbc : Influences b c) :
    IdeaticSpace.depth a <= IdeaticSpace.depth c :=
  le_trans hab.2 hbc.2

/-- A two-step chain is a valid influence chain. -/
theorem two_step_influence_chain {a b c : I}
    (hab : Influences a b) (hbc : Influences b c) :
    IsInfluenceChain [a, b, c] :=
  ⟨hab, ⟨hbc, trivial⟩⟩

/-- The first element of a non-empty chain influences the second. -/
theorem influence_chain_head {a b : I} {rest : List I}
    (h : IsInfluenceChain (a :: b :: rest)) :
    Influences a b := h.1

/-- In a three-element chain, depth is non-decreasing end-to-end.
    LITERARY INSIGHT: along any influence lineage, depth accumulates. -/
theorem three_step_depth_le {a b c : I} {rest : List I}
    (h : IsInfluenceChain (a :: b :: c :: rest)) :
    IdeaticSpace.depth a <= IdeaticSpace.depth c :=
  le_trans h.1.2 h.2.1.2

end PrecursorChains

/-! ## §8. Recombinant Influence (Creative Synthesis) -/

section RecombinantInfluence
variable {I : Type*} [RecombinantDiffusion I]

/-- Recombination always resonates with the first parent.
    LITERARY INSIGHT: the first source is always detectable. -/
theorem recombinant_resonates_left (a b : I) :
    IdeaticSpace.resonates a (RecombinantDiffusion.recombine a b) :=
  RecombinantDiffusion.recombine_resonant_left a b

/-- Recombination always resonates with the second parent.
    LITERARY INSIGHT: the second source is equally detectable. -/
theorem recombinant_resonates_right (a b : I) :
    IdeaticSpace.resonates b (RecombinantDiffusion.recombine a b) :=
  RecombinantDiffusion.recombine_resonant_right a b

/-- Recombination creates ideas influenced by both parents (given depth).
    LITERARY INSIGHT: Dante combines Virgil and Christian theology —
    the result resonates with both. -/
theorem recombinant_influenced_by_both (a b : I)
    (hda : IdeaticSpace.depth a <= IdeaticSpace.depth (RecombinantDiffusion.recombine a b))
    (hdb : IdeaticSpace.depth b <= IdeaticSpace.depth (RecombinantDiffusion.recombine a b)) :
    Influences a (RecombinantDiffusion.recombine a b) ∧
    Influences b (RecombinantDiffusion.recombine a b) :=
  ⟨⟨RecombinantDiffusion.recombine_resonant_left a b, hda⟩,
   ⟨RecombinantDiffusion.recombine_resonant_right a b, hdb⟩⟩

/-- Self-recombination resonates with the original. -/
theorem self_recombination_resonant (a : I) :
    IdeaticSpace.resonates a (RecombinantDiffusion.recombine a a) :=
  RecombinantDiffusion.recombine_resonant_left a a

/-- Recombination of atomic ideas has bounded depth.
    LITERARY INSIGHT: combining simple ideas produces controlled complexity. -/
theorem recombinant_atomic_bound (a b : I)
    (ha : IdeaticSpace.atomic a) (hb : IdeaticSpace.atomic b) :
    IdeaticSpace.depth (RecombinantDiffusion.recombine a b) <= 3 := by
  have h1 := IdeaticSpace.depth_atomic a ha
  have h2 := IdeaticSpace.depth_atomic b hb
  have h3 := RecombinantDiffusion.recombine_depth_bound a b
  omega

/-- Recombination depth is bounded by parents' depths plus 1.
    LITERARY INSIGHT: creative synthesis has controlled growth. -/
theorem recombinant_depth_bound' (a b : I) :
    IdeaticSpace.depth (RecombinantDiffusion.recombine a b) <=
    IdeaticSpace.depth a + IdeaticSpace.depth b + 1 :=
  RecombinantDiffusion.recombine_depth_bound a b

/-- Order of recombination produces resonant results.
    LITERARY INSIGHT: while AB is not BA in general, the two syntheses
    are "similar" — order affects details, not essence. -/
theorem recombinant_order_resonant' (a b : I) :
    IdeaticSpace.resonates
      (RecombinantDiffusion.recombine a b)
      (RecombinantDiffusion.recombine b a) :=
  RecombinantDiffusion.recombine_comm_resonant a b

end RecombinantInfluence

/-! ## §9. Depth Dynamics of Influence -/

section DepthDynamics
variable {I : Type*} [IdeaticSpace I]

/-- Composition of ideas has bounded depth. -/
theorem resonant_compose_depth (a b : I) :
    IdeaticSpace.depth (IdeaticSpace.compose a b) <=
    IdeaticSpace.depth a + IdeaticSpace.depth b :=
  IdeaticSpace.depth_subadditive a b

/-- If a influences b, composing a with c has depth bounded by b's depth plus c's.
    LITERARY INSIGHT: influence context is bounded. -/
theorem influence_compose_depth_bound {a b : I} (h : Influences a b) (c : I) :
    IdeaticSpace.depth (IdeaticSpace.compose a c) <=
    IdeaticSpace.depth b + IdeaticSpace.depth c := by
  have ha := h.2
  have := IdeaticSpace.depth_subadditive a c
  omega

/-- Void composition preserves depth. -/
theorem void_compose_depth (a : I) :
    IdeaticSpace.depth (IdeaticSpace.compose (IdeaticSpace.void : I) a) =
    IdeaticSpace.depth a := by
  rw [IdeaticSpace.void_left]

/-- Atomic composition is bounded by 2.
    LITERARY INSIGHT: simple ideas combined give bounded complexity. -/
theorem atomic_compose_bound (a b : I)
    (ha : IdeaticSpace.atomic a) (hb : IdeaticSpace.atomic b) :
    IdeaticSpace.depth (IdeaticSpace.compose a b) <= 2 := by
  have h1 := IdeaticSpace.depth_atomic a ha
  have h2 := IdeaticSpace.depth_atomic b hb
  have h3 := IdeaticSpace.depth_subadditive a b
  omega

end DepthDynamics

/-! ## §10. Selective Canon Formation -/

section SelectiveCanon
variable {I : Type*} [SelectiveDiffusion I]

/-- Selection preserves or increases fitness.
    LITERARY INSIGHT: competition always selects the fitter idea. -/
theorem selection_fitness_nondecreasing (a b : I) :
    SelectiveDiffusion.fitness (SelectiveDiffusion.select a b) >=
    SelectiveDiffusion.fitness a := by
  rw [SelectiveDiffusion.select_maximizes]
  exact Nat.le_max_left _ _

/-- Self-selection is idempotent. -/
theorem selection_self_idempotent (a : I) :
    SelectiveDiffusion.select (SelectiveDiffusion.select a a) a = a := by
  rw [selective_self a, selective_self a]

/-- Selection is depth-bounded by the inputs.
    LITERARY INSIGHT: competition produces no new complexity. -/
theorem selection_depth_bounded (a b : I) :
    IdeaticSpace.depth (SelectiveDiffusion.select a b) <=
    IdeaticSpace.depth a ∨
    IdeaticSpace.depth (SelectiveDiffusion.select a b) <=
    IdeaticSpace.depth b := by
  rcases SelectiveDiffusion.select_is_input a b with h | h
  · left; rw [h]
  · right; rw [h]

/-- Selection from void yields the other idea or void.
    LITERARY INSIGHT: silence cannot outcompete substance. -/
theorem selection_with_void (a : I) :
    SelectiveDiffusion.select a (IdeaticSpace.void : I) = a ∨
    SelectiveDiffusion.select a (IdeaticSpace.void : I) = (IdeaticSpace.void : I) :=
  SelectiveDiffusion.select_is_input a _

end SelectiveCanon

end IDT
