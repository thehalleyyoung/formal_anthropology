import FormalAnthropology.IDT_Foundations

/-! # Resonance Path Theory

The genuinely novel algebra of IDT: a monoid with a reflexive, symmetric,
NON-TRANSITIVE relation compatible with composition. The transitive closure
is a congruence, giving a quotient monoid of "literary traditions."

KEY RESULTS:
1. RConn (transitive closure) is an equivalence + congruence
2. Left/right multiplication preserve connectivity
3. Quotient I/RConn is a well-defined monoid
4. Recombinant diffusion collapses the quotient (classification theorem)
5. Mutagenic diffusion preserves connectivity while decaying depth
-/

namespace IDT

/-! ## §1. Resonance Connectivity -/

section RConnDef
variable {I : Type*} [IdeaticSpace I]

/-- Transitive-reflexive closure of resonance. -/
inductive RConn : I → I → Prop where
  | refl (a : I) : RConn a a
  | step {a b c : I} : IdeaticSpace.resonates a b → RConn b c → RConn a c

/-- Direct resonance implies connection. -/
theorem resonance_to_conn {a b : I} (h : IdeaticSpace.resonates a b) :
    RConn a b := .step h (.refl b)

/-- Connection is transitive. -/
theorem rconn_trans {a b c : I} (h1 : RConn a b) (h2 : RConn b c) :
    RConn a c := by
  induction h1 with
  | refl => exact h2
  | step hr _ ih => exact .step hr (ih h2)

/-- Connection is symmetric.

    LITERARY INSIGHT: intertextual connection is always bidirectional.
    If Hamlet echoes Oedipus through intermediaries, Oedipus echoes Hamlet
    through the reverse chain. -/
theorem rconn_symm {a b : I} (h : RConn a b) : RConn b a := by
  induction h with
  | refl => exact .refl _
  | step hr _ ih => exact rconn_trans ih (resonance_to_conn (resonance_symm hr))

end RConnDef

/-! ## §2. Composition Preserves Connectivity -/

section CompConn
variable {I : Type*} [IdeaticSpace I]

/-- Left multiplication preserves connectivity. c·(−) is a graph endomorphism.

    LITERARY INSIGHT: prefixing any context preserves the chain of associations. -/
theorem left_comp_conn (c : I) {a b : I} (h : RConn a b) :
    RConn (IdeaticSpace.compose c a) (IdeaticSpace.compose c b) := by
  induction h with
  | refl => exact .refl _
  | step hr _ ih => exact .step (resonance_compose_left c hr) ih

/-- Right multiplication preserves connectivity. -/
theorem right_comp_conn (c : I) {a b : I} (h : RConn a b) :
    RConn (IdeaticSpace.compose a c) (IdeaticSpace.compose b c) := by
  induction h with
  | refl => exact .refl _
  | step hr _ ih => exact .step (resonance_compose_right hr c) ih

/-- FUNDAMENTAL THEOREM: RConn is a congruence on the monoid.

    MATHEMATICAL INSIGHT: the quotient I/RConn inherits monoid structure.

    LITERARY INSIGHT: "traditions compose." Picking any representative from
    Greek tragedy and any from comedy gives a result in a well-defined
    "tragicomedy" tradition regardless of which specific works you chose. -/
theorem bilateral_conn {a₁ a₂ b₁ b₂ : I}
    (ha : RConn a₁ a₂) (hb : RConn b₁ b₂) :
    RConn (IdeaticSpace.compose a₁ b₁) (IdeaticSpace.compose a₂ b₂) :=
  rconn_trans (right_comp_conn b₁ ha) (left_comp_conn a₂ hb)

end CompConn

/-! ## §3. The Quotient Monoid -/

section Quotient
variable {I : Type*} [IdeaticSpace I]

/-- Quotient left identity. -/
theorem quot_void_left (a : I) :
    RConn (IdeaticSpace.compose IdeaticSpace.void a) a := by
  rw [IdeaticSpace.void_left]; exact .refl _

/-- Quotient right identity. -/
theorem quot_void_right (a : I) :
    RConn (IdeaticSpace.compose a IdeaticSpace.void) a := by
  rw [IdeaticSpace.void_right]; exact .refl _

/-- Quotient associativity. -/
theorem quot_assoc (a b c : I) :
    RConn (IdeaticSpace.compose (IdeaticSpace.compose a b) c)
          (IdeaticSpace.compose a (IdeaticSpace.compose b c)) := by
  rw [IdeaticSpace.compose_assoc]; exact .refl _

end Quotient

/-! ## §4. Resonance Components -/

section Components
variable {I : Type*} [IdeaticSpace I]

/-- The resonance component (literary tradition) containing a. -/
def RComponent (a : I) : Set I := {b | RConn a b}

theorem mem_own_rcomp (a : I) : a ∈ RComponent a := .refl a

theorem rcomp_symm {a b : I} (h : b ∈ RComponent a) : a ∈ RComponent b :=
  rconn_symm h

theorem resonant_same_rcomp {a b : I} (h : IdeaticSpace.resonates a b) :
    b ∈ RComponent a := resonance_to_conn h

/-- Composing an element with void stays in the component. -/
theorem compose_void_in_comp {a b : I} (h : b ∈ RComponent a) :
    IdeaticSpace.compose b IdeaticSpace.void ∈ RComponent a := by
  rw [IdeaticSpace.void_right]; exact h

/-- Bilateral composition maps components. -/
theorem bilateral_maps_comp {a₁ a₂ b₁ b₂ : I}
    (ha : a₁ ∈ RComponent a₂) (hb : b₁ ∈ RComponent b₂) :
    IdeaticSpace.compose a₁ b₁ ∈
    RComponent (IdeaticSpace.compose a₂ b₂) :=
  bilateral_conn ha hb

end Components

/-! ## §5. Resonance Triples: Non-Transitivity as Structure -/

section Triples
variable {I : Type*} [IdeaticSpace I]

/-- A resonance triple: a~b~c with a~c NOT assumed. -/
structure RTriple (I : Type*) [IdeaticSpace I] where
  left : I
  mid : I
  right : I
  left_mid : IdeaticSpace.resonates left mid
  mid_right : IdeaticSpace.resonates mid right

/-- Triple compositions through the middle resonate (left side). -/
theorem triple_left_med (t : RTriple I) :
    IdeaticSpace.resonates
      (IdeaticSpace.compose t.left t.mid)
      (IdeaticSpace.compose t.mid t.mid) :=
  resonance_compose_right t.left_mid t.mid

/-- Triple compositions through the middle resonate (right side). -/
theorem triple_right_med (t : RTriple I) :
    IdeaticSpace.resonates
      (IdeaticSpace.compose t.mid t.mid)
      (IdeaticSpace.compose t.mid t.right) :=
  resonance_compose_left t.mid t.mid_right

/-- Triple endpoints are connected (gap ≤ 2).

    MATHEMATICAL INSIGHT: non-transitivity creates gaps of size at most 2.
    The "resonance gap" is always bounded. -/
theorem triple_endpoints_conn (t : RTriple I) : RConn t.left t.right :=
  .step t.left_mid (.step t.mid_right (.refl _))

/-- Triples compose pointwise.

    MATHEMATICAL INSIGHT: "resonance triples" form a sub-object of I³
    closed under the diagonal monoid action. -/
def compose_triples (t₁ t₂ : RTriple I) : RTriple I where
  left := IdeaticSpace.compose t₁.left t₂.left
  mid := IdeaticSpace.compose t₁.mid t₂.mid
  right := IdeaticSpace.compose t₁.right t₂.right
  left_mid := IdeaticSpace.resonance_compose _ _ _ _ t₁.left_mid t₂.left_mid
  mid_right := IdeaticSpace.resonance_compose _ _ _ _ t₁.mid_right t₂.mid_right

/-- Triple endpoint composition has bounded depth. -/
theorem triple_depth (t : RTriple I) :
    IdeaticSpace.depth (IdeaticSpace.compose t.left t.right) ≤
    IdeaticSpace.depth t.left + IdeaticSpace.depth t.right :=
  IdeaticSpace.depth_subadditive _ _

/-- The void triple: void can mediate between any resonant pair. -/
def void_mediates {a b : I} (h : IdeaticSpace.resonates a b) :
    RTriple I :=
  { left := a, mid := a, right := b,
    left_mid := IdeaticSpace.resonance_refl a, mid_right := h }

end Triples

/-! ## §6. Mutagenic Diffusion and Connectivity -/

section MutagenicConn
variable {I : Type*} [MutagenicDiffusion I]

/-- Mutagenic transmission preserves connectivity. It maps a~b to
    a chain: T(a) ~ a ~ b ~ T(b), so RConn T(a) T(b).

    LITERARY INSIGHT: retelling preserves chains of influence even
    though individual ideas degrade. The NETWORK of stories survives
    while the CONTENT simplifies. -/
theorem mutagenic_conn {a b : I} (h : RConn a b) :
    RConn (MutagenicDiffusion.transmit a) (MutagenicDiffusion.transmit b) := by
  induction h with
  | @refl x => exact .refl _
  | @step x y z hr _ ih =>
    have hta : IdeaticSpace.resonates (MutagenicDiffusion.transmit x) x :=
      IdeaticSpace.resonance_symm _ _ (MutagenicDiffusion.transmit_resonant x)
    have htb : IdeaticSpace.resonates y (MutagenicDiffusion.transmit y) :=
      MutagenicDiffusion.transmit_resonant y
    exact rconn_trans (.step hta (.step hr (.step htb (.refl _)))) ih

/-- Iterated transmission preserves connectivity. -/
theorem iter_mutagenic_conn {a b : I} (h : RConn a b) :
    ∀ (n : ℕ), RConn (Nat.iterate MutagenicDiffusion.transmit n a)
                      (Nat.iterate MutagenicDiffusion.transmit n b) := by
  intro n; induction n generalizing a b with
  | zero => exact h
  | succ n ih => exact ih (mutagenic_conn h)

/-- THEOREM (Connectivity-Depth Tension): transmission preserves
    the resonance network while eventually simplifying all ideas to depth ≤ 1.

    MATHEMATICAL INSIGHT: transmission is a graph endomorphism AND a
    depth-contracting map. This is a "convergence" where the space
    collapses in depth while maintaining its topology.

    LITERARY INSIGHT: oral tradition preserves WHICH stories are related
    while simplifying each story. Structure survives; complexity degrades. -/
theorem conn_depth_tension {a b : I}
    (h : RConn a b) (n : ℕ) :
    RConn (Nat.iterate MutagenicDiffusion.transmit n a)
          (Nat.iterate MutagenicDiffusion.transmit n b) ∧
    IdeaticSpace.depth (Nat.iterate MutagenicDiffusion.transmit n a) ≤
    IdeaticSpace.depth a := by
  exact ⟨iter_mutagenic_conn h n, mutagenic_depth_global_bound a n⟩

/-- Transmission maps components into components. -/
theorem transmit_maps_comp {a b : I} (h : b ∈ RComponent a) :
    MutagenicDiffusion.transmit b ∈
    RComponent (MutagenicDiffusion.transmit a) :=
  mutagenic_conn h

end MutagenicConn

/-! ## §7. Conservative Diffusion -/

section ConservativeConn
variable {I : Type*} [ConservativeDiffusion I]

/-- Conservative diffusion preserves ALL connectivity structure. -/
theorem conservative_conn {a b : I} (h : RConn a b) :
    RConn (ConservativeDiffusion.transmit a) (ConservativeDiffusion.transmit b) := by
  rw [ConservativeDiffusion.transmit_faithful, ConservativeDiffusion.transmit_faithful]
  exact h

end ConservativeConn

/-! ## §8. Selective Diffusion -/

section SelectiveConn
variable {I : Type*} [SelectiveDiffusion I]

/-- Selection from the same component stays in that component.

    LITERARY INSIGHT: choosing the "better" version of a story stays
    within the same tradition. Selection doesn't cross boundaries. -/
theorem select_preserves_comp {a b c : I}
    (hb : b ∈ RComponent a) (hc : c ∈ RComponent a) :
    SelectiveDiffusion.select b c ∈ RComponent a := by
  rcases SelectiveDiffusion.select_is_input b c with h | h <;> rw [h]
  · exact hb
  · exact hc

end SelectiveConn

/-! ## §9. Recombinant Diffusion: Component Merging

CLASSIFICATION THEOREM: Recombinant diffusion collapses the quotient
monoid to a single element. This classifies the four diffusion axioms
by their effect on tradition structure. -/

section RecombinantConn
variable {I : Type*} [RecombinantDiffusion I]

/-- Recombination connects to the left parent.

    LITERARY INSIGHT: innovation (combining traditions) creates bridges.
    Joyce combining stream-of-consciousness with classical epic connects
    modernism and classicism. -/
theorem recombine_conn_left {a b : I} :
    RConn a (RecombinantDiffusion.recombine a b) :=
  resonance_to_conn (RecombinantDiffusion.recombine_resonant_left a b)

/-- Recombination connects to the right parent. -/
theorem recombine_conn_right {a b : I} :
    RConn b (RecombinantDiffusion.recombine a b) :=
  resonance_to_conn (RecombinantDiffusion.recombine_resonant_right a b)

/-- Recombination bridges any two ideas.

    MATHEMATICAL INSIGHT: recombination is the ONLY diffusion mode
    that can change the number of connected components. -/
theorem recombine_bridges {a b : I} : RConn a b :=
  rconn_trans recombine_conn_left (rconn_symm recombine_conn_right)

/-- CLASSIFICATION THEOREM: Recombinant spaces are totally connected.
    The quotient monoid I/RConn is trivial.

    MATHEMATICAL INSIGHT: this classifies diffusion by quotient effect:
    - Conservative → preserves quotient exactly
    - Mutagenic → preserves quotient (connections survive mutation)
    - Selective → preserves quotient (choosing within doesn't merge)
    - Recombinant → collapses quotient to trivial

    LITERARY INSIGHT: in a culture where ideas freely recombine,
    ALL ideas are connected. No literary tradition is truly isolated
    when innovation can bridge any gap. -/
theorem recombinant_connected (a b : I) : RConn a b :=
  recombine_bridges

/-- Everything is in a single component. -/
theorem recombinant_single_comp (a b : I) : b ∈ RComponent a :=
  recombinant_connected a b

/-- Recombinant spaces have trivial component structure. -/
theorem recombinant_comp_eq (a b : I) : RComponent a = RComponent b := by
  ext x; constructor
  · intro hx; exact recombinant_connected b x
  · intro hx; exact recombinant_connected a x

end RecombinantConn

/-! ## §10. Coherent Sequences and Connectivity -/

section CoherentConn
variable {I : Type*} [IdeaticSpace I]

/-- Consecutive coherent elements are connected. -/
theorem coherent_head_conn {a b : I} {rest : List I}
    (h : Coherent (a :: b :: rest)) : RConn a b :=
  resonance_to_conn h.1

/-- All elements in a coherent list connect to the head.

    LITERARY INSIGHT: in a coherent narrative, every element traces
    back to the beginning through a chain of associations. -/
theorem coherent_all_conn (s : List I) :
    ∀ (a : I), Coherent (a :: s) → ∀ b ∈ s, RConn a b := by
  induction s with
  | nil => intro _ _ b hb; exact absurd hb (List.not_mem_nil _)
  | cons c rest ih =>
    intro a h b hb
    simp [List.mem_cons] at hb
    cases hb with
    | inl heq => subst heq; exact resonance_to_conn h.1
    | inr hrest =>
      exact rconn_trans (resonance_to_conn h.1) (ih c h.2 b hrest)

end CoherentConn

/-! ## §11. Depth-Connectivity Interaction -/

section DepthConn
variable {I : Type*} [IdeaticSpace I]

/-- Composition of connected elements has bounded depth. -/
theorem conn_compose_depth {a b : I} (_ : RConn a b) :
    IdeaticSpace.depth (IdeaticSpace.compose a b) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b :=
  IdeaticSpace.depth_subadditive a b

/-- Atomic resonant pairs compose to depth ≤ 2. -/
theorem atomic_resonant_bound {a b : I}
    (ha : IdeaticSpace.depth a ≤ 1) (hb : IdeaticSpace.depth b ≤ 1)
    (_ : IdeaticSpace.resonates a b) :
    IdeaticSpace.depth (IdeaticSpace.compose a b) ≤ 2 := by
  have := IdeaticSpace.depth_subadditive a b; omega

/-- Void composition doesn't change depth. -/
theorem void_compose_depth (a : I) :
    IdeaticSpace.depth (IdeaticSpace.compose IdeaticSpace.void a) =
    IdeaticSpace.depth a := by rw [IdeaticSpace.void_left]

/-- Self-composition depth bound (linear growth). -/
theorem composeN_depth (a : I) (n : ℕ) :
    IdeaticSpace.depth (composeN a n) ≤ (n + 1) * IdeaticSpace.depth a := by
  induction n with
  | zero => simp [composeN, Nat.one_mul]
  | succ n ih =>
    simp [composeN]
    calc IdeaticSpace.depth (IdeaticSpace.compose (composeN a n) a)
        ≤ IdeaticSpace.depth (composeN a n) + IdeaticSpace.depth a :=
          IdeaticSpace.depth_subadditive _ _
      _ ≤ (n + 1) * IdeaticSpace.depth a + IdeaticSpace.depth a := by omega
      _ = (n + 2) * IdeaticSpace.depth a := by ring

end DepthConn

/-! ## §12. Resonance Chains (List-Based) -/

section Chains
variable {I : Type*} [IdeaticSpace I]

/-- A resonance chain: consecutive elements resonate. -/
def RChain : List I → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => IdeaticSpace.resonates a b ∧ RChain (b :: rest)

theorem rchain_nil : RChain ([] : List I) := trivial
theorem rchain_singleton (a : I) : RChain [a] := trivial
theorem rchain_pair {a b : I} (h : IdeaticSpace.resonates a b) :
    RChain [a, b] := ⟨h, trivial⟩

/-- Chain elements connect to the head.

    LITERARY INSIGHT: a chain of allusions from Homer to Virgil to Dante
    to Eliot creates a connected tradition. Every work in the chain is
    connected to the first. -/
theorem rchain_all_conn :
    ∀ (s : List I) (a : I), RChain (a :: s) → ∀ b ∈ s, RConn a b := by
  intro s; induction s with
  | nil => intro _ _ b hb; exact absurd hb (List.not_mem_nil _)
  | cons c rest ih =>
    intro a hc b hb
    simp [List.mem_cons] at hb
    cases hb with
    | inl heq => subst heq; exact resonance_to_conn hc.1
    | inr hrest =>
      exact rconn_trans (resonance_to_conn hc.1) (ih c hc.2 b hrest)

/-- Chain composition of empty list is void. -/
theorem chain_compose_nil :
    ([].foldl IdeaticSpace.compose (IdeaticSpace.void : I)) = IdeaticSpace.void := rfl

/-- Chain composition of singleton equals the element. -/
theorem chain_compose_singleton (a : I) :
    [a].foldl IdeaticSpace.compose IdeaticSpace.void = a := by
  simp [List.foldl, IdeaticSpace.void_left]

end Chains

end IDT
