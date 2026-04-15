import FormalAnthropology.IDT_Foundations

/-!
# Signalling Games in IDT — Chapter 16: Cooperative Composition and Gift Exchange

**Anthropological motivation.** Marcel Mauss's *Essai sur le don* (1925) revealed
that gift exchange is never merely economic — it creates social bonds, obligations,
and shared meaning. In IDT, cooperation is *composition*: when two agents contribute
their ideas to a joint project, the result is `compose(a, b)`. The order matters
(gifts are not symmetric!), and the void contributes nothing.

This chapter formalizes cooperative game theory within ideatic space:

- **jointCompose**: sequential composition as collaboration
- **symmetricJoint**: the rare case where order doesn't matter
- **JointProject**: multi-party cooperative structures
- Depth bounds on collaborative output
- Resonance preservation in cooperative projects
- Void as the non-contributor

## 20 Theorems, 0 Sorries
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.Signal.Ch16

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- Joint composition: two agents contribute ideas sequentially.
    In Mauss's terms, agent `a` gives first, agent `b` reciprocates.
    The result is a shared compound idea. -/
def jointCompose (a b : I) : I := IdeaticSpace.compose a b

/-- Symmetric joint: the rare case where the order of gift-giving
    doesn't matter. Most real exchanges are NOT symmetric — who
    gives first shapes the meaning of the entire exchange. -/
def symmetricJoint (a b : I) : Prop := IdeaticSpace.compose a b = IdeaticSpace.compose b a

/-- A joint project: multiple participants each contribute an idea.
    The project's output is the sequential composition of all contributions. -/
structure JointProject (I : Type*) [IdeaticSpace I] where
  participants : List I

/-- The output of a joint project: fold all contributions via composition.
    Order matters — the first contributor sets the frame. -/
def JointProject.output (p : JointProject I) : I :=
  p.participants.foldl IdeaticSpace.compose IdeaticSpace.void

/-- Total contribution depth of a joint project. -/
def JointProject.totalDepth (p : JointProject I) : ℕ :=
  depthSum p.participants

/-! ## §2. Fundamental Cooperation Theorems -/

/-- **Theorem 16.1 (Void Contributes Nothing — Left).**
    Adding void as a first contributor doesn't change the outcome.

    *Mauss*: Silence before a gift changes nothing about the gift. -/
theorem void_joint_left (b : I) :
    jointCompose IdeaticSpace.void b = b := by
  simp [jointCompose]

/-- **Theorem 16.2 (Void Contributes Nothing — Right).**
    Adding void as a second contributor doesn't change the outcome.

    *Mauss*: A gift followed by silence is just the gift. -/
theorem void_joint_right (a : I) :
    jointCompose a IdeaticSpace.void = a := by
  simp [jointCompose]

/-- **Theorem 16.3 (Associativity of Multi-Party Cooperation).**
    Three-way cooperation is independent of bracketing.

    *Anthropological insight*: In a ritual with three participants,
    it doesn't matter whether (A and B) then C cooperate, or A then (B and C).
    The overall composite meaning is the same. -/
theorem joint_assoc (a b c : I) :
    jointCompose (jointCompose a b) c = jointCompose a (jointCompose b c) := by
  simp [jointCompose, compose_assoc]

/-- **Theorem 16.4 (Resonant Partners Produce Resonant Outcomes).**
    If both partners resonate with their counterparts, the joint outputs resonate.

    *Mauss*: When gift-givers are spiritually aligned, their combined gifts
    carry a resonance that mismatched givers cannot achieve. -/
theorem resonant_partners_resonant_output {a₁ a₂ b₁ b₂ : I}
    (ha : IdeaticSpace.resonates a₁ a₂) (hb : IdeaticSpace.resonates b₁ b₂) :
    IdeaticSpace.resonates (jointCompose a₁ b₁) (jointCompose a₂ b₂) := by
  exact IdeaticSpace.resonance_compose a₁ a₂ b₁ b₂ ha hb

/-- **Theorem 16.5 (Depth Bound on Joint Output).**
    The depth of a joint product is bounded by the sum of contributors' depths.

    *Economic analogy*: The complexity of a joint venture cannot exceed
    the total intellectual capital invested by both partners. -/
theorem joint_depth_bound (a b : I) :
    IdeaticSpace.depth (jointCompose a b) ≤ IdeaticSpace.depth a + IdeaticSpace.depth b := by
  exact depth_compose_le a b

/-- **Theorem 16.6 (Joint With Self Equals ComposeN 2).**
    Cooperating with yourself is just repetition.

    *Ritual theory*: Self-reinforcement through repeated practice is
    formally identical to composing an idea with itself. -/
theorem joint_self_is_composeN2 (a : I) :
    jointCompose a a = composeN a 2 := by
  simp [jointCompose, composeN, composeN_one']

/-- **Theorem 16.7 (Void Symmetry).**
    Void always commutes — silence is the universal symmetric partner.

    *Mauss*: Non-participation is the one "gift" whose order never matters. -/
theorem void_symmetric_left (a : I) : symmetricJoint IdeaticSpace.void a := by
  simp [symmetricJoint]

/-- **Theorem 16.8 (Void Symmetry — Self).**
    Void is symmetric with itself.

    *Wittgenstein*: "Whereof one cannot speak, thereof one must be silent" —
    and the order of two silences is immaterial. -/
theorem void_symmetric_self : symmetricJoint (IdeaticSpace.void : I) IdeaticSpace.void := by
  simp [symmetricJoint]

/-- **Theorem 16.9 (Empty Project Produces Void).**
    A project with no participants produces nothing.

    *Organizational theory*: An unfunded, unstaffed project yields silence. -/
theorem empty_project_void :
    (⟨([] : List I)⟩ : JointProject I).output = IdeaticSpace.void := by
  simp [JointProject.output, List.foldl]

/-- **Theorem 16.10 (Singleton Project Preserves Contribution).**
    A one-person project outputs exactly that person's contribution.

    *Anthropology*: A solo artisan's work is their own idea, unmediated. -/
theorem singleton_project (a : I) :
    (⟨[a]⟩ : JointProject I).output = a := by
  simp [JointProject.output, List.foldl, jointCompose]

/-- **Theorem 16.11 (Self-Resonance of Joint Output).**
    Every joint output resonates with itself.

    *Mauss*: Any completed exchange, however imperfect, achieves internal coherence. -/
theorem joint_self_resonance (a b : I) :
    IdeaticSpace.resonates (jointCompose a b) (jointCompose a b) := by
  exact resonance_refl _

/-- **Theorem 16.12 (Right-Resonance Preservation in Cooperation).**
    If two agents share resonance, cooperating with the same third party
    preserves that resonance.

    *Durkheim*: Agents who share collective consciousness produce similar
    ritual outcomes regardless of the specific ritual form. -/
theorem joint_resonance_right {a b : I} (hab : IdeaticSpace.resonates a b) (c : I) :
    IdeaticSpace.resonates (jointCompose a c) (jointCompose b c) := by
  exact resonance_compose_right hab c

/-- **Theorem 16.13 (Left-Resonance Preservation in Cooperation).**
    Cooperating with resonant partners preserves the frame's identity.

    *Bourdieu*: The same habitus (frame `c`) applied to resonant inputs
    produces resonant interpretations. -/
theorem joint_resonance_left (c : I) {a b : I} (hab : IdeaticSpace.resonates a b) :
    IdeaticSpace.resonates (jointCompose c a) (jointCompose c b) := by
  exact resonance_compose_left c hab

/-- **Theorem 16.14 (Depth Zero Closure Under Cooperation).**
    If both partners contribute trivial ideas, the result is trivial.

    *Critical theory*: Shallow discourse combined with shallow discourse
    can never produce depth. You cannot build profundity from banality. -/
theorem trivial_cooperation {a b : I}
    (ha : IdeaticSpace.depth a = 0) (hb : IdeaticSpace.depth b = 0) :
    IdeaticSpace.depth (jointCompose a b) = 0 := by
  exact depth_zero_closed ha hb

/-- **Theorem 16.15 (Reciprocal Exchange Resonance).**
    If A gives to B and B gives to A, both exchanges resonate
    with each other whenever A and B individually resonate.

    *Mauss*: The counter-gift resonates with the gift when giver and
    receiver are in spiritual accord. -/
theorem reciprocal_resonance {a b : I} (hab : IdeaticSpace.resonates a b) :
    IdeaticSpace.resonates (jointCompose a b) (jointCompose b a) := by
  exact IdeaticSpace.resonance_compose a b b a hab (resonance_symm hab)

/-- **Theorem 16.16 (Joint Project Depth Sum Bound).**
    The total depth of individual contributions bounds the project scope.

    *Project management*: Total intellectual capital invested constrains
    what the project can achieve. -/
theorem project_depth_bound (p : JointProject I) (d : ℕ)
    (hbound : ∀ a : I, a ∈ p.participants → IdeaticSpace.depth a ≤ d) :
    depthSum p.participants ≤ p.participants.length * d := by
  exact depthSum_bound p.participants d hbound

/-- **Theorem 16.17 (Cooperation Monotonicity for Depth).**
    Adding a void contributor doesn't increase joint depth.

    *Economics*: Free-riders (void contributors) don't add complexity
    to the joint output, but they don't reduce it either. -/
theorem void_cooperation_depth (a : I) :
    IdeaticSpace.depth (jointCompose a IdeaticSpace.void) = IdeaticSpace.depth a := by
  simp [jointCompose]

/-- **Theorem 16.18 (Four-Party Cooperation Associativity).**
    Four-way cooperation is well-defined regardless of bracketing.

    *Organizational theory*: In a four-person team, the final product
    is the same whether sub-teams form as (AB)(CD) or A(B(CD)). -/
theorem four_party_assoc (a b c d : I) :
    jointCompose (jointCompose (jointCompose a b) c) d =
    jointCompose a (jointCompose b (jointCompose c d)) := by
  simp [jointCompose, compose_assoc]

/-- **Theorem 16.19 (ComposeN as Iterated Self-Cooperation).**
    Composing with yourself n times = n-fold self-cooperation depth bound.

    *Ritual theory*: Repeating a ritual n times has bounded cumulative depth,
    growing at most linearly with repetitions. -/
theorem iterated_self_cooperation_depth (a : I) (n : ℕ) :
    IdeaticSpace.depth (composeN a n) ≤ n * IdeaticSpace.depth a := by
  exact depth_composeN a n

/-- **Theorem 16.20 (Gift Exchange Triangle).**
    In a three-party gift cycle A→B→C, the total depth is bounded.

    *Malinowski's Kula ring*: Gifts circulating through a ring of partners
    have bounded total complexity, ensuring the exchange remains manageable. -/
theorem gift_triangle_depth (a b c : I) :
    IdeaticSpace.depth (jointCompose (jointCompose a b) c) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b + IdeaticSpace.depth c := by
  have h1 := depth_compose_le (IdeaticSpace.compose a b) c
  have h2 := depth_compose_le a b
  simp [jointCompose] at *
  linarith

end IDT.Signal.Ch16
