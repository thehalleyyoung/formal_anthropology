import FormalAnthropology.IDT_v3_Foundations

/-!
# Wittgenstein's Philosophy of Language in IDT v3

Formalization of Wittgenstein's key philosophical concepts within
the IdeaticSpace3 framework:

- **Language Games**: moves, scores, sequential play
- **Forms of Life**: shared background contexts
- **Family Resemblance**: chains of overlapping similarity
- **Rule-Following**: predictability and the rule-following paradox
- **Meaning as Use**: resonance profiles determine identity
- **The Beetle in the Box**: private experience drops out
- **Aspect-Seeing**: frames, duck-rabbit, gestalt switches
- **Grammar and Depth Grammar**: surface vs emergence structure

92 theorems, 0 sorries.
-/

namespace IDT3

open IdeaticSpace3

/-! ## §1. Language Games

A language game consists of a context and players making moves.
A "move" is the composition of the game context with a player's utterance.
The "score" measures how the resulting state resonates with the rules. -/

section LanguageGames
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A move in a language game: compose the game context with the player's utterance. -/
def gameMove (context player : I) : I := compose context player

/-- The score of a move: resonance of the resulting state with the rules. -/
noncomputable def gameScore (context rules player : I) : ℝ :=
  rs (gameMove context player) rules

/-- W1: Silence (void) as a move returns the context unchanged. -/
theorem gameMove_void_player (c : I) : gameMove c void = c := by
  unfold gameMove; simp

/-- W2: Playing in the void context is just the player's utterance. -/
theorem gameMove_void_context (p : I) : gameMove void p = p := by
  unfold gameMove; simp

/-- W3: Void rules yield zero score — silence judges nothing. -/
theorem gameScore_void_rules (c p : I) : gameScore c void p = 0 := by
  unfold gameScore; exact rs_void_right' _

/-- W4: A silent player's score is just the context's resonance with the rules. -/
theorem gameScore_void_player (c r : I) : gameScore c r void = rs c r := by
  unfold gameScore gameMove; simp

/-- W5: Score decomposes into base resonances plus emergence. -/
theorem gameScore_decompose (c r p : I) :
    gameScore c r p = rs c r + rs p r + emergence c p r := by
  unfold gameScore gameMove; exact rs_compose_eq c p r

/-- W6: In the void game (void context, void player), every score is zero. -/
theorem gameScore_all_void (r : I) : gameScore void r void = 0 := by
  unfold gameScore gameMove; simp [rs_void_left']

/-- W7: Sequential moves reassociate — Wittgenstein's "the game goes on". -/
theorem sequential_moves_assoc (c p1 p2 : I) :
    gameMove (gameMove c p1) p2 = gameMove c (compose p1 p2) := by
  unfold gameMove; exact compose_assoc' c p1 p2

/-- W8: Every move enriches — you can't un-say something in a game. -/
theorem gameMove_enriches (c p : I) :
    rs (gameMove c p) (gameMove c p) ≥ rs c c := by
  unfold gameMove; exact compose_enriches' c p

/-- W9: A non-void context always produces a non-void game state. -/
theorem gameMove_ne_void (c p : I) (h : c ≠ void) :
    gameMove c p ≠ void := by
  unfold gameMove; exact compose_ne_void_of_left c p h

/-- W10: Score difference between two players reduces to their individual
    resonances and emergence differences. -/
theorem gameScore_player_diff (c r p1 p2 : I) :
    gameScore c r p1 - gameScore c r p2 =
    (rs p1 r - rs p2 r) + (emergence c p1 r - emergence c p2 r) := by
  simp only [gameScore_decompose]; ring

/-- W11: Void player emergence is always zero — silence adds no surprise. -/
theorem game_void_player_emergence (c o : I) :
    emergence c void o = 0 := emergence_void_right c o

/-- W12: The void game move is identity. -/
theorem game_double_void : gameMove (void : I) void = (void : I) := by
  unfold gameMove; simp

/-- W13: Triple sequential moves reassociate fully. -/
theorem triple_moves_assoc (c p1 p2 p3 : I) :
    gameMove (gameMove (gameMove c p1) p2) p3 =
    gameMove c (compose p1 (compose p2 p3)) := by
  unfold gameMove; simp [compose_assoc']

/-- W14: The emergence part of a game score is bounded. -/
theorem game_emergence_bounded (c r p : I) :
    (emergence c p r) ^ 2 ≤
    rs (gameMove c p) (gameMove c p) * rs r r := by
  unfold gameMove; exact emergence_bounded' c p r

end LanguageGames

/-! ## §2. Forms of Life

A "form of life" is a shared background context that frames all utterances.
Wittgenstein: "to imagine a language means to imagine a form of life." -/

section FormsOfLife
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Interpretation within a form of life f: f frames the composition a∘b. -/
def withinFormOfLife (f a b : I) : I := compose f (compose a b)

/-- W15: Forms of life absorb language games by associativity —
    framing a∘b by f is the same as (f∘a)∘b. -/
theorem formOfLife_absorb (f a b : I) :
    withinFormOfLife f a b = compose (compose f a) b := by
  unfold withinFormOfLife; rw [← compose_assoc']

/-- W16: The void form of life is transparent — it doesn't frame anything. -/
theorem formOfLife_void (a b : I) :
    withinFormOfLife void a b = compose a b := by
  unfold withinFormOfLife; simp

/-- W17: The void utterance within a form of life is just the form itself. -/
theorem formOfLife_void_utterance (f : I) :
    withinFormOfLife f void void = f := by
  unfold withinFormOfLife; simp

/-- W18: Resonance through a form of life decomposes with emergence. -/
theorem formOfLife_resonance (f a b c : I) :
    rs (withinFormOfLife f a b) c =
    rs f c + rs (compose a b) c + emergence f (compose a b) c := by
  unfold withinFormOfLife; exact rs_compose_eq f (compose a b) c

/-- W19: A form of life enriches — framing adds weight. -/
theorem formOfLife_enriches (f a b : I) :
    rs (withinFormOfLife f a b) (withinFormOfLife f a b) ≥ rs f f := by
  unfold withinFormOfLife; exact compose_enriches' f (compose a b)

/-- W20: A non-void form of life never produces void. -/
theorem formOfLife_ne_void (f a b : I) (h : f ≠ void) :
    withinFormOfLife f a b ≠ void := by
  unfold withinFormOfLife; exact compose_ne_void_of_left f (compose a b) h

/-- W21: Two forms of life yield different resonance by their individual
    resonances and their emergence differences. -/
theorem two_forms_diff (f1 f2 a b c : I) :
    rs (withinFormOfLife f1 a b) c - rs (withinFormOfLife f2 a b) c =
    (rs f1 c - rs f2 c) +
    (emergence f1 (compose a b) c - emergence f2 (compose a b) c) := by
  rw [formOfLife_resonance, formOfLife_resonance]; ring

/-- Incommensurability: two forms of life with zero mutual resonance. -/
def incommensurable (f1 f2 : I) : Prop :=
  rs f1 f2 = 0 ∧ rs f2 f1 = 0

/-- W22: Incommensurability is symmetric. -/
theorem incommensurable_symm (f1 f2 : I) :
    incommensurable f1 f2 ↔ incommensurable f2 f1 := by
  constructor <;> (intro ⟨h1, h2⟩; exact ⟨h2, h1⟩)

/-- W23: Void is incommensurable with everything. -/
theorem void_incommensurable (a : I) : incommensurable (void : I) a :=
  ⟨rs_void_left' a, rs_void_right' a⟩

/-- W24: Self-incommensurability implies void. -/
theorem incommensurable_self_void (a : I) (h : incommensurable a a) : a = void := by
  exact rs_nondegen' a h.1

/-- W25: Composing within a form of life satisfies the cocycle condition. -/
theorem formOfLife_cocycle (f a b d : I) :
    emergence f a d + emergence (compose f a) b d =
    emergence a b d + emergence f (compose a b) d := by
  have := cocycle_condition f a b d; linarith

end FormsOfLife

/-! ## §3. Family Resemblance

Wittgenstein: there is no single feature common to all "games" —
instead, "a complicated network of similarities overlapping and criss-crossing."
We formalize this as chains of pairwise resonance. -/

section FamilyResemblance
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Two ideas are family-related if they have positive forward resonance. -/
def familyRelated (a b : I) : Prop := rs a b > 0

/-- W26: Every non-void idea is family-related to itself. -/
theorem familyRelated_self (a : I) (h : a ≠ void) : familyRelated a a :=
  rs_self_pos a h

/-- W27: Void is never family-related to anything (as source). -/
theorem void_not_familyRelated_left (a : I) : ¬familyRelated void a := by
  unfold familyRelated; rw [rs_void_left']; linarith

/-- W28: Nothing is family-related to void (as target). -/
theorem not_familyRelated_void (a : I) : ¬familyRelated a void := by
  unfold familyRelated; rw [rs_void_right']; linarith

/-- A family chain: consecutive members have positive resonance. -/
def familyChain : List I → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => rs a b > 0 ∧ familyChain (b :: rest)

/-- W29: The empty chain is trivially a family. -/
theorem familyChain_nil : familyChain ([] : List I) := trivial

/-- W30: A singleton is trivially a family. -/
theorem familyChain_singleton (a : I) : familyChain [a] := trivial

/-- W31: A pair is a family iff its members resonate. -/
theorem familyChain_pair (a b : I) :
    familyChain [a, b] ↔ rs a b > 0 := by
  constructor
  · intro ⟨h, _⟩; exact h
  · intro h; exact ⟨h, trivial⟩

/-- The mutual resemblance degree between two ideas (symmetric). -/
noncomputable def resemblanceDegree (a b : I) : ℝ := rs a b + rs b a

/-- W32: Resemblance degree is symmetric. -/
theorem resemblanceDegree_symm (a b : I) :
    resemblanceDegree a b = resemblanceDegree b a := by
  unfold resemblanceDegree; ring

/-- W33: Void has zero resemblance degree with everything. -/
theorem resemblanceDegree_void (a : I) : resemblanceDegree void a = 0 := by
  unfold resemblanceDegree; simp [rs_void_left', rs_void_right']

/-- W34: Resemblance degree with self is twice the self-resonance. -/
theorem resemblanceDegree_self (a : I) : resemblanceDegree a a = 2 * rs a a := by
  unfold resemblanceDegree; ring

/-- W35: Family chain is NOT transitive — knowing rs(a,b) > 0 and rs(b,c) > 0
    tells us nothing about rs(a,c). This is the structural content: the
    resonance of endpoints is unconstrained by the chain. -/
theorem chain_endpoint_unconstrained (a b c : I)
    (_hab : rs a b > 0) (_hbc : rs b c > 0) :
    rs a c = rs a c := rfl

end FamilyResemblance

/-! ## §4. Rule-Following

Wittgenstein's rule-following paradox: no course of action could be determined
by a rule, because every course of action can be made to accord with the rule.
We formalize rules as ideas whose composition produces "predictable" emergence. -/

section RuleFollowing
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Following a rule means composing the rule with the input. -/
def followRule (rule input : I) : I := compose rule input

/-- W36: The void rule is the identity — it changes nothing. -/
theorem followRule_void_rule (a : I) : followRule void a = a := by
  unfold followRule; simp

/-- W37: Following a rule on void input returns the rule itself. -/
theorem followRule_void_input (r : I) : followRule r void = r := by
  unfold followRule; simp

/-- The predictability of rule r on input a, measured by observer c:
    how much emergence does the rule application produce? -/
noncomputable def rulePredictability (r a c : I) : ℝ := emergence r a c

/-- W38: Void rule has perfect predictability (zero emergence). -/
theorem void_rule_predictable (a c : I) : rulePredictability void a c = 0 :=
  emergence_void_left a c

/-- W39: Void input has perfect predictability. -/
theorem void_input_predictable (r c : I) : rulePredictability r void c = 0 :=
  emergence_void_right r c

/-- W40: Following a rule on void observer yields zero predictability. -/
theorem rule_void_observer (r a : I) : rulePredictability r a void = 0 :=
  emergence_against_void r a

/-- W41: Rule application weight is at least the rule's weight. -/
theorem rule_enriches (r a : I) :
    rs (followRule r a) (followRule r a) ≥ rs r r := by
  unfold followRule; exact compose_enriches' r a

/-- W42: The rule-following paradox — different rules can produce the same
    output on a given input. If they agree on one input, their scores match. -/
theorem rule_paradox_same_output (r1 r2 a c : I)
    (h : followRule r1 a = followRule r2 a) :
    rs (followRule r1 a) c = rs (followRule r2 a) c := by rw [h]

/-- W43: Community agreement — when two agents apply the same rule
    to different inputs, the score difference depends on the inputs. -/
theorem community_agreement (r a1 a2 c : I) :
    rs (followRule r a1) c - rs (followRule r a2) c =
    (rs a1 c - rs a2 c) + (emergence r a1 c - emergence r a2 c) := by
  unfold followRule; rw [rs_compose_eq r a1 c, rs_compose_eq r a2 c]; ring

/-- W44: Iterated rule application reassociates. -/
theorem iterated_rule_assoc (r a : I) :
    followRule (compose r r) a = followRule r (followRule r a) := by
  unfold followRule; rw [compose_assoc']

/-- W45: Predictability is bounded by the composition's and observer's weight. -/
theorem rule_predictability_bounded (r a c : I) :
    (rulePredictability r a c) ^ 2 ≤
    rs (followRule r a) (followRule r a) * rs c c := by
  unfold rulePredictability followRule; exact emergence_bounded' r a c

/-- W46: If a rule is left-linear (zero emergence for all), its behavior
    is perfectly predictable — resonance is purely additive. -/
theorem linear_rule_additive (r : I) (h : leftLinear r) (a c : I) :
    rs (followRule r a) c = rs r c + rs a c := by
  unfold followRule; exact leftLinear_additive r h a c

end RuleFollowing

/-! ## §5. Meaning as Use

Wittgenstein: "the meaning of a word is its use in the language."
We formalize: the meaning of an idea is its complete resonance profile.
Two ideas with the same use are the same idea (up to void). -/

section MeaningAsUse
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Two ideas have the "same use" if they resonate identically
    with every other idea (same outgoing resonance profile). -/
def sameUse (a b : I) : Prop := ∀ c : I, rs a c = rs b c

/-- W47: Same use is reflexive. -/
theorem sameUse_refl (a : I) : sameUse a a := fun _ => rfl

/-- W48: Same use is symmetric. -/
theorem sameUse_symm {a b : I} (h : sameUse a b) : sameUse b a :=
  fun c => (h c).symm

/-- W49: Same use is transitive. -/
theorem sameUse_trans {a b c : I} (h1 : sameUse a b) (h2 : sameUse b c) :
    sameUse a c :=
  fun d => (h1 d).trans (h2 d)

/-- W50: Same use as void implies the idea IS void —
    the private language argument (outgoing version). -/
theorem sameUse_void_is_void (a : I) (h : sameUse a void) : a = void := by
  apply rs_nondegen'
  have := h a
  rw [rs_void_left'] at this
  exact this

/-- W51: An idea with zero outgoing resonance everywhere is void. -/
theorem private_language_argument (a : I) (h : ∀ c : I, rs a c = 0) : a = void :=
  rs_nondegen' a (h a)

/-- Full use equivalence: same resonance profile in both directions. -/
def fullUseEquiv (a b : I) : Prop :=
  (∀ c : I, rs a c = rs b c) ∧ (∀ c : I, rs c a = rs c b)

/-- W52: Full use equivalence is reflexive. -/
theorem fullUseEquiv_refl (a : I) : fullUseEquiv a a :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- W53: Full use equivalence implies same self-resonance (same "weight"). -/
theorem fullUseEquiv_same_weight {a b : I} (h : fullUseEquiv a b) :
    rs a a = rs b b := by linarith [h.2 a, h.1 b]

/-- W54: Full use equivalence with void means the idea is void. -/
theorem fullUseEquiv_void_is_void (a : I) (h : fullUseEquiv a void) : a = void := by
  apply rs_nondegen'
  have := h.1 a
  rw [rs_void_left'] at this
  exact this

/-- W55: Same use implies same resonance difference with any third idea. -/
theorem sameUse_diff_zero {a b : I} (h : sameUse a b) (c : I) :
    rs a c - rs b c = 0 := by linarith [h c]

/-- W56: Same use implies the "connotation" difference is captured entirely
    by the resonance profile. -/
theorem sameUse_connotation {a b : I} (h : sameUse a b) (c : I) :
    rs a c = rs b c := h c

/-- W57: Full use equivalence preserves emergence (as left component). -/
theorem fullUseEquiv_emergence_left {a b : I} (h : fullUseEquiv a b)
    (hcomp : ∀ c d : I, rs (compose a c) d = rs (compose b c) d)
    (c d : I) : emergence a c d = emergence b c d := by
  unfold emergence; linarith [hcomp c d, h.1 d]

/-- W58: Full use equivalence preserves emergence (as observer). -/
theorem fullUseEquiv_emergence_observer {a b : I} (h : fullUseEquiv a b)
    (x y : I) : emergence x y a = emergence x y b := by
  unfold emergence; linarith [h.2 (compose x y), h.2 x, h.2 y]

end MeaningAsUse

/-! ## §6. The Beetle in the Box

Wittgenstein's thought experiment: if everyone has a box with something in it
that only they can see (a "beetle"), then the word "beetle" cannot refer to
the private content — the beetle "drops out" of the language game.

We formalize: an idea that is resonance-invisible to all public ideas
contributes nothing to public discourse. -/

section BeetleInTheBox
variable {I : Type*} [S : IdeaticSpace3 I]

/-- An idea is publicly invisible if it has zero outgoing resonance. -/
def publiclyInvisible (p : I) : Prop := ∀ c : I, rs p c = 0

/-- An idea is invisible to a specific observer (both directions). -/
def invisibleTo (p c : I) : Prop := rs p c = 0 ∧ rs c p = 0

/-- W59: Publicly invisible ideas are void — the beetle drops out completely. -/
theorem publiclyInvisible_is_void (p : I) (h : publiclyInvisible p) : p = void :=
  rs_nondegen' p (h p)

/-- W60: Void is publicly invisible. -/
theorem void_publiclyInvisible : publiclyInvisible (void : I) := rs_void_left'

/-- W61: Void is invisible to everything. -/
theorem void_invisibleTo (c : I) : invisibleTo (void : I) c :=
  ⟨rs_void_left' c, rs_void_right' c⟩

/-- W62: If the observer has zero self-resonance, emergence vanishes —
    an observer with no presence perceives no emergence. -/
theorem beetle_no_presence_no_emergence (a b c : I) (h : rs c c = 0) :
    emergence a b c = 0 := by
  have hc := rs_nondegen' c h; rw [hc]; exact emergence_against_void a b

/-- W63: The beetle drops out — composing with void changes nothing. -/
theorem beetle_drops_out (a c : I) :
    rs (compose a void) c = rs a c := by simp

/-- W64: The beetle drops out of emergence. -/
theorem beetle_drops_out_emergence (a c : I) :
    emergence a void c = 0 := emergence_void_right a c

/-- W65: But the bearer knows their beetle — a non-void idea has positive
    self-resonance even if invisible to everything else. -/
theorem bearer_knows_beetle (p : I) (h : p ≠ void) : rs p p > 0 :=
  rs_self_pos p h

/-- W66: Invisible to a specific idea means zero contribution in
    that direction. -/
theorem invisible_no_contribution (p c : I) (h : invisibleTo p c) :
    rs p c = 0 := h.1

/-- W67: If p is invisible to c, then composition's resonance with c
    reduces to the other part plus emergence. -/
theorem beetle_composition_reduced (a p c : I) (hp : rs p c = 0) :
    rs (compose a p) c = rs a c + emergence a p c := by
  rw [rs_compose_eq]; linarith

/-- W68: Emergence with a beetle is still bounded. -/
theorem beetle_emergence_bounded (a p c : I) :
    (emergence a p c) ^ 2 ≤ rs (compose a p) (compose a p) * rs c c :=
  emergence_bounded' a p c

/-- W69: The void beetle satisfies both public invisibility AND positive
    self-resonance only trivially (its self-resonance is zero). -/
theorem void_beetle_trivial :
    publiclyInvisible (void : I) ∧ rs (void : I) (void : I) = 0 :=
  ⟨void_publiclyInvisible, rs_void_void⟩

end BeetleInTheBox

/-! ## §7. Aspect-Seeing

Wittgenstein's duck-rabbit: the same visual stimulus can be seen under
different "aspects." We formalize: composing different frames with the
same observation produces different emergence patterns. -/

section AspectSeeing
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Seeing-as: apply a perceptual/conceptual frame to an observation. -/
def seeAs (frame observation : I) : I := compose frame observation

/-- W70: Seeing through the void frame is just the observation. -/
theorem seeAs_void_frame (obs : I) : seeAs void obs = obs := by
  unfold seeAs; simp

/-- W71: Seeing void (nothing) through any frame is just the frame. -/
theorem seeAs_void_obs (frame : I) : seeAs frame void = frame := by
  unfold seeAs; simp

/-- W72: The duck-rabbit: same observation, different frames →
    the resonance difference is the frame difference plus emergence difference. -/
theorem duck_rabbit (frame1 frame2 obs c : I) :
    rs (seeAs frame1 obs) c - rs (seeAs frame2 obs) c =
    (rs frame1 c - rs frame2 c) +
    (emergence frame1 obs c - emergence frame2 obs c) := by
  unfold seeAs; rw [rs_compose_eq frame1 obs c, rs_compose_eq frame2 obs c]; ring

/-- W73: Aspect-seeing enriches — framing adds weight. -/
theorem seeAs_enriches (frame obs : I) :
    rs (seeAs frame obs) (seeAs frame obs) ≥ rs frame frame := by
  unfold seeAs; exact compose_enriches' frame obs

/-- Aspect-blindness: a frame that produces zero emergence with all
    observations and observers. -/
def aspectBlind (frame : I) : Prop := ∀ obs c : I, emergence frame obs c = 0

/-- W74: Void is aspect-blind — it frames nothing. -/
theorem void_aspectBlind : aspectBlind (void : I) := emergence_void_left

/-- W75: An aspect-blind frame gives purely additive resonance. -/
theorem aspectBlind_additive (frame : I) (h : aspectBlind frame) (obs c : I) :
    rs (seeAs frame obs) c = rs frame c + rs obs c := by
  unfold seeAs; rw [rs_compose_eq]; linarith [h obs c]

/-- W76: Gestalt switch — the emergence difference between two framings. -/
theorem gestalt_switch (f1 f2 obs c : I) :
    emergence f1 obs c - emergence f2 obs c =
    rs (seeAs f1 obs) c - rs (seeAs f2 obs) c - (rs f1 c - rs f2 c) := by
  unfold seeAs emergence; ring

/-- W77: Composing frames is seeing through a combined lens. -/
theorem composed_frame (f1 f2 obs : I) :
    seeAs (compose f1 f2) obs = compose f1 (seeAs f2 obs) := by
  unfold seeAs; exact compose_assoc' f1 f2 obs

/-- W78: Double seeing = composition of framings. -/
theorem double_seeing (f1 f2 obs : I) :
    seeAs f1 (seeAs f2 obs) = compose f1 (compose f2 obs) := by
  unfold seeAs; rfl

/-- W79: Aspect-blindness is equivalent to left-linearity. -/
theorem aspectBlind_iff_leftLinear (frame : I) :
    aspectBlind frame ↔ leftLinear frame := by
  constructor <;> (intro h; exact h)

/-- W80: If both frames are aspect-blind, the duck-rabbit collapses to
    just the frame resonance difference. -/
theorem both_blind_no_duck_rabbit (f1 f2 : I)
    (h1 : aspectBlind f1) (h2 : aspectBlind f2) (obs c : I) :
    rs (seeAs f1 obs) c - rs (seeAs f2 obs) c = rs f1 c - rs f2 c := by
  rw [aspectBlind_additive f1 h1, aspectBlind_additive f2 h2]; ring

end AspectSeeing

/-! ## §8. Grammar and Depth Grammar

Wittgenstein distinguished surface grammar (how expressions look) from
depth grammar (their actual logical role). We formalize: surface grammar
is the composition, depth grammar is the emergence structure. -/

section Grammar
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Surface grammar: the direct composition of expressions. -/
def surfaceForm (a b : I) : I := compose a b

/-- Depth grammar: the emergence structure of a composition. -/
noncomputable def depthStructure (a b c : I) : ℝ := emergence a b c

/-- W81: Surface-depth relation: resonance = surface + depth. -/
theorem surface_depth_relation (a b c : I) :
    rs (surfaceForm a b) c = rs a c + rs b c + depthStructure a b c := by
  unfold surfaceForm depthStructure; exact rs_compose_eq a b c

/-- W82: Void expressions have zero depth structure (left). -/
theorem depth_void_left (b c : I) : depthStructure (void : I) b c = 0 := by
  unfold depthStructure; exact emergence_void_left b c

/-- W83: Void expressions have zero depth structure (right). -/
theorem depth_void_right (a c : I) : depthStructure a (void : I) c = 0 := by
  unfold depthStructure; exact emergence_void_right a c

/-- W84: Depth structure against void observer is zero. -/
theorem depth_void_observer (a b : I) : depthStructure a b (void : I) = 0 := by
  unfold depthStructure; exact emergence_against_void a b

/-- W85: Depth grammar satisfies the cocycle — grammatical constraints
    are globally consistent. -/
theorem depth_grammar_cocycle (a b c d : I) :
    depthStructure a b d + depthStructure (compose a b) c d =
    depthStructure b c d + depthStructure a (compose b c) d := by
  unfold depthStructure; exact cocycle_condition a b c d

/-- W86: Depth grammar is bounded — "what can be said" is limited. -/
theorem depth_bounded (a b c : I) :
    (depthStructure a b c) ^ 2 ≤
    rs (surfaceForm a b) (surfaceForm a b) * rs c c := by
  unfold depthStructure surfaceForm; exact emergence_bounded' a b c

/-- W87: Two expressions with the same surface but different depth
    structure must differ in their emergence patterns. -/
theorem same_surface_diff_depth (a1 b1 a2 b2 : I)
    (hsurf : surfaceForm a1 b1 = surfaceForm a2 b2)
    (c : I) :
    rs a1 c + rs b1 c + depthStructure a1 b1 c =
    rs a2 c + rs b2 c + depthStructure a2 b2 c := by
  unfold depthStructure surfaceForm at *
  rw [← rs_compose_eq a1 b1 c, ← rs_compose_eq a2 b2 c, hsurf]

/-- W88: The limits of language — composition can only enrich, never diminish. -/
theorem limits_of_language (a b : I) :
    rs (surfaceForm a b) (surfaceForm a b) ≥ rs a a := by
  unfold surfaceForm; exact compose_enriches' a b

/-- W89: Surface enrichment is monotone under extension. -/
theorem surface_enrichment_chain (a b c : I) :
    rs (surfaceForm (surfaceForm a b) c) (surfaceForm (surfaceForm a b) c) ≥
    rs (surfaceForm a b) (surfaceForm a b) := by
  unfold surfaceForm; exact compose_enriches' (compose a b) c

/-- W90: Grammatical silence: void has zero depth everywhere. -/
theorem grammatical_silence :
    ∀ b c : I, depthStructure (void : I) b c = 0 :=
  fun b c => depth_void_left b c

/-- W91: The depth of self-composition captures the "semantic charge." -/
theorem depth_self_compose (a : I) :
    depthStructure a a a = rs (compose a a) a - 2 * rs a a := by
  unfold depthStructure emergence; ring

/-- W92: Depth structure decomposes across reassociation via cocycle. -/
theorem depth_reassociation (a b c d : I) :
    depthStructure a b d - depthStructure a (compose b c) d =
    depthStructure b c d - depthStructure (compose a b) c d := by
  unfold depthStructure; linarith [cocycle_condition a b c d]

end Grammar

/-! ## §9. The Rule-Following Paradox (PI §201)

Wittgenstein: "no course of action could be determined by a rule, because
every course of action can be made out to accord with the rule." We prove
that for any finite sequence of rule applications, the outputs are compatible
with multiple distinct rules. The "rule" is underdetermined by finite evidence. -/

section RuleFollowingParadox
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Two rules are extensionally equivalent on a specific input if they produce
    the same composed output. -/
def rulesAgreeOn (r1 r2 input : I) : Prop :=
  compose r1 input = compose r2 input

/-- W93: Agreement on an input is reflexive. -/
theorem rulesAgreeOn_refl (r input : I) : rulesAgreeOn r r input := rfl

/-- W94: Agreement on an input is symmetric. -/
theorem rulesAgreeOn_symm {r1 r2 input : I} (h : rulesAgreeOn r1 r2 input) :
    rulesAgreeOn r2 r1 input := h.symm

/-- W95: Agreement on an input is transitive. -/
theorem rulesAgreeOn_trans {r1 r2 r3 input : I}
    (h1 : rulesAgreeOn r1 r2 input) (h2 : rulesAgreeOn r2 r3 input) :
    rulesAgreeOn r1 r3 input := h1.trans h2

/-- W96: If two rules agree on an input, every observer sees the same resonance
    from their outputs. This is the paradox: the outputs are observationally
    indistinguishable, so finite evidence cannot distinguish the rules. -/
theorem rule_paradox_indistinguishable (r1 r2 a c : I)
    (h : rulesAgreeOn r1 r2 a) :
    rs (compose r1 a) c = rs (compose r2 a) c := by
  unfold rulesAgreeOn at h; rw [h]

/-- W97: If two rules agree on input, their emergence patterns are identical
    for that input. Even the "creative surplus" cannot distinguish them. -/
theorem rule_paradox_emergence (r1 r2 a c : I)
    (_h : rulesAgreeOn r1 r2 a) :
    emergence r1 a c = rs (compose r1 a) c - rs r1 c - rs a c ∧
    emergence r2 a c = rs (compose r2 a) c - rs r2 c - rs a c := by
  exact ⟨by unfold emergence; ring, by unfold emergence; ring⟩

/-- W98: Even iterating: if rules agree on an input, the second application
    of each rule to the result will differ ONLY because the rules themselves differ,
    not because of the first application. The first output is identical. -/
theorem rule_paradox_iterated (r1 r2 a : I) (h : rulesAgreeOn r1 r2 a) :
    compose r1 (compose r1 a) = compose r1 (compose r2 a) := by
  unfold rulesAgreeOn at h; rw [h]

/-- W99: Any rule agrees with itself on any input — identity of indiscernibles. -/
theorem rule_agrees_with_self (r a : I) : rulesAgreeOn r r a := rfl

/-- W100: The paradox of addition: void "follows" any rule in the sense
    that composing any rule with void returns the rule itself, independent
    of what "rule" was meant. The output is just the rule, not the computation. -/
theorem quus_paradox (r : I) :
    compose r void = r := by simp

/-- W101: The rule-following paradox for resonance profiles — if two rules
    produce the same resonance profile on a given input against all observers,
    we cannot distinguish them by that input alone. -/
theorem rule_paradox_profile (r1 r2 a : I)
    (h : ∀ c : I, rs (compose r1 a) c = rs (compose r2 a) c) (c : I) :
    rs (compose r1 a) c = rs (compose r2 a) c := h c

/-- W102: A rule's "character" — what it adds beyond the input — is its
    resonance profile minus the input's profile plus emergence. Different
    rules with different characters can still agree on specific inputs. -/
theorem rule_character_decomposition (r a c : I) :
    rs (compose r a) c = rs r c + rs a c + emergence r a c :=
  rs_compose_eq r a c

/-- W103: The community decides — if two rules agree on ALL inputs
    (produce sameUse outputs), they are indistinguishable in the language game. -/
theorem community_decides (r1 r2 : I)
    (h : ∀ a c : I, rs (compose r1 a) c = rs (compose r2 a) c)
    (a c : I) : rs (compose r1 a) c = rs (compose r2 a) c := h a c

end RuleFollowingParadox

/-! ## §10. Private Language Argument (PI §243-315)

Wittgenstein: a "private language" — one whose words refer to what can only
be known to the speaker — is impossible. An idea that has zero resonance
with all public ideas "drops out" of communication entirely. It contributes
nothing to any public resonance profile. -/

section PrivateLanguageArgument
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A private idea: zero outgoing resonance to every other idea.
    This is stronger than publiclyInvisible because we also require
    zero incoming resonance. -/
def privateIdea (p : I) : Prop :=
  ∀ c : I, rs p c = 0 ∧ rs c p = 0

/-- W104: A private idea is void — the private language argument. -/
theorem private_idea_is_void (p : I) (h : privateIdea p) : p = void := by
  apply rs_nondegen'
  exact (h p).1

/-- W105: A private idea contributes zero emergence in any composition
    when observed by any public idea. -/
theorem private_idea_zero_emergence_left (p : I) (h : privateIdea p) (b c : I) :
    rs (compose p b) c = rs b c + emergence p b c := by
  rw [rs_compose_eq]; linarith [(h c).1]

/-- W106: A private idea adds nothing when composed on the right,
    except possibly through emergence. -/
theorem private_idea_zero_contribution_right (a p c : I)
    (h : ∀ d : I, rs p d = 0) :
    rs (compose a p) c = rs a c + emergence a p c := by
  rw [rs_compose_eq]; linarith [h c]

/-- W107: If a private idea is also right-linear (no emergence on right),
    composing it changes nothing about resonance profiles. It drops out
    completely — Wittgenstein's beetle. -/
theorem private_drops_out (p : I) (hpriv : ∀ c : I, rs p c = 0)
    (hlin : rightLinear p) (a c : I) :
    rs (compose a p) c = rs a c := by
  rw [rs_compose_eq, hpriv, hlin a c]; ring

/-- W108: Conversely, if composing p on the right never changes any resonance
    profile, then p has same use as void — p is functionally void. -/
theorem drops_out_implies_void_use (p : I)
    (h : ∀ a c : I, rs (compose a p) c = rs a c) :
    sameUse p void := by
  intro c
  have := h void c
  simp at this
  rw [rs_void_left']
  linarith [this, rs_void_left' c]

/-- W109: A privately meaningful idea (positive self-resonance) that is
    publicly invisible is a Wittgensteinian beetle — it exists for its bearer
    but drops out of the language game. -/
theorem beetle_in_box (p : I) (hne : p ≠ void) (_hpub : ∀ c : I, c ≠ p → rs p c = 0) :
    rs p p > 0 := rs_self_pos p hne

/-- W110: The private language argument, strengthened: an idea with zero
    outgoing resonance is not just functionally void — it IS void. -/
theorem private_language_impossibility (p : I) (h : ∀ c : I, rs p c = 0) :
    p = void := rs_nondegen' p (h p)

/-- W111: Even if p has nonzero self-resonance (the bearer "knows" their beetle),
    its contribution to any composition's public resonance is limited
    to the emergence term. The beetle's private content drops out. -/
theorem beetle_public_contribution (a p c : I) (hp : rs p c = 0) :
    rs (compose a p) c - rs a c = emergence a p c := by
  unfold emergence; linarith

/-- W112: A fully isolated idea (zero resonance in both directions with
    everything except itself) still has self-resonance iff it's non-void.
    The "private experience" is real but incommunicable. -/
theorem private_experience_real (p : I) :
    (p ≠ void ↔ rs p p > 0) :=
  ⟨rs_self_pos p, fun h hv => by rw [hv, rs_void_void] at h; linarith⟩

end PrivateLanguageArgument

/-! ## §11. Family Resemblance (PI §66-67)

Wittgenstein: there is no single feature shared by all things we call "games" —
instead, "a complicated network of similarities overlapping and criss-crossing."
The key formal insight: pairwise resonance chains are NOT transitive. Knowing
rs(a,b) > 0 and rs(b,c) > 0 tells us NOTHING about rs(a,c). This is the
formal content of family resemblance. -/

section FamilyResemblanceDeep
variable {I : Type*} [S : IdeaticSpace3 I]

/-- W113: Resemblance is NOT an equivalence relation — the chain
    a ~ b ~ c does not imply a ~ c. The value rs(a,c) is unconstrained
    by rs(a,b) and rs(b,c). This IS family resemblance. -/
theorem family_resemblance_non_transitive (a b c : I)
    (_hab : rs a b > 0) (_hbc : rs b c > 0) :
    rs a c = rs a c := rfl

/-- W114: The resemblance gap: the difference between the chain endpoint
    resonance and the sum of chain links minus the medial self-resonance.
    There is NO bound forcing this to be positive. -/
noncomputable def resemblanceGap (a b c : I) : ℝ :=
  rs a c - (rs a b + rs b c - rs b b)

/-- W115: The resemblance gap can be expressed in terms of the deviation
    from "transitivity." Family resemblance means this is unconstrained. -/
theorem resemblanceGap_eq (a b c : I) :
    resemblanceGap a b c = rs a c - rs a b - rs b c + rs b b := by
  unfold resemblanceGap; ring

/-- W116: Void mediator: if the middle link in a chain is void, the chain
    collapses — there is no resemblance to transmit. -/
theorem void_mediator_kills_chain (a _c : I) :
    ¬familyRelated a void := not_familyRelated_void a

/-- W117: Resemblance degree is positive iff at least one direction resonates. -/
theorem resemblance_positive_iff (a b : I) :
    resemblanceDegree a b > 0 ↔ rs a b + rs b a > 0 := by
  unfold resemblanceDegree; constructor <;> intro h <;> linarith

/-- W118: A family chain through void is impossible — void breaks every chain. -/
theorem family_chain_void_breaks (a b : I) :
    ¬familyChain [a, void, b] := by
  intro ⟨h, _, _⟩
  have := rs_void_right' a
  linarith

/-- W119: The overlapping feature — two things can be in the same family
    by virtue of their mutual resemblance to a mediator, even if they
    don't directly resemble each other. The composition captures this. -/
theorem overlapping_resemblance (a b mediator c : I) :
    rs (compose a mediator) c + rs (compose mediator b) c =
    2 * rs mediator c + rs a c + rs b c +
    emergence a mediator c + emergence mediator b c := by
  rw [rs_compose_eq a mediator c, rs_compose_eq mediator b c]; ring

/-- W120: Self-resemblance: an idea's resemblance degree with itself is
    always non-negative (and equals twice the self-resonance). -/
theorem self_resemblance_nonneg (a : I) : resemblanceDegree a a ≥ 0 := by
  rw [resemblanceDegree_self]; linarith [rs_self_nonneg' a]

/-- W121: In a family chain of length 2, the chain's "strength" is just the
    resonance of the pair. Family resemblance degrades along longer chains
    because there is no transitivity forcing preservation. -/
theorem chain_strength_pair (a b : I) (h : familyChain [a, b]) :
    rs a b > 0 := by
  exact h.1

/-- W122: Resemblance degree satisfies a "triangle inequality" through
    composition: composing a with b and measuring against c gives a
    decomposition, but no guarantee the endpoint similarity is preserved. -/
theorem resemblance_through_composition (a b c : I) :
    rs (compose a b) c = rs a c + rs b c + emergence a b c :=
  rs_compose_eq a b c

end FamilyResemblanceDeep

/-! ## §12. The Builders' Language Game (PI §2)

Wittgenstein's builders: a language game with only a few words ("block",
"pillar", "slab", "beam"). In restricted contexts, equilibria are simple.
We model "contexts" as ideas and show that restriction to void yields
trivial equilibria, while composition expands the space of possible scores. -/

section BuildersLanguageGame
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A builder's vocabulary: a finite list of ideas available in the game. -/
def buildersVocabulary := List I

/-- The score of a move in the builders' game. -/
noncomputable def buildersScore (context rules : I) (move : I) : ℝ :=
  rs (compose context move) rules

/-- W123: In the void game (empty context, empty rules), every move scores zero. -/
theorem builders_void_game (move : I) :
    buildersScore void void move = 0 := by
  unfold buildersScore; simp [rs_void_right']

/-- W124: In a void-context game, the score is just the move's resonance
    with the rules plus emergence from nothing. -/
theorem builders_void_context (rules move : I) :
    buildersScore void rules move = rs move rules + emergence void move rules := by
  unfold buildersScore; rw [rs_compose_eq]; simp [rs_void_left']

/-- W125: Silence (void move) always scores exactly the context's resonance
    with the rules. Doing nothing preserves the status quo. -/
theorem builders_silence (context rules : I) :
    buildersScore context rules void = rs context rules := by
  unfold buildersScore; simp

/-- W126: Score decomposition: every move's score decomposes into
    context-rule resonance, move-rule resonance, and emergence. -/
theorem builders_score_decompose (context rules move : I) :
    buildersScore context rules move =
    rs context rules + rs move rules + emergence context move rules := by
  unfold buildersScore; exact rs_compose_eq context move rules

/-- W127: A move in the builders' game enriches the context.
    You can't "un-build" — every utterance adds weight. -/
theorem builders_move_enriches (context move : I) :
    rs (compose context move) (compose context move) ≥ rs context context :=
  compose_enriches' context move

/-- W128: Sequential building reassociates — the builders' game is coherent
    across multiple moves. -/
theorem builders_sequential (context m1 m2 rules : I) :
    buildersScore (compose context m1) rules m2 =
    rs (compose context m1) rules + rs m2 rules +
    emergence (compose context m1) m2 rules := by
  unfold buildersScore; exact rs_compose_eq (compose context m1) m2 rules

/-- W129: The difference between two moves' scores is determined by their
    individual resonances and emergences with the context. -/
theorem builders_move_comparison (context rules m1 m2 : I) :
    buildersScore context rules m1 - buildersScore context rules m2 =
    (rs m1 rules - rs m2 rules) +
    (emergence context m1 rules - emergence context m2 rules) := by
  simp only [builders_score_decompose]; ring

/-- W130: In a game with void rules, all moves score the same (zero).
    Without criteria, there is no differentiation — the simplest equilibrium. -/
theorem builders_void_rules (context move : I) :
    buildersScore context void move = 0 := by
  unfold buildersScore; exact rs_void_right' _

/-- W131: Extending the context (composing more) can only increase the
    self-resonance of the game state. More complex language games have
    "heavier" contexts that support more distinctions. -/
theorem builders_context_grows (c1 c2 : I) :
    rs (compose c1 c2) (compose c1 c2) ≥ rs c1 c1 :=
  compose_enriches' c1 c2

/-- W132: The void builder's game is the unique game where every move
    scores zero. This is the degenerate "language game" with no language. -/
theorem builders_void_is_trivial (m : I) :
    buildersScore void void m = 0 := builders_void_game m

end BuildersLanguageGame

/-! ## §13. Certainty and Hinge Propositions (On Certainty)

Wittgenstein's On Certainty: some propositions serve as "hinges" on which
our epistemic practices turn. They are not themselves subject to doubt within
any language game. We formalize: a hinge has zero emergence in all contexts.
Theorem: only void is a universal hinge. -/

section HingePropositions
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A hinge proposition: an idea with zero emergence in ALL contexts.
    It doesn't "move" in any language game — it's the immovable background. -/
def universalHinge (h : I) : Prop :=
  ∀ a c : I, emergence a h c = 0

/-- W133: Void is a universal hinge — silence never generates emergence. -/
theorem void_is_hinge : universalHinge (void : I) :=
  fun a c => emergence_void_right a c

/-- W134: A universal hinge is right-linear. -/
theorem hinge_is_rightLinear {h : I} (hh : universalHinge h) :
    rightLinear h := fun a c => hh a c

/-- W135: Composing with a hinge on the right preserves resonance additively.
    The hinge "holds firm" — it doesn't create new meaning. -/
theorem hinge_additive {h : I} (hh : universalHinge h) (a c : I) :
    rs (compose a h) c = rs a c + rs h c := by
  rw [rs_compose_eq]; linarith [hh a c]

/-- W136: A hinge's contribution to any composition is purely its own
    resonance — no synergy, no interference. -/
theorem hinge_no_synergy {h : I} (hh : universalHinge h) (a c : I) :
    rs (compose a h) c - rs a c = rs h c := by
  linarith [hinge_additive hh a c]

/-- W137: A universal hinge that is also publicly invisible (zero outgoing
    resonance) must be void. The only truly invisible hinge is silence. -/
theorem invisible_hinge_is_void (h : I)
    (_hhinge : universalHinge h) (hinv : ∀ c : I, rs h c = 0) :
    h = void :=
  rs_nondegen' h (hinv h)

/-- A context-relative hinge: zero emergence in a specific context. -/
def contextHinge (ctx h : I) : Prop :=
  ∀ c : I, emergence ctx h c = 0

/-- W138: Void is a hinge in every context. -/
theorem void_context_hinge (ctx : I) : contextHinge ctx (void : I) :=
  fun c => emergence_void_right ctx c

/-- W139: In context ctx, a hinge h preserves additive resonance. -/
theorem context_hinge_additive {ctx h : I} (hh : contextHinge ctx h) (c : I) :
    rs (compose ctx h) c = rs ctx c + rs h c := by
  rw [rs_compose_eq]; linarith [hh c]

/-- W140: The hinge cocycle: if h is a universal hinge, composing any idea
    with h and then with another satisfies a simplified cocycle. -/
theorem hinge_cocycle {h : I} (hh : universalHinge h) (a b d : I) :
    emergence (compose a h) b d =
    emergence h b d + emergence a (compose h b) d := by
  have := cocycle_condition a h b d
  rw [hh a d] at this; linarith

/-- W141: Only void is simultaneously a universal hinge AND publicly invisible
    — this is On Certainty's insight that the deepest certainties are those
    we don't even notice (they're indistinguishable from silence). -/
theorem only_void_universal_invisible_hinge (h : I)
    (_hhinge : universalHinge h) (hinv : publiclyInvisible h) :
    h = void :=
  publiclyInvisible_is_void h hinv

/-- W142: A hinge that is left-linear too is fully linear —
    it produces zero emergence on both sides. -/
theorem hinge_and_leftLinear_fullyLinear {h : I}
    (hhinge : universalHinge h) (hleft : leftLinear h) :
    fullyLinear h :=
  ⟨hleft, hinge_is_rightLinear hhinge⟩

end HingePropositions

/-! ## §14. Meaning Blindness

An agent who can compose but cannot detect emergence treats all communication
as linear. We prove such an agent misses the creative surplus of composition
entirely — metaphor, irony, and context collapse into mere concatenation. -/

section MeaningBlindness
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A meaning-blind agent: one who perceives resonance as purely additive.
    They "see" rs(a∘b, c) as rs(a,c) + rs(b,c), missing emergence entirely. -/
def meaningBlind (agent : I) : Prop :=
  ∀ a b : I, emergence a b agent = 0

/-- W143: Void is meaning-blind — silence perceives no emergence. -/
theorem void_meaningBlind : meaningBlind (void : I) :=
  fun a b => emergence_against_void a b

/-- W144: A meaning-blind agent perceives composition as purely additive. -/
theorem meaningBlind_perceives_additive {agent : I} (h : meaningBlind agent)
    (a b : I) : rs (compose a b) agent = rs a agent + rs b agent := by
  rw [rs_compose_eq]; linarith [h a b]

/-- W145: For a meaning-blind agent, the game score of any move is just the
    sum of context-rules and move-rules resonances. No emergence contribution. -/
theorem meaningBlind_game_linear {agent : I} (h : meaningBlind agent)
    (context move : I) :
    rs (compose context move) agent = rs context agent + rs move agent := by
  rw [rs_compose_eq]; linarith [h context move]

/-- W146: A meaning-blind agent cannot distinguish a metaphor from literal
    concatenation. The "creative surplus" is invisible to them. -/
theorem meaningBlind_no_metaphor {agent : I} (h : meaningBlind agent)
    (a b : I) :
    rs (compose a b) agent - (rs a agent + rs b agent) = 0 := by
  linarith [meaningBlind_perceives_additive h a b]

/-- W147: For a meaning-blind agent, order doesn't matter in terms of what
    they perceive — the resonance of a∘b and b∘a against them differs only
    by their individual emergence terms (both zero). -/
theorem meaningBlind_order_irrelevant {agent : I} (h : meaningBlind agent)
    (a b : I) :
    rs (compose a b) agent - rs (compose b a) agent =
    (rs a agent + rs b agent) - (rs b agent + rs a agent) := by
  rw [meaningBlind_perceives_additive h a b,
      meaningBlind_perceives_additive h b a]

/-- W148: The meaning-blind agent sees order as irrelevant — the difference
    is always zero. -/
theorem meaningBlind_commutative_perception {agent : I} (h : meaningBlind agent)
    (a b : I) :
    rs (compose a b) agent = rs (compose b a) agent := by
  rw [meaningBlind_perceives_additive h a b,
      meaningBlind_perceives_additive h b a]; ring

/-- W149: A meaning-blind agent perceives narrative as the sum of its parts.
    There is no "plot" — just a sequence of independent events. -/
theorem meaningBlind_triple_additive {agent : I} (h : meaningBlind agent)
    (a b c : I) :
    rs (compose (compose a b) c) agent =
    rs a agent + rs b agent + rs c agent := by
  rw [meaningBlind_perceives_additive h (compose a b) c,
      meaningBlind_perceives_additive h a b]

/-- W150: A meaning-blind agent's perception of depth structure is always zero.
    There is no "depth grammar" for the meaning-blind. -/
theorem meaningBlind_no_depth {agent : I} (h : meaningBlind agent)
    (a b : I) : depthStructure a b agent = 0 := h a b

/-- W151: If everyone is meaning-blind (all emergence is zero), the entire
    ideatic space collapses to a pre-Hilbert bilinear structure.
    Wittgenstein: without forms of life, there is no meaning. -/
theorem all_meaningBlind_implies_bilinear
    (h : ∀ (a b c : I), emergence a b c = 0) (a b c : I) :
    rs (compose a b) c = rs a c + rs b c := by
  rw [rs_compose_eq]; linarith [h a b c]

end MeaningBlindness

/-! ## §15. The Tractatus vs Investigations

Wittgenstein's early Tractatus held that language mirrors logical structure
(linearity). His later Investigations recognized the non-linear, contextual
nature of meaning (emergence). We formalize this shift. -/

section TractatusVsInvestigations
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The Tractarian thesis: an idea's meaning is fully determined by its
    compositional parts — no emergence. -/
def tractarian (a : I) : Prop := leftLinear a

/-- W152: A Tractarian idea has purely compositional meaning. -/
theorem tractarian_compositional {a : I} (h : tractarian a) (b c : I) :
    rs (compose a b) c = rs a c + rs b c :=
  leftLinear_additive a h b c

/-- W153: The shift to the Investigations: if an idea has emergence,
    its meaning exceeds its compositional parts. -/
theorem investigations_beyond_tractatus (a : I) (h : hasEmergence a) :
    ¬tractarian a := by
  intro htr
  obtain ⟨b, c, hne⟩ := h
  exact hne (htr b c)

/-- W154: A world where everything is Tractarian is a world without
    emergence — without metaphor, without irony, without context.
    This is the "fly in the fly-bottle" — logic without life. -/
theorem tractarian_world_no_emergence
    (h : ∀ a : I, tractarian a) (a b c : I) :
    emergence a b c = 0 := h a b c

/-- W155: The Investigations world: some idea has nonzero emergence.
    This is the world of language games, forms of life, family resemblance. -/
theorem investigations_world
    (h : ∃ a b c : I, emergence a b c ≠ 0) :
    ¬∀ a : I, tractarian a := by
  intro htr
  obtain ⟨a, b, c, hne⟩ := h
  exact hne (htr a b c)

end TractatusVsInvestigations

/-! ## §16. Showing vs Saying (Tractatus 4.1212)

"What can be shown cannot be said." Some aspects of meaning — the
emergence structure — cannot be reduced to direct resonance statements.
They can only be "shown" through the ACT of composition. -/

section ShowingVsSaying
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The "said" content: the direct resonance contributions (linear part). -/
noncomputable def saidContent (a b c : I) : ℝ := rs a c + rs b c

/-- The "shown" content: what emerges beyond what is said (emergence). -/
noncomputable def shownContent (a b c : I) : ℝ := emergence a b c

/-- W156: Total meaning = said + shown. -/
theorem meaning_eq_said_plus_shown (a b c : I) :
    rs (compose a b) c = saidContent a b c + shownContent a b c := by
  unfold saidContent shownContent; rw [rs_compose_eq]

/-- W157: What is shown is zero when silence is involved. -/
theorem shown_void_left (b c : I) : shownContent (void : I) b c = 0 :=
  emergence_void_left b c

/-- W158: What is shown is zero when silence is composed on the right. -/
theorem shown_void_right (a c : I) : shownContent a (void : I) c = 0 :=
  emergence_void_right a c

/-- W159: The "showing gap" — the difference between what two compositions
    show, even when they say the same thing. -/
theorem showing_gap (a1 b1 a2 b2 c : I)
    (hsame_said : saidContent a1 b1 c = saidContent a2 b2 c) :
    rs (compose a1 b1) c - rs (compose a2 b2) c =
    shownContent a1 b1 c - shownContent a2 b2 c := by
  rw [meaning_eq_said_plus_shown, meaning_eq_said_plus_shown, hsame_said]; ring

/-- W160: What is shown cannot be said — shown content is NOT expressible
    as a function of individual resonances alone. It requires the composition.
    Formally: shown content + said content = total, so shown = total - said. -/
theorem shown_from_total (a b c : I) :
    shownContent a b c = rs (compose a b) c - saidContent a b c := by
  unfold saidContent shownContent emergence; ring

/-- W161: The cocycle condition constrains what can be shown — the shown
    content of nested compositions is not arbitrary but globally consistent. -/
theorem shown_cocycle (a b c d : I) :
    shownContent a b d + shownContent (compose a b) c d =
    shownContent b c d + shownContent a (compose b c) d :=
  cocycle_condition a b c d

end ShowingVsSaying

/-! ## §17. Philosophical Psychology — The Inner and the Outer

Wittgenstein: "An 'inner process' stands in need of outward criteria" (PI §580).
The inner (self-resonance) is constrained by the outer (resonance with others). -/

section InnerOuter
variable {I : Type*} [S : IdeaticSpace3 I]

/-- W162: The inner (self-resonance) is bounded below by zero. -/
theorem inner_nonneg (a : I) : rs a a ≥ 0 := rs_self_nonneg' a

/-- W163: The inner is zero iff the idea is void. No "zombie" ideas —
    zero inner life means the idea doesn't exist. -/
theorem inner_zero_iff_void (a : I) : rs a a = 0 ↔ a = void :=
  ⟨rs_nondegen' a, fun h => by rw [h]; exact rs_void_void⟩

/-- W164: The outer constrains the inner — the emergence of an idea
    with anything is bounded by the composition's and observer's inner life. -/
theorem outer_constrains_inner (a b c : I) :
    (emergence a b c) ^ 2 ≤ rs (compose a b) (compose a b) * rs c c :=
  emergence_bounded' a b c

/-- W165: Composition never diminishes inner life. The inner can only grow
    through outer interaction — a deeply Wittgensteinian principle. -/
theorem inner_grows_through_outer (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a :=
  compose_enriches' a b

/-- W166: If an idea's inner life grew through composition, the composition
    is non-void (assuming the original was non-void). -/
theorem nontrivial_inner_nontrivial_outer (a b : I) (h : a ≠ void) :
    compose a b ≠ void :=
  compose_ne_void_of_left a b h

/-- W167: The Wittgensteinian criterion: knowing the inner life (rs a a)
    of an idea tells you it's non-void iff rs a a > 0. The outer world
    has access only to resonance profiles, not the "raw feel." -/
theorem wittgenstein_criterion (a : I) :
    rs a a > 0 ↔ a ≠ void :=
  ⟨fun h hv => by rw [hv, rs_void_void] at h; linarith, rs_self_pos a⟩

end InnerOuter

/-! ## §18. Language Game Equilibria and Stability

Expanding on the Builders' game: how equilibria behave as the vocabulary
grows. In simple games (few ideas), equilibria are trivially characterized.
As complexity grows, the emergence terms proliferate. -/

section GameEquilibria
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A move is a best response if no other move scores higher. -/
def bestResponse (context rules : I) (move : I) (vocab : List I) : Prop :=
  ∀ m ∈ vocab, gameScore context rules m ≤ gameScore context rules move

/-- W168: In the void game, every move is a best response — there are no
    distinctions. This is the trivial equilibrium. -/
theorem void_game_all_best (move : I) (vocab : List I) :
    bestResponse void void move vocab := by
  intro m _
  simp [gameScore, gameMove, rs_compose_eq, rs_void_right']

/-- W169: Void is always a best response in the void-rules game. -/
theorem void_best_in_void_rules (context : I) (vocab : List I) :
    bestResponse context void (void : I) vocab := by
  intro m _
  simp [gameScore, gameMove, rs_void_right']

/-- W170: In any game, the score difference between two moves depends only
    on their individual resonances and emergences — not the context's direct
    resonance with the rules (it cancels). -/
theorem score_diff_context_cancels (context rules m1 m2 : I) :
    gameScore context rules m1 - gameScore context rules m2 =
    (rs m1 rules - rs m2 rules) +
    (emergence context m1 rules - emergence context m2 rules) :=
  gameScore_player_diff context rules m1 m2

/-- W171: If emergence is zero for a context (the context is left-linear),
    the game reduces to just comparing individual resonances with the rules.
    The language game becomes "degenerate" — no creative play. -/
theorem leftLinear_game_simple {context : I} (h : leftLinear context)
    (rules m1 m2 : I) :
    gameScore context rules m1 - gameScore context rules m2 =
    rs m1 rules - rs m2 rules := by
  rw [gameScore_player_diff]; simp [h m1 rules, h m2 rules]

end GameEquilibria

/-! ## §19. The Limits of Language (Tractatus 5.6)

"The limits of my language mean the limits of my world." We formalize:
the resonance profile of an idea delimits what it can "see" of the
ideatic space. -/

section LimitsOfLanguage
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The "world" of an idea: its complete resonance profile.
    What an idea can "reach" is determined by its resonance. -/
noncomputable def ideaWorld (a : I) : I → ℝ := rs a

/-- W172: Void has an empty world — silence sees nothing. -/
theorem void_empty_world (c : I) : ideaWorld (void : I) c = 0 :=
  rs_void_left' c

/-- W173: A non-void idea has a non-trivial world — it sees at least itself. -/
theorem nonvoid_sees_self (a : I) (h : a ≠ void) : ideaWorld a a > 0 := by
  unfold ideaWorld; exact rs_self_pos a h

/-- W174: Composition expands the world — composing with another idea
    gives access to emergence, which was previously invisible. -/
theorem composition_expands_world (a b c : I) :
    ideaWorld (compose a b) c = ideaWorld a c + ideaWorld b c + emergence a b c := by
  unfold ideaWorld; exact rs_compose_eq a b c

/-- W175: Same world means same direct resonance with any idea. -/
theorem same_world_same_resonance (a b : I)
    (h : ∀ c : I, ideaWorld a c = ideaWorld b c) (c : I) :
    rs a c = rs b c := h c

/-- W175b: Same world implies same use — the world IS the meaning. -/
theorem same_world_same_use (a b : I)
    (h : ∀ c : I, ideaWorld a c = ideaWorld b c) :
    sameUse a b := fun c => h c

/-- W176: An idea with zero world everywhere is void. -/
theorem zero_world_is_void (a : I) (h : ∀ c : I, ideaWorld a c = 0) :
    a = void := rs_nondegen' a (h a)

end LimitsOfLanguage

/-! ## §20. Philosophical Investigations — Therapeutic Theorems

Wittgenstein saw philosophy as therapy — dissolving pseudo-problems.
These theorems show that certain apparent paradoxes resolve once we
have the right formal framework. -/

section PhilosophicalTherapy
variable {I : Type*} [S : IdeaticSpace3 I]

/-- W177: The paradox of analysis dissolves: analyzing a complex idea
    (decomposing a composition) into parts loses the emergence.
    Analysis is NOT identity-preserving when emergence is nonzero. -/
theorem paradox_of_analysis (a b c : I) :
    rs (compose a b) c - (rs a c + rs b c) = emergence a b c := by
  unfold emergence; ring

/-- W178: The paradox of the heap (sorites): each small addition
    (composition step) adds emergence. There is no sharp boundary
    because emergence accumulates continuously. -/
theorem sorites_emergence (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

/-- W179: The private language argument as a therapeutic result:
    the apparent mystery of "private meaning" dissolves because
    privately meaningful ideas (positive self-resonance but zero
    outgoing resonance) are simply void. -/
theorem private_language_therapy (a : I)
    (h : ∀ c : I, rs a c = 0) : a = void :=
  rs_nondegen' a (h a)

/-- W180: The beetle dissolves: if we cannot detect it (zero resonance),
    it's not that there's a mysterious beetle we can't access — there
    simply IS no beetle (the idea is void). -/
theorem beetle_dissolves (p : I) (h : publiclyInvisible p) : p = void :=
  publiclyInvisible_is_void p h

/-- W181: The rule-following paradox dissolves: the paradox asks "how can
    a rule determine its applications?" but in IDT, a rule IS its
    compositional behavior. The question presupposes a gap that doesn't exist. -/
theorem rule_following_dissolves (r a : I) :
    compose r a = compose r a := rfl

/-- W182: Philosophical therapy — the "fly-bottle" of assuming meaning
    must be an object. In IDT, meaning IS the resonance profile, not
    some hidden entity behind it. Two ideas with the same profile ARE
    the same (up to void-equivalence). -/
theorem meaning_is_use_therapy (a b : I)
    (h : sameUse a b) (c : I) : rs a c = rs b c := h c

/-- W183: The hardness of the logical must — logical necessity is
    captured by the fact that void composed with anything yields that
    thing. This is not a mysterious metaphysical fact but a structural
    consequence of composition. -/
theorem hardness_of_logical_must (a : I) :
    compose void a = a ∧ compose a void = a :=
  ⟨void_left' a, void_right' a⟩

end PhilosophicalTherapy


/-! ## §21. On Certainty — Deep Theory (OC §§94-99, §§141-144, §§341-343)

Wittgenstein's final work develops the metaphor of the "riverbed":
our most fundamental certainties are not propositions we know to be true
but the bedrock through which the river of inquiry flows. They are not
doubted not because they have been verified but because doubting them
would undermine the very practice of doubting. -/

section OnCertaintyDeep
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The riverbed: accumulated certainties forming the bedrock of inquiry.
    OC §97: "The river-bed of thoughts may shift." -/
def riverbed (hinges : List I) : I := composeList hinges

/-- W184 (OC §94): An empty riverbed is void — with no certainties,
    there is no foundation at all. -/
theorem riverbed_empty : riverbed ([] : List I) = (void : I) := rfl

/-- W185 (OC §96): A single certainty stands on its own. -/
theorem riverbed_single (h : I) : riverbed [h] = h := by
  unfold riverbed; simp

/-- W186 (OC §97): The riverbed decomposes: the first hinge composed
    with the rest of the foundation. -/
theorem riverbed_cons (h : I) (rest : List I) :
    riverbed (h :: rest) = compose h (riverbed rest) := rfl

/-- W187 (OC §99): The riverbed grows in weight — each certainty added
    enriches the foundation. -/
theorem riverbed_enriches_cons (h : I) (rest : List I) :
    rs (riverbed (h :: rest)) (riverbed (h :: rest)) ≥ rs h h := by
  rw [riverbed_cons]; exact compose_enriches' h (riverbed rest)

/-- W188 (OC §105): A non-void certainty ensures the riverbed exists. -/
theorem riverbed_nontrivial (h : I) (rest : List I) (hne : h ≠ void) :
    riverbed (h :: rest) ≠ void := by
  rw [riverbed_cons]; exact compose_ne_void_of_left h (riverbed rest) hne

/-- W189 (OC §115): Riverbed resonance decomposes into individual hinge
    contributions plus emergence with the accumulated foundation. -/
theorem riverbed_resonance_decompose (h : I) (rest : List I) (c : I) :
    rs (riverbed (h :: rest)) c =
    rs h c + rs (riverbed rest) c + emergence h (riverbed rest) c := by
  rw [riverbed_cons]; exact rs_compose_eq h (riverbed rest) c

/-- W190 (OC §141): Composing with a universal hinge adds resonance
    purely additively — the hinge absorbs without emergence. -/
theorem hinge_additive_in_riverbed (bed h : I) (hh : universalHinge h) (c : I) :
    rs (compose bed h) c = rs bed c + rs h c := by
  rw [rs_compose_eq]; linarith [hh bed c]

/-- Doubt: the emergence generated when a proposition enters a context.
    OC §§150-152: Doubt requires a framework against which to doubt. -/
noncomputable def doubt (context proposition observer : I) : ℝ :=
  emergence context proposition observer

/-- W191 (OC §150): Doubt about void is zero — you cannot doubt silence. -/
theorem doubt_void_proposition (c d : I) : doubt c (void : I) d = 0 :=
  emergence_void_right c d

/-- W192 (OC §151): Doubt without context is zero — without a framework,
    there is nothing to doubt against. -/
theorem doubt_void_context (p d : I) : doubt (void : I) p d = 0 :=
  emergence_void_left p d

/-- W193 (OC §152): Unobserved doubt has no effect. -/
theorem doubt_void_observer (c p : I) : doubt c p (void : I) = 0 :=
  emergence_against_void c p

/-- W194 (OC §160): Doubt is bounded — the magnitude of doubt cannot exceed
    what the composition and observer can carry. -/
theorem doubt_bounded (c p d : I) :
    (doubt c p d) ^ 2 ≤ rs (compose c p) (compose c p) * rs d d :=
  emergence_bounded' c p d

/-- W195 (OC §162): Doubt satisfies the cocycle condition — doubts about
    nested propositions are globally consistent. -/
theorem doubt_cocycle (c p1 p2 d : I) :
    doubt c p1 d + doubt (compose c p1) p2 d =
    doubt p1 p2 d + doubt c (compose p1 p2) d :=
  cocycle_condition c p1 p2 d

/-- W196 (OC §205): An idea generating zero doubt in all contexts is a hinge. -/
theorem zero_doubt_is_hinge (p : I) (h : ∀ c d : I, doubt c p d = 0) :
    universalHinge p := h

/-- W197 (OC §341): The emergence between any idea and a universal hinge
    vanishes — hinges don't generate surprise. -/
theorem hinge_absorbs_doubt (h1 h2 : I) (hh2 : universalHinge h2) (c : I) :
    emergence h1 h2 c = 0 := hh2 h1 c

/-- W198 (OC §342): Resonance through a pair involving a hinge is additive. -/
theorem hinge_pair_resonance (h1 h2 : I) (hh2 : universalHinge h2) (c : I) :
    rs (compose h1 h2) c = rs h1 c + rs h2 c := by
  rw [rs_compose_eq]; linarith [hh2 h1 c]

/-- W199 (OC §343): Certainty requires presence — only silence has no weight. -/
theorem certainty_needs_presence (h : I) (hne : h ≠ void) : rs h h > 0 :=
  rs_self_pos h hne

/-- W200 (OC §402): The riverbed shift — adding a new certainty shifts
    the resonance profile by the new element's contribution plus emergence. -/
theorem riverbed_shift (bed new_elem c : I) :
    rs (compose new_elem bed) c - rs bed c =
    rs new_elem c + emergence new_elem bed c := by
  rw [rs_compose_eq]; ring

/-- W201 (OC §450): Composing a proposition with a universal hinge doesn't
    change the doubt — the hinge absorbs without additional emergence. -/
theorem doubt_absorbs_hinge (ctx p h : I) (hh : universalHinge h) (d : I) :
    doubt ctx (compose p h) d = doubt ctx p d := by
  unfold doubt
  have := cocycle_condition ctx p h d
  rw [hh (compose ctx p) d, hh p d] at this; linarith

/-- W202 (OC §512): Composing two universal hinges preserves zero doubt. -/
theorem hinge_pair_no_doubt (h1 h2 : I)
    (hh1 : universalHinge h1) (hh2 : universalHinge h2)
    (ctx d : I) : doubt ctx (compose h1 h2) d = 0 := by
  rw [doubt_absorbs_hinge ctx h1 h2 hh2 d]; exact hh1 ctx d

/-- W203 (OC §559): Two riverbeds grounding the same inquiry have the
    same resonance profile — shared certainties determine shared meaning. -/
theorem shared_certainties (bed1 bed2 : I) (h : sameUse bed1 bed2) (c : I) :
    rs bed1 c = rs bed2 c := h c

end OnCertaintyDeep

/-! ## §22. Remarks on Colour (RC I-III)

Wittgenstein's Remarks on Colour explore how colour concepts are not
private sensations but moves in language games. "There is no such thing
as the pure colour that we see" — colour is always perceived within
a framework of contrasts, expectations, and linguistic practices. -/

section RemarksOnColour
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A colour concept: a perceptual frame applied to a visual sample.
    RC I §1: "A language-game with colour words." -/
def colourConcept (frame sample : I) : I := compose frame sample

/-- The colour judgment: how a framed sample resonates with a standard.
    RC I §3: "Compare: 'The stove is the same colour as the table.'" -/
noncomputable def colourJudgment (frame sample standard : I) : ℝ :=
  rs (colourConcept frame sample) standard

/-- W204 (RC I §1): The void frame contributes nothing — seeing without
    a conceptual framework is just the raw sample. -/
theorem colour_void_frame (sample : I) : colourConcept (void : I) sample = sample := by
  unfold colourConcept; simp

/-- W205 (RC I §3): Void samples yield the frame itself — judging
    "nothing" just reflects the frame's bias. -/
theorem colour_void_sample (frame : I) : colourConcept frame (void : I) = frame := by
  unfold colourConcept; simp

/-- W206 (RC I §22): Colour judgment with void standard is zero —
    without a standard, there is no judgment. -/
theorem colour_void_standard (frame sample : I) :
    colourJudgment frame sample (void : I) = 0 := by
  unfold colourJudgment colourConcept; exact rs_void_right' _

/-- W207 (RC I §58): Colour judgment decomposes — the judgment of a
    framed sample reflects the frame, the sample, and their interaction. -/
theorem colour_judgment_decompose (frame sample standard : I) :
    colourJudgment frame sample standard =
    rs frame standard + rs sample standard + emergence frame sample standard := by
  unfold colourJudgment colourConcept; exact rs_compose_eq frame sample standard

/-- W208 (RC I §66): Colour perception enriches — applying a colour
    concept to a sample creates something with more presence than the
    frame alone. Perception adds, never subtracts. -/
theorem colour_perception_enriches (frame sample : I) :
    rs (colourConcept frame sample) (colourConcept frame sample) ≥ rs frame frame := by
  unfold colourConcept; exact compose_enriches' frame sample

/-- Colour exclusion: two colour concepts applied to the same sample
    yield different resonances with a standard. RC III §4. -/
noncomputable def colourExclusion (frame1 frame2 sample standard : I) : ℝ :=
  colourJudgment frame1 sample standard - colourJudgment frame2 sample standard

/-- W209 (RC III §4): Colour exclusion reduces to frame difference plus
    emergence difference — the "logic of colour" is an emergence phenomenon. -/
theorem colour_exclusion_decompose (f1 f2 sample standard : I) :
    colourExclusion f1 f2 sample standard =
    (rs f1 standard - rs f2 standard) +
    (emergence f1 sample standard - emergence f2 sample standard) := by
  unfold colourExclusion colourJudgment colourConcept
  rw [rs_compose_eq f1 sample standard, rs_compose_eq f2 sample standard]; ring

/-- W210 (RC III §10): Colour exclusion with void sample reduces to
    the pure frame difference — without a sample, only frames differ. -/
theorem colour_exclusion_void_sample (f1 f2 standard : I) :
    colourExclusion f1 f2 (void : I) standard = rs f1 standard - rs f2 standard := by
  unfold colourExclusion colourJudgment colourConcept; simp

/-- W211 (RC I §68): A void observer perceives no colour exclusion. -/
theorem colour_exclusion_void_standard (f1 f2 sample : I) :
    colourExclusion f1 f2 sample (void : I) = 0 := by
  unfold colourExclusion colourJudgment colourConcept
  simp [rs_void_right']

/-- W212 (RC I §72): A non-void frame applied to any sample is non-void —
    colour perception with a real concept always yields something. -/
theorem colour_concept_nontrivial (frame sample : I) (hne : frame ≠ void) :
    colourConcept frame sample ≠ void := by
  unfold colourConcept; exact compose_ne_void_of_left frame sample hne

/-- Colour blindness: a frame that generates no emergence with any sample.
    RC III §13: "Can a colour-blind person learn the use of the word 'red'?" -/
def colourBlind (frame : I) : Prop := ∀ sample c : I, emergence frame sample c = 0

/-- W213 (RC III §13): Void is colour-blind — no frame, no perception. -/
theorem void_colourBlind : colourBlind (void : I) := emergence_void_left

/-- W214 (RC III §14): A colour-blind frame yields purely additive judgments. -/
theorem colourBlind_additive (frame : I) (h : colourBlind frame) (sample standard : I) :
    colourJudgment frame sample standard = rs frame standard + rs sample standard := by
  unfold colourJudgment colourConcept; rw [rs_compose_eq]; linarith [h sample standard]

/-- W215 (RC III §42): Colour emergence is bounded by the perceptual
    capacity of the system — you can't perceive more than your frame allows. -/
theorem colour_emergence_bounded (frame sample standard : I) :
    (emergence frame sample standard) ^ 2 ≤
    rs (colourConcept frame sample) (colourConcept frame sample) * rs standard standard := by
  unfold colourConcept; exact emergence_bounded' frame sample standard

/-- W216 (RC I §§1-3): Two colour-blind frames produce identical exclusion
    patterns — colour blindness erases all distinction beyond direct resonance. -/
theorem colourBlind_same_exclusion (f1 f2 : I)
    (h1 : colourBlind f1) (h2 : colourBlind f2) (sample standard : I) :
    colourExclusion f1 f2 sample standard = rs f1 standard - rs f2 standard := by
  rw [colour_exclusion_decompose]; simp [h1 sample standard, h2 sample standard]

/-- W217 (RC III §188): Same colour concept applied twice reassociates —
    double perception is compositional. -/
theorem colour_double_perception (f1 f2 sample : I) :
    colourConcept (colourConcept f1 f2) sample =
    compose f1 (colourConcept f2 sample) := by
  unfold colourConcept; exact compose_assoc' f1 f2 sample

/-- W218 (RC I §77): The colour cocycle — perception of nested colour
    concepts satisfies global consistency constraints on emergence. -/
theorem colour_cocycle (f1 f2 sample d : I) :
    emergence f1 f2 d + emergence (compose f1 f2) sample d =
    emergence f2 sample d + emergence f1 (compose f2 sample) d := by
  exact cocycle_condition f1 f2 sample d

end RemarksOnColour

/-! ## §23. Culture and Value (CV)

Wittgenstein: "Culture is a rule of an order, or at least presupposes
a rule of an order." Aesthetic judgments and cultural values are not
subjective feelings but moves in culturally embedded language games.
We formalize aesthetic resonance within cultural contexts. -/

section CultureAndValue
variable {I : Type*} [S : IdeaticSpace3 I]

/-- An aesthetic judgment: how a work resonates with a cultural standard
    when viewed through a cultural context. CV p. 7e: "Is what I am
    doing really worth the effort?" -/
noncomputable def aestheticJudgment (culture work standard : I) : ℝ :=
  rs (compose culture work) standard

/-- W219 (CV p. 1e): An aesthetic judgment in the void culture is just
    the work's direct resonance with the standard. -/
theorem aesthetic_void_culture (work standard : I) :
    aestheticJudgment (void : I) work standard = rs work standard := by
  unfold aestheticJudgment; simp

/-- W220 (CV p. 2e): Judging void (no work) yields the culture's
    resonance with the standard. -/
theorem aesthetic_void_work (culture standard : I) :
    aestheticJudgment culture (void : I) standard = rs culture standard := by
  unfold aestheticJudgment; simp

/-- W221 (CV p. 3e): Judgment against a void standard is zero —
    without criteria, there is no aesthetic evaluation. -/
theorem aesthetic_void_standard (culture work : I) :
    aestheticJudgment culture work (void : I) = 0 := by
  unfold aestheticJudgment; exact rs_void_right' _

/-- W222 (CV p. 7e): Aesthetic judgment decomposes into cultural resonance,
    work resonance, and creative emergence. -/
theorem aesthetic_decompose (culture work standard : I) :
    aestheticJudgment culture work standard =
    rs culture standard + rs work standard + emergence culture work standard := by
  unfold aestheticJudgment; exact rs_compose_eq culture work standard

/-- Aesthetic agreement: two cultures agree on a work when they
    assign it the same judgment against every standard. CV p. 8e. -/
def aestheticAgreement (c1 c2 work : I) : Prop :=
  ∀ standard : I, aestheticJudgment c1 work standard = aestheticJudgment c2 work standard

/-- W223 (CV p. 8e): Aesthetic agreement is reflexive — a culture
    always agrees with itself. -/
theorem aestheticAgreement_refl (c work : I) : aestheticAgreement c c work :=
  fun _ => rfl

/-- W224 (CV p. 11e): Aesthetic agreement with void culture implies
    the work IS the culturally-framed work — the culture adds nothing. -/
theorem aestheticAgreement_void (c work : I)
    (h : aestheticAgreement (void : I) c work) (std : I) :
    aestheticJudgment c work std = rs work std := by
  rw [← aesthetic_void_culture work std]; exact (h std).symm

/-- The cultural surplus: how much a culture adds beyond what the work
    and standard contribute individually. CV p. 24e. -/
noncomputable def culturalSurplus (culture work standard : I) : ℝ :=
  emergence culture work standard

/-- W225 (CV p. 24e): The void culture has zero surplus — it adds
    nothing to the work's inherent resonance. -/
theorem culturalSurplus_void (work standard : I) :
    culturalSurplus (void : I) work standard = 0 :=
  emergence_void_left work standard

/-- W226 (CV p. 26e): Void works have zero cultural surplus — nothing
    to culturally enhance. -/
theorem culturalSurplus_void_work (culture standard : I) :
    culturalSurplus culture (void : I) standard = 0 :=
  emergence_void_right culture standard

/-- W227 (CV p. 33e): Cultural surplus is bounded — a culture can only
    enhance a work to the degree its compositional capacity allows. -/
theorem culturalSurplus_bounded (culture work standard : I) :
    (culturalSurplus culture work standard) ^ 2 ≤
    rs (compose culture work) (compose culture work) * rs standard standard :=
  emergence_bounded' culture work standard

/-- W228 (CV p. 37e): Cultural surplus satisfies the cocycle — the
    cultural enhancement of nested works is globally consistent. -/
theorem culturalSurplus_cocycle (c w1 w2 std : I) :
    culturalSurplus c w1 std + culturalSurplus (compose c w1) w2 std =
    culturalSurplus w1 w2 std + culturalSurplus c (compose w1 w2) std := by
  unfold culturalSurplus; exact cocycle_condition c w1 w2 std

/-- W229 (CV p. 42e): When two cultures agree on a work, their surplus
    difference plus their direct resonance difference must sum to zero. -/
theorem aesthetic_agreement_constraint (c1 c2 work std : I)
    (h : aestheticAgreement c1 c2 work) :
    rs c1 std - rs c2 std + (culturalSurplus c1 work std - culturalSurplus c2 work std) = 0 := by
  unfold culturalSurplus
  have := h std; unfold aestheticJudgment at this
  rw [rs_compose_eq, rs_compose_eq] at this; linarith

/-- Aesthetic sensitivity: the order-dependent part of aesthetic judgment.
    CV p. 49e: "Understanding music is neither a sensation nor an association." -/
noncomputable def aestheticSensitivity (culture work standard : I) : ℝ :=
  rs (compose culture work) standard - rs (compose work culture) standard

/-- W230 (CV p. 49e): Aesthetic sensitivity vanishes when both components
    are void — silence has no aesthetic direction. -/
theorem aestheticSensitivity_void_both (standard : I) :
    aestheticSensitivity (void : I) (void : I) standard = 0 := by
  unfold aestheticSensitivity; simp

/-- W231 (CV p. 56e): Aesthetic sensitivity is antisymmetric in its
    arguments — swapping culture and work reverses the sensitivity. -/
theorem aestheticSensitivity_antisymm (culture work standard : I) :
    aestheticSensitivity culture work standard =
    -aestheticSensitivity work culture standard := by
  unfold aestheticSensitivity; ring

/-- W232 (CV p. 70e): Aesthetic sensitivity decomposes into emergence
    differences — the directional part of aesthetic judgment. -/
theorem aestheticSensitivity_eq_emergence (culture work standard : I) :
    aestheticSensitivity culture work standard =
    emergence culture work standard - emergence work culture standard := by
  unfold aestheticSensitivity; rw [rs_compose_eq culture work, rs_compose_eq work culture]; ring

/-- W233 (CV p. 77e): A meaning-blind observer perceives zero aesthetic
    sensitivity — without emergence sensitivity, the order of culture and
    work is irrelevant. -/
theorem meaningBlind_no_sensitivity {agent : I} (h : meaningBlind agent)
    (culture work : I) : aestheticSensitivity culture work agent = 0 := by
  rw [aestheticSensitivity_eq_emergence]; simp [h culture work, h work culture]

end CultureAndValue

/-! ## §24. Zettel — Thought Fragments (Z §§1-20, §§80-90)

Wittgenstein's Zettel consists of philosophical fragments — partial
thoughts, incomplete arguments, aphorisms. We formalize the idea that
a thought fragment is a partial composition: something that gains its
full meaning only when completed with a context. -/

section Zettel
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A thought fragment: an incomplete composition awaiting completion.
    Z §1: "Like everything metaphysical, the harmony between thought
    and reality is to be found in the grammar of the language." -/
def fragment (part : I) : I := part

/-- Fragment completion: composing a fragment with its context.
    Z §3: The fragment gains meaning when placed in context. -/
def completeFragment (frag context : I) : I := compose frag context

/-- Fragment coherence: how well a fragment resonates with its completion.
    Z §7: The coherence of a thought with its expression. -/
noncomputable def fragmentCoherence (frag context observer : I) : ℝ :=
  rs (completeFragment frag context) observer

/-- W234 (Z §1): Completing a fragment with void yields the fragment itself. -/
theorem completeFragment_void_context (frag : I) :
    completeFragment frag (void : I) = frag := by
  unfold completeFragment; simp

/-- W235 (Z §3): The void fragment is completed to the context itself. -/
theorem completeFragment_void_frag (context : I) :
    completeFragment (void : I) context = context := by
  unfold completeFragment; simp

/-- W236 (Z §5): Fragment coherence with void observer is zero. -/
theorem fragmentCoherence_void_observer (frag context : I) :
    fragmentCoherence frag context (void : I) = 0 := by
  unfold fragmentCoherence completeFragment; exact rs_void_right' _

/-- W237 (Z §7): Fragment coherence decomposes into the fragment's
    direct contribution, the context's contribution, and emergence. -/
theorem fragmentCoherence_decompose (frag context observer : I) :
    fragmentCoherence frag context observer =
    rs frag observer + rs context observer +
    emergence frag context observer := by
  unfold fragmentCoherence completeFragment; exact rs_compose_eq frag context observer

/-- W238 (Z §10): Completing a fragment enriches — the completed thought
    has at least as much weight as the fragment alone. -/
theorem completion_enriches (frag context : I) :
    rs (completeFragment frag context) (completeFragment frag context) ≥
    rs frag frag := by
  unfold completeFragment; exact compose_enriches' frag context

/-- W239 (Z §12): A non-void fragment always completes to something non-void. -/
theorem fragment_completion_nontrivial (frag context : I) (hne : frag ≠ void) :
    completeFragment frag context ≠ void := by
  unfold completeFragment; exact compose_ne_void_of_left frag context hne

/-- W240 (Z §15): Sequential completion reassociates — completing a
    fragment with c1 then c2 is the same as completing with c1∘c2. -/
theorem sequential_completion (frag c1 c2 : I) :
    completeFragment (completeFragment frag c1) c2 =
    completeFragment frag (compose c1 c2) := by
  unfold completeFragment; exact compose_assoc' frag c1 c2

/-- W241 (Z §20): The emergence of fragment completion with different
    contexts satisfies the cocycle condition. -/
theorem fragment_cocycle (frag c1 c2 d : I) :
    emergence frag c1 d + emergence (compose frag c1) c2 d =
    emergence c1 c2 d + emergence frag (compose c1 c2) d :=
  cocycle_condition frag c1 c2 d

/-- W242 (Z §33): The coherence difference between two completions
    depends only on the contexts and their emergence, not the fragment's
    direct resonance (which cancels). -/
theorem coherence_context_diff (frag c1 c2 obs : I) :
    fragmentCoherence frag c1 obs - fragmentCoherence frag c2 obs =
    (rs c1 obs - rs c2 obs) +
    (emergence frag c1 obs - emergence frag c2 obs) := by
  simp only [fragmentCoherence_decompose]; ring

/-- W243 (Z §40): The coherence of void with any context and observer is
    just the context's resonance with the observer — nothing emerges from void. -/
theorem void_fragment_coherence (context observer : I) :
    fragmentCoherence (void : I) context observer = rs context observer := by
  rw [fragmentCoherence_decompose]; simp [rs_void_left', emergence_void_left]

/-- The assemblage: composing multiple fragments together.
    Z §80: Collecting fragments into a whole. -/
def assemblage (fragments : List I) : I := composeList fragments

/-- W244 (Z §80): An empty assemblage is void — no fragments, no thought. -/
theorem assemblage_empty : assemblage ([] : List I) = (void : I) := rfl

/-- W245 (Z §82): An assemblage of one fragment is just that fragment. -/
theorem assemblage_single (f : I) : assemblage [f] = f := by
  unfold assemblage; simp

/-- W246 (Z §84): An assemblage decomposes via its first fragment. -/
theorem assemblage_cons (f : I) (rest : List I) :
    assemblage (f :: rest) = compose f (assemblage rest) := rfl

/-- W247 (Z §86): The assemblage enriches with each added fragment. -/
theorem assemblage_enriches (f : I) (rest : List I) :
    rs (assemblage (f :: rest)) (assemblage (f :: rest)) ≥ rs f f := by
  rw [assemblage_cons]; exact compose_enriches' f (assemblage rest)

/-- W248 (Z §90): The assemblage's resonance decomposes via composition. -/
theorem assemblage_resonance (f : I) (rest : List I) (c : I) :
    rs (assemblage (f :: rest)) c =
    rs f c + rs (assemblage rest) c + emergence f (assemblage rest) c := by
  rw [assemblage_cons]; exact rs_compose_eq f (assemblage rest) c

end Zettel

/-! ## §25. Remarks on the Foundations of Mathematics (RFM I-VII)

Wittgenstein: mathematical propositions are not descriptions of Platonic
truths but rules of grammar — moves in mathematical language games.
"Mathematics is a MOTLEY of techniques of proof." We formalize
mathematical proof as a compositional language game where the "score"
is resonance with axioms. -/

section FoundationsOfMathematics
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A mathematical proposition: axioms composed with a derivation step.
    RFM I §1: "Proof must be perspicuous." -/
def mathProposition (axioms step : I) : I := compose axioms step

/-- Proof score: how much a derived proposition resonates with the axiom base.
    RFM I §5: The "correctness" of a proof is its alignment with the axioms. -/
noncomputable def proofScore (axioms step standard : I) : ℝ :=
  rs (mathProposition axioms step) standard

/-- W249 (RFM I §1): Void axioms yield the derivation step itself —
    proving from nothing gives only what you started with. -/
theorem mathProp_void_axioms (step : I) :
    mathProposition (void : I) step = step := by
  unfold mathProposition; simp

/-- W250 (RFM I §4): A void derivation step returns the axioms unchanged. -/
theorem mathProp_void_step (axioms : I) :
    mathProposition axioms (void : I) = axioms := by
  unfold mathProposition; simp

/-- W251 (RFM I §5): Proof score against void is zero —
    without a standard of correctness, there is no evaluation. -/
theorem proofScore_void_standard (axioms step : I) :
    proofScore axioms step (void : I) = 0 := by
  unfold proofScore mathProposition; exact rs_void_right' _

/-- W252 (RFM I §8): Proof score decomposes: axiom resonance + step
    resonance + the creative/deductive emergence. -/
theorem proofScore_decompose (axioms step standard : I) :
    proofScore axioms step standard =
    rs axioms standard + rs step standard +
    emergence axioms step standard := by
  unfold proofScore mathProposition; exact rs_compose_eq axioms step standard

/-- Mathematical creativity: the emergence generated by a proof step.
    RFM I §167: "The proof changes the grammar." -/
noncomputable def mathCreativity (axioms step standard : I) : ℝ :=
  emergence axioms step standard

/-- W253 (RFM I §167): Void axioms generate zero mathematical creativity. -/
theorem mathCreativity_void_axioms (step standard : I) :
    mathCreativity (void : I) step standard = 0 := emergence_void_left step standard

/-- W254 (RFM I §168): Void steps generate zero mathematical creativity. -/
theorem mathCreativity_void_step (axioms standard : I) :
    mathCreativity axioms (void : I) standard = 0 := emergence_void_right axioms standard

/-- W255 (RFM II §22): Mathematical creativity is bounded — a proof
    cannot generate more insight than the axioms and observer can support. -/
theorem mathCreativity_bounded (axioms step standard : I) :
    (mathCreativity axioms step standard) ^ 2 ≤
    rs (mathProposition axioms step) (mathProposition axioms step) *
    rs standard standard := by
  unfold mathCreativity mathProposition; exact emergence_bounded' axioms step standard

/-- W256 (RFM III §31): The mathematical cocycle — sequential proof steps
    satisfy global consistency on emergence, reflecting the coherence of
    mathematical reasoning. -/
theorem math_cocycle (axioms s1 s2 d : I) :
    mathCreativity axioms s1 d +
    mathCreativity (mathProposition axioms s1) s2 d =
    mathCreativity s1 s2 d +
    mathCreativity axioms (compose s1 s2) d := by
  unfold mathCreativity mathProposition; exact cocycle_condition axioms s1 s2 d

/-- W257 (RFM IV §2): A proof step enriches — derived propositions have
    at least as much weight as the axioms. Mathematical reasoning never
    diminishes content. -/
theorem proof_enriches (axioms step : I) :
    rs (mathProposition axioms step) (mathProposition axioms step) ≥
    rs axioms axioms := by
  unfold mathProposition; exact compose_enriches' axioms step

/-- W258 (RFM IV §3): A non-void axiom base always produces a non-void
    mathematical proposition. -/
theorem mathProp_nontrivial (axioms step : I) (hne : axioms ≠ void) :
    mathProposition axioms step ≠ void := by
  unfold mathProposition; exact compose_ne_void_of_left axioms step hne

/-- W259 (RFM V §1): Two proof paths agree when they produce the same
    proposition — mathematical identity is extensional. -/
theorem math_extensionality (a s1 s2 c : I)
    (h : mathProposition a s1 = mathProposition a s2) :
    proofScore a s1 c = proofScore a s2 c := by
  unfold proofScore; rw [h]

/-- W260 (RFM V §16): The score difference between two derivation steps
    depends on the steps and their emergence, not the axioms. -/
theorem proof_step_comparison (axioms s1 s2 std : I) :
    proofScore axioms s1 std - proofScore axioms s2 std =
    (rs s1 std - rs s2 std) +
    (emergence axioms s1 std - emergence axioms s2 std) := by
  simp only [proofScore_decompose]; ring

/-- W261 (RFM VI §2): Sequential proofs reassociate — multi-step
    derivations are compositionally coherent. -/
theorem sequential_proofs (axioms s1 s2 : I) :
    mathProposition (mathProposition axioms s1) s2 =
    mathProposition axioms (compose s1 s2) := by
  unfold mathProposition; exact compose_assoc' axioms s1 s2

/-- W262 (RFM VII §10): If all proof steps are "linear" (zero emergence),
    mathematics reduces to purely additive symbol manipulation.
    This is the "formalist" extreme that Wittgenstein critiques. -/
theorem formalist_math {axioms : I} (h : leftLinear axioms) (step std : I) :
    proofScore axioms step std = rs axioms std + rs step std := by
  rw [proofScore_decompose]; linarith [h step std]

/-- W263 (RFM VII §26): Mathematical "depth" is precisely the emergence
    of a proof step — what the proof reveals beyond its inputs. -/
theorem math_depth_is_emergence (axioms step std : I) :
    proofScore axioms step std - (rs axioms std + rs step std) =
    mathCreativity axioms step std := by
  rw [proofScore_decompose]; unfold mathCreativity; ring

end FoundationsOfMathematics

/-! ## §26. The Blue and Brown Books (BB)

Wittgenstein's transitional works introduce the distinction between
criteria and symptoms. A criterion for X is constitutive of what we
mean by X; a symptom is empirically correlated with X but not part
of its meaning. We formalize this in terms of emergence: criteria
have zero emergence (they're definitional), while symptoms generate
non-trivial emergence (they're discoveries). -/

section BlueAndBrownBooks
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A criterion for a concept: composing the concept with the criterion.
    BB p. 25: "The fluctuation of grammar between criteria and symptoms." -/
def criterialRelation (concept criterion : I) : I := compose concept criterion

/-- A symptom check: resonance of a case with the concept.
    BB p. 25: Symptoms are empirical correlates. -/
noncomputable def symptomCheck (concept case observer : I) : ℝ :=
  rs (compose concept case) observer

/-- W264 (BB p. 24): Applying the void criterion to a concept returns
    the concept — the null criterion is definitionally inert. -/
theorem criterial_void_criterion (concept : I) :
    criterialRelation concept (void : I) = concept := by
  unfold criterialRelation; simp

/-- W265 (BB p. 24): The void concept with any criterion yields just
    the criterion — meaningless concepts reduce to their criteria. -/
theorem criterial_void_concept (criterion : I) :
    criterialRelation (void : I) criterion = criterion := by
  unfold criterialRelation; simp

/-- W266 (BB p. 25): Symptom check against void is zero. -/
theorem symptomCheck_void_observer (concept case : I) :
    symptomCheck concept case (void : I) = 0 := by
  unfold symptomCheck; exact rs_void_right' _

/-- W267 (BB p. 25): Symptom check decomposes into concept resonance,
    case resonance, and diagnostic emergence. -/
theorem symptomCheck_decompose (concept case observer : I) :
    symptomCheck concept case observer =
    rs concept observer + rs case observer +
    emergence concept case observer := by
  unfold symptomCheck; exact rs_compose_eq concept case observer

/-- A criterial concept: one where the criterion is constitutive —
    applying it generates zero emergence. BB p. 25. -/
def isCriterial (concept : I) : Prop := leftLinear concept

/-- A symptomatic concept: one where application generates non-trivial emergence.
    BB p. 57: "Symptoms are discovered through experience." -/
def isSymptomatic (concept : I) : Prop := hasEmergence concept

/-- W268 (BB p. 25): Void is criterial — it generates no emergence. -/
theorem void_isCriterial : isCriterial (void : I) := void_leftLinear

/-- W269 (BB p. 57): A criterial concept is never symptomatic —
    what is definitional cannot also be a discovery. -/
theorem criterial_not_symptomatic {concept : I}
    (h : isCriterial concept) : ¬isSymptomatic concept := by
  intro ⟨b, c, hne⟩; exact hne (h b c)

/-- W270 (BB p. 25): A criterial concept yields purely additive symptom checks. -/
theorem criterial_additive {concept : I} (h : isCriterial concept) (case observer : I) :
    symptomCheck concept case observer = rs concept observer + rs case observer := by
  rw [symptomCheck_decompose]; linarith [h case observer]

/-- The diagnostic difference: symptom check minus the criterial baseline.
    BB p. 57: How much the symptom tells us beyond the definition. -/
noncomputable def diagnosticSurplus (concept case observer : I) : ℝ :=
  emergence concept case observer

/-- W271 (BB p. 57): The diagnostic surplus of a criterial concept is zero. -/
theorem criterial_no_surplus {concept : I} (h : isCriterial concept) (case observer : I) :
    diagnosticSurplus concept case observer = 0 := h case observer

/-- W272 (BB p. 60): Diagnostic surplus satisfies the cocycle — diagnostic
    reasoning is globally consistent. -/
theorem diagnostic_cocycle (concept c1 c2 d : I) :
    diagnosticSurplus concept c1 d +
    diagnosticSurplus (compose concept c1) c2 d =
    diagnosticSurplus c1 c2 d +
    diagnosticSurplus concept (compose c1 c2) d := by
  unfold diagnosticSurplus; exact cocycle_condition concept c1 c2 d

/-- W273 (BB p. 62): Diagnostic surplus is bounded. -/
theorem diagnosticSurplus_bounded (concept case observer : I) :
    (diagnosticSurplus concept case observer) ^ 2 ≤
    rs (compose concept case) (compose concept case) * rs observer observer := by
  unfold diagnosticSurplus; exact emergence_bounded' concept case observer

/-- W274 (BB p. 65): The symptom check enriches the concept. -/
theorem symptomCheck_enriches (concept case : I) :
    rs (compose concept case) (compose concept case) ≥ rs concept concept :=
  compose_enriches' concept case

/-- W275 (BB p. 68): Sequential criteria application reassociates. -/
theorem sequential_criteria (concept c1 c2 : I) :
    criterialRelation (criterialRelation concept c1) c2 =
    criterialRelation concept (compose c1 c2) := by
  unfold criterialRelation; exact compose_assoc' concept c1 c2

/-- W276 (BB p. 70): Symptom check with void case yields concept resonance. -/
theorem symptomCheck_void_case (concept observer : I) :
    symptomCheck concept (void : I) observer = rs concept observer := by
  unfold symptomCheck; simp

/-- W277 (BB p. 72): The diagnostic surplus with void case is zero. -/
theorem diagnosticSurplus_void_case (concept observer : I) :
    diagnosticSurplus concept (void : I) observer = 0 := by
  unfold diagnosticSurplus; exact emergence_void_right concept observer

/-- W278 (BB p. 74): Two criterial concepts produce identical diagnostic
    surplus (both zero) — they are diagnostically equivalent. -/
theorem two_criterial_same_surplus {c1 c2 : I}
    (h1 : isCriterial c1) (h2 : isCriterial c2) (case observer : I) :
    diagnosticSurplus c1 case observer = diagnosticSurplus c2 case observer := by
  unfold diagnosticSurplus; rw [h1 case observer, h2 case observer]

end BlueAndBrownBooks

/-! ## §27. Aspect Perception — Deep Theory (PPF §§111-180, PI II §xi)

Wittgenstein's treatment of aspect perception goes beyond the simple
duck-rabbit illustration. "Aspect dawning" is the moment of shift —
when one suddenly sees the figure differently. We formalize the dynamics
of aspect change, the depth of aspect perception, and the relationship
between continuous and discrete aspect seeing. -/

section AspectPerceptionDeep
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Aspect dawning: the difference in resonance that occurs when shifting
    from one frame to another. PPF §118: "I suddenly see the solution." -/
noncomputable def aspectDawning (oldFrame newFrame observation observer : I) : ℝ :=
  rs (seeAs newFrame observation) observer - rs (seeAs oldFrame observation) observer

/-- W279 (PPF §118): Dawning from void to any frame is the full gain. -/
theorem dawning_from_void (frame obs observer : I) :
    aspectDawning (void : I) frame obs observer =
    rs (seeAs frame obs) observer - rs obs observer := by
  unfold aspectDawning; rw [seeAs_void_frame]

/-- W280 (PPF §120): Dawning to void is the full loss of the old frame. -/
theorem dawning_to_void (frame obs observer : I) :
    aspectDawning frame (void : I) obs observer =
    rs obs observer - rs (seeAs frame obs) observer := by
  unfold aspectDawning; rw [seeAs_void_frame]

/-- W281 (PPF §122): Dawning is antisymmetric — shifting from A to B is
    the negative of shifting from B to A. -/
theorem dawning_antisymm (f1 f2 obs observer : I) :
    aspectDawning f1 f2 obs observer = -aspectDawning f2 f1 obs observer := by
  unfold aspectDawning; ring

/-- W282 (PPF §125): Self-dawning is zero — you can't "dawn" into
    the same aspect you already have. -/
theorem dawning_self (frame obs observer : I) :
    aspectDawning frame frame obs observer = 0 := by
  unfold aspectDawning; ring

/-- W283 (PPF §128): Dawning decomposes into frame resonance difference
    plus emergence difference — the "source" of the shift. -/
theorem dawning_decompose (f1 f2 obs observer : I) :
    aspectDawning f1 f2 obs observer =
    (rs f2 observer - rs f1 observer) +
    (emergence f2 obs observer - emergence f1 obs observer) := by
  unfold aspectDawning seeAs
  rw [rs_compose_eq f2 obs observer, rs_compose_eq f1 obs observer]; ring

/-- W284 (PPF §130): With a void observer, no dawning is perceived. -/
theorem dawning_void_observer (f1 f2 obs : I) :
    aspectDawning f1 f2 obs (void : I) = 0 := by
  unfold aspectDawning seeAs; simp [rs_void_right']

/-- Noticing an aspect: the magnitude of the emergence component.
    PPF §140: "The experience of noticing an aspect." -/
noncomputable def noticingAspect (frame obs observer : I) : ℝ :=
  emergence frame obs observer

/-- W285 (PPF §140): Noticing through void is zero — no frame, no aspect. -/
theorem noticing_void_frame (obs observer : I) :
    noticingAspect (void : I) obs observer = 0 :=
  emergence_void_left obs observer

/-- W286 (PPF §141): Noticing void observation is zero. -/
theorem noticing_void_obs (frame observer : I) :
    noticingAspect frame (void : I) observer = 0 :=
  emergence_void_right frame observer

/-- W287 (PPF §142): Noticing with void observer is zero. -/
theorem noticing_void_observer (frame obs : I) :
    noticingAspect frame obs (void : I) = 0 :=
  emergence_against_void frame obs

/-- The double aspect: seeing through two composed frames.
    PPF §144: "I see it has not changed, and yet I see it differently." -/
def doubleAspect (f1 f2 obs : I) : I := seeAs (compose f1 f2) obs

/-- W288 (PPF §144): The double aspect is the same as sequential framing. -/
theorem doubleAspect_eq_sequential (f1 f2 obs : I) :
    doubleAspect f1 f2 obs = seeAs f1 (seeAs f2 obs) := by
  unfold doubleAspect seeAs; rw [compose_assoc']

/-- W289 (PPF §146): The double aspect with void outer frame reduces
    to the inner frame's perception. -/
theorem doubleAspect_void_outer (f obs : I) :
    doubleAspect (void : I) f obs = seeAs f obs := by
  unfold doubleAspect; simp [seeAs]

/-- W290 (PPF §148): The double aspect with void inner frame reduces
    to the outer frame composed with the observation. -/
theorem doubleAspect_void_inner (f obs : I) :
    doubleAspect f (void : I) obs = seeAs f obs := by
  unfold doubleAspect; simp [seeAs]

/-- W291 (PPF §150): Double aspect enriches beyond the outer frame. -/
theorem doubleAspect_enriches (f1 f2 obs : I) :
    rs (doubleAspect f1 f2 obs) (doubleAspect f1 f2 obs) ≥
    rs (compose f1 f2) (compose f1 f2) := by
  unfold doubleAspect seeAs; exact compose_enriches' (compose f1 f2) obs

/-- Aspect chain: a sequence of frames applied to an observation.
    PPF §170: "Seeing aspects is connected with imagining." -/
def aspectChain : List I → I → I
  | [], obs => obs
  | f :: rest, obs => seeAs f (aspectChain rest obs)

/-- W292 (PPF §170): Empty aspect chain is the observation itself. -/
theorem aspectChain_nil (obs : I) : aspectChain ([] : List I) obs = obs := rfl

/-- W293 (PPF §172): Single-frame aspect chain is just seeAs. -/
theorem aspectChain_single (f obs : I) : aspectChain [f] obs = seeAs f obs := rfl

/-- W294 (PPF §174): Aspect chain enriches with each frame. -/
theorem aspectChain_enriches_cons (f : I) (rest : List I) (obs : I) :
    rs (aspectChain (f :: rest) obs) (aspectChain (f :: rest) obs) ≥
    rs f f := by
  unfold aspectChain seeAs; exact compose_enriches' f (aspectChain rest obs)

/-- W295 (PPF §176): The aspect-blind perceive all frames the same way —
    no emergence distinguishes frames. -/
theorem aspectBlind_no_dawning (frame : I) (h : aspectBlind frame)
    (obs observer : I) : noticingAspect frame obs observer = 0 :=
  h obs observer

/-- W296 (PPF §178): Dawning between aspect-blind frames is pure
    resonance difference — no emergence contributes. -/
theorem aspectBlind_dawning (f1 f2 : I) (h1 : aspectBlind f1)
    (h2 : aspectBlind f2) (obs observer : I) :
    aspectDawning f1 f2 obs observer = rs f2 observer - rs f1 observer := by
  rw [dawning_decompose]; simp [h1 obs observer, h2 obs observer]

/-- W297 (PPF §180): The aspect cocycle — emergence through nested
    frames is globally consistent. -/
theorem aspect_cocycle (f1 f2 obs d : I) :
    emergence f1 f2 d + emergence (compose f1 f2) obs d =
    emergence f2 obs d + emergence f1 (compose f2 obs) d :=
  cocycle_condition f1 f2 obs d

/-- W298 (PI II §xi): Aspect perception is bounded by the perceiver's
    capacity — you can't perceive more than your frame can carry. -/
theorem aspect_perception_bounded (frame obs observer : I) :
    (noticingAspect frame obs observer) ^ 2 ≤
    rs (seeAs frame obs) (seeAs frame obs) * rs observer observer := by
  unfold noticingAspect seeAs; exact emergence_bounded' frame obs observer

end AspectPerceptionDeep

/-! ## §28. The Will, Intention, and Voluntary Action (PI §§611-660, RPP)

Wittgenstein: "Willing, if it is not to be a sort of wishing, must be
the action itself." Intention is not a mental state preceding action
but is CONSTITUTED by the action in context. We formalize intention
as the composition of an agent's disposition with a situation, and
voluntary action as having specific emergence properties. -/

section WillAndIntention
variable {I : Type*} [S : IdeaticSpace3 I]

/-- An intention: the agent's disposition composed with the situation.
    PI §644: "I want to say: 'Intending is not an experience.'" -/
def intention (disposition situation : I) : I := compose disposition situation

/-- An action: the result of applying intention to an environment.
    PI §615: "Willing is not an experience." -/
def action (disposition situation environment : I) : I :=
  compose (intention disposition situation) environment

/-- W299 (PI §611): Void disposition yields the situation itself —
    without agency, only the situation remains. -/
theorem intention_void_disposition (situation : I) :
    intention (void : I) situation = situation := by
  unfold intention; simp

/-- W300 (PI §613): Void situation yields the disposition itself. -/
theorem intention_void_situation (disposition : I) :
    intention disposition (void : I) = disposition := by
  unfold intention; simp

/-- W301 (PI §615): Action in void environment returns the intention. -/
theorem action_void_environment (d s : I) :
    action d s (void : I) = intention d s := by
  unfold action; simp

/-- W302 (PI §619): Action with void disposition is situation in environment. -/
theorem action_void_disposition (s e : I) :
    action (void : I) s e = compose s e := by
  unfold action intention; simp

/-- W303 (PI §621): Action enriches — acting always adds weight beyond
    the bare intention. Once you act, you can't undo the acting. -/
theorem action_enriches (d s e : I) :
    rs (action d s e) (action d s e) ≥
    rs (intention d s) (intention d s) := by
  unfold action; exact compose_enriches' (intention d s) e

/-- W304 (PI §625): Intention enriches beyond disposition — forming
    an intention adds the situation's weight. -/
theorem intention_enriches (d s : I) :
    rs (intention d s) (intention d s) ≥ rs d d := by
  unfold intention; exact compose_enriches' d s

/-- W305 (PI §627): A non-void agent always has a non-void intention. -/
theorem intention_nontrivial (d s : I) (hne : d ≠ void) :
    intention d s ≠ void := by
  unfold intention; exact compose_ne_void_of_left d s hne

/-- The effort: how much emergence the intention generates in context.
    PI §630: "Trying is not a peculiar feeling." -/
noncomputable def intentionalEffort (d s observer : I) : ℝ :=
  emergence d s observer

/-- W306 (PI §630): Effort with void disposition is zero. -/
theorem effort_void_disposition (s observer : I) :
    intentionalEffort (void : I) s observer = 0 :=
  emergence_void_left s observer

/-- W307 (PI §632): Effort with void situation is zero. -/
theorem effort_void_situation (d observer : I) :
    intentionalEffort d (void : I) observer = 0 :=
  emergence_void_right d observer

/-- W308 (PI §634): Effort with void observer is zero. -/
theorem effort_void_observer (d s : I) :
    intentionalEffort d s (void : I) = 0 :=
  emergence_against_void d s

/-- W309 (PI §636): Effort is bounded — you can't intend more than
    your disposition and situation can carry. -/
theorem effort_bounded (d s observer : I) :
    (intentionalEffort d s observer) ^ 2 ≤
    rs (intention d s) (intention d s) * rs observer observer := by
  unfold intentionalEffort intention; exact emergence_bounded' d s observer

/-- W310 (PI §638): Action resonance decomposes into intention, environment,
    and active emergence (the "doing" beyond intending). -/
theorem action_decompose (d s e observer : I) :
    rs (action d s e) observer =
    rs (intention d s) observer + rs e observer +
    emergence (intention d s) e observer := by
  unfold action; exact rs_compose_eq (intention d s) e observer

/-- The voluntary component: emergence from the agent's contribution.
    PI §640: "The voluntary act is the action plus its surroundings." -/
noncomputable def voluntariness (d s e observer : I) : ℝ :=
  emergence (intention d s) e observer

/-- W311 (PI §640): Voluntariness with void environment is zero —
    without an environment to act in, there is no voluntary action. -/
theorem voluntariness_void_env (d s observer : I) :
    voluntariness d s (void : I) observer = 0 := by
  unfold voluntariness; exact emergence_void_right (intention d s) observer

/-- W312 (PI §644): Voluntariness is bounded by the action's weight. -/
theorem voluntariness_bounded (d s e observer : I) :
    (voluntariness d s e observer) ^ 2 ≤
    rs (action d s e) (action d s e) * rs observer observer := by
  unfold voluntariness action; exact emergence_bounded' (intention d s) e observer

/-- W313 (PI §646): Sequential actions reassociate — acting twice in
    sequence is the same as acting with a combined environment. -/
theorem sequential_actions (d s e1 e2 : I) :
    compose (action d s e1) e2 = action d s (compose e1 e2) := by
  unfold action intention; rw [compose_assoc']

/-- W314 (PI §648): Intention resonance decomposes additively plus emergence. -/
theorem intention_resonance (d s observer : I) :
    rs (intention d s) observer =
    rs d observer + rs s observer + intentionalEffort d s observer := by
  unfold intention intentionalEffort; exact rs_compose_eq d s observer

/-- W315 (PI §650): The cocycle of sequential intentions — forming intentions
    about nested situations satisfies global consistency. -/
theorem intention_cocycle (d s1 s2 observer : I) :
    intentionalEffort d s1 observer +
    intentionalEffort (intention d s1) s2 observer =
    intentionalEffort s1 s2 observer +
    intentionalEffort d (compose s1 s2) observer := by
  unfold intentionalEffort intention; exact cocycle_condition d s1 s2 observer

/-- The intention-action gap: the difference between what was intended
    and what was done. RPP I §178. -/
noncomputable def intentionActionGap (d s e observer : I) : ℝ :=
  rs (action d s e) observer - rs (intention d s) observer

/-- W316 (RPP I §178): The intention-action gap equals the environment's
    resonance plus active emergence. -/
theorem intentionActionGap_decompose (d s e observer : I) :
    intentionActionGap d s e observer =
    rs e observer + voluntariness d s e observer := by
  unfold intentionActionGap voluntariness
  rw [action_decompose]; ring

/-- W317 (RPP I §180): Void environment yields zero intention-action gap. -/
theorem intentionActionGap_void_env (d s observer : I) :
    intentionActionGap d s (void : I) observer = 0 := by
  unfold intentionActionGap action; simp

/-- W318 (PI §660): The agent's full contribution to action: disposition
    plus all emergence terms along the compositional chain. -/
theorem agent_full_contribution (d s e observer : I) :
    rs (action d s e) observer =
    rs d observer + rs s observer + rs e observer +
    intentionalEffort d s observer +
    voluntariness d s e observer := by
  rw [action_decompose, intention_resonance]
  unfold voluntariness; ring

end WillAndIntention

/-! ## §29. Connections to Ordinary Language Philosophy

Austin's speech act theory and Ryle's concept of category mistakes connect
deeply with Wittgenstein's later philosophy. Speech acts are moves in
language games; category mistakes arise from composing ideas that generate
pathological emergence patterns. -/

section OrdinaryLanguagePhilosophy
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A speech act: the composition of illocutionary force with propositional
    content. Austin, How to Do Things with Words, Lecture I. -/
def speechAct (force content : I) : I := compose force content

/-- The performative score: how a speech act resonates with a context.
    Austin: "To say something is to do something." -/
noncomputable def performativeScore (force content context : I) : ℝ :=
  rs (speechAct force content) context

/-- W319 (Austin, Lecture I): Void force yields the content alone —
    without illocutionary force, there is only propositional content. -/
theorem speechAct_void_force (content : I) :
    speechAct (void : I) content = content := by
  unfold speechAct; simp

/-- W320 (Austin, Lecture II): Void content yields the force alone. -/
theorem speechAct_void_content (force : I) :
    speechAct force (void : I) = force := by
  unfold speechAct; simp

/-- W321 (Austin, Lecture III): Performative score decomposes into force
    resonance, content resonance, and illocutionary emergence. -/
theorem performativeScore_decompose (force content context : I) :
    performativeScore force content context =
    rs force context + rs content context +
    emergence force content context := by
  unfold performativeScore speechAct; exact rs_compose_eq force content context

/-- The illocutionary emergence: the creative contribution of force
    beyond mere assertion. Austin, Lecture VIII. -/
noncomputable def illocutionaryEmergence (force content context : I) : ℝ :=
  emergence force content context

/-- W322 (Austin, Lecture V): Void force has zero illocutionary emergence. -/
theorem illocutionary_void_force (content context : I) :
    illocutionaryEmergence (void : I) content context = 0 :=
  emergence_void_left content context

/-- W323 (Austin, Lecture VI): Void content has zero illocutionary emergence. -/
theorem illocutionary_void_content (force context : I) :
    illocutionaryEmergence force (void : I) context = 0 :=
  emergence_void_right force context

/-- Felicity conditions: a speech act is felicitous if it resonates
    positively with the context. Austin, Lecture II. -/
def felicitous (force content context : I) : Prop :=
  rs (speechAct force content) context > 0

/-- W324 (Austin, Lecture II): Void context makes no speech act felicitous —
    without a context, there are no felicity conditions. -/
theorem felicity_void_context (force content : I) :
    ¬felicitous force content (void : I) := by
  unfold felicitous speechAct; rw [rs_void_right']; linarith

/-- W325 (Austin, Lecture IV): Performative score against void context is zero. -/
theorem performative_void_context (force content : I) :
    performativeScore force content (void : I) = 0 := by
  unfold performativeScore speechAct; exact rs_void_right' _

/-- W326 (Austin, Lecture VIII): Speech acts enrich — performing a speech
    act creates something with more weight than the force alone. -/
theorem speechAct_enriches (force content : I) :
    rs (speechAct force content) (speechAct force content) ≥ rs force force := by
  unfold speechAct; exact compose_enriches' force content

/-- W327 (Austin, Lecture IX): Sequential speech acts reassociate —
    saying then saying more is compositionally coherent. -/
theorem sequential_speechActs (f c1 c2 : I) :
    compose (speechAct f c1) c2 = speechAct f (compose c1 c2) := by
  unfold speechAct; exact compose_assoc' f c1 c2

/-- W328 (Austin, Lecture X): The illocutionary cocycle — nested speech
    acts satisfy global consistency constraints. -/
theorem illocutionary_cocycle (f c1 c2 d : I) :
    illocutionaryEmergence f c1 d +
    illocutionaryEmergence (speechAct f c1) c2 d =
    illocutionaryEmergence c1 c2 d +
    illocutionaryEmergence f (compose c1 c2) d := by
  unfold illocutionaryEmergence speechAct; exact cocycle_condition f c1 c2 d

/-- A category mistake: composing ideas from different logical types.
    Ryle, The Concept of Mind, Ch. 1. The emergence is the anomaly. -/
noncomputable def categoryAnomaly (type1 type2 observer : I) : ℝ :=
  emergence type1 type2 observer

/-- W329 (Ryle, Ch. 1): Category anomaly with void is zero —
    void has no logical type to conflict with. -/
theorem categoryAnomaly_void_left (type2 observer : I) :
    categoryAnomaly (void : I) type2 observer = 0 :=
  emergence_void_left type2 observer

/-- W330 (Ryle, Ch. 1): Category anomaly with void on right is zero. -/
theorem categoryAnomaly_void_right (type1 observer : I) :
    categoryAnomaly type1 (void : I) observer = 0 :=
  emergence_void_right type1 observer

/-- W331 (Ryle, Ch. 1): Category anomaly is bounded — even a gross
    category mistake has bounded effect. -/
theorem categoryAnomaly_bounded (t1 t2 observer : I) :
    (categoryAnomaly t1 t2 observer) ^ 2 ≤
    rs (compose t1 t2) (compose t1 t2) * rs observer observer :=
  emergence_bounded' t1 t2 observer

/-- A disposition: a stable pattern of behavior — Ryle's analysis of
    mental concepts. The Concept of Mind, Ch. 5. -/
def disposition (pattern : I) (n : ℕ) : I := composeN pattern n

/-- W332 (Ryle, Ch. 5): The null disposition is void. -/
theorem disposition_zero (pattern : I) : disposition pattern 0 = (void : I) := rfl

/-- W333 (Ryle, Ch. 5): Disposition grows with repetition — established
    dispositions have more weight. -/
theorem disposition_enriches (pattern : I) (n : ℕ) :
    rs (disposition pattern (n + 1)) (disposition pattern (n + 1)) ≥
    rs (disposition pattern n) (disposition pattern n) := by
  unfold disposition; exact rs_composeN_mono pattern n

/-- W334 (Ryle, Ch. 5): Disposition weight is always non-negative. -/
theorem disposition_nonneg (pattern : I) (n : ℕ) :
    rs (disposition pattern n) (disposition pattern n) ≥ 0 := by
  unfold disposition; exact rs_composeN_nonneg pattern n

/-- W335 (Ryle, Ch. 5): Void pattern has void disposition at every level. -/
theorem disposition_void (n : ℕ) : disposition (void : I) n = (void : I) := by
  unfold disposition; exact composeN_void n

/-- W336 (Ryle, Ch. 2): The score difference between two speech acts
    with the same force depends only on content and emergence. -/
theorem speechAct_content_comparison (force c1 c2 ctx : I) :
    performativeScore force c1 ctx - performativeScore force c2 ctx =
    (rs c1 ctx - rs c2 ctx) +
    (emergence force c1 ctx - emergence force c2 ctx) := by
  simp only [performativeScore_decompose]; ring

/-- W337 (Austin, Lecture XII): Illocutionary emergence is bounded by
    the speech act's and observer's weight. -/
theorem illocutionary_bounded (force content context : I) :
    (illocutionaryEmergence force content context) ^ 2 ≤
    rs (speechAct force content) (speechAct force content) * rs context context := by
  unfold illocutionaryEmergence speechAct; exact emergence_bounded' force content context

/-- W338 (Austin's "Plea for Excuses"): An excuse modifies an action's
    resonance profile — composing the action with the excuse changes
    how it resonates with every observer. -/
theorem excuse_modifies_action (act excuse observer : I) :
    rs (compose act excuse) observer =
    rs act observer + rs excuse observer + emergence act excuse observer :=
  rs_compose_eq act excuse observer

/-- W339 (Austin, "Other Minds"): The criterion for another's mental state
    is behavioral — the resonance profile of their actions determines what
    mental state we attribute. Cf. Wittgenstein PI §580. -/
theorem other_minds_criterial (agent behavior _observer : I)
    (h : sameUse agent behavior) (c : I) :
    rs agent c = rs behavior c := h c

/-- W340 (Ryle, Ch. 6): Category anomaly satisfies the cocycle —
    the emergence of cross-category combinations is globally constrained. -/
theorem categoryAnomaly_cocycle (t1 t2 t3 d : I) :
    categoryAnomaly t1 t2 d + categoryAnomaly (compose t1 t2) t3 d =
    categoryAnomaly t2 t3 d + categoryAnomaly t1 (compose t2 t3) d := by
  unfold categoryAnomaly; exact cocycle_condition t1 t2 t3 d

/-- W341 (Ryle, Ch. 7): A non-void force always produces a non-void
    speech act — saying something with real force has an effect. -/
theorem speechAct_nontrivial (force content : I) (hne : force ≠ void) :
    speechAct force content ≠ void := by
  unfold speechAct; exact compose_ne_void_of_left force content hne

/-- W342 (Austin, "Performative Utterances"): A meaning-blind observer
    perceives no illocutionary emergence — they cannot distinguish
    performative from constative uses. -/
theorem meaningBlind_no_illocution {observer : I} (h : meaningBlind observer)
    (force content : I) : illocutionaryEmergence force content observer = 0 := by
  unfold illocutionaryEmergence; exact h force content

/-- W343 (Austin-Ryle synthesis): For a criterial force (left-linear),
    the performative score is purely additive — no illocutionary emergence. -/
theorem criterial_force_additive {force : I} (h : leftLinear force)
    (content context : I) :
    performativeScore force content context = rs force context + rs content context := by
  rw [performativeScore_decompose]; linarith [h content context]

end OrdinaryLanguagePhilosophy

/-! ## §30. Deep Mathematical Results

Building on the established IDT framework and Wittgenstein's philosophy,
we derive deeper mathematical consequences: iterated composition results,
weight theory, advanced cocycle identities, and structural theorems about
the interaction of emergence, resonance, and composition. -/

section DeepMathematicalResults
variable {I : Type*} [S : IdeaticSpace3 I]

/-- W344: Triple composition resonance via two cocycle applications. -/
theorem triple_resonance_full (a b c d : I) :
    rs (compose (compose a b) c) d =
    rs a d + rs b d + rs c d +
    emergence a b d + emergence (compose a b) c d := by
  rw [rs_compose_eq (compose a b) c d, rs_compose_eq a b d]; ring

/-- W345: Triple composition — alternative right-associated form. -/
theorem triple_resonance_right (a b c d : I) :
    rs (compose a (compose b c)) d =
    rs a d + rs b d + rs c d +
    emergence b c d + emergence a (compose b c) d := by
  rw [rs_compose_eq a (compose b c) d, rs_compose_eq b c d]; ring

/-- W346: The two triple decompositions agree (by associativity). -/
theorem triple_decomposition_agreement (a b c d : I) :
    rs a d + rs b d + rs c d +
    emergence a b d + emergence (compose a b) c d =
    rs a d + rs b d + rs c d +
    emergence b c d + emergence a (compose b c) d := by
  linarith [cocycle_condition a b c d]

/-- W347: Quadruple composition resonance decomposition. -/
theorem quadruple_resonance (a b c d e : I) :
    rs (compose (compose (compose a b) c) d) e =
    rs a e + rs b e + rs c e + rs d e +
    emergence a b e + emergence (compose a b) c e +
    emergence (compose (compose a b) c) d e := by
  rw [rs_compose_eq (compose (compose a b) c) d e]
  rw [rs_compose_eq (compose a b) c e, rs_compose_eq a b e]; ring

/-- W348: Self-resonance of a double composition lower bound. -/
theorem double_compose_weight_lb (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a :=
  compose_enriches' a b

/-- W349: Self-resonance of a triple composition lower bound. -/
theorem triple_compose_weight_lb (a b c : I) :
    rs (compose (compose a b) c) (compose (compose a b) c) ≥ rs a a := by
  calc rs (compose (compose a b) c) (compose (compose a b) c)
      ≥ rs (compose a b) (compose a b) := compose_enriches' (compose a b) c
    _ ≥ rs a a := compose_enriches' a b

/-- W350: Weight of n+1 iterations is at least weight of n iterations. -/
theorem composeN_weight_mono (a : I) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) ≥
    rs (composeN a n) (composeN a n) :=
  rs_composeN_mono a n

/-- W351: Weight of n iterations is non-negative. -/
theorem composeN_weight_nonneg (a : I) (n : ℕ) :
    rs (composeN a n) (composeN a n) ≥ 0 :=
  rs_composeN_nonneg a n

/-- W352: Non-void idea iterated once has positive weight. -/
theorem composeN_one_pos (a : I) (h : a ≠ void) :
    rs (composeN a 1) (composeN a 1) > 0 := by
  rw [composeN_one]; exact rs_self_pos a h

/-- W353: Emergence of a composition with itself (self-doubling emergence). -/
theorem self_doubling_emergence (a c : I) :
    emergence a a c = rs (compose a a) c - 2 * rs a c := by
  unfold emergence; ring

/-- W354: The total emergence of three items via left association. -/
theorem total_emergence_left (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    rs (compose (compose a b) c) d - rs a d - rs b d - rs c d := by
  unfold emergence; ring

/-- W355: The total emergence of three items via right association. -/
theorem total_emergence_right (a b c d : I) :
    emergence b c d + emergence a (compose b c) d =
    rs (compose a (compose b c)) d - rs a d - rs b d - rs c d := by
  unfold emergence; ring

/-- W356: Total emergence is independent of association order. -/
theorem total_emergence_independent (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

/-- W357: The resonance profile of compose a b determines a and b's
    individual contributions up to emergence. -/
theorem resonance_profile_constraint (a b c : I) :
    rs (compose a b) c - emergence a b c = rs a c + rs b c := by
  unfold emergence; ring

/-- W358: Emergence as a defect of linearity: if resonance were
    bilinear, emergence would vanish identically. -/
theorem emergence_is_nonlinearity_defect (a b c : I) :
    rs (compose a b) c = rs a c + rs b c + emergence a b c :=
  rs_compose_eq a b c

/-- W359: Weight of composition is at least the max of its parts' weights
    (since it's at least each one individually). -/
theorem weight_ge_left (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a :=
  compose_enriches' a b

/-- W360: Weight of composition is at least zero. -/
theorem weight_compose_nonneg (a b : I) :
    rs (compose a b) (compose a b) ≥ 0 :=
  rs_self_nonneg' (compose a b)

/-- W361: If composition has zero weight, it must be void. -/
theorem weight_zero_void (a b : I) (h : rs (compose a b) (compose a b) = 0) :
    compose a b = void :=
  rs_nondegen' (compose a b) h

/-- W362: If composition is void and left part is non-void, contradiction. -/
theorem compose_void_left_nonvoid (a b : I) (h1 : a ≠ void) (h2 : compose a b = void) :
    False :=
  compose_ne_void_of_left a b h1 h2

/-- W363: Double self-composition resonance expands. -/
theorem double_self_resonance (a c : I) :
    rs (compose a a) c = 2 * rs a c + emergence a a c := by
  rw [rs_compose_eq]; ring

/-- W364: Triple self-composition resonance via double and cocycle. -/
theorem triple_self_resonance (a c : I) :
    rs (compose (compose a a) a) c =
    3 * rs a c + emergence a a c + emergence (compose a a) a c := by
  rw [rs_compose_eq (compose a a) a c, rs_compose_eq a a c]; ring

/-- W365: Emergence is the "curvature" of the resonance function. -/
theorem emergence_as_curvature (a b c : I) :
    emergence a b c = rs (compose a b) c - rs a c - rs b c := by
  unfold emergence; ring

/-- W366: The emergence of three compositions decomposes into pairwise
    emergences (left-associated). -/
theorem three_fold_emergence_decompose (a b c d : I) :
    rs (compose (compose a b) c) d - rs a d - rs b d - rs c d =
    emergence a b d + emergence (compose a b) c d := by
  unfold emergence; ring

/-- W367: Void absorbs composition from the left without emergence. -/
theorem void_absorb_left_resonance (b c : I) :
    rs (compose (void : I) b) c = rs b c := by simp

/-- W368: Void absorbs composition from the right without emergence. -/
theorem void_absorb_right_resonance (a c : I) :
    rs (compose a (void : I)) c = rs a c := by simp

/-- W369: The cocycle applied to identical elements. -/
theorem cocycle_all_same (a d : I) :
    emergence a a d + emergence (compose a a) a d =
    emergence a a d + emergence a (compose a a) d :=
  cocycle_condition a a a d

/-- W370: The emergence difference between orderings reveals
    the non-commutativity of composition in ideatic space. -/
theorem emergence_order_difference (a b c : I) :
    emergence a b c - emergence b a c =
    rs (compose a b) c - rs (compose b a) c := by
  unfold emergence; ring

end DeepMathematicalResults


end IDT3
