import FormalAnthropology.IDT_Foundations_v2

/-!
# IDT v2: Idea Diffusion Dynamics

Dynamics of idea diffusion in the ideatic space. How ideas spread,
compose, and change over time. Diffusion operators model agents
updating their ideas by composing with received signals.

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT2.Dynamics

open IDT2
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-! ## §1. Diffusion Step -/

/-- A diffusion step: an agent updates their idea by composing with a received signal -/
def diffusionStep (signal current : I) : I := compose current signal

/-- n steps of diffusion with the same signal -/
def iteratedDiffusion (signal : I) : ℕ → I → I
  | 0, current => current
  | n + 1, current => diffusionStep signal (iteratedDiffusion signal n current)

/-- A fixed point: when diffusing doesn't change the idea -/
def isFixedPoint (signal current : I) : Prop :=
  diffusionStep signal current = current

/-- Resonance gain from a single diffusion step -/
noncomputable def diffusionGain (signal current : I) : ℝ :=
  resonanceStrength (diffusionStep signal current) (diffusionStep signal current) -
  resonanceStrength current current

/-! ## §2. Basic Diffusion Properties -/

@[simp] theorem diffusionStep_void_signal (c : I) :
    diffusionStep (void : I) c = c := by
  unfold diffusionStep; simp

@[simp] theorem diffusionStep_void_current (s : I) :
    diffusionStep s (void : I) = s := by
  unfold diffusionStep; simp

theorem diffusionStep_eq_compose (s c : I) :
    diffusionStep s c = compose c s := rfl

/-- Sequential diffusion equals diffusion by composed signal -/
theorem diffusionStep_assoc (a b c : I) :
    diffusionStep a (diffusionStep b c) = diffusionStep (compose b a) c := by
  unfold diffusionStep; rw [compose_assoc]

/-! ## §3. Iterated Diffusion -/

@[simp] theorem iteratedDiffusion_zero (s : I) (c : I) :
    iteratedDiffusion s 0 c = c := rfl

theorem iteratedDiffusion_one (s : I) (c : I) :
    iteratedDiffusion s 1 c = diffusionStep s c := rfl

theorem iteratedDiffusion_succ (s : I) (n : ℕ) (c : I) :
    iteratedDiffusion s (n + 1) c = diffusionStep s (iteratedDiffusion s n c) := rfl

theorem iteratedDiffusion_void_signal (n : ℕ) (c : I) :
    iteratedDiffusion (void : I) n c = c := by
  induction n with
  | zero => rfl
  | succ n ih => unfold iteratedDiffusion; rw [ih, diffusionStep_void_signal]

/-- Iterated diffusion equals composing current with n-fold signal -/
theorem iterated_as_compose (s : I) (n : ℕ) (c : I) :
    iteratedDiffusion s n c = compose c (composeN s n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    change compose (iteratedDiffusion s n c) s = compose c (compose (composeN s n) s)
    rw [ih, compose_assoc]

/-- Iterated diffusion from void equals iterated self-composition of signal -/
theorem iterated_void_as_composeN (s : I) (n : ℕ) :
    iteratedDiffusion s n (void : I) = composeN s n := by
  rw [iterated_as_compose]; simp

/-- Two steps equals iterated diffusion 2 -/
theorem double_diffusion (s c : I) :
    diffusionStep s (diffusionStep s c) = iteratedDiffusion s 2 c := rfl

/-! ## §4. Fixed Points -/

/-- Void signal leaves everything fixed -/
theorem void_signal_all_fixed (c : I) : isFixedPoint (void : I) c := by
  unfold isFixedPoint; simp [diffusionStep]

/-- Void is a fixed point iff the signal is void -/
theorem void_current_fixed_iff (s : I) :
    isFixedPoint s (void : I) ↔ s = (void : I) := by
  unfold isFixedPoint diffusionStep; simp

/-- Fixed points are preserved under void signal -/
theorem fixed_point_compose_void (s c : I) (_ : isFixedPoint s c) :
    compose c (void : I) = c := by simp

/-! ## §5. Resonance During Diffusion -/

/-- Each diffusion step preserves or increases self-resonance relative to current -/
theorem diffusion_rs_ge_current (s c : I) :
    resonanceStrength (diffusionStep s c) (diffusionStep s c) ≥
    resonanceStrength c c := by
  unfold diffusionStep; exact rs_compose_self_right c s

/-- Each diffusion step preserves or increases self-resonance relative to signal -/
theorem diffusion_rs_ge_signal (s c : I) :
    resonanceStrength (diffusionStep s c) (diffusionStep s c) ≥
    resonanceStrength s s := by
  unfold diffusionStep; exact rs_compose_self_left s c

/-- Diffused ideas always have self-resonance ≥ 1 -/
theorem diffusion_rs_ge_one (s c : I) :
    resonanceStrength (diffusionStep s c) (diffusionStep s c) ≥ 1 := by
  linarith [diffusion_rs_ge_current (I := I) s c, rs_self_ge_one (I := I) c]

/-- Diffusion gain is always non-negative -/
theorem diffusionGain_nonneg (s c : I) : diffusionGain s c ≥ 0 := by
  unfold diffusionGain; linarith [diffusion_rs_ge_current (I := I) s c]

/-- Diffusion with void signal has zero gain -/
theorem diffusionGain_void_signal (c : I) : diffusionGain (void : I) c = 0 := by
  unfold diffusionGain; simp [diffusionStep]

/-! ## §6. Iterated Diffusion Resonance -/

/-- Self-resonance is monotonically non-decreasing with each diffusion step -/
theorem iterated_diffusion_rs_mono (s : I) (n : ℕ) (c : I) :
    resonanceStrength (iteratedDiffusion s (n + 1) c) (iteratedDiffusion s (n + 1) c) ≥
    resonanceStrength (iteratedDiffusion s n c) (iteratedDiffusion s n c) := by
  change resonanceStrength (diffusionStep s (iteratedDiffusion s n c))
           (diffusionStep s (iteratedDiffusion s n c)) ≥ _
  exact diffusion_rs_ge_current s (iteratedDiffusion s n c)

/-- Self-resonance after any number of diffusion steps is ≥ 1 -/
theorem iterated_diffusion_rs_ge_one (s : I) (n : ℕ) (c : I) :
    resonanceStrength (iteratedDiffusion s n c) (iteratedDiffusion s n c) ≥ 1 := by
  induction n with
  | zero => exact rs_self_ge_one c
  | succ n ih => linarith [iterated_diffusion_rs_mono (I := I) s n c]

/-- Self-resonance after diffusion is always ≥ starting self-resonance -/
theorem iterated_diffusion_rs_ge_start (s : I) (c : I) : ∀ (n : ℕ),
    resonanceStrength (iteratedDiffusion s n c) (iteratedDiffusion s n c) ≥
    resonanceStrength c c
  | 0 => le_refl _
  | n + 1 => by linarith [iterated_diffusion_rs_mono (I := I) s n c,
                           iterated_diffusion_rs_ge_start s c n]

/-! ## §7. Depth Bounds -/

theorem depth_diffusion_step (s c : I) :
    depth (diffusionStep s c) ≤ depth c + depth s := by
  unfold diffusionStep; exact depth_subadditive' c s

theorem iteratedDiffusion_depth_bound (s : I) (n : ℕ) (c : I) :
    depth (iteratedDiffusion s n c) ≤ n * depth s + depth c := by
  induction n with
  | zero => simp
  | succ n ih =>
    change depth (diffusionStep s (iteratedDiffusion s n c)) ≤ (n + 1) * depth s + depth c
    have h1 := depth_diffusion_step (I := I) s (iteratedDiffusion s n c)
    have h2 : (n + 1) * depth s + depth c = n * depth s + depth s + depth c := by ring
    omega

/-! ## §8. Cross-Resonance Bounds -/

/-- After diffusion, resonance with the signal is at least rs(current, void) -/
theorem diffusion_signal_rs_lower (s c : I) :
    resonanceStrength (diffusionStep s c) s ≥ resonanceStrength c (void : I) := by
  unfold diffusionStep
  have key := IdeaticSpace2.rs_compose_right_mono c (void : I) s
  simp at key; exact key

/-- After diffusion, resonance with the current is at least rs(signal, void) -/
theorem diffusion_current_rs_lower (s c : I) :
    resonanceStrength (diffusionStep s c) c ≥ resonanceStrength s (void : I) := by
  unfold diffusionStep
  have key := IdeaticSpace2.rs_compose_left_mono s (void : I) c
  simp at key; exact key

/-- Diffusing two ideas with the same signal preserves their resonance -/
theorem diffusion_preserves_rs (s a b : I) :
    resonanceStrength (diffusionStep s a) (diffusionStep s b) ≥
    resonanceStrength a b := by
  unfold diffusionStep
  exact IdeaticSpace2.rs_compose_right_mono a b s

/-- Diffusion with common current preserves resonance between signals -/
theorem diffusion_common_current_rs (a b c : I) :
    resonanceStrength (diffusionStep a c) (diffusionStep b c) ≥
    resonanceStrength a b := by
  unfold diffusionStep
  exact IdeaticSpace2.rs_compose_left_mono a b c

end IDT2.Dynamics
