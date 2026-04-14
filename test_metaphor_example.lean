import Mathlib.Data.Set.Basic
import Mathlib.Topology.MetricSpace.Basic
import FormalAnthropology.SingleAgent_Basic

open Set

variable {S : IdeogeneticSystem}

inductive SourceDomainType
  | Space
  | Object
  deriving DecidableEq

structure SourceDomain (S : IdeogeneticSystem) where
  domain_type : SourceDomainType
  ideas : Set S.Idea
  nonempty : ideas.Nonempty
  embodied : Bool

structure TargetDomain (S : IdeogeneticSystem) where
  ideas : Set S.Idea
  nonempty : ideas.Nonempty
  abstraction_level : ℕ

structure MetaphoricalMapping (S : IdeogeneticSystem) [MetricSpace S.Idea] where
  source : SourceDomain S
  target : TargetDomain S
  map : S.Idea → Option S.Idea
  distortion : ℝ
  distortion_bounds : 0 ≤ distortion ∧ distortion ≤ 1
  maps_source_to_target : ∀ s ∈ source.ideas, ∀ t, map s = some t → t ∈ target.ideas

example [MetricSpace S.Idea] [Nonempty S.Idea] : 
    ∃ (time_space : MetaphoricalMapping S),
      time_space.source.domain_type = SourceDomainType.Space ∧
      time_space.distortion < 0.3 := by
  have h_nonempty_source : (univ : Set S.Idea).Nonempty := ⟨Classical.arbitrary S.Idea, mem_univ _⟩
  have h_nonempty_target : (univ : Set S.Idea).Nonempty := ⟨Classical.arbitrary S.Idea, mem_univ _⟩
  let source_domain : SourceDomain S := {
    domain_type := SourceDomainType.Space
    ideas := univ
    nonempty := h_nonempty_source
    embodied := true
  }
  let target_domain : TargetDomain S := {
    ideas := univ
    nonempty := h_nonempty_target
    abstraction_level := 3
  }
  let time_space_map : MetaphoricalMapping S := {
    source := source_domain
    target := target_domain
    map := fun _ => none
    distortion := 0.25
    distortion_bounds := by norm_num
    maps_source_to_target := by intros; contradiction
  }
  use time_space_map
  constructor
  · rfl
  · norm_num
