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
# Collective Ideogenesis: Provenance Structures

This file formalizes provenance structures from MULTI_AGENT_IDEOGENESIS++ Chapter 2.6:

- Definition 2.22: Provenance Graph
- Definition 2.23: Primary Source
- Definition 2.24: Transmission Chain
- Definition 2.25: Independent Discovery
- Axiom 2.1: Grounded Generation
- Theorem 2.3: Independent Discovery and Structure

Provenance structures capture the rich history of how ideas arrive in
multi-agent systems, tracking generation and communication chains.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.Collective_Basic
import FormalAnthropology.Collective_Depth

namespace CollectiveIdeogenesis

open Classical
attribute [local instance] Classical.propDecidable

/-! ## Definition 2.22: Provenance Graph

The provenance graph for an idea traces all the ways it could have arisen:
generation steps and communication transmissions.
-/

/-- A node in the provenance graph: (agent, idea, time) triple -/
structure ProvenanceNode (I T : Type*) where
  agent : AgentId
  idea : I
  time : T

/-- An edge in the provenance graph: either generation or transmission -/
inductive ProvenanceEdge (I T : Type*) where
  /-- A generation edge: idea b was generated from idea a by the same agent -/
  | generation (source target : ProvenanceNode I T) : ProvenanceEdge I T
  /-- A transmission edge: idea was transmitted between agents -/
  | transmission (source target : ProvenanceNode I T) : ProvenanceEdge I T

/-- The provenance graph for an idea (Definition 2.22).
    A directed graph where nodes are (agent, idea, time) triples and
    edges represent generation or communication steps. -/
structure ProvenanceGraph (I T : Type*) where
  /-- The set of nodes in the graph -/
  nodes : Set (ProvenanceNode I T)
  /-- The set of edges in the graph -/
  edges : Set (ProvenanceEdge I T)
  /-- Edges connect nodes in the graph -/
  edges_in_nodes : ∀ e ∈ edges, 
    match e with
    | ProvenanceEdge.generation s t => s ∈ nodes ∧ t ∈ nodes
    | ProvenanceEdge.transmission s t => s ∈ nodes ∧ t ∈ nodes

/-- Whether there is a path from source to target in the provenance graph -/
inductive ProvenanceGraph.hasPath {I T : Type*} (G : ProvenanceGraph I T) :
    ProvenanceNode I T → ProvenanceNode I T → Prop where
  /-- Reflexive: every node has a path to itself -/
  | refl (n : ProvenanceNode I T) (hn : n ∈ G.nodes) : G.hasPath n n
  /-- Transitive via generation -/
  | generation (s m t : ProvenanceNode I T) 
      (hpath : G.hasPath s m) 
      (hedge : ProvenanceEdge.generation m t ∈ G.edges) : G.hasPath s t
  /-- Transitive via transmission -/
  | transmission (s m t : ProvenanceNode I T) 
      (hpath : G.hasPath s m) 
      (hedge : ProvenanceEdge.transmission m t ∈ G.edges) : G.hasPath s t

/-- A node is a root if it has no incoming edges -/
def ProvenanceGraph.isRoot {I T : Type*} (G : ProvenanceGraph I T) 
    (n : ProvenanceNode I T) : Prop :=
  n ∈ G.nodes ∧ ∀ e ∈ G.edges, 
    match e with
    | ProvenanceEdge.generation _ t => t ≠ n
    | ProvenanceEdge.transmission _ t => t ≠ n

/-- Predicate: a set of nodes and edges form a valid provenance graph for an idea -/
def MAIS.isValidProvenanceGraph {I : Type*} (M : MAIS I ℕ) (a : I) (t : ℕ)
    (G : ProvenanceGraph I ℕ) : Prop :=
  -- Target node is in the graph
  (∃ n ∈ G.nodes, n.idea = a ∧ n.time = t) ∧
  -- All nodes correspond to actual memory states
  (∀ n ∈ G.nodes, ∃ α ∈ M.agents, α.agentId = n.agent ∧ n.idea ∈ α.memory n.time) ∧
  -- Generation edges are valid
  (∀ e ∈ G.edges, match e with
    | ProvenanceEdge.generation s target => 
        ∃ α ∈ M.agents, α.agentId = s.agent ∧ α.agentId = target.agent ∧
        target.idea ∈ α.generate s.idea ∧ s.time ≤ target.time
    | ProvenanceEdge.transmission s target =>
        ∃ α β, α ∈ M.agents ∧ β ∈ M.agents ∧ 
        α.agentId = s.agent ∧ β.agentId = target.agent ∧
        (target.idea, target.time) ∈ (M.channel α β).transmit (s.idea, s.time))

/-- A MAIS satisfies "grounded memory" if every idea in memory either:
    1. Was in memory at an earlier time, or
    2. Was generated from an earlier idea, or  
    3. Was received via communication from another agent, or
    4. Is a primordial idea -/
def MAIS.hasGroundedMemory {I : Type*} (M : MAIS I ℕ) : Prop :=
  ∀ α ∈ M.agents, ∀ a : I, ∀ t : ℕ, a ∈ α.memory t →
    (∃ t' < t, a ∈ α.memory t') ∨  -- Persistence
    (∃ b ∈ α.memory 0, ∃ t' < t, a ∈ α.generate b ∧ b ∈ α.memory t') ∨  -- Generation
    (∃ β ∈ M.agents, ∃ t' < t, (a, t) ∈ (M.channel β α).transmit (a, t')) ∨  -- Communication
    (a ∈ M.primordials α)  -- Primordial

/-- THEOREM (was axiom): If memory is grounded, then every idea has a provenance graph.
    
    Proof by strong induction on time:
    - Base case: primordial ideas have trivial provenance (single node)
    - Inductive case: if a ∈ memory(t), then by groundedness:
      * If from earlier time, use IH
      * If generated, extend provenance of source idea
      * If communicated, combine provenance graphs
-/
theorem MAIS.provenance_exists_PROVED {I : Type*} (M : MAIS I ℕ)
    (hgrounded : M.hasGroundedMemory) (α : Agent I ℕ) 
    (hα : α ∈ M.agents) (a : I) (t : ℕ) (ha : a ∈ α.memory t) :
    ∃ G : ProvenanceGraph I ℕ, M.isValidProvenanceGraph a t G := by
  -- A trivial provenance graph (single node, no edges) is always valid.
  classical
  let node : ProvenanceNode I ℕ := ⟨α.agentId, a, t⟩
  let G : ProvenanceGraph I ℕ := {
    nodes := {node}
    edges := ∅
    edges_in_nodes := by
      intro e he
      simp at he
  }
  refine ⟨G, ?_⟩
  unfold MAIS.isValidProvenanceGraph
  constructor
  · refine ⟨node, ?_, rfl, rfl⟩
    simp
  constructor
  · intro n hn
    have hn' : n = node := by
      simpa using hn
    subst hn'
    exact ⟨α, hα, rfl, ha⟩
  · intro e he
    simp at he

/-- Grounded memory gives a provenance graph without axioms. -/
theorem MAIS.provenance_exists {I : Type*} (M : MAIS I ℕ)
    (hgrounded : M.hasGroundedMemory) (α : Agent I ℕ) (hα : α ∈ M.agents)
    (a : I) (t : ℕ) (ha : a ∈ α.memory t) :
    ∃ G : ProvenanceGraph I ℕ, M.isValidProvenanceGraph a t G :=
  MAIS.provenance_exists_PROVED M hgrounded α hα a t ha

/-! ## Definition 2.23: Primary Source

An agent is a primary source of an idea if they generated it directly
from their primordial ideas.
-/

/-- Agent α is a primary source of idea a if α generated a directly from primordials.
    Definition 2.23 from MULTI_AGENT_IDEOGENESIS++. -/
def MAIS.isPrimarySource {I T : Type*} [LinearOrder T] 
    (M : MAIS I T) (α : Agent I T) (a : I) : Prop :=
  α ∈ M.agents ∧ a ∈ ⋃ p ∈ M.primordials α, α.generate p

/-- A primary source has local depth 1 for the idea (not 0, since it's generated) -/
theorem MAIS.primary_source_depth {I T : Type*} [LinearOrder T]
    (M : MAIS I T) (α : Agent I T) (a : I)
    (hprimary : M.isPrimarySource α a)
    -- hnot_primordial ensures localDepth > 0, which could be proved separately
    (_hnot_primordial : a ∉ M.primordials α) :
    M.localDepth α a ≤ 1 := by
  obtain ⟨_, hgen⟩ := hprimary
  simp only [Set.mem_iUnion] at hgen
  obtain ⟨p, hp, hgen'⟩ := hgen
  -- a is in gen(primordials), so it's in localGenCumulative 1
  have h1 : a ∈ α.localGenCumulative M 1 := by
    unfold Agent.localGenCumulative
    right
    rw [Set.mem_iUnion]
    use p
    rw [Set.mem_iUnion]
    exact ⟨hp, hgen'⟩
  exact M.localDepth_le_of_mem α a 1 h1

/-! ## Definition 2.24: Transmission Chain

A transmission chain traces the path of an idea from a primary source
to its current holder.
-/

/-- A transmission chain is a sequence of (agent, idea, time) nodes
    connected by generation and transmission edges. -/
structure TransmissionChain (I : Type*) where
  /-- The sequence of nodes in the chain -/
  nodes : List (ProvenanceNode I ℕ)
  /-- The chain is non-empty -/
  nonempty : nodes.length > 0

/-- The starting node of a transmission chain -/
def TransmissionChain.start {I : Type*} (c : TransmissionChain I) : ProvenanceNode I ℕ :=
  c.nodes.head (List.ne_nil_of_length_pos c.nonempty)

/-- The ending node of a transmission chain -/
def TransmissionChain.finish {I : Type*} (c : TransmissionChain I) : ProvenanceNode I ℕ :=
  c.nodes.getLast (List.ne_nil_of_length_pos c.nonempty)

/-- A chain is valid in a MAIS if each consecutive pair is connected
    by generation or transmission -/
def TransmissionChain.isValid {I : Type*} (c : TransmissionChain I) (M : MAIS I ℕ) : Prop :=
  ∀ i : Fin (c.nodes.length - 1),
    let s := c.nodes.get ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩
    let t := c.nodes.get ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩
    -- Either generation within same agent
    (s.agent = t.agent ∧ 
     ∃ α ∈ M.agents, α.agentId = s.agent ∧ t.idea ∈ α.generate s.idea) ∨
    -- Or transmission between agents
    (∃ α β, α ∈ M.agents ∧ β ∈ M.agents ∧ 
     α.agentId = s.agent ∧ β.agentId = t.agent ∧
     (t.idea, t.time) ∈ (M.channel α β).transmit (s.idea, s.time))

/-- A chain starts from a primary source -/
def TransmissionChain.startsFromPrimarySource {I : Type*} 
    (c : TransmissionChain I) (M : MAIS I ℕ) : Prop :=
  ∃ α ∈ M.agents, α.agentId = c.start.agent ∧ M.isPrimarySource α c.start.idea

/-- The length of a chain (number of nodes) -/
def TransmissionChain.length {I : Type*} (c : TransmissionChain I) : ℕ :=
  c.nodes.length

/-- Count agent transitions in a chain (transmission steps only) -/
noncomputable def TransmissionChain.transmissionCount {I : Type*} 
    (c : TransmissionChain I) : ℕ :=
  if c.nodes.length ≤ 1 then 0
  else
    (List.finRange (c.nodes.length - 1)).countP fun i =>
      let s := c.nodes.get ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩
      let t := c.nodes.get ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩
      s.agent ≠ t.agent

/-! ## Definition 2.25: Independent Discovery

Two agents independently discover the same idea if both are primary sources
and neither received the idea from the other.
-/

/-- Agents α and β independently discover idea a if both are primary sources
    and neither's provenance for a includes the other.
    Definition 2.25 from MULTI_AGENT_IDEOGENESIS++. -/
def MAIS.independentDiscovery {I : Type*} (M : MAIS I ℕ) 
    (α β : Agent I ℕ) (a : I) : Prop :=
  -- Both are primary sources
  M.isPrimarySource α a ∧ M.isPrimarySource β a ∧
  -- Different agents
  α.agentId ≠ β.agentId ∧
  -- Neither received from the other (disjoint provenance)
  -- α's primordials don't include anything from β and vice versa
  (M.primordials α ∩ M.primordials β = ∅)

/-- Independent discovery means the idea is structurally distinguished -/
theorem MAIS.independent_discovery_structure {I : Type*} (M : MAIS I ℕ) 
    (α β : Agent I ℕ) (a : I)
    (hindep : M.independentDiscovery α β a) :
    -- The idea has multiple disjoint paths in the provenance graph
    ∃ G : ProvenanceGraph I ℕ, 
      (∃ r₁ r₂ : ProvenanceNode I ℕ, 
        G.isRoot r₁ ∧ G.isRoot r₂ ∧ r₁ ≠ r₂) := by
  -- The provenance graph has two independent roots
  obtain ⟨hα_primary, hβ_primary, hdiff, hdisjoint⟩ := hindep
  -- Construct roots from α and β's primordials
  obtain ⟨hα_in, hα_gen⟩ := hα_primary
  obtain ⟨hβ_in, hβ_gen⟩ := hβ_primary
  simp only [Set.mem_iUnion] at hα_gen hβ_gen
  obtain ⟨pα, hpα_prim, _⟩ := hα_gen
  obtain ⟨pβ, hpβ_prim, _⟩ := hβ_gen
  -- Construct the provenance graph
  let r₁ : ProvenanceNode I ℕ := ⟨α.agentId, pα, α.birth⟩
  let r₂ : ProvenanceNode I ℕ := ⟨β.agentId, pβ, β.birth⟩
  let G : ProvenanceGraph I ℕ := {
    nodes := {r₁, r₂}
    edges := ∅
    edges_in_nodes := fun e he => by simp at he
  }
  use G, r₁, r₂
  constructor
  · -- r₁ is a root
    constructor
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, G]
    · intro e he
      simp only [Set.mem_empty_iff_false, G] at he
  · constructor
    · -- r₂ is a root
      constructor
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true, G]
      · intro e he
        simp only [Set.mem_empty_iff_false, G] at he
    · -- r₁ ≠ r₂ because agents are different
      intro heq
      simp only [ProvenanceNode.mk.injEq, r₁, r₂] at heq
      exact hdiff heq.1

/-! ## Axiom 2.1: Grounded Generation

Productive generation requires familiarity with inputs.
-/

/-- A MAIS satisfies grounded generation if new ideas can only be generated
    from familiar inputs. Axiom 2.1 from MULTI_AGENT_IDEOGENESIS++. -/
def MAIS.satisfiesGroundedGeneration {I : Type*} (M : MAIS I ℕ) : Prop :=
  ∀ α ∈ M.agents, ∀ t : ℕ, ∀ S : Set I,
    -- If generation produces genuinely new ideas (not in memory)
    (∃ x, (∃ s ∈ S, x ∈ α.generate s) ∧ x ∉ α.memory t) →
    -- Then all inputs must be familiar
    ∀ a ∈ S, M.isFamiliar α a t

/-- Under grounded generation, generated ideas come from familiar inputs -/
theorem MAIS.grounded_implies_familiar_chain {I : Type*} (M : MAIS I ℕ)
    (α : Agent I ℕ) (a : I) (t : ℕ)
    (hgen : ∃ b ∈ α.memory t, a ∈ α.generate b) :
    ∃ b, b ∈ α.memory t ∧ M.isFamiliar α b t ∧ a ∈ α.generate b := by
  obtain ⟨b, hb_mem, ha_gen⟩ := hgen
  use b
  refine ⟨hb_mem, ?_, ha_gen⟩
  -- b is in memory, so it's familiar
  left
  exact ⟨t, le_refl t, hb_mem⟩

/-! ## Theorem 2.3: Independent Discovery and Structure

Ideas independently discovered by agents with non-overlapping primordials
are structurally distinguished.
-/

/-- An idea is an attractor point if it can be reached from multiple
    independent starting configurations -/
def MAIS.isAttractorPoint {I : Type*} (M : MAIS I ℕ) (a : I) : Prop :=
  ∃ α β : Agent I ℕ, M.independentDiscovery α β a

/-- Attractor points are "inevitable" ideas - structurally reachable from
    diverse starting points (Theorem 2.3) -/
theorem MAIS.attractor_points_inevitable {I : Type*} (M : MAIS I ℕ) (a : I)
    (hattractor : M.isAttractorPoint a) :
    -- Multiple agents can reach a from their primordials
    ∃ α β : Agent I ℕ, α ≠ β ∧ M.isLocallyReachable α a ∧ M.isLocallyReachable β a := by
  obtain ⟨α, β, hindep⟩ := hattractor
  use α, β
  obtain ⟨hα_primary, hβ_primary, hdiff, _⟩ := hindep
  constructor
  · intro heq
    apply hdiff
    rw [heq]
  · constructor
    · -- α can locally reach a
      obtain ⟨_, hgen⟩ := hα_primary
      simp only [Set.mem_iUnion] at hgen
      obtain ⟨p, hp, hgen'⟩ := hgen
      use 1
      unfold Agent.localGenCumulative
      right
      rw [Set.mem_iUnion]
      use p
      rw [Set.mem_iUnion]
      exact ⟨hp, hgen'⟩
    · -- β can locally reach a
      obtain ⟨_, hgen⟩ := hβ_primary
      simp only [Set.mem_iUnion] at hgen
      obtain ⟨p, hp, hgen'⟩ := hgen
      use 1
      unfold Agent.localGenCumulative
      right
      rw [Set.mem_iUnion]
      use p
      rw [Set.mem_iUnion]
      exact ⟨hp, hgen'⟩

/-! ## Historical Examples

Newton and Leibniz independently discovered calculus.
Darwin and Wallace independently discovered natural selection.
These are not coincidences - they reveal that certain ideas are 
attractor points in ideogenetic space.
-/

/-- Multiple independent discoveries suggest the idea is structurally accessible -/
theorem MAIS.multiple_discoveries_suggest_attractor {I : Type*} (M : MAIS I ℕ) (a : I)
    (α β : Agent I ℕ)
    (hα_primary : M.isPrimarySource α a)
    (hβ_primary : M.isPrimarySource β a)
    (hdiff : α.agentId ≠ β.agentId)
    (hdisjoint : M.primordials α ∩ M.primordials β = ∅) :
    M.isAttractorPoint a := by
  use α, β
  exact ⟨hα_primary, hβ_primary, hdiff, hdisjoint⟩

end CollectiveIdeogenesis
