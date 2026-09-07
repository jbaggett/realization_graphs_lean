/-
Copyright (c) 2026 Jeffrey S. Baggett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey S. Baggett
-/
import Realization.Transfer
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.SymmDiff

set_option autoImplicit false
set_option linter.style.nativeDecide false
set_option linter.dupNamespace false
set_option linter.unnecessarySimpa false

open scoped symmDiff

namespace Brualdi.RealizationGraph

universe u

variable {V : Type u}

/-- A realization of a degree function by a finite simple graph. -/
structure Realization [Fintype V] (d : V → ℕ) where
  graph : SimpleGraph V
  adjDecidable : DecidableRel graph.Adj
  degree_eq : letI := adjDecidable; ∀ v, graph.degree v = d v

namespace Realization

variable [Fintype V] {d : V → ℕ}

instance (G : Realization d) : DecidableRel G.graph.Adj :=
  G.adjDecidable

/-- The graph degree of a vertex in a realization, using the stored decidability instance. -/
def degree (G : Realization d) (v : V) : ℕ :=
  letI := G.adjDecidable
  G.graph.degree v

@[simp]
theorem degree_eq_apply (G : Realization d) (v : V) : G.degree v = d v :=
  G.degree_eq v

/-- The finite edge set of a realization. -/
noncomputable def edgeFinset (G : Realization d) : Finset (Sym2 V) := by
  classical
  letI := G.adjDecidable
  exact G.graph.edgeFinset

/-- The neighbor finset in a realization, using the stored decidability instance. -/
noncomputable def neighborFinset (G : Realization d) (v : V) : Finset V := by
  classical
  letI := G.adjDecidable
  exact G.graph.neighborFinset v

@[simp]
theorem mem_neighborFinset (G : Realization d) (v w : V) :
    w ∈ G.neighborFinset v ↔ G.graph.Adj v w := by
  classical
  simp [neighborFinset]

end Realization

variable [Fintype V] [DecidableEq V]

/-- One paper-convention 2-switch step: the edge sets differ in Hamming distance four. -/
noncomputable def twoSwitchAdjacent {d : V → ℕ} (G H : Realization d) : Prop :=
  ((G.edgeFinset) ∆ (H.edgeFinset)).card = 4

/-- The realization graph whose vertices are realizations and whose edges are 2-switch steps. -/
noncomputable def RealizationGraph (d : V → ℕ) : SimpleGraph (Realization d) where
  Adj G H := twoSwitchAdjacent G H
  symm := by
    constructor
    intro G H h
    dsimp [twoSwitchAdjacent] at h ⊢
    rwa [symmDiff_comm]
  loopless := by
    constructor
    intro G h
    simpa [twoSwitchAdjacent] using h

/-- Package a realization as the shared `Graphical` predicate from `Transfer.lean`. -/
def Realization.toGraphical {d : V → ℕ} (G : Realization d) : Graphical d :=
  ⟨G.graph, G.adjDecidable, G.degree_eq⟩

/-- Noncomputably unpackage the shared `Graphical` predicate as a realization. -/
noncomputable def realizationOfGraphical {d : V → ℕ} (h : Graphical d) : Realization d :=
  let G : SimpleGraph V := Classical.choose h
  let hGExists :
      ∃ hG : DecidableRel G.Adj,
        letI := hG
        ∀ v : V, G.degree v = d v := Classical.choose_spec h
  let hG : DecidableRel G.Adj := Classical.choose hGExists
  let hdeg :
      letI := hG
      ∀ v : V, G.degree v = d v := Classical.choose_spec hGExists
  { graph := G
    adjDecidable := hG
    degree_eq := hdeg }

/-- Delete `v` and decrement the residual demand on the prescribed neighbors `S`. -/
def residualDegree (d : V → ℕ) (v : V) (S : Finset V) (u : {x : V // x ≠ v}) : ℕ :=
  d u.val - if u.val ∈ S then 1 else 0

/-- The concrete left side of Observation 0. -/
def HasRealizationWithNeighborSet (d : V → ℕ) (v : V) (S : Finset V) : Prop :=
  ∃ G : Realization d, G.neighborFinset v = S

/-- An admissible neighbor set, phrased through the residual graphicality predicate. -/
abbrev AdmissibleNeighborSet (d : V → ℕ) (v : V) (S : Finset V) : Prop :=
  Graphical (residualDegree d v S)

@[simp]
theorem observation0_admissible_iff_graphical (d : V → ℕ) (v : V) (S : Finset V) :
    AdmissibleNeighborSet d v S ↔ Graphical (residualDegree d v S) :=
  Iff.rfl

end Brualdi.RealizationGraph
