/-
Copyright (c) 2026 Jeffrey S. Baggett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey S. Baggett
-/
import BrualdiLean.RealizationGraph.Defs

set_option autoImplicit false
set_option linter.style.nativeDecide false
set_option linter.unnecessarySimpa false

namespace Brualdi.RealizationGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Delete a vertex and keep the induced graph on the complement. -/
def deleteVertexGraph (G : SimpleGraph V) (v : V) : SimpleGraph {x : V // x ≠ v} :=
  G.comap (fun u : {x : V // x ≠ v} => u.val)

instance (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    DecidableRel (deleteVertexGraph G v).Adj := by
  unfold deleteVertexGraph
  infer_instance

theorem deleteVertexGraph_degree_eq_erase (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (u : {x : V // x ≠ v}) :
    (deleteVertexGraph G v).degree u = ((G.neighborFinset u.val).erase v).card := by
  classical
  rw [SimpleGraph.degree]
  exact Finset.card_bij
    (fun w _hw => w.val)
    (by
      intro w hw
      have hw_adj : G.Adj u.val w.val := by
        rw [SimpleGraph.mem_neighborFinset] at hw
        simpa [deleteVertexGraph] using hw
      rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
      exact ⟨w.property, hw_adj⟩)
    (by
      intro a _ha b _hb h
      exact Subtype.ext h)
    (by
      intro w hw
      rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hw
      refine ⟨⟨w, hw.1⟩, ?_, rfl⟩
      rw [SimpleGraph.mem_neighborFinset]
      simpa [deleteVertexGraph] using hw.2)

theorem deleteVertexGraph_degree_eq_sub (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (u : {x : V // x ≠ v}) :
    (deleteVertexGraph G v).degree u =
      G.degree u.val - if G.Adj u.val v then 1 else 0 := by
  classical
  rw [deleteVertexGraph_degree_eq_erase]
  by_cases huv : G.Adj u.val v
  · have hv_mem : v ∈ G.neighborFinset u.val := by
      rw [SimpleGraph.mem_neighborFinset]
      exact huv
    rw [if_pos huv, Finset.card_erase_of_mem hv_mem, SimpleGraph.card_neighborFinset_eq_degree]
  · have hv_not_mem : v ∉ G.neighborFinset u.val := by
      rw [SimpleGraph.mem_neighborFinset]
      exact huv
    rw [if_neg huv, Finset.erase_eq_of_notMem hv_not_mem,
      SimpleGraph.card_neighborFinset_eq_degree, Nat.sub_zero]

def deleteVertexGraph_realizes_residual {d : V → ℕ} (G : Realization d)
    (v : V) (S : Finset V) (hS : G.neighborFinset v = S) :
    Realization (residualDegree d v S) where
  graph := deleteVertexGraph G.graph v
  adjDecidable := by
    infer_instance
  degree_eq := by
    intro u
    rw [deleteVertexGraph_degree_eq_sub]
    have hmem : u.val ∈ S ↔ G.graph.Adj u.val v := by
      rw [← hS, Realization.mem_neighborFinset]
      exact G.graph.adj_comm v u.val
    have hdeg : G.graph.degree u.val = d u.val := by
      letI := G.adjDecidable
      exact G.degree_eq u.val
    rw [hdeg, residualDegree]
    by_cases huS : u.val ∈ S
    · rw [if_pos huS, if_pos (hmem.mp huS)]
    · rw [if_neg huS, if_neg (fun h => huS (hmem.mpr h))]

theorem observation0_delete_direction {d : V → ℕ} {v : V} {S : Finset V} :
    HasRealizationWithNeighborSet d v S → Graphical (residualDegree d v S) := by
  rintro ⟨G, hS⟩
  exact (deleteVertexGraph_realizes_residual G v S hS).toGraphical

/-- The inclusion of the deleted vertex subtype. -/
def deletedVertexEmbedding (v : V) : {x : V // x ≠ v} ↪ V where
  toFun := Subtype.val
  inj' := Subtype.val_injective

/-- Add `v` back and join it exactly to the vertices of `S`. -/
def addVertexGraph (v : V) (S : Finset V) (hvS : v ∉ S)
    (H : SimpleGraph {x : V // x ≠ v}) : SimpleGraph V where
  Adj a b :=
    (∃ (ha : a ≠ v) (hb : b ≠ v), H.Adj ⟨a, ha⟩ ⟨b, hb⟩) ∨
      (a = v ∧ b ∈ S) ∨ (b = v ∧ a ∈ S)
  symm := by
    constructor
    intro a b h
    rcases h with ⟨ha, hb, hab⟩ | ⟨ha, hbS⟩ | ⟨hb, haS⟩
    · exact Or.inl ⟨hb, ha, hab.symm⟩
    · exact Or.inr (Or.inr ⟨ha, hbS⟩)
    · exact Or.inr (Or.inl ⟨hb, haS⟩)
  loopless := by
    constructor
    intro a h
    rcases h with ⟨ha, hb, haa⟩ | ⟨ha, haS⟩ | ⟨ha, haS⟩
    · have hsub : (⟨a, ha⟩ : {x : V // x ≠ v}) = ⟨a, hb⟩ := Subtype.ext rfl
      rw [hsub] at haa
      exact H.irrefl haa
    · exact hvS (by simpa [ha] using haS)
    · exact hvS (by simpa [ha] using haS)

instance (v : V) (S : Finset V) (hvS : v ∉ S)
    (H : SimpleGraph {x : V // x ≠ v}) [DecidableRel H.Adj] :
    DecidableRel (addVertexGraph v S hvS H).Adj := by
  intro a b
  unfold addVertexGraph
  infer_instance

theorem addVertexGraph_neighborFinset_v (v : V) (S : Finset V) (hvS : v ∉ S)
    (H : SimpleGraph {x : V // x ≠ v}) [DecidableRel H.Adj] :
    (addVertexGraph v S hvS H).neighborFinset v = S := by
  classical
  ext w
  rw [SimpleGraph.mem_neighborFinset]
  constructor
  · intro h
    rcases h with ⟨hv, _hw, _h⟩ | ⟨_hv, hwS⟩ | ⟨hwv, hvS'⟩
    · exact (hv rfl).elim
    · exact hwS
    · exact (hvS (by simpa [hwv] using hvS')).elim
  · intro hwS
    exact Or.inr (Or.inl ⟨rfl, hwS⟩)

theorem addVertexGraph_neighborFinset_ne (v : V) (S : Finset V) (hvS : v ∉ S)
    (H : SimpleGraph {x : V // x ≠ v}) [DecidableRel H.Adj]
    (u : {x : V // x ≠ v}) :
    (addVertexGraph v S hvS H).neighborFinset u.val =
      (H.neighborFinset u).map (deletedVertexEmbedding v) ∪
        (if u.val ∈ S then {v} else ∅) := by
  classical
  ext w
  rw [SimpleGraph.mem_neighborFinset, Finset.mem_union]
  constructor
  · intro h
    rcases h with ⟨hu, hw, huw⟩ | ⟨huv, _hwS⟩ | ⟨hwv, huS⟩
    · left
      rw [Finset.mem_map]
      refine ⟨⟨w, hw⟩, ?_, rfl⟩
      rw [SimpleGraph.mem_neighborFinset]
      have hu_eq : (⟨u.val, hu⟩ : {x : V // x ≠ v}) = u := Subtype.ext rfl
      simpa [hu_eq] using huw
    · exact (u.property huv).elim
    · right
      rw [if_pos huS]
      simp [hwv]
  · intro h
    rcases h with hmap | hnew
    · rw [Finset.mem_map] at hmap
      rcases hmap with ⟨w', hw', rfl⟩
      left
      refine ⟨u.property, w'.property, ?_⟩
      rw [SimpleGraph.mem_neighborFinset] at hw'
      exact hw'
    · by_cases huS : u.val ∈ S
      · rw [if_pos huS] at hnew
        right
        right
        exact ⟨by simpa using hnew, huS⟩
      · rw [if_neg huS] at hnew
        simp at hnew

theorem addVertexGraph_degree_ne (v : V) (S : Finset V) (hvS : v ∉ S)
    (H : SimpleGraph {x : V // x ≠ v}) [DecidableRel H.Adj]
    (u : {x : V // x ≠ v}) :
    (addVertexGraph v S hvS H).degree u.val =
      H.degree u + if u.val ∈ S then 1 else 0 := by
  classical
  rw [SimpleGraph.degree, addVertexGraph_neighborFinset_ne]
  by_cases huS : u.val ∈ S
  · rw [if_pos huS]
    have hdis :
        Disjoint ((H.neighborFinset u).map (deletedVertexEmbedding v)) ({v} : Finset V) := by
      rw [Finset.disjoint_singleton_right]
      intro hv_mem
      rw [Finset.mem_map] at hv_mem
      rcases hv_mem with ⟨w, _hw, hwv⟩
      exact w.property hwv
    rw [Finset.card_union_of_disjoint hdis]
    simp [deletedVertexEmbedding, SimpleGraph.card_neighborFinset_eq_degree, huS]
  · rw [if_neg huS]
    simp [SimpleGraph.card_neighborFinset_eq_degree, huS]

def addVertexGraph_realizes_original {d : V → ℕ} {v : V} {S : Finset V}
    (hvS : v ∉ S) (hcard : S.card = d v) (hpos : ∀ u, u ∈ S → 0 < d u)
    (H : Realization (residualDegree d v S)) : Realization d where
  graph := addVertexGraph v S hvS H.graph
  adjDecidable := by
    infer_instance
  degree_eq := by
    intro x
    by_cases hxv : x = v
    · subst x
      rw [SimpleGraph.degree, addVertexGraph_neighborFinset_v]
      exact hcard
    · let u : {x : V // x ≠ v} := ⟨x, hxv⟩
      have hdu :
          (addVertexGraph v S hvS H.graph).degree x =
            H.graph.degree u + if x ∈ S then 1 else 0 := by
        simpa [u] using addVertexGraph_degree_ne v S hvS H.graph u
      rw [hdu]
      have hHdeg : H.graph.degree u = residualDegree d v S u := by
        letI := H.adjDecidable
        exact H.degree_eq u
      rw [hHdeg, residualDegree]
      dsimp [u]
      by_cases hxS : x ∈ S
      · rw [if_pos hxS]
        exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr (hpos x hxS))
      · rw [if_neg hxS]
        simp

theorem observation0_add_direction {d : V → ℕ} {v : V} {S : Finset V}
    (hvS : v ∉ S) (hcard : S.card = d v) (hpos : ∀ u, u ∈ S → 0 < d u) :
    Graphical (residualDegree d v S) → HasRealizationWithNeighborSet d v S := by
  intro hH
  let H := realizationOfGraphical hH
  refine ⟨addVertexGraph_realizes_original hvS hcard hpos H, ?_⟩
  change (addVertexGraph v S hvS H.graph).neighborFinset v = S
  exact addVertexGraph_neighborFinset_v v S hvS H.graph

theorem observation0_with_positive {d : V → ℕ} {v : V} {S : Finset V}
    (hvS : v ∉ S) (hcard : S.card = d v) (hpos : ∀ u, u ∈ S → 0 < d u) :
    HasRealizationWithNeighborSet d v S ↔ Graphical (residualDegree d v S) :=
  ⟨observation0_delete_direction, observation0_add_direction hvS hcard hpos⟩

end Brualdi.RealizationGraph
