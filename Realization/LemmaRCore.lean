/-
Copyright (c) 2026 Jeffrey S. Baggett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey S. Baggett
-/
import Realization.Observation0

set_option autoImplicit false
set_option linter.style.nativeDecide false

namespace Brualdi.RealizationGraph

universe u₁ u₂

variable {V : Type u₁} {W : Type u₂} [Fintype V] [Fintype W]

theorem comap_equiv_degree (G : SimpleGraph V) [DecidableRel G.Adj] (e : W ≃ V) (w : W) :
    (G.comap e).degree w = G.degree (e w) := by
  classical
  rw [SimpleGraph.degree]
  exact Finset.card_bij
    (fun x _hx => e x)
    (by
      intro x hx
      rw [SimpleGraph.mem_neighborFinset] at hx ⊢
      exact hx)
    (by
      intro x _hx y _hy hxy
      exact e.injective hxy)
    (by
      intro y hy
      refine ⟨e.symm y, ?_, by simp⟩
      rw [SimpleGraph.mem_neighborFinset] at hy ⊢
      simpa using hy)

def relabelRealization {d : V → ℕ} (e : W ≃ V) (G : Realization d) :
    Realization (fun w : W => d (e w)) where
  graph := G.graph.comap e
  adjDecidable := by
    infer_instance
  degree_eq := by
    intro w
    rw [comap_equiv_degree]
    exact G.degree_eq (e w)

/-- Relabelling transports a neighborhood by the inverse equivalence. -/
theorem relabelRealization_neighborFinset {d : V → ℕ} (e : W ≃ V)
    (G : Realization d) (w : W) :
    (relabelRealization e G).neighborFinset w =
      (G.neighborFinset (e w)).map e.symm.toEmbedding := by
  ext x
  simp [Realization.mem_neighborFinset, relabelRealization]

/-- Relabelling transports the finite edge set by the induced equivalence on unordered pairs. -/
theorem relabelRealization_edgeFinset {d : V → ℕ} (e : W ≃ V)
    (G : Realization d) :
    (relabelRealization e G).edgeFinset =
      G.edgeFinset.map e.symm.toEmbedding.sym2Map := by
  change (G.graph.comap e.toEmbedding).edgeFinset =
    G.graph.edgeFinset.map e.symm.toEmbedding.sym2Map
  ext z
  induction z using Sym2.inductionOn with
  | _ x y =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.comap_adj, Finset.mem_map, Function.Embedding.sym2Map_apply]
      constructor
      · intro h
        exact ⟨s(e x, e y), h, by simp⟩
      · rintro ⟨a, ha, hmap⟩
        change e.symm.toEmbedding.sym2Map a = s(x, y) at hmap
        have haeq : a = s(e x, e y) := by
          apply e.symm.toEmbedding.sym2Map.injective
          rw [hmap]
          simp [Function.Embedding.sym2Map_apply]
        rw [haeq] at ha
        exact ha

/-- Relabelling preserves the two-switch relation, for arbitrary finite ground types. -/
theorem relabelRealization_twoSwitchAdjacent_iff [DecidableEq V] [DecidableEq W]
    {d : V → ℕ} (e : W ≃ V) (G H : Realization d) :
    twoSwitchAdjacent (relabelRealization e G) (relabelRealization e H) ↔
      twoSwitchAdjacent G H := by
  unfold twoSwitchAdjacent
  rw [relabelRealization_edgeFinset, relabelRealization_edgeFinset]
  rw [Finset.map_eq_image, Finset.map_eq_image]
  rw [← Finset.image_symmDiff _ _ e.symm.toEmbedding.sym2Map.injective]
  rw [← Finset.map_eq_image]
  rw [Finset.card_map]

/-- Relabel a realization by a degree-preserving permutation of its ground type. -/
def relabelRealizationOfInvariant {d : V → ℕ} (e : Equiv.Perm V)
    (he : ∀ x, d (e x) = d x) (G : Realization d) : Realization d where
  graph := G.graph.comap e
  adjDecidable := by infer_instance
  degree_eq := by
    intro x
    rw [comap_equiv_degree, G.degree_eq, he]

/-- Neighborhood transport for a degree-preserving permutation. -/
theorem relabelRealizationOfInvariant_neighborFinset {d : V → ℕ}
    (e : Equiv.Perm V) (he : ∀ x, d (e x) = d x) (G : Realization d) (x : V) :
    (relabelRealizationOfInvariant e he G).neighborFinset x =
      (G.neighborFinset (e x)).map e.symm.toEmbedding := by
  ext y
  simp [Realization.mem_neighborFinset, relabelRealizationOfInvariant]

/-- A degree-preserving permutation acts by an automorphism of the realization graph. -/
theorem relabelRealizationOfInvariant_adj_iff [DecidableEq V] {d : V → ℕ}
    (e : Equiv.Perm V) (he : ∀ x, d (e x) = d x) (G H : Realization d) :
    (RealizationGraph d).Adj (relabelRealizationOfInvariant e he G)
        (relabelRealizationOfInvariant e he H) ↔
      (RealizationGraph d).Adj G H := by
  change twoSwitchAdjacent (relabelRealizationOfInvariant e he G)
      (relabelRealizationOfInvariant e he H) ↔ twoSwitchAdjacent G H
  unfold twoSwitchAdjacent
  have hG : (relabelRealizationOfInvariant e he G).edgeFinset =
      (relabelRealization e G).edgeFinset := by
    unfold Realization.edgeFinset
    congr
  have hH : (relabelRealizationOfInvariant e he H).edgeFinset =
      (relabelRealization e H).edgeFinset := by
    unfold Realization.edgeFinset
    congr
  rw [hG, hH]
  exact relabelRealization_twoSwitchAdjacent_iff e G H

variable [DecidableEq V]

theorem graphical_residual_const_congr {k : ℕ} {v : V} {S₁ S₂ : Finset V}
    (e : {x : V // x ≠ v} ≃ {x : V // x ≠ v})
    (he : ∀ u : {x : V // x ≠ v}, u.val ∈ S₂ ↔ (e u).val ∈ S₁) :
    Graphical (residualDegree (fun _ : V => k) v S₁) →
      Graphical (residualDegree (fun _ : V => k) v S₂) := by
  intro hG
  let G := realizationOfGraphical hG
  refine Realization.toGraphical ?_
  convert relabelRealization e G using 1
  funext u
  unfold residualDegree
  by_cases hu : u.val ∈ S₂
  · rw [if_pos hu, if_pos ((he u).mp hu)]
  · rw [if_neg hu, if_neg (fun h => hu ((he u).mpr h))]

/-- Lemma R core: for a constant degree function, admissibility is invariant under
an explicit permutation of `V \ {v}` carrying `S₁` to `S₂`. -/
theorem lemmaR_core_partition_symmetry {k : ℕ} {v : V} {S₁ S₂ : Finset V}
    (e : {x : V // x ≠ v} ≃ {x : V // x ≠ v})
    (he : ∀ u : {x : V // x ≠ v}, u.val ∈ S₂ ↔ (e u).val ∈ S₁) :
    AdmissibleNeighborSet (fun _ : V => k) v S₁ ↔
      AdmissibleNeighborSet (fun _ : V => k) v S₂ := by
  constructor
  · exact graphical_residual_const_congr e he
  · have he_symm :
        ∀ u : {x : V // x ≠ v}, u.val ∈ S₁ ↔ (e.symm u).val ∈ S₂ := by
      intro u
      have h := he (e.symm u)
      simpa using h.symm
    exact graphical_residual_const_congr e.symm he_symm

end Brualdi.RealizationGraph
