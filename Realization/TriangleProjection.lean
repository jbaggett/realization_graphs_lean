/-
Copyright (c) 2026 Jeffrey S. Baggett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey S. Baggett
-/
import Realization.Defs
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Triangle projection (E2-odd)

This module proves that every triangle in a realization graph projects at some ground vertex
to three pairwise adjacent neighbor sets.  The proof is entirely at the edge-finset symmetric-
difference level used by `RealizationGraph.Defs`.
-/

set_option autoImplicit false
set_option linter.style.nativeDecide false
set_option linter.dupNamespace false
set_option linter.unnecessarySimpa false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

open scoped symmDiff

namespace Brualdi.RealizationGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The simple graph whose edges are precisely the edge symmetric difference of `G` and `H`. -/
noncomputable def edgeDifferenceGraph {d : V → ℕ} (G H : Realization d) : SimpleGraph V where
  Adj v w := (G.graph.Adj v w ∧ ¬ H.graph.Adj v w) ∨
    (H.graph.Adj v w ∧ ¬ G.graph.Adj v w)
  symm := by
    constructor
    intro v w
    rintro (⟨hG, hH⟩ | ⟨hH, hG⟩)
    · exact Or.inl ⟨hG.symm, fun h ↦ hH h.symm⟩
    · exact Or.inr ⟨hH.symm, fun h ↦ hG h.symm⟩
  loopless := by
    constructor
    intro v
    simp

private noncomputable instance edgeDifferenceGraphAdjDecidable {d : V → ℕ}
    (G H : Realization d) : DecidableRel (edgeDifferenceGraph G H).Adj :=
  Classical.decRel _

@[simp]
theorem edgeDifferenceGraph_adj {d : V → ℕ} (G H : Realization d) (v w : V) :
    (edgeDifferenceGraph G H).Adj v w ↔
      (G.graph.Adj v w ∧ ¬ H.graph.Adj v w) ∨
        (H.graph.Adj v w ∧ ¬ G.graph.Adj v w) :=
  Iff.rfl

theorem edgeDifferenceGraph_neighborFinset {d : V → ℕ} (G H : Realization d) (v : V) :
    (edgeDifferenceGraph G H).neighborFinset v =
      G.neighborFinset v ∆ H.neighborFinset v := by
  classical
  ext w
  simp [edgeDifferenceGraph, Realization.mem_neighborFinset, Finset.mem_symmDiff]

theorem edgeDifferenceGraph_edgeFinset {d : V → ℕ} (G H : Realization d) :
    (edgeDifferenceGraph G H).edgeFinset = G.edgeFinset ∆ H.edgeFinset := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ v w =>
      simp [edgeDifferenceGraph, Realization.edgeFinset, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, Finset.mem_symmDiff]

private theorem neighbor_card_eq {d : V → ℕ} (G H : Realization d) (v : V) :
    (G.neighborFinset v).card = (H.neighborFinset v).card := by
  classical
  simp [Realization.neighborFinset, SimpleGraph.card_neighborFinset_eq_degree,
    G.degree_eq v, H.degree_eq v]

private theorem edgeDifference_degree_eq_twice {d : V → ℕ}
    (G H : Realization d) (v : V) :
    (edgeDifferenceGraph G H).degree v =
      2 * (G.neighborFinset v \ H.neighborFinset v).card := by
  classical
  rw [SimpleGraph.degree, edgeDifferenceGraph_neighborFinset]
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint]
  · have hcards := Finset.card_sdiff_comm (neighbor_card_eq G H v)
    omega
  · exact Finset.sdiff_disjoint.mono_right Finset.sdiff_subset

/-- Edge-set-level formulation of the alternating four-cycle structure of one switch.

The support has four distinct vertices.  At every support vertex the edge difference has
degree two, with exactly one incident edge belonging only to `G` and exactly one belonging
only to `H`.  A loopless two-regular simple graph on four vertices is a four-cycle, and the
last two equalities say that its colors alternate. -/
theorem four_edge_difference_is_alternating_cycle {d : V → ℕ}
    (G H : Realization d)
    (hfour : (G.edgeFinset ∆ H.edgeFinset).card = 4) :
    (edgeDifferenceGraph G H).support.toFinset.card = 4 ∧
      ∀ v ∈ (edgeDifferenceGraph G H).support,
        (edgeDifferenceGraph G H).degree v = 2 ∧
        (G.neighborFinset v \ H.neighborFinset v).card = 1 ∧
        (H.neighborFinset v \ G.neighborFinset v).card = 1 := by
  classical
  let D : SimpleGraph V := edgeDifferenceGraph G H
  have hDcard : D.edgeFinset.card = 4 := by
    simpa [D, edgeDifferenceGraph_edgeFinset] using hfour
  have hdeg_two_le : ∀ v ∈ D.support, 2 ≤ D.degree v := by
    intro v hv
    have hpos : 0 < D.degree v := (D.degree_pos_iff_mem_support v).2 hv
    change 0 < (edgeDifferenceGraph G H).degree v at hpos
    change 2 ≤ (edgeDifferenceGraph G H).degree v
    rw [edgeDifference_degree_eq_twice] at hpos ⊢
    omega
  have hsum : ∑ v ∈ D.support.toFinset, D.degree v = 8 := by
    rw [D.sum_degrees_support_eq_twice_card_edges, hDcard]
  have hsupp_le : D.support.toFinset.card ≤ 4 := by
    have hlower : 2 * D.support.toFinset.card ≤
        ∑ v ∈ D.support.toFinset, D.degree v := by
      calc
        2 * D.support.toFinset.card = ∑ _v ∈ D.support.toFinset, 2 := by
          simp [Nat.mul_comm]
        _ ≤ ∑ v ∈ D.support.toFinset, D.degree v := by
          exact Finset.sum_le_sum fun v hv ↦ hdeg_two_le v (Set.mem_toFinset.mp hv)
    omega
  have hedge_bound : 4 ≤ (Fintype.card D.support).choose 2 := by
    have h := (D.induce D.support).card_edgeFinset_le_card_choose_two
    rw [D.card_edgeFinset_induce_support, hDcard] at h
    exact h
  have hsupp_ge : 4 ≤ D.support.toFinset.card := by
    have hcard_type : Fintype.card D.support = D.support.toFinset.card := by simp
    rw [hcard_type] at hedge_bound
    by_contra h
    have hle : D.support.toFinset.card ≤ 3 := by omega
    interval_cases D.support.toFinset.card <;> simp at hedge_bound
  have hsupp : D.support.toFinset.card = 4 := by omega
  refine ⟨hsupp, ?_⟩
  intro v hv
  have hvfin : v ∈ D.support.toFinset := Set.mem_toFinset.mpr hv
  have herase_card : (D.support.toFinset.erase v).card = 3 := by
    rw [Finset.card_erase_of_mem hvfin, hsupp]
  have hrest : 6 ≤ ∑ w ∈ D.support.toFinset.erase v, D.degree w := by
    calc
      6 = ∑ _w ∈ D.support.toFinset.erase v, 2 := by simp [herase_card]
      _ ≤ ∑ w ∈ D.support.toFinset.erase v, D.degree w := by
        exact Finset.sum_le_sum fun w hw ↦
          hdeg_two_le w (Set.mem_toFinset.mp (Finset.mem_of_mem_erase hw))
  have hsplit : D.degree v + ∑ w ∈ D.support.toFinset.erase v, D.degree w = 8 := by
    calc
      D.degree v + ∑ w ∈ D.support.toFinset.erase v, D.degree w =
          (∑ w ∈ D.support.toFinset.erase v, D.degree w) + D.degree v := by omega
      _ = ∑ w ∈ D.support.toFinset, D.degree w := Finset.sum_erase_add _ _ hvfin
      _ = 8 := hsum
  have hdeg : D.degree v = 2 := by
    have := hdeg_two_le v hv
    omega
  have hGH : (G.neighborFinset v \ H.neighborFinset v).card = 1 := by
    change (edgeDifferenceGraph G H).degree v = 2 at hdeg
    rw [edgeDifference_degree_eq_twice] at hdeg
    omega
  have hHG := Finset.card_sdiff_comm (neighbor_card_eq G H v)
  exact ⟨hdeg, hGH, by omega⟩

/-- The repository's realization-graph adjacency supplies the four-edge hypothesis of the
alternating-cycle structure theorem. -/
theorem twoSwitchAdjacent_is_alternating_cycle {d : V → ℕ}
    {G H : Realization d} (h : twoSwitchAdjacent G H) :
    (edgeDifferenceGraph G H).support.toFinset.card = 4 ∧
      ∀ v ∈ (edgeDifferenceGraph G H).support,
        (edgeDifferenceGraph G H).degree v = 2 ∧
        (G.neighborFinset v \ H.neighborFinset v).card = 1 ∧
        (H.neighborFinset v \ G.neighborFinset v).card = 1 := by
  exact four_edge_difference_is_alternating_cycle G H h

private theorem edgeFinset_symmDiff_chain {d : V → ℕ}
    (G₁ G₂ G₃ : Realization d) :
    G₁.edgeFinset ∆ G₃.edgeFinset =
      (G₁.edgeFinset ∆ G₂.edgeFinset) ∆
        (G₂.edgeFinset ∆ G₃.edgeFinset) := by
  classical
  ext e
  simp only [Finset.mem_symmDiff]
  tauto

private theorem shared_edge_card_eq_two {d : V → ℕ}
    (G₁ G₂ G₃ : Realization d)
    (h₁₂ : (G₁.edgeFinset ∆ G₂.edgeFinset).card = 4)
    (h₂₃ : (G₂.edgeFinset ∆ G₃.edgeFinset).card = 4)
    (h₁₃ : (G₁.edgeFinset ∆ G₃.edgeFinset).card = 4) :
    ((G₁.edgeFinset ∆ G₂.edgeFinset) ∩
      (G₂.edgeFinset ∆ G₃.edgeFinset)).card = 2 := by
  classical
  let A := G₁.edgeFinset ∆ G₂.edgeFinset
  let B := G₂.edgeFinset ∆ G₃.edgeFinset
  have hA : A.card = 4 := h₁₂
  have hB : B.card = 4 := h₂₃
  have hAB : (A ∆ B).card = 4 := by
    rw [← edgeFinset_symmDiff_chain G₁ G₂ G₃]
    exact h₁₃
  have hsplitA := Finset.card_sdiff_add_card_inter A B
  have hsplitB := Finset.card_sdiff_add_card_inter B A
  have hsymm : (A ∆ B).card = (A \ B).card + (B \ A).card := by
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint]
    exact Finset.sdiff_disjoint.mono_right Finset.sdiff_subset
  have hinter : (A ∩ B).card = (B ∩ A).card := by rw [Finset.inter_comm]
  rw [hA] at hsplitA
  rw [hB] at hsplitB
  rw [hAB] at hsymm
  change (A ∩ B).card = 2
  omega

private theorem exists_endpoint_not_mem {e f : Sym2 V}
    (he : ¬ e.IsDiag) (hf : ¬ f.IsDiag) (hef : e ≠ f) : ∃ v, v ∈ e ∧ v ∉ f := by
  classical
  have hecard : e.toFinset.card = 2 := Sym2.card_toFinset_of_not_isDiag e he
  have hfcard : f.toFinset.card = 2 := Sym2.card_toFinset_of_not_isDiag f hf
  by_cases hopposite : Disjoint e.toFinset f.toFinset
  · -- Opposite shared edges: either endpoint of `e` is outside `f`.
    have hepos : 0 < e.toFinset.card := by omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hepos
    refine ⟨v, Sym2.mem_toFinset.mp hv, ?_⟩
    intro hvf
    exact (Finset.disjoint_left.mp hopposite) hv (Sym2.mem_toFinset.mpr hvf)
  · -- Adjacent shared edges: take the noncommon endpoint (the `a-b-x-d` endpoint).
    have hnsub : ¬ e.toFinset ⊆ f.toFinset := by
      intro hsub
      have heq : e.toFinset = f.toFinset :=
        Finset.eq_of_subset_of_card_le hsub (by omega)
      apply hef
      apply Sym2.ext
      intro x
      simpa only [Sym2.mem_toFinset] using Finset.ext_iff.mp heq x
    obtain ⟨v, hve, hvf⟩ := Finset.not_subset.mp hnsub
    exact ⟨v, Sym2.mem_toFinset.mp hve, fun h ↦ hvf (Sym2.mem_toFinset.mpr h)⟩

private theorem support_of_incident_edge {d : V → ℕ} {G H : Realization d}
    {e : Sym2 V} {v : V} (he : e ∈ G.edgeFinset ∆ H.edgeFinset) (hv : v ∈ e) :
    v ∈ (edgeDifferenceGraph G H).support := by
  classical
  rw [SimpleGraph.mem_support]
  rw [Sym2.mem_iff_exists] at hv
  obtain ⟨w, rfl⟩ := hv
  have hedge : s(v, w) ∈ (edgeDifferenceGraph G H).edgeFinset := by
    simpa [edgeDifferenceGraph_edgeFinset] using he
  exact ⟨w, by simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hedge⟩

private theorem exists_common_support {d : V → ℕ}
    (G₁ G₂ G₃ : Realization d)
    (h₁₂ : (G₁.edgeFinset ∆ G₂.edgeFinset).card = 4)
    (h₂₃ : (G₂.edgeFinset ∆ G₃.edgeFinset).card = 4)
    (h₁₃ : (G₁.edgeFinset ∆ G₃.edgeFinset).card = 4) :
    ∃ v, v ∈ (edgeDifferenceGraph G₁ G₂).support ∧
      v ∈ (edgeDifferenceGraph G₂ G₃).support ∧
      v ∈ (edgeDifferenceGraph G₁ G₃).support := by
  classical
  let A := G₁.edgeFinset ∆ G₂.edgeFinset
  let B := G₂.edgeFinset ∆ G₃.edgeFinset
  have hinter : (A ∩ B).card = 2 := shared_edge_card_eq_two G₁ G₂ G₃ h₁₂ h₂₃ h₁₃
  obtain ⟨e, f, hef, hpair⟩ := Finset.card_eq_two.mp hinter
  have heinter : e ∈ A ∩ B := by simp [hpair]
  have hfinter : f ∈ A ∩ B := by simp [hpair]
  have he_nondiag : ¬ e.IsDiag := by
    rcases Finset.mem_symmDiff.mp (Finset.mem_inter.mp heinter).1 with heG₁ | heG₂
    · exact G₁.graph.not_isDiag_of_mem_edgeFinset heG₁.1
    · exact G₂.graph.not_isDiag_of_mem_edgeFinset heG₂.1
  have hf_nondiag : ¬ f.IsDiag := by
    rcases Finset.mem_symmDiff.mp (Finset.mem_inter.mp hfinter).1 with hfG₁ | hfG₂
    · exact G₁.graph.not_isDiag_of_mem_edgeFinset hfG₁.1
    · exact G₂.graph.not_isDiag_of_mem_edgeFinset hfG₂.1
  obtain ⟨v, hve, hvf⟩ := exists_endpoint_not_mem he_nondiag hf_nondiag hef
  have hvA : v ∈ (edgeDifferenceGraph G₁ G₂).support :=
    support_of_incident_edge (Finset.mem_inter.mp heinter).1 hve
  have hvB : v ∈ (edgeDifferenceGraph G₂ G₃).support :=
    support_of_incident_edge (Finset.mem_inter.mp heinter).2 hve
  have hstructA := (four_edge_difference_is_alternating_cycle G₁ G₂ h₁₂).2 v hvA
  have hextra : ∃ w, w ∈ A ∧ v ∈ w ∧ w ≠ e := by
    have hdeg : ((edgeDifferenceGraph G₁ G₂).neighborFinset v).card = 2 := by
      have h := hstructA.1
      rw [SimpleGraph.degree] at h
      exact h
    have he_neighbor : Sym2.Mem.other hve ∈
        (edgeDifferenceGraph G₁ G₂).neighborFinset v := by
      have hedge : e ∈ (edgeDifferenceGraph G₁ G₂).edgeFinset := by
        simpa [edgeDifferenceGraph_edgeFinset] using (Finset.mem_inter.mp heinter).1
      have heeq : s(v, Sym2.Mem.other hve) = e := Sym2.other_spec hve
      rw [← heeq] at hedge
      simpa only [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet] using hedge
    have hneigh : ∃ y ∈ (edgeDifferenceGraph G₁ G₂).neighborFinset v,
        y ≠ Sym2.Mem.other hve := by
      by_contra h
      push Not at h
      have hsub : (edgeDifferenceGraph G₁ G₂).neighborFinset v ⊆
          {Sym2.Mem.other hve} := by
        intro y hy
        simp only [Finset.mem_singleton]
        exact h y hy
      have := Finset.card_le_card hsub
      simp only [Finset.card_singleton, hdeg] at this
      omega
    obtain ⟨y, hy, hyne⟩ := hneigh
    refine ⟨s(v, y), ?_, Sym2.mem_mk_left v y, ?_⟩
    · have : s(v, y) ∈ (edgeDifferenceGraph G₁ G₂).edgeFinset := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          SimpleGraph.mem_neighborFinset] using hy
      simpa [edgeDifferenceGraph_edgeFinset] using this
    · intro hsame
      exact hyne (Sym2.congr_right.mp (hsame.trans (Sym2.other_spec hve).symm))
  obtain ⟨g, hgA, hvg, hge⟩ := hextra
  have hgnotB : g ∉ B := by
    intro hgB
    have hginter : g ∈ A ∩ B := Finset.mem_inter.mpr ⟨hgA, hgB⟩
    rw [hpair] at hginter
    simp only [Finset.mem_insert, Finset.mem_singleton] at hginter
    exact hginter.elim hge (fun hgf ↦ hvf (hgf ▸ hvg))
  have hgC : g ∈ G₁.edgeFinset ∆ G₃.edgeFinset := by
    rw [edgeFinset_symmDiff_chain G₁ G₂ G₃]
    exact Finset.mem_symmDiff.mpr (Or.inl ⟨hgA, hgnotB⟩)
  exact ⟨v, hvA, hvB, support_of_incident_edge hgC hvg⟩

/-- E2-odd: a triangle in the realization graph projects to a triangle of neighbor sets at
some vertex.  Each projected edge is one exchange, i.e. symmetric difference two. -/
theorem triangle_projects_to_neighbor_triangle {d : V → ℕ}
    (G₁ G₂ G₃ : Realization d)
    (h₁₂ : twoSwitchAdjacent G₁ G₂)
    (h₂₃ : twoSwitchAdjacent G₂ G₃)
    (h₁₃ : twoSwitchAdjacent G₁ G₃) :
    ∃ v,
      G₁.neighborFinset v ≠ G₂.neighborFinset v ∧
      G₂.neighborFinset v ≠ G₃.neighborFinset v ∧
      G₁.neighborFinset v ≠ G₃.neighborFinset v ∧
      (G₁.neighborFinset v ∆ G₂.neighborFinset v).card = 2 ∧
      (G₂.neighborFinset v ∆ G₃.neighborFinset v).card = 2 ∧
      (G₁.neighborFinset v ∆ G₃.neighborFinset v).card = 2 := by
  classical
  dsimp [twoSwitchAdjacent] at h₁₂ h₂₃ h₁₃
  obtain ⟨v, hv₁₂, hv₂₃, hv₁₃⟩ :=
    exists_common_support G₁ G₂ G₃ h₁₂ h₂₃ h₁₃
  have hlocal₁₂ := (four_edge_difference_is_alternating_cycle G₁ G₂ h₁₂).2 v hv₁₂
  have hlocal₂₃ := (four_edge_difference_is_alternating_cycle G₂ G₃ h₂₃).2 v hv₂₃
  have hlocal₁₃ := (four_edge_difference_is_alternating_cycle G₁ G₃ h₁₃).2 v hv₁₃
  have hc₁₂ : (G₁.neighborFinset v ∆ G₂.neighborFinset v).card = 2 := by
    simpa [SimpleGraph.degree, edgeDifferenceGraph_neighborFinset] using hlocal₁₂.1
  have hc₂₃ : (G₂.neighborFinset v ∆ G₃.neighborFinset v).card = 2 := by
    simpa [SimpleGraph.degree, edgeDifferenceGraph_neighborFinset] using hlocal₂₃.1
  have hc₁₃ : (G₁.neighborFinset v ∆ G₃.neighborFinset v).card = 2 := by
    simpa [SimpleGraph.degree, edgeDifferenceGraph_neighborFinset] using hlocal₁₃.1
  refine ⟨v, ?_, ?_, ?_, hc₁₂, hc₂₃, hc₁₃⟩
  · exact fun h ↦ by simpa [h] using hc₁₂
  · exact fun h ↦ by simpa [h] using hc₂₃
  · exact fun h ↦ by simpa [h] using hc₁₃

end Brualdi.RealizationGraph
