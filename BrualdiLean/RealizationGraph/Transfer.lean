/-
Copyright (c) 2026 Jeffrey S. Baggett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey S. Baggett
-/
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Brualdi.RealizationGraph

universe u

/-- A labeled degree function is graphical if it is realized by a finite simple graph.

The decidability witness is packaged with the graph so that `SimpleGraph.degree` can be used
without making the graph computable globally. -/
def Graphical {V : Type u} [Fintype V] [DecidableEq V] (f : V → ℕ) : Prop :=
  ∃ G : SimpleGraph V, ∃ hG : DecidableRel G.Adj,
    letI := hG
    ∀ v : V, G.degree v = f v

/-- Delete the edge `xz` and add the edge `yz`. If either named pair is not a valid edge,
the adjacency predicate itself still stays loopless and symmetric; the degree lemmas below
record the hypotheses under which it performs the intended transfer. -/
def transferGraph {V : Type u} (G : SimpleGraph V) (x y z : V) : SimpleGraph V where
  Adj a b :=
    (G.Adj a b ∧ ¬ ((a = x ∧ b = z) ∨ (a = z ∧ b = x))) ∨
      (a ≠ b ∧ ((a = y ∧ b = z) ∨ (a = z ∧ b = y)))
  symm := ⟨by
    intro a b h
    rcases h with ⟨hG, hdel⟩ | ⟨hne, hnew⟩
    · left
      refine ⟨hG.symm, ?_⟩
      intro hb
      apply hdel
      rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
    · right
      refine ⟨hne.symm, ?_⟩
      rcases hnew with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩⟩
  loopless := ⟨by
    intro a h
    rcases h with ⟨hG, _⟩ | ⟨hne, _⟩
    · exact G.irrefl hG
    · exact hne rfl⟩

instance transferGraphDecidable {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (x y z : V) :
    DecidableRel (transferGraph G x y z).Adj := by
  intro a b
  unfold transferGraph
  infer_instance

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {x y z v : V}

theorem transferGraph_neighborFinset_x (hxz : G.Adj x z) (_hyz : ¬ G.Adj y z)
    (hxy : x ≠ y) :
    (transferGraph G x y z).neighborFinset x = (G.neighborFinset x).erase z := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset]
  simp [transferGraph, hxy, hxz.ne, and_comm]

theorem transferGraph_neighborFinset_y (hyz : ¬ G.Adj y z) (hxy : x ≠ y)
    (hyz_ne : y ≠ z) :
    (transferGraph G x y z).neighborFinset y = insert z (G.neighborFinset y) := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset]
  by_cases hwz : w = z
  · subst w
    simp [transferGraph, hxy.symm, hyz_ne, hyz]
  · simp [transferGraph, hxy.symm, hyz_ne, hwz, or_comm, and_comm]

theorem transferGraph_neighborFinset_z (hxz : G.Adj x z) (hyz : ¬ G.Adj y z)
    (hyz_ne : y ≠ z) :
    (transferGraph G x y z).neighborFinset z = insert y ((G.neighborFinset z).erase x) := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset]
  have hzy : ¬ G.Adj z y := fun h => hyz h.symm
  by_cases hwy : w = y
  · subst w
    simp [transferGraph, hyz_ne.symm, hzy]
  · by_cases hwx : w = x
    · subst w
      simp only [Finset.mem_insert, Finset.mem_erase, ne_eq, not_true_eq_false,
        SimpleGraph.mem_neighborFinset, false_and, or_false]
      constructor
      · intro h
        change (G.Adj z x ∧ ¬ ((z = x ∧ x = z) ∨ (z = z ∧ x = x))) ∨
            (z ≠ x ∧ ((z = y ∧ x = z) ∨ (z = z ∧ x = y))) at h
        rcases h with ⟨_, hdel⟩ | ⟨_, hnew⟩
        · exact False.elim (hdel (Or.inr ⟨rfl, rfl⟩))
        · rcases hnew with hnew | hnew
          · exact hnew.2.trans hnew.1
          · exact hnew.2
      · intro h
        exact False.elim (hwy h)
    · simp [transferGraph, hwy, hwx, hxz.ne', hyz_ne.symm, hzy, or_comm, and_comm]

theorem transferGraph_neighborFinset_other (hvx : v ≠ x) (hvy : v ≠ y) (hvz : v ≠ z) :
    (transferGraph G x y z).neighborFinset v = G.neighborFinset v := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset]
  simp [transferGraph, hvx, hvx.symm, hvy, hvz, hvz.symm, and_comm]

theorem transferGraph_degree_x (hxz : G.Adj x z) (hyz : ¬ G.Adj y z) (hxy : x ≠ y) :
    (transferGraph G x y z).degree x = G.degree x - 1 := by
  rw [SimpleGraph.degree, transferGraph_neighborFinset_x (G := G) (y := y) hxz hyz hxy]
  rw [Finset.card_erase_of_mem]
  · rfl
  · simpa [SimpleGraph.mem_neighborFinset] using hxz

theorem transferGraph_degree_y (hyz : ¬ G.Adj y z) (hxy : x ≠ y) (hyz_ne : y ≠ z) :
    (transferGraph G x y z).degree y = G.degree y + 1 := by
  rw [SimpleGraph.degree, transferGraph_neighborFinset_y (G := G) (x := x) hyz hxy hyz_ne]
  rw [Finset.card_insert_of_notMem]
  · rfl
  · intro hz
    exact hyz (by simpa [SimpleGraph.mem_neighborFinset] using hz)

theorem transferGraph_degree_z (hxz : G.Adj x z) (hyz : ¬ G.Adj y z) (hyz_ne : y ≠ z) :
    (transferGraph G x y z).degree z = G.degree z := by
  rw [SimpleGraph.degree, transferGraph_neighborFinset_z (G := G) hxz hyz hyz_ne]
  have hxmem : x ∈ G.neighborFinset z := by
    simpa [SimpleGraph.mem_neighborFinset] using hxz.symm
  have hymem : y ∉ (G.neighborFinset z).erase x := by
    intro hy
    have hzy_adj : G.Adj z y := by
      simpa [SimpleGraph.mem_neighborFinset] using Finset.mem_of_mem_erase hy
    exact hyz hzy_adj.symm
  rw [Finset.card_insert_of_notMem hymem, Finset.card_erase_of_mem hxmem]
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨x, hxmem⟩))

theorem transferGraph_degree_other (hvx : v ≠ x) (hvy : v ≠ y) (hvz : v ≠ z) :
    (transferGraph G x y z).degree v = G.degree v := by
  rw [SimpleGraph.degree, transferGraph_neighborFinset_other (G := G) hvx hvy hvz]
  rw [SimpleGraph.card_neighborFinset_eq_degree]

/-- Down-transfer for graphical labeled degree functions.

If `f x` exceeds `f y` by at least two, one unit of degree can be transferred from `x` to `y`
while preserving graphicality. -/
theorem down_transfer {f : V → ℕ} (hf : Graphical f) {x y : V} (hxydeg : f y + 2 ≤ f x) :
    Graphical (Function.update (Function.update f x (f x - 1)) y (f y + 1)) := by
  rcases hf with ⟨G, hGdec, hdeg⟩
  letI := hGdec
  change ∀ v : V, G.degree v = f v at hdeg
  have hxy : x ≠ y := by
    intro h
    subst y
    omega
  let A : Finset V := (G.neighborFinset x).erase y
  let B : Finset V := G.neighborFinset y
  have hAcardLower : f x - 1 ≤ A.card := by
    dsimp [A]
    by_cases hyx : y ∈ G.neighborFinset x
    · rw [Finset.card_erase_of_mem hyx]
      rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg x]
    · rw [Finset.erase_eq_of_notMem hyx]
      rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg x]
      exact Nat.sub_le _ _
  have hfy_lt_A : f y < A.card := by
    have hstrict : f y < f x - 1 := by omega
    exact lt_of_lt_of_le hstrict hAcardLower
  have hBcard : B.card = f y := by
    dsimp [B]
    exact hdeg y
  have hnot_sub : ¬ A ⊆ B := by
    intro hsub
    have hcardle : A.card ≤ B.card := Finset.card_le_card hsub
    omega
  obtain ⟨z, hzA, hzB⟩ := Finset.not_subset.mp hnot_sub
  have hz_ne_y : z ≠ y := (Finset.mem_erase.mp hzA).1
  have hzNx : z ∈ G.neighborFinset x := (Finset.mem_erase.mp hzA).2
  have hxz : G.Adj x z := by
    simpa [SimpleGraph.mem_neighborFinset] using hzNx
  have hyz : ¬ G.Adj y z := by
    intro hyzAdj
    exact hzB (by
      change z ∈ G.neighborFinset y
      simpa [SimpleGraph.mem_neighborFinset] using hyzAdj)
  let G' : SimpleGraph V := transferGraph G x y z
  let hG'dec : DecidableRel G'.Adj := inferInstance
  refine ⟨G', hG'dec, ?_⟩
  letI := hG'dec
  change ∀ v : V, G'.degree v =
    Function.update (Function.update f x (f x - 1)) y (f y + 1) v
  intro v
  by_cases hvx : v = x
  · subst v
    rw [transferGraph_degree_x (G := G) (y := y) hxz hyz hxy, hdeg x]
    simp [Function.update, hxy]
  · by_cases hvy : v = y
    · subst v
      rw [transferGraph_degree_y (G := G) (x := x) hyz hxy hz_ne_y.symm, hdeg y]
      simp [Function.update]
    · by_cases hvz : v = z
      · subst v
        rw [transferGraph_degree_z (G := G) hxz hyz hz_ne_y.symm, hdeg z]
        simp [Function.update, hvx, hvy]
      · rw [transferGraph_degree_other (G := G) hvx hvy hvz, hdeg v]
        simp [Function.update, hvx, hvy]

end Brualdi.RealizationGraph
