/-
Copyright (c) 2026 Jeffrey S. Baggett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey S. Baggett
-/
import Realization.QStar

/-!
# The set-form Erdős–Gallai equality case

This prerequisite module breaks the former import cycle between `SBPlusOrd` and `TightUnion`.
The theorem below is moved verbatim from `SBPlusOrd`; its namespace and declaration name are
unchanged, so existing consumers continue to use the same result.
-/

namespace Brualdi.RealizationGraph.SBPlusOrd

/-- **(EG-set), the equality case.** Equality forces both termwise bounds to be tight: `T` is a
clique, and every vertex outside `T` sends `min(deg, |T|)` edges into it. -/
theorem isClique_of_sum_degree_eq {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] {T : Finset W}
    (heq : ∑ u ∈ T, G.degree u = T.card * (T.card - 1) + ∑ u ∈ Tᶜ, min (G.degree u) T.card) :
    G.IsClique (T : Set W) ∧
      ∀ u ∈ Tᶜ, (G.neighborFinset u ∩ T).card = min (G.degree u) T.card := by
  have hsplit (u : W) :
      G.degree u = (G.neighborFinset u ∩ T).card +
        (G.neighborFinset u ∩ Tᶜ).card := by
    rw [← G.card_neighborFinset_eq_degree]
    have hT : (G.neighborFinset u).filter (fun z => z ∈ T) =
        G.neighborFinset u ∩ T := Finset.filter_mem_eq_inter
    have hTc : (G.neighborFinset u).filter (fun z => z ∉ T) =
        G.neighborFinset u ∩ Tᶜ := by
      ext z
      simp
    rw [← hT, ← hTc]
    exact (Finset.card_filter_add_card_filter_not (s := G.neighborFinset u)
      (fun z => z ∈ T)).symm
  have hinter (u : W) (S : Finset W) :
      (G.neighborFinset u ∩ S).card =
        ∑ y ∈ S, if G.Adj u y then 1 else 0 := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
    congr 1
    ext y
    simp [SimpleGraph.mem_neighborFinset, and_comm]
  have hcross : (∑ u ∈ T, (G.neighborFinset u ∩ Tᶜ).card) =
      ∑ u ∈ Tᶜ, (G.neighborFinset u ∩ T).card := by
    calc
      (∑ u ∈ T, (G.neighborFinset u ∩ Tᶜ).card) =
          ∑ u ∈ T, ∑ y ∈ Tᶜ, if G.Adj u y then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro u _
            exact hinter u Tᶜ
      _ = ∑ y ∈ Tᶜ, ∑ u ∈ T, if G.Adj u y then 1 else 0 := Finset.sum_comm
      _ = ∑ y ∈ Tᶜ, ∑ u ∈ T, if G.Adj y u then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro y _
        apply Finset.sum_congr rfl
        intro u _
        simp only [G.adj_comm]
      _ = ∑ y ∈ Tᶜ, (G.neighborFinset y ∩ T).card := by
        apply Finset.sum_congr rfl
        intro y _
        exact (hinter y T).symm
  have hdecomp : ∑ u ∈ T, G.degree u =
      (∑ u ∈ T, (G.neighborFinset u ∩ T).card) +
        ∑ u ∈ Tᶜ, (G.neighborFinset u ∩ T).card := by
    calc
      (∑ u ∈ T, G.degree u) = ∑ u ∈ T,
          ((G.neighborFinset u ∩ T).card + (G.neighborFinset u ∩ Tᶜ).card) := by
            apply Finset.sum_congr rfl
            intro u _
            exact hsplit u
      _ = (∑ u ∈ T, (G.neighborFinset u ∩ T).card) +
          ∑ u ∈ T, (G.neighborFinset u ∩ Tᶜ).card := by
            rw [Finset.sum_add_distrib]
      _ = _ := by rw [hcross]
  have hinternal (u : W) (hu : u ∈ T) :
      (G.neighborFinset u ∩ T).card ≤ T.card - 1 := by
    have hsub : G.neighborFinset u ∩ T ⊆ T.erase u := by
      intro y hy
      rw [Finset.mem_erase]
      refine ⟨?_, (Finset.mem_inter.mp hy).2⟩
      intro hyu
      subst y
      exact G.irrefl (by
        simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hy).1)
    simpa [Finset.card_erase_of_mem hu] using Finset.card_le_card hsub
  have hexternal (u : W) (hu : u ∈ Tᶜ) :
      (G.neighborFinset u ∩ T).card ≤ min (G.degree u) T.card := by
    apply le_min
    · rw [← G.card_neighborFinset_eq_degree]
      exact Finset.card_le_card Finset.inter_subset_left
    · exact Finset.card_le_card Finset.inter_subset_right
  have hsum_internal : (∑ u ∈ T, (G.neighborFinset u ∩ T).card) ≤
      T.card * (T.card - 1) := by simpa using Finset.sum_le_sum hinternal
  have hsum_external : (∑ u ∈ Tᶜ, (G.neighborFinset u ∩ T).card) ≤
      ∑ u ∈ Tᶜ, min (G.degree u) T.card := Finset.sum_le_sum hexternal
  have htotal :
      (∑ u ∈ T, (G.neighborFinset u ∩ T).card) +
          ∑ u ∈ Tᶜ, (G.neighborFinset u ∩ T).card =
        T.card * (T.card - 1) + ∑ u ∈ Tᶜ, min (G.degree u) T.card := by
    rw [← hdecomp]
    exact heq
  have hsum_internal_eq : (∑ u ∈ T, (G.neighborFinset u ∩ T).card) =
      T.card * (T.card - 1) := by omega
  have hsum_external_eq : (∑ u ∈ Tᶜ, (G.neighborFinset u ∩ T).card) =
      ∑ u ∈ Tᶜ, min (G.degree u) T.card := by omega
  have hinternal_eq : ∀ u ∈ T,
      (G.neighborFinset u ∩ T).card = T.card - 1 :=
    (Finset.sum_eq_sum_iff_of_le hinternal).mp (by simpa using hsum_internal_eq)
  have hexternal_eq : ∀ u ∈ Tᶜ,
      (G.neighborFinset u ∩ T).card = min (G.degree u) T.card :=
    (Finset.sum_eq_sum_iff_of_le hexternal).mp hsum_external_eq
  refine ⟨?_, hexternal_eq⟩
  rw [G.isClique_iff]
  intro u hu v hv huv
  have hsub : G.neighborFinset u ∩ T ⊆ T.erase u := by
    intro y hy
    rw [Finset.mem_erase]
    refine ⟨?_, (Finset.mem_inter.mp hy).2⟩
    intro hyu
    subst y
    exact G.irrefl (by
      simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hy).1)
  have hcard_erase : (T.erase u).card = T.card - 1 := Finset.card_erase_of_mem hu
  have hinter_eq : G.neighborFinset u ∩ T = T.erase u := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hcard_erase, hinternal_eq u hu]
  have hvN : v ∈ G.neighborFinset u := by
    have : v ∈ T.erase u := Finset.mem_erase.mpr ⟨huv.symm, hv⟩
    rw [← hinter_eq] at this
    exact (Finset.mem_inter.mp this).1
  simpa only [SimpleGraph.mem_neighborFinset] using hvN

end Brualdi.RealizationGraph.SBPlusOrd
