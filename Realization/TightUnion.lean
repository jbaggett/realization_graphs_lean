/-
`TightUnion.lean` — **the tight-union lemma for Erdős–Gallai tight sets.**

WHY THIS FILE EXISTS.  Lemma 8.3d of `Paper-realization` propagates a lower Erdős–Gallai
witness upward by a *slack recurrence* on the sorted degree sequence: the paper's longest
internal argument, and in Lean the bulk of `lemma_8_3d_lower_witness_propagation`
(`SBPlusOrd.lean`).  The recurrence can be replaced by a statement about **sets of vertices**
rather than a monotone sequence of numerical slacks:

> a union of equal-sized tight sets, all of whose vertices have degree at least that common
> size, is itself tight.

Equality at a tied sorted prefix can then be read at *every* choice of tied labels, and taking
the union of those choices jumps directly to the larger prefix — in one step, with no recurrence.

REUSE.  `Brualdi.RealizationGraph.SBPlusOrd.isClique_of_sum_degree_eq` already proves the forward direction of the
equality case (tight → clique and saturated).  Its docstring records that the converse "also
holds and the numeric check confirms it … left unstated rather than unproved"; the union lemma
needs exactly that converse, so it is supplied here as `egTight_of_isClique_of_saturated`.

STATUS.  Reached from the `Realization` target through `SBPlusOrd.lean`, which imports it and is
where the lemma is consumed; it is not a root of its own.

PROVENANCE.  The mathematics replaces the slack recurrence the paper originally printed for
Lemma 8.3d, and was carried into Lean rather than discovered in it.  It is wired into Lemma 8.3d
through the graph/sequence tightness bridge in `SBPlusOrd.lean`.
-/
import Realization.EqualityCase

namespace Brualdi.RealizationGraph.TightUnion

open Finset

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **`T` is Erdős–Gallai tight**: the (EG-set) inequality holds with equality.  This is exactly
the hypothesis `Brualdi.RealizationGraph.SBPlusOrd.isClique_of_sum_degree_eq` consumes, named so that it can be both
consumed and produced. -/
def EGTight (G : SimpleGraph W) [DecidableRel G.Adj] (T : Finset W) : Prop :=
  ∑ u ∈ T, G.degree u = T.card * (T.card - 1) + ∑ u ∈ Tᶜ, min (G.degree u) T.card

/-- The double count behind (EG-set): the degrees of `T` count its internal adjacencies once
from each end, plus every edge leaving `T` once. -/
theorem sum_degree_decomp (G : SimpleGraph W) [DecidableRel G.Adj] (T : Finset W) :
    ∑ u ∈ T, G.degree u =
      (∑ u ∈ T, (G.neighborFinset u ∩ T).card) + ∑ u ∈ Tᶜ, (G.neighborFinset u ∩ T).card := by
  have hsplit (u : W) :
      G.degree u = (G.neighborFinset u ∩ T).card + (G.neighborFinset u ∩ Tᶜ).card := by
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

/-- Inside a clique, a member sees exactly the rest of the clique. -/
theorem inter_neighbor_eq_erase (G : SimpleGraph W) [DecidableRel G.Adj] {T : Finset W}
    (hclique : G.IsClique (T : Set W)) {u : W} (hu : u ∈ T) :
    G.neighborFinset u ∩ T = T.erase u := by
  ext y
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_erase]
  constructor
  · rintro ⟨hadj, hyT⟩
    exact ⟨fun h => G.irrefl (h ▸ hadj), hyT⟩
  · rintro ⟨hne, hyT⟩
    exact ⟨hclique (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hyT) (Ne.symm hne), hyT⟩

/-- **The converse of `Brualdi.RealizationGraph.SBPlusOrd.isClique_of_sum_degree_eq`.**  A clique whose outside vertices
are all saturated is tight.  Recorded there as true and unstated; the union lemma needs it, so
it is proved here. -/
theorem egTight_of_isClique_of_saturated (G : SimpleGraph W) [DecidableRel G.Adj] {T : Finset W}
    (hclique : G.IsClique (T : Set W))
    (hsat : ∀ u ∈ Tᶜ, (G.neighborFinset u ∩ T).card = min (G.degree u) T.card) :
    EGTight G T := by
  have hinternal_eq : ∀ u ∈ T, (G.neighborFinset u ∩ T).card = T.card - 1 := by
    intro u hu
    rw [inter_neighbor_eq_erase G hclique hu, Finset.card_erase_of_mem hu]
  unfold EGTight
  rw [sum_degree_decomp G T]
  congr 1
  · rw [Finset.sum_congr rfl hinternal_eq, Finset.sum_const, smul_eq_mul]
  · exact Finset.sum_congr rfl hsat

/-- **The tight-union lemma.**  Let `𝒯` be a nonempty collection of `t`-element tight sets and
let `H` be their union.  If every vertex of `H` has degree at least `t`, then `H` is tight.

The sets need not be nested and need not be the unique top sets of their size; the common size
and the degree bound on the union are what make the argument work.  No external structural
theorem is invoked.

⚠ The degree hypothesis is not decoration.  It is what lets a member of one `T` be reached from
a *different* `T'` of the collection: without it the union need not even be a clique. -/
theorem egTight_biUnion (G : SimpleGraph W) [DecidableRel G.Adj]
    {𝒯 : Finset (Finset W)} {t : ℕ}
    (hne : 𝒯.Nonempty)
    (hcard : ∀ T ∈ 𝒯, T.card = t)
    (htight : ∀ T ∈ 𝒯, EGTight G T)
    (hdeg : ∀ h ∈ 𝒯.biUnion id, t ≤ G.degree h) :
    EGTight G (𝒯.biUnion id) := by
  set H := 𝒯.biUnion id with hH
  -- Each member of the collection is tight, hence a clique with saturated outside.
  have hstruct : ∀ T ∈ 𝒯, G.IsClique (T : Set W) ∧
      ∀ u ∈ Tᶜ, (G.neighborFinset u ∩ T).card = min (G.degree u) T.card := by
    intro T hT
    exact Brualdi.RealizationGraph.SBPlusOrd.isClique_of_sum_degree_eq G (htight T hT)
  have hsub : ∀ T ∈ 𝒯, T ⊆ H := by
    intro T hT y hy
    exact Finset.mem_biUnion.mpr ⟨T, hT, hy⟩
  obtain ⟨T₀, hT₀⟩ := hne
  have ht_le : t ≤ H.card := by
    have := Finset.card_le_card (hsub T₀ hT₀)
    rwa [hcard T₀ hT₀] at this
  -- An outside vertex of degree at least `t` is adjacent to every member set, hence to all of `H`.
  have hbig : ∀ {u : W}, t ≤ G.degree u → ∀ T ∈ 𝒯, T ⊆ G.neighborFinset u ∨ u ∈ T := by
    intro u hu T hT
    by_cases huT : u ∈ T
    · exact Or.inr huT
    · refine Or.inl ?_
      have hsatT := (hstruct T hT).2 u (Finset.mem_compl.mpr huT)
      have hmin : min (G.degree u) T.card = T.card := by
        rw [hcard T hT]; omega
      rw [hmin] at hsatT
      have hEq : G.neighborFinset u ∩ T = T :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (le_of_eq hsatT.symm)
      intro y hy
      have hy' : y ∈ G.neighborFinset u ∩ T := by rw [hEq]; exact hy
      exact (Finset.mem_inter.mp hy').1
  -- `H` is a clique.
  have hHclique : G.IsClique (H : Set W) := by
    rw [SimpleGraph.isClique_iff]
    intro x hx y hy hxy
    obtain ⟨T, hT, hxT⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hx)
    have hydeg : t ≤ G.degree y := hdeg y (Finset.mem_coe.mp hy)
    rcases hbig hydeg T hT with hsubN | hyT
    · have : x ∈ G.neighborFinset y := hsubN hxT
      exact (SimpleGraph.mem_neighborFinset _ _ _).mp this |>.symm
    · exact (hstruct T hT).1 (Finset.mem_coe.mpr hxT) (Finset.mem_coe.mpr hyT) hxy
  -- Every outside vertex is saturated against `H`.
  have hHsat : ∀ u ∈ Hᶜ, (G.neighborFinset u ∩ H).card = min (G.degree u) H.card := by
    intro u hu
    have huH : u ∉ H := Finset.mem_compl.mp hu
    by_cases hdu : t ≤ G.degree u
    · -- high degree: adjacent to all of `H`
      have hHsubN : H ⊆ G.neighborFinset u := by
        intro y hy
        obtain ⟨T, hT, hyT⟩ := Finset.mem_biUnion.mp hy
        rcases hbig hdu T hT with hsubN | huT
        · exact hsubN hyT
        · exact absurd (hsub T hT huT) huH
      have hinter : G.neighborFinset u ∩ H = H :=
        Finset.inter_eq_right.mpr hHsubN
      have hcard_le : H.card ≤ G.degree u := by
        rw [← G.card_neighborFinset_eq_degree]
        exact Finset.card_le_card hHsubN
      rw [hinter]
      omega
    · -- low degree: all neighbors already lie inside a single member set
      rw [Nat.not_le] at hdu
      have huT₀ : u ∉ T₀ := fun h => huH (hsub T₀ hT₀ h)
      have hsatT := (hstruct T₀ hT₀).2 u (Finset.mem_compl.mpr huT₀)
      have hmin : min (G.degree u) T₀.card = G.degree u := by
        rw [hcard T₀ hT₀]; omega
      rw [hmin] at hsatT
      have hNsub : G.neighborFinset u ⊆ T₀ := by
        have hle : (G.neighborFinset u).card ≤ (G.neighborFinset u ∩ T₀).card := by
          rw [hsatT, G.card_neighborFinset_eq_degree]
        have hEq := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hle
        intro y hy
        have hy' : y ∈ G.neighborFinset u ∩ T₀ := by rw [hEq]; exact hy
        exact (Finset.mem_inter.mp hy').2
      have hinter : G.neighborFinset u ∩ H = G.neighborFinset u :=
        Finset.inter_eq_left.mpr (fun y hy => hsub T₀ hT₀ (hNsub hy))
      rw [hinter, G.card_neighborFinset_eq_degree]
      omega
  exact egTight_of_isClique_of_saturated G hHclique hHsat

end Brualdi.RealizationGraph.TightUnion
