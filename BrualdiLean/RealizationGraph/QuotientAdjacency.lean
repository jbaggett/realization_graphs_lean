/-
Copyright (c) 2026 Jeffrey S. Baggett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey S. Baggett
-/
import BrualdiLean.RealizationGraph.Defs
import BrualdiLean.RealizationGraph.Observation0

set_option autoImplicit false
set_option linter.style.nativeDecide false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

open scoped symmDiff

namespace Brualdi.RealizationGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

private theorem finset_symmDiff_erase_erase_insert_insert {α : Type u} [DecidableEq α]
    {E : Finset α} {e₁ e₂ f₁ f₂ : α}
    (he₁ : e₁ ∈ E) (he₂ : e₂ ∈ E) (hf₁ : f₁ ∉ E) (hf₂ : f₂ ∉ E)
    (he₁e₂ : e₁ ≠ e₂) (he₁f₁ : e₁ ≠ f₁) (he₁f₂ : e₁ ≠ f₂)
    (he₂f₁ : e₂ ≠ f₁) (he₂f₂ : e₂ ≠ f₂) (hf₁f₂ : f₁ ≠ f₂) :
    E ∆ insert f₂ (insert f₁ ((E.erase e₁).erase e₂)) = {e₁, e₂, f₁, f₂} := by
  ext x
  by_cases hx₁ : x = e₁
  · subst x
    simp [Finset.mem_symmDiff, he₁, he₁e₂, he₁f₁, he₁f₂]
  · by_cases hx₂ : x = e₂
    · subst x
      simp [Finset.mem_symmDiff, he₂, he₁e₂.symm, he₂f₁, he₂f₂]
    · by_cases hxf₁ : x = f₁
      · subst x
        simp [Finset.mem_symmDiff, hf₁, he₁f₁.symm, he₂f₁.symm, hf₁f₂]
      · by_cases hxf₂ : x = f₂
        · subst x
          simp [Finset.mem_symmDiff, hf₂, he₁f₂.symm, he₂f₂.symm, hf₁f₂.symm]
        · simp [Finset.mem_symmDiff, hx₁, hx₂, hxf₁, hxf₂]

private theorem finset_card_four {α : Type u} [DecidableEq α] {e₁ e₂ f₁ f₂ : α}
    (he₁e₂ : e₁ ≠ e₂) (he₁f₁ : e₁ ≠ f₁) (he₁f₂ : e₁ ≠ f₂)
    (he₂f₁ : e₂ ≠ f₁) (he₂f₂ : e₂ ≠ f₂) (hf₁f₂ : f₁ ≠ f₂) :
    ({e₁, e₂, f₁, f₂} : Finset α).card = 4 := by
  rw [Finset.card_eq_four]
  exact ⟨e₁, e₂, f₁, f₂, he₁e₂, he₁f₁, he₁f₂, he₂f₁, he₂f₂, hf₁f₂, rfl⟩

private theorem twoSwitchAdjacent_symm {d : V → ℕ} {G H : Realization d}
    (h : twoSwitchAdjacent G H) : twoSwitchAdjacent H G := by
  dsimp [twoSwitchAdjacent] at h ⊢
  rwa [symmDiff_comm]

/-- The graph obtained by the paper's switch
`vb, ca ↦ va, cb`, implemented as two existing one-edge transfers. -/
noncomputable def quotientSwitchGraph (G : SimpleGraph V) (v b a c : V) : SimpleGraph V :=
  transferGraph (transferGraph G b a v) a b c

instance quotientSwitchGraphDecidable (G : SimpleGraph V) [DecidableRel G.Adj]
    (v b a c : V) : DecidableRel (quotientSwitchGraph G v b a c).Adj := by
  unfold quotientSwitchGraph
  infer_instance

set_option linter.flexible false in
private theorem transferGraph_edgeFinset {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y z : V} (hxz : G.Adj x z) (hyz : ¬ G.Adj y z)
    (hxy : x ≠ y) (hyz_ne : y ≠ z) :
    (transferGraph G x y z).edgeFinset = insert s(y, z) (G.edgeFinset.erase s(x, z)) := by
  ext e
  induction e using Sym2.ind with
  | h p q =>
      have hnzy : ¬ G.Adj z y := fun h => hyz h.symm
      have hxz' : G.Adj z x := hxz.symm
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_insert,
        Finset.mem_erase]
      simp [transferGraph, hxz, hxz', hyz, hnzy, hxy, hxy.symm, hyz_ne, hyz_ne.symm,
        Sym2.eq_iff]
      constructor
      · rintro (⟨hpq, hp, hq⟩ | ⟨hne, hnew⟩)
        · exact Or.inr ⟨⟨hp, hq⟩, hpq⟩
        · exact Or.inl hnew
      · rintro (hnew | ⟨⟨hp, hq⟩, hpq⟩)
        · refine Or.inr ⟨?_, hnew⟩
          rcases hnew with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hyz_ne
          · exact hyz_ne.symm
        · exact Or.inl ⟨hpq, hp, hq⟩

private theorem quotientSwitchGraph_edgeFinset {G : SimpleGraph V} [DecidableRel G.Adj]
    {v b a c : V} (hvb : G.Adj v b) (hva : ¬ G.Adj v a)
    (hca : G.Adj c a) (hcb : ¬ G.Adj c b)
    (hav : a ≠ v) (hbv : b ≠ v) (hba : b ≠ a) (hcv : c ≠ v) (hcb_ne : c ≠ b) :
    (quotientSwitchGraph G v b a c).edgeFinset =
      insert s(b, c) (insert s(a, v) ((G.edgeFinset.erase s(b, v)).erase s(a, c))) := by
  let G₁ : SimpleGraph V := transferGraph G b a v
  have hG₁ca : G₁.Adj a c := by
    change (transferGraph G b a v).Adj a c
    simp [transferGraph, hca.symm, hba.symm, hcv, hav]
  have hG₁cb : ¬ G₁.Adj b c := by
    change ¬ (transferGraph G b a v).Adj b c
    have hbc : ¬ G.Adj b c := fun h => hcb h.symm
    simp [transferGraph, hbc, hba, hbv]
  have hstep₂ :
      (quotientSwitchGraph G v b a c).edgeFinset =
        insert s(b, c) (G₁.edgeFinset.erase s(a, c)) := by
    change (transferGraph G₁ a b c).edgeFinset =
      insert s(b, c) (G₁.edgeFinset.erase s(a, c))
    exact transferGraph_edgeFinset (G := G₁) (x := a) (y := b) (z := c)
      hG₁ca hG₁cb hba.symm hcb_ne.symm
  have hstep₁ :
      G₁.edgeFinset = insert s(a, v) (G.edgeFinset.erase s(b, v)) := by
    exact transferGraph_edgeFinset (G := G) (x := b) (y := a) (z := v)
      hvb.symm (fun h => hva h.symm) hba hav
  have hnew_old_ne : s(a, v) ≠ s(a, c) := by
    intro h
    rcases (Sym2.eq_iff.mp h) with ⟨_, hv_eq_c⟩ | ⟨ha_eq_c, hv_eq_a⟩
    · exact hcv hv_eq_c.symm
    · exact hav hv_eq_a.symm
  rw [hstep₂, hstep₁, Finset.erase_insert_of_ne hnew_old_ne]

private theorem quotientSwitchGraph_degree_eq {d : V → ℕ} (G : Realization d)
    {v b a c : V} (hvb : G.graph.Adj v b) (hva : ¬ G.graph.Adj v a)
    (hca : G.graph.Adj c a) (hcb : ¬ G.graph.Adj c b)
    (hav : a ≠ v) (hbv : b ≠ v) (hba : b ≠ a) (hcv : c ≠ v) (hcb_ne : c ≠ b) :
    letI : DecidableRel (quotientSwitchGraph G.graph v b a c).Adj :=
      quotientSwitchGraphDecidable G.graph v b a c
    ∀ x : V, (quotientSwitchGraph G.graph v b a c).degree x = d x := by
  classical
  let G₁ : SimpleGraph V := transferGraph G.graph b a v
  have hG₁ca : G₁.Adj a c := by
    change (transferGraph G.graph b a v).Adj a c
    simp [transferGraph, hca.symm, hba.symm, hcv, hav]
  have hG₁cb : ¬ G₁.Adj b c := by
    change ¬ (transferGraph G.graph b a v).Adj b c
    have hbc : ¬ G.graph.Adj b c := fun h => hcb h.symm
    simp [transferGraph, hbc, hba, hbv]
  have hdb_pos : 0 < d b := by
    rw [← G.degree_eq b]
    exact hvb.symm.degree_pos_left
  intro x
  by_cases hxv : x = v
  · subst x
    have h₂ := transferGraph_degree_other (G := G₁) (x := a) (y := b) (z := c)
      (v := v) hav.symm hbv.symm hcv.symm
    have h₁ := transferGraph_degree_z (G := G.graph) (x := b) (y := a) (z := v)
      hvb.symm (fun h => hva h.symm) hav
    change (transferGraph G₁ a b c).degree v = d v
    rw [h₂, h₁, G.degree_eq]
  · by_cases hxb : x = b
    · subst x
      have h₂ := transferGraph_degree_y (G := G₁) (x := a) (y := b) (z := c)
        hG₁cb hba.symm hcb_ne.symm
      have h₁ := transferGraph_degree_x (G := G.graph) (x := b) (y := a) (z := v)
        hvb.symm (fun h => hva h.symm) hba
      change (transferGraph G₁ a b c).degree b = d b
      rw [h₂, h₁, G.degree_eq]
      omega
    · by_cases hxa : x = a
      · subst x
        have h₂ := transferGraph_degree_x (G := G₁) (x := a) (y := b) (z := c)
          hG₁ca hG₁cb hba.symm
        have h₁ := transferGraph_degree_y (G := G.graph) (x := b) (y := a) (z := v)
          (fun h => hva h.symm) hba hav
        change (transferGraph G₁ a b c).degree a = d a
        rw [h₂, h₁, G.degree_eq]
        omega
      · by_cases hxc : x = c
        · subst x
          have h₂ := transferGraph_degree_z (G := G₁) (x := a) (y := b) (z := c)
            hG₁ca hG₁cb hcb_ne.symm
          have h₁ := transferGraph_degree_other (G := G.graph) (x := b) (y := a) (z := v)
            (v := c) hcb_ne hca.ne hcv
          change (transferGraph G₁ a b c).degree c = d c
          rw [h₂, h₁, G.degree_eq]
        · have h₂ := transferGraph_degree_other (G := G₁) (x := a) (y := b) (z := c)
            (v := x) hxa hxb hxc
          have h₁ := transferGraph_degree_other (G := G.graph) (x := b) (y := a) (z := v)
            (v := x) hxb hxa hxv
          change (transferGraph G₁ a b c).degree x = d x
          rw [h₂, h₁, G.degree_eq]

noncomputable def quotientSwitchRealization {d : V → ℕ} (G : Realization d)
    {v b a c : V} (hvb : G.graph.Adj v b) (hva : ¬ G.graph.Adj v a)
    (hca : G.graph.Adj c a) (hcb : ¬ G.graph.Adj c b)
    (hav : a ≠ v) (hbv : b ≠ v) (hba : b ≠ a) (hcv : c ≠ v) (hcb_ne : c ≠ b) :
    Realization d where
  graph := quotientSwitchGraph G.graph v b a c
  adjDecidable := quotientSwitchGraphDecidable G.graph v b a c
  degree_eq :=
    quotientSwitchGraph_degree_eq G hvb hva hca hcb hav hbv hba hcv hcb_ne

private theorem quotientSwitch_neighborFinset_v {d : V → ℕ} (G : Realization d)
    {S : Finset V} {v b a c : V} (hS : G.neighborFinset v = S)
    (hvb : G.graph.Adj v b) (hva : ¬ G.graph.Adj v a)
    (hca : G.graph.Adj c a) (hcb : ¬ G.graph.Adj c b)
    (hav : a ≠ v) (hbv : b ≠ v) (hba : b ≠ a) (hcv : c ≠ v) (hcb_ne : c ≠ b) :
    (quotientSwitchRealization G hvb hva hca hcb hav hbv hba hcv hcb_ne).neighborFinset v =
      insert a (S.erase b) := by
  classical
  let G₁ : SimpleGraph V := transferGraph G.graph b a v
  have hfirst :
      G₁.neighborFinset v = insert a ((G.graph.neighborFinset v).erase b) := by
    simpa [G₁] using
      transferGraph_neighborFinset_z (G := G.graph) (x := b) (y := a) (z := v)
        hvb.symm (fun h => hva h.symm) hav
  change (quotientSwitchGraph G.graph v b a c).neighborFinset v = insert a (S.erase b)
  have hsecond :
      (transferGraph G₁ a b c).neighborFinset v = G₁.neighborFinset v := by
    exact transferGraph_neighborFinset_other (G := G₁) (x := a) (y := b) (z := c)
      (v := v) hav.symm hbv.symm hcv.symm
  have hgraphS : G.graph.neighborFinset v = S := by
    simpa [Realization.neighborFinset] using hS
  change (transferGraph G₁ a b c).neighborFinset v = insert a (S.erase b)
  rw [hsecond, hfirst, hgraphS]

omit [Fintype V] in
private theorem four_switch_edges_card {v b a c : V}
    (hav : a ≠ v) (hbv : b ≠ v) (hba : b ≠ a) (hcv : c ≠ v) (hca_ne : c ≠ a)
    (hcb_ne : c ≠ b) :
    ({s(v, b), s(c, a), s(v, a), s(c, b)} : Finset (Sym2 V)).card = 4 := by
  apply finset_card_four
  · intro h
    rcases (Sym2.eq_iff.mp h) with ⟨hv_eq_c, hb_eq_a⟩ | ⟨hv_eq_a, hb_eq_c⟩
    · exact hcv hv_eq_c.symm
    · exact hav hv_eq_a.symm
  · intro h
    rcases (Sym2.eq_iff.mp h) with ⟨hv_eq_v, hb_eq_a⟩ | ⟨hv_eq_a, hb_eq_v⟩
    · exact hba hb_eq_a
    · exact hav hv_eq_a.symm
  · intro h
    rcases (Sym2.eq_iff.mp h) with ⟨hv_eq_c, hb_eq_b⟩ | ⟨hv_eq_b, hb_eq_c⟩
    · exact hcv hv_eq_c.symm
    · exact hbv hv_eq_b.symm
  · intro h
    rcases (Sym2.eq_iff.mp h) with ⟨hc_eq_v, ha_eq_a⟩ | ⟨hc_eq_a, ha_eq_v⟩
    · exact hcv hc_eq_v
    · exact hca_ne hc_eq_a
  · intro h
    rcases (Sym2.eq_iff.mp h) with ⟨_, ha_eq_b⟩ | ⟨hc_eq_b, _⟩
    · exact hba ha_eq_b.symm
    · exact hcb_ne hc_eq_b
  · intro h
    rcases (Sym2.eq_iff.mp h) with ⟨hv_eq_c, ha_eq_b⟩ | ⟨hv_eq_b, ha_eq_c⟩
    · exact hcv hv_eq_c.symm
    · exact hbv hv_eq_b.symm

private theorem quotientSwitch_twoSwitchAdjacent {d : V → ℕ} (G : Realization d)
    {v b a c : V} (hvb : G.graph.Adj v b) (hva : ¬ G.graph.Adj v a)
    (hca : G.graph.Adj c a) (hcb : ¬ G.graph.Adj c b)
    (hav : a ≠ v) (hbv : b ≠ v) (hba : b ≠ a) (hcv : c ≠ v) (hcb_ne : c ≠ b) :
    twoSwitchAdjacent G
      (quotientSwitchRealization G hvb hva hca hcb hav hbv hba hcv hcb_ne) := by
  classical
  dsimp [twoSwitchAdjacent, Realization.edgeFinset]
  let K : Finset (Sym2 V) := {s(b, v), s(a, c), s(a, v), s(b, c)}
  have hfin :
      (quotientSwitchGraph G.graph v b a c).edgeFinset =
        insert s(b, c) (insert s(a, v) ((G.graph.edgeFinset.erase s(b, v)).erase s(a, c))) :=
    quotientSwitchGraph_edgeFinset (G := G.graph) hvb hva hca hcb hav hbv hba hcv hcb_ne
  have he₁e₂ : s(b, v) ≠ s(a, c) := by
    intro h
    rcases (Sym2.eq_iff.mp h) with ⟨hb_eq_a, hv_eq_c⟩ | ⟨hb_eq_c, hv_eq_a⟩
    · exact hcv hv_eq_c.symm
    · exact hav hv_eq_a.symm
  have he₁f₁ : s(b, v) ≠ s(a, v) := by
    intro h
    rcases (Sym2.eq_iff.mp h) with ⟨hb_eq_a, _⟩ | ⟨hb_eq_v, hv_eq_a⟩
    · exact hba hb_eq_a
    · exact hbv hb_eq_v
  have he₁f₂ : s(b, v) ≠ s(b, c) := by
    intro h
    rcases (Sym2.eq_iff.mp h) with ⟨_, hv_eq_c⟩ | ⟨hb_eq_c, hv_eq_b⟩
    · exact hcv hv_eq_c.symm
    · exact hbv hv_eq_b.symm
  have he₂f₁ : s(a, c) ≠ s(a, v) := by
    intro h
    rcases (Sym2.eq_iff.mp h) with ⟨_, hc_eq_v⟩ | ⟨ha_eq_v, hc_eq_a⟩
    · exact hcv hc_eq_v
    · exact hav ha_eq_v
  have he₂f₂ : s(a, c) ≠ s(b, c) := by
    intro h
    rcases (Sym2.eq_iff.mp h) with ⟨ha_eq_b, _⟩ | ⟨ha_eq_c, hc_eq_b⟩
    · exact hba ha_eq_b.symm
    · exact hcb_ne hc_eq_b
  have hf₁f₂ : s(a, v) ≠ s(b, c) := by
    intro h
    rcases (Sym2.eq_iff.mp h) with ⟨ha_eq_b, hv_eq_c⟩ | ⟨ha_eq_c, hv_eq_b⟩
    · exact hba ha_eq_b.symm
    · exact hbv hv_eq_b.symm
  have hsymm :
      G.graph.edgeFinset ∆
          insert s(b, c) (insert s(a, v) ((G.graph.edgeFinset.erase s(b, v)).erase s(a, c))) =
        K := by
    simpa [K] using
      finset_symmDiff_erase_erase_insert_insert
        (E := G.graph.edgeFinset) (e₁ := s(b, v)) (e₂ := s(a, c))
        (f₁ := s(a, v)) (f₂ := s(b, c))
        (SimpleGraph.mem_edgeFinset.mpr (by simpa [SimpleGraph.mem_edgeSet] using hvb.symm))
        (SimpleGraph.mem_edgeFinset.mpr (by simpa [SimpleGraph.mem_edgeSet] using hca.symm))
        (by
          intro h
          have hav_edge : G.graph.Adj a v := by
            simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using h
          exact hva hav_edge.symm)
        (by
          intro h
          have hbc_edge : G.graph.Adj b c := by
            simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using h
          exact hcb hbc_edge.symm)
        he₁e₂ he₁f₁ he₁f₂ he₂f₁ he₂f₂ hf₁f₂
  change (G.graph.edgeFinset ∆ (quotientSwitchGraph G.graph v b a c).edgeFinset).card = 4
  rw [hfin, hsymm]
  exact finset_card_four he₁e₂ he₁f₁ he₁f₂ he₂f₁ he₂f₂ hf₁f₂

/-- The exact four-edge symmetric difference of a literal quotient switch. This public set-level
form is stronger than `sSideConnectorSwitch_spec`'s adjacency conclusion and supports collision
arguments between two switches with a common target. -/
theorem quotientSwitchRealization_symmDiff {d : V → ℕ} (G : Realization d)
    {v b a c : V} (hvb : G.graph.Adj v b) (hva : ¬ G.graph.Adj v a)
    (hca : G.graph.Adj c a) (hcb : ¬ G.graph.Adj c b)
    (hav : a ≠ v) (hbv : b ≠ v) (hba : b ≠ a) (hcv : c ≠ v) (hcb_ne : c ≠ b) :
    G.edgeFinset ∆
        (quotientSwitchRealization G hvb hva hca hcb hav hbv hba hcv hcb_ne).edgeFinset =
      {s(b, v), s(a, c), s(a, v), s(b, c)} := by
  classical
  have hfin :
      (quotientSwitchGraph G.graph v b a c).edgeFinset =
        insert s(b, c) (insert s(a, v)
          ((G.graph.edgeFinset.erase s(b, v)).erase s(a, c))) :=
    quotientSwitchGraph_edgeFinset (G := G.graph) hvb hva hca hcb hav hbv hba hcv hcb_ne
  have he₁e₂ : s(b, v) ≠ s(a, c) := by
    intro h
    rcases (Sym2.eq_iff.mp h) with ⟨hb_eq_a, hv_eq_c⟩ | ⟨hb_eq_c, hv_eq_a⟩
    · exact hcv hv_eq_c.symm
    · exact hav hv_eq_a.symm
  have he₁f₁ : s(b, v) ≠ s(a, v) := by
    intro h
    rcases (Sym2.eq_iff.mp h) with ⟨hb_eq_a, _⟩ | ⟨hb_eq_v, hv_eq_a⟩
    · exact hba hb_eq_a
    · exact hbv hb_eq_v
  have he₁f₂ : s(b, v) ≠ s(b, c) := by
    intro h
    rcases (Sym2.eq_iff.mp h) with ⟨_, hv_eq_c⟩ | ⟨hb_eq_c, hv_eq_b⟩
    · exact hcv hv_eq_c.symm
    · exact hbv hv_eq_b.symm
  have he₂f₁ : s(a, c) ≠ s(a, v) := by
    intro h
    rcases (Sym2.eq_iff.mp h) with ⟨_, hc_eq_v⟩ | ⟨ha_eq_v, hc_eq_a⟩
    · exact hcv hc_eq_v
    · exact hav ha_eq_v
  have he₂f₂ : s(a, c) ≠ s(b, c) := by
    intro h
    rcases (Sym2.eq_iff.mp h) with ⟨ha_eq_b, _⟩ | ⟨ha_eq_c, hc_eq_b⟩
    · exact hba ha_eq_b.symm
    · exact hcb_ne hc_eq_b
  have hf₁f₂ : s(a, v) ≠ s(b, c) := by
    intro h
    rcases (Sym2.eq_iff.mp h) with ⟨ha_eq_b, hv_eq_c⟩ | ⟨ha_eq_c, hv_eq_b⟩
    · exact hba ha_eq_b.symm
    · exact hbv hv_eq_b.symm
  change G.graph.edgeFinset ∆ (quotientSwitchGraph G.graph v b a c).edgeFinset = _
  rw [hfin]
  exact finset_symmDiff_erase_erase_insert_insert
    (E := G.graph.edgeFinset) (e₁ := s(b, v)) (e₂ := s(a, c))
    (f₁ := s(a, v)) (f₂ := s(b, c))
    (SimpleGraph.mem_edgeFinset.mpr (by simpa [SimpleGraph.mem_edgeSet] using hvb.symm))
    (SimpleGraph.mem_edgeFinset.mpr (by simpa [SimpleGraph.mem_edgeSet] using hca.symm))
    (by
      intro h
      have hav_edge : G.graph.Adj a v := by
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using h
      exact hva hav_edge.symm)
    (by
      intro h
      have hbc_edge : G.graph.Adj b c := by
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using h
      exact hcb hbc_edge.symm)
    he₁e₂ he₁f₁ he₁f₂ he₂f₁ he₂f₂ hf₁f₂

/-- The printed Lemma Q candidate set on one side:
`N(a) \ {b}` after deleting `v`, with the vertices also adjacent to `b` removed. -/
noncomputable def residualConnectorCandidates {d : V → ℕ} (G : Realization d)
    (v a b : V) (hav : a ≠ v) (hbv : b ≠ v) : Finset {x : V // x ≠ v} := by
  classical
  letI := G.adjDecidable
  let av : {x : V // x ≠ v} := ⟨a, hav⟩
  let bv : {x : V // x ≠ v} := ⟨b, hbv⟩
  exact ((deleteVertexGraph G.graph v).neighborFinset av).erase bv \
    (((deleteVertexGraph G.graph v).neighborFinset bv).erase av)

/-- Lemma Q quantitative count on one side:
`|N(a) \ {b} \ (N(b) \ {a})| ≥ f(a)-f(b)`. -/
theorem residualConnectorCandidates_card_lower {d : V → ℕ} {S : Finset V}
    {v a b : V} (G : Realization d) (hS : G.neighborFinset v = S)
    (hav : a ≠ v) (hbv : b ≠ v) :
    residualDegree d v S ⟨a, hav⟩ - residualDegree d v S ⟨b, hbv⟩ ≤
      (residualConnectorCandidates G v a b hav hbv).card := by
  classical
  let F := deleteVertexGraph_realizes_residual G v S hS
  let av : {x : V // x ≠ v} := ⟨a, hav⟩
  let bv : {x : V // x ≠ v} := ⟨b, hbv⟩
  let A : Finset {x : V // x ≠ v} := (F.neighborFinset av).erase bv
  let B : Finset {x : V // x ≠ v} := (F.neighborFinset bv).erase av
  have hAcard :
      A.card = residualDegree d v S av - if F.graph.Adj av bv then 1 else 0 := by
    dsimp [A]
    by_cases habF : F.graph.Adj av bv
    · have hbmem : bv ∈ F.neighborFinset av := by
        simpa [Realization.mem_neighborFinset] using habF
      rw [Finset.card_erase_of_mem hbmem]
      change F.degree av - 1 =
        residualDegree d v S av - if F.graph.Adj av bv then 1 else 0
      simp [Realization.degree_eq_apply, habF]
    · have hbnot : bv ∉ F.neighborFinset av := by
        simpa [Realization.mem_neighborFinset] using habF
      rw [Finset.erase_eq_of_notMem hbnot]
      change F.degree av = residualDegree d v S av - if F.graph.Adj av bv then 1 else 0
      simp [Realization.degree_eq_apply, habF]
  have hBcard :
      B.card = residualDegree d v S bv - if F.graph.Adj av bv then 1 else 0 := by
    dsimp [B]
    by_cases habF : F.graph.Adj av bv
    · have hamem : av ∈ F.neighborFinset bv := by
        simpa [Realization.mem_neighborFinset] using habF.symm
      rw [Finset.card_erase_of_mem hamem]
      change F.degree bv - 1 =
        residualDegree d v S bv - if F.graph.Adj av bv then 1 else 0
      simp [Realization.degree_eq_apply, habF]
    · have hanot : av ∉ F.neighborFinset bv := by
        intro hmem
        have hbaF : F.graph.Adj bv av := by
          simpa [Realization.mem_neighborFinset] using hmem
        exact habF hbaF.symm
      rw [Finset.erase_eq_of_notMem hanot]
      change F.degree bv = residualDegree d v S bv - if F.graph.Adj av bv then 1 else 0
      simp [Realization.degree_eq_apply, habF]
  have hres :
      residualDegree d v S av - residualDegree d v S bv ≤ A.card - B.card := by
    rw [hAcard, hBcard]
    by_cases habF : F.graph.Adj av bv
    · have havpos : 0 < residualDegree d v S av := by
        rw [← F.degree_eq av]
        exact habF.degree_pos_left
      have hbvpos : 0 < residualDegree d v S bv := by
        rw [← F.degree_eq bv]
        exact habF.symm.degree_pos_left
      simp [habF]
      omega
    · simp [habF]
  have hsdiff : A.card - B.card ≤ (A \ B).card := Finset.le_card_sdiff B A
  have hC :
      (residualConnectorCandidates G v a b hav hbv).card = (A \ B).card := by
    rfl
  rw [hC]
  exact le_trans hres hsdiff

private theorem residualConnectorCandidate_data {d : V → ℕ} {v a b : V}
    (G : Realization d) {hav : a ≠ v} {hbv : b ≠ v}
    {c : {x : V // x ≠ v}} (hc : c ∈ residualConnectorCandidates G v a b hav hbv) :
    c.val ≠ b ∧ G.graph.Adj c.val a ∧ ¬ G.graph.Adj c.val b := by
  classical
  letI := G.adjDecidable
  let av : {x : V // x ≠ v} := ⟨a, hav⟩
  let bv : {x : V // x ≠ v} := ⟨b, hbv⟩
  have hc' :
      c ∈ ((deleteVertexGraph G.graph v).neighborFinset av).erase bv \
        (((deleteVertexGraph G.graph v).neighborFinset bv).erase av) := by
    simpa [residualConnectorCandidates, av, bv] using hc
  have hcA :
      c ∈ ((deleteVertexGraph G.graph v).neighborFinset av).erase bv :=
    (Finset.mem_sdiff.mp hc').1
  have hcB :
      c ∉ ((deleteVertexGraph G.graph v).neighborFinset bv).erase av :=
    (Finset.mem_sdiff.mp hc').2
  have hc_ne_b_sub : c ≠ bv := (Finset.mem_erase.mp hcA).1
  have hc_adj_a_sub : (deleteVertexGraph G.graph v).Adj av c := by
    simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_erase.mp hcA).2
  have hc_ne_a_sub : c ≠ av := by
    intro h
    rw [h] at hc_adj_a_sub
    exact (deleteVertexGraph G.graph v).irrefl hc_adj_a_sub
  have hc_ne_b : c.val ≠ b := by
    intro h
    exact hc_ne_b_sub (Subtype.ext h)
  have hca : G.graph.Adj c.val a := by
    have hac : G.graph.Adj a c.val := by
      simpa [deleteVertexGraph] using hc_adj_a_sub
    exact hac.symm
  have hcb : ¬ G.graph.Adj c.val b := by
    intro h
    apply hcB
    rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
    exact ⟨hc_ne_a_sub, by simpa [deleteVertexGraph] using h.symm⟩
  exact ⟨hc_ne_b, hca, hcb⟩

/-- Public membership specification for a residual connector candidate. -/
theorem residualConnectorCandidate_spec {d : V → ℕ} {v a b : V}
    (G : Realization d) {hav : a ≠ v} {hbv : b ≠ v}
    {c : {x : V // x ≠ v}} (hc : c ∈ residualConnectorCandidates G v a b hav hbv) :
    c.val ≠ b ∧ G.graph.Adj c.val a ∧ ¬ G.graph.Adj c.val b :=
  residualConnectorCandidate_data G hc

/-- The switch produced by a single Lemma Q connector candidate on the `S` side. -/
noncomputable def sSideConnectorSwitch {d : V → ℕ} {S : Finset V} {v a b : V}
    (G : Realization d) (hS : G.neighborFinset v = S) (hbS : b ∈ S) (haS : a ∉ S)
    (hav : a ≠ v) (hbv : b ≠ v)
    (c : {x : V // x ≠ v}) (hc : c ∈ residualConnectorCandidates G v a b hav hbv) :
    Realization d := by
  classical
  have hba : b ≠ a := fun h => haS (h ▸ hbS)
  have hvb : G.graph.Adj v b := by
    rw [← Realization.mem_neighborFinset, hS]
    exact hbS
  have hva : ¬ G.graph.Adj v a := by
    intro h
    exact haS (by rw [← hS, Realization.mem_neighborFinset]; exact h)
  let hdata := residualConnectorCandidate_data G hc
  exact quotientSwitchRealization G hvb hva hdata.2.1 hdata.2.2 hav hbv hba c.property hdata.1

/-- Exact symmetric difference for the source-side connector constructor. -/
theorem sSideConnectorSwitch_symmDiff {d : V → ℕ} {S : Finset V} {v a b : V}
    (G : Realization d) (hS : G.neighborFinset v = S) (hbS : b ∈ S) (haS : a ∉ S)
    (hav : a ≠ v) (hbv : b ≠ v)
    (c : {x : V // x ≠ v}) (hc : c ∈ residualConnectorCandidates G v a b hav hbv) :
    G.edgeFinset ∆ (sSideConnectorSwitch G hS hbS haS hav hbv c hc).edgeFinset =
      {s(b, v), s(a, c.val), s(a, v), s(b, c.val)} := by
  classical
  have hba : b ≠ a := fun h => haS (h ▸ hbS)
  have hvb : G.graph.Adj v b := by
    rw [← Realization.mem_neighborFinset, hS]
    exact hbS
  have hva : ¬ G.graph.Adj v a := by
    intro h
    exact haS (by rw [← hS, Realization.mem_neighborFinset]; exact h)
  let hdata := residualConnectorCandidate_data G hc
  change G.edgeFinset ∆
      (quotientSwitchRealization G hvb hva hdata.2.1 hdata.2.2 hav hbv hba c.property
        hdata.1).edgeFinset = _
  exact quotientSwitchRealization_symmDiff G hvb hva hdata.2.1 hdata.2.2 hav hbv hba
    c.property hdata.1

theorem sSideConnectorSwitch_spec {d : V → ℕ} {S : Finset V} {v a b : V}
    (G : Realization d) (hS : G.neighborFinset v = S) (hbS : b ∈ S) (haS : a ∉ S)
    (hav : a ≠ v) (hbv : b ≠ v)
    (c : {x : V // x ≠ v}) (hc : c ∈ residualConnectorCandidates G v a b hav hbv) :
    (sSideConnectorSwitch G hS hbS haS hav hbv c hc).neighborFinset v =
        insert a (S.erase b) ∧
      twoSwitchAdjacent G (sSideConnectorSwitch G hS hbS haS hav hbv c hc) := by
  classical
  have hba : b ≠ a := fun h => haS (h ▸ hbS)
  have hvb : G.graph.Adj v b := by
    rw [← Realization.mem_neighborFinset, hS]
    exact hbS
  have hva : ¬ G.graph.Adj v a := by
    intro h
    exact haS (by rw [← hS, Realization.mem_neighborFinset]; exact h)
  let hdata := residualConnectorCandidate_data G hc
  constructor
  · change
      (quotientSwitchRealization G hvb hva hdata.2.1 hdata.2.2 hav hbv hba c.property
          hdata.1).neighborFinset v = insert a (S.erase b)
    exact quotientSwitch_neighborFinset_v G hS hvb hva hdata.2.1 hdata.2.2 hav hbv hba
      c.property hdata.1
  · change
      twoSwitchAdjacent G
        (quotientSwitchRealization G hvb hva hdata.2.1 hdata.2.2 hav hbv hba c.property
          hdata.1)
    exact quotientSwitch_twoSwitchAdjacent G hvb hva hdata.2.1 hdata.2.2 hav hbv hba
      c.property hdata.1

private theorem sSideConnectorSwitch_adj_created {d : V → ℕ} {S : Finset V}
    {v a b : V} (G : Realization d) (hS : G.neighborFinset v = S)
    (hbS : b ∈ S) (haS : a ∉ S) (hav : a ≠ v) (hbv : b ≠ v)
    (c : {x : V // x ≠ v}) (hc : c ∈ residualConnectorCandidates G v a b hav hbv) :
    (sSideConnectorSwitch G hS hbS haS hav hbv c hc).graph.Adj c.val b := by
  classical
  have hdata := residualConnectorCandidate_data G hc
  change (quotientSwitchGraph G.graph v b a c.val).Adj c.val b
  simp [quotientSwitchGraph, transferGraph, hdata.1]

private theorem sSideConnectorSwitch_not_adj_created_for_other {d : V → ℕ}
    {S : Finset V} {v a b : V} (G : Realization d) (hS : G.neighborFinset v = S)
    (hbS : b ∈ S) (haS : a ∉ S) (hav : a ≠ v) (hbv : b ≠ v)
    (c₁ c₂ : {x : V // x ≠ v})
    (hc₁ : c₁ ∈ residualConnectorCandidates G v a b hav hbv)
    (hc₂ : c₂ ∈ residualConnectorCandidates G v a b hav hbv) (hne : c₁ ≠ c₂) :
    ¬ (sSideConnectorSwitch G hS hbS haS hav hbv c₂ hc₂).graph.Adj c₁.val b := by
  classical
  have hba : b ≠ a := fun h => haS (h ▸ hbS)
  have hdata₁ := residualConnectorCandidate_data G hc₁
  have hdata₂ := residualConnectorCandidate_data G hc₂
  have hc₁_ne_a : c₁.val ≠ a := hdata₁.2.1.ne
  have hc₁_ne_c₂ : c₁.val ≠ c₂.val := by
    intro h
    exact hne (Subtype.ext h)
  change ¬ (quotientSwitchGraph G.graph v b a c₂.val).Adj c₁.val b
  simp [quotientSwitchGraph, transferGraph, hdata₁.2.2, hdata₁.1, hdata₂.1,
    hc₁_ne_a, c₁.property, hbv, hba, hc₁_ne_c₂]

/-- Distinct Lemma Q candidates produce distinct switched realizations. -/
theorem sSideConnectorSwitch_injective {d : V → ℕ} {S : Finset V} {v a b : V}
    (G : Realization d) (hS : G.neighborFinset v = S) (hbS : b ∈ S) (haS : a ∉ S)
    (hav : a ≠ v) (hbv : b ≠ v) :
    Function.Injective
      (fun c : {c : {x : V // x ≠ v} //
          c ∈ residualConnectorCandidates G v a b hav hbv} =>
        sSideConnectorSwitch G hS hbS haS hav hbv c.1 c.2) := by
  intro c₁ c₂ hEq
  by_contra hne
  have hne_val : c₁.1 ≠ c₂.1 := by
    intro h
    exact hne (Subtype.ext h)
  have hadj :
      (sSideConnectorSwitch G hS hbS haS hav hbv c₁.1 c₁.2).graph.Adj c₁.1.val b :=
    sSideConnectorSwitch_adj_created G hS hbS haS hav hbv c₁.1 c₁.2
  have hnot :
      ¬ (sSideConnectorSwitch G hS hbS haS hav hbv c₂.1 c₂.2).graph.Adj c₁.1.val b :=
    sSideConnectorSwitch_not_adj_created_for_other G hS hbS haS hav hbv
      c₁.1 c₂.1 c₁.2 c₂.2 hne_val
  have hgraph := congrArg Realization.graph hEq
  exact hnot (by simpa [hgraph] using hadj)

/-- The connector targets reached from a fixed `S`-side realization by Lemma Q switches. -/
noncomputable def sSideConnectorTargets {d : V → ℕ} {S : Finset V} {v a b : V}
    (G : Realization d) (hS : G.neighborFinset v = S) (hbS : b ∈ S) (haS : a ∉ S)
    (hav : a ≠ v) (hbv : b ≠ v) : Finset (Realization d) := by
  classical
  exact (residualConnectorCandidates G v a b hav hbv).attach.image
    (fun c => sSideConnectorSwitch G hS hbS haS hav hbv c.1 c.2)

theorem mem_sSideConnectorTargets_spec {d : V → ℕ} {S : Finset V} {v a b : V}
    (G : Realization d) (hS : G.neighborFinset v = S) (hbS : b ∈ S) (haS : a ∉ S)
    (hav : a ≠ v) (hbv : b ≠ v) {H : Realization d}
    (hH : H ∈ sSideConnectorTargets G hS hbS haS hav hbv) :
    H.neighborFinset v = insert a (S.erase b) ∧ twoSwitchAdjacent G H := by
  classical
  rw [sSideConnectorTargets, Finset.mem_image] at hH
  rcases hH with ⟨c, _hc_mem, rfl⟩
  exact sSideConnectorSwitch_spec G hS hbS haS hav hbv c.1 c.2

/-- Lemma Q quantitative addendum, `S` side:
every fixed `S`-fiber realization has connector degree at least `f(a)-f(b)`. -/
theorem sSide_connector_degree_lower_bound {d : V → ℕ} {S : Finset V} {v a b : V}
    (G : Realization d) (hS : G.neighborFinset v = S) (hbS : b ∈ S) (haS : a ∉ S)
    (hav : a ≠ v) (hbv : b ≠ v) :
    residualDegree d v S ⟨a, hav⟩ - residualDegree d v S ⟨b, hbv⟩ ≤
      (sSideConnectorTargets G hS hbS haS hav hbv).card := by
  classical
  have hcard :
      (sSideConnectorTargets G hS hbS haS hav hbv).card =
        (residualConnectorCandidates G v a b hav hbv).card := by
    rw [sSideConnectorTargets, Finset.card_image_of_injective]
    · simp
    · exact sSideConnectorSwitch_injective G hS hbS haS hav hbv
  rw [hcard]
  exact residualConnectorCandidates_card_lower G hS hav hbv

omit [Fintype V] in
private theorem insert_erase_swap_back {S : Finset V} {a b : V}
    (hbS : b ∈ S) (haS : a ∉ S) :
    insert b ((insert a (S.erase b)).erase a) = S := by
  ext x
  have hab : a ≠ b := fun h => haS (h ▸ hbS)
  by_cases hxa : x = a
  · subst x
    simp [haS, hab]
  · by_cases hxb : x = b
    · subst x
      simp [hbS, hab.symm]
    · simp [hxa, hxb]

/-- Connector targets reached from a fixed `S' = S - b + a` realization back to `S`. -/
noncomputable def sPrimeSideConnectorTargets {d : V → ℕ} {S : Finset V} {v a b : V}
    (H : Realization d) (hH : H.neighborFinset v = insert a (S.erase b))
    (hbS : b ∈ S) (haS : a ∉ S) (hav : a ≠ v) (hbv : b ≠ v) :
    Finset (Realization d) := by
  classical
  have hab : a ≠ b := fun h => haS (h ▸ hbS)
  have hbS' : a ∈ insert a (S.erase b) := Finset.mem_insert_self _ _
  have haS' : b ∉ insert a (S.erase b) := by
    simp [hab.symm]
  exact sSideConnectorTargets H hH hbS' haS' hbv hav

theorem mem_sPrimeSideConnectorTargets_spec {d : V → ℕ} {S : Finset V} {v a b : V}
    (H : Realization d) (hH : H.neighborFinset v = insert a (S.erase b))
    (hbS : b ∈ S) (haS : a ∉ S) (hav : a ≠ v) (hbv : b ≠ v)
    {G : Realization d} (hG : G ∈ sPrimeSideConnectorTargets H hH hbS haS hav hbv) :
    G.neighborFinset v = S ∧ twoSwitchAdjacent G H := by
  classical
  have hab : a ≠ b := fun h => haS (h ▸ hbS)
  have hbS' : a ∈ insert a (S.erase b) := Finset.mem_insert_self _ _
  have haS' : b ∉ insert a (S.erase b) := by
    simp [hab.symm]
  have hspec :=
    mem_sSideConnectorTargets_spec H hH hbS' haS' hbv hav
      (H := G) (by simpa [sPrimeSideConnectorTargets, hab, hbS', haS'] using hG)
  rcases hspec with ⟨hN, hadj⟩
  rw [insert_erase_swap_back hbS haS] at hN
  exact ⟨hN, twoSwitchAdjacent_symm hadj⟩

/-- Lemma Q quantitative addendum, `S'` side:
every fixed `S'`-fiber realization has connector degree at least `f(b)+2-f(a)`,
the natural-number positive part of the printed `f(b)-f(a)+2`. -/
theorem sPrimeSide_connector_degree_lower_bound {d : V → ℕ} {S : Finset V} {v a b : V}
    (hSreal : HasRealizationWithNeighborSet d v S)
    (H : Realization d) (hH : H.neighborFinset v = insert a (S.erase b))
    (hbS : b ∈ S) (haS : a ∉ S) (hav : a ≠ v) (hbv : b ≠ v) :
    residualDegree d v S ⟨b, hbv⟩ + 2 - residualDegree d v S ⟨a, hav⟩ ≤
      (sPrimeSideConnectorTargets H hH hbS haS hav hbv).card := by
  classical
  have hab : a ≠ b := fun h => haS (h ▸ hbS)
  have hbS' : a ∈ insert a (S.erase b) := Finset.mem_insert_self _ _
  have haS' : b ∉ insert a (S.erase b) := by
    simp [hab.symm]
  have ha_pos : 0 < d a := by
    have hva : H.graph.Adj v a := by
      rw [← Realization.mem_neighborFinset, hH]
      exact Finset.mem_insert_self _ _
    rw [← H.degree_eq a]
    exact hva.symm.degree_pos_left
  have hb_pos : 0 < d b := by
    rcases hSreal with ⟨G, hG⟩
    have hvb : G.graph.Adj v b := by
      rw [← Realization.mem_neighborFinset, hG]
      exact hbS
    rw [← G.degree_eq b]
    exact hvb.symm.degree_pos_left
  have hconvert :
      residualDegree d v S ⟨b, hbv⟩ + 2 - residualDegree d v S ⟨a, hav⟩ =
        residualDegree d v (insert a (S.erase b)) ⟨b, hbv⟩ -
          residualDegree d v (insert a (S.erase b)) ⟨a, hav⟩ := by
    dsimp [residualDegree]
    simp [hbS, haS, hab, hab.symm]
    omega
  rw [hconvert]
  simpa [sPrimeSideConnectorTargets, hab, hbS', haS'] using
    sSide_connector_degree_lower_bound H hH hbS' haS' hbv hav

private theorem exists_residual_witness {d : V → ℕ} {S : Finset V} {v a b : V}
    (G : Realization d) (hS : G.neighborFinset v = S)
    (hav : a ≠ v) (hbv : b ≠ v)
    (hgt :
      residualDegree d v S ⟨a, hav⟩ > residualDegree d v S ⟨b, hbv⟩) :
    ∃ c : V, c ≠ v ∧ c ≠ b ∧ G.graph.Adj c a ∧ ¬ G.graph.Adj c b := by
  classical
  let F := deleteVertexGraph_realizes_residual G v S hS
  let av : {x : V // x ≠ v} := ⟨a, hav⟩
  let bv : {x : V // x ≠ v} := ⟨b, hbv⟩
  let A : Finset {x : V // x ≠ v} := (F.neighborFinset av).erase bv
  let B : Finset {x : V // x ≠ v} := (F.neighborFinset bv).erase av
  have hAcard :
      A.card = residualDegree d v S av - if F.graph.Adj av bv then 1 else 0 := by
    dsimp [A]
    by_cases habF : F.graph.Adj av bv
    · have hbmem : bv ∈ F.neighborFinset av := by
        simpa [Realization.mem_neighborFinset] using habF
      rw [Finset.card_erase_of_mem hbmem]
      change F.degree av - 1 =
        residualDegree d v S av - if F.graph.Adj av bv then 1 else 0
      simp [Realization.degree_eq_apply, habF]
    · have hbnot : bv ∉ F.neighborFinset av := by
        simpa [Realization.mem_neighborFinset] using habF
      rw [Finset.erase_eq_of_notMem hbnot]
      change F.degree av = residualDegree d v S av - if F.graph.Adj av bv then 1 else 0
      simp [Realization.degree_eq_apply, habF]
  have hBcard :
      B.card = residualDegree d v S bv - if F.graph.Adj av bv then 1 else 0 := by
    dsimp [B]
    by_cases habF : F.graph.Adj av bv
    · have hamem : av ∈ F.neighborFinset bv := by
        simpa [Realization.mem_neighborFinset] using habF.symm
      rw [Finset.card_erase_of_mem hamem]
      change F.degree bv - 1 =
        residualDegree d v S bv - if F.graph.Adj av bv then 1 else 0
      simp [Realization.degree_eq_apply, habF]
    · have hanot : av ∉ F.neighborFinset bv := by
        intro hmem
        have hbaF : F.graph.Adj bv av := by
          simpa [Realization.mem_neighborFinset] using hmem
        exact habF hbaF.symm
      rw [Finset.erase_eq_of_notMem hanot]
      change F.degree bv = residualDegree d v S bv - if F.graph.Adj av bv then 1 else 0
      simp [Realization.degree_eq_apply, habF]
  have hAgtB : B.card < A.card := by
    have hgt' : residualDegree d v S bv < residualDegree d v S av := by
      simpa [av, bv] using hgt
    rw [hAcard, hBcard]
    by_cases habF : F.graph.Adj av bv
    · have havpos : 0 < residualDegree d v S av := by
        rw [← F.degree_eq av]
        exact habF.degree_pos_left
      have hbvpos : 0 < residualDegree d v S bv := by
        rw [← F.degree_eq bv]
        exact habF.symm.degree_pos_left
      simp [habF]
      omega
    · simp [habF]
      omega
  have hnsubset : ¬ A ⊆ B := fun hsub => by
    exact (not_lt_of_ge (Finset.card_le_card hsub)) hAgtB
  obtain ⟨c, hcA, hcB⟩ := Finset.not_subset.mp hnsubset
  have hc_ne_b : c ≠ bv := (Finset.mem_erase.mp hcA).1
  have hc_adj_a_sub : F.graph.Adj av c := by
    simpa [Realization.mem_neighborFinset] using (Finset.mem_erase.mp hcA).2
  have hc_ne_a : c ≠ av := by
    intro h
    subst h
    exact F.graph.irrefl hc_adj_a_sub
  have hc_not_adj_b_sub : ¬ F.graph.Adj bv c := by
    intro hb_adj
    apply hcB
    rw [Finset.mem_erase, Realization.mem_neighborFinset]
    exact ⟨hc_ne_a, hb_adj⟩
  refine ⟨c.val, c.property, ?_, ?_, ?_⟩
  · intro h
    exact hc_ne_b (Subtype.ext h)
  · have hac : G.graph.Adj a c.val := by
      simpa [F, deleteVertexGraph_realizes_residual, deleteVertexGraph] using hc_adj_a_sub
    exact hac.symm
  · intro hcb
    apply hc_not_adj_b_sub
    change (deleteVertexGraph G.graph v).Adj bv c
    simpa [deleteVertexGraph] using hcb.symm

private theorem forward_quotient_switch {d : V → ℕ} {S : Finset V} {v a b : V}
    (G : Realization d) (hS : G.neighborFinset v = S) (hbS : b ∈ S) (haS : a ∉ S)
    (hav : a ≠ v)
    (hgt : residualDegree d v S ⟨a, hav⟩ >
      residualDegree d v S ⟨b, by
        intro hbv
        subst b
        have hv_mem : v ∈ G.neighborFinset v := by
          rw [hS]
          exact hbS
        exact (SimpleGraph.notMem_neighborFinset_self G.graph v) hv_mem⟩) :
    ∃ H : Realization d,
      H.neighborFinset v = insert a (S.erase b) ∧ twoSwitchAdjacent G H := by
  classical
  have hbv : b ≠ v := by
    intro hbv
    subst b
    have hv_mem : v ∈ G.neighborFinset v := by
      rw [hS]
      exact hbS
    exact (SimpleGraph.notMem_neighborFinset_self G.graph v) hv_mem
  have hba : b ≠ a := fun h => haS (h ▸ hbS)
  have hvb : G.graph.Adj v b := by
    rw [← Realization.mem_neighborFinset, hS]
    exact hbS
  have hva : ¬ G.graph.Adj v a := by
    intro h
    exact haS (by rw [← hS, Realization.mem_neighborFinset]; exact h)
  obtain ⟨c, hcv, hcb_ne, hca, hcb⟩ :=
    exists_residual_witness G hS hav hbv hgt
  let H := quotientSwitchRealization G hvb hva hca hcb hav hbv hba hcv hcb_ne
  refine ⟨H, ?_, ?_⟩
  · exact quotientSwitch_neighborFinset_v G hS hvb hva hca hcb hav hbv hba hcv hcb_ne
  · exact quotientSwitch_twoSwitchAdjacent G hvb hva hca hcb hav hbv hba hcv hcb_ne

private theorem ne_of_insert_erase_realizable {d : V → ℕ} {S : Finset V} {v a b : V}
    (hS' : HasRealizationWithNeighborSet d v (insert a (S.erase b))) : a ≠ v := by
  intro ha
  subst a
  rcases hS' with ⟨G, hG⟩
  have hv_mem : v ∈ G.neighborFinset v := by
    rw [hG]
    exact Finset.mem_insert_self _ _
  exact (SimpleGraph.notMem_neighborFinset_self G.graph v) hv_mem

/-- Lemma Q, quotient adjacency for realization fibers.

If `b ∈ S`, `a ∉ S`, and both `S` and `S - b + a` occur as neighbor sets of `v`,
then some realization in the `S` fiber is 2-switch adjacent to some realization in the
swapped fiber. -/
theorem quotient_adjacent {d : V → ℕ} {S : Finset V} {v a b : V}
    (hbS : b ∈ S) (haS : a ∉ S)
    (hS : HasRealizationWithNeighborSet d v S)
    (hS' : HasRealizationWithNeighborSet d v (insert a (S.erase b))) :
    ∃ G H : Realization d,
      G.neighborFinset v = S ∧
        H.neighborFinset v = insert a (S.erase b) ∧
          twoSwitchAdjacent G H := by
  classical
  have hav : a ≠ v := ne_of_insert_erase_realizable hS'
  have hbv_from (G : Realization d) (hG : G.neighborFinset v = S) : b ≠ v := by
    intro hbv
    subst b
    have hv_mem : v ∈ G.neighborFinset v := by
      rw [hG]
      exact hbS
    exact (SimpleGraph.notMem_neighborFinset_self G.graph v) hv_mem
  rcases hS with ⟨G, hG⟩
  let bv : {x : V // x ≠ v} := ⟨b, hbv_from G hG⟩
  let av : {x : V // x ≠ v} := ⟨a, hav⟩
  by_cases hgt : residualDegree d v S av > residualDegree d v S bv
  · obtain ⟨H, hH, hadj⟩ := forward_quotient_switch G hG hbS haS hav hgt
    exact ⟨G, H, hG, hH, hadj⟩
  · rcases hS' with ⟨H, hH⟩
    have hab : a ≠ b := fun h => haS (h ▸ hbS)
    have hbS' : a ∈ insert a (S.erase b) := Finset.mem_insert_self _ _
    have haS' : b ∉ insert a (S.erase b) := by simp [hab.symm]
    have hbv : b ≠ v := by
      intro hbv
      subst b
      have hv_mem : v ∈ G.neighborFinset v := by
        rw [hG]
        exact hbS
      exact (SimpleGraph.notMem_neighborFinset_self G.graph v) hv_mem
    let av' : {x : V // x ≠ v} := ⟨a, hav⟩
    let bv' : {x : V // x ≠ v} := ⟨b, hbv⟩
    have hle : residualDegree d v S av ≤ residualDegree d v S bv := le_of_not_gt hgt
    have hdb_pos : 0 < d b := by
      have hvb : G.graph.Adj v b := by
        rw [← Realization.mem_neighborFinset, hG]
        exact hbS
      rw [← G.degree_eq b]
      exact hvb.symm.degree_pos_left
    have hmirror :
        residualDegree d v (insert a (S.erase b)) bv' >
          residualDegree d v (insert a (S.erase b)) av' := by
      dsimp [residualDegree, av, bv, av', bv'] at hle ⊢
      simp [haS, hbS, hab, hab.symm] at hle ⊢
      omega
    obtain ⟨G', hG', hadjHG'⟩ :=
      forward_quotient_switch H hH hbS' haS' hbv hmirror
    have htarget : insert b ((insert a (S.erase b)).erase a) = S := by
      ext x
      by_cases hxa : x = a
      · subst x
        simp [haS, hab]
      · by_cases hxb : x = b
        · subst x
          simp [hbS, hab.symm]
        · simp [hxa, hxb]
    rw [htarget] at hG'
    exact ⟨G', H, hG', hH, twoSwitchAdjacent_symm hadjHG'⟩

#print axioms sSide_connector_degree_lower_bound
#print axioms sPrimeSide_connector_degree_lower_bound
#print axioms sSideConnectorSwitch_injective
#print axioms quotientSwitchRealization_symmDiff
#print axioms residualConnectorCandidate_spec
#print axioms sSideConnectorSwitch_symmDiff

end Brualdi.RealizationGraph
