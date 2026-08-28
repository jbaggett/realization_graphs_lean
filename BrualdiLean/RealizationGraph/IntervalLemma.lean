/-
Copyright (c) 2026 Jeffrey S. Baggett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey S. Baggett
-/
import BrualdiLean.RealizationGraph.Transfer
import BrualdiLean.RealizationGraph.LemmaRCore
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.nativeDecide false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false

namespace Brualdi.RealizationGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The deleted-vertex type `V \ {v}`. -/
abbrev Deleted (v : V) := {x : V // x ≠ v}

/-- Near-regularity with values exactly among `k` and `k+1`. -/
def NearRegular (d : V → ℕ) (k : ℕ) : Prop :=
  ∀ x : V, d x = k ∨ d x = k + 1

/-- Residual degree function on `V \ {v}` after prescribing the neighbor set `S`. -/
def intervalResidual (d : V → ℕ) {v : V} (S : Finset (Deleted v)) (u : Deleted v) :
    ℕ :=
  d u.val - if u ∈ S then 1 else 0

/-- The high vertices in `V \ {v}`. -/
def highSet (d : V → ℕ) (k : ℕ) (v : V) : Finset (Deleted v) :=
  Finset.univ.filter fun u : Deleted v => d u.val = k + 1

/-- The low vertices in `V \ {v}`. -/
def lowSet (d : V → ℕ) (k : ℕ) (v : V) : Finset (Deleted v) :=
  Finset.univ.filter fun u : Deleted v => d u.val = k

/-- The number of prescribed neighbors lying in the high class. -/
def highCount (d : V → ℕ) (k : ℕ) {v : V} (S : Finset (Deleted v)) : ℕ :=
  (S.filter fun u : Deleted v => d u.val = k + 1).card

/-- The number of prescribed neighbors lying in the low class. -/
def lowCount (d : V → ℕ) (k : ℕ) {v : V} (S : Finset (Deleted v)) : ℕ :=
  (S.filter fun u : Deleted v => d u.val = k).card

/-- The feasible interval for `h`, written as natural-number bounds:
`max(0, r-L') <= h <= min(r,H')` is `r-L' <= h`, `h <= r`, `h <= H'`. -/
def FeasibleH (d : V → ℕ) (k : ℕ) (v : V) (r h : ℕ) : Prop :=
  r - (lowSet d k v).card ≤ h ∧ h ≤ r ∧ h ≤ (highSet d k v).card

/-- The admissible `h`-layer, encoded by a residual degree function on `V \ {v}`. -/
def AdmissibleH (d : V → ℕ) (k : ℕ) (v : V) (r h : ℕ) : Prop :=
  ∃ S : Finset (Deleted v),
    S.card = r ∧ highCount d k S = h ∧ Graphical (intervalResidual d S)

@[simp]
theorem mem_highSet {d : V → ℕ} {k : ℕ} {v : V} {u : Deleted v} :
    u ∈ highSet d k v ↔ d u.val = k + 1 := by
  simp [highSet]

@[simp]
theorem mem_lowSet {d : V → ℕ} {k : ℕ} {v : V} {u : Deleted v} :
    u ∈ lowSet d k v ↔ d u.val = k := by
  simp [lowSet]

theorem high_ne_low {d : V → ℕ} {k : ℕ} {v : V} {u : Deleted v}
    (hhi : u ∈ highSet d k v) (hlo : u ∈ lowSet d k v) : False := by
  have h1 : d u.val = k + 1 := by simpa using hhi
  have h0 : d u.val = k := by simpa using hlo
  omega

theorem card_eq_highCount_add_lowCount {d : V → ℕ} {k : ℕ} {v : V}
    (hnear : NearRegular d k) (S : Finset (Deleted v)) :
    S.card = highCount d k S + lowCount d k S := by
  classical
  let SH : Finset (Deleted v) := S.filter fun u : Deleted v => d u.val = k + 1
  let SL : Finset (Deleted v) := S.filter fun u : Deleted v => d u.val = k
  have hdis : Disjoint SH SL := by
    rw [Finset.disjoint_left]
    intro u huH huL
    simp [SH] at huH
    simp [SL] at huL
    omega
  have hunion : SH ∪ SL = S := by
    ext u
    constructor
    · intro hu
      rcases Finset.mem_union.mp hu with huH | huL
      · have huH' : u ∈ S ∧ d u.val = k + 1 := by simpa [SH] using huH
        exact huH'.1
      · have huL' : u ∈ S ∧ d u.val = k := by simpa [SL] using huL
        exact huL'.1
    · intro huS
      rcases hnear u.val with hlow | hhigh
      · exact Finset.mem_union.mpr (Or.inr (by simp [SL, huS, hlow]))
      · exact Finset.mem_union.mpr (Or.inl (by simp [SH, huS, hhigh]))
  calc
    S.card = (SH ∪ SL).card := by rw [hunion]
    _ = SH.card + SL.card := by rw [Finset.card_union_of_disjoint hdis]
    _ = highCount d k S + lowCount d k S := by rfl

/-- Any concrete layer representative lies in the arithmetic feasible interval. -/
theorem feasible_of_layer {d : V → ℕ} {k : ℕ} {v : V} {r h : ℕ}
    (hnear : NearRegular d k) {S : Finset (Deleted v)}
    (hcard : S.card = r) (hh : highCount d k S = h) :
    FeasibleH d k v r h := by
  classical
  have h_high_le_r : h ≤ r := by
    rw [← hh, ← hcard]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have h_high_le_total : h ≤ (highSet d k v).card := by
    rw [← hh]
    exact Finset.card_le_card (by
      intro u hu
      exact (by
        rw [mem_highSet]
        exact (Finset.mem_filter.mp hu).2))
  have hlow_le_total :
      lowCount d k S ≤ (lowSet d k v).card := by
    exact Finset.card_le_card (by
      intro u hu
      rw [mem_lowSet]
      exact (Finset.mem_filter.mp hu).2)
  have hsplit : r = h + lowCount d k S := by
    rw [← hcard, card_eq_highCount_add_lowCount hnear S, hh]
  constructor
  · omega
  constructor
  · exact h_high_le_r
  · exact h_high_le_total

/-- Relabeling core for interval residuals.  This is the partition-symmetry mechanism:
if a permutation of `V \ {v}` preserves the ambient degree function and carries `S₂` to `S₁`,
then residual graphicality is invariant. -/
theorem graphical_intervalResidual_congr {d : V → ℕ} {v : V}
    {S₁ S₂ : Finset (Deleted v)}
    (e : Deleted v ≃ Deleted v)
    (hS : ∀ u : Deleted v, u ∈ S₂ ↔ e u ∈ S₁)
    (hd : ∀ u : Deleted v, d (e u).val = d u.val) :
    Graphical (intervalResidual d S₁) → Graphical (intervalResidual d S₂) := by
  intro hG
  rcases hG with ⟨G, hGdec, hdeg⟩
  letI := hGdec
  refine ⟨G.comap e, inferInstance, ?_⟩
  intro u
  rw [comap_equiv_degree]
  change G.degree (e u) = intervalResidual d S₂ u
  rw [hdeg]
  unfold intervalResidual
  rw [hd u]
  by_cases hu : u ∈ S₂
  · rw [if_pos hu, if_pos ((hS u).mp hu)]
  · rw [if_neg hu, if_neg (fun h => hu ((hS u).mpr h))]

/-- IL-A, in its explicit relabeling form. -/
theorem interval_partition_symmetry {d : V → ℕ} {v : V}
    {S₁ S₂ : Finset (Deleted v)}
    (e : Deleted v ≃ Deleted v)
    (hS : ∀ u : Deleted v, u ∈ S₂ ↔ e u ∈ S₁)
    (hd : ∀ u : Deleted v, d (e u).val = d u.val) :
    Graphical (intervalResidual d S₁) ↔ Graphical (intervalResidual d S₂) := by
  constructor
  · exact graphical_intervalResidual_congr e hS hd
  · have hSsymm :
        ∀ u : Deleted v, u ∈ S₁ ↔ e.symm u ∈ S₂ := by
      intro u
      have h := hS (e.symm u)
      simpa using h.symm
    have hdsymm :
        ∀ u : Deleted v, d (e.symm u).val = d u.val := by
      intro u
      have h := hd (e.symm u)
      simpa using h.symm
    exact graphical_intervalResidual_congr e.symm hSsymm hdsymm

theorem exists_high_not_mem_of_succ_feasible {d : V → ℕ} {k : ℕ} {v : V}
    {r h : ℕ} {S : Finset (Deleted v)}
    (hh : highCount d k S = h)
    (hfeas : FeasibleH d k v r (h + 1)) :
    ∃ x : Deleted v, x ∈ highSet d k v ∧ x ∉ S := by
  classical
  have hlt : h < (highSet d k v).card := by
    have hsucc_le : h + 1 ≤ (highSet d k v).card := hfeas.2.2
    omega
  by_contra hnone
  have hsub : highSet d k v ⊆ S := by
    intro x hx
    by_contra hxS
    exact hnone ⟨x, hx, hxS⟩
  have heq : S.filter (fun u : Deleted v => d u.val = k + 1) = highSet d k v := by
    ext u
    constructor
    · intro hu
      rw [mem_highSet]
      exact (Finset.mem_filter.mp hu).2
    · intro hu
      exact Finset.mem_filter.mpr ⟨hsub hu, by simpa using hu⟩
  have hcardeq : h = (highSet d k v).card := by
    rw [← hh]
    unfold highCount
    rw [heq]
  omega

theorem exists_low_mem_of_card_highCount_lt {d : V → ℕ} {k : ℕ} {v : V}
    {r h : ℕ} {S : Finset (Deleted v)}
    (hnear : NearRegular d k) (hcard : S.card = r) (hh : highCount d k S = h)
    (hlt : h < r) :
    ∃ y : Deleted v, y ∈ S ∧ y ∈ lowSet d k v := by
  classical
  by_contra hnone
  have hfilter_eq : S.filter (fun u : Deleted v => d u.val = k + 1) = S := by
    ext u
    constructor
    · exact fun hu => (Finset.mem_filter.mp hu).1
    · intro huS
      have hnot_low : d u.val ≠ k := by
        intro hlow
        exact hnone ⟨u, huS, by simp [lowSet, hlow]⟩
      rcases hnear u.val with hlow | hhigh
      · exact False.elim (hnot_low hlow)
      · exact Finset.mem_filter.mpr ⟨huS, hhigh⟩
  have hcardeq : h = r := by
    rw [← hh]
    unfold highCount
    rw [hfilter_eq, hcard]
  omega

theorem intervalResidual_eq_update_exchange {d : V → ℕ} {k : ℕ} {v : V}
    {S : Finset (Deleted v)} {x y : Deleted v}
    (hk : 0 < k)
    (hxS : x ∉ S) (hyS : y ∈ S)
    (hxhi : x ∈ highSet d k v) (hylow : y ∈ lowSet d k v) :
    intervalResidual d (insert x (S.erase y)) =
      Function.update
        (Function.update (intervalResidual d S) x (intervalResidual d S x - 1))
        y (intervalResidual d S y + 1) := by
  classical
  funext u
  unfold intervalResidual
  have hxdeg : d x.val = k + 1 := by simpa using hxhi
  have hydeg : d y.val = k := by simpa using hylow
  have hxy : x ≠ y := by
    intro h
    subst y
    omega
  by_cases hux : u = x
  · subst u
    simp [Function.update, hxS, hxy, hxdeg]
  · by_cases huy : u = y
    · subst u
      simp [Function.update, hyS, hxy.symm, hydeg]
      omega
    · have hmem_new : u ∈ insert x (S.erase y) ↔ u ∈ S := by
        simp [hux, huy]
      simp [Function.update, hux, huy, hmem_new]

/-- Exchanging a selected low vertex for an unselected high vertex raises `h` by one. -/
theorem highCount_exchange {d : V → ℕ} {k : ℕ} {v : V}
    {S : Finset (Deleted v)} {x y : Deleted v} {h : ℕ}
    (hh : highCount d k S = h)
    (hxS : x ∉ S) (hyS : y ∈ S)
    (hxhi : x ∈ highSet d k v) (hylow : y ∈ lowSet d k v) :
    highCount d k (insert x (S.erase y)) = h + 1 := by
  classical
  have hxdeg : d x.val = k + 1 := by simpa using hxhi
  have hydeg : d y.val = k := by simpa using hylow
  have hxy : x ≠ y := by
    intro hxy
    subst y
    omega
  have hy_not_high : d y.val ≠ k + 1 := by omega
  have hfilter :
      (insert x (S.erase y)).filter (fun u : Deleted v => d u.val = k + 1) =
        insert x (S.filter fun u : Deleted v => d u.val = k + 1) := by
    ext u
    by_cases hux : u = x
    · subst u
      simp [hxdeg]
    · by_cases huy : u = y
      · subst u
        simp [hxS, hy_not_high, hxy.symm]
      · simp [hux, huy]
  unfold highCount
  rw [hfilter, Finset.card_insert_of_notMem]
  · rw [show (S.filter fun u : Deleted v => d u.val = k + 1).card = h by
        simpa [highCount] using hh]
  · intro hxmem
    exact hxS (Finset.mem_filter.mp hxmem).1

theorem card_exchange {v : V} {S : Finset (Deleted v)} {x y : Deleted v} {r : ℕ}
    (hcard : S.card = r) (hxS : x ∉ S) (hyS : y ∈ S) :
    (insert x (S.erase y)).card = r := by
  classical
  have hx_not_erase : x ∉ S.erase y := by
    intro hx
    exact hxS (Finset.mem_of_mem_erase hx)
  have hrpos : 0 < r := by
    rw [← hcard]
    exact Finset.card_pos.mpr ⟨y, hyS⟩
  rw [Finset.card_insert_of_notMem hx_not_erase, Finset.card_erase_of_mem hyS, hcard]
  omega

/-- IL-B for a concrete representative: if the next `h` is feasible, replace one low
selected vertex by one high unselected vertex and apply `down_transfer`. -/
theorem interval_step_up_representative {d : V → ℕ} {k : ℕ} {v : V} {r h : ℕ}
    (hnear : NearRegular d k) (hk : 0 < k)
    {S : Finset (Deleted v)}
    (hcard : S.card = r) (hh : highCount d k S = h)
    (hG : Graphical (intervalResidual d S))
    (hfeasSucc : FeasibleH d k v r (h + 1)) :
    ∃ T : Finset (Deleted v),
      T.card = r ∧ highCount d k T = h + 1 ∧ Graphical (intervalResidual d T) := by
  classical
  obtain ⟨x, hxhi, hxS⟩ := exists_high_not_mem_of_succ_feasible (d := d) (k := k)
    (v := v) (r := r) (h := h) (S := S) hh hfeasSucc
  have hlt_hr : h < r := by
    have hsucc_le : h + 1 ≤ r := hfeasSucc.2.1
    omega
  obtain ⟨y, hyS, hylow⟩ := exists_low_mem_of_card_highCount_lt (d := d) (k := k)
    (v := v) (r := r) (h := h) (S := S) hnear hcard hh hlt_hr
  let T : Finset (Deleted v) := insert x (S.erase y)
  have hxdeg : d x.val = k + 1 := by simpa using hxhi
  have hydeg : d y.val = k := by simpa using hylow
  have hx_res : intervalResidual d S x = k + 1 := by
    unfold intervalResidual
    simp [hxS, hxdeg]
  have hy_res : intervalResidual d S y = k - 1 := by
    unfold intervalResidual
    simp [hyS, hydeg]
  have htransfer_cond : intervalResidual d S y + 2 ≤ intervalResidual d S x := by
    rw [hx_res, hy_res]
    omega
  have hGT :
      Graphical
        (Function.update
          (Function.update (intervalResidual d S) x (intervalResidual d S x - 1))
          y (intervalResidual d S y + 1)) :=
    down_transfer hG htransfer_cond
  have hfun :
      intervalResidual d T =
        Function.update
          (Function.update (intervalResidual d S) x (intervalResidual d S x - 1))
          y (intervalResidual d S y + 1) := by
    simpa [T] using intervalResidual_eq_update_exchange (d := d) (k := k)
      (S := S) (x := x) (y := y) hk hxS hyS hxhi hylow
  refine ⟨T, ?_, ?_, ?_⟩
  · exact card_exchange (S := S) (x := x) (y := y) hcard hxS hyS
  · exact highCount_exchange (d := d) (k := k) (S := S) (x := x) (y := y)
      hh hxS hyS hxhi hylow
  · rwa [hfun]

/-- IL-B as an upward-closure theorem for admissible `h` values. -/
theorem admissibleH_step_up {d : V → ℕ} {k : ℕ} {v : V} {r h : ℕ}
    (hnear : NearRegular d k) (hk : 0 < k)
    (hA : AdmissibleH d k v r h)
    (hfeasSucc : FeasibleH d k v r (h + 1)) :
    AdmissibleH d k v r (h + 1) := by
  rcases hA with ⟨S, hcard, hh, hG⟩
  rcases interval_step_up_representative (d := d) (k := k) (v := v) (r := r) (h := h)
      hnear hk hcard hh hG hfeasSucc with ⟨T, hTcard, hTh, hTG⟩
  exact ⟨T, hTcard, hTh, hTG⟩

/-- The prescribed neighbor set of `v`, as a finset in the deleted-vertex subtype. -/
def deletedNeighborSet (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Finset (Deleted v) :=
  Finset.univ.filter fun u : Deleted v => G.Adj v u.val

theorem deletedNeighborSet_card_eq_degree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (deletedNeighborSet G v).card = G.degree v := by
  classical
  rw [SimpleGraph.degree]
  exact Finset.card_bij
    (fun u _hu => u.val)
    (by
      intro u hu
      rw [SimpleGraph.mem_neighborFinset]
      exact (Finset.mem_filter.mp hu).2)
    (by
      intro a _ha b _hb h
      exact Subtype.ext h)
    (by
      intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw
      have hw_ne_v : w ≠ v := by
        intro hwv
        subst w
        exact G.irrefl hw
      refine ⟨⟨w, hw_ne_v⟩, ?_, rfl⟩
      simp [deletedNeighborSet, hw])

theorem graphical_intervalResidual_deletedNeighborSet {d : V → ℕ} {v : V}
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ x : V, G.degree x = d x) :
    Graphical (intervalResidual d (deletedNeighborSet G v)) := by
  classical
  refine ⟨deleteVertexGraph G v, inferInstance, ?_⟩
  intro u
  rw [deleteVertexGraph_degree_eq_sub, hdeg u.val]
  unfold intervalResidual deletedNeighborSet
  have hmem : u ∈ Finset.univ.filter (fun w : Deleted v => G.Adj v w.val) ↔
      G.Adj u.val v := by
    simp [G.adj_comm]
  by_cases hu : u ∈ Finset.univ.filter (fun w : Deleted v => G.Adj v w.val)
  · rw [if_pos hu, if_pos ((hmem.mp hu))]
  · rw [if_neg hu, if_neg (fun h => hu ((hmem.mpr h)))]

/-- Nonemptiness of the admissible `h`-set, obtained from a realization of `d`. -/
theorem admissibleH_nonempty_of_graphical {d : V → ℕ} {k : ℕ} {v : V} {r : ℕ}
    (hd : Graphical d) (hr : r = d v) :
    ∃ h : ℕ, AdmissibleH d k v r h := by
  classical
  rcases hd with ⟨G, hGdec, hdeg⟩
  letI := hGdec
  let S : Finset (Deleted v) := deletedNeighborSet G v
  refine ⟨highCount d k S, S, ?_, rfl, ?_⟩
  · dsimp [S]
    rw [deletedNeighborSet_card_eq_degree, hdeg v, ← hr]
  · exact graphical_intervalResidual_deletedNeighborSet (d := d) (v := v) hdeg

/-- Feasible predecessor inside the interval, used for iterating the transfer step. -/
theorem feasible_prev_of_succ {d : V → ℕ} {k : ℕ} {v : V} {r a m : ℕ}
    (hfa : FeasibleH d k v r a)
    (ha_le : a ≤ a + m)
    (hfs : FeasibleH d k v r (a + m + 1)) :
    FeasibleH d k v r (a + m) := by
  rcases hfa with ⟨hlo_a, _ha_r, _ha_H⟩
  rcases hfs with ⟨_hlo_s, hs_r, hs_H⟩
  constructor
  · omega
  constructor <;> omega

/-- The positive-`k` interval lemma, suffix form.  Within the feasible interval, the admissible
`h` values are exactly the values at least as large as the first admissible layer. -/
theorem intervalLemma_suffix_pos {d : V → ℕ} {k : ℕ} {v : V} {r : ℕ}
    (hnear : NearRegular d k) (hk : 0 < k)
    (hd : Graphical d) (hr : r = d v) :
    ∃ a : ℕ,
      FeasibleH d k v r a ∧ AdmissibleH d k v r a ∧
        ∀ h : ℕ, FeasibleH d k v r h →
          (AdmissibleH d k v r h ↔ a ≤ h) := by
  classical
  have hnonemptyA : ∃ h : ℕ, AdmissibleH d k v r h :=
    admissibleH_nonempty_of_graphical (d := d) (k := k) (v := v) (r := r) hd hr
  let a : ℕ := Nat.find hnonemptyA
  have haA : AdmissibleH d k v r a := Nat.find_spec hnonemptyA
  have hfa : FeasibleH d k v r a := by
    rcases haA with ⟨S, hcard, hh, _hG⟩
    exact feasible_of_layer hnear hcard hh
  have hmin : ∀ h : ℕ, AdmissibleH d k v r h → a ≤ h := by
    intro h hAh
    exact Nat.find_min' hnonemptyA hAh
  have h_up_from_a :
      ∀ m : ℕ, FeasibleH d k v r (a + m) → AdmissibleH d k v r (a + m) := by
    intro m
    induction m with
    | zero =>
        intro _hf
        simpa using haA
    | succ m ih =>
        intro hfs
        have hfprev : FeasibleH d k v r (a + m) :=
          feasible_prev_of_succ (d := d) (k := k) (v := v) (r := r) (a := a) (m := m)
            hfa (Nat.le_add_right a m) hfs
        have hAprev : AdmissibleH d k v r (a + m) := ih hfprev
        simpa [Nat.add_assoc] using
          admissibleH_step_up (d := d) (k := k) (v := v) (r := r) (h := a + m)
            hnear hk hAprev (by simpa [Nat.add_assoc] using hfs)
  refine ⟨a, hfa, haA, ?_⟩
  intro h hfh
  constructor
  · exact hmin h
  · intro hah
    have hrepr : h = a + (h - a) := by omega
    rw [hrepr] at hfh ⊢
    exact h_up_from_a (h - a) hfh

#print axioms intervalLemma_suffix_pos

theorem highSet_card_eq_odd_degree_others_of_k0 {d : V → ℕ} {v : V}
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hnear : NearRegular d 0) (hdeg : ∀ x : V, G.degree x = d x) :
    (highSet d 0 v).card =
      (Finset.univ.filter fun w : V => w ≠ v ∧ Odd (G.degree w)).card := by
  classical
  exact Finset.card_bij
    (fun u _hu => u.val)
    (by
      intro u hu
      rw [Finset.mem_filter]
      have hdu : d u.val = 1 := by simpa [highSet] using hu
      refine ⟨Finset.mem_univ _, u.property, ?_⟩
      rw [hdeg u.val, hdu]
      norm_num)
    (by
      intro a _ha b _hb h
      exact Subtype.ext h)
    (by
      intro w hw
      rw [Finset.mem_filter] at hw
      rcases hw with ⟨_hwu, hwne, hwodd⟩
      have hdw : d w = 1 := by
        rcases hnear w with hlow | hhigh
        · exfalso
          rw [hdeg w, hlow] at hwodd
          norm_num at hwodd
        · simpa using hhigh
      refine ⟨⟨w, hwne⟩, ?_, rfl⟩
      simp [highSet, hdw])

theorem highSet_card_odd_of_graphical_k0_one {d : V → ℕ} {v : V}
    (hnear : NearRegular d 0) (hd : Graphical d) (hdv : d v = 1) :
    Odd (highSet d 0 v).card := by
  classical
  rcases hd with ⟨G, hGdec, hdeg⟩
  letI := hGdec
  have hvodd : Odd (G.degree v) := by
    rw [hdeg v, hdv]
    norm_num
  have hodd_others :
      Odd (Finset.univ.filter fun w : V => w ≠ v ∧ Odd (G.degree w)).card := by
    simpa using G.odd_card_odd_degree_vertices_ne v hvodd
  rw [highSet_card_eq_odd_degree_others_of_k0 (d := d) (v := v) (G := G) hnear hdeg]
  exact hodd_others

theorem highSet_card_even_of_admissible_zero_k0 {d : V → ℕ} {v : V} {r : ℕ}
    (hnear : NearRegular d 0) (hA : AdmissibleH d 0 v r 0) :
    Even (highSet d 0 v).card := by
  classical
  rcases hA with ⟨S, _hcard, hh, hG⟩
  have hfilter_empty :
      S.filter (fun u : Deleted v => d u.val = 1) = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [highCount] using hh
  have hselected_not_high :
      ∀ u : Deleted v, d u.val = 1 → u ∉ S := by
    intro u hdu huS
    have hu : u ∈ S.filter (fun u : Deleted v => d u.val = 1) :=
      Finset.mem_filter.mpr ⟨huS, hdu⟩
    rw [hfilter_empty] at hu
    simpa using hu
  rcases hG with ⟨G, hGdec, hdeg⟩
  letI := hGdec
  have hodd_eq :
      (Finset.univ.filter fun u : Deleted v => Odd (G.degree u)).card =
        (highSet d 0 v).card := by
    congr 1
    ext u
    constructor
    · intro hu
      rw [Finset.mem_filter] at hu
      have hodd : Odd (G.degree u) := hu.2
      rw [hdeg u] at hodd
      unfold intervalResidual at hodd
      rcases hnear u.val with hlow | hhigh
      · rw [hlow] at hodd
        norm_num at hodd
      · simp [highSet, hhigh]
    · intro hu
      rw [Finset.mem_filter]
      have hhigh : d u.val = 1 := by simpa [highSet] using hu
      have huS : u ∉ S := hselected_not_high u hhigh
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hdeg u]
      unfold intervalResidual
      simp [hhigh, huS]
  have heven_odd_vertices : Even (Finset.univ.filter fun u : Deleted v => Odd (G.degree u)).card :=
    G.even_card_odd_degree_vertices
  rwa [hodd_eq] at heven_odd_vertices

theorem not_admissible_zero_layer_k0_one {d : V → ℕ} {v : V} {r : ℕ}
    (hnear : NearRegular d 0) (hd : Graphical d) (hr : r = d v) (hr1 : r = 1) :
    ¬ AdmissibleH d 0 v r 0 := by
  intro hA
  have hdv : d v = 1 := by omega
  have hodd : Odd (highSet d 0 v).card :=
    highSet_card_odd_of_graphical_k0_one hnear hd hdv
  have heven : Even (highSet d 0 v).card :=
    highSet_card_even_of_admissible_zero_k0 hnear hA
  exact (Nat.not_even_iff_odd.mpr hodd) heven

theorem intervalLemma_suffix_zero {d : V → ℕ} {v : V} {r : ℕ}
    (hnear : NearRegular d 0)
    (hd : Graphical d) (hr : r = d v) :
    ∃ a : ℕ,
      FeasibleH d 0 v r a ∧ AdmissibleH d 0 v r a ∧
        ∀ h : ℕ, FeasibleH d 0 v r h →
          (AdmissibleH d 0 v r h ↔ a ≤ h) := by
  classical
  have hnonemptyA : ∃ h : ℕ, AdmissibleH d 0 v r h :=
    admissibleH_nonempty_of_graphical (d := d) (k := 0) (v := v) (r := r) hd hr
  rcases hnear v with hdv0 | hdv1
  · have hr0 : r = 0 := by omega
    obtain ⟨h0, hA0raw⟩ := hnonemptyA
    have hf0raw : FeasibleH d 0 v r h0 := by
      rcases hA0raw with ⟨S, hcard, hh, _hG⟩
      exact feasible_of_layer hnear hcard hh
    have hh0 : h0 = 0 := by
      have hle : h0 ≤ r := hf0raw.2.1
      omega
    have hA0 : AdmissibleH d 0 v r 0 := by simpa [hh0] using hA0raw
    have hf0 : FeasibleH d 0 v r 0 := by simpa [hh0] using hf0raw
    refine ⟨0, hf0, hA0, ?_⟩
    intro h hf
    have hh : h = 0 := by
      have hle : h ≤ r := hf.2.1
      omega
    subst h
    constructor
    · intro _; exact le_rfl
    · intro _; exact hA0
  · have hr1 : r = 1 := by omega
    have hnotA0 : ¬ AdmissibleH d 0 v r 0 :=
      not_admissible_zero_layer_k0_one hnear hd hr hr1
    obtain ⟨h1, hA1raw⟩ := hnonemptyA
    have hf1raw : FeasibleH d 0 v r h1 := by
      rcases hA1raw with ⟨S, hcard, hh, _hG⟩
      exact feasible_of_layer hnear hcard hh
    have hh1 : h1 = 1 := by
      have hle : h1 ≤ 1 := by
        have hle_r : h1 ≤ r := hf1raw.2.1
        omega
      interval_cases h1
      · exact False.elim (hnotA0 (by simpa using hA1raw))
      · rfl
    have hA1 : AdmissibleH d 0 v r 1 := by simpa [hh1] using hA1raw
    have hf1 : FeasibleH d 0 v r 1 := by simpa [hh1] using hf1raw
    refine ⟨1, hf1, hA1, ?_⟩
    intro h hf
    have hle : h ≤ 1 := by
      have hle_r : h ≤ r := hf.2.1
      omega
    interval_cases h
    · constructor
      · intro hA; exact False.elim (hnotA0 hA)
      · intro hle10; omega
    · constructor
      · intro _; exact le_rfl
      · intro _; exact hA1

/-- The interval lemma, suffix form.  Within the feasible interval, the admissible `h` values
are exactly the values at least as large as the first admissible layer. -/
theorem intervalLemma_suffix {d : V → ℕ} {k : ℕ} {v : V} {r : ℕ}
    (hnear : NearRegular d k)
    (hd : Graphical d) (hr : r = d v) :
    ∃ a : ℕ,
      FeasibleH d k v r a ∧ AdmissibleH d k v r a ∧
        ∀ h : ℕ, FeasibleH d k v r h →
          (AdmissibleH d k v r h ↔ a ≤ h) := by
  by_cases hk : 0 < k
  · exact intervalLemma_suffix_pos hnear hk hd hr
  · have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    subst k
    exact intervalLemma_suffix_zero hnear hd hr

#print axioms intervalLemma_suffix

end Brualdi.RealizationGraph
