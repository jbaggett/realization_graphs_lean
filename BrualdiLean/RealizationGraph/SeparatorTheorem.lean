/-
Copyright (c) 2026 Jeffrey S. Baggett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey S. Baggett
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Atoms.Finite
import Init.Omega

/-!
# The capacity-one separator theorem

This file is intentionally not imported by `BrualdiLean.lean`.  It formalizes the
separator stack from `next_paper/explore/capacity_separator.md`, using the independent
derivations in `round5_adversary.md`.  In particular it does not import
`RealizationGraph.LayerCapacity`, whose threshold results are axiomatized.
-/

set_option autoImplicit false
set_option linter.style.nativeDecide false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open scoped BigOperators

namespace Brualdi.RealizationGraph.SeparatorTheorem

universe u

/-! ## 1. The profile box and the lead's lattice lemmas -/

/-- Capacity accumulated in the first `k` classes. -/
def capacityPrefix {s : ℕ} (c : Fin s → ℕ) (k : Fin (s + 1)) : ℕ :=
  ∑ i : Fin s, if i.val < k.val then c i else 0

@[simp]
theorem capacityPrefix_zero {s : ℕ} (c : Fin s → ℕ) :
    capacityPrefix c 0 = 0 := by
  simp [capacityPrefix]

theorem capacityPrefix_succ {s : ℕ} (c : Fin s → ℕ) (k : Fin s) :
    capacityPrefix c k.succ = capacityPrefix c k.castSucc + c k := by
  classical
  unfold capacityPrefix
  calc
    (∑ i, if i.val < k.succ.val then c i else 0) =
        ∑ i, ((if i.val < k.castSucc.val then c i else 0) +
          if i = k then c k else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hik : i = k
      · subst i
        simp
      · by_cases hi : i.val < k.val
        · have his : i.val < k.val + 1 := by omega
          simp [hi, his, hik]
        · have hki : k.val < i.val := by
            have hne : i.val ≠ k.val := fun h => hik (Fin.ext h)
            omega
          have hnis : ¬ i.val < k.val + 1 := by omega
          simp [hi, hnis, hik]
    _ = (∑ i, if i.val < k.castSucc.val then c i else 0) +
          ∑ i, if i = k then c k else 0 := Finset.sum_add_distrib
    _ = (∑ i, if i.val < k.castSucc.val then c i else 0) + c k := by
      simp

@[simp]
theorem capacityPrefix_last {s : ℕ} (c : Fin s → ℕ) :
    capacityPrefix c (Fin.last s) = ∑ i, c i := by
  classical
  unfold capacityPrefix
  apply Finset.sum_congr rfl
  intro i _
  simp [Fin.is_lt i]

/-- `Omega(c,r)`, encoded by its prefix vector including the fixed endpoints `0` and `r`.
The class count in position `k` is `prefix k.succ - prefix k.castSucc`. -/
structure Profile {s : ℕ} (c : Fin s → ℕ) (r : ℕ) where
  pref : Fin (s + 1) → ℕ
  pref_zero : pref 0 = 0
  pref_last : pref (Fin.last s) = r
  step_mono : ∀ k : Fin s, pref k.castSucc ≤ pref k.succ
  step_cap : ∀ k : Fin s, pref k.succ ≤ pref k.castSucc + c k

namespace Profile

variable {s : ℕ} {c : Fin s → ℕ} {r : ℕ}

instance : LE (Profile c r) := ⟨fun x y ↦ ∀ k, x.pref k ≤ y.pref k⟩

instance : PartialOrder (Profile c r) where
  le_refl x _ := le_rfl
  le_trans _ _ _ hxy hyz k := (hxy k).trans (hyz k)
  le_antisymm x y hxy hyx := by
    cases x
    cases y
    congr
    funext k
    exact Nat.le_antisymm (hxy k) (hyx k)

@[ext]
theorem ext {x y : Profile c r} (h : ∀ k, x.pref k = y.pref k) : x = y := by
  cases x
  cases y
  congr
  funext k
  exact h k

/-- Componentwise maximum of feasible prefix vectors. -/
def join (x y : Profile c r) : Profile c r where
  pref k := max (x.pref k) (y.pref k)
  pref_zero := by simp [x.pref_zero, y.pref_zero]
  pref_last := by simp [x.pref_last, y.pref_last]
  step_mono k := by
    exact max_le_max (x.step_mono k) (y.step_mono k)
  step_cap k := by
    rcases le_total (x.pref k.castSucc) (y.pref k.castSucc) with h | h
    · rcases le_total (x.pref k.succ) (y.pref k.succ) with h' | h'
      · simpa [max_eq_right h, max_eq_right h'] using y.step_cap k
      · rw [max_eq_right h, max_eq_left h']
        exact (x.step_cap k).trans (Nat.add_le_add_right h _)
    · rcases le_total (x.pref k.succ) (y.pref k.succ) with h' | h'
      · rw [max_eq_left h, max_eq_right h']
        exact (y.step_cap k).trans (Nat.add_le_add_right h _)
      · simpa [max_eq_left h, max_eq_left h'] using x.step_cap k

/-- Componentwise minimum of feasible prefix vectors. -/
def meet (x y : Profile c r) : Profile c r where
  pref k := min (x.pref k) (y.pref k)
  pref_zero := by simp [x.pref_zero, y.pref_zero]
  pref_last := by simp [x.pref_last, y.pref_last]
  step_mono k := min_le_min (x.step_mono k) (y.step_mono k)
  step_cap k := by
    rcases le_total (x.pref k.castSucc) (y.pref k.castSucc) with h | h
    · rcases le_total (x.pref k.succ) (y.pref k.succ) with h' | h'
      · simpa [min_eq_left h, min_eq_left h'] using x.step_cap k
      · rw [min_eq_left h, min_eq_right h']
        exact h'.trans (x.step_cap k)
    · rcases le_total (x.pref k.succ) (y.pref k.succ) with h' | h'
      · rw [min_eq_right h, min_eq_left h']
        exact h'.trans (y.step_cap k)
      · simpa [min_eq_right h, min_eq_right h'] using y.step_cap k

instance : Lattice (Profile c r) where
  sup := join
  le_sup_left x y k := Nat.le_max_left _ _
  le_sup_right x y k := Nat.le_max_right _ _
  sup_le x y z hx hy k := max_le (hx k) (hy k)
  inf := meet
  inf_le_left x y k := min_le_left _ _
  inf_le_right x y k := min_le_right _ _
  le_inf x y z hxy hxz k := le_min (hxy k) (hxz k)

@[simp]
theorem join_prefix (x y : Profile c r) (k : Fin (s + 1)) :
    (x ⊔ y).pref k = max (x.pref k) (y.pref k) := rfl

@[simp]
theorem meet_prefix (x y : Profile c r) (k : Fin (s + 1)) :
    (x ⊓ y).pref k = min (x.pref k) (y.pref k) := rfl

/-- The greedy profile, filling higher classes first. -/
def boxTop (c : Fin s → ℕ) (r : ℕ) (hr : r ≤ ∑ i, c i) : Profile c r where
  pref k := min r (capacityPrefix c k)
  pref_zero := by simp
  pref_last := by simp [hr]
  step_mono k := by
    rw [capacityPrefix_succ]
    exact min_le_min le_rfl (Nat.le_add_right _ _)
  step_cap k := by
    rw [capacityPrefix_succ]
    omega

theorem prefix_le_capacity (x : Profile c r) (k : Fin (s + 1)) :
    x.pref k ≤ capacityPrefix c k := by
  induction k using Fin.induction with
  | zero => simp [x.pref_zero]
  | succ j ih =>
      rw [capacityPrefix_succ]
      exact (x.step_cap j).trans (Nat.add_le_add_right ih _)

theorem prefix_le_total (x : Profile c r) (k : Fin (s + 1)) : x.pref k ≤ r := by
  have hmono : Monotone x.pref := Fin.monotone_iff_le_succ.mpr x.step_mono
  exact (hmono (Fin.le_last k)).trans_eq x.pref_last

noncomputable instance : Fintype (Profile c r) := by
  classical
  let f : Profile c r → (Fin (s + 1) → Fin (r + 1)) := fun x k =>
    ⟨x.pref k, Nat.lt_succ_of_le (prefix_le_total x k)⟩
  exact Fintype.ofInjective f (by
    intro x y h
    apply ext
    intro k
    exact congrArg (fun g => (g k).val) h)

theorem le_boxTop (x : Profile c r) (hr : r ≤ ∑ i, c i) : x ≤ boxTop c r hr := by
  intro k
  exact le_min (prefix_le_total x k) (prefix_le_capacity x k)

/-- Principal upper filter `L(z)` from the lead's note. -/
def filter (z : Profile c r) : Set (Profile c r) := {x | z ≤ x}

/-- Lead Lemma 2: filter intersections are filters of joins. -/
theorem filter_inter (x y : Profile c r) : filter x ∩ filter y = filter (x ⊔ y) := by
  ext z
  simp only [filter, Set.mem_inter_iff, Set.mem_setOf_eq]
  exact ⟨fun h ↦ sup_le h.1 h.2, fun h ↦ ⟨le_sup_left.trans h, le_sup_right.trans h⟩⟩

/-- Lead Lemma 3, stated without cardinal arithmetic: a principal upper filter is a
singleton exactly at the box top. -/
theorem filter_eq_singleton_iff (z : Profile c r) (hr : r ≤ ∑ i, c i) :
    filter z = {boxTop c r hr} ↔ z = boxTop c r hr := by
  constructor
  · intro h
    have hz : z ∈ filter z := by
      change z ≤ z
      exact le_rfl
    rw [h] at hz
    simpa using hz
  · rintro rfl
    ext x
    simp only [filter, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      exact le_antisymm (le_boxTop x hr) h
    · rintro rfl
      exact le_rfl

/-- Lead Lemma 1: the profile box is a distributive lattice. -/
theorem sup_inf_distrib (x y z : Profile c r) : x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z) := by
  ext k
  simp only [join_prefix, meet_prefix]
  omega

theorem inf_sup_distrib (x y z : Profile c r) : x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := by
  ext k
  simp only [join_prefix, meet_prefix]
  omega

end Profile

/-! ## 2. Graphicality and threshold rigidity -/

section Graphicality

variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable local instance graphAdjDecidable (G : SimpleGraph V) : DecidableRel G.Adj :=
  Classical.decRel G.Adj

/-- A foundations-only graphicality interface.  This is the same simple-graph existence
predicate as `RealizationGraph.Transfer.Graphical`, restated here to keep this module isolated
from the main realization-graph import tree. -/
def Graphical (d : V → ℕ) : Prop :=
  ∃ G : SimpleGraph V, ∀ v, G.degree v = d v

/-- A labeled realization of a finite degree function. -/
def Realization (d : V → ℕ) := {G : SimpleGraph V // ∀ v, G.degree v = d v}

noncomputable instance (d : V → ℕ) : Fintype (Realization d) := by
  classical
  unfold Realization
  infer_instance

/-- The printed capacity: the number of realizations on the fixed labels. -/
noncomputable def capacity (d : V → ℕ) : ℕ := Fintype.card (Realization d)

theorem graphical_iff_realization_nonempty {d : V → ℕ} :
    Graphical d ↔ Nonempty (Realization d) := by
  constructor
  · rintro ⟨G, hG⟩
    exact ⟨⟨G, hG⟩⟩
  · rintro ⟨G⟩
    exact ⟨G.1, G.2⟩

theorem capacity_eq_one_iff_unique {d : V → ℕ} :
    capacity d = 1 ↔ ∃ G : Realization d, ∀ H : Realization d, H = G := by
  classical
  exact Fintype.card_eq_one_iff

/-- Degree inside a finite induced vertex set. -/
noncomputable def degreeOn (G : SimpleGraph V) (S : Finset V) (v : V) : ℕ :=
  (S.filter (G.Adj v)).card

theorem degreeOn_univ (G : SimpleGraph V) (v : V) : degreeOn G Finset.univ v = G.degree v := by
  classical
  unfold degreeOn SimpleGraph.degree SimpleGraph.neighborFinset
  congr
  ext w
  simp

theorem degreeOn_erase (G : SimpleGraph V) (S : Finset V) {v x : V} (hvS : v ∈ S) :
    degreeOn G (S.erase v) x = degreeOn G S x - if G.Adj x v then 1 else 0 := by
  classical
  unfold degreeOn
  by_cases hxv : G.Adj x v
  · have hvfilter : v ∈ S.filter (G.Adj x) := Finset.mem_filter.mpr ⟨hvS, hxv⟩
    rw [Finset.filter_erase, Finset.card_erase_of_mem hvfilter]
    simp [hxv]
  · have hvfilter : v ∉ S.filter (G.Adj x) := by simp [hxv]
    rw [Finset.filter_erase, Finset.erase_eq_of_notMem hvfilter]
    simp [hxv]

/-- Isolated in the graph induced by `S`. -/
def IsIsolatedIn (G : SimpleGraph V) (S : Finset V) (v : V) : Prop :=
  v ∈ S ∧ ∀ w ∈ S, ¬ G.Adj v w

/-- Universal in the graph induced by `S`. -/
def IsUniversalIn (G : SimpleGraph V) (S : Finset V) (v : V) : Prop :=
  v ∈ S ∧ ∀ w ∈ S, w ≠ v → G.Adj v w

/-- Deletion characterization of a threshold graph, expressed hereditarily: every nonempty
induced subgraph has an isolated or a universal vertex. -/
def IsThresholdGraph (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, S.Nonempty → ∃ v, IsIsolatedIn G S v ∨ IsUniversalIn G S v

/-- A degree function is threshold when one (and hence, below, every) realization is a
threshold graph. -/
def IsThreshold (d : V → ℕ) : Prop :=
  ∃ G : Realization d, IsThresholdGraph G.1

private theorem isolatedIn_of_degreeOn_eq_zero {G : SimpleGraph V} {S : Finset V} {v : V}
    (hvS : v ∈ S) (hdeg : degreeOn G S v = 0) : IsIsolatedIn G S v := by
  refine ⟨hvS, ?_⟩
  intro w hwS hvw
  have : w ∈ S.filter (G.Adj v) := Finset.mem_filter.mpr ⟨hwS, hvw⟩
  have hpos : 0 < (S.filter (G.Adj v)).card := Finset.card_pos.mpr ⟨w, this⟩
  have hzero : (S.filter (G.Adj v)).card = 0 := by simpa [degreeOn] using hdeg
  omega

private theorem degreeOn_universalIn {G : SimpleGraph V} {S : Finset V} {v : V}
    (hv : IsUniversalIn G S v) : degreeOn G S v = S.card - 1 := by
  classical
  have heq : S.filter (G.Adj v) = S.erase v := by
    ext w
    constructor
    · intro hw
      have hmem := Finset.mem_filter.mp hw
      exact Finset.mem_erase.mpr ⟨fun h => G.irrefl (h ▸ hmem.2), hmem.1⟩
    · intro hw
      have hmem := Finset.mem_erase.mp hw
      exact Finset.mem_filter.mpr ⟨hmem.2, hv.2 w hmem.2 hmem.1⟩
  rw [degreeOn, heq, Finset.card_erase_of_mem hv.1]

private theorem universalIn_of_degreeOn_eq {G : SimpleGraph V} {S : Finset V} {v : V}
    (hvS : v ∈ S) (hdeg : degreeOn G S v = S.card - 1) : IsUniversalIn G S v := by
  classical
  refine ⟨hvS, ?_⟩
  have hsub : S.filter (G.Adj v) ⊆ S.erase v := by
    intro w hw
    have hmem := Finset.mem_filter.mp hw
    exact Finset.mem_erase.mpr ⟨fun h => G.irrefl (h ▸ hmem.2), hmem.1⟩
  have hcardErase : (S.erase v).card = S.card - 1 := Finset.card_erase_of_mem hvS
  have heq : S.filter (G.Adj v) = S.erase v := by
    apply Finset.eq_of_subset_of_card_le hsub
    have hc : (S.filter (G.Adj v)).card = (S.erase v).card := by
      rw [hcardErase]
      simpa [degreeOn] using hdeg
    exact hc.ge
  intro w hwS hwv
  have : w ∈ S.erase v := Finset.mem_erase.mpr ⟨hwv, hwS⟩
  rw [← heq] at this
  exact (Finset.mem_filter.mp this).2

/-- The deletion induction from Round 5: a threshold realization is rigid among labeled
graphs with the same degree function. -/
theorem thresholdGraph_rigid {G H : SimpleGraph V} (hthreshold : IsThresholdGraph G)
    (hdeg : ∀ v, G.degree v = H.degree v) : G = H := by
  classical
  apply SimpleGraph.ext
  funext a b
  apply propext
  have aux : ∀ S : Finset V,
      (∀ x ∈ S, degreeOn G S x = degreeOn H S x) →
        ∀ x ∈ S, ∀ y ∈ S, G.Adj x y ↔ H.Adj x y := by
    intro S
    induction hn : S.card using Nat.strong_induction_on generalizing S with
    | h n ih =>
      intro hdegrees x hxS y hyS
      by_cases hSne : S.Nonempty
      · obtain ⟨v, hviso | hvuniv⟩ := hthreshold S hSne
        · have hGv0 : degreeOn G S v = 0 := by
            unfold degreeOn
            apply Finset.card_eq_zero.mpr
            by_contra hne
            obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr hne
            exact hviso.2 w (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hw).2
          have hHv0 : degreeOn H S v = 0 := (hdegrees v hviso.1) ▸ hGv0
          have hHiso : IsIsolatedIn H S v := isolatedIn_of_degreeOn_eq_zero hviso.1 hHv0
          have hadjv : ∀ w ∈ S, G.Adj v w ↔ H.Adj v w := by
            intro w hw
            exact ⟨fun h => False.elim (hviso.2 w hw h),
              fun h => False.elim (hHiso.2 w hw h)⟩
          let T := S.erase v
          have hTcard : T.card < n := by
            rw [← hn]
            exact Finset.card_erase_lt_of_mem hviso.1
          have hTdegrees : ∀ q ∈ T, degreeOn G T q = degreeOn H T q := by
            intro q hq
            have hqS : q ∈ S := Finset.mem_of_mem_erase hq
            have hqv : q ≠ v := (Finset.mem_erase.mp hq).1
            rw [degreeOn_erase G S hviso.1, degreeOn_erase H S hviso.1,
              hdegrees q hqS]
            have hadj : G.Adj q v ↔ H.Adj q v := by
              simpa [SimpleGraph.adj_comm] using hadjv q hqS
            simp only [hadj]
          by_cases hxv : x = v
          · subst x
            exact hadjv y hyS
          · by_cases hyv : y = v
            · subst y
              simpa [SimpleGraph.adj_comm] using hadjv x hxS
            · exact ih T.card hTcard T rfl hTdegrees x
                (Finset.mem_erase.mpr ⟨hxv, hxS⟩) y
                (Finset.mem_erase.mpr ⟨hyv, hyS⟩)
        · have hGv : degreeOn G S v = S.card - 1 := degreeOn_universalIn hvuniv
          have hHv : degreeOn H S v = S.card - 1 := (hdegrees v hvuniv.1) ▸ hGv
          have hHuniv : IsUniversalIn H S v := universalIn_of_degreeOn_eq hvuniv.1 hHv
          have hadjv : ∀ w ∈ S, G.Adj v w ↔ H.Adj v w := by
            intro w hw
            by_cases hwv : w = v
            · subst w
              simp
            · exact ⟨fun _ => hHuniv.2 w hw hwv, fun _ => hvuniv.2 w hw hwv⟩
          let T := S.erase v
          have hTcard : T.card < n := by
            rw [← hn]
            exact Finset.card_erase_lt_of_mem hvuniv.1
          have hTdegrees : ∀ q ∈ T, degreeOn G T q = degreeOn H T q := by
            intro q hq
            have hqS : q ∈ S := Finset.mem_of_mem_erase hq
            rw [degreeOn_erase G S hvuniv.1, degreeOn_erase H S hvuniv.1,
              hdegrees q hqS]
            have hadj : G.Adj q v ↔ H.Adj q v := by
              simpa [SimpleGraph.adj_comm] using hadjv q hqS
            simp only [hadj]
          by_cases hxv : x = v
          · subst x
            exact hadjv y hyS
          · by_cases hyv : y = v
            · subst y
              simpa [SimpleGraph.adj_comm] using hadjv x hxS
            · exact ih T.card hTcard T rfl hTdegrees x
                (Finset.mem_erase.mpr ⟨hxv, hxS⟩) y
                (Finset.mem_erase.mpr ⟨hyv, hyS⟩)
      · exact False.elim (hSne ⟨x, hxS⟩)
  exact aux Finset.univ (fun v _ => by simpa [degreeOn_univ] using hdeg v)
    a (Finset.mem_univ _) b (Finset.mem_univ _)

theorem threshold_capacity_one {d : V → ℕ} (hd : IsThreshold d) : capacity d = 1 := by
  classical
  obtain ⟨G, hGthreshold⟩ := hd
  rw [capacity_eq_one_iff_unique]
  refine ⟨G, fun H => ?_⟩
  apply Subtype.ext
  exact (thresholdGraph_rigid hGthreshold fun v => (G.2 v).trans (H.2 v).symm).symm

private def Pair (a b x y : V) : Prop := (a = x ∧ b = y) ∨ (a = y ∧ b = x)

private theorem Pair.symm {a b x y : V} : Pair a b x y → Pair b a x y := by
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [Pair]

/-- The degree-preserving switch from Round 5: delete `uw,vz` and add `uv,wz`. -/
private def switchGraph (G : SimpleGraph V) (u w v z : V) : SimpleGraph V where
  Adj a b :=
    (G.Adj a b ∧ ¬ Pair a b u w ∧ ¬ Pair a b v z) ∨
      (a ≠ b ∧ Pair a b u v) ∨ (a ≠ b ∧ Pair a b w z)
  symm := ⟨by
    intro a b h
    rcases h with ⟨hG, huw, hvz⟩ | ⟨hne, huv⟩ | ⟨hne, hwz⟩
    · exact Or.inl ⟨hG.symm, fun h => huw h.symm, fun h => hvz h.symm⟩
    · exact Or.inr (Or.inl ⟨hne.symm, huv.symm⟩)
    · exact Or.inr (Or.inr ⟨hne.symm, hwz.symm⟩)⟩
  loopless := ⟨by
    intro a h
    rcases h with ⟨hG, _, _⟩ | ⟨hne, _⟩ | ⟨hne, _⟩
    · exact G.irrefl hG
    · exact hne rfl
    · exact hne rfl⟩

private theorem switchGraph_adj_u {G : SimpleGraph V} {u w v z q : V}
    (huw : G.Adj u w) (hvz : G.Adj v z) (huv : ¬ G.Adj u v) (hwz : ¬ G.Adj w z)
    (huwv : u ≠ w) (huv' : u ≠ v) (huz : u ≠ z) (hwv : w ≠ v) (hwz' : w ≠ z)
    (hvz' : v ≠ z) :
    (switchGraph G u w v z).Adj u q ↔ (G.Adj u q ∧ q ≠ w) ∨ q = v := by
  change ((G.Adj u q ∧ ¬ Pair u q u w ∧ ¬ Pair u q v z) ∨
      (u ≠ q ∧ Pair u q u v) ∨ (u ≠ q ∧ Pair u q w z)) ↔ _
  constructor
  · rintro (⟨huq, hdeluw, _hdelvz⟩ | ⟨_, (⟨_, hqv⟩ | ⟨huvEq, _⟩)⟩ |
      ⟨_, (⟨huwEq, _⟩ | ⟨huzEq, _⟩)⟩)
    · exact Or.inl ⟨huq, fun h => hdeluw (Or.inl ⟨rfl, h⟩)⟩
    · exact Or.inr hqv
    · exact False.elim (huv' huvEq)
    · exact False.elim (huwv huwEq)
    · exact False.elim (huz huzEq)
  · rintro (⟨huq, hqw⟩ | rfl)
    · left
      refine ⟨huq, ?_, ?_⟩
      · rintro (⟨_, rfl⟩ | ⟨huwEq, _⟩)
        · exact hqw rfl
        · exact huwv huwEq
      · rintro (⟨huvEq, _⟩ | ⟨huzEq, _⟩)
        · exact huv' huvEq
        · exact huz huzEq
    · exact Or.inr (Or.inl ⟨huv', Or.inl ⟨rfl, rfl⟩⟩)

private theorem switchGraph_adj_w {G : SimpleGraph V} {u w v z q : V}
    (huw : G.Adj u w) (hvz : G.Adj v z) (huv : ¬ G.Adj u v) (hwz : ¬ G.Adj w z)
    (huwv : u ≠ w) (huv' : u ≠ v) (huz : u ≠ z) (hwv : w ≠ v) (hwz' : w ≠ z)
    (hvz' : v ≠ z) :
    (switchGraph G u w v z).Adj w q ↔ (G.Adj w q ∧ q ≠ u) ∨ q = z := by
  have h := switchGraph_adj_u (G := G) (u := w) (w := u) (v := z) (z := v) (q := q)
    huw.symm hvz.symm hwz huv
      huwv.symm hwz' hwv huz huv' hvz'.symm
  simpa [switchGraph, Pair, or_comm, and_left_comm, and_comm] using h

private theorem switchGraph_adj_v {G : SimpleGraph V} {u w v z q : V}
    (huw : G.Adj u w) (hvz : G.Adj v z) (huv : ¬ G.Adj u v) (hwz : ¬ G.Adj w z)
    (huwv : u ≠ w) (huv' : u ≠ v) (huz : u ≠ z) (hwv : w ≠ v) (hwz' : w ≠ z)
    (hvz' : v ≠ z) :
    (switchGraph G u w v z).Adj v q ↔ (G.Adj v q ∧ q ≠ z) ∨ q = u := by
  have h := switchGraph_adj_u (G := G) (u := v) (w := z) (v := u) (z := w) (q := q)
    hvz huw (fun h => huv h.symm) (fun h => hwz h.symm)
      hvz' huv'.symm hwv.symm huz.symm hwz'.symm huwv
  simpa [switchGraph, Pair, or_comm, and_left_comm, and_comm] using h

private theorem switchGraph_adj_z {G : SimpleGraph V} {u w v z q : V}
    (huw : G.Adj u w) (hvz : G.Adj v z) (huv : ¬ G.Adj u v) (hwz : ¬ G.Adj w z)
    (huwv : u ≠ w) (huv' : u ≠ v) (huz : u ≠ z) (hwv : w ≠ v) (hwz' : w ≠ z)
    (hvz' : v ≠ z) :
    (switchGraph G u w v z).Adj z q ↔ (G.Adj z q ∧ q ≠ v) ∨ q = w := by
  have h := switchGraph_adj_w (G := G) (u := v) (w := z) (v := u) (z := w) (q := q)
    hvz huw (fun h => huv h.symm) (fun h => hwz h.symm)
      hvz' huv'.symm hwv.symm huz.symm hwz'.symm huwv
  simpa [switchGraph, Pair, or_comm, and_left_comm, and_comm] using h

private theorem switchGraph_adj_other {G : SimpleGraph V} {u w v z q a : V}
    (hau : a ≠ u) (haw : a ≠ w) (hav : a ≠ v) (haz : a ≠ z) :
    (switchGraph G u w v z).Adj a q ↔ G.Adj a q := by
  simp [switchGraph, Pair, hau, haw, hav, haz]

/-- The explicit two-switch preserves every labeled degree. -/
private theorem switchGraph_degree {G : SimpleGraph V} {u w v z : V}
    (huw : G.Adj u w) (hvz : G.Adj v z) (huv : ¬ G.Adj u v) (hwz : ¬ G.Adj w z)
    (huwv : u ≠ w) (huv' : u ≠ v) (huz : u ≠ z) (hwv : w ≠ v) (hwz' : w ≠ z)
    (hvz' : v ≠ z) :
    ∀ a, (switchGraph G u w v z).degree a = G.degree a := by
  classical
  intro a
  unfold SimpleGraph.degree
  by_cases hau : a = u
  · subst a
    have heq : (switchGraph G u w v z).neighborFinset u =
        insert v ((G.neighborFinset u).erase w) := by
      ext q
      simp [SimpleGraph.mem_neighborFinset, and_comm, or_comm, or_left_comm,
        switchGraph_adj_u huw hvz huv hwz huwv huv' huz hwv hwz' hvz']
    rw [heq, Finset.card_insert_of_notMem, Finset.card_erase_add_one]
    · simpa [SimpleGraph.mem_neighborFinset] using huw
    · simp [SimpleGraph.mem_neighborFinset, huv, hwv.symm]
  · by_cases haw : a = w
    · subst a
      have heq : (switchGraph G u w v z).neighborFinset w =
          insert z ((G.neighborFinset w).erase u) := by
        ext q
        simp [SimpleGraph.mem_neighborFinset, and_comm, or_comm, or_left_comm,
          switchGraph_adj_w huw hvz huv hwz huwv huv' huz hwv hwz' hvz']
      rw [heq, Finset.card_insert_of_notMem, Finset.card_erase_add_one]
      · simpa [SimpleGraph.mem_neighborFinset] using huw.symm
      · simp [SimpleGraph.mem_neighborFinset, hwz, huz]
    · by_cases hav : a = v
      · subst a
        have heq : (switchGraph G u w v z).neighborFinset v =
            insert u ((G.neighborFinset v).erase z) := by
          ext q
          simp [SimpleGraph.mem_neighborFinset, and_comm, or_comm, or_left_comm,
            switchGraph_adj_v huw hvz huv hwz huwv huv' huz hwv hwz' hvz']
        rw [heq, Finset.card_insert_of_notMem, Finset.card_erase_add_one]
        · simpa [SimpleGraph.mem_neighborFinset] using hvz
        · have hnot : ¬ G.Adj v u := fun h => huv h.symm
          simp [SimpleGraph.mem_neighborFinset, hnot, huz]
      · by_cases haz : a = z
        · subst a
          have heq : (switchGraph G u w v z).neighborFinset z =
              insert w ((G.neighborFinset z).erase v) := by
            ext q
            simp [SimpleGraph.mem_neighborFinset, and_comm, or_comm, or_left_comm,
              switchGraph_adj_z huw hvz huv hwz huwv huv' huz hwv hwz' hvz']
          rw [heq, Finset.card_insert_of_notMem, Finset.card_erase_add_one]
          · simpa [SimpleGraph.mem_neighborFinset] using hvz.symm
          · have hnot : ¬ G.Adj z w := fun h => hwz h.symm
            simp [SimpleGraph.mem_neighborFinset, hnot, hwv]
        · congr 1
          ext q
          simp [SimpleGraph.mem_neighborFinset, switchGraph_adj_other hau haw hav haz]

/-- Round 5's independently re-derived switch witness.  A finite induced graph with no
isolated and no universal vertex contains the four distinct labels needed for a switch. -/
private theorem exists_switch_data (G : SimpleGraph V) (S : Finset V) (hS : S.Nonempty)
    (hno : ∀ a ∈ S, ¬ IsIsolatedIn G S a ∧ ¬ IsUniversalIn G S a) :
    ∃ u w v z,
      G.Adj u w ∧ G.Adj v z ∧ ¬ G.Adj u v ∧ ¬ G.Adj w z ∧
      u ≠ w ∧ u ≠ v ∧ u ≠ z ∧ w ≠ v ∧ w ≠ z ∧ v ≠ z := by
  classical
  obtain ⟨v, hvS, hvmax⟩ := S.exists_max_image (degreeOn G S) hS
  have hnuv := (hno v hvS).2
  have hexu : ∃ u ∈ S, u ≠ v ∧ ¬ G.Adj v u := by
    by_contra h
    apply hnuv
    refine ⟨hvS, ?_⟩
    intro u huS huv
    by_contra hnedge
    exact h ⟨u, huS, huv, hnedge⟩
  obtain ⟨u, huS, huv, hvunot⟩ := hexu
  have hnisou := (hno u huS).1
  have hexw : ∃ w ∈ S, G.Adj u w := by
    by_contra h
    apply hnisou
    refine ⟨huS, ?_⟩
    intro w hwS huw
    exact h ⟨w, hwS, huw⟩
  obtain ⟨w, hwS, huw⟩ := hexw
  have hu_ne_w : u ≠ w := huw.ne
  have hw_ne_v : w ≠ v := by
    intro h
    subst w
    exact hvunot huw.symm
  let A := S.filter (G.Adj v)
  let B := S.filter (G.Adj w)
  have hcardBA : B.card ≤ A.card := by
    simpa [A, B, degreeOn] using hvmax w hwS
  have hdiffcard : (B \ A).card ≤ (A \ B).card :=
    Finset.card_sdiff_le_card_sdiff_iff.mpr hcardBA
  have huBA : u ∈ B \ A := by
    simp [A, B, huS, huw.symm, hvunot]
  by_cases hvw : G.Adj v w
  · have hvBA : v ∈ B \ A := by
      simp [A, B, hvS, hvw.symm]
    have hpairSub : ({u, v} : Finset V) ⊆ B \ A := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact huBA
      · exact hvBA
    have htwoBA : 2 ≤ (B \ A).card := by
      have hcard := Finset.card_le_card hpairSub
      simpa [huv] using hcard
    have htwoAB : 2 ≤ (A \ B).card := htwoBA.trans hdiffcard
    have hwAB : w ∈ A \ B := by
      simp [A, B, hwS, hvw]
    have hposErase : 0 < ((A \ B).erase w).card := by
      rw [Finset.card_erase_of_mem hwAB]
      omega
    obtain ⟨z, hzErase⟩ := Finset.card_pos.mp hposErase
    have hzAB : z ∈ A \ B := Finset.mem_of_mem_erase hzErase
    have hz_ne_w : z ≠ w := (Finset.mem_erase.mp hzErase).1
    have hzA := (Finset.mem_sdiff.mp hzAB).1
    have hzB := (Finset.mem_sdiff.mp hzAB).2
    have hzS : z ∈ S := (Finset.mem_filter.mp hzA).1
    have hvz : G.Adj v z := (Finset.mem_filter.mp hzA).2
    have hwz : ¬ G.Adj w z := fun h => hzB (Finset.mem_filter.mpr ⟨hzS, h⟩)
    have hu_ne_z : u ≠ z := by
      intro h
      subst z
      exact hvunot hvz
    have hv_ne_z : v ≠ z := hvz.ne
    exact ⟨u, w, v, z, huw, hvz, (fun h => hvunot h.symm), hwz,
      hu_ne_w, huv, hu_ne_z, hw_ne_v, hz_ne_w.symm, hv_ne_z⟩
  · have honeBA : 1 ≤ (B \ A).card := Finset.card_pos.mpr ⟨u, huBA⟩
    have honeAB : 1 ≤ (A \ B).card := honeBA.trans hdiffcard
    obtain ⟨z, hzAB⟩ := Finset.card_pos.mp honeAB
    have hzA := (Finset.mem_sdiff.mp hzAB).1
    have hzB := (Finset.mem_sdiff.mp hzAB).2
    have hzS : z ∈ S := (Finset.mem_filter.mp hzA).1
    have hvz : G.Adj v z := (Finset.mem_filter.mp hzA).2
    have hwz : ¬ G.Adj w z := fun h => hzB (Finset.mem_filter.mpr ⟨hzS, h⟩)
    have hu_ne_z : u ≠ z := by
      intro h
      subst z
      exact hvunot hvz
    have hw_ne_z : w ≠ z := by
      intro h
      subst z
      exact hvw hvz
    have hv_ne_z : v ≠ z := hvz.ne
    exact ⟨u, w, v, z, huw, hvz, (fun h => hvunot h.symm), hwz,
      hu_ne_w, huv, hu_ne_z, hw_ne_v, hw_ne_z, hv_ne_z⟩

/-- Capacity one implies threshold, by the freshly derived two-switch and induced-subgraph
deletion argument from Round 5. -/
theorem capacity_one_threshold {d : V → ℕ} (hcap : capacity d = 1) : IsThreshold d := by
  classical
  obtain ⟨G, huniq⟩ := capacity_eq_one_iff_unique.mp hcap
  refine ⟨G, ?_⟩
  intro S hS
  by_contra hnone
  have hno : ∀ a ∈ S, ¬ IsIsolatedIn G.1 S a ∧ ¬ IsUniversalIn G.1 S a := by
    intro a haS
    constructor
    · intro ha
      exact hnone ⟨a, Or.inl ha⟩
    · intro ha
      exact hnone ⟨a, Or.inr ha⟩
  obtain ⟨u, w, v, z, huw, hvz, huv, hwz, hu_ne_w, hu_ne_v, hu_ne_z,
      hw_ne_v, hw_ne_z, hv_ne_z⟩ := exists_switch_data G.1 S hS hno
  let Hgraph := switchGraph G.1 u w v z
  have hHdeg : ∀ a, Hgraph.degree a = d a := by
    intro a
    exact (switchGraph_degree huw hvz huv hwz hu_ne_w hu_ne_v hu_ne_z hw_ne_v
      hw_ne_z hv_ne_z a).trans (G.2 a)
  let H : Realization d := ⟨Hgraph, hHdeg⟩
  have hHG : H = G := huniq H
  have hadjH : Hgraph.Adj u v := by
    exact (switchGraph_adj_u huw hvz huv hwz hu_ne_w hu_ne_v hu_ne_z hw_ne_v
      hw_ne_z hv_ne_z).2 (Or.inr rfl)
  have hadjG : G.1.Adj u v := by
    have hgraphs := congrArg (fun R : Realization d => R.1) hHG
    simpa [H, Hgraph] using hgraphs ▸ hadjH
  exact huv hadjG

/-- Round-5 capacity characterization, with both directions proved in this file. -/
theorem capacity_one_iff_threshold (d : V → ℕ) : capacity d = 1 ↔ IsThreshold d :=
  ⟨capacity_one_threshold, threshold_capacity_one⟩

/-! ### The one-edge transfer used for graphical residual up-closure -/

private def transferGraph (G : SimpleGraph V) (a b z : V) : SimpleGraph V where
  Adj x y := (G.Adj x y ∧ ¬ Pair x y a z) ∨ (x ≠ y ∧ Pair x y b z)
  symm := ⟨by
    intro x y h
    rcases h with ⟨hG, hdel⟩ | ⟨hne, hadd⟩
    · exact Or.inl ⟨hG.symm, fun h => hdel h.symm⟩
    · exact Or.inr ⟨hne.symm, hadd.symm⟩⟩
  loopless := ⟨by
    intro x h
    rcases h with ⟨hG, _⟩ | ⟨hne, _⟩
    · exact G.irrefl hG
    · exact hne rfl⟩

private theorem transferGraph_adj_a {G : SimpleGraph V} {a b z q : V}
    (hab : a ≠ b) (haz : a ≠ z) :
    (transferGraph G a b z).Adj a q ↔ G.Adj a q ∧ q ≠ z := by
  change ((G.Adj a q ∧ ¬ Pair a q a z) ∨ (a ≠ q ∧ Pair a q b z)) ↔ _
  constructor
  · intro h
    rcases h with ⟨haq, hdel⟩ | ⟨_, (⟨habEq, _⟩ | ⟨hazEq, _⟩)⟩
    · exact ⟨haq, fun h => hdel (Or.inl ⟨rfl, h⟩)⟩
    · exact False.elim (hab habEq)
    · exact False.elim (haz hazEq)
  · rintro ⟨haq, hqz⟩
    left
    refine ⟨haq, ?_⟩
    rintro (⟨_, rfl⟩ | ⟨hazEq, _⟩)
    · exact hqz rfl
    · exact haz hazEq

private theorem transferGraph_adj_b {G : SimpleGraph V} {a b z q : V}
    (hab : a ≠ b) (hbz : b ≠ z) :
    (transferGraph G a b z).Adj b q ↔ (G.Adj b q ∨ q = z) := by
  change ((G.Adj b q ∧ ¬ Pair b q a z) ∨ (b ≠ q ∧ Pair b q b z)) ↔ _
  constructor
  · intro h
    rcases h with ⟨hbq, _⟩ | ⟨_, (⟨_, hqz⟩ | ⟨hba, _⟩)⟩
    · exact Or.inl hbq
    · exact Or.inr hqz
    · exact False.elim (hbz hba)
  · intro h
    rcases h with hbq | rfl
    · left
      refine ⟨hbq, ?_⟩
      rintro (⟨hba, _⟩ | ⟨hbzEq, _⟩)
      · exact hab hba.symm
      · exact hbz hbzEq
    · exact Or.inr ⟨hbz, Or.inl ⟨rfl, rfl⟩⟩

private theorem transferGraph_adj_z {G : SimpleGraph V} {a b z q : V}
    (haz : a ≠ z) (hbz : b ≠ z) :
    (transferGraph G a b z).Adj z q ↔ (G.Adj z q ∧ q ≠ a) ∨ q = b := by
  change ((G.Adj z q ∧ ¬ Pair z q a z) ∨ (z ≠ q ∧ Pair z q b z)) ↔ _
  constructor
  · intro h
    rcases h with ⟨hzq, hdel⟩ | ⟨_, (⟨hzb, _⟩ | ⟨_, hqb⟩)⟩
    · exact Or.inl ⟨hzq, fun h => hdel (Or.inr ⟨rfl, h⟩)⟩
    · exact False.elim (hbz hzb.symm)
    · exact Or.inr hqb
  · rintro (⟨hzq, hqa⟩ | rfl)
    · left
      refine ⟨hzq, ?_⟩
      rintro (⟨hza, _⟩ | ⟨_, rfl⟩)
      · exact haz hza.symm
      · exact hqa rfl
    · exact Or.inr ⟨hbz.symm, Or.inr ⟨rfl, rfl⟩⟩

private theorem transferGraph_adj_other {G : SimpleGraph V} {a b z q x : V}
    (hxa : x ≠ a) (hxb : x ≠ b) (hxz : x ≠ z) :
    (transferGraph G a b z).Adj x q ↔ G.Adj x q := by
  simp [transferGraph, Pair, hxa, hxb, hxz]

private theorem transferGraph_degree {G : SimpleGraph V} {a b z : V}
    (hazEdge : G.Adj a z) (hbzNonedge : ¬ G.Adj b z)
    (hab : a ≠ b) (haz : a ≠ z) (hbz : b ≠ z) :
    ∀ x,
      (transferGraph G a b z).degree x =
        Function.update (Function.update (fun q => G.degree q) a (G.degree a - 1))
          b (G.degree b + 1) x := by
  classical
  intro x
  by_cases hxa : x = a
  · subst x
    have heq : (transferGraph G a b z).neighborFinset a =
        (G.neighborFinset a).erase z := by
      ext q
      simp [SimpleGraph.mem_neighborFinset, and_comm, transferGraph_adj_a hab haz]
    rw [SimpleGraph.degree, heq, Finset.card_erase_of_mem]
    · simp [Function.update, hab]
    · simpa [SimpleGraph.mem_neighborFinset] using hazEdge
  · by_cases hxb : x = b
    · subst x
      have heq : (transferGraph G a b z).neighborFinset b =
          insert z (G.neighborFinset b) := by
        ext q
        simp [SimpleGraph.mem_neighborFinset, or_comm, transferGraph_adj_b hab hbz]
      rw [SimpleGraph.degree, heq, Finset.card_insert_of_notMem]
      · simp [Function.update]
      · simpa [SimpleGraph.mem_neighborFinset] using hbzNonedge
    · by_cases hxz : x = z
      · subst x
        have heq : (transferGraph G a b z).neighborFinset z =
            insert b ((G.neighborFinset z).erase a) := by
          ext q
          simp [SimpleGraph.mem_neighborFinset, and_comm, or_comm,
            transferGraph_adj_z haz hbz]
        have haMem : a ∈ G.neighborFinset z := by
          simpa [SimpleGraph.mem_neighborFinset] using hazEdge.symm
        have hbNot : b ∉ (G.neighborFinset z).erase a := by
          have hnot : ¬ G.Adj z b := fun h => hbzNonedge h.symm
          simp [SimpleGraph.mem_neighborFinset, hnot, hab.symm]
        rw [SimpleGraph.degree, heq, Finset.card_insert_of_notMem hbNot,
          Finset.card_erase_add_one haMem]
        simp [Function.update, hxa, hxb]
      · have heq : (transferGraph G a b z).neighborFinset x = G.neighborFinset x := by
          ext q
          simp [SimpleGraph.mem_neighborFinset, transferGraph_adj_other hxa hxb hxz]
        rw [SimpleGraph.degree, heq]
        simp [Function.update, hxa, hxb]

/-- Constructive graphical down-transfer, including the actual exchanged neighbor. -/
theorem graphical_down_transfer {d : V → ℕ} (hd : Graphical d) {a b : V}
    (hgap : d b + 2 ≤ d a) :
    Graphical (Function.update (Function.update d a (d a - 1)) b (d b + 1)) := by
  classical
  obtain ⟨G, hG⟩ := hd
  have hab : a ≠ b := by
    intro h
    subst b
    omega
  let A := (G.neighborFinset a).erase b
  let B := G.neighborFinset b
  have hA : d a - 1 ≤ A.card := by
    dsimp [A]
    by_cases hba : b ∈ G.neighborFinset a
    · rw [Finset.card_erase_of_mem hba, SimpleGraph.card_neighborFinset_eq_degree, hG]
    · rw [Finset.erase_eq_of_notMem hba, SimpleGraph.card_neighborFinset_eq_degree, hG]
      exact Nat.sub_le _ _
  have hB : B.card = d b := by
    dsimp [B]
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using hG b
  have hnsub : ¬ A ⊆ B := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨z, hzA, hzB⟩ := Finset.not_subset.mp hnsub
  have hza : G.Adj a z := by
    simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_erase.mp hzA).2
  have hzb : ¬ G.Adj b z := by
    intro h
    exact hzB (by simpa [B, SimpleGraph.mem_neighborFinset] using h)
  have haz : a ≠ z := hza.ne
  have hbz : b ≠ z := by
    exact (Finset.mem_erase.mp hzA).1.symm
  refine ⟨transferGraph G a b z, ?_⟩
  intro x
  rw [transferGraph_degree hza hzb hab haz hbz x]
  simp only [hG]

/-! ### Threshold dominance in the one transfer form used by profiles -/

/-- A strict dominance raise transfers one unit from a no-larger entry `b` to `a`. -/
def DominanceStep (d e : V → ℕ) : Prop :=
  ∃ a b, a ≠ b ∧ d b ≤ d a ∧ e a = d a + 1 ∧ d b = e b + 1 ∧
    ∀ q, q ≠ a → q ≠ b → e q = d q

private theorem unique_realization_nested {d : V → ℕ} (hcap : capacity d = 1)
    (G : Realization d) {a b z : V} (hdeg : d b ≤ d a)
    (hbz : G.1.Adj b z) (haz : ¬ G.1.Adj a z) (haz' : a ≠ z) : False := by
  classical
  have hab : a ≠ b := by
    intro h
    subst b
    exact haz hbz
  have hbz' : b ≠ z := hbz.ne
  let A := G.1.neighborFinset a
  let B := G.1.neighborFinset b
  have hcard : B.card ≤ A.card := by
    simpa [A, B, SimpleGraph.card_neighborFinset_eq_degree, G.2] using hdeg
  have hzBA : z ∈ B \ A := by
    apply Finset.mem_sdiff.mpr
    constructor
    · simpa [B, SimpleGraph.mem_neighborFinset] using hbz
    · intro h
      exact haz (by simpa [A, SimpleGraph.mem_neighborFinset] using h)
  have hdiff : (B \ A).card ≤ (A \ B).card :=
    Finset.card_sdiff_le_card_sdiff_iff.mpr hcard
  have ht : ∃ t, t ∈ A \ B ∧ t ≠ b := by
    by_cases habEdge : G.1.Adj a b
    · have haBA : a ∈ B \ A := by
        apply Finset.mem_sdiff.mpr
        constructor
        · simpa [B, SimpleGraph.mem_neighborFinset] using habEdge.symm
        · simp [A, SimpleGraph.mem_neighborFinset]
      have hpair : ({a, z} : Finset V) ⊆ B \ A := by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl
        · exact haBA
        · exact hzBA
      have htwo : 2 ≤ (A \ B).card := by
        have hc := (Finset.card_le_card hpair).trans hdiff
        simpa [haz'] using hc
      have hbAB : b ∈ A \ B := by
        simp [A, B, SimpleGraph.mem_neighborFinset, habEdge]
      have hpos : 0 < ((A \ B).erase b).card := by
        rw [Finset.card_erase_of_mem hbAB]
        omega
      obtain ⟨t, ht⟩ := Finset.card_pos.mp hpos
      exact ⟨t, Finset.mem_of_mem_erase ht, (Finset.mem_erase.mp ht).1⟩
    · have hposBA : 0 < (B \ A).card := Finset.card_pos.mpr ⟨z, hzBA⟩
      have hone : 1 ≤ (A \ B).card := by omega
      obtain ⟨t, ht⟩ := Finset.card_pos.mp hone
      have htA := (Finset.mem_sdiff.mp ht).1
      have ht_ne_b : t ≠ b := by
        intro h
        subst t
        exact habEdge (by simpa [A, SimpleGraph.mem_neighborFinset] using htA)
      exact ⟨t, ht, ht_ne_b⟩
  obtain ⟨t, htAB, ht_ne_b⟩ := ht
  have hat : G.1.Adj a t := by
    simpa [A, SimpleGraph.mem_neighborFinset] using (Finset.mem_sdiff.mp htAB).1
  have hbt : ¬ G.1.Adj b t := by
    intro h
    exact (Finset.mem_sdiff.mp htAB).2 (by simpa [B, SimpleGraph.mem_neighborFinset] using h)
  have hz_ne_t : z ≠ t := by
    intro h
    subst t
    exact hbt hbz
  have ha_ne_t : a ≠ t := hat.ne
  let Hgraph := switchGraph G.1 b z t a
  have hHdeg : ∀ q, Hgraph.degree q = d q := by
    intro q
    exact (switchGraph_degree hbz hat.symm hbt (fun h => haz h.symm)
      hbz' ht_ne_b.symm hab.symm hz_ne_t haz'.symm ha_ne_t.symm q).trans (G.2 q)
  let H : Realization d := ⟨Hgraph, hHdeg⟩
  obtain ⟨U, huniq⟩ := capacity_eq_one_iff_unique.mp hcap
  have hGU : G = U := huniq G
  have hHU : H = U := huniq H
  have hHG : H = G := hHU.trans hGU.symm
  have hHaz : Hgraph.Adj a z := by
    have h := switchGraph_adj_z (G := G.1) (u := b) (w := z) (v := t) (z := a) (q := z)
      hbz hat.symm hbt (fun h => haz h.symm) hbz' ht_ne_b.symm hab.symm hz_ne_t
        haz'.symm ha_ne_t.symm
    exact h.2 (Or.inr rfl)
  have hGaz : G.1.Adj a z := by
    have heq := congrArg (fun R : Realization d => R.1) hHG
    simpa [H, Hgraph] using heq ▸ hHaz
  exact haz hGaz

/-- The exact strict-balancing obstruction used in Lemma 2.3: a graphical strict raise
cannot balance in one step to a capacity-one degree function. -/
theorem no_graphical_dominance_step_into_capacity_one {d e : V → ℕ}
    (hcap : capacity d = 1) (he : Graphical e) (hed : DominanceStep d e) : False := by
  classical
  obtain ⟨a, b, hab, hba, hea, heb, hother⟩ := hed
  obtain ⟨E, hE⟩ := he
  have hgap : e b + 2 ≤ e a := by omega
  let A := (E.neighborFinset a).erase b
  let B := E.neighborFinset b
  have hA : e a - 1 ≤ A.card := by
    dsimp [A]
    by_cases hbaEdge : b ∈ E.neighborFinset a
    · rw [Finset.card_erase_of_mem hbaEdge, SimpleGraph.card_neighborFinset_eq_degree, hE]
    · rw [Finset.erase_eq_of_notMem hbaEdge, SimpleGraph.card_neighborFinset_eq_degree, hE]
      exact Nat.sub_le _ _
  have hB : B.card = e b := by
    dsimp [B]
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using hE b
  have hnsub : ¬ A ⊆ B := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨z, hzA, hzB⟩ := Finset.not_subset.mp hnsub
  have hazEdge : E.Adj a z := by
    simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_erase.mp hzA).2
  have hbzNonedge : ¬ E.Adj b z := by
    intro h
    exact hzB (by simpa [B, SimpleGraph.mem_neighborFinset] using h)
  have haz : a ≠ z := hazEdge.ne
  have hbz : b ≠ z := (Finset.mem_erase.mp hzA).1.symm
  let Hgraph := transferGraph E a b z
  have hHdeg : ∀ q, Hgraph.degree q = d q := by
    intro q
    rw [transferGraph_degree hazEdge hbzNonedge hab haz hbz q]
    by_cases hqa : q = a
    · subst q
      simp [Function.update, hab, hE, hea]
    · by_cases hqb : q = b
      · subst q
        simp [Function.update, hE, heb]
      · simp [Function.update, hqa, hqb, hE, hother q hqa hqb]
  let H : Realization d := ⟨Hgraph, hHdeg⟩
  have hHbz : Hgraph.Adj b z :=
    (transferGraph_adj_b hab hbz).2 (Or.inr rfl)
  have hHaz : ¬ Hgraph.Adj a z := by
    rw [transferGraph_adj_a hab haz]
    simp
  exact unique_realization_nested hcap H hba hHbz hHaz haz

/-- Strict dominance is the transitive closure of unit dominance raises. -/
def StrictlyDominates (e d : V → ℕ) : Prop := Relation.TransGen DominanceStep d e

/-! ### Graphical residual families -/

/-- Interface supplied by the printed degree classes.  A dominance cover is an upward
unit profile move; on residual degrees it is exactly one strict balancing transfer. -/
structure ResidualSystem {s : ℕ} (c : Fin s → ℕ) (r : ℕ) (V : Type u) where
  residual : Profile c r → V → ℕ
  cover_balance : ∀ ⦃x y : Profile c r⦄, x ⋖ y →
    DominanceStep (residual y) (residual x)

namespace ResidualSystem

variable {s : ℕ} {c : Fin s → ℕ} {r : ℕ}

/-- Admissibility means graphicality of the labeled residual degree function. -/
def Admissible (R : ResidualSystem c r V) (x : Profile c r) : Prop :=
  Graphical (R.residual x)

private theorem graphical_of_dominanceStep {d e : V → ℕ}
    (he : Graphical e) (hstep : DominanceStep d e) : Graphical d := by
  classical
  obtain ⟨a, b, hab, hba, hea, heb, hother⟩ := hstep
  have hgap : e b + 2 ≤ e a := by omega
  have hgraph := graphical_down_transfer he hgap
  convert hgraph using 1
  funext q
  by_cases hqa : q = a
  · subst q
    simp [Function.update, hab, hea]
  · by_cases hqb : q = b
    · subst q
      simp [Function.update, heb]
    · simp [Function.update, hqa, hqb, hother q hqa hqb]

/-- Lemma 2.1 in transfer-generated form: a threshold degree function is dominance-maximal
among graphical degree functions.  Reading a dominance chain backwards, each reverse
balancing transfer is graphical, so the first strict raise already contradicts capacity one. -/
theorem threshold_dominance_maximal {d e : V → ℕ}
    (hd : IsThreshold d) (he : Graphical e) : ¬ StrictlyDominates e d := by
  intro hdom
  have hcap : capacity d = 1 := threshold_capacity_one hd
  induction hdom with
  | single h => exact no_graphical_dominance_step_into_capacity_one hcap he h
  | tail hxy hyz ih =>
      have hmiddle := graphical_of_dominanceStep he hyz
      exact ih hmiddle

theorem admissible_of_covBy (R : ResidualSystem c r V) {x y : Profile c r}
    (hx : R.Admissible x) (hxy : x ⋖ y) : R.Admissible y :=
  graphical_of_dominanceStep hx (R.cover_balance hxy)

/-- The graphical-residual up-closure: admissible profiles form an upper ideal in prefix
dominance.  Finite strong atomicity supplies a chain of unit profile moves. -/
theorem admissible_upperIdeal (R : ResidualSystem c r V) :
    ∀ ⦃x y : Profile c r⦄, R.Admissible x → x ≤ y → R.Admissible y := by
  classical
  intro x
  induction x using WellFoundedGT.induction with
  | ind x ih =>
    intro y hx hxy
    by_cases hEq : x = y
    · simpa [hEq] using hx
    · have hlt : x < y := lt_of_le_of_ne hxy hEq
      obtain ⟨z, hxz, hzy⟩ := exists_covBy_le_of_lt hlt
      have hz := R.admissible_of_covBy hx hxz
      exact ih z hxz.lt hz hzy

/-- Capacity-one residuals are minimal admissible profiles.  If a strict predecessor
existed, take the final dominance cover: its graphical residual would be a strict raise
balancing in one step to a capacity-one residual, forbidden by the two-switch theorem. -/
theorem capacityOne_minimal (R : ResidualSystem c r V) {t : Profile c r}
    (htA : R.Admissible t) (ht1 : capacity (R.residual t) = 1) :
    ∀ ⦃y⦄, R.Admissible y → y ≤ t → t ≤ y := by
  classical
  intro y hy hyt
  by_contra hnot
  have hne : y ≠ t := fun h => hnot (h ▸ le_rfl)
  have hlt : y < t := lt_of_le_of_ne hyt hne
  obtain ⟨z, hyz, hzt⟩ := exists_le_covBy_of_lt hlt
  have hz : R.Admissible z := R.admissible_upperIdeal hy hyz
  exact no_graphical_dominance_step_into_capacity_one ht1 hz (R.cover_balance hzt)

end ResidualSystem

end Graphicality

/-! ## 3. Upper ideals and the three parts of Theorem 4.1 -/

section Separator

variable {s : ℕ} {c : Fin s → ℕ} {r : ℕ}

local notation "P₀" => Profile c r

/-- An upper ideal in the printed dominance order. -/
def IsUpperIdeal (A : P₀ → Prop) : Prop :=
  ∀ ⦃x y⦄, A x → x ≤ y → A y

/-- Minimality inside a family, without requiring global minimality in the whole box. -/
def IsMinimalIn (A : P₀ → Prop) (x : P₀) : Prop :=
  A x ∧ ∀ ⦃y⦄, A y → y ≤ x → x ≤ y

/-- Reachability in the quotient induced by a predicate `A`. -/
def ReachWithin (Adj : P₀ → P₀ → Prop) (A : P₀ → Prop) (x y : P₀) : Prop :=
  Relation.ReflTransGen (fun p q => A p ∧ A q ∧ Adj p q) x y

/-- Connectedness of an induced quotient. -/
def QuotientConnected (Adj : P₀ → P₀ → Prop) (A : P₀ → Prop) : Prop :=
  ∀ ⦃x⦄, A x → ∀ ⦃y⦄, A y → ReachWithin Adj A x y

/-- A path whose non-endpoints avoid `C`: all path vertices lie in the core or are one of
the two named endpoints. -/
def InternallyAvoids (Adj : P₀ → P₀ → Prop) (C : P₀ → Prop) (x y : P₀) : Prop :=
  ReachWithin Adj (fun z => ¬ C z ∨ z = x ∨ z = y) x y

private theorem reach_boxTop_of_upper
    (Adj : P₀ → P₀ → Prop) (hAdjCover : ∀ ⦃x y : P₀⦄, x ⋖ y → Adj x y)
    (A : P₀ → Prop) (hA : IsUpperIdeal A) (hr : r ≤ ∑ i, c i)
    {x : P₀} (hx : A x) :
    Relation.ReflTransGen (fun p q => A p ∧ A q ∧ Adj p q) x (Profile.boxTop c r hr) := by
  classical
  induction x using WellFoundedGT.induction with
  | ind x ih =>
    by_cases hxt : x = Profile.boxTop c r hr
    · subst x
      exact Relation.ReflTransGen.refl
    · have hxlt : x < Profile.boxTop c r hr :=
        lt_of_le_of_ne (Profile.le_boxTop x hr) hxt
      obtain ⟨y, hxy, hyt⟩ := exists_covBy_le_of_lt hxlt
      have hyA : A y := hA hx hxy.le
      exact Relation.ReflTransGen.head ⟨hx, hyA, hAdjCover hxy⟩
        (ih y hxy.lt hyA)

private theorem reachWithin_symm
    (Adj : P₀ → P₀ → Prop) (hAdjSymm : ∀ ⦃x y⦄, Adj x y → Adj y x)
    (A : P₀ → Prop) {x y : P₀} : ReachWithin Adj A x y → ReachWithin Adj A y x := by
  intro h
  have hs := Relation.ReflTransGen.swap h
  exact hs.mono fun a b hab => ⟨hab.2.1, hab.1, hAdjSymm hab.2.2⟩

/-- Every nonempty upper ideal in the profile box has a connected quotient.  The proof
chains each profile through dominance covers to the greedy top; every cover is required to
be an actual quotient edge. -/
theorem upperIdeal_quotientConnected
    (Adj : P₀ → P₀ → Prop) (hAdjSymm : ∀ ⦃x y⦄, Adj x y → Adj y x)
    (hAdjCover : ∀ ⦃x y : P₀⦄, x ⋖ y → Adj x y)
    (A : P₀ → Prop) (hA : IsUpperIdeal A) (hr : r ≤ ∑ i, c i) :
    QuotientConnected Adj A := by
  intro x hx y hy
  have hxTop := reach_boxTop_of_upper Adj hAdjCover A hA hr hx
  have hyTop := reach_boxTop_of_upper Adj hAdjCover A hA hr hy
  exact hxTop.trans (reachWithin_symm Adj hAdjSymm A hyTop)

/-- Removing any collection of minimal members of an upper ideal leaves an upper ideal. -/
theorem upperIdeal_diff_minimals
    {A C : P₀ → Prop} (hA : IsUpperIdeal A)
    (hCmin : ∀ ⦃x⦄, C x → IsMinimalIn A x) :
    IsUpperIdeal (fun x => A x ∧ ¬ C x) := by
  intro x y hx hxy
  refine ⟨hA hx.1 hxy, ?_⟩
  intro hCy
  have hyx : y ≤ x := (hCmin hCy).2 hx.1 hxy
  have hxyEq : x = y := le_antisymm hxy hyx
  exact hx.2 (hxyEq ▸ hCy)

/-- The endpoint-augmented core remains an upper ideal. -/
private theorem upperIdeal_endpoint_core
    {A C : P₀ → Prop} (hA : IsUpperIdeal A)
    (hCmin : ∀ ⦃x⦄, C x → IsMinimalIn A x)
    {x y : P₀} (hx : A x) (hy : A y) :
    IsUpperIdeal (fun z => A z ∧ (¬ C z ∨ z = x ∨ z = y)) := by
  intro z q hz hzq
  refine ⟨hA hz.1 hzq, ?_⟩
  rcases hz.2 with hnC | hzx | hzy
  · left
    intro hCq
    have hqz := (hCmin hCq).2 hz.1 hzq
    exact hnC (le_antisymm hzq hqz ▸ hCq)
  · by_cases hqx : q = x
    · exact Or.inr (Or.inl hqx)
    · left
      intro hCq
      have hxq : x ≤ q := hzx ▸ hzq
      have hqx' := (hCmin hCq).2 hx hxq
      exact hqx (le_antisymm hqx' hxq)
  · by_cases hqy : q = y
    · exact Or.inr (Or.inr hqy)
    · left
      intro hCq
      have hyq : y ≤ q := hzy ▸ hzq
      have hqy' := (hCmin hCq).2 hy hyq
      exact hqy (le_antisymm hqy' hyq)

/-- Theorem 4.1(1): deleting all capacity-one/minimal profiles leaves a connected upper
ideal whenever it is nonempty. -/
theorem capacitySeparator_part1
    (Adj : P₀ → P₀ → Prop) (hAdjSymm : ∀ ⦃x y⦄, Adj x y → Adj y x)
    (hAdjCover : ∀ ⦃x y : P₀⦄, x ⋖ y → Adj x y)
    {A C : P₀ → Prop} (hA : IsUpperIdeal A)
    (hCmin : ∀ ⦃x⦄, C x → IsMinimalIn A x) (hr : r ≤ ∑ i, c i) :
    IsUpperIdeal (fun x => A x ∧ ¬ C x) ∧
      QuotientConnected Adj (fun x => A x ∧ ¬ C x) := by
  have hB := upperIdeal_diff_minimals hA hCmin
  exact ⟨hB, upperIdeal_quotientConnected Adj hAdjSymm hAdjCover _ hB hr⟩

/-- Theorem 4.1(2): every endpoint pair has a quotient path whose internal vertices avoid
the whole capacity-one family. -/
theorem capacitySeparator_part2
    (Adj : P₀ → P₀ → Prop) (hAdjSymm : ∀ ⦃x y⦄, Adj x y → Adj y x)
    (hAdjCover : ∀ ⦃x y : P₀⦄, x ⋖ y → Adj x y)
    {A C : P₀ → Prop} (hA : IsUpperIdeal A)
    (hCmin : ∀ ⦃x⦄, C x → IsMinimalIn A x) (hr : r ≤ ∑ i, c i)
    {x y : P₀} (hx : A x) (hy : A y) : InternallyAvoids Adj C x y := by
  let E : P₀ → Prop := fun z => A z ∧ (¬ C z ∨ z = x ∨ z = y)
  have hE : IsUpperIdeal E := upperIdeal_endpoint_core hA hCmin hx hy
  have hxE : E x := ⟨hx, Or.inr (Or.inl rfl)⟩
  have hyE : E y := ⟨hy, Or.inr (Or.inr rfl)⟩
  have hpath := upperIdeal_quotientConnected Adj hAdjSymm hAdjCover E hE hr hxE hyE
  exact hpath.mono fun p q hpq => ⟨hpq.1.2, hpq.2.1.2, hpq.2.2⟩

/-- Theorem 4.1(3): a capacity-one profile distinct from both endpoints cannot separate
those endpoints. -/
theorem capacitySeparator_part3_no_internal_separator
    (Adj : P₀ → P₀ → Prop) (hAdjSymm : ∀ ⦃x y⦄, Adj x y → Adj y x)
    (hAdjCover : ∀ ⦃x y : P₀⦄, x ⋖ y → Adj x y)
    {A C : P₀ → Prop} (hA : IsUpperIdeal A)
    (hCmin : ∀ ⦃x⦄, C x → IsMinimalIn A x) (hr : r ≤ ∑ i, c i)
    {t x y : P₀} (ht : C t) (hx : A x) (hy : A y) (htx : t ≠ x) (hty : t ≠ y) :
    ReachWithin Adj (fun z => z ≠ t) x y := by
  have hpath := capacitySeparator_part2 Adj hAdjSymm hAdjCover hA hCmin hr hx hy
  exact hpath.mono fun p q hpq => by
    refine ⟨?_, ?_, hpq.2.2⟩
    · rcases hpq.1 with hn | rfl | rfl
      · exact fun h => hn (h ▸ ht)
      · exact htx.symm
      · exact hty.symm
    · rcases hpq.2.1 with hn | rfl | rfl
      · exact fun h => hn (h ▸ ht)
      · exact htx.symm
      · exact hty.symm

/-- Capacity-one part of an admissible graphical-residual system. -/
def ResidualCapacityOne {V : Type u} [Fintype V] [DecidableEq V]
    (R : ResidualSystem c r V) (x : P₀) : Prop :=
  R.Admissible x ∧ capacity (R.residual x) = 1

/-- Theorem 4.1(1), instantiated with graphical admissibility and labeled capacity. -/
theorem residual_capacitySeparator_part1
    {V : Type u} [Fintype V] [DecidableEq V] (R : ResidualSystem c r V)
    (Adj : P₀ → P₀ → Prop) (hAdjSymm : ∀ ⦃x y⦄, Adj x y → Adj y x)
    (hAdjCover : ∀ ⦃x y : P₀⦄, x ⋖ y → Adj x y) (hr : r ≤ ∑ i, c i) :
    IsUpperIdeal (fun x => R.Admissible x ∧ ¬ ResidualCapacityOne R x) ∧
      QuotientConnected Adj (fun x => R.Admissible x ∧ ¬ ResidualCapacityOne R x) := by
  apply capacitySeparator_part1 Adj hAdjSymm hAdjCover R.admissible_upperIdeal _ hr
  intro x hx
  exact ⟨hx.1, R.capacityOne_minimal hx.1 hx.2⟩

/-- Theorem 4.1(2), instantiated with graphical admissibility and labeled capacity. -/
theorem residual_capacitySeparator_part2
    {V : Type u} [Fintype V] [DecidableEq V] (R : ResidualSystem c r V)
    (Adj : P₀ → P₀ → Prop) (hAdjSymm : ∀ ⦃x y⦄, Adj x y → Adj y x)
    (hAdjCover : ∀ ⦃x y : P₀⦄, x ⋖ y → Adj x y) (hr : r ≤ ∑ i, c i)
    {x y : P₀} (hx : R.Admissible x) (hy : R.Admissible y) :
    InternallyAvoids Adj (ResidualCapacityOne R) x y := by
  apply capacitySeparator_part2 Adj hAdjSymm hAdjCover R.admissible_upperIdeal _ hr hx hy
  intro t ht
  exact ⟨ht.1, R.capacityOne_minimal ht.1 ht.2⟩

/-- Theorem 4.1(3), instantiated with graphical admissibility and labeled capacity. -/
theorem residual_capacitySeparator_part3_no_internal_separator
    {V : Type u} [Fintype V] [DecidableEq V] (R : ResidualSystem c r V)
    (Adj : P₀ → P₀ → Prop) (hAdjSymm : ∀ ⦃x y⦄, Adj x y → Adj y x)
    (hAdjCover : ∀ ⦃x y : P₀⦄, x ⋖ y → Adj x y) (hr : r ≤ ∑ i, c i)
    {t x y : P₀} (ht : ResidualCapacityOne R t)
    (hx : R.Admissible x) (hy : R.Admissible y) (htx : t ≠ x) (hty : t ≠ y) :
    ReachWithin Adj (fun z => z ≠ t) x y := by
  apply capacitySeparator_part3_no_internal_separator Adj hAdjSymm hAdjCover
    R.admissible_upperIdeal _ hr ht hx hy htx hty
  intro q hq
  exact ⟨hq.1, R.capacityOne_minimal hq.1 hq.2⟩

end Separator

/-! ## Axiom audit -/

#print axioms capacityPrefix_zero
#print axioms capacityPrefix_succ
#print axioms capacityPrefix_last
#print axioms Profile.ext
#print axioms Profile.join_prefix
#print axioms Profile.meet_prefix
#print axioms Profile.prefix_le_capacity
#print axioms Profile.prefix_le_total
#print axioms Profile.le_boxTop
#print axioms Profile.sup_inf_distrib
#print axioms Profile.inf_sup_distrib
#print axioms Profile.filter_inter
#print axioms Profile.filter_eq_singleton_iff
#print axioms graphical_iff_realization_nonempty
#print axioms capacity_eq_one_iff_unique
#print axioms degreeOn_univ
#print axioms degreeOn_erase
#print axioms thresholdGraph_rigid
#print axioms threshold_capacity_one
#print axioms capacity_one_threshold
#print axioms capacity_one_iff_threshold
#print axioms graphical_down_transfer
#print axioms no_graphical_dominance_step_into_capacity_one
#print axioms ResidualSystem.threshold_dominance_maximal
#print axioms ResidualSystem.admissible_of_covBy
#print axioms ResidualSystem.admissible_upperIdeal
#print axioms ResidualSystem.capacityOne_minimal
#print axioms upperIdeal_diff_minimals
#print axioms upperIdeal_quotientConnected
#print axioms capacitySeparator_part1
#print axioms capacitySeparator_part2
#print axioms capacitySeparator_part3_no_internal_separator
#print axioms residual_capacitySeparator_part1
#print axioms residual_capacitySeparator_part2
#print axioms residual_capacitySeparator_part3_no_internal_separator

end Brualdi.RealizationGraph.SeparatorTheorem
