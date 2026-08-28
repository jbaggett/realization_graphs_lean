/-
Copyright (c) 2026 Jeffrey S. Baggett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey S. Baggett
-/
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Init.Omega

/-!
# Bounded-composition principal filters

This file is the concrete finite-vector layer used by the sequel's dodge
arguments.  A profile is a vector `Fin s → ℕ`; `filter c r m` consists of
the profiles bounded by `c`, of total `r`, and above `m` in dominance order.

The definitions deliberately expose every predicate appearing in
`next_paper/explore/buffer_lemma.md`: coordinate ranges and activity, unit
transfers, effective dimension, slices, and the Ferrers graph of `(m,c-m)`.
-/

set_option autoImplicit false
set_option linter.style.nativeDecide false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open scoped BigOperators

namespace Brualdi.RealizationGraph.BoundedComposition

/-- Sum of the coordinates strictly before the boundary `k`.  Boundary
`0` is the empty prefix and boundary `s` is the total. -/
def prefixSum {s : ℕ} (x : Fin s → ℕ) (k : Fin (s + 1)) : ℕ :=
  ∑ i : Fin s, if i.val < k.val then x i else 0

@[simp] theorem prefixSum_zero {s : ℕ} (x : Fin s → ℕ) : prefixSum x 0 = 0 := by
  simp [prefixSum]

@[simp] theorem prefixSum_last {s : ℕ} (x : Fin s → ℕ) :
    prefixSum x (Fin.last s) = ∑ i, x i := by
  classical
  simp [prefixSum, Fin.is_lt]

/-- Dominance order on bounded compositions, expressed in prefix sums. -/
def Dominates {s : ℕ} (m x : Fin s → ℕ) : Prop :=
  ∀ k : Fin (s + 1), prefixSum m k ≤ prefixSum x k

theorem dominates_refl {s : ℕ} (x : Fin s → ℕ) : Dominates x x := by
  intro k
  exact le_rfl

theorem dominates_trans {s : ℕ} {x y z : Fin s → ℕ}
    (hxy : Dominates x y) (hyz : Dominates y z) : Dominates x z := by
  intro k
  exact (hxy k).trans (hyz k)

/-- Coordinatewise cap predicate. -/
def WithinCap {s : ℕ} (c x : Fin s → ℕ) : Prop := ∀ i, x i ≤ c i

/-- The finite box `0 ≤ x ≤ c`, represented as a `Finset` of natural vectors. -/
noncomputable def boundedVectors {s : ℕ} (c : Fin s → ℕ) : Finset (Fin s → ℕ) := by
  classical
  exact (Finset.univ : Finset ((i : Fin s) → Fin (c i + 1))).image
    (fun x i ↦ (x i).val)

theorem mem_boundedVectors_iff {s : ℕ} {c x : Fin s → ℕ} :
    x ∈ boundedVectors c ↔ WithinCap c x := by
  classical
  constructor
  · intro hx i
    simp only [boundedVectors, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨y, rfl⟩ := hx
    exact Nat.le_of_lt_succ (y i).isLt
  · intro hx
    let y : (i : Fin s) → Fin (c i + 1) := fun i ↦
      ⟨x i, Nat.lt_succ_of_le (hx i)⟩
    apply Finset.mem_image.mpr
    refine ⟨y, Finset.mem_univ _, ?_⟩
    funext i
    rfl

/-- Feasibility in the principal dominance filter `L(c,r;m)`. -/
def Feasible {s : ℕ} (c : Fin s → ℕ) (r : ℕ) (m x : Fin s → ℕ) : Prop :=
  WithinCap c x ∧ (∑ i, x i) = r ∧ Dominates m x

/-- The bounded-composition principal filter `L(c,r;m)`. -/
noncomputable def filter {s : ℕ} (c : Fin s → ℕ) (r : ℕ)
    (m : Fin s → ℕ) : Finset (Fin s → ℕ) := by
  classical
  exact (boundedVectors c).filter fun x ↦
    (∑ i, x i) = r ∧ Dominates m x

theorem mem_filter_iff {s : ℕ} {c m x : Fin s → ℕ} {r : ℕ} :
    x ∈ filter c r m ↔ Feasible c r m x := by
  classical
  simp [filter, Feasible, mem_boundedVectors_iff]

theorem base_mem_filter {s : ℕ} {c m : Fin s → ℕ} {r : ℕ}
    (hcap : WithinCap c m) (htotal : (∑ i, m i) = r) : m ∈ filter c r m := by
  rw [mem_filter_iff]
  exact ⟨hcap, htotal, dominates_refl m⟩

/-- A directed unit transfer sends one unit from `q` to `p`.  The coordinate
equations avoid truncated-subtraction artifacts. -/
def DirectedTransfer {s : ℕ} (x y : Fin s → ℕ) (p q : Fin s) : Prop :=
  p ≠ q ∧ y p = x p + 1 ∧ x q = y q + 1 ∧
    ∀ i, i ≠ p → i ≠ q → y i = x i

/-- Undirected unit-transfer adjacency. -/
def UnitTransfer {s : ℕ} (x y : Fin s → ℕ) : Prop :=
  (∃ p q, DirectedTransfer x y p q) ∨ ∃ p q, DirectedTransfer y x p q

theorem unitTransfer_symm {s : ℕ} {x y : Fin s → ℕ} :
    UnitTransfer x y → UnitTransfer y x := by
  rintro (h | h)
  · exact Or.inr h
  · exact Or.inl h

theorem directedTransfer_ne {s : ℕ} {x y : Fin s → ℕ} {p q : Fin s}
    (h : DirectedTransfer x y p q) : x ≠ y := by
  obtain ⟨_, hp, _, _⟩ := h
  intro hxy
  rw [hxy] at hp
  omega

theorem unitTransfer_irrefl {s : ℕ} (x : Fin s → ℕ) : ¬ UnitTransfer x x := by
  rintro (h | h) <;> obtain ⟨p, q, hpq⟩ := h <;>
    exact directedTransfer_ne hpq rfl

/-- The unit-transfer graph induced on a principal filter. -/
noncomputable def transferGraph {s : ℕ} (c : Fin s → ℕ) (r : ℕ)
    (m : Fin s → ℕ) : SimpleGraph {x // x ∈ filter c r m} where
  Adj x y := UnitTransfer x.1 y.1
  symm := by
    constructor
    intro x y h
    exact unitTransfer_symm h
  loopless := by
    constructor
    intro x h
    exact unitTransfer_irrefl x.1 h

/-- Values attained by coordinate `q` in the filter. -/
noncomputable def attainedRange {s : ℕ} (c : Fin s → ℕ) (r : ℕ)
    (m : Fin s → ℕ) (q : Fin s) : Finset ℕ := by
  classical
  exact (filter c r m).image fun x ↦ x q

theorem mem_attainedRange_iff {s : ℕ} {c m : Fin s → ℕ} {r : ℕ}
    {q : Fin s} {t : ℕ} :
    t ∈ attainedRange c r m q ↔ ∃ x ∈ filter c r m, x q = t := by
  classical
  simp [attainedRange]

/-- A coordinate is active when it takes at least two values. -/
def Active {s : ℕ} (c : Fin s → ℕ) (r : ℕ) (m : Fin s → ℕ)
    (q : Fin s) : Prop :=
  ∃ x ∈ filter c r m, ∃ y ∈ filter c r m, x q ≠ y q

/-- The active coordinates, used instead of physically deleting fixed ones. -/
noncomputable def activeCoordinates {s : ℕ} (c : Fin s → ℕ) (r : ℕ)
    (m : Fin s → ℕ) : Finset (Fin s) := by
  classical
  exact Finset.univ.filter fun q ↦ Active c r m q

/-- Effective dimension: the number of non-fixed coordinates. -/
noncomputable def effectiveDimension {s : ℕ} (c : Fin s → ℕ) (r : ℕ)
    (m : Fin s → ℕ) : ℕ :=
  (activeCoordinates c r m).card

theorem mem_activeCoordinates_iff {s : ℕ} {c m : Fin s → ℕ} {r : ℕ} {q : Fin s} :
    q ∈ activeCoordinates c r m ↔ Active c r m q := by
  classical
  simp [activeCoordinates]

/-- The slice at coordinate `q` and value `t`. -/
noncomputable def slice {s : ℕ} (c : Fin s → ℕ) (r : ℕ) (m : Fin s → ℕ)
    (q : Fin s) (t : ℕ) : Finset (Fin s → ℕ) := by
  classical
  exact (filter c r m).filter fun x ↦ x q = t

theorem mem_slice_iff {s : ℕ} {c m : Fin s → ℕ} {r t : ℕ} {q : Fin s}
    {x : Fin s → ℕ} :
    x ∈ slice c r m q t ↔ x ∈ filter c r m ∧ x q = t := by
  classical
  simp [slice]

/-- Mass strictly before a coordinate. -/
def massBefore {s : ℕ} (x : Fin s → ℕ) (q : Fin s) : ℕ :=
  ∑ j : Fin s, if j.val < q.val then x j else 0

/-- Spare capacity strictly before `q`, for `b = c-m`. -/
def spareBefore {s : ℕ} (c m : Fin s → ℕ) (q : Fin s) : ℕ :=
  ∑ j : Fin s, if j.val < q.val then c j - m j else 0

/-- Base mass strictly after `q`. -/
def massAfter {s : ℕ} (m : Fin s → ℕ) (q : Fin s) : ℕ :=
  ∑ j : Fin s, if q.val < j.val then m j else 0

theorem total_eq_massBefore_add_self_add_massAfter {s : ℕ} (x : Fin s → ℕ)
    (q : Fin s) :
    (∑ i, x i) = massBefore x q + x q + massAfter x q := by
  classical
  unfold massBefore massAfter
  calc
    (∑ i, x i) = ∑ i,
        ((if i.val < q.val then x i else 0) +
          ((if i = q then x q else 0) + if q.val < i.val then x i else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hiq : i = q
      · subst i
        simp
      · have hlt_or_gt : i.val < q.val ∨ q.val < i.val := by
          have hne : i.val ≠ q.val := fun h ↦ hiq (Fin.ext h)
          omega
        rcases hlt_or_gt with hlt | hgt
        · have hn : ¬ q.val < i.val := by omega
          simp [hlt, hn, hiq]
        · have hn : ¬ i.val < q.val := by omega
          simp [hgt, hn, hiq]
    _ = (∑ i, if i.val < q.val then x i else 0) +
          ((∑ i, if i = q then x q else 0) +
            ∑ i, if q.val < i.val then x i else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = _ := by simp [Nat.add_assoc]

theorem prefixSum_at_castSucc {s : ℕ} (x : Fin s → ℕ) (q : Fin s) :
    prefixSum x q.castSucc = massBefore x q := by
  rfl

theorem prefixSum_at_succ {s : ℕ} (x : Fin s → ℕ) (q : Fin s) :
    prefixSum x q.succ = massBefore x q + x q := by
  classical
  rw [prefixSum, massBefore]
  calc
    (∑ i, if i.val < q.succ.val then x i else 0) =
        ∑ i, ((if i.val < q.val then x i else 0) + if i = q then x q else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hiq : i = q
          · subst i
            simp
          · have hne : i.val ≠ q.val := fun h ↦ hiq (Fin.ext h)
            by_cases hlt : i.val < q.val
            · have hlts : i.val < q.val + 1 := by omega
              simp [hlt, hlts, hiq]
            · have hnlt : ¬ i.val < q.val + 1 := by omega
              simp [hlt, hnlt, hiq]
    _ = _ := by simp [Finset.sum_add_distrib]

theorem massBefore_cap_decomposition {s : ℕ} {c m : Fin s → ℕ}
    (hcap : WithinCap c m) (q : Fin s) :
    massBefore c q = massBefore m q + spareBefore c m q := by
  classical
  rw [massBefore, massBefore, spareBefore, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < q.val
  · simp only [hi, if_true]
    have hcm := hcap i
    omega
  · simp [hi]

theorem massBefore_mono_of_cap {s : ℕ} {c x : Fin s → ℕ}
    (hcap : WithinCap c x) (q : Fin s) : massBefore x q ≤ massBefore c q := by
  classical
  unfold massBefore
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i.val < q.val
  · simp only [hi, if_true]
    exact hcap i
  · simp [hi]

/-- Lower endpoint from equation (2.1) of the Buffer Lemma. -/
def lowerEndpoint {s : ℕ} (c m : Fin s → ℕ) (q : Fin s) : ℕ :=
  m q - spareBefore c m q

/-- Upper endpoint from equation (2.1) of the Buffer Lemma. -/
def upperEndpoint {s : ℕ} (c m : Fin s → ℕ) (q : Fin s) : ℕ :=
  min (c q) (m q + massAfter m q)

theorem feasible_coordinate_bounds {s : ℕ} {c m x : Fin s → ℕ} {r : ℕ}
    (hm : Feasible c r m m) (hx : Feasible c r m x) (q : Fin s) :
    lowerEndpoint c m q ≤ x q ∧ x q ≤ upperEndpoint c m q := by
  rcases hm with ⟨hmcap, hmtotal, _⟩
  rcases hx with ⟨hxcap, hxtotal, hxdom⟩
  have hdomSucc := hxdom q.succ
  rw [prefixSum_at_succ, prefixSum_at_succ] at hdomSucc
  have hxBeforeCap := massBefore_mono_of_cap hxcap q
  have hcapSplit := massBefore_cap_decomposition hmcap q
  have hlower : lowerEndpoint c m q ≤ x q := by
    unfold lowerEndpoint
    omega
  have hdomBefore := hxdom q.castSucc
  rw [prefixSum_at_castSucc, prefixSum_at_castSucc] at hdomBefore
  have hmSplit := total_eq_massBefore_add_self_add_massAfter m q
  have hxSplit := total_eq_massBefore_add_self_add_massAfter x q
  have hmass : x q ≤ m q + massAfter m q := by
    omega
  have hupper : x q ≤ upperEndpoint c m q := by
    unfold upperEndpoint
    exact le_min (hxcap q) hmass
  exact ⟨hlower, hupper⟩

theorem attainedRange_subset_Icc {s : ℕ} {c m : Fin s → ℕ} {r : ℕ}
    (hm : Feasible c r m m) (q : Fin s) :
    attainedRange c r m q ⊆ Finset.Icc (lowerEndpoint c m q) (upperEndpoint c m q) := by
  classical
  intro t ht
  rw [mem_attainedRange_iff] at ht
  obtain ⟨x, hx, rfl⟩ := ht
  rw [Finset.mem_Icc]
  exact feasible_coordinate_bounds hm (mem_filter_iff.mp hx) q

theorem endpoint_lt_iff_activity_arithmetic {s : ℕ} {c m : Fin s → ℕ}
    (hcap : WithinCap c m) (q : Fin s) :
    lowerEndpoint c m q < upperEndpoint c m q ↔
      (0 < m q ∧ 0 < spareBefore c m q) ∨
      (m q < c q ∧ 0 < massAfter m q) := by
  unfold lowerEndpoint upperEndpoint
  have hmq := hcap q
  omega

private theorem exists_suballocation {s : ℕ} (f : Fin s → ℕ) (d : ℕ)
    (hd : d ≤ ∑ i, f i) :
    ∃ g : Fin s → ℕ, (∀ i, g i ≤ f i) ∧ (∑ i, g i) = d := by
  classical
  suffices h : ∀ (S : Finset (Fin s)) (d : ℕ), d ≤ ∑ i ∈ S, f i →
      ∃ g : Fin s → ℕ,
        (∀ i ∈ S, g i ≤ f i) ∧ (∀ i ∉ S, g i = 0) ∧ (∑ i ∈ S, g i) = d by
    obtain ⟨g, hg, _, hsum⟩ := h Finset.univ d (by simpa using hd)
    exact ⟨g, fun i ↦ hg i (Finset.mem_univ i), by simpa using hsum⟩
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro d hd
      have hd0 : d = 0 := by simpa using hd
      subst d
      refine ⟨fun _ ↦ 0, ?_, ?_, by simp⟩
      · intro i hi
        simp at hi
      · simp
  | @insert a S ha ih =>
      intro d hd
      let da := min d (f a)
      let dr := d - da
      have hdr : dr ≤ ∑ i ∈ S, f i := by
        rw [Finset.sum_insert ha] at hd
        dsimp [dr, da]
        omega
      obtain ⟨g, hgBound, hgOutside, hgSum⟩ := ih dr hdr
      let g' := Function.update g a da
      refine ⟨g', ?_, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hiS
        · simp [g', da]
        · have hia : i ≠ a := fun h ↦ ha (h ▸ hiS)
          simpa [g', hia] using hgBound i hiS
      · intro i hi
        have hia : i ≠ a := by
          intro h
          subst i
          exact hi (Finset.mem_insert_self a S)
        have hiS : i ∉ S := fun h ↦ hi (Finset.mem_insert_of_mem h)
        simpa [g', hia] using hgOutside i hiS
      · rw [Finset.sum_insert ha]
        have hsumUpdate : ∑ i ∈ S, g' i = ∑ i ∈ S, g i := by
          apply Finset.sum_congr rfl
          intro i hiS
          have hia : i ≠ a := fun h ↦ ha (h ▸ hiS)
          simp [g', hia]
        rw [hsumUpdate, hgSum]
        simp [g', da, dr]

private theorem attain_of_le_base {s : ℕ} {c m : Fin s → ℕ} {r t : ℕ}
    (hcap : WithinCap c m) (htotal : (∑ i, m i) = r) (q : Fin s)
    (htm : t ≤ m q) (hroom : m q - t ≤ spareBefore c m q) :
    ∃ x ∈ filter c r m, x q = t := by
  classical
  let d := m q - t
  let f : Fin s → ℕ := fun i ↦ if i.val < q.val then c i - m i else 0
  have hfsum : (∑ i, f i) = spareBefore c m q := by rfl
  have hdle : d ≤ ∑ i, f i := by
    rw [hfsum]
    exact hroom
  obtain ⟨g, hgBound, hgSum⟩ := exists_suballocation f d hdle
  have hgq : g q = 0 := by
    have h := hgBound q
    simp [f] at h
    omega
  have hgOutside : ∀ i, ¬ i.val < q.val → g i = 0 := by
    intro i hi
    have h := hgBound i
    have hi' : ¬ i < q := by simpa using hi
    simp [f, hi'] at h
    omega
  let x : Fin s → ℕ := fun i ↦ if i = q then t else m i + g i
  have hxq : x q = t := by simp [x]
  have hxcap : WithinCap c x := by
    intro i
    by_cases hiq : i = q
    · subst i
      simp only [hxq]
      exact htm.trans (hcap q)
    · simp only [x, hiq, if_false]
      by_cases hi : i.val < q.val
      · have hg := hgBound i
        have hc := hcap i
        simp only [f, hi, if_true] at hg
        omega
      · rw [hgOutside i hi, Nat.add_zero]
        exact hcap i
  have hqUniv : q ∈ (Finset.univ : Finset (Fin s)) := Finset.mem_univ q
  have hxErase :
      ∑ i ∈ (Finset.univ.erase q), x i =
        (∑ i ∈ (Finset.univ.erase q), m i) +
          ∑ i ∈ (Finset.univ.erase q), g i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hiq : i ≠ q := by simpa using (Finset.mem_erase.mp hi).1
    simp [x, hiq]
  have hgErase : ∑ i ∈ (Finset.univ.erase q), g i = d := by
    have h := Finset.sum_erase_add Finset.univ g hqUniv
    omega
  have hmErase := Finset.sum_erase_add Finset.univ m hqUniv
  have hxEraseAdd := Finset.sum_erase_add Finset.univ x hqUniv
  have hd : t + d = m q := by
    dsimp [d]
    omega
  have hxtotal : (∑ i, x i) = r := by
    omega
  have hxdom : Dominates m x := by
    intro k
    by_cases hqk : q.val < k.val
    · let S : Finset (Fin s) := Finset.univ.filter fun i ↦ i.val < k.val
      have hqS : q ∈ S := by simp [S, hqk]
      have hsumX : prefixSum x k = ∑ i ∈ S, x i := by
        simp [prefixSum, S, Finset.sum_filter]
      have hsumM : prefixSum m k = ∑ i ∈ S, m i := by
        simp [prefixSum, S, Finset.sum_filter]
      have hgS : ∑ i ∈ S, g i = d := by
        calc
          (∑ i ∈ S, g i) = ∑ i ∈ (Finset.univ : Finset (Fin s)), g i := by
            apply Finset.sum_subset (by intro i hi; simp)
            intro i _ hiS
            apply hgOutside i
            intro hiq
            apply hiS
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
            omega
          _ = d := hgSum
      have hgEraseS : ∑ i ∈ S.erase q, g i = d := by
        have h := Finset.sum_erase_add S g hqS
        omega
      have hxEraseS :
          ∑ i ∈ S.erase q, x i =
            (∑ i ∈ S.erase q, m i) + ∑ i ∈ S.erase q, g i := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        have hiq : i ≠ q := by simpa using (Finset.mem_erase.mp hi).1
        simp [x, hiq]
      have hmEraseS := Finset.sum_erase_add S m hqS
      have hxEraseAddS := Finset.sum_erase_add S x hqS
      rw [hsumM, hsumX]
      omega
    · unfold prefixSum
      apply Finset.sum_le_sum
      intro i _
      by_cases hik : i.val < k.val
      · have hiq : i ≠ q := by
          intro hi
          subst i
          exact hqk hik
        simp [hik, x, hiq]
      · simp [hik]
  refine ⟨x, mem_filter_iff.mpr ⟨hxcap, hxtotal, hxdom⟩, hxq⟩

private theorem attain_of_base_le {s : ℕ} {c m : Fin s → ℕ} {r t : ℕ}
    (hcap : WithinCap c m) (htotal : (∑ i, m i) = r) (q : Fin s)
    (hmt : m q ≤ t) (htcap : t ≤ c q) (hroom : t - m q ≤ massAfter m q) :
    ∃ x ∈ filter c r m, x q = t := by
  classical
  let d := t - m q
  let f : Fin s → ℕ := fun i ↦ if q.val < i.val then m i else 0
  have hfsum : (∑ i, f i) = massAfter m q := by rfl
  have hdle : d ≤ ∑ i, f i := by
    rw [hfsum]
    exact hroom
  obtain ⟨g, hgBound, hgSum⟩ := exists_suballocation f d hdle
  have hgq : g q = 0 := by
    have h := hgBound q
    simp [f] at h
    omega
  have hgOutside : ∀ i, ¬ q.val < i.val → g i = 0 := by
    intro i hi
    have h := hgBound i
    have hi' : ¬ q < i := by simpa using hi
    simp [f, hi'] at h
    omega
  let x : Fin s → ℕ := fun i ↦ if i = q then t else m i - g i
  have hxq : x q = t := by simp [x]
  have hxcap : WithinCap c x := by
    intro i
    by_cases hiq : i = q
    · subst i
      simpa only [hxq] using htcap
    · simp only [x, hiq, if_false]
      exact (Nat.sub_le _ _).trans (hcap i)
  have hqUniv : q ∈ (Finset.univ : Finset (Fin s)) := Finset.mem_univ q
  have hmEraseSplit :
      ∑ i ∈ (Finset.univ.erase q), m i =
        (∑ i ∈ (Finset.univ.erase q), x i) +
          ∑ i ∈ (Finset.univ.erase q), g i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hiq : i ≠ q := by simpa using (Finset.mem_erase.mp hi).1
    have hgLe : g i ≤ m i := by
      have hg := hgBound i
      by_cases hqi : q.val < i.val
      · simpa only [f, hqi, if_true] using hg
      · rw [hgOutside i hqi]
        exact Nat.zero_le _
    rw [show x i = m i - g i by simp [x, hiq]]
    exact (Nat.sub_add_cancel hgLe).symm
  have hgErase : ∑ i ∈ (Finset.univ.erase q), g i = d := by
    have h := Finset.sum_erase_add Finset.univ g hqUniv
    omega
  have hmEraseAdd := Finset.sum_erase_add Finset.univ m hqUniv
  have hxEraseAdd := Finset.sum_erase_add Finset.univ x hqUniv
  have hd : m q + d = t := by
    dsimp [d]
    omega
  have hxtotal : (∑ i, x i) = r := by
    omega
  have hxdom : Dominates m x := by
    intro k
    by_cases hqk : q.val < k.val
    · let S : Finset (Fin s) := Finset.univ.filter fun i ↦ i.val < k.val
      have hqS : q ∈ S := by simp [S, hqk]
      have hsumX : prefixSum x k = ∑ i ∈ S, x i := by
        simp [prefixSum, S, Finset.sum_filter]
      have hsumM : prefixSum m k = ∑ i ∈ S, m i := by
        simp [prefixSum, S, Finset.sum_filter]
      have hgEraseS : ∑ i ∈ S.erase q, g i ≤ d := by
        calc
          (∑ i ∈ S.erase q, g i) ≤
              ∑ i ∈ (Finset.univ : Finset (Fin s)), g i := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro i hi
              simp
            · simp
          _ = d := hgSum
      have hmEraseS :
          ∑ i ∈ S.erase q, m i =
            (∑ i ∈ S.erase q, x i) + ∑ i ∈ S.erase q, g i := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        have hiq : i ≠ q := by simpa using (Finset.mem_erase.mp hi).1
        have hgLe : g i ≤ m i := by
          have hg := hgBound i
          by_cases hqi : q.val < i.val
          · simpa only [f, hqi, if_true] using hg
          · rw [hgOutside i hqi]
            exact Nat.zero_le _
        rw [show x i = m i - g i by simp [x, hiq]]
        exact (Nat.sub_add_cancel hgLe).symm
      have hmEraseAddS := Finset.sum_erase_add S m hqS
      have hxEraseAddS := Finset.sum_erase_add S x hqS
      rw [hsumM, hsumX]
      omega
    · unfold prefixSum
      apply Finset.sum_le_sum
      intro i _
      by_cases hik : i.val < k.val
      · have hiq : i ≠ q := by
          intro hi
          subst i
          exact hqk hik
        have hnqi : ¬ q.val < i.val := by omega
        have hzero := hgOutside i hnqi
        simp [hik, x, hiq, hzero]
      · simp [hik]
  refine ⟨x, mem_filter_iff.mpr ⟨hxcap, hxtotal, hxdom⟩, hxq⟩

theorem attainedRange_eq_Icc {s : ℕ} {c m : Fin s → ℕ} {r : ℕ}
    (hm : Feasible c r m m) (q : Fin s) :
    attainedRange c r m q = Finset.Icc (lowerEndpoint c m q) (upperEndpoint c m q) := by
  classical
  apply Finset.Subset.antisymm (attainedRange_subset_Icc hm q)
  intro t ht
  rw [Finset.mem_Icc] at ht
  rw [mem_attainedRange_iff]
  rcases hm with ⟨hcap, htotal, _⟩
  rcases le_total t (m q) with htm | hmt
  · apply attain_of_le_base hcap htotal q htm
    unfold lowerEndpoint at ht
    omega
  · apply attain_of_base_le hcap htotal q hmt
    · exact ht.2.trans (min_le_left _ _)
    · unfold upperEndpoint at ht
      omega

theorem active_iff_endpoint_lt {s : ℕ} {c m : Fin s → ℕ} {r : ℕ}
    (hm : Feasible c r m m) (q : Fin s) :
    Active c r m q ↔ lowerEndpoint c m q < upperEndpoint c m q := by
  classical
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    have hxb := feasible_coordinate_bounds hm (mem_filter_iff.mp hx) q
    have hyb := feasible_coordinate_bounds hm (mem_filter_iff.mp hy) q
    omega
  · intro hlt
    have hlmem : lowerEndpoint c m q ∈ attainedRange c r m q := by
      rw [attainedRange_eq_Icc hm q, Finset.mem_Icc]
      exact ⟨le_rfl, hlt.le⟩
    have humem : upperEndpoint c m q ∈ attainedRange c r m q := by
      rw [attainedRange_eq_Icc hm q, Finset.mem_Icc]
      exact ⟨hlt.le, le_rfl⟩
    rw [mem_attainedRange_iff] at hlmem humem
    obtain ⟨x, hx, hxl⟩ := hlmem
    obtain ⟨y, hy, hyu⟩ := humem
    refine ⟨x, hx, y, hy, ?_⟩
    omega

theorem activity_criterion {s : ℕ} {c m : Fin s → ℕ} {r : ℕ}
    (hm : Feasible c r m m) (q : Fin s) :
    Active c r m q ↔
      (0 < m q ∧ 0 < spareBefore c m q) ∨
      (m q < c q ∧ 0 < massAfter m q) := by
  rw [active_iff_endpoint_lt hm q]
  exact endpoint_lt_iff_activity_arithmetic hm.1 q


/-- Ferrers graph of `(a,b)=(m,c-m)`: an edge `j--k`, oriented by the index
order, records spare capacity at the earlier coordinate and positive mass at
the later coordinate. -/
def ferrersGraph {s : ℕ} (c m : Fin s → ℕ) : SimpleGraph (Fin s) where
  Adj j k :=
    (j.val < k.val ∧ m j < c j ∧ 0 < m k) ∨
    (k.val < j.val ∧ m k < c k ∧ 0 < m j)
  symm := by
    constructor
    intro j k h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  loopless := by
    constructor
    intro j h
    omega

theorem active_iff_ferrers_nonisolated {s : ℕ} {c m : Fin s → ℕ} {r : ℕ}
    (hm : Feasible c r m m) (q : Fin s) :
    Active c r m q ↔ ∃ j, (ferrersGraph c m).Adj q j := by
  rw [activity_criterion hm q]
  constructor
  · rintro (hleft | hright)
    · rw [spareBefore, Finset.sum_pos_iff] at hleft
      obtain ⟨j, _, hj⟩ := hleft.2
      by_cases hjq : j.val < q.val
      · refine ⟨j, Or.inr ⟨hjq, ?_, hleft.1⟩⟩
        simp only [hjq, if_true] at hj
        omega
      · simp [hjq] at hj
    · rw [massAfter, Finset.sum_pos_iff] at hright
      obtain ⟨j, _, hj⟩ := hright.2
      by_cases hqj : q.val < j.val
      · refine ⟨j, Or.inl ⟨hqj, hright.1, ?_⟩⟩
        simpa [hqj] using hj
      · simp [hqj] at hj
  · rintro ⟨j, hj⟩
    rcases hj with hj | hj
    · exact Or.inr ⟨hj.2.1, by
        rw [massAfter, Finset.sum_pos_iff]
        exact ⟨j, Finset.mem_univ j, by simp [hj.1, hj.2.2]⟩⟩
    · exact Or.inl ⟨hj.2.2, by
        rw [spareBefore, Finset.sum_pos_iff]
        refine ⟨j, Finset.mem_univ j, ?_⟩
        simp only [hj.1, if_true]
        omega⟩

/-- Concrete one-step vector, used by the Ferrers bridge and port lemmas. -/
def transfer {s : ℕ} (x : Fin s → ℕ) (p q : Fin s) : Fin s → ℕ :=
  Function.update (Function.update x p (x p + 1)) q (x q - 1)

@[simp] theorem transfer_source {s : ℕ} (x : Fin s → ℕ) {p q : Fin s}
    (hpq : p ≠ q) : transfer x p q p = x p + 1 := by
  simp [transfer, hpq]

@[simp] theorem transfer_donor {s : ℕ} (x : Fin s → ℕ) (p q : Fin s) :
    transfer x p q q = x q - 1 := by
  simp [transfer]

theorem transfer_other {s : ℕ} (x : Fin s → ℕ) {p q i : Fin s}
    (hip : i ≠ p) (hiq : i ≠ q) : transfer x p q i = x i := by
  simp [transfer, hip, hiq]

theorem directedTransfer_transfer {s : ℕ} (x : Fin s → ℕ) {p q : Fin s}
    (hpq : p ≠ q) (hq : 0 < x q) : DirectedTransfer x (transfer x p q) p q := by
  refine ⟨hpq, transfer_source x hpq, ?_, ?_⟩
  · rw [transfer_donor x p q]
    omega
  · intro i hip hiq
    exact transfer_other x hip hiq

theorem ferrers_transfer_mem {s : ℕ} {c m : Fin s → ℕ} {r : ℕ}
    (hm : Feasible c r m m) {p q : Fin s}
    (hpq : p.val < q.val) (hpcap : m p < c p) (hqpos : 0 < m q) :
    transfer m p q ∈ filter c r m := by
  classical
  rcases hm with ⟨hmcap, hmtotal, _⟩
  have hpne : p ≠ q := by omega
  rw [mem_filter_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hip : i = p
    · subst i
      rw [transfer_source m hpne]
      omega
    · by_cases hiq : i = q
      · subst i
        rw [transfer_donor m p q]
        exact (Nat.sub_le _ _).trans (hmcap q)
      · rw [transfer_other m hip hiq]
        exact hmcap i
  · have hpUniv : p ∈ (Finset.univ : Finset (Fin s)) := Finset.mem_univ p
    have hqErase : q ∈ (Finset.univ.erase p : Finset (Fin s)) := by simp [hpne.symm]
    have hmP := Finset.sum_erase_add Finset.univ m hpUniv
    have htP := Finset.sum_erase_add Finset.univ (transfer m p q) hpUniv
    have hmQ := Finset.sum_erase_add (Finset.univ.erase p) m hqErase
    have htQ := Finset.sum_erase_add (Finset.univ.erase p) (transfer m p q) hqErase
    have hrest :
        ∑ i ∈ (Finset.univ.erase p).erase q, transfer m p q i =
          ∑ i ∈ (Finset.univ.erase p).erase q, m i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hip : i ≠ p := by
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      have hiq : i ≠ q := (Finset.mem_erase.mp hi).1
      exact transfer_other m hip hiq
    have htp := transfer_source m hpne
    have htq := transfer_donor m p q
    omega
  · intro k
    by_cases hqk : q.val < k.val
    · let S : Finset (Fin s) := Finset.univ.filter fun i ↦ i.val < k.val
      have hpS : p ∈ S := by simp [S]; omega
      have hqS : q ∈ S.erase p := by simp [S, hpne.symm, hqk]
      have hmP := Finset.sum_erase_add S m hpS
      have htP := Finset.sum_erase_add S (transfer m p q) hpS
      have hmQ := Finset.sum_erase_add (S.erase p) m hqS
      have htQ := Finset.sum_erase_add (S.erase p) (transfer m p q) hqS
      have hrest :
          ∑ i ∈ (S.erase p).erase q, transfer m p q i =
            ∑ i ∈ (S.erase p).erase q, m i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hip : i ≠ p :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
        have hiq : i ≠ q := (Finset.mem_erase.mp hi).1
        exact transfer_other m hip hiq
      have hsumM : prefixSum m k = ∑ i ∈ S, m i := by
        simp [prefixSum, S, Finset.sum_filter]
      have hsumT : prefixSum (transfer m p q) k = ∑ i ∈ S, transfer m p q i := by
        simp [prefixSum, S, Finset.sum_filter]
      rw [hsumM, hsumT]
      have htp := transfer_source m hpne
      have htq := transfer_donor m p q
      omega
    · unfold prefixSum
      apply Finset.sum_le_sum
      intro i _
      by_cases hik : i.val < k.val
      · have hiq : i ≠ q := by
          intro hi
          subst i
          exact hqk hik
        by_cases hip : i = p
        · subst i
          simp [hik, transfer_source m hpne]
        · simp [hik, transfer_other m hip hiq]
      · simp [hik]

#print axioms mem_filter_iff
#print axioms attainedRange_eq_Icc
#print axioms active_iff_endpoint_lt
#print axioms activity_criterion
#print axioms active_iff_ferrers_nonisolated
#print axioms ferrers_transfer_mem

end Brualdi.RealizationGraph.BoundedComposition
