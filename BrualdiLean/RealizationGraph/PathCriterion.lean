/-
Copyright (c) 2026 Jeffrey S. Baggett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey S. Baggett
-/
import BrualdiLean.RealizationGraph.BoundedCompositionFilter
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# The bounded-composition path criterion

The path predicate is literal graph isomorphism with `SimpleGraph.pathGraph`.
-/

set_option autoImplicit false
set_option linter.style.nativeDecide false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open scoped BigOperators

namespace Brualdi.RealizationGraph.BoundedComposition

/-- A finite simple graph is a path when it is isomorphic to `pathGraph n`
for some `n`; this convention includes `P₀` and `P₁`. -/
def IsPathGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ n, Nonempty (G ≃g SimpleGraph.pathGraph n)

theorem active_of_coordinate_ne {s : ℕ} {c m x y : Fin s → ℕ} {r : ℕ}
    {i : Fin s} (hx : x ∈ filter c r m) (hy : y ∈ filter c r m) (hxy : x i ≠ y i) :
    Active c r m i :=
  ⟨x, hx, y, hy, hxy⟩

private theorem exists_second_difference {s : ℕ} {x y : Fin s → ℕ} {p : Fin s}
    (htotal : (∑ i, x i) = ∑ i, y i) (hp : x p ≠ y p) :
    ∃ q, q ≠ p ∧ x q ≠ y q := by
  classical
  by_contra h
  have hsame : ∀ q, q ≠ p → x q = y q := by
    intro q hqp
    by_contra hq
    exact h ⟨q, hqp, hq⟩
  have hpUniv : p ∈ (Finset.univ : Finset (Fin s)) := Finset.mem_univ p
  have hxErase := Finset.sum_erase_add Finset.univ x hpUniv
  have hyErase := Finset.sum_erase_add Finset.univ y hpUniv
  have hrest : ∑ i ∈ Finset.univ.erase p, x i = ∑ i ∈ Finset.univ.erase p, y i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hsame i (Finset.mem_erase.mp hi).1
  omega

private theorem three_active_contradiction {s : ℕ} {c m : Fin s → ℕ} {r : ℕ}
    {i j k : Fin s} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : Active c r m i) (hj : Active c r m j) (hk : Active c r m k)
    (hdim : effectiveDimension c r m ≤ 2) : False := by
  classical
  have hsub : ({i, j, k} : Finset (Fin s)) ⊆ activeCoordinates c r m := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact mem_activeCoordinates_iff.mpr hi
    · exact mem_activeCoordinates_iff.mpr hj
    · exact mem_activeCoordinates_iff.mpr hk
  have hcard := Finset.card_le_card hsub
  have hthree : ({i, j, k} : Finset (Fin s)).card = 3 := by
    simp [hij, hik, hjk]
  unfold effectiveDimension at hdim
  omega

private theorem coordinate_injective_of_dim_le_two
    {s : ℕ} {c m : Fin s → ℕ} {r : ℕ} {q : Fin s}
    (hqActive : Active c r m q) (hdim : effectiveDimension c r m ≤ 2) :
    Function.Injective (fun x : {x // x ∈ filter c r m} ↦ x.1 q) := by
  intro x y hq
  apply Subtype.ext
  funext p
  by_contra hp
  have hpne : p ≠ q := by
    intro hpq
    subst p
    exact hp hq
  have hxTotal := (mem_filter_iff.mp x.2).2.1
  have hyTotal := (mem_filter_iff.mp y.2).2.1
  obtain ⟨k, hkp, hk⟩ := exists_second_difference (hxTotal.trans hyTotal.symm) hp
  have hkq : k ≠ q := by
    intro hkq
    subst k
    exact hk hq
  exact three_active_contradiction hpne.symm hkq.symm hkp.symm hqActive
    (active_of_coordinate_ne x.2 y.2 hp) (active_of_coordinate_ne x.2 y.2 hk) hdim

private theorem unitTransfer_coordinate_step
    {s : ℕ} {c m : Fin s → ℕ} {r : ℕ} {q : Fin s}
    (hinj : Function.Injective (fun x : {x // x ∈ filter c r m} ↦ x.1 q))
    {x y : {x // x ∈ filter c r m}} (hxy : UnitTransfer x.1 y.1) :
    x.1 q + 1 = y.1 q ∨ y.1 q + 1 = x.1 q := by
  rcases hxy with hxy | hxy
  · obtain ⟨p, d, hpd, hp, hd, hother⟩ := hxy
    by_cases hqp : q = p
    · subst p
      exact Or.inl hp.symm
    · by_cases hqd : q = d
      · subst d
        exact Or.inr hd.symm
      · have heq : y.1 q = x.1 q := hother q hqp hqd
        exfalso
        apply directedTransfer_ne ⟨hpd, hp, hd, hother⟩
        exact congrArg Subtype.val (hinj heq.symm)
  · obtain ⟨p, d, hpd, hp, hd, hother⟩ := hxy
    by_cases hqp : q = p
    · subst p
      exact Or.inr hp.symm
    · by_cases hqd : q = d
      · subst d
        exact Or.inl hd.symm
      · have heq : x.1 q = y.1 q := hother q hqp hqd
        exfalso
        apply directedTransfer_ne ⟨hpd, hp, hd, hother⟩
        exact congrArg Subtype.val (hinj heq).symm

private theorem unitTransfer_of_coordinate_step_forward
    {s : ℕ} {c m : Fin s → ℕ} {r : ℕ} {q : Fin s}
    (hqActive : Active c r m q) (hdim : effectiveDimension c r m ≤ 2)
    {x y : {x // x ∈ filter c r m}}
    (hstep : x.1 q + 1 = y.1 q) :
    UnitTransfer x.1 y.1 := by
  classical
  have hxTotal := (mem_filter_iff.mp x.2).2.1
  have hyTotal := (mem_filter_iff.mp y.2).2.1
  have hqne : x.1 q ≠ y.1 q := by omega
  obtain ⟨p, hpq, hp⟩ :=
    exists_second_difference (hxTotal.trans hyTotal.symm) hqne
  have hother : ∀ i, i ≠ q → i ≠ p → y.1 i = x.1 i := by
    intro i hiq hip
    by_contra hi
    exact three_active_contradiction hpq.symm hiq.symm hip.symm hqActive
      (active_of_coordinate_ne x.2 y.2 hp)
      (active_of_coordinate_ne x.2 y.2 (Ne.symm hi)) hdim
  have hpUniv : p ∈ (Finset.univ : Finset (Fin s)) := Finset.mem_univ p
  have hqErase : q ∈ (Finset.univ.erase p : Finset (Fin s)) := by simp [hpq.symm]
  have hxP := Finset.sum_erase_add Finset.univ x.1 hpUniv
  have hyP := Finset.sum_erase_add Finset.univ y.1 hpUniv
  have hxQ := Finset.sum_erase_add (Finset.univ.erase p) x.1 hqErase
  have hyQ := Finset.sum_erase_add (Finset.univ.erase p) y.1 hqErase
  have hrest :
      ∑ i ∈ (Finset.univ.erase p).erase q, x.1 i =
        ∑ i ∈ (Finset.univ.erase p).erase q, y.1 i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hip : i ≠ p :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    have hiq : i ≠ q := (Finset.mem_erase.mp hi).1
    exact (hother i hiq hip).symm
  have hpstep : x.1 p = y.1 p + 1 := by omega
  exact Or.inl ⟨q, p, hpq.symm, hstep.symm, hpstep, hother⟩

private theorem unitTransfer_of_coordinate_step
    {s : ℕ} {c m : Fin s → ℕ} {r : ℕ} {q : Fin s}
    (hqActive : Active c r m q) (hdim : effectiveDimension c r m ≤ 2)
    {x y : {x // x ∈ filter c r m}}
    (hstep : x.1 q + 1 = y.1 q ∨ y.1 q + 1 = x.1 q) :
    UnitTransfer x.1 y.1 := by
  rcases hstep with hstep | hstep
  · exact unitTransfer_of_coordinate_step_forward hqActive hdim hstep
  · exact unitTransfer_symm
      (unitTransfer_of_coordinate_step_forward (x := y) (y := x) hqActive hdim hstep)

/-- The easy direction of the path criterion, including the singleton case:
at most two active coordinates give a literal path graph. -/
theorem isPathGraph_of_effectiveDimension_le_two
    {s : ℕ} {c m : Fin s → ℕ} {r : ℕ}
    (hm : Feasible c r m m) (hdim : effectiveDimension c r m ≤ 2) :
    IsPathGraph (transferGraph c r m) := by
  classical
  by_cases hactive : ∃ q, Active c r m q
  · obtain ⟨q, hqActive⟩ := hactive
    let lo := lowerEndpoint c m q
    let hi := upperEndpoint c m q
    have hlohi : lo < hi := active_iff_endpoint_lt hm q |>.mp hqActive
    let n := hi - lo + 1
    let f : {x // x ∈ filter c r m} → Fin n := fun x ↦
      ⟨x.1 q - lo, by
        have hb := feasible_coordinate_bounds hm (mem_filter_iff.mp x.2) q
        dsimp [n, lo, hi]
        omega⟩
    have hinjCoord := coordinate_injective_of_dim_le_two hqActive hdim
    have hinj : Function.Injective f := by
      intro x y hxy
      apply hinjCoord
      have hxb := feasible_coordinate_bounds hm (mem_filter_iff.mp x.2) q
      have hyb := feasible_coordinate_bounds hm (mem_filter_iff.mp y.2) q
      have hv := congrArg Fin.val hxy
      change x.1 q - lowerEndpoint c m q = y.1 q - lowerEndpoint c m q at hv
      calc
        x.1 q = (x.1 q - lowerEndpoint c m q) + lowerEndpoint c m q :=
          (Nat.sub_add_cancel hxb.1).symm
        _ = (y.1 q - lowerEndpoint c m q) + lowerEndpoint c m q := by rw [hv]
        _ = y.1 q := Nat.sub_add_cancel hyb.1
    have hsurj : Function.Surjective f := by
      intro z
      let t := lo + z.val
      have htmem : t ∈ attainedRange c r m q := by
        rw [attainedRange_eq_Icc hm q, Finset.mem_Icc]
        dsimp [t, lo, hi, n] at ⊢ z
        omega
      rw [mem_attainedRange_iff] at htmem
      obtain ⟨x, hx, hxt⟩ := htmem
      refine ⟨⟨x, hx⟩, Fin.ext ?_⟩
      dsimp [f, t]
      omega
    let e : {x // x ∈ filter c r m} ≃ Fin n := Equiv.ofBijective f ⟨hinj, hsurj⟩
    refine ⟨n, ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩⟩
    intro x y
    rw [SimpleGraph.pathGraph_adj]
    change ((f x).val + 1 = (f y).val ∨ (f y).val + 1 = (f x).val) ↔
      UnitTransfer x.1 y.1
    have hxb := feasible_coordinate_bounds hm (mem_filter_iff.mp x.2) q
    have hyb := feasible_coordinate_bounds hm (mem_filter_iff.mp y.2) q
    constructor
    · intro hxy
      apply unitTransfer_of_coordinate_step hqActive hdim
      rcases hxy with h | h
      · left
        dsimp [f, lo] at h
        omega
      · right
        dsimp [f, lo] at h
        omega
    · intro hxy
      rcases unitTransfer_coordinate_step hinjCoord hxy with h | h
      · left
        dsimp [f, lo]
        omega
      · right
        dsimp [f, lo]
        omega
  · have hsubsingleton : Subsingleton {x // x ∈ filter c r m} := ⟨by
      intro x y
      apply Subtype.ext
      funext i
      by_contra hxy
      exact hactive ⟨i, active_of_coordinate_ne x.2 y.2 hxy⟩⟩
    have hnonempty : Nonempty {x // x ∈ filter c r m} :=
      ⟨⟨m, base_mem_filter hm.1 hm.2.1⟩⟩
    letI : Unique {x // x ∈ filter c r m} :=
      { default := Classical.choice hnonempty
        uniq := fun x ↦ Subsingleton.elim _ _ }
    let e : {x // x ∈ filter c r m} ≃ Fin 1 := Equiv.ofUnique _ _
    refine ⟨1, ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩⟩
    intro x y
    constructor
    · intro h
      simp [SimpleGraph.pathGraph_adj] at h
    · intro h
      have hxy : x = y := Subsingleton.elim _ _
      subst y
      exact (unitTransfer_irrefl x.1 h).elim

#print axioms isPathGraph_of_effectiveDimension_le_two

end Brualdi.RealizationGraph.BoundedComposition
