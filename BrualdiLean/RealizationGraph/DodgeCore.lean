/-
Copyright (c) 2026 Jeffrey S. Baggett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey S. Baggett
-/
import BrualdiLean.RealizationGraph.BoundedCompositionFilter
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Finite dodge core

Pure finite-state and path-separator lemmas used by the sequel.  Nothing in
this file assumes graphicality or polyhedral integrality.
-/

set_option autoImplicit false
set_option linter.style.nativeDecide false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace Brualdi.RealizationGraph.DodgeCore

universe u v

/-! ## First-death localization -/

section FirstDeath

variable {α : Type u} [DecidableEq α]

/-- One forward image, restricted to the next finite state set. -/
def nextLayer (R : α → α → Prop) [DecidableRel R] (A B : Finset α) : Finset α :=
  B.filter fun y ↦ ∃ x ∈ A, R x y

theorem mem_nextLayer_iff {R : α → α → Prop} [DecidableRel R]
    {A B : Finset α} {y : α} :
    y ∈ nextLayer R A B ↔ y ∈ B ∧ ∃ x ∈ A, R x y := by
  simp [nextLayer]

/-- An indexed composite-relation witness of length `n`. -/
def RelChain (R : ℕ → α → α → Prop) : ℕ → α → α → Prop
  | 0, x, y => x = y
  | n + 1, x, y => ∃ z, RelChain R n x z ∧ R n z y

theorem forward_member_has_chain
    (R : ℕ → α → α → Prop) [∀ n, DecidableRel (R n)]
    (B F : ℕ → Finset α)
    (hrec : ∀ n, F (n + 1) = nextLayer (R n) (F n) (B (n + 1))) :
    ∀ {n y}, y ∈ F n → ∃ x ∈ F 0, RelChain R n x y := by
  intro n
  induction n with
  | zero =>
      intro y hy
      exact ⟨y, hy, rfl⟩
  | succ n ih =>
      intro y hy
      rw [hrec n, mem_nextLayer_iff] at hy
      obtain ⟨z, hzF, hzR⟩ := hy.2
      obtain ⟨x, hxF, hxChain⟩ := ih hzF
      exact ⟨x, hxF, z, hxChain, hzR⟩

/-- If every forward domain through layer `h` is nonempty, then the indexed
composite relation from layer zero to layer `h` is nonempty. -/
theorem composed_relation_nonempty_of_forward_domains
    (R : ℕ → α → α → Prop) [∀ n, DecidableRel (R n)]
    (B F : ℕ → Finset α)
    (hrec : ∀ n, F (n + 1) = nextLayer (R n) (F n) (B (n + 1)))
    (h : ℕ) (hnonempty : ∀ n ≤ h, (F n).Nonempty) :
    ∃ x ∈ F 0, ∃ y ∈ F h, RelChain R h x y := by
  obtain ⟨y, hy⟩ := hnonempty h le_rfl
  obtain ⟨x, hx, hchain⟩ := forward_member_has_chain R B F hrec hy
  exact ⟨x, hx, y, hy, hchain⟩

/-- Sub-lemma 3: a first empty forward layer has a nonempty predecessor and
no interface edge from that predecessor to any allowed next state. -/
theorem first_death_localization
    (R : ℕ → α → α → Prop) [∀ n, DecidableRel (R n)]
    (B F : ℕ → Finset α)
    (hrec : ∀ n, F (n + 1) = nextLayer (R n) (F n) (B (n + 1)))
    (h : ℕ) (hF0 : (F 0).Nonempty) (hFh : F h = ∅) :
    ∃ t < h, (F t).Nonempty ∧ F (t + 1) = ∅ ∧
      ∀ x ∈ F t, ∀ y ∈ B (t + 1), ¬ R t x y := by
  let hex : ∃ n, F n = ∅ := ⟨h, hFh⟩
  let k := Nat.find hex
  have hkEmpty : F k = ∅ := Nat.find_spec hex
  have hkle : k ≤ h := Nat.find_min' hex hFh
  have hkpos : 0 < k := by
    by_contra hk
    have hk0 : k = 0 := by omega
    rw [hk0] at hkEmpty
    simpa [hkEmpty] using hF0
  obtain ⟨t, hkt⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have htNonempty : (F t).Nonempty := by
    by_contra ht
    have htEmpty : F t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    exact (Nat.find_min hex (by omega : t < k)) htEmpty
  have hth : t < h := by omega
  have htSuccEmpty : F (t + 1) = ∅ := by
    simpa [hkt] using hkEmpty
  refine ⟨t, hth, htNonempty, htSuccEmpty, ?_⟩
  intro x hx y hy hxy
  have hymem : y ∈ nextLayer (R t) (F t) (B (t + 1)) :=
    mem_nextLayer_iff.mpr ⟨hy, x, hx, hxy⟩
  rw [← hrec t, htSuccEmpty] at hymem
  simp at hymem

end FirstDeath

/-! ## Hamilton-path separator counting -/

section Separator

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Number of nonempty runs left in a list after deleting `U`. -/
def remainingRunCount (U : Finset V) : List V → ℕ
  | [] => 0
  | [x] => if x ∈ U then 0 else 1
  | x :: y :: xs =>
      if x ∈ U then remainingRunCount U (y :: xs)
      else if y ∈ U then remainingRunCount U (y :: xs) + 1
      else remainingRunCount U (y :: xs)

def headDeleted (U : Finset V) : List V → ℕ
  | [] => 0
  | x :: _ => if x ∈ U then 1 else 0

def lastDeleted (U : Finset V) : List V → ℕ
  | [] => 0
  | [x] => if x ∈ U then 1 else 0
  | _ :: y :: xs => lastDeleted U (y :: xs)

theorem lastDeleted_eq_ite_of_getLast (U : Finset V) (l : List V) (b : V)
    (h : l.getLast? = some b) :
    lastDeleted U l = if b ∈ U then 1 else 0 := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at h
          subst x
          simp [lastDeleted]
      | cons y ys =>
          simp only [List.getLast?_cons_cons] at h
          simpa [lastDeleted] using ih h

theorem remainingRunCount_endpoint_bound (U : Finset V) (l : List V) :
    remainingRunCount U l + headDeleted U l + lastDeleted U l ≤
      (l.filter fun x ↦ x ∈ U).length + 1 := by
  induction l with
  | nil => simp [remainingRunCount, headDeleted, lastDeleted]
  | cons x xs ih =>
      cases xs with
      | nil =>
          by_cases hx : x ∈ U <;>
            simp [remainingRunCount, headDeleted, lastDeleted, hx]
      | cons y ys =>
          by_cases hx : x ∈ U <;> by_cases hy : y ∈ U <;>
            simp [remainingRunCount, headDeleted, lastDeleted, hx, hy] at ih ⊢ <;> omega

/-- Colors appearing on undeleted list entries. -/
def remainingColors {C : Type v} [DecidableEq C]
    (U : Finset V) (color : V → C) (l : List V) : Finset C :=
  ((l.filter fun x ↦ x ∉ U).map color).toFinset

theorem remainingColors_card_le_runs {C : Type v} [DecidableEq C]
    (U : Finset V) (color : V → C) (l : List V)
    (hchain : l.IsChain fun x y ↦ x ∉ U → y ∉ U → color x = color y) :
    (remainingColors U color l).card ≤ remainingRunCount U l := by
  induction l with
  | nil => simp [remainingColors, remainingRunCount]
  | cons x xs ih =>
      cases xs with
      | nil =>
          by_cases hx : x ∈ U <;> simp [remainingColors, remainingRunCount, hx]
      | cons y ys =>
          rw [List.isChain_cons_cons] at hchain
          have iht := ih hchain.2
          by_cases hx : x ∈ U
          · simpa [remainingColors, remainingRunCount, hx] using iht
          · by_cases hy : y ∈ U
            · have hins := Finset.card_insert_le (color x)
                  (remainingColors U color (y :: ys))
              have heq : remainingColors U color (x :: y :: ys) =
                  insert (color x) (remainingColors U color (y :: ys)) := by
                simp [remainingColors, hx]
              rw [heq]
              simp [remainingRunCount, hx, hy]
              omega
            · have hcolor := hchain.1 hx hy
              have heq : remainingColors U color (x :: y :: ys) =
                  remainingColors U color (y :: ys) := by
                simp [remainingColors, hx, hy, hcolor]
              rw [heq]
              simpa [remainingRunCount, hx, hy] using iht

/-- A component labelling of `G-U`: every label is used by a remaining
vertex, and adjacent remaining vertices have the same label.  Taking labels
to be the connected components of the induced graph gives the usual
component count. -/
structure ComponentLabelling (G : SimpleGraph V) (U : Finset V)
    (C : Type v) [DecidableEq C] where
  labels : Finset C
  color : V → C
  witnessed : ∀ c ∈ labels, ∃ x, x ∉ U ∧ color x = c
  adjacent_same : ∀ {x y}, x ∉ U → y ∉ U → G.Adj x y → color x = color y

/-- Sub-lemma 7, in a general simple-graph component-labelling form.  A
spanning `a`-to-`b` path leaves at most
`|U|+1-[a∈U]-[b∈U]` components after deleting `U`. -/
theorem hamilton_path_separator_bound
    (G : SimpleGraph V) (U : Finset V) {C : Type v} [DecidableEq C]
    (D : ComponentLabelling G U C) (order : List V) (a b : V)
    (hnodup : order.Nodup) (hcover : order.toFinset = Finset.univ)
    (hpath : order.IsChain G.Adj) (hhead : order.head? = some a)
    (hlast : order.getLast? = some b) :
    D.labels.card ≤ U.card + 1 - (if a ∈ U then 1 else 0) -
      (if b ∈ U then 1 else 0) := by
  let localRel : V → V → Prop := fun x y ↦
    x ∉ U → y ∉ U → D.color x = D.color y
  have hlocal : order.IsChain localRel := hpath.imp (by
    intro x y hxy hx hy
    exact D.adjacent_same hx hy hxy)
  have hlabelSub : D.labels ⊆ remainingColors U D.color order := by
    intro c hc
    obtain ⟨x, hxU, hxc⟩ := D.witnessed c hc
    have hxOrder : x ∈ order := by
      rw [← List.mem_toFinset, hcover]
      simp
    rw [remainingColors, List.mem_toFinset]
    exact List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨hxOrder, by simpa using hxU⟩, hxc⟩
  have hcardColors : D.labels.card ≤ remainingRunCount U order :=
    (Finset.card_le_card hlabelSub).trans (remainingColors_card_le_runs U D.color order hlocal)
  have hdeleted : (order.filter fun x ↦ x ∈ U).length = U.card := by
    have hnodupFilter := hnodup.filter (fun x ↦ x ∈ U)
    rw [← List.toFinset_card_of_nodup hnodupFilter]
    congr 1
    ext x
    simp [hcover]
  have hrun := remainingRunCount_endpoint_bound U order
  rw [hdeleted] at hrun
  have hheadDel : headDeleted U order = if a ∈ U then 1 else 0 := by
    cases order with
    | nil => simp at hhead
    | cons x xs =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst x
        simp [headDeleted]
  have hlastDel : lastDeleted U order = if b ∈ U then 1 else 0 :=
    lastDeleted_eq_ite_of_getLast U order b hlast
  rw [hheadDel, hlastDel] at hrun
  omega

end Separator

#print axioms composed_relation_nonempty_of_forward_domains
#print axioms first_death_localization
#print axioms remainingRunCount_endpoint_bound
#print axioms remainingColors_card_le_runs
#print axioms hamilton_path_separator_bound

end Brualdi.RealizationGraph.DodgeCore
