/-
Copyright (c) 2026 Jeffrey S. Baggett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey S. Baggett
-/
/-
# `(Q*)` — statements-first

The endgame theorem of the realization lane's `(Q)` thread, stated at the graph boundary. Prose
sources, all in `topics/flipgraphs/realization/`:

* `QSTAR_DESIGN_2026-08-15.md` §1 — the statement of `(Q*)`.
* `STEP_LEMMA_2026-08-15.md` §0–§3 — Lemma 1 (bottom of a shifted family), Lemma 2 (the universal
  pair is the Gale-least pair), Lemma 3 (clique-sums are exactly the Y-families), and the crossing lemma.
* `QSTAR_BASE_WF_2026-08-15.md` — the rank-two base and the well-foundedness bookkeeping.

## Why this file exists, and what it deliberately does not do

`HladikFink.lean` already states Hladík–Fink Theorem 2.1: the flip graph of a **principal** ideal
`{A : A ≼ M}` is Hamilton-connected. `(Q*)` is the generalization to an **arbitrary** shifted
family, and the generalization is not cosmetic — it is where an **exception class appears**. That
class is invisible in the principal case (every clique-sum is non-principal), which is exactly why
Hladík–Fink's Lemma 3.2, claiming actual neighborhood quotients are principal, could be false
without their Theorem 2.1 being false. See `HF_DEFECT_2026-08-14.md`.

**REUSE-FIRST audit (run before writing this file, per the repository rules).** `HasHamPath` /
`IsHamConnected` already exist in `ColemanDefs.lean` and are reused; `johnsonGraph` exists in
`KeystoneCitedAxioms.lean` but is the *full* Johnson graph, not an induced subgraph on a family, so
it is not the right object here. Nothing else in the development covers shifted families.

**Why `GaleLE` is restated here rather than reused (2026-08-16).** The first version of this file
imported `HladikFink.lean` for `GaleLE`, which put that module — and so Hladík and Fink — back into
the dependency tree of everything downstream, exactly as the mathematics was being taken off it.
`GaleLE` is three lines and carries no content from their paper, so it is defined here and the
import is gone. **This module now has no Hladík–Fink dependency of any kind**, and neither does
anything that imports it.

**Lemma 3 status.** The prose classifies clique-sums as the Y-families `F(k; r, s)`. The
index-free arms are supplied by `lemma3_two_arms`; their coordinate forms, contiguity, and the full
yFamily parametrization are formalized below by `lemma3_arms_are_contiguous`. The complete layer-bottom
table and its yFamily-arm rows use the same `initialSegment` coordinate convention.

## CLOSED OBLIGATIONS OF THIS MODULE

**Why the history is recorded here rather than as declarations.** Until 2026-08-16 these were carried as
`theorem <name> : True := by trivial`. That is a worse mechanism than a `sorry`, and the reason is
worth stating once: such a declaration compiles green, carries **no** `sorryAx`, and an axiom trace
reports it as *"does not depend on any axioms"* — cleaner than a genuinely proved theorem. Any count
of the form "N declarations, 0 `sorryAx`" silently includes it, while it asserts nothing whatsoever.
A `sorry` is honest about what it owes; `True` is not.

The final genuine obligation, **`crossingLemma`**, was discharged on 2026-08-16 by the four positional
regimes and complement-and-reverse duality below.  This module now has no open proof obligations.
-/
import BrualdiLean.ColemanDefs
import BrualdiLean.RealizationGraph.Splice
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Bipartite

namespace Brualdi.RealizationGraph.QStar

open Brualdi.Ledger
open scoped symmDiff

universe u

variable {α : Type u} [LinearOrder α] [DecidableEq α]

/-! ## 0. The Gale order -/

/-- The Gale (dominance) order on finsets, in threshold form: `A ≼ M` when `A` has, for every
threshold `x`, at most as many elements at least `x` as `M` has. Equivalent, over equal
cardinalities, to the sorted pointwise form `aᵢ ≤ mᵢ`. -/
def GaleLE (A M : Finset α) : Prop :=
  ∀ x : α, (A.filter (fun a => x ≤ a)).card ≤ (M.filter (fun m => x ≤ m)).card

set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
theorem galeLE_refl (A : Finset α) : GaleLE A A := fun _ => le_rfl

set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
theorem galeLE_trans {A B C : Finset α} (hAB : GaleLE A B) (hBC : GaleLE B C) :
    GaleLE A C := fun x => (hAB x).trans (hBC x)

/-- The `i`-th smallest element of `A` is at least `x` exactly when at least `k - i` members of
`A` are. Stated with addition rather than truncated subtraction. -/
private theorem le_orderEmbOfFin_iff_card_filter
    {A : Finset α} {k : ℕ} (hA : A.card = k) (x : α) (i : Fin k) :
    x ≤ A.orderEmbOfFin hA i ↔ k ≤ (A.filter (fun a => x ≤ a)).card + (i : ℕ) := by
  let a := A.orderEmbOfFin hA
  let S : Finset (Fin k) := Finset.univ.filter (fun j => x ≤ a j)
  have hcard : (A.filter (fun y => x ≤ y)).card = S.card := by
    have hAimage : Finset.univ.image a = A := by
      apply Finset.ext
      intro y
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, hj⟩
        change A.orderEmbOfFin hA j = y at hj
        exact hj ▸ Finset.orderEmbOfFin_mem A hA j
      · intro hy
        have hyRange : y ∈ Set.range (A.orderEmbOfFin hA) := by
          rw [Finset.range_orderEmbOfFin A hA]
          exact hy
        rcases hyRange with ⟨j, rfl⟩
        exact ⟨j, rfl⟩
    calc
      (A.filter (fun y => x ≤ y)).card =
          ((Finset.univ.image a).filter (fun y => x ≤ y)).card := by
            rw [hAimage]
      _ = ((Finset.univ.filter (fun j => x ≤ a j)).image a).card := by
        rw [Finset.filter_image]
      _ = S.card := by
        rw [Finset.card_image_of_injective _ a.injective]
  constructor
  · intro hxi
    have hsub : Finset.Ici i ⊆ S := by
      intro j hj
      have hij : i ≤ j := Finset.mem_Ici.mp hj
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hxi.trans (a.monotone hij)
    have hcards := Finset.card_le_card hsub
    have hIci : (Finset.Ici i).card = k - (i : ℕ) := Fin.card_Ici i
    rw [hIci] at hcards
    rw [hcard]
    omega
  · intro hbound
    rw [hcard] at hbound
    by_contra hxi
    have hsub : S ⊆ Finset.Ioi i := by
      intro j hj
      have hxaj : x ≤ a j := by
        simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hj
      apply Finset.mem_Ioi.mpr
      exact lt_of_not_ge (fun hji => hxi (hxaj.trans (a.monotone hji)))
    have hcards := Finset.card_le_card hsub
    have hIoi : (Finset.Ioi i).card = k - 1 - (i : ℕ) := Fin.card_Ioi i
    rw [hIoi] at hcards
    omega

/-- **FAITHFULNESS.** The threshold order of `GaleLE` is the manuscript's sorted pointwise order.
Section 7.1 defines `X ≼ Y` by `x_i ≤ y_i` on sorted entries and uses the threshold form
interchangeably; this is that equivalence, so every theorem below reads as a theorem about the
printed order. -/
theorem galeLE_iff_pointwise {A M : Finset α} {k : ℕ} (hA : A.card = k) (hM : M.card = k) :
    GaleLE A M ↔ ∀ i : Fin k, A.orderEmbOfFin hA i ≤ M.orderEmbOfFin hM i := by
  constructor
  · intro hG i
    let x := A.orderEmbOfFin hA i
    have hAbound : k ≤ (A.filter (fun a => x ≤ a)).card + (i : ℕ) :=
      (le_orderEmbOfFin_iff_card_filter hA x i).mp le_rfl
    have hthreshold := hG x
    have hMbound : k ≤ (M.filter (fun m => x ≤ m)).card + (i : ℕ) := by
      omega
    exact (le_orderEmbOfFin_iff_card_filter hM x i).mpr hMbound
  · intro hpoint x
    let c := (A.filter (fun a => x ≤ a)).card
    by_cases hc0 : c = 0
    · change c ≤ (M.filter (fun m => x ≤ m)).card
      omega
    · have hcpos : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr hc0
      have hcle : c ≤ k := by
        dsimp [c]
        rw [← hA]
        exact Finset.card_filter_le _ _
      have hiLt : k - c < k := by omega
      let i : Fin k := ⟨k - c, hiLt⟩
      have hAbound : k ≤ (A.filter (fun a => x ≤ a)).card + (i : ℕ) := by
        dsimp [i, c]
        omega
      have hxAi : x ≤ A.orderEmbOfFin hA i :=
        (le_orderEmbOfFin_iff_card_filter hA x i).mpr hAbound
      have hxMi : x ≤ M.orderEmbOfFin hM i := hxAi.trans (hpoint i)
      have hMbound : k ≤ (M.filter (fun m => x ≤ m)).card + (i : ℕ) :=
        (le_orderEmbOfFin_iff_card_filter hM x i).mp hxMi
      change c ≤ (M.filter (fun m => x ≤ m)).card
      dsimp [i] at hMbound
      omega

/-- An equicardinal lower-closed finset is Gale-below every comparison finset. -/
theorem galeLE_of_card_eq_of_lowerClosed {A B : Finset α}
    (hcard : A.card = B.card)
    (hclosed : ∀ j ∈ A, ∀ i, i < j → i ∈ A) :
    GaleLE A B := by
  intro x
  by_cases hAhi : (A.filter fun a => x ≤ a).Nonempty
  · obtain ⟨j, hj⟩ := hAhi
    have hjA : j ∈ A := (Finset.mem_filter.mp hj).1
    have hxj : x ≤ j := (Finset.mem_filter.mp hj).2
    have hlowSubset : (B.filter fun b => b < x) ⊆ (A.filter fun a => a < x) := by
      intro i hi
      simp only [Finset.mem_filter] at hi ⊢
      exact ⟨hclosed j hjA i (hi.2.trans_le hxj), hi.2⟩
    have hlowcard := Finset.card_le_card hlowSubset
    have hpartA :
        (A.filter fun a => x ≤ a).card + (A.filter fun a => a < x).card = A.card := by
      simpa [not_le] using
        (Finset.card_filter_add_card_filter_not (s := A) (p := fun a => x ≤ a))
    have hpartB :
        (B.filter fun b => x ≤ b).card + (B.filter fun b => b < x).card = B.card := by
      simpa [not_le] using
        (Finset.card_filter_add_card_filter_not (s := B) (p := fun b => x ≤ b))
    omega
  · have hz : (A.filter fun a => x ≤ a).card = 0 :=
      Finset.not_nonempty_iff_eq_empty.mp hAhi ▸ rfl
    omega

/-- Replacing a member by a strictly smaller new member moves downward in Gale order. -/
theorem galeLE_singleDecrement {X : Finset α} {i j : α}
    (hj : j ∈ X) (hij : i < j) (hi : i ∉ X) :
    GaleLE (insert i (X.erase j)) X := by
  intro x
  by_cases hxi : x ≤ i
  · have hxj : x ≤ j := hxi.trans hij.le
    have hi' : i ∉ (X.filter (fun a => x ≤ a)).erase j := by simp [hi]
    have hj' : j ∈ X.filter (fun a => x ≤ a) := by simp [hj, hxj]
    simp only [Finset.filter_insert, hxi, if_true, Finset.filter_erase]
    rw [Finset.card_insert_of_notMem hi', Finset.card_erase_of_mem hj']
    have : 0 < (X.filter (fun a => x ≤ a)).card := Finset.card_pos.mpr ⟨j, hj'⟩
    omega
  · rw [Finset.filter_insert, if_neg hxi]
    exact Finset.card_le_card (by
      intro y
      simp only [Finset.mem_filter, Finset.mem_erase]
      exact fun hy => ⟨hy.1.2, hy.2⟩)

/-- A legal single decrement is strictly smaller in colex order. -/
theorem toColex_singleDecrement_lt {X : Finset α} {i j : α}
    (hj : j ∈ X) (hij : i < j) (hi : i ∉ X) :
    toColex (insert i (X.erase j)) < toColex X := by
  have hiErase : i ∉ X.erase j := by simp [hi]
  have hjErase : j ∉ X.erase j := Finset.notMem_erase j X
  have h := (Finset.Colex.insert_lt_insert hiErase hjErase).2 hij
  simpa only [Finset.insert_erase hj] using h

/-- Gale domination implies colex domination. -/
theorem toColex_le_of_galeLE {A B : Finset α} (hAB : GaleLE A B) :
    toColex A ≤ toColex B := by
  rw [Finset.Colex.toColex_le_toColex]
  intro a haA haB
  by_contra hnone
  push Not at hnone
  have hsub : (B.filter fun b => a ≤ b) ⊆ (A.filter fun b => a ≤ b) := by
    intro b hb
    simp only [Finset.mem_filter] at hb ⊢
    refine ⟨?_, hb.2⟩
    by_contra hbA
    exact (not_le_of_gt (hnone b hb.1 hbA)) hb.2
  have hproper : (B.filter fun b => a ≤ b) ⊂ (A.filter fun b => a ≤ b) := by
    refine ⟨hsub, ?_⟩
    intro hrev
    exact haB ((Finset.mem_filter.mp
      (hrev (Finset.mem_filter.mpr ⟨haA, le_rfl⟩))).1)
  exact (not_lt_of_ge (hAB a)) (Finset.card_lt_card hproper)

/-- Unless two equicardinal Gale-comparable finsets coincide, one can make a legal decrement of
the upper finset that remains above the lower one and strictly reduces their set difference. -/
theorem exists_singleDecrement_preserving_galeLE {B X : Finset α}
    (hcard : B.card = X.card) (hne : B ≠ X) (hBX : GaleLE B X) :
    ∃ i j : α,
      j ∈ X ∧ i < j ∧ i ∉ X ∧
      GaleLE B (insert i (X.erase j)) ∧
      (B \ insert i (X.erase j)).card < (B \ X).card := by
  have hBdiff : (B \ X).Nonempty := Finset.sdiff_nonempty.mpr (by
    intro hsub
    exact hne (Finset.eq_of_subset_of_card_le hsub hcard.ge))
  have hXdiff : (X \ B).Nonempty := Finset.sdiff_nonempty.mpr (by
    intro hsub
    exact hne (Finset.eq_of_subset_of_card_le hsub hcard.le).symm)
  let i := (B \ X).max' hBdiff
  let j := (X \ B).max' hXdiff
  have hiDiff : i ∈ B \ X := by exact Finset.max'_mem _ _
  have hjDiff : j ∈ X \ B := by exact Finset.max'_mem _ _
  have hiB : i ∈ B := Finset.mem_sdiff.mp hiDiff |>.1
  have hiX : i ∉ X := Finset.mem_sdiff.mp hiDiff |>.2
  have hjX : j ∈ X := Finset.mem_sdiff.mp hjDiff |>.1
  have hjB : j ∉ B := Finset.mem_sdiff.mp hjDiff |>.2
  have hij : i < j := by
    by_contra hnot
    have hji : j ≤ i := le_of_not_gt hnot
    have hfilter : B.filter (fun y => i ≤ y) =
        insert i (X.filter (fun y => i ≤ y)) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hyB, hiy⟩
        by_cases hyX : y ∈ X
        · exact Or.inr ⟨hyX, hiy⟩
        · left
          exact le_antisymm (Finset.le_max' (B \ X) y (by simp [hyB, hyX])) hiy
      · rintro (rfl | ⟨hyX, hiy⟩)
        · exact ⟨hiB, le_rfl⟩
        · refine ⟨?_, hiy⟩
          by_contra hyB
          have hyj : y ≤ j := Finset.le_max' (X \ B) y (by simp [hyX, hyB])
          have hyi : y ≤ i := hyj.trans hji
          have : y = i := le_antisymm hyi hiy
          subst y
          exact hiX hyX
    have hni : i ∉ X.filter (fun y => i ≤ y) := by simp [hiX]
    have hcontra := hBX i
    rw [hfilter, Finset.card_insert_of_notMem hni] at hcontra
    omega
  refine ⟨i, j, hjX, hij, hiX, ?_, ?_⟩
  · intro x
    by_cases hxi : x ≤ i
    · have hxj : x ≤ j := hxi.trans hij.le
      have hi' : i ∉ (X.filter (fun y => x ≤ y)).erase j := by simp [hiX]
      have hj' : j ∈ X.filter (fun y => x ≤ y) := by simp [hjX, hxj]
      have hpos : 0 < (X.filter (fun y => x ≤ y)).card := Finset.card_pos.mpr ⟨j, hj'⟩
      simpa only [Finset.filter_insert, hxi, if_true, Finset.filter_erase,
        Finset.card_insert_of_notMem hi', Finset.card_erase_of_mem hj',
        Nat.sub_add_cancel hpos] using hBX x
    · apply Finset.card_le_card
      intro y hy
      simp only [Finset.mem_filter] at hy ⊢
      have hyX : y ∈ X := by
        by_contra hynX
        have hyi : y ≤ i := Finset.le_max' (B \ X) y (by simp [hy.1, hynX])
        exact hxi (hy.2.trans hyi)
      have hyj : y ≠ j := by
        intro hyj
        subst y
        exact hjB hy.1
      exact ⟨by simp [hyX, hyj], hy.2⟩
  · have hsdiff : B \ insert i (X.erase j) = (B \ X).erase i := by
      ext y
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨hyB, hne⟩
        have hyi : y ≠ i := fun h => hne (Or.inl h)
        have hyX : y ∉ X := by
          intro hyX
          exact hne (Or.inr ⟨fun hyj => hjB (hyj ▸ hyB), hyX⟩)
        exact ⟨hyi, hyB, hyX⟩
      · rintro ⟨hyi, hyB, hyX⟩
        exact ⟨hyB, by simp [hyi, hyX]⟩
    rw [hsdiff, Finset.card_erase_of_mem hiDiff]
    have hpos : 0 < (B \ X).card := Finset.card_pos.mpr hBdiff
    omega

/-! ## 1. Shifted families, two ways -/

/-- **Shifted**, in the single-decrement form used throughout `STEP_LEMMA_2026-08-15.md` §0:
replacing an element of `X` by a smaller element not in `X` stays in the family. -/
def IsShifted (F : Finset (Finset α)) (κ : ℕ) : Prop :=
  F.Nonempty ∧ (∀ X ∈ F, X.card = κ) ∧
    ∀ X ∈ F, ∀ i j : α, j ∈ X → i < j → i ∉ X → insert i (X.erase j) ∈ F

/-- **Gale ideal**: a nonempty down-closed family of `κ`-sets.
`MAXIMAL_INDUCTION_LEAD_2026-08-14.md`
§1 uses this form. -/
def IsGaleIdeal (F : Finset (Finset α)) (κ : ℕ) : Prop :=
  F.Nonempty ∧ (∀ X ∈ F, X.card = κ) ∧
    ∀ X ∈ F, ∀ B : Finset α, B.card = κ → GaleLE B X → B ∈ F

/-- **FAITHFULNESS OBLIGATION.** The two forms agree. The prose uses them interchangeably ("A Gale
ideal `I` is a nonempty down-closed family — equivalently a **shifted** family"), so this
equivalence
is load-bearing for reading any statement below as the statement the notes prove. It is stated, not
assumed, for the same reason `galeLE_iff_sorted_pointwise` is. -/
theorem isShifted_iff_isGaleIdeal (F : Finset (Finset α)) (κ : ℕ) :
    IsShifted F κ ↔ IsGaleIdeal F κ := by
  constructor
  · rintro ⟨hne, hcard, hshift⟩
    refine ⟨hne, hcard, ?_⟩
    intro X hXF B hBcard hBX
    have hBXcard : B.card = X.card := hBcard.trans (hcard X hXF).symm
    generalize hn : (B \ X).card = n
    induction n using Nat.strong_induction_on generalizing X with
    | h n ih =>
        by_cases hEq : B = X
        · rw [hEq]
          exact hXF
        · obtain ⟨i, j, hjX, hij, hiX, hBnext, hdecrease⟩ :=
            exists_singleDecrement_preserving_galeLE hBXcard hEq hBX
          let X' := insert i (X.erase j)
          have hX'F : X' ∈ F := hshift X hXF i j hjX hij hiX
          apply ih (B \ X').card
          · simpa [hn] using hdecrease
          · exact hX'F
          · exact hBnext
          · exact hBcard.trans (hcard X' hX'F).symm
          · rfl
  · rintro ⟨hne, hcard, hdown⟩
    refine ⟨hne, hcard, ?_⟩
    intro X hXF i j hjX hij hiX
    have hiErase : i ∉ X.erase j := by simp [hiX]
    have hpos : 0 < X.card := Finset.card_pos.mpr ⟨j, hjX⟩
    have hreplacementCard : (insert i (X.erase j)).card = κ := by
      calc
        (insert i (X.erase j)).card = X.card - 1 + 1 := by
          rw [Finset.card_insert_of_notMem hiErase, Finset.card_erase_of_mem hjX]
        _ = X.card := Nat.sub_add_cancel hpos
        _ = κ := hcard X hXF
    exact hdown X hXF _ hreplacementCard (galeLE_singleDecrement hjX hij hiX)

/-! ## 1.1. The decrement census -/

/-- All distinct finsets obtained from `W` by replacing one member by a strictly smaller new
member. The locally finite lower-order hypothesis makes the collection finite. -/
def singleDecrements [LocallyFiniteOrderBot α] (W : Finset α) : Finset (Finset α) :=
  W.biUnion fun j => (Finset.Iio j \ W).image fun i => insert i (W.erase j)

theorem mem_singleDecrements [LocallyFiniteOrderBot α] {V W : Finset α} :
    V ∈ singleDecrements W ↔
      ∃ j ∈ W, ∃ i : α, i < j ∧ i ∉ W ∧ V = insert i (W.erase j) := by
  simp only [singleDecrements, Finset.mem_biUnion, Finset.mem_image, Finset.mem_sdiff,
    Finset.mem_Iio]
  aesop

/-- **Decrement census.** For `W = [k] - i + a`, where `[k]` is the initial interval `Iic k`
and `i ≤ k < a`, its distinct single decrements split into two explicit collections:

* replace `a` by `i` or by an element strictly between `k` and `a`;
* replace an element in `(i, k]` by `i`.

The equality is an equality of finsets, so duplicates are removed on both sides. -/
theorem singleDecrements_insert_erase_Iic [LocallyFiniteOrder α]
    [LocallyFiniteOrderBot α] {i k a : α}
    (hik : i ≤ k) (hka : k < a) :
    let W := insert a ((Finset.Iic k).erase i)
    singleDecrements W =
      ((insert i (Finset.Ioo k a)).image fun a' => insert a' (W.erase a)) ∪
      ((Finset.Ioc i k).image fun j => insert i (W.erase j)) := by
  let W := insert a ((Finset.Iic k).erase i)
  change singleDecrements W =
    ((insert i (Finset.Ioo k a)).image fun a' => insert a' (W.erase a)) ∪
    ((Finset.Ioc i k).image fun j => insert i (W.erase j))
  ext V
  rw [mem_singleDecrements]
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨j, hjW, x, hxj, hxW, rfl⟩
    by_cases hja : j = a
    · subst j
      left
      refine ⟨x, ?_, rfl⟩
      by_cases hxk : x ≤ k
      · apply Finset.mem_insert.mpr
        refine Or.inl ?_
        by_contra hxi
        apply hxW
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr
          ⟨hxi, Finset.mem_Iic.mpr hxk⟩))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_Ioo.mpr
          ⟨lt_of_not_ge hxk, hxj⟩))
    · right
      have hjrest : j ∈ (Finset.Iic k).erase i := by
        rcases Finset.mem_insert.mp hjW with h | h
        · exact absurd h hja
        · exact h
      have hji : j ≠ i := (Finset.mem_erase.mp hjrest).1
      have hjk : j ≤ k := Finset.mem_Iic.mp (Finset.mem_erase.mp hjrest).2
      have hxk : x ≤ k := hxj.le.trans hjk
      have hxi : x = i := by
        by_contra hxi
        apply hxW
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr
          ⟨hxi, Finset.mem_Iic.mpr hxk⟩))
      subst x
      exact ⟨j, Finset.mem_Ioc.mpr ⟨hxj, hjk⟩, rfl⟩
  · rintro (h | h)
    · rcases h with ⟨x, hx, hV⟩
      refine ⟨a, by simp [W], x, ?_, ?_, hV.symm⟩
      · rcases Finset.mem_insert.mp hx with hxi | hx
        · subst x
          exact hik.trans_lt hka
        · exact (Finset.mem_Ioo.mp hx).2
      · rcases Finset.mem_insert.mp hx with hxi | hx
        · subst x
          have hia : i ≠ a := (hik.trans_lt hka).ne
          simp [W, hia]
        · have hkx : k < x := (Finset.mem_Ioo.mp hx).1
          have hxa : x ≠ a := (Finset.mem_Ioo.mp hx).2.ne
          simp [W, hxa, not_le.mpr hkx]
    · rcases h with ⟨j, hj, hV⟩
      have hij : i < j := (Finset.mem_Ioc.mp hj).1
      have hjk : j ≤ k := (Finset.mem_Ioc.mp hj).2
      have hja : j ≠ a := (hjk.trans_lt hka).ne
      have hji : j ≠ i := hij.ne'
      have hia : i ≠ a := (hik.trans_lt hka).ne
      refine ⟨j, ?_, i, hij, ?_, hV.symm⟩
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr
          ⟨hji, Finset.mem_Iic.mpr hjk⟩))
      · simp [W, hia]

/-- Cardinal form of the decrement census. In a discrete interval such as the positive naturals,
the two summands are respectively the sizes of `{i} ∪ (k,a)` and `(i,k]`. -/
theorem card_singleDecrements_insert_erase_Iic [LocallyFiniteOrder α]
    [LocallyFiniteOrderBot α] {i k a : α} (hik : i ≤ k) (hka : k < a) :
    (singleDecrements (insert a ((Finset.Iic k).erase i))).card =
      (Finset.Ioo k a).card + 1 + (Finset.Ioc i k).card := by
  let W := insert a ((Finset.Iic k).erase i)
  let L := (insert i (Finset.Ioo k a)).image fun a' => insert a' (W.erase a)
  let R := (Finset.Ioc i k).image fun j => insert i (W.erase j)
  have hia : i ≠ a := (hik.trans_lt hka).ne
  have hiW : i ∉ W := by simp [W, hia]
  have hleft_lt : ∀ x ∈ insert i (Finset.Ioo k a), x < a := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hxi | hx
    · subst x
      exact hik.trans_lt hka
    · exact (Finset.mem_Ioo.mp hx).2
  have hleft_notW : ∀ x ∈ insert i (Finset.Ioo k a), x ∉ W := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hxi | hx
    · subst x
      exact hiW
    · have hkx : k < x := (Finset.mem_Ioo.mp hx).1
      have hxa : x ≠ a := (Finset.mem_Ioo.mp hx).2.ne
      simp [W, hxa, not_le.mpr hkx]
  have hLinj : Set.InjOn (fun x => insert x (W.erase a))
      ↑(insert i (Finset.Ioo k a) : Finset α) := by
    intro x hx y _ hxy
    exact (Finset.insert_inj (by
      exact fun hxmem => hleft_notW x hx (Finset.mem_of_mem_erase hxmem))).mp hxy
  have hRinj : Set.InjOn (fun j => insert i (W.erase j)) (Finset.Ioc i k) := by
    intro j₁ hj₁ j₂ hj₂ hEq
    have hj₁W : j₁ ∈ W := by
      have hij₁ : i < j₁ := (Finset.mem_Ioc.mp hj₁).1
      have hj₁k : j₁ ≤ k := (Finset.mem_Ioc.mp hj₁).2
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr
        ⟨hij₁.ne', Finset.mem_Iic.mpr hj₁k⟩))
    have hErase := congrArg (fun S : Finset α => S.erase i) hEq
    have hiErase₁ : i ∉ W.erase j₁ := fun h => hiW (Finset.mem_of_mem_erase h)
    have hiErase₂ : i ∉ W.erase j₂ := fun h => hiW (Finset.mem_of_mem_erase h)
    have hErase' : W.erase j₁ = W.erase j₂ := by
      simpa [Finset.erase_insert, hiErase₁, hiErase₂] using hErase
    exact (Finset.erase_inj W hj₁W).mp hErase'
  have hLR : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro V hVL hVR
    rcases Finset.mem_image.mp hVL with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp hVR with ⟨j, hj, hEq⟩
    have hxa : x ≠ a := (hleft_lt x hx).ne
    have hjk : j ≤ k := (Finset.mem_Ioc.mp hj).2
    have haj : a ≠ j := (hjk.trans_lt hka).ne'
    have haW : a ∈ W := by simp [W]
    have haRight : a ∈ insert i (W.erase j) :=
      Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨haj, haW⟩))
    have haLeft : a ∈ insert x (W.erase a) := hEq ▸ haRight
    have hax : a = x := by simpa using haLeft
    exact hxa hax.symm
  have hcensus : singleDecrements W = L ∪ R := by
    simpa [W, L, R] using singleDecrements_insert_erase_Iic hik hka
  rw [hcensus, Finset.card_union_of_disjoint hLR]
  rw [show L.card = (insert i (Finset.Ioo k a)).card by
        exact Finset.card_image_of_injOn hLinj]
  rw [show R.card = (Finset.Ioc i k).card by
        exact Finset.card_image_of_injOn hRinj]
  rw [Finset.card_insert_of_notMem (by simp [not_lt_of_ge hik])]

/-! ## 2. The exchange graph `J(F)` -/

/-- Vertices of `J(F)`: the members of `F`. -/
abbrev ExchangeV (F : Finset (Finset α)) : Type u := {X : Finset α // X ∈ F}

/-- **The exchange graph `J(F)`**: members of `F` joined when their symmetric difference has two
elements. -/
def exchangeGraph (F : Finset (Finset α)) : SimpleGraph (ExchangeV F) :=
  SimpleGraph.fromRel fun A B => (A.val ∆ B.val).card = 2

/-! ## 3. Lemma 1 — the bottom of a shifted family -/

/-- `X` is Gale-least in `F`. -/
def IsGaleLeast (F : Finset (Finset α)) (X : Finset α) : Prop :=
  X ∈ F ∧ ∀ Y ∈ F, GaleLE X Y

/-- `X` is Gale-least among `F` with `m₁` removed — the "second-least". -/
def IsGaleSecondLeast (F : Finset (Finset α)) (m₁ X : Finset α) : Prop :=
  X ∈ F ∧ X ≠ m₁ ∧ ∀ Y ∈ F, Y ≠ m₁ → GaleLE X Y

/-- The two bottom members, together with the boundary data used by the small-family census. -/
theorem exists_gale_bottom_pair_with_boundary {F : Finset (Finset α)} {κ : ℕ}
    (hF : IsShifted F κ) (h2 : 2 ≤ F.card) :
    ∃ m₁ m₂ : Finset α,
      IsGaleLeast F m₁ ∧ IsGaleSecondLeast F m₁ m₂ ∧
      ∃ i j : α,
        i ∈ m₁ ∧ i ∉ m₂ ∧ j ∈ m₂ ∧ j ∉ m₁ ∧ i < j ∧
        m₂ = insert j (m₁.erase i) ∧
        (∀ z ∈ m₁, z ≤ i) ∧ (∀ z, z < j → z ∈ m₁) := by
  rcases hF with ⟨hFne, hcard, hshift⟩
  obtain ⟨m₁, hm₁F, hm₁min⟩ :=
    Finset.exists_min_image F (fun X => toColex X) hFne
  have hm₁closed : ∀ j ∈ m₁, ∀ i, i < j → i ∈ m₁ := by
    intro j hj i hij
    by_contra hi
    have hnextF : insert i (m₁.erase j) ∈ F := hshift m₁ hm₁F i j hj hij hi
    have hlt := toColex_singleDecrement_lt hj hij hi
    exact (not_lt_of_ge (hm₁min _ hnextF)) hlt
  have hm₁least : IsGaleLeast F m₁ := by
    refine ⟨hm₁F, ?_⟩
    intro Y hY
    exact galeLE_of_card_eq_of_lowerClosed
      ((hcard m₁ hm₁F).trans (hcard Y hY).symm) hm₁closed
  have hFgt1 : 1 < F.card := by omega
  obtain ⟨m₂w, hm₂wF, hm₂wne⟩ := F.exists_mem_ne hFgt1 m₁
  have hresne : (F.erase m₁).Nonempty :=
    ⟨m₂w, Finset.mem_erase.mpr ⟨hm₂wne, hm₂wF⟩⟩
  obtain ⟨m₂, hm₂res, hm₂min⟩ :=
    Finset.exists_min_image (F.erase m₁) (fun X => toColex X) hresne
  have hm₂ne : m₂ ≠ m₁ := (Finset.mem_erase.mp hm₂res).1
  have hm₂F : m₂ ∈ F := (Finset.mem_erase.mp hm₂res).2
  have hcards : m₁.card = m₂.card := (hcard m₁ hm₁F).trans (hcard m₂ hm₂F).symm
  obtain ⟨i, j, hjm₂, hij, him₂, _hgale, _hdiff⟩ :=
    exists_singleDecrement_preserving_galeLE hcards hm₂ne.symm (hm₁least.2 m₂ hm₂F)
  let D := insert i (m₂.erase j)
  have hDF : D ∈ F := hshift m₂ hm₂F i j hjm₂ hij him₂
  have hDlt : toColex D < toColex m₂ := toColex_singleDecrement_lt hjm₂ hij him₂
  have hDeq : D = m₁ := by
    by_contra hDne
    have hDres : D ∈ F.erase m₁ := Finset.mem_erase.mpr ⟨hDne, hDF⟩
    exact (not_lt_of_ge (hm₂min D hDres)) hDlt
  have hm₁eq : m₁ = insert i (m₂.erase j) := hDeq.symm
  have him₁ : i ∈ m₁ := by simp [hm₁eq]
  have hjm₁ : j ∉ m₁ := by simp [hm₁eq, hij.ne']
  have hm₂repr : m₂ = insert j (m₁.erase i) := by
    calc
      m₂ = insert j (m₂.erase j) := (Finset.insert_erase hjm₂).symm
      _ = insert j (m₁.erase i) := by rw [hm₁eq]; simp [him₂, hij.ne]
  have himax : ∀ z ∈ m₁, z ≤ i := by
    intro z hzm₁
    by_contra hzi
    have hiz : i < z := lt_of_not_ge hzi
    have hznei : z ≠ i := hiz.ne'
    have hzm₂erase : z ∈ m₂.erase j := by
      have : z ∈ insert i (m₂.erase j) := hm₁eq ▸ hzm₁
      exact (Finset.mem_insert.mp this).resolve_left hznei
    have hzm₂ : z ∈ m₂ := Finset.mem_of_mem_erase hzm₂erase
    have hznej : z ≠ j := (Finset.mem_erase.mp hzm₂erase).1
    let D' := insert i (m₂.erase z)
    have hD'F : D' ∈ F := hshift m₂ hm₂F i z hzm₂ hiz him₂
    have hD'lt : toColex D' < toColex m₂ := toColex_singleDecrement_lt hzm₂ hiz him₂
    have hjD' : j ∈ D' := by simp [D', hjm₂, hznej.symm, hij.ne']
    have hD'ne : D' ≠ m₁ := fun h => hjm₁ (h ▸ hjD')
    have hD'res : D' ∈ F.erase m₁ := Finset.mem_erase.mpr ⟨hD'ne, hD'F⟩
    exact (not_lt_of_ge (hm₂min D' hD'res)) hD'lt
  have hjmin : ∀ z, z < j → z ∈ m₁ := by
    intro z hzj
    by_contra hzm₁
    have hznei : z ≠ i := fun h => hzm₁ (h ▸ him₁)
    have hzm₂ : z ∉ m₂ := by
      intro hz
      have hznej : z ≠ j := hzj.ne
      have : z ∈ insert i (m₂.erase j) := Finset.mem_insert.mpr
        (Or.inr (Finset.mem_erase.mpr ⟨hznej, hz⟩))
      exact hzm₁ (hm₁eq.symm ▸ this)
    let D' := insert z (m₂.erase j)
    have hD'F : D' ∈ F := hshift m₂ hm₂F z j hjm₂ hzj hzm₂
    have hD'lt : toColex D' < toColex m₂ := toColex_singleDecrement_lt hjm₂ hzj hzm₂
    have hiD' : i ∉ D' := by simp [D', him₂, hznei.symm]
    have hD'ne : D' ≠ m₁ := fun h => hiD' (h ▸ him₁)
    have hD'res : D' ∈ F.erase m₁ := Finset.mem_erase.mpr ⟨hD'ne, hD'F⟩
    exact (not_lt_of_ge (hm₂min D' hD'res)) hD'lt
  have hm₂second : IsGaleSecondLeast F m₁ m₂ := by
    refine ⟨hm₂F, hm₂ne, ?_⟩
    intro Y hY hYne
    intro x
    by_cases hxi : x ≤ i
    · have hxj : x ≤ j := hxi.trans hij.le
      have hiHigh : i ∈ m₁.filter (fun z => x ≤ z) := Finset.mem_filter.mpr ⟨him₁, hxi⟩
      have hjHigh : j ∉ m₁.filter (fun z => x ≤ z) := by simp [hjm₁]
      have heq : (m₂.filter fun z => x ≤ z).card = (m₁.filter fun z => x ≤ z).card := by
        rw [hm₂repr, Finset.filter_insert, if_pos hxj, Finset.filter_erase]
        rw [Finset.card_insert_of_notMem (by simp [hjHigh]),
          Finset.card_erase_of_mem hiHigh]
        exact Nat.sub_add_cancel (Finset.card_pos.mpr ⟨i, hiHigh⟩)
      rw [heq]
      exact hm₁least.2 Y hY x
    · have hix : i < x := lt_of_not_ge hxi
      by_cases hjx : j < x
      · have heq : (m₂.filter fun z => x ≤ z) = (m₁.filter fun z => x ≤ z) := by
          rw [hm₂repr, Finset.filter_insert, if_neg (not_le_of_gt hjx),
            Finset.filter_erase]
          exact Finset.erase_eq_of_notMem (by simp [not_le_of_gt hix])
        rw [heq]
        exact hm₁least.2 Y hY x
      · have hxj : x ≤ j := le_of_not_gt hjx
        have hm₁empty : m₁.filter (fun z => x ≤ z) = ∅ :=
          Finset.filter_eq_empty_iff.mpr (fun z hzm₁ hxz =>
            (not_le_of_gt hix) (hxz.trans (himax z hzm₁)))
        have hm₂one : (m₂.filter fun z => x ≤ z).card = 1 := by
          rw [hm₂repr, Finset.filter_insert, if_pos hxj, Finset.filter_erase, hm₁empty]
          simp
        have hYdiff : (Y \ m₁).Nonempty := Finset.sdiff_nonempty.mpr (by
          intro hsub
          exact hYne (Finset.eq_of_subset_of_card_le hsub (by
            rw [hcard Y hY, hcard m₁ hm₁F])))
        obtain ⟨q, hq⟩ := hYdiff
        have hqY : q ∈ Y := (Finset.mem_sdiff.mp hq).1
        have hqm₁ : q ∉ m₁ := (Finset.mem_sdiff.mp hq).2
        have hjq : j ≤ q := le_of_not_gt (fun hqj => hqm₁ (hjmin q hqj))
        have hYpos : 1 ≤ (Y.filter fun z => x ≤ z).card := Finset.one_le_card.mpr
          ⟨q, Finset.mem_filter.mpr ⟨hqY, hxj.trans hjq⟩⟩
        omega
  exact ⟨m₁, m₂, hm₁least, hm₂second, i, j, him₁, him₂, hjm₂, hjm₁, hij,
    hm₂repr, himax, hjmin⟩

/-- If a member has at least two elements outside the lower-closed bottom member, shifting gives
four distinct family members different from the original member.  See
`four_le_card_singleDecrements_of_two_outside` for the stronger conclusion that the four witnesses
are actual single decrements. -/
theorem four_distinct_decrements_of_two_outside {F : Finset (Finset α)} {κ : ℕ}
    (hF : IsShifted F κ) {m₁ W : Finset α}
    (hm₁F : m₁ ∈ F) (hWF : W ∈ F)
    (hbelow : ∀ p ∈ m₁, ∀ a, a ∉ m₁ → p < a)
    (htwo : 2 ≤ (W \ m₁).card) :
    ∃ D₁₁ D₁₂ D₂₁ D₂₂ : Finset α,
      D₁₁ ∈ F ∧ D₁₂ ∈ F ∧ D₂₁ ∈ F ∧ D₂₂ ∈ F ∧
      D₁₁ ≠ W ∧ D₁₂ ≠ W ∧ D₂₁ ≠ W ∧ D₂₂ ≠ W ∧
      D₁₁ ≠ D₁₂ ∧ D₁₁ ≠ D₂₁ ∧ D₁₁ ≠ D₂₂ ∧
      D₁₂ ≠ D₂₁ ∧ D₁₂ ≠ D₂₂ ∧ D₂₁ ≠ D₂₂ := by
  rcases hF with ⟨_, hcard, hshift⟩
  have hdiffcard : (m₁ \ W).card = (W \ m₁).card := by
    have h₁ := Finset.card_sdiff_add_card_inter m₁ W
    have h₂ := Finset.card_sdiff_add_card_inter W m₁
    rw [Finset.inter_comm W m₁] at h₂
    have hsame : m₁.card = W.card := (hcard m₁ hm₁F).trans (hcard W hWF).symm
    omega
  have htwo' : 2 ≤ (m₁ \ W).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.mp (show 1 < (W \ m₁).card by omega)
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    Finset.one_lt_card.mp (show 1 < (m₁ \ W).card by omega)
  have haW : a ∈ W := (Finset.mem_sdiff.mp ha).1
  have ham₁ : a ∉ m₁ := (Finset.mem_sdiff.mp ha).2
  have hbW : b ∈ W := (Finset.mem_sdiff.mp hb).1
  have hbm₁ : b ∉ m₁ := (Finset.mem_sdiff.mp hb).2
  have hpm₁ : p ∈ m₁ := (Finset.mem_sdiff.mp hp).1
  have hpW : p ∉ W := (Finset.mem_sdiff.mp hp).2
  have hqm₁ : q ∈ m₁ := (Finset.mem_sdiff.mp hq).1
  have hqW : q ∉ W := (Finset.mem_sdiff.mp hq).2
  have hpa : p < a := hbelow p hpm₁ a ham₁
  have hqa : q < a := hbelow q hqm₁ a ham₁
  have hpb : p < b := hbelow p hpm₁ b hbm₁
  have hqb : q < b := hbelow q hqm₁ b hbm₁
  let D₁₁ := insert p (W.erase a)
  let D₁₂ := insert q (W.erase a)
  let D₂₁ := insert p (W.erase b)
  let D₂₂ := insert q (W.erase b)
  have hD₁₁F : D₁₁ ∈ F := hshift W hWF p a haW hpa hpW
  have hD₁₂F : D₁₂ ∈ F := hshift W hWF q a haW hqa hqW
  have hD₂₁F : D₂₁ ∈ F := hshift W hWF p b hbW hpb hpW
  have hD₂₂F : D₂₂ ∈ F := hshift W hWF q b hbW hqb hqW
  have hD₁₁W : D₁₁ ≠ W := by
    intro h
    exact hpW (h ▸ Finset.mem_insert_self p (W.erase a))
  have hD₁₂W : D₁₂ ≠ W := by
    intro h
    exact hqW (h ▸ Finset.mem_insert_self q (W.erase a))
  have hD₂₁W : D₂₁ ≠ W := by
    intro h
    exact hpW (h ▸ Finset.mem_insert_self p (W.erase b))
  have hD₂₂W : D₂₂ ≠ W := by
    intro h
    exact hqW (h ▸ Finset.mem_insert_self q (W.erase b))
  have hpD₁₂ : p ∉ D₁₂ := by simp [D₁₂, hpW, hpq]
  have hpD₂₂ : p ∉ D₂₂ := by simp [D₂₂, hpW, hpq]
  have hbD₁₁ : b ∈ D₁₁ := by simp [D₁₁, hbW, hab.symm]
  have hbD₁₂ : b ∈ D₁₂ := by simp [D₁₂, hbW, hab.symm]
  have hbp : b ≠ p := fun h => hpW (h ▸ hbW)
  have hbq : b ≠ q := fun h => hqW (h ▸ hbW)
  have hbD₂₁ : b ∉ D₂₁ := by simp [D₂₁, hbp]
  have hbD₂₂ : b ∉ D₂₂ := by simp [D₂₂, hbq]
  have hD₁₁D₁₂ : D₁₁ ≠ D₁₂ := by
    intro h
    exact hpD₁₂ (h ▸ Finset.mem_insert_self p (W.erase a))
  have hD₁₁D₂₁ : D₁₁ ≠ D₂₁ := by intro h; exact hbD₂₁ (h ▸ hbD₁₁)
  have hD₁₁D₂₂ : D₁₁ ≠ D₂₂ := by intro h; exact hbD₂₂ (h ▸ hbD₁₁)
  have hD₁₂D₂₁ : D₁₂ ≠ D₂₁ := by intro h; exact hbD₂₁ (h ▸ hbD₁₂)
  have hD₁₂D₂₂ : D₁₂ ≠ D₂₂ := by intro h; exact hbD₂₂ (h ▸ hbD₁₂)
  have hD₂₁D₂₂ : D₂₁ ≠ D₂₂ := by
    intro h
    exact hpD₂₂ (h ▸ Finset.mem_insert_self p (W.erase b))
  exact ⟨D₁₁, D₁₂, D₂₁, D₂₂, hD₁₁F, hD₁₂F, hD₂₁F, hD₂₂F,
    hD₁₁W, hD₁₂W, hD₂₁W, hD₂₂W, hD₁₁D₁₂, hD₁₁D₂₁, hD₁₁D₂₂,
    hD₁₂D₂₁, hD₁₂D₂₂, hD₂₁D₂₂⟩

/-- **Lemma 7.1(d), order-generic form.** If an equicardinal set `W` has at least two
elements outside a lower-closed bottom set `m₁`, then `W` has at least four distinct actual single
decrements. -/
theorem four_le_card_singleDecrements_of_two_outside [LocallyFiniteOrderBot α]
    {m₁ W : Finset α} (hcard : m₁.card = W.card)
    (hbelow : ∀ p ∈ m₁, ∀ a, a ∉ m₁ → p < a)
    (htwo : 2 ≤ (W \ m₁).card) :
    4 ≤ (singleDecrements W).card := by
  have hdiffcard : (m₁ \ W).card = (W \ m₁).card := by
    have h₁ := Finset.card_sdiff_add_card_inter m₁ W
    have h₂ := Finset.card_sdiff_add_card_inter W m₁
    rw [Finset.inter_comm W m₁] at h₂
    omega
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.mp (show 1 < (W \ m₁).card by omega)
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    Finset.one_lt_card.mp (show 1 < (m₁ \ W).card by omega)
  have haW : a ∈ W := (Finset.mem_sdiff.mp ha).1
  have ham₁ : a ∉ m₁ := (Finset.mem_sdiff.mp ha).2
  have hbW : b ∈ W := (Finset.mem_sdiff.mp hb).1
  have hbm₁ : b ∉ m₁ := (Finset.mem_sdiff.mp hb).2
  have hpm₁ : p ∈ m₁ := (Finset.mem_sdiff.mp hp).1
  have hpW : p ∉ W := (Finset.mem_sdiff.mp hp).2
  have hqm₁ : q ∈ m₁ := (Finset.mem_sdiff.mp hq).1
  have hqW : q ∉ W := (Finset.mem_sdiff.mp hq).2
  have hpa : p < a := hbelow p hpm₁ a ham₁
  have hqa : q < a := hbelow q hqm₁ a ham₁
  have hpb : p < b := hbelow p hpm₁ b hbm₁
  have hqb : q < b := hbelow q hqm₁ b hbm₁
  let D₁₁ := insert p (W.erase a)
  let D₁₂ := insert q (W.erase a)
  let D₂₁ := insert p (W.erase b)
  let D₂₂ := insert q (W.erase b)
  have hD₁₁ : D₁₁ ∈ singleDecrements W :=
    mem_singleDecrements.mpr ⟨a, haW, p, hpa, hpW, rfl⟩
  have hD₁₂ : D₁₂ ∈ singleDecrements W :=
    mem_singleDecrements.mpr ⟨a, haW, q, hqa, hqW, rfl⟩
  have hD₂₁ : D₂₁ ∈ singleDecrements W :=
    mem_singleDecrements.mpr ⟨b, hbW, p, hpb, hpW, rfl⟩
  have hD₂₂ : D₂₂ ∈ singleDecrements W :=
    mem_singleDecrements.mpr ⟨b, hbW, q, hqb, hqW, rfl⟩
  have hpD₁₂ : p ∉ D₁₂ := by simp [D₁₂, hpW, hpq]
  have hpD₂₂ : p ∉ D₂₂ := by simp [D₂₂, hpW, hpq]
  have hbD₁₁ : b ∈ D₁₁ := by simp [D₁₁, hbW, hab.symm]
  have hbD₁₂ : b ∈ D₁₂ := by simp [D₁₂, hbW, hab.symm]
  have hbp : b ≠ p := fun h => hpW (h ▸ hbW)
  have hbq : b ≠ q := fun h => hqW (h ▸ hbW)
  have hbD₂₁ : b ∉ D₂₁ := by simp [D₂₁, hbp]
  have hbD₂₂ : b ∉ D₂₂ := by simp [D₂₂, hbq]
  have hD₁₁D₁₂ : D₁₁ ≠ D₁₂ := by
    intro h
    exact hpD₁₂ (h ▸ Finset.mem_insert_self p (W.erase a))
  have hD₁₁D₂₁ : D₁₁ ≠ D₂₁ := by intro h; exact hbD₂₁ (h ▸ hbD₁₁)
  have hD₁₁D₂₂ : D₁₁ ≠ D₂₂ := by intro h; exact hbD₂₂ (h ▸ hbD₁₁)
  have hD₁₂D₂₁ : D₁₂ ≠ D₂₁ := by intro h; exact hbD₂₁ (h ▸ hbD₁₂)
  have hD₁₂D₂₂ : D₁₂ ≠ D₂₂ := by intro h; exact hbD₂₂ (h ▸ hbD₁₂)
  have hD₂₁D₂₂ : D₂₁ ≠ D₂₂ := by
    intro h
    exact hpD₂₂ (h ▸ Finset.mem_insert_self p (W.erase b))
  let S : Finset (Finset α) := {D₁₁, D₁₂, D₂₁, D₂₂}
  have hScard : S.card = 4 := by
    simp [S, hD₁₁D₁₂, hD₁₁D₂₁, hD₁₁D₂₂, hD₁₂D₂₁, hD₁₂D₂₂, hD₂₁D₂₂]
  have hSsub : S ⊆ singleDecrements W := by
    intro D hD
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hD
    rcases hD with rfl | rfl | rfl | rfl
    · exact hD₁₁
    · exact hD₁₂
    · exact hD₂₁
    · exact hD₂₂
  have hle := Finset.card_le_card hSsub
  omega

/-- A legal one-element replacement gives an edge in the exchange graph. -/
theorem exchangeGraph_adj_of_replacement {F : Finset (Finset α)} {X Y : Finset α}
    (hXF : X ∈ F) (hYF : Y ∈ F) {i j : α}
    (hj : j ∈ X) (hi : i ∉ X) (hij : i ≠ j)
    (hY : Y = insert i (X.erase j)) :
    (exchangeGraph F).Adj ⟨X, hXF⟩ ⟨Y, hYF⟩ := by
  have hdiff : X ∆ Y = {i, j} := by
    ext z
    simp only [Finset.mem_symmDiff, hY, Finset.mem_insert, Finset.mem_erase]
    aesop
  have hXY : X ≠ Y := by
    intro h
    exact hi (h ▸ hY ▸ Finset.mem_insert_self i (X.erase j))
  simp only [exchangeGraph, SimpleGraph.fromRel_adj]
  refine ⟨fun h => hXY (congrArg Subtype.val h), Or.inl ?_⟩
  rw [hdiff, Finset.card_pair hij]

/-- Two finsets whose directed differences are singletons differ by the corresponding replacement. -/
theorem eq_insert_erase_of_sdiff_eq_singletons {X B : Finset α} {a p : α}
    (hXB : X \ B = {a}) (hBX : B \ X = {p}) :
    X = insert a (B.erase p) := by
  ext z
  constructor
  · intro hzX
    by_cases hza : z = a
    · simp [hza]
    · have hzB : z ∈ B := by
        by_contra hzB
        have : z ∈ X \ B := Finset.mem_sdiff.mpr ⟨hzX, hzB⟩
        have : z = a := by simpa [hXB] using this
        exact hza this
      have hzp : z ≠ p := by
        intro hzp
        have hpBX : p ∈ B \ X := by simp [hBX]
        exact (Finset.mem_sdiff.mp hpBX).2 (hzp ▸ hzX)
      simp [hzB, hzp]
  · intro hz
    rcases Finset.mem_insert.mp hz with hza | hz
    · have haX : a ∈ X := (Finset.mem_sdiff.mp (by simp [hXB] : a ∈ X \ B)).1
      exact hza ▸ haX
    · have hzB : z ∈ B := Finset.mem_of_mem_erase hz
      by_contra hzX
      have : z ∈ B \ X := Finset.mem_sdiff.mpr ⟨hzB, hzX⟩
      have hzp : z = p := by simpa [hBX] using this
      exact (Finset.mem_erase.mp hz).1 hzp

/-- The Gale-bottom pair of a shifted family with at least two members is an exchange edge. -/
theorem exists_adjacent_gale_bottom_pair {F : Finset (Finset α)} {κ : ℕ}
    (hF : IsShifted F κ) (h2 : 2 ≤ F.card) :
    ∃ (m₁ m₂ : Finset α) (hm₁ : IsGaleLeast F m₁) (hm₂ : IsGaleSecondLeast F m₁ m₂),
      (exchangeGraph F).Adj ⟨m₁, hm₁.1⟩ ⟨m₂, hm₂.1⟩ := by
  obtain ⟨m₁, m₂, hm₁, hm₂, i, j, him₁, _him₂, _hjm₂, hjm₁, hij,
      hm₂repr, _himax, _hjmin⟩ := exists_gale_bottom_pair_with_boundary hF h2
  exact ⟨m₁, m₂, hm₁, hm₂,
    exchangeGraph_adj_of_replacement hm₁.1 hm₂.1 him₁ hjm₁ hij.ne' hm₂repr⟩

/-- **Lemma 1 (bottom of a shifted family)**, `STEP_LEMMA_2026-08-15.md` §1.

Stated index-free. The concrete coordinate identifications of `m₁` and `m₂` as `{g₁,…,g_κ}` and
`{g₁,…,g_{κ−1}, g_{κ+1}}` on the used ground are
`galeLeast_eq_initialSegment` and `galeSecondLeast_eq_secondInitialSegment`. -/
theorem lemma1_bottom {F : Finset (Finset α)} {κ : ℕ} (hF : IsShifted F κ) (h2 : 2 ≤ F.card) :
    ∃ m₁ m₂ : Finset α,
      IsGaleLeast F m₁ ∧ IsGaleSecondLeast F m₁ m₂ ∧
      -- (iii) a 2-element shifted family is exactly `{m₁, m₂}`, and they are adjacent
      (F.card = 2 → F = {m₁, m₂}) ∧
      -- (iv) a 3-element shifted family is a triangle: its exchange graph is complete
      (F.card = 3 → ∀ A B : ExchangeV F, A ≠ B → (exchangeGraph F).Adj A B) := by
  obtain ⟨m₁, m₂, hm₁, hm₂, i, j, him₁, him₂, hjm₂, hjm₁, hij,
      hm₂repr, himax, hjmin⟩ := exists_gale_bottom_pair_with_boundary hF h2
  refine ⟨m₁, m₂, hm₁, hm₂, ?_, ?_⟩
  · intro hcard2
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro X hX
      rcases Finset.mem_insert.mp hX with rfl | hX
      · exact hm₁.1
      · have : X = m₂ := by simpa using hX
        exact this ▸ hm₂.1
    · rw [hcard2, Finset.card_pair hm₂.2.1.symm]
  · intro hcard3
    rcases hF with ⟨_, hcard, hshift⟩
    have hres₁card : (F.erase m₁).card = 2 := by
      rw [Finset.card_erase_of_mem hm₁.1, hcard3]
    have hm₂res₁ : m₂ ∈ F.erase m₁ := Finset.mem_erase.mpr ⟨hm₂.2.1, hm₂.1⟩
    have hres₂card : ((F.erase m₁).erase m₂).card = 1 := by
      rw [Finset.card_erase_of_mem hm₂res₁, hres₁card]
    have hres₂ne : ((F.erase m₁).erase m₂).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨W, hWres₂⟩ := hres₂ne
    have hWres₁ : W ∈ F.erase m₁ := Finset.mem_of_mem_erase hWres₂
    have hWF : W ∈ F := Finset.mem_of_mem_erase hWres₁
    have hWm₁ : W ≠ m₁ := (Finset.mem_erase.mp hWres₁).1
    have hWm₂ : W ≠ m₂ := (Finset.mem_erase.mp hWres₂).1
    have hbelow : ∀ p ∈ m₁, ∀ a, a ∉ m₁ → p < a := by
      intro p hp a ha
      have hpj : p < j := (himax p hp).trans_lt hij
      have hja : j ≤ a := le_of_not_gt (fun haj => ha (hjmin a haj))
      exact hpj.trans_le hja
    have hWdiff_le : (W \ m₁).card ≤ 1 := by
      by_contra hnot
      have htwo : 2 ≤ (W \ m₁).card := by omega
      obtain ⟨D₁₁, D₁₂, D₂₁, D₂₂, hD₁₁F, hD₁₂F, hD₂₁F, _hD₂₂F,
          hD₁₁W, hD₁₂W, hD₂₁W, _hD₂₂W,
          hD₁₁D₁₂, hD₁₁D₂₁, _hD₁₁D₂₂,
          hD₁₂D₂₁, _hD₁₂D₂₂, _hD₂₁D₂₂⟩ :=
        four_distinct_decrements_of_two_outside
          ⟨⟨m₁, hm₁.1⟩, hcard, hshift⟩ hm₁.1 hWF hbelow htwo
      let S : Finset (Finset α) := {D₁₁, D₁₂, D₂₁}
      have hScard : S.card = 3 := by
        simp [S, hD₁₁D₁₂, hD₁₁D₂₁, hD₁₂D₂₁]
      have hSsub : S ⊆ F.erase W := by
        intro D hD
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hD
        rcases hD with rfl | rfl | rfl
        · exact Finset.mem_erase.mpr ⟨hD₁₁W, hD₁₁F⟩
        · exact Finset.mem_erase.mpr ⟨hD₁₂W, hD₁₂F⟩
        · exact Finset.mem_erase.mpr ⟨hD₂₁W, hD₂₁F⟩
      have hFWcard : (F.erase W).card = 2 := by
        rw [Finset.card_erase_of_mem hWF, hcard3]
      have := Finset.card_le_card hSsub
      omega
    have hWdiff_ne : (W \ m₁).Nonempty := Finset.sdiff_nonempty.mpr (by
      intro hsub
      exact hWm₁ (Finset.eq_of_subset_of_card_le hsub (by
        rw [hcard W hWF, hcard m₁ hm₁.1])))
    have hWdiff_card : (W \ m₁).card = 1 := by
      have := Finset.card_pos.mpr hWdiff_ne
      omega
    have hm₁diff_card : (m₁ \ W).card = 1 := by
      have h₁ := Finset.card_sdiff_add_card_inter m₁ W
      have h₂ := Finset.card_sdiff_add_card_inter W m₁
      rw [Finset.inter_comm W m₁] at h₂
      have hsame : m₁.card = W.card := (hcard m₁ hm₁.1).trans (hcard W hWF).symm
      omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hWdiff_card
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hm₁diff_card
    have haW : a ∈ W := (Finset.mem_sdiff.mp (by simp [ha] : a ∈ W \ m₁)).1
    have ham₁ : a ∉ m₁ := (Finset.mem_sdiff.mp (by simp [ha] : a ∈ W \ m₁)).2
    have hpm₁ : p ∈ m₁ := (Finset.mem_sdiff.mp (by simp [hp] : p ∈ m₁ \ W)).1
    have hpW : p ∉ W := (Finset.mem_sdiff.mp (by simp [hp] : p ∈ m₁ \ W)).2
    have hpa : p < a := hbelow p hpm₁ a ham₁
    have hWrepr : W = insert a (m₁.erase p) :=
      eq_insert_erase_of_sdiff_eq_singletons ha hp
    have hFeq : F = {m₁, m₂, W} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro X hX
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX
        rcases hX with rfl | rfl | rfl
        · exact hm₁.1
        · exact hm₂.1
        · exact hWF
      · rw [hcard3]
        simp [hm₂.2.1.symm, hWm₁.symm, hWm₂.symm]
    have hm₁m₂adj :
        (exchangeGraph F).Adj (⟨m₁, hm₁.1⟩ : ExchangeV F) ⟨m₂, hm₂.1⟩ :=
      exchangeGraph_adj_of_replacement hm₁.1 hm₂.1 him₁ hjm₁ hij.ne' hm₂repr
    have hm₁Wadj :
        (exchangeGraph F).Adj (⟨m₁, hm₁.1⟩ : ExchangeV F) ⟨W, hWF⟩ :=
      exchangeGraph_adj_of_replacement hm₁.1 hWF hpm₁ ham₁ hpa.ne' hWrepr
    have hWm₂adj :
        (exchangeGraph F).Adj (⟨W, hWF⟩ : ExchangeV F) ⟨m₂, hm₂.1⟩ := by
      have hja : j ≤ a := le_of_not_gt (fun haj => ham₁ (hjmin a haj))
      by_cases haj : a = j
      · have hpi : p ≠ i := by
          intro hpi
          apply hWm₂
          calc
            W = insert a (m₁.erase p) := hWrepr
            _ = insert j (m₁.erase i) := by rw [haj, hpi]
            _ = m₂ := hm₂repr.symm
        have hpi_lt : p < i := lt_of_le_of_ne (himax p hpm₁) hpi
        have hiW : i ∈ W := by
          rw [hWrepr]
          simp [him₁, hpi.symm]
        let D := insert p (W.erase i)
        have hDF : D ∈ F := hshift W hWF p i hiW hpi_lt hpW
        have hDW : D ≠ W := by
          intro h
          exact hpW (h ▸ Finset.mem_insert_self p (W.erase i))
        have hai : a ≠ i := haj.trans_ne hij.ne'
        have haD : a ∈ D := by simp [D, haW, hai]
        have hDm₁ : D ≠ m₁ := fun h => ham₁ (h ▸ haD)
        have hDm₂ : D = m₂ := by
          have : D = m₁ ∨ D = m₂ ∨ D = W := by simpa [hFeq] using hDF
          rcases this with h | h | h
          · exact absurd h hDm₁
          · exact h
          · exact absurd h hDW
        exact exchangeGraph_adj_of_replacement hWF hm₂.1 hiW hpW hpi
          (hDm₂.symm.trans rfl)
      · have hja_lt : j < a := lt_of_le_of_ne hja (Ne.symm haj)
        have hjW : j ∉ W := by
          rw [hWrepr]
          simp [hjm₁, Ne.symm haj]
        let D := insert j (W.erase a)
        have hDF : D ∈ F := hshift W hWF j a haW hja_lt hjW
        have hDW : D ≠ W := by
          intro h
          exact hjW (h ▸ Finset.mem_insert_self j (W.erase a))
        have hjD : j ∈ D := Finset.mem_insert_self j (W.erase a)
        have hDm₁ : D ≠ m₁ := fun h => hjm₁ (h ▸ hjD)
        have hDm₂ : D = m₂ := by
          have : D = m₁ ∨ D = m₂ ∨ D = W := by simpa [hFeq] using hDF
          rcases this with h | h | h
          · exact absurd h hDm₁
          · exact h
          · exact absurd h hDW
        exact exchangeGraph_adj_of_replacement hWF hm₂.1 haW hjW hja_lt.ne
          (hDm₂.symm.trans rfl)
    intro A B hAB
    have hAval : A.val = m₁ ∨ A.val = m₂ ∨ A.val = W := by
      simpa [hFeq] using A.prop
    have hBval : B.val = m₁ ∨ B.val = m₂ ∨ B.val = W := by
      simpa [hFeq] using B.prop
    rcases hAval with hA | hA | hA <;> rcases hBval with hB | hB | hB
    · exfalso
      apply hAB
      exact Subtype.ext (hA.trans hB.symm)
    · have hAe : A = ⟨m₁, hm₁.1⟩ := Subtype.ext hA
      have hBe : B = ⟨m₂, hm₂.1⟩ := Subtype.ext hB
      rw [hAe, hBe]
      exact hm₁m₂adj
    · have hAe : A = ⟨m₁, hm₁.1⟩ := Subtype.ext hA
      have hBe : B = ⟨W, hWF⟩ := Subtype.ext hB
      rw [hAe, hBe]
      exact hm₁Wadj
    · have hAe : A = ⟨m₂, hm₂.1⟩ := Subtype.ext hA
      have hBe : B = ⟨m₁, hm₁.1⟩ := Subtype.ext hB
      rw [hAe, hBe]
      exact hm₁m₂adj.symm
    · exfalso
      apply hAB
      exact Subtype.ext (hA.trans hB.symm)
    · have hAe : A = ⟨m₂, hm₂.1⟩ := Subtype.ext hA
      have hBe : B = ⟨W, hWF⟩ := Subtype.ext hB
      rw [hAe, hBe]
      exact hWm₂adj.symm
    · have hAe : A = ⟨W, hWF⟩ := Subtype.ext hA
      have hBe : B = ⟨m₁, hm₁.1⟩ := Subtype.ext hB
      rw [hAe, hBe]
      exact hm₁Wadj.symm
    · have hAe : A = ⟨W, hWF⟩ := Subtype.ext hA
      have hBe : B = ⟨m₂, hm₂.1⟩ := Subtype.ext hB
      rw [hAe, hBe]
      exact hWm₂adj
    · exfalso
      apply hAB
      exact Subtype.ext (hA.trans hB.symm)

/-- Every shifted family with at least three members contains a triangle in its exchange graph;
consequently that graph is not bipartite. -/
theorem exchangeGraph_not_bipartite_of_three_le
    {F : Finset (Finset α)} {κ : ℕ} (hF : IsShifted F κ) (h3 : 3 ≤ F.card) :
    (∃ A B C : ExchangeV F,
      A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
      (exchangeGraph F).Adj A B ∧ (exchangeGraph F).Adj A C ∧
      (exchangeGraph F).Adj B C) ∧
    ¬(exchangeGraph F).IsBipartite := by
  obtain ⟨m₁, m₂, hm₁, hm₂, i, j, him₁, him₂, hjm₂, hjm₁, hij,
      hm₂repr, himax, hjmin⟩ :=
    exists_gale_bottom_pair_with_boundary hF (by omega)
  rcases hF with ⟨_hFne, hcard, hshift⟩
  have hres₁card : (F.erase m₁).card = F.card - 1 :=
    Finset.card_erase_of_mem hm₁.1
  have hm₂res₁ : m₂ ∈ F.erase m₁ := Finset.mem_erase.mpr ⟨hm₂.2.1, hm₂.1⟩
  have hres₂card : ((F.erase m₁).erase m₂).card = F.card - 2 := by
    rw [Finset.card_erase_of_mem hm₂res₁, hres₁card]
    omega
  have hres₂ne : ((F.erase m₁).erase m₂).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨W, hWres, hWmin⟩ :=
    Finset.exists_min_image ((F.erase m₁).erase m₂) (fun X => toColex X) hres₂ne
  have hWres₁ : W ∈ F.erase m₁ := Finset.mem_of_mem_erase hWres
  have hWF : W ∈ F := Finset.mem_of_mem_erase hWres₁
  have hWm₁ : W ≠ m₁ := (Finset.mem_erase.mp hWres₁).1
  have hWm₂ : W ≠ m₂ := (Finset.mem_erase.mp hWres).1
  have hWgaleMin : ∀ D ∈ (F.erase m₁).erase m₂, GaleLE D W → D = W := by
    intro D hD hDW
    apply toColex.injective
    exact le_antisymm (toColex_le_of_galeLE hDW) (hWmin D hD)
  have hdec : ∀ r s : α, s ∈ W → r < s → r ∉ W →
      insert r (W.erase s) = m₁ ∨ insert r (W.erase s) = m₂ := by
    intro r s hsW hrs hrW
    let D := insert r (W.erase s)
    have hDF : D ∈ F := hshift W hWF r s hsW hrs hrW
    have hDW : D ≠ W := by
      intro h
      exact hrW (h ▸ Finset.mem_insert_self r (W.erase s))
    by_cases hDm₁ : D = m₁
    · exact Or.inl hDm₁
    by_cases hDm₂ : D = m₂
    · exact Or.inr hDm₂
    exfalso
    have hDres : D ∈ (F.erase m₁).erase m₂ := by
      exact Finset.mem_erase.mpr ⟨hDm₂, Finset.mem_erase.mpr ⟨hDm₁, hDF⟩⟩
    exact hDW (hWgaleMin D hDres (galeLE_singleDecrement hsW hrs hrW))
  have hbelow : ∀ p ∈ m₁, ∀ a, a ∉ m₁ → p < a := by
    intro p hp a ha
    have hpj : p < j := (himax p hp).trans_lt hij
    have hja : j ≤ a := le_of_not_gt (fun haj => ha (hjmin a haj))
    exact hpj.trans_le hja
  have hWdiff_le : (W \ m₁).card ≤ 1 := by
    by_contra hnot
    have htwo : 2 ≤ (W \ m₁).card := by omega
    have hdiffcard : (m₁ \ W).card = (W \ m₁).card := by
      have h₁ := Finset.card_sdiff_add_card_inter m₁ W
      have h₂ := Finset.card_sdiff_add_card_inter W m₁
      rw [Finset.inter_comm W m₁] at h₂
      have hsame : m₁.card = W.card := (hcard m₁ hm₁.1).trans (hcard W hWF).symm
      omega
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Finset.one_lt_card.mp (show 1 < (W \ m₁).card by omega)
    obtain ⟨p, hp, q, hq, hpq⟩ :=
      Finset.one_lt_card.mp (show 1 < (m₁ \ W).card by omega)
    have haW : a ∈ W := (Finset.mem_sdiff.mp ha).1
    have ham₁ : a ∉ m₁ := (Finset.mem_sdiff.mp ha).2
    have hbW : b ∈ W := (Finset.mem_sdiff.mp hb).1
    have hbm₁ : b ∉ m₁ := (Finset.mem_sdiff.mp hb).2
    have hpm₁ : p ∈ m₁ := (Finset.mem_sdiff.mp hp).1
    have hpW : p ∉ W := (Finset.mem_sdiff.mp hp).2
    have hqm₁ : q ∈ m₁ := (Finset.mem_sdiff.mp hq).1
    have hqW : q ∉ W := (Finset.mem_sdiff.mp hq).2
    have hpa : p < a := hbelow p hpm₁ a ham₁
    have hqa : q < a := hbelow q hqm₁ a ham₁
    have hpb : p < b := hbelow p hpm₁ b hbm₁
    let D₁₁ := insert p (W.erase a)
    let D₁₂ := insert q (W.erase a)
    let D₂₁ := insert p (W.erase b)
    have hD₁₁ : D₁₁ = m₁ ∨ D₁₁ = m₂ := hdec p a haW hpa hpW
    have hD₁₂ : D₁₂ = m₁ ∨ D₁₂ = m₂ := hdec q a haW hqa hqW
    have hD₂₁ : D₂₁ = m₁ ∨ D₂₁ = m₂ := hdec p b hbW hpb hpW
    have hpD₁₂ : p ∉ D₁₂ := by simp [D₁₂, hpW, hpq]
    have hbD₁₁ : b ∈ D₁₁ := by simp [D₁₁, hbW, hab.symm]
    have hbD₁₂ : b ∈ D₁₂ := by simp [D₁₂, hbW, hab.symm]
    have hbp : b ≠ p := fun h => hpW (h ▸ hbW)
    have hbD₂₁ : b ∉ D₂₁ := by simp [D₂₁, hbp]
    have hD₁₁D₁₂ : D₁₁ ≠ D₁₂ := by
      intro h
      exact hpD₁₂ (h ▸ Finset.mem_insert_self p (W.erase a))
    have hD₁₁D₂₁ : D₁₁ ≠ D₂₁ := by intro h; exact hbD₂₁ (h ▸ hbD₁₁)
    have hD₁₂D₂₁ : D₁₂ ≠ D₂₁ := by intro h; exact hbD₂₁ (h ▸ hbD₁₂)
    let S : Finset (Finset α) := {D₁₁, D₁₂, D₂₁}
    have hScard : S.card = 3 := by
      simp [S, hD₁₁D₁₂, hD₁₁D₂₁, hD₁₂D₂₁]
    have hSsub : S ⊆ {m₁, m₂} := by
      intro D hD
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hD ⊢
      rcases hD with rfl | rfl | rfl
      · exact hD₁₁
      · exact hD₁₂
      · exact hD₂₁
    have hcardS := Finset.card_le_card hSsub
    rw [hScard, Finset.card_pair hm₂.2.1.symm] at hcardS
    omega
  have hWdiff_ne : (W \ m₁).Nonempty := Finset.sdiff_nonempty.mpr (by
    intro hsub
    exact hWm₁ (Finset.eq_of_subset_of_card_le hsub (by
      rw [hcard W hWF, hcard m₁ hm₁.1])))
  have hWdiff_card : (W \ m₁).card = 1 := by
    have := Finset.card_pos.mpr hWdiff_ne
    omega
  have hm₁diff_card : (m₁ \ W).card = 1 := by
    have h₁ := Finset.card_sdiff_add_card_inter m₁ W
    have h₂ := Finset.card_sdiff_add_card_inter W m₁
    rw [Finset.inter_comm W m₁] at h₂
    have hsame : m₁.card = W.card := (hcard m₁ hm₁.1).trans (hcard W hWF).symm
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hWdiff_card
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hm₁diff_card
  have haW : a ∈ W := (Finset.mem_sdiff.mp (by simp [ha] : a ∈ W \ m₁)).1
  have ham₁ : a ∉ m₁ := (Finset.mem_sdiff.mp (by simp [ha] : a ∈ W \ m₁)).2
  have hpm₁ : p ∈ m₁ := (Finset.mem_sdiff.mp (by simp [hp] : p ∈ m₁ \ W)).1
  have hpW : p ∉ W := (Finset.mem_sdiff.mp (by simp [hp] : p ∈ m₁ \ W)).2
  have hpa : p < a := hbelow p hpm₁ a ham₁
  have hWrepr : W = insert a (m₁.erase p) :=
    eq_insert_erase_of_sdiff_eq_singletons ha hp
  let M₁ : ExchangeV F := ⟨m₁, hm₁.1⟩
  let M₂ : ExchangeV F := ⟨m₂, hm₂.1⟩
  let WV : ExchangeV F := ⟨W, hWF⟩
  have hM₁M₂ : (exchangeGraph F).Adj M₁ M₂ :=
    exchangeGraph_adj_of_replacement hm₁.1 hm₂.1 him₁ hjm₁ hij.ne' hm₂repr
  have hM₁W : (exchangeGraph F).Adj M₁ WV :=
    exchangeGraph_adj_of_replacement hm₁.1 hWF hpm₁ ham₁ hpa.ne' hWrepr
  have hWM₂ : (exchangeGraph F).Adj WV M₂ := by
    have hja : j ≤ a := le_of_not_gt (fun haj => ham₁ (hjmin a haj))
    by_cases haj : a = j
    · have hpi : p ≠ i := by
        intro hpi
        apply hWm₂
        calc
          W = insert a (m₁.erase p) := hWrepr
          _ = insert j (m₁.erase i) := by rw [haj, hpi]
          _ = m₂ := hm₂repr.symm
      have hpi_lt : p < i := lt_of_le_of_ne (himax p hpm₁) hpi
      have hiW : i ∈ W := by rw [hWrepr]; simp [him₁, hpi.symm]
      let D := insert p (W.erase i)
      have hDm₁or₂ : D = m₁ ∨ D = m₂ := hdec p i hiW hpi_lt hpW
      have hai : a ≠ i := haj.trans_ne hij.ne'
      have haD : a ∈ D := by simp [D, haW, hai]
      have hDm₁ : D ≠ m₁ := fun h => ham₁ (h ▸ haD)
      have hDm₂ : D = m₂ := hDm₁or₂.resolve_left hDm₁
      exact exchangeGraph_adj_of_replacement hWF hm₂.1 hiW hpW hpi
        (hDm₂.symm.trans rfl)
    · have hja_lt : j < a := lt_of_le_of_ne hja (Ne.symm haj)
      have hjW : j ∉ W := by rw [hWrepr]; simp [hjm₁, Ne.symm haj]
      let D := insert j (W.erase a)
      have hDm₁or₂ : D = m₁ ∨ D = m₂ := hdec j a haW hja_lt hjW
      have hjD : j ∈ D := Finset.mem_insert_self j (W.erase a)
      have hDm₁ : D ≠ m₁ := fun h => hjm₁ (h ▸ hjD)
      have hDm₂ : D = m₂ := hDm₁or₂.resolve_left hDm₁
      exact exchangeGraph_adj_of_replacement hWF hm₂.1 haW hjW hja_lt.ne
        (hDm₂.symm.trans rfl)
  have hM₁M₂ne : M₁ ≠ M₂ := by
    intro h
    exact hm₂.2.1 (congrArg Subtype.val h).symm
  have hM₁Wne : M₁ ≠ WV := by
    intro h
    exact hWm₁ (congrArg Subtype.val h).symm
  have hM₂Wne : M₂ ≠ WV := by
    intro h
    exact hWm₂ (congrArg Subtype.val h).symm
  refine ⟨⟨M₁, M₂, WV, hM₁M₂ne, hM₁Wne, hM₂Wne, hM₁M₂, hM₁W, hWM₂.symm⟩, ?_⟩
  intro hbip
  obtain ⟨C⟩ := hbip
  have hc₁₂ : C M₁ ≠ C M₂ := C.valid hM₁M₂
  have hc₁W : C M₁ ≠ C WV := C.valid hM₁W
  have hc₂W : C M₂ ≠ C WV := C.valid hWM₂.symm
  let S : Finset (Fin 2) := {C M₁, C M₂, C WV}
  have hScard : S.card = 3 := by simp [S, hc₁₂, hc₁W, hc₂W]
  have hle := Finset.card_le_card (Finset.subset_univ S)
  rw [hScard, Finset.card_univ] at hle
  norm_num at hle

/-! ## 4. Clique-sums, and Lemma 2 -/

/-- `u` is adjacent to every other vertex of a graph. -/
def _root_.SimpleGraph.IsUniversalVertex {W : Type*} (G : SimpleGraph W) (u : W) : Prop :=
  ∀ w : W, w ≠ u → G.Adj u w

/-- **Clique-sum, at the level of an arbitrary graph**: `G ≅ K₂ ∨ (K_p ⊔ K_q)` with `p, q ≥ 1`.

Stated generically because two different lanes need it on two different vertex types — here on
`J(F)`, and in `SBPlusOrd.lean` on the neighborhood quotient of a realization graph. Written without
constructing the join: two universal vertices `u, v`, and outside `{u,v}` adjacency is exactly "same
side" for a two-valued `side`, with both sides nonempty. -/
def _root_.SimpleGraph.IsCliqueSum {W : Type*} (G : SimpleGraph W) (u v : W) : Prop :=
  u ≠ v ∧ G.IsUniversalVertex u ∧ G.IsUniversalVertex v ∧
    ∃ side : W → Bool,
      (∃ a : W, a ≠ u ∧ a ≠ v ∧ side a = true) ∧
      (∃ b : W, b ≠ u ∧ b ≠ v ∧ side b = false) ∧
      (∀ a b : W, a ≠ u → a ≠ v → b ≠ u → b ≠ v → a ≠ b →
        (G.Adj a b ↔ side a = side b))

/-- `u` is adjacent to every other vertex of `J(F)`. -/
def IsUniversalVertex (F : Finset (Finset α)) (u : ExchangeV F) : Prop :=
  (exchangeGraph F).IsUniversalVertex u

/-- **Clique-sum**: `J(F) ≅ K₂ ∨ (K_p ⊔ K_q)` with `p, q ≥ 1`.

Written without constructing the join: two universal vertices `u, v`, and outside `{u,v}` the graph
is exactly two nonempty cliques with no edges between them — i.e. adjacency outside `{u,v}` is
"same side" for a two-valued `side`. -/
def IsCliqueSum (F : Finset (Finset α)) (u v : ExchangeV F) : Prop :=
  (exchangeGraph F).IsCliqueSum u v

/-- For equicardinal finsets, exchange adjacency is equivalent to one directed difference having
cardinality one. -/
theorem card_symmDiff_eq_two_iff {A B : Finset α} (hcard : A.card = B.card) :
    (A ∆ B).card = 2 ↔ (A \ B).card = 1 := by
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint]
  · have hdiff : (B \ A).card = (A \ B).card := by
      exact Finset.card_sdiff_comm hcard.symm
    rw [hdiff]
    omega
  · rw [Finset.disjoint_left]
    intro a ha ha'
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp ha').1

/-- Equicardinal nonadjacent exchange vertices differ in at least two elements in each direction. -/
theorem two_le_sdiff_of_not_adj_of_card_eq {F : Finset (Finset α)}
    {A B : ExchangeV F} (hcard : A.val.card = B.val.card)
    (hne : A ≠ B) (hnadj : ¬(exchangeGraph F).Adj A B) :
    2 ≤ (A.val \ B.val).card := by
  have hdiffne : (A.val \ B.val).Nonempty := Finset.sdiff_nonempty.mpr (by
    intro hsub
    apply hne
    apply Subtype.ext
    exact Finset.eq_of_subset_of_card_le hsub hcard.ge)
  have hnotone : (A.val \ B.val).card ≠ 1 := by
    intro hone
    apply hnadj
    simp only [exchangeGraph, SimpleGraph.fromRel_adj]
    exact ⟨hne, Or.inl ((card_symmDiff_eq_two_iff hcard).2 hone)⟩
  have hpos := Finset.card_pos.mpr hdiffne
  omega

/-- The two-exchange identity used in the boundary case of the decrement census. -/
theorem insert_erase_insert_erase {S : Finset α} {p i j : α}
    (hp : p ∈ S) (hi : i ∈ S) (hj : j ∉ S) (hpi : p ≠ i) :
    insert p ((insert j (S.erase p)).erase i) = insert j (S.erase i) := by
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  ext z
  simp only [Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro (rfl | ⟨hzi, rfl | ⟨hzp, hzS⟩⟩)
    · exact Or.inr ⟨hpi, hp⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hzi, hzS⟩
  · rintro (rfl | ⟨hzi, hzS⟩)
    · exact Or.inr ⟨Ne.symm hij, Or.inl rfl⟩
    · by_cases hzp : z = p
      · exact Or.inl hzp
      · exact Or.inr ⟨hzi, Or.inr ⟨hzp, hzS⟩⟩

/-- If every legal decrement of `W` is one of two targets, then `W` has at most one element
outside the lower-closed bottom member. The proof constructs four distinct decrements. -/
theorem two_outside_impossible_of_all_decrements_in_pair
    {F : Finset (Finset α)} {κ : ℕ} (hF : IsShifted F κ)
    {m₁ W t₁ t₂ : Finset α} (hm₁F : m₁ ∈ F) (hWF : W ∈ F)
    (hbelow : ∀ p ∈ m₁, ∀ a, a ∉ m₁ → p < a)
    (htarget : ∀ r s : α, s ∈ W → r < s → r ∉ W →
      insert r (W.erase s) = t₁ ∨ insert r (W.erase s) = t₂) :
    (W \ m₁).card ≤ 1 := by
  rcases hF with ⟨_, hcard, _⟩
  by_contra hnot
  have htwo : 2 ≤ (W \ m₁).card := by omega
  have hdiffcard : (m₁ \ W).card = (W \ m₁).card :=
    Finset.card_sdiff_comm ((hcard m₁ hm₁F).trans (hcard W hWF).symm)
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.mp (show 1 < (W \ m₁).card by omega)
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    Finset.one_lt_card.mp (show 1 < (m₁ \ W).card by omega)
  have haW : a ∈ W := (Finset.mem_sdiff.mp ha).1
  have ham₁ : a ∉ m₁ := (Finset.mem_sdiff.mp ha).2
  have hbW : b ∈ W := (Finset.mem_sdiff.mp hb).1
  have hbm₁ : b ∉ m₁ := (Finset.mem_sdiff.mp hb).2
  have hpm₁ : p ∈ m₁ := (Finset.mem_sdiff.mp hp).1
  have hpW : p ∉ W := (Finset.mem_sdiff.mp hp).2
  have hqm₁ : q ∈ m₁ := (Finset.mem_sdiff.mp hq).1
  have hqW : q ∉ W := (Finset.mem_sdiff.mp hq).2
  have hpa : p < a := hbelow p hpm₁ a ham₁
  have hqa : q < a := hbelow q hqm₁ a ham₁
  have hpb : p < b := hbelow p hpm₁ b hbm₁
  have hqb : q < b := hbelow q hqm₁ b hbm₁
  let D₁₁ := insert p (W.erase a)
  let D₁₂ := insert q (W.erase a)
  let D₂₁ := insert p (W.erase b)
  let D₂₂ := insert q (W.erase b)
  have hD₁₁ : D₁₁ = t₁ ∨ D₁₁ = t₂ := htarget p a haW hpa hpW
  have hD₁₂ : D₁₂ = t₁ ∨ D₁₂ = t₂ := htarget q a haW hqa hqW
  have hD₂₁ : D₂₁ = t₁ ∨ D₂₁ = t₂ := htarget p b hbW hpb hpW
  have hD₂₂ : D₂₂ = t₁ ∨ D₂₂ = t₂ := htarget q b hbW hqb hqW
  have hpD₁₂ : p ∉ D₁₂ := by simp [D₁₂, hpW, hpq]
  have hpD₂₂ : p ∉ D₂₂ := by simp [D₂₂, hpW, hpq]
  have hbD₁₁ : b ∈ D₁₁ := by simp [D₁₁, hbW, hab.symm]
  have hbD₁₂ : b ∈ D₁₂ := by simp [D₁₂, hbW, hab.symm]
  have hbp : b ≠ p := fun h => hpW (h ▸ hbW)
  have hbq : b ≠ q := fun h => hqW (h ▸ hbW)
  have hbD₂₁ : b ∉ D₂₁ := by simp [D₂₁, hbp]
  have hbD₂₂ : b ∉ D₂₂ := by simp [D₂₂, hbq]
  have hD₁₁D₁₂ : D₁₁ ≠ D₁₂ := by
    intro h
    exact hpD₁₂ (h ▸ Finset.mem_insert_self p (W.erase a))
  have hD₁₁D₂₁ : D₁₁ ≠ D₂₁ := by intro h; exact hbD₂₁ (h ▸ hbD₁₁)
  have hD₁₁D₂₂ : D₁₁ ≠ D₂₂ := by intro h; exact hbD₂₂ (h ▸ hbD₁₁)
  have hD₁₂D₂₁ : D₁₂ ≠ D₂₁ := by intro h; exact hbD₂₁ (h ▸ hbD₁₂)
  have hD₁₂D₂₂ : D₁₂ ≠ D₂₂ := by intro h; exact hbD₂₂ (h ▸ hbD₁₂)
  have hD₂₁D₂₂ : D₂₁ ≠ D₂₂ := by
    intro h
    exact hpD₂₂ (h ▸ Finset.mem_insert_self p (W.erase b))
  let S : Finset (Finset α) := {D₁₁, D₁₂, D₂₁, D₂₂}
  have hScard : S.card = 4 := by
    simp [S, hD₁₁D₁₂, hD₁₁D₂₁, hD₁₁D₂₂, hD₁₂D₂₁, hD₁₂D₂₂, hD₂₁D₂₂]
  have hSsub : S ⊆ {t₁, t₂} := by
    intro D hD
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hD ⊢
    rcases hD with rfl | rfl | rfl | rfl
    · exact hD₁₁
    · exact hD₁₂
    · exact hD₂₁
    · exact hD₂₂
  have hle := Finset.card_le_card hSsub
  have hpairle : ({t₁, t₂} : Finset (Finset α)).card ≤ 2 := by
    by_cases h : t₁ = t₂ <;> simp [h]
  omega

/-- A decrement of a side-minimal non-universal vertex must be universal: it is adjacent to its
source, so the side relation keeps it in the same clique unless it is universal, while minimality
excludes a proper decrement in that clique. -/
theorem decrement_mem_universal_of_side_minimal
    {F : Finset (Finset α)} {κ : ℕ} (hF : IsShifted F κ)
    {u v W : ExchangeV F} {side : ExchangeV F → Bool} {c : Bool}
    (hWu : W ≠ u) (hWv : W ≠ v) (hWside : side W = c)
    (hside : ∀ a b : ExchangeV F, a ≠ u → a ≠ v → b ≠ u → b ≠ v → a ≠ b →
      ((exchangeGraph F).Adj a b ↔ side a = side b))
    (hmin : ∀ Z : ExchangeV F, Z ≠ u → Z ≠ v → side Z = c →
      toColex W.val ≤ toColex Z.val) :
    ∀ r s : α, s ∈ W.val → r < s → r ∉ W.val →
      insert r (W.val.erase s) = u.val ∨ insert r (W.val.erase s) = v.val := by
  rcases hF with ⟨_, _, hshift⟩
  intro r s hsW hrs hrW
  let D := insert r (W.val.erase s)
  have hDF : D ∈ F := hshift W.val W.prop r s hsW hrs hrW
  let DV : ExchangeV F := ⟨D, hDF⟩
  by_cases hDu : D = u.val
  · exact Or.inl hDu
  by_cases hDv : D = v.val
  · exact Or.inr hDv
  exfalso
  have hDW : D ≠ W.val := by
    intro h
    exact hrW (h ▸ Finset.mem_insert_self r (W.val.erase s))
  have hW_DV : W ≠ DV := by
    intro h
    exact hDW (congrArg Subtype.val h).symm
  have hD_u : DV ≠ u := by
    intro h
    exact hDu (congrArg Subtype.val h)
  have hD_v : DV ≠ v := by
    intro h
    exact hDv (congrArg Subtype.val h)
  have hAdj : (exchangeGraph F).Adj W DV :=
    exchangeGraph_adj_of_replacement W.prop hDF hsW hrW hrs.ne (by rfl)
  have hDside : side DV = c :=
    (hside W DV hWu hWv hD_u hD_v hW_DV).1 hAdj |>.symm.trans hWside
  have hlt : toColex D < toColex W.val := toColex_singleDecrement_lt hsW hrs hrW
  exact (not_lt_of_ge (hmin DV hD_u hD_v hDside)) hlt

/-- **Lemma 2**, `STEP_LEMMA_2026-08-15.md` §2: the universal pair of a shifted clique-sum is its
Gale-least pair. This supersedes the earlier *measured* 153/153 normal form.

**CORRECTED 2026-08-16.** The first version of this statement concluded
`IsGaleLeast F u.val ∧ IsGaleSecondLeast F u.val v.val`, naming `u` as the Gale-least member. That is
**false**: `IsCliqueSum F u v` is symmetric in `u` and `v`, so nothing distinguishes them, and the
yFamily `{01,02,03,12}` with `u = 02`, `v = 01` is a kernel-checked counterexample. The conclusion is
about the unordered **pair**, and now says so. Found by a Lean wave that was instructed to stop and
report rather than weaken a statement it could not prove — which is the whole point of that
instruction, since the natural "repair" here would have been to add a hypothesis ordering `u` and `v`
and quietly prove something weaker than the paper claims. -/
theorem lemma2_universalPair_is_galeLeast {F : Finset (Finset α)} {κ : ℕ}
    (hF : IsShifted F κ) {u v : ExchangeV F} (h : IsCliqueSum F u v) :
    (IsGaleLeast F u.val ∧ IsGaleSecondLeast F u.val v.val) ∨
      (IsGaleLeast F v.val ∧ IsGaleSecondLeast F v.val u.val) := by
  rcases h with ⟨huv, huUniv, hvUniv, side, htrue, hfalse, hside⟩
  have huvval : u.val ≠ v.val := fun h => huv (Subtype.ext h)
  have hpairsub : {u.val, v.val} ⊆ F := by
    intro X hX
    rcases Finset.mem_insert.mp hX with hX | hX
    · exact hX ▸ u.prop
    · have hX' : X = v.val := by simpa using hX
      exact hX' ▸ v.prop
  have hpaircard := Finset.card_le_card hpairsub
  have h2 : 2 ≤ F.card := by simpa [Finset.card_pair huvval] using hpaircard
  obtain ⟨m₁, m₂, hm₁, hm₂, i, j, him₁, him₂, hjm₂, hjm₁, hij,
      hm₂repr, himax, hjmin⟩ := exists_gale_bottom_pair_with_boundary hF h2
  let M₁ : ExchangeV F := ⟨m₁, hm₁.1⟩
  let M₂ : ExchangeV F := ⟨m₂, hm₂.1⟩
  rcases hF with ⟨hFne, hcard, hshift⟩
  have hbelow : ∀ p ∈ m₁, ∀ a, a ∉ m₁ → p < a := by
    intro p hp a ha
    have hpj : p < j := (himax p hp).trans_lt hij
    have hja : j ≤ a := le_of_not_gt (fun haj => ha (hjmin a haj))
    exact hpj.trans_le hja
  have chooseMinOpposite : ∀ Z : ExchangeV F, Z ≠ u → Z ≠ v →
      ∃ W : ExchangeV F,
        W ≠ u ∧ W ≠ v ∧ side W ≠ side Z ∧
        ∀ T : ExchangeV F, T ≠ u → T ≠ v → side T = side W →
          toColex W.val ≤ toColex T.val := by
    intro Z hZu hZv
    rcases htrue with ⟨T, hTu, hTv, hTside⟩
    rcases hfalse with ⟨R, hRu, hRv, hRside⟩
    have chooseAt (c : Bool) (hcZ : c ≠ side Z)
        (A : ExchangeV F) (hAu : A ≠ u) (hAv : A ≠ v) (hAside : side A = c) :
        ∃ W : ExchangeV F,
          W ≠ u ∧ W ≠ v ∧ side W ≠ side Z ∧
          ∀ T : ExchangeV F, T ≠ u → T ≠ v → side T = side W →
            toColex W.val ≤ toColex T.val := by
      let C : Finset (ExchangeV F) :=
        Finset.univ.filter fun X => X ≠ u ∧ X ≠ v ∧ side X = c
      have hCne : C.Nonempty := by
        refine ⟨A, ?_⟩
        simp [C, hAu, hAv, hAside]
      obtain ⟨W, hWC, hWmin⟩ :=
        Finset.exists_min_image C (fun X => toColex X.val) hCne
      have hWdata : W ≠ u ∧ W ≠ v ∧ side W = c := by simpa [C] using hWC
      refine ⟨W, hWdata.1, hWdata.2.1, ?_, ?_⟩
      · exact fun h => hcZ (hWdata.2.2.symm.trans h)
      · intro X hXu hXv hXside
        apply hWmin X
        simp [C, hXu, hXv, hXside.trans hWdata.2.2]
    cases hZ : side Z with
    | false =>
        simpa [hZ] using chooseAt true (by simp [hZ]) T hTu hTv hTside
    | true =>
        simpa [hZ] using chooseAt false (by simp [hZ]) R hRu hRv hRside
  -- Step 1: the Gale-least member belongs to the universal pair.
  have hm₁pair : M₁ = u ∨ M₁ = v := by
    by_contra hnot
    rw [not_or] at hnot
    obtain ⟨W, hWu, hWv, hWside, hWmin⟩ := chooseMinOpposite M₁ hnot.1 hnot.2
    have hWM₁ : W ≠ M₁ := fun h => hWside (congrArg side h)
    have hnotadj : ¬(exchangeGraph F).Adj W M₁ := by
      intro hAdj
      have hs := (hside W M₁ hWu hWv hnot.1 hnot.2 hWM₁).1 hAdj
      exact hWside hs
    have htwoOutside : 2 ≤ (W.val \ m₁).card :=
      two_le_sdiff_of_not_adj_of_card_eq
        ((hcard W.val W.prop).trans (hcard m₁ hm₁.1).symm) hWM₁ hnotadj
    have htarget : ∀ r s : α, s ∈ W.val → r < s → r ∉ W.val →
        insert r (W.val.erase s) = u.val ∨ insert r (W.val.erase s) = v.val :=
      decrement_mem_universal_of_side_minimal
        ⟨hFne, hcard, hshift⟩ hWu hWv rfl hside
        (fun T hTu hTv hTside => hWmin T hTu hTv hTside)
    have hle := two_outside_impossible_of_all_decrements_in_pair
      ⟨hFne, hcard, hshift⟩ hm₁.1 W.prop hbelow htarget
    omega
  -- Step 2: after orienting the first universal vertex as `m₁`, the other one is `m₂`.
  have hM₂M₁ : M₂ ≠ M₁ := by
    intro hEq
    exact hm₂.2.1 (congrArg Subtype.val hEq)
  have step2 (a b : ExchangeV F) (hm₁a : M₁ = a)
      (hpair : (a = u ∧ b = v) ∨ (a = v ∧ b = u)) : M₂ = b := by
    by_contra hm₂b
    have hm₂a : M₂ ≠ a := fun hEq => hM₂M₁ (hEq.trans hm₁a.symm)
    have hm₂u : M₂ ≠ u := by
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hm₂a
      · exact hm₂b
    have hm₂v : M₂ ≠ v := by
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hm₂b
      · exact hm₂a
    obtain ⟨W, hWu, hWv, hWside, hWmin⟩ := chooseMinOpposite M₂ hm₂u hm₂v
    have hWM₂ : W ≠ M₂ := fun hEq => hWside (congrArg side hEq)
    have hWM₁ : W ≠ M₁ := by
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact fun hEq => hWu (hEq.trans hm₁a)
      · exact fun hEq => hWv (hEq.trans hm₁a)
    have htarget : ∀ r s : α, s ∈ W.val → r < s → r ∉ W.val →
        insert r (W.val.erase s) = u.val ∨ insert r (W.val.erase s) = v.val :=
      decrement_mem_universal_of_side_minimal
        ⟨hFne, hcard, hshift⟩ hWu hWv rfl hside
        (fun T hTu hTv hTside => hWmin T hTu hTv hTside)
    have hWdiff_le := two_outside_impossible_of_all_decrements_in_pair
      ⟨hFne, hcard, hshift⟩ hm₁.1 W.prop hbelow htarget
    have hWdiff_ne : (W.val \ m₁).Nonempty := Finset.sdiff_nonempty.mpr (by
      intro hsub
      apply hWM₁
      apply Subtype.ext
      exact Finset.eq_of_subset_of_card_le hsub (by
        rw [hcard W.val W.prop, hcard m₁ hm₁.1]))
    have hWdiff_card : (W.val \ m₁).card = 1 := by
      have := Finset.card_pos.mpr hWdiff_ne
      omega
    have hm₁diff_card : (m₁ \ W.val).card = 1 := by
      rw [Finset.card_sdiff_comm ((hcard m₁ hm₁.1).trans (hcard W.val W.prop).symm)]
      exact hWdiff_card
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hWdiff_card
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hm₁diff_card
    have hxW : x ∈ W.val := (Finset.mem_sdiff.mp (by simp [hx] : x ∈ W.val \ m₁)).1
    have hxm₁ : x ∉ m₁ := (Finset.mem_sdiff.mp (by simp [hx] : x ∈ W.val \ m₁)).2
    have hpm₁ : p ∈ m₁ := (Finset.mem_sdiff.mp (by simp [hp] : p ∈ m₁ \ W.val)).1
    have hpW : p ∉ W.val := (Finset.mem_sdiff.mp (by simp [hp] : p ∈ m₁ \ W.val)).2
    have hWrepr : W.val = insert x (m₁.erase p) :=
      eq_insert_erase_of_sdiff_eq_singletons hx hp
    have hresolve : ∀ {D : Finset α},
        (D = u.val ∨ D = v.val) → D ≠ m₁ → D = b.val := by
      intro D hD hDm₁
      have hm₁aVal : m₁ = a.val := congrArg Subtype.val hm₁a
      rcases hpair with ⟨hau, hbv⟩ | ⟨hav, hbu⟩
      · have hm₁u : m₁ = u.val := hm₁aVal.trans (congrArg Subtype.val hau)
        rcases hD with hDu | hDv
        · exact absurd (hDu.trans hm₁u.symm) hDm₁
        · exact hDv.trans (congrArg Subtype.val hbv).symm
      · have hm₁v : m₁ = v.val := hm₁aVal.trans (congrArg Subtype.val hav)
        rcases hD with hDu | hDv
        · exact hDu.trans (congrArg Subtype.val hbu).symm
        · exact absurd (hDv.trans hm₁v.symm) hDm₁
    have hjx : j ≤ x := le_of_not_gt (fun hxj => hxm₁ (hjmin x hxj))
    by_cases hxj : x = j
    · by_cases hpi : p = i
      · apply hWM₂
        apply Subtype.ext
        calc
          W.val = insert x (m₁.erase p) := hWrepr
          _ = insert j (m₁.erase i) := by rw [hxj, hpi]
          _ = m₂ := hm₂repr.symm
      · have hpi_lt : p < i := lt_of_le_of_ne (himax p hpm₁) hpi
        have hiW : i ∈ W.val := by
          rw [hWrepr]
          simp [him₁, Ne.symm hpi, hxj, hij.ne]
        let D := insert p (W.val.erase i)
        have hDt : D = u.val ∨ D = v.val := htarget p i hiW hpi_lt hpW
        have hxi : x ≠ i := hxj.trans_ne hij.ne'
        have hxD : x ∈ D := by simp [D, hxW, hxi]
        have hDm₁ : D ≠ m₁ := fun hEq => hxm₁ (hEq ▸ hxD)
        have hDb : D = b.val := hresolve hDt hDm₁
        have hDm₂ : D = m₂ := by
          rw [hm₂repr]
          change insert p (W.val.erase i) = insert j (m₁.erase i)
          rw [hWrepr, hxj]
          exact insert_erase_insert_erase hpm₁ him₁ hjm₁ hpi
        apply hm₂b
        exact Subtype.ext (hDm₂.symm.trans hDb)
    · have hjxlt : j < x := lt_of_le_of_ne hjx (Ne.symm hxj)
      have hjW : j ∉ W.val := by rw [hWrepr]; simp [hjm₁, Ne.symm hxj]
      let D₁ := insert j (W.val.erase x)
      have hD₁t : D₁ = u.val ∨ D₁ = v.val := htarget j x hxW hjxlt hjW
      have hjD₁ : j ∈ D₁ := Finset.mem_insert_self j (W.val.erase x)
      have hD₁m₁ : D₁ ≠ m₁ := fun hEq => hjm₁ (hEq ▸ hjD₁)
      have hD₁b : D₁ = b.val := hresolve hD₁t hD₁m₁
      by_cases hpi : p = i
      · have hD₁m₂ : D₁ = m₂ := by
          rw [hm₂repr]
          change insert j (W.val.erase x) = insert j (m₁.erase i)
          rw [hWrepr, hpi]
          simp [hxm₁]
        apply hm₂b
        exact Subtype.ext (hD₁m₂.symm.trans hD₁b)
      · have hpi_lt : p < i := lt_of_le_of_ne (himax p hpm₁) hpi
        have hiW : i ∈ W.val := by rw [hWrepr]; simp [him₁, Ne.symm hpi]
        let D₂ := insert p (W.val.erase i)
        have hD₂t : D₂ = u.val ∨ D₂ = v.val := htarget p i hiW hpi_lt hpW
        have hxi : x ≠ i := (hij.trans hjxlt).ne'
        have hxD₂ : x ∈ D₂ := by simp [D₂, hxW, hxi]
        have hD₂m₁ : D₂ ≠ m₁ := fun hEq => hxm₁ (hEq ▸ hxD₂)
        have hD₂b : D₂ = b.val := hresolve hD₂t hD₂m₁
        have hxD₁ : x ∉ D₁ := by simp [D₁, hxj]
        exact hxD₁ (hD₁b.trans hD₂b.symm ▸ hxD₂)
  rcases hm₁pair with hm₁u | hm₁v
  · left
    have hm₂v : M₂ = v := step2 u v hm₁u (Or.inl ⟨rfl, rfl⟩)
    have hm₁uVal : m₁ = u.val := congrArg Subtype.val hm₁u
    have hm₂vVal : m₂ = v.val := congrArg Subtype.val hm₂v
    constructor
    · rw [← hm₁uVal]
      exact hm₁
    · rw [← hm₁uVal, ← hm₂vVal]
      exact hm₂
  · right
    have hm₂u : M₂ = u := step2 v u hm₁v (Or.inr ⟨rfl, rfl⟩)
    have hm₁vVal : m₁ = v.val := congrArg Subtype.val hm₁v
    have hm₂uVal : m₂ = u.val := congrArg Subtype.val hm₂u
    constructor
    · rw [← hm₁vVal]
      exact hm₁
    · rw [← hm₁vVal, ← hm₂uVal]
      exact hm₂

/-- Antisymmetry of Gale order, transferred through its colex realization. -/
theorem galeLE_antisymm {A B : Finset α} (hAB : GaleLE A B) (hBA : GaleLE B A) :
    A = B := by
  apply toColex.injective
  exact le_antisymm (toColex_le_of_galeLE hAB) (toColex_le_of_galeLE hBA)

/-- A finite family has at most one Gale-least member. -/
theorem isGaleLeast_unique {F : Finset (Finset α)} {A B : Finset α}
    (hA : IsGaleLeast F A) (hB : IsGaleLeast F B) : A = B :=
  galeLE_antisymm (hA.2 B hB.1) (hB.2 A hA.1)

/-- Once its least member is fixed, a finite family has at most one Gale-second member. -/
theorem isGaleSecondLeast_unique {F : Finset (Finset α)} {m A B : Finset α}
    (hA : IsGaleSecondLeast F m A) (hB : IsGaleSecondLeast F m B) : A = B :=
  galeLE_antisymm (hA.2.2 B hB.1 hB.2.1) (hB.2.2 A hA.1 hA.2.1)

/-- In a uniform family, exchange-graph adjacency removes exactly one element in either directed
difference. -/
theorem card_sdiff_eq_one_of_adj_of_card_eq {F : Finset (Finset α)}
    {A B : ExchangeV F} (hcard : A.val.card = B.val.card)
    (hAdj : (exchangeGraph F).Adj A B) : (A.val \ B.val).card = 1 := by
  simp only [exchangeGraph, SimpleGraph.fromRel_adj] at hAdj
  rcases hAdj.2 with hdiff | hdiff
  · exact (card_symmDiff_eq_two_iff hcard).1 hdiff
  · have hcomm : A.val ∆ B.val = B.val ∆ A.val := by
      ext x
      simp [Finset.symmDiff_def, or_comm]
    have hdiff' : (A.val ∆ B.val).card = 2 := by
      rw [hcomm]
      exact hdiff
    exact (card_symmDiff_eq_two_iff hcard).1 hdiff'

/-- A vertex adjacent to both members of the canonical bottom pair lies in exactly one of the
index-free outer and inner arms. -/
theorem bottom_common_neighbor_arm_xor
    {F : Finset (Finset α)} {m₁ m₂ X : Finset α} {i j : α}
    (hm₁F : m₁ ∈ F) (hm₂F : m₂ ∈ F) (hXF : X ∈ F)
    (heqcard : m₁.card = m₂.card ∧ X.card = m₁.card)
    (him₁ : i ∈ m₁) (him₂ : i ∉ m₂) (hjm₁ : j ∉ m₁)
    (hm₂repr : m₂ = insert j (m₁.erase i)) (hXm₂ : X ≠ m₂)
    (hAdj₁ : (exchangeGraph F).Adj ⟨X, hXF⟩ ⟨m₁, hm₁F⟩)
    (hAdj₂ : (exchangeGraph F).Adj ⟨X, hXF⟩ ⟨m₂, hm₂F⟩) :
    (m₁ ∩ m₂ ⊆ X) ≠ (X ⊆ m₁ ∪ m₂) := by
  have hXdiffCard : (X \ m₁).card = 1 :=
    card_sdiff_eq_one_of_adj_of_card_eq heqcard.2 hAdj₁
  have hm₁diffCard : (m₁ \ X).card = 1 := by
    rw [Finset.card_sdiff_comm heqcard.2.symm]
    exact hXdiffCard
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hXdiffCard
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hm₁diffCard
  have haX : a ∈ X := (Finset.mem_sdiff.mp (by simp [ha] : a ∈ X \ m₁)).1
  have ham₁ : a ∉ m₁ := (Finset.mem_sdiff.mp (by simp [ha] : a ∈ X \ m₁)).2
  have hpm₁ : p ∈ m₁ := (Finset.mem_sdiff.mp (by simp [hp] : p ∈ m₁ \ X)).1
  have hpX : p ∉ X := (Finset.mem_sdiff.mp (by simp [hp] : p ∈ m₁ \ X)).2
  have hXrepr : X = insert a (m₁.erase p) :=
    eq_insert_erase_of_sdiff_eq_singletons ha hp
  have hinter : m₁ ∩ m₂ = m₁.erase i := by
    ext z
    simp [hm₂repr, hjm₁]
  have hunion : m₁ ∪ m₂ = insert j m₁ := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_union.mp hz with hzm₁ | hzm₂
      · exact Finset.mem_insert.mpr (Or.inr hzm₁)
      · rw [hm₂repr] at hzm₂
        rcases Finset.mem_insert.mp hzm₂ with hzj | hzerase
        · exact Finset.mem_insert.mpr (Or.inl hzj)
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_of_mem_erase hzerase))
    · intro hz
      rcases Finset.mem_insert.mp hz with hzj | hzm₁
      · apply Finset.mem_union_right
        rw [hm₂repr]
        exact Finset.mem_insert.mpr (Or.inl hzj)
      · exact Finset.mem_union_left _ hzm₁
  have hPiff : m₁ ∩ m₂ ⊆ X ↔ p = i := by
    rw [hinter]
    constructor
    · intro hsub
      by_contra hpi
      have hpC : p ∈ m₁.erase i := Finset.mem_erase.mpr ⟨hpi, hpm₁⟩
      exact hpX (hsub hpC)
    · rintro rfl z hz
      rw [hXrepr]
      exact Finset.mem_insert.mpr (Or.inr hz)
  have hQiff : X ⊆ m₁ ∪ m₂ ↔ a = j := by
    rw [hunion]
    constructor
    · intro hsub
      have haU := hsub haX
      rcases Finset.mem_insert.mp haU with haj | hamem
      · exact haj
      · exact absurd hamem ham₁
    · rintro rfl z hz
      rw [hXrepr] at hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_of_mem_erase hz))
  have hone : p = i ∨ a = j := by
    by_contra hneither
    rw [not_or] at hneither
    have haM₂ : a ∉ m₂ := by simp [hm₂repr, ham₁, hneither.2]
    have hiX : i ∈ X := by rw [hXrepr]; simp [him₁, Ne.symm hneither.1]
    have haDiff : a ∈ X \ m₂ := Finset.mem_sdiff.mpr ⟨haX, haM₂⟩
    have hiDiff : i ∈ X \ m₂ := Finset.mem_sdiff.mpr ⟨hiX, him₂⟩
    have hai : a ≠ i := fun h => ham₁ (h ▸ him₁)
    have htwo : 2 ≤ (X \ m₂).card := by
      have hlt : 1 < (X \ m₂).card :=
        Finset.one_lt_card.mpr ⟨a, haDiff, i, hiDiff, hai⟩
      omega
    have honeCard : (X \ m₂).card = 1 :=
      card_sdiff_eq_one_of_adj_of_card_eq (heqcard.2.trans heqcard.1) hAdj₂
    omega
  have hnotboth : ¬(p = i ∧ a = j) := by
    rintro ⟨rfl, rfl⟩
    apply hXm₂
    exact hXrepr.trans hm₂repr.symm
  intro hEq
  rcases hone with hpi | haj
  · have hP : m₁ ∩ m₂ ⊆ X := hPiff.2 hpi
    have hQ : X ⊆ m₁ ∪ m₂ := hEq ▸ hP
    exact hnotboth ⟨hpi, hQiff.1 hQ⟩
  · have hQ : X ⊆ m₁ ∪ m₂ := hQiff.2 haj
    have hP : m₁ ∩ m₂ ⊆ X := hEq.symm ▸ hQ
    exact hnotboth ⟨hPiff.1 hP, haj⟩

/-- **Lemma 3, structural (index-free) half**, `STEP_LEMMA_2026-08-15.md` §3.

Every non-universal member of a clique-sum lies in exactly one of two arms, and the arms are
characterized without any index arithmetic: the **outer** arm consists of the members containing
`m₁ ∩ m₂`, and the **inner** arm of the members contained in `m₁ ∪ m₂`. Both are nonempty.

The index-bearing half — that the arms are contiguous, giving the parametrization `F(k; r, s)` —
is `lemma3_arms_are_contiguous` below. -/
theorem lemma3_two_arms {F : Finset (Finset α)} {κ : ℕ}
    (hF : IsShifted F κ) {u v : ExchangeV F} (h : IsCliqueSum F u v) :
    ∀ X : ExchangeV F, X ≠ u → X ≠ v →
      (u.val ∩ v.val ⊆ X.val) ≠ (X.val ⊆ u.val ∪ v.val) := by
  have hleastPair := lemma2_universalPair_is_galeLeast hF h
  rcases h with ⟨huv, huUniv, hvUniv, side, htrue, hfalse, hside⟩
  have huvval : u.val ≠ v.val := fun heq => huv (Subtype.ext heq)
  have hpairsub : {u.val, v.val} ⊆ F := by
    intro Y hY
    rcases Finset.mem_insert.mp hY with hY | hY
    · exact hY ▸ u.prop
    · have hY' : Y = v.val := by simpa using hY
      exact hY' ▸ v.prop
  have hpaircard := Finset.card_le_card hpairsub
  have htwo : 2 ≤ F.card := by simpa [Finset.card_pair huvval] using hpaircard
  obtain ⟨m₁, m₂, hm₁, hm₂, i, j, him₁, him₂, hjm₂, hjm₁, hij,
      hm₂repr, himax, hjmin⟩ := exists_gale_bottom_pair_with_boundary hF htwo
  rcases hF with ⟨hFne, hcard, hshift⟩
  let M₁ : ExchangeV F := ⟨m₁, hm₁.1⟩
  let M₂ : ExchangeV F := ⟨m₂, hm₂.1⟩
  have hcards : m₁.card = m₂.card ∧ ∀ X : ExchangeV F, X.val.card = m₁.card := by
    exact ⟨(hcard m₁ hm₁.1).trans (hcard m₂ hm₂.1).symm,
      fun X => (hcard X.val X.prop).trans (hcard m₁ hm₁.1).symm⟩
  intro X hXu hXv
  rcases hleastPair with ⟨huLeast, hvSecond⟩ | ⟨hvLeast, huSecond⟩
  · have huEq : u.val = m₁ := isGaleLeast_unique huLeast hm₁
    have hvSecond' : IsGaleSecondLeast F m₁ v.val := by
      rw [← huEq]
      exact hvSecond
    have hvEq : v.val = m₂ := isGaleSecondLeast_unique hvSecond' hm₂
    have huM₁ : u = M₁ := by apply Subtype.ext; exact huEq
    have hvM₂ : v = M₂ := by apply Subtype.ext; exact hvEq
    have hXm₂ : X.val ≠ m₂ := fun heq => hXv (by
      apply Subtype.ext
      exact heq.trans hvEq.symm)
    have hAdj₁ : (exchangeGraph F).Adj X M₁ := by
      rw [← huM₁]
      exact (huUniv X hXu).symm
    have hAdj₂ : (exchangeGraph F).Adj X M₂ := by
      rw [← hvM₂]
      exact (hvUniv X hXv).symm
    have hcore := bottom_common_neighbor_arm_xor hm₁.1 hm₂.1 X.prop
      ⟨hcards.1, hcards.2 X⟩ him₁ him₂ hjm₁ hm₂repr hXm₂ hAdj₁ hAdj₂
    simpa only [huEq, hvEq] using hcore
  · have hvEq : v.val = m₁ := isGaleLeast_unique hvLeast hm₁
    have huSecond' : IsGaleSecondLeast F m₁ u.val := by
      rw [← hvEq]
      exact huSecond
    have huEq : u.val = m₂ := isGaleSecondLeast_unique huSecond' hm₂
    have hvM₁ : v = M₁ := by apply Subtype.ext; exact hvEq
    have huM₂ : u = M₂ := by apply Subtype.ext; exact huEq
    have hXm₂ : X.val ≠ m₂ := fun heq => hXu (by
      apply Subtype.ext
      exact heq.trans huEq.symm)
    have hAdj₁ : (exchangeGraph F).Adj X M₁ := by
      rw [← hvM₁]
      exact (hvUniv X hXv).symm
    have hAdj₂ : (exchangeGraph F).Adj X M₂ := by
      rw [← huM₂]
      exact (huUniv X hXu).symm
    have hcore := bottom_common_neighbor_arm_xor hm₁.1 hm₂.1 X.prop
      ⟨hcards.1, hcards.2 X⟩ him₁ him₂ hjm₁ hm₂repr hXm₂ hAdj₁ hAdj₂
    simpa only [huEq, hvEq, Finset.inter_comm, Finset.union_comm] using hcore

private theorem prop_xor_of_ne {P Q : Prop} (h : P ≠ Q) :
    (P ∧ ¬ Q) ∨ (¬ P ∧ Q) := by
  by_cases hP : P
  · by_cases hQ : Q
    · exfalso
      apply h
      exact propext ⟨fun _ => hQ, fun _ => hP⟩
    · exact Or.inl ⟨hP, hQ⟩
  · by_cases hQ : Q
    · exact Or.inr ⟨hP, hQ⟩
    · exfalso
      apply h
      exact propext ⟨fun hP' => (hP hP').elim, fun hQ' => (hQ hQ').elim⟩

/-- Two distinct members which contain the same codimension-one core are exchange-adjacent. -/
private theorem exchangeGraph_adj_of_common_lowerCover
    {F : Finset (Finset α)} {C X Y : Finset α}
    (hXF : X ∈ F) (hYF : Y ∈ F) (hCX : C ⊆ X) (hCY : C ⊆ Y)
    (hXcard : X.card = C.card + 1) (hYcard : Y.card = C.card + 1)
    (hXY : X ≠ Y) :
    (exchangeGraph F).Adj ⟨X, hXF⟩ ⟨Y, hYF⟩ := by
  have hXCcard : (X \ C).card = 1 := by
    rw [Finset.card_sdiff_of_subset hCX, hXcard]
    omega
  have hYCcard : (Y \ C).card = 1 := by
    rw [Finset.card_sdiff_of_subset hCY, hYcard]
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hXCcard
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hYCcard
  have haDiff : a ∈ X \ C := by simp [ha]
  have hbDiff : b ∈ Y \ C := by simp [hb]
  have haX : a ∈ X := (Finset.mem_sdiff.mp haDiff).1
  have haC : a ∉ C := (Finset.mem_sdiff.mp haDiff).2
  have hbY : b ∈ Y := (Finset.mem_sdiff.mp hbDiff).1
  have hbC : b ∉ C := (Finset.mem_sdiff.mp hbDiff).2
  have hXrepr : X = insert a C := by
    apply Finset.Subset.antisymm
    · intro z hzX
      by_cases hzC : z ∈ C
      · exact Finset.mem_insert.mpr (Or.inr hzC)
      · have hzDiff : z ∈ X \ C := Finset.mem_sdiff.mpr ⟨hzX, hzC⟩
        have hza : z = a := by simpa [ha] using hzDiff
        exact Finset.mem_insert.mpr (Or.inl hza)
    · exact Finset.insert_subset haX hCX
  have hYrepr : Y = insert b C := by
    apply Finset.Subset.antisymm
    · intro z hzY
      by_cases hzC : z ∈ C
      · exact Finset.mem_insert.mpr (Or.inr hzC)
      · have hzDiff : z ∈ Y \ C := Finset.mem_sdiff.mpr ⟨hzY, hzC⟩
        have hzb : z = b := by simpa [hb] using hzDiff
        exact Finset.mem_insert.mpr (Or.inl hzb)
    · exact Finset.insert_subset hbY hCY
  have hab : a ≠ b := by
    intro hab
    apply hXY
    rw [hXrepr, hYrepr, hab]
  have hbX : b ∉ X := by simp [hXrepr, hbC, hab.symm]
  apply exchangeGraph_adj_of_replacement hXF hYF haX hbX hab.symm
  rw [hXrepr, hYrepr]
  simp [haC]

/-- Two distinct members contained in the same codimension-one extension are exchange-adjacent. -/
private theorem exchangeGraph_adj_of_common_upperCover
    {F : Finset (Finset α)} {U X Y : Finset α}
    (hXF : X ∈ F) (hYF : Y ∈ F) (hXU : X ⊆ U) (hYU : Y ⊆ U)
    (hUcardX : U.card = X.card + 1) (hUcardY : U.card = Y.card + 1)
    (hXY : X ≠ Y) :
    (exchangeGraph F).Adj ⟨X, hXF⟩ ⟨Y, hYF⟩ := by
  have hUXcard : (U \ X).card = 1 := by
    rw [Finset.card_sdiff_of_subset hXU, hUcardX]
    omega
  have hUYcard : (U \ Y).card = 1 := by
    rw [Finset.card_sdiff_of_subset hYU, hUcardY]
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hUXcard
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hUYcard
  have haDiff : a ∈ U \ X := by simp [ha]
  have hbDiff : b ∈ U \ Y := by simp [hb]
  have haU : a ∈ U := (Finset.mem_sdiff.mp haDiff).1
  have haX : a ∉ X := (Finset.mem_sdiff.mp haDiff).2
  have hbU : b ∈ U := (Finset.mem_sdiff.mp hbDiff).1
  have hbY : b ∉ Y := (Finset.mem_sdiff.mp hbDiff).2
  have hXrepr : X = U.erase a := by
    apply Finset.Subset.antisymm
    · exact fun z hzX => Finset.mem_erase.mpr ⟨fun hza => haX (hza ▸ hzX), hXU hzX⟩
    · intro z hz
      obtain ⟨hza, hzU⟩ := Finset.mem_erase.mp hz
      by_contra hzX
      have hzDiff : z ∈ U \ X := Finset.mem_sdiff.mpr ⟨hzU, hzX⟩
      have : z = a := by simpa [ha] using hzDiff
      exact hza this
  have hYrepr : Y = U.erase b := by
    apply Finset.Subset.antisymm
    · exact fun z hzY => Finset.mem_erase.mpr ⟨fun hzb => hbY (hzb ▸ hzY), hYU hzY⟩
    · intro z hz
      obtain ⟨hzb, hzU⟩ := Finset.mem_erase.mp hz
      by_contra hzY
      have hzDiff : z ∈ U \ Y := Finset.mem_sdiff.mpr ⟨hzU, hzY⟩
      have : z = b := by simpa [hb] using hzDiff
      exact hzb this
  have hab : a ≠ b := by
    intro hab
    apply hXY
    rw [hXrepr, hYrepr, hab]
  have hbX : b ∈ X := by simp [hXrepr, hbU, hab.symm]
  apply exchangeGraph_adj_of_replacement hXF hYF hbX haX hab
  rw [hXrepr, hYrepr]
  ext z
  simp only [Finset.mem_erase, Finset.mem_insert]
  constructor
  · rintro ⟨hzb, hzU⟩
    by_cases hza : z = a
    · exact Or.inl hza
    · exact Or.inr ⟨hzb, hza, hzU⟩
  · rintro (rfl | ⟨hzb, _hza, hzU⟩)
    · exact ⟨hab, haU⟩
    · exact ⟨hzb, hzU⟩

/-- A family cut out by a single Gale upper bound cannot be a clique-sum. -/
private theorem not_isCliqueSum_of_principal
    {F : Finset (Finset α)} {κ : ℕ} (hF : IsShifted F κ) (M : Finset α)
    (hprincipal : ∀ X, X ∈ F ↔ (X.card = κ ∧ GaleLE X M))
    (u v : ExchangeV F) : ¬ IsCliqueSum F u v := by
  intro hbad
  have hleast := lemma2_universalPair_is_galeLeast hF hbad
  have harms := lemma3_two_arms hF hbad
  rcases hbad with ⟨huv, huUniv, hvUniv, side, htrue, hfalse, hside⟩
  have hcard := hF.2.1
  have huvval : u.val ≠ v.val := fun h => huv (Subtype.ext h)
  have hpairsub : {u.val, v.val} ⊆ F := by
    intro X hX
    rcases Finset.mem_insert.mp hX with hX | hX
    · exact hX ▸ u.prop
    · have hX' : X = v.val := by simpa using hX
      exact hX' ▸ v.prop
  have htwo : 2 ≤ F.card := by
    have := Finset.card_le_card hpairsub
    simpa [Finset.card_pair huvval] using this
  obtain ⟨m₁, m₂, hm₁, hm₂, i, j, him₁, him₂, hjm₂, hjm₁, hij,
      hm₂repr, himax, hjmin⟩ := exists_gale_bottom_pair_with_boundary hF htwo
  have hpairEq :
      (u.val = m₁ ∧ v.val = m₂) ∨ (v.val = m₁ ∧ u.val = m₂) := by
    rcases hleast with ⟨huLeast, hvSecond⟩ | ⟨hvLeast, huSecond⟩
    · left
      have huEq : u.val = m₁ := isGaleLeast_unique huLeast hm₁
      refine ⟨huEq, ?_⟩
      apply isGaleSecondLeast_unique (m := m₁)
      · rwa [← huEq]
      · exact hm₂
    · right
      have hvEq : v.val = m₁ := isGaleLeast_unique hvLeast hm₁
      refine ⟨hvEq, ?_⟩
      apply isGaleSecondLeast_unique (m := m₁)
      · rwa [← hvEq]
      · exact hm₂
  have hUVinter : u.val ∩ v.val = m₁ ∩ m₂ := by
    rcases hpairEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Finset.inter_comm _ _
  have hUVunion : u.val ∪ v.val = m₁ ∪ m₂ := by
    rcases hpairEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Finset.union_comm _ _
  have hCform : m₁ ∩ m₂ = m₁.erase i := by
    ext z
    simp [hm₂repr, hjm₁]
  have hUform : m₁ ∪ m₂ = insert j m₁ := by
    ext z
    rw [hm₂repr]
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro (hzm₁ | rfl | ⟨_hzj, hzm₁⟩)
      · exact Or.inr hzm₁
      · exact Or.inl rfl
      · exact Or.inr hzm₁
    · rintro (rfl | hzm₁)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl hzm₁
  have hm₁card : m₁.card = κ := hcard m₁ hm₁.1
  have hCcard : (m₁ ∩ m₂).card + 1 = κ := by
    rw [hCform, Finset.card_erase_of_mem him₁, hm₁card]
    have : 0 < κ := by
      rw [← hm₁card]
      exact Finset.card_pos.mpr ⟨i, him₁⟩
    omega
  have hUcard : (m₁ ∪ m₂).card = κ + 1 := by
    rw [hUform, Finset.card_insert_of_notMem hjm₁, hm₁card]
  let P : ExchangeV F → Prop := fun X => m₁ ∩ m₂ ⊆ X.val
  let Q : ExchangeV F → Prop := fun X => X.val ⊆ m₁ ∪ m₂
  obtain ⟨T, hTu, hTv, hTside⟩ := htrue
  obtain ⟨R, hRu, hRv, hRside⟩ := hfalse
  have hTR : T ≠ R := by
    intro hEq
    have hsides := congrArg side hEq
    have : true = false := hTside.symm.trans (hsides.trans hRside)
    simp at this
  have hnotAdj : ¬(exchangeGraph F).Adj T R := by
    intro hAdj
    have hsides := (hside T R hTu hTv hRu hRv hTR).1 hAdj
    have : true = false := hTside.symm.trans (hsides.trans hRside)
    simp at this
  have hTarm : P T ≠ Q T := by
    simpa only [P, Q, hUVinter, hUVunion] using harms T hTu hTv
  have hRarm : P R ≠ Q R := by
    simpa only [P, Q, hUVinter, hUVunion] using harms R hRu hRv
  have hnotBothP : ¬(P T ∧ P R) := by
    rintro ⟨hTP, hRP⟩
    apply hnotAdj
    apply exchangeGraph_adj_of_common_lowerCover T.prop R.prop hTP hRP
    · exact (hcard T.val T.prop).trans hCcard.symm
    · exact (hcard R.val R.prop).trans hCcard.symm
    · exact fun h => hTR (Subtype.ext h)
  have hnotBothQ : ¬(Q T ∧ Q R) := by
    rintro ⟨hTQ, hRQ⟩
    apply hnotAdj
    apply exchangeGraph_adj_of_common_upperCover T.prop R.prop hTQ hRQ
    · rw [hUcard, hcard T.val T.prop]
    · rw [hUcard, hcard R.val R.prop]
    · exact fun h => hTR (Subtype.ext h)
  obtain ⟨X, Y, hXP, hXnQ, hYnP, hYQ⟩ :
      ∃ X Y : ExchangeV F, P X ∧ ¬ Q X ∧ ¬ P Y ∧ Q Y := by
    rcases prop_xor_of_ne hTarm with ⟨hTP, hTnQ⟩ | ⟨hTnP, hTQ⟩
    · rcases prop_xor_of_ne hRarm with ⟨hRP, hRnQ⟩ | ⟨hRnP, hRQ⟩
      · exact (hnotBothP ⟨hTP, hRP⟩).elim
      · exact ⟨T, R, hTP, hTnQ, hRnP, hRQ⟩
    · rcases prop_xor_of_ne hRarm with ⟨hRP, hRnQ⟩ | ⟨hRnP, hRQ⟩
      · exact ⟨R, T, hRP, hRnQ, hTnP, hTQ⟩
      · exact (hnotBothQ ⟨hTQ, hRQ⟩).elim
  obtain ⟨a, haX, haU⟩ := Finset.not_subset.mp hXnQ
  have hCsubU : m₁ ∩ m₂ ⊆ m₁ ∪ m₂ := by
    intro z hz
    exact Finset.mem_union_left _ (Finset.mem_inter.mp hz).1
  have haC : a ∉ m₁ ∩ m₂ := fun ha => haU (hCsubU ha)
  have hXrepr : X.val = insert a (m₁ ∩ m₂) := by
    have hsub : insert a (m₁ ∩ m₂) ⊆ X.val :=
      Finset.insert_subset haX hXP
    apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [Finset.card_insert_of_notMem haC, hCcard, hcard X.val X.prop]
  obtain ⟨p, hpC, hpY⟩ := Finset.not_subset.mp hYnP
  have hpU : p ∈ m₁ ∪ m₂ := hCsubU hpC
  have hUreprY : m₁ ∪ m₂ = insert p Y.val := by
    have hsub : insert p Y.val ⊆ m₁ ∪ m₂ :=
      Finset.insert_subset hpU hYQ
    apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [Finset.card_insert_of_notMem hpY, hUcard, hcard Y.val Y.prop]
  have hYrepr : Y.val = (m₁ ∪ m₂).erase p := by
    rw [hUreprY]
    simp [hpY]
  have hpErase : p ∈ m₁.erase i := by simpa only [← hCform] using hpC
  have hpne : p ≠ i := (Finset.mem_erase.mp hpErase).1
  have hpm₁ : p ∈ m₁ := (Finset.mem_erase.mp hpErase).2
  have hpi : p < i := lt_of_le_of_ne (himax p hpm₁) hpne
  have haNotm₁ : a ∉ m₁ := fun ha => haU (Finset.mem_union_left _ ha)
  have hjU : j ∈ m₁ ∪ m₂ := Finset.mem_union_right _ hjm₂
  have hja : j < a := by
    have hjaLe : j ≤ a := le_of_not_gt (fun haj => haNotm₁ (hjmin a haj))
    exact lt_of_le_of_ne hjaLe (fun h => haU (h ▸ hjU))
  have hXrepr' : X.val = insert a (m₁.erase i) := by rw [hXrepr, hCform]
  have hYrepr' : Y.val = insert j (m₁.erase p) := by
    rw [hYrepr, hUform]
    exact Finset.erase_insert_of_ne (hpi.trans hij).ne.symm
  let Z : Finset α := insert a (m₁.erase p)
  have hZcard : Z.card = κ := by
    rw [Finset.card_insert_of_notMem (by simp [haNotm₁]),
      Finset.card_erase_of_mem hpm₁, hm₁card]
    have : 0 < κ := by
      rw [← hm₁card]
      exact Finset.card_pos.mpr ⟨p, hpm₁⟩
    omega
  have hXM : GaleLE X.val M := (hprincipal X.val).1 X.prop |>.2
  have hYM : GaleLE Y.val M := (hprincipal Y.val).1 Y.prop |>.2
  have hZM : GaleLE Z M := by
    intro t
    by_cases htp : t ≤ p
    · have hti : t ≤ i := htp.trans hpi.le
      have hta : t ≤ a := hti.trans (hij.trans hja).le
      have hfilters :
          (Z.filter fun z => t ≤ z).card = (X.val.filter fun z => t ≤ z).card := by
        rw [hXrepr']
        have hpHigh : p ∈ m₁.filter (fun z => t ≤ z) := by simp [hpm₁, htp]
        have hiHigh : i ∈ m₁.filter (fun z => t ≤ z) := by simp [him₁, hti]
        have haHigh : a ∉ m₁.filter (fun z => t ≤ z) := by simp [haNotm₁]
        simp only [Z, Finset.filter_insert, hta, if_true, Finset.filter_erase]
        rw [Finset.card_insert_of_notMem (by simp [haHigh]),
          Finset.card_insert_of_notMem (by simp [haHigh]),
          Finset.card_erase_of_mem hpHigh, Finset.card_erase_of_mem hiHigh]
      rw [hfilters]
      exact hXM t
    · by_cases hti : t ≤ i
      · have htj : t ≤ j := hti.trans hij.le
        have hta : t ≤ a := htj.trans hja.le
        have hfilters :
            (Z.filter fun z => t ≤ z).card = (Y.val.filter fun z => t ≤ z).card := by
          rw [hYrepr']
          have haHigh : a ∉ (m₁.filter (fun z => t ≤ z)).erase p := by
            simp [haNotm₁]
          have hjHigh : j ∉ (m₁.filter (fun z => t ≤ z)).erase p := by
            simp [hjm₁]
          simp only [Z, Finset.filter_insert, hta, htj, if_true, Finset.filter_erase]
          rw [Finset.card_insert_of_notMem haHigh, Finset.card_insert_of_notMem hjHigh]
        rw [hfilters]
        exact hYM t
      · have hm₁high : m₁.filter (fun z => t ≤ z) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro z hz
          simp only [Finset.mem_filter] at hz
          exact hti (hz.2.trans (himax z hz.1))
        have hfilters :
          (Z.filter fun z => t ≤ z).card = (X.val.filter fun z => t ≤ z).card := by
          rw [hXrepr']
          simp only [Z, Finset.filter_insert, Finset.filter_erase, hm₁high,
            Finset.erase_empty]
        rw [hfilters]
        exact hXM t
  have hZF : Z ∈ F := (hprincipal Z).2 ⟨hZcard, hZM⟩
  let ZV : ExchangeV F := ⟨Z, hZF⟩
  have hpa : p ≠ a := fun h => haNotm₁ (h ▸ hpm₁)
  have hpZ : p ∉ Z := by simp [Z, hpa]
  have haZ : a ∈ Z := by simp [Z]
  have hZnP : ¬ P ZV := by
    intro hP
    exact hpZ (hP hpC)
  have hZnQ : ¬ Q ZV := by
    intro hQ
    exact haU (hQ haZ)
  have hZu : ZV ≠ u := by
    intro hEq
    apply hZnP
    change m₁ ∩ m₂ ⊆ Z
    have hvalEq : Z = u.val := congrArg Subtype.val hEq
    rw [hvalEq]
    intro z hz
    exact (Finset.mem_inter.mp (hUVinter.symm ▸ hz)).1
  have hZv : ZV ≠ v := by
    intro hEq
    apply hZnP
    change m₁ ∩ m₂ ⊆ Z
    have hvalEq : Z = v.val := congrArg Subtype.val hEq
    rw [hvalEq]
    intro z hz
    exact (Finset.mem_inter.mp (hUVinter.symm ▸ hz)).2
  have hZarm : P ZV ≠ Q ZV := by
    simpa only [P, Q, hUVinter, hUVunion] using harms ZV hZu hZv
  apply hZarm
  apply propext
  exact ⟨fun h => (hZnP h).elim, fun h => (hZnQ h).elim⟩

/-- A nonempty equicardinal family cut out by one Gale upper bound is shifted. -/
private theorem isShifted_of_principal
    {F : Finset (Finset α)} {κ : ℕ} (M : Finset α)
    (hprincipal : ∀ X, X ∈ F ↔ (X.card = κ ∧ GaleLE X M))
    (hne : F.Nonempty) : IsShifted F κ := by
  rw [isShifted_iff_isGaleIdeal]
  refine ⟨hne, fun X hXF => ((hprincipal X).1 hXF).1, ?_⟩
  intro X hXF B hBcard hBX
  apply (hprincipal B).2
  exact ⟨hBcard, galeLE_trans hBX ((hprincipal X).1 hXF).2⟩

/-! ## 5. `(Q*)` -/

/-- The two universal vertices of a clique-sum cannot be the endpoints of a Hamilton path.
Deleting the endpoints from such a path would leave one chain through every non-universal vertex,
but every edge of that chain preserves the side of the clique-sum while both sides are nonempty. -/
theorem no_hamPath_of_cliqueSum {W : Type u} [DecidableEq W]
    {G : SimpleGraph W} {u v : W} (hbad : G.IsCliqueSum u v) :
    ¬ HasHamPath G u v := by
  rintro ⟨p, hp⟩
  rcases hbad with ⟨huv, _hu, _hv, side, ⟨a, hau, hav, ha⟩,
    ⟨b, hbu, hbv, hb⟩, hside⟩
  have hpnotnil : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne huv
  let interior : List W := p.tail.support.dropLast
  have hdecomp : p.support = u :: interior ++ [v] := by
    rw [← p.cons_support_tail hpnotnil]
    rw [← p.tail.dropLast_support_concat]
    simp [interior]
  have hnodup : (u :: interior ++ [v]).Nodup := by
    rw [← hdecomp]
    exact hp.isPath.support_nodup
  have huI : u ∉ interior := by
    exact fun hu => (List.nodup_cons.mp hnodup).1 (List.mem_append_left [v] hu)
  have hvI : v ∉ interior := by
    have htail := (List.nodup_cons.mp hnodup).2
    have hd : List.Disjoint interior [v] := List.disjoint_of_nodup_append htail
    exact fun hv => (List.disjoint_left.mp hd) hv (by simp)
  have haI : a ∈ interior := by
    have hamem := hp.mem_support a
    rw [hdecomp] at hamem
    simpa [hau, hav] using hamem
  have hbI : b ∈ interior := by
    have hbmem := hp.mem_support b
    rw [hdecomp] at hbmem
    simpa [hbu, hbv] using hbmem
  have hchainI : interior.IsChain G.Adj := by
    have hchain := (p.isChain_adj_support.tail).dropLast
    simpa [interior, p.support_tail_of_not_nil hpnotnil] using hchain
  have hchainSide : (interior.map side).IsChain (· = ·) := by
    rw [List.isChain_map]
    apply hchainI.imp_of_mem_imp
    intro x y hx hy hxy
    exact (hside x y (fun h => huI (h ▸ hx)) (fun h => hvI (h ▸ hx))
      (fun h => huI (h ▸ hy)) (fun h => hvI (h ▸ hy)) hxy.ne).1 hxy
  have haMap : side a ∈ interior.map side := List.mem_map.mpr ⟨a, haI, rfl⟩
  have hbMap : side b ∈ interior.map side := List.mem_map.mpr ⟨b, hbI, rfl⟩
  cases hmap : interior.map side with
  | nil => simp [hmap] at haMap
  | cons c cs =>
      have htailrep : cs = List.replicate cs.length c :=
        List.isChain_cons_eq_iff_eq_replicate.mp (hmap ▸ hchainSide)
      have hac : side a = c := by
        rw [hmap, htailrep] at haMap
        simp only [List.mem_cons, List.mem_replicate] at haMap
        exact haMap.elim id And.right
      have hbc : side b = c := by
        rw [hmap, htailrep] at hbMap
        simp only [List.mem_cons, List.mem_replicate] at hbMap
        exact hbMap.elim id And.right
      exact Bool.false_ne_true (ha.symm.trans (hac.trans (hbc.symm.trans hb))).symm


/-! ## 6. The crossing lemma -/

/-- The layer of `F` above `e` (members containing `e`) and below `e` (members avoiding it). -/
def layerAbove (F : Finset (Finset α)) (e : α) : Finset (Finset α) := F.filter (fun X => e ∈ X)

/-- See `layerAbove`. -/
def layerBelow (F : Finset (Finset α)) (e : α) : Finset (Finset α) := F.filter (fun X => e ∉ X)

/-! ## 6.1. Complement-and-reverse duality -/

/-- Order reversal on the zero-indexed ground set `Fin n`. Thus the manuscript's one-indexed
formula `x ↦ n + 1 - x` becomes `e ↦ n - 1 - e`, implemented by `Fin.rev`. -/
def dualElem {n : ℕ} (e : Fin n) : Fin n := e.rev

/-- Complement in the whole ground set `Fin n`, then reverse its order. -/
def dualSet {n : ℕ} (X : Finset (Fin n)) : Finset (Fin n) := Xᶜ.image dualElem

/-- The zero-indexed numerical form of the reversal convention. -/
theorem dualElem_val {n : ℕ} (e : Fin n) :
    (dualElem e).val = n - (e.val + 1) := by
  exact Fin.val_rev e

/-- Sanity check: for `n = 5`, the dual of zero-indexed `{0, 2}` is `{0, 1, 3}`.
Equivalently, the one-indexed dual of `{1, 3}` is `{1, 2, 4}`. -/
theorem dualSet_fin5_example :
    dualSet ({0, 2} : Finset (Fin 5)) = {0, 1, 3} := by
  decide

@[simp] theorem dualElem_dualElem {n : ℕ} (e : Fin n) : dualElem (dualElem e) = e := by
  exact Fin.rev_rev e

theorem dualElem_injective {n : ℕ} : Function.Injective (@dualElem n) := by
  exact fun _ _ h => Fin.rev_injective h

@[simp] theorem mem_dualSet {n : ℕ} {X : Finset (Fin n)} {e : Fin n} :
    e ∈ dualSet X ↔ dualElem e ∉ X := by
  simp only [dualSet, Finset.mem_image, Finset.mem_compl]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro he
    exact ⟨dualElem e, he, by simp⟩

theorem mem_iff_dualElem_notMem_dualSet {n : ℕ} {X : Finset (Fin n)} {e : Fin n} :
    e ∈ X ↔ dualElem e ∉ dualSet X := by
  simp

@[simp] theorem dualSet_dualSet {n : ℕ} (X : Finset (Fin n)) :
    dualSet (dualSet X) = X := by
  ext e
  simp

theorem card_dualSet {n : ℕ} (X : Finset (Fin n)) :
    (dualSet X).card = n - X.card := by
  rw [dualSet, Finset.card_image_of_injective _ dualElem_injective,
    Finset.card_compl, Fintype.card_fin]

/-- Complement-and-reverse commutes with symmetric difference up to the reversal image. -/
theorem dualSet_symmDiff {n : ℕ} (X Y : Finset (Fin n)) :
    dualSet X ∆ dualSet Y = (X ∆ Y).image dualElem := by
  ext e
  simp only [Finset.mem_symmDiff, mem_dualSet, Finset.mem_image]
  constructor
  · intro h
    refine ⟨dualElem e, ?_, by simp⟩
    aesop
  · rintro ⟨a, ha, rfl⟩
    aesop

/-- Complement-and-reverse preserves symmetric-difference distance. -/
theorem card_dualSet_symmDiff {n : ℕ} (X Y : Finset (Fin n)) :
    (dualSet X ∆ dualSet Y).card = (X ∆ Y).card := by
  rw [dualSet_symmDiff,
    Finset.card_image_of_injective _ dualElem_injective]

@[simp] theorem dualSet_subset_dualSet {n : ℕ} {X Y : Finset (Fin n)} :
    dualSet X ⊆ dualSet Y ↔ Y ⊆ X := by
  constructor
  · intro h e heY
    by_contra heX
    have heDX : dualElem e ∈ dualSet X := mem_dualSet.mpr (by simpa using heX)
    have heDY : dualElem e ∈ dualSet Y := h heDX
    exact (mem_dualSet.mp heDY) (by simpa using heY)
  · intro h e heDX
    apply mem_dualSet.mpr
    intro heY
    exact (mem_dualSet.mp heDX) (h heY)

/-- Complement reverses inclusion, while the reversal bijection preserves it. -/
theorem subset_iff_dualSet_subset {n : ℕ} {X Y : Finset (Fin n)} :
    X ⊆ Y ↔ dualSet Y ⊆ dualSet X := by
  exact dualSet_subset_dualSet.symm

/-- Dualizing a union gives the intersection of the duals. -/
theorem dualSet_union {n : ℕ} (X Y : Finset (Fin n)) :
    dualSet (X ∪ Y) = dualSet X ∩ dualSet Y := by
  ext e
  simp only [mem_dualSet, Finset.mem_union, Finset.mem_inter]
  tauto

/-- Dualizing an intersection gives the union of the duals. -/
theorem dualSet_inter {n : ℕ} (X Y : Finset (Fin n)) :
    dualSet (X ∩ Y) = dualSet X ∪ dualSet Y := by
  ext e
  simp only [mem_dualSet, Finset.mem_inter, Finset.mem_union]
  tauto

/-- Under duality, membership in an inner arm becomes membership in an outer arm. -/
theorem innerArm_dual_iff_outerArm {n : ℕ} {X u v : Finset (Fin n)} :
    X ⊆ u ∪ v ↔ dualSet u ∩ dualSet v ⊆ dualSet X := by
  rw [subset_iff_dualSet_subset, dualSet_union]

/-- Under duality, membership in an outer arm becomes membership in an inner arm. -/
theorem outerArm_dual_iff_innerArm {n : ℕ} {X u v : Finset (Fin n)} :
    u ∩ v ⊆ X ↔ dualSet X ⊆ dualSet u ∪ dualSet v := by
  rw [subset_iff_dualSet_subset, dualSet_inter]

theorem card_filter_dualSet_ge {n : ℕ} (X : Finset (Fin n)) (x : Fin n) :
    ((dualSet X).filter fun z => x ≤ z).card =
      ((Finset.univ.filter fun z => z ≤ dualElem x) \ X).card := by
  let S := Finset.univ.filter fun z => z ≤ dualElem x
  have hset : ((dualSet X).filter fun z => x ≤ z) = (S \ X).image dualElem := by
    ext z
    simp only [Finset.mem_filter, mem_dualSet, Finset.mem_image, Finset.mem_sdiff,
      Finset.mem_univ, true_and, S]
    constructor
    · rintro ⟨hzX, hxz⟩
      exact ⟨dualElem z, ⟨Fin.rev_le_rev.mpr hxz, hzX⟩, by simp⟩
    · rintro ⟨y, ⟨hyx, hyX⟩, rfl⟩
      refine ⟨by simpa using hyX, ?_⟩
      simpa [dualElem] using Fin.rev_anti hyx
  rw [hset, Finset.card_image_of_injective _ dualElem_injective]

theorem card_filter_dualSet_le {n : ℕ} (X : Finset (Fin n)) (x : Fin n) :
    ((dualSet X).filter fun z => z ≤ x).card =
      ((Finset.univ.filter fun z => dualElem x ≤ z) \ X).card := by
  let S := Finset.univ.filter fun z => dualElem x ≤ z
  have hset : ((dualSet X).filter fun z => z ≤ x) = (S \ X).image dualElem := by
    ext z
    simp only [Finset.mem_filter, mem_dualSet, Finset.mem_image, Finset.mem_sdiff,
      Finset.mem_univ, true_and, S]
    constructor
    · rintro ⟨hzX, hzx⟩
      refine ⟨dualElem z, ⟨?_, hzX⟩, by simp⟩
      simpa [dualElem] using Fin.rev_anti hzx
    · rintro ⟨y, ⟨hxy, hyX⟩, rfl⟩
      refine ⟨by simpa using hyX, ?_⟩
      simpa [dualElem] using Fin.rev_anti hxy
  rw [hset, Finset.card_image_of_injective _ dualElem_injective]

theorem galeLE_iff_lowerCard_ge {n : ℕ} {X Y : Finset (Fin n)}
    (hcard : X.card = Y.card) :
    GaleLE X Y ↔
      ∀ x : Fin n, (Y.filter fun z => z ≤ x).card ≤ (X.filter fun z => z ≤ x).card := by
  constructor
  · intro h x
    by_cases hx : x.val + 1 < n
    · let s : Fin n := ⟨x.val + 1, hx⟩
      have hXpart := Finset.card_filter_add_card_filter_not
        (s := X) (p := fun z => z ≤ x)
      have hYpart := Finset.card_filter_add_card_filter_not
        (s := Y) (p := fun z => z ≤ x)
      have hXfilter : (X.filter fun z => ¬z ≤ x) = X.filter fun z => s ≤ z := by
        ext z
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hzX, hzx⟩
          refine ⟨hzX, ?_⟩
          simp only [Fin.le_iff_val_le_val, s]
          simp only [Fin.le_iff_val_le_val] at hzx
          omega
        · rintro ⟨hzX, hsz⟩
          refine ⟨hzX, ?_⟩
          simp only [Fin.le_iff_val_le_val, s] at hsz
          simp only [Fin.le_iff_val_le_val]
          omega
      have hYfilter : (Y.filter fun z => ¬z ≤ x) = Y.filter fun z => s ≤ z := by
        ext z
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hzY, hzx⟩
          refine ⟨hzY, ?_⟩
          simp only [Fin.le_iff_val_le_val, s]
          simp only [Fin.le_iff_val_le_val] at hzx
          omega
        · rintro ⟨hzY, hsz⟩
          refine ⟨hzY, ?_⟩
          simp only [Fin.le_iff_val_le_val, s] at hsz
          simp only [Fin.le_iff_val_le_val]
          omega
      rw [hXfilter] at hXpart
      rw [hYfilter] at hYpart
      have hs := h s
      omega
    · have htop : ∀ z : Fin n, z ≤ x := by
        intro z
        simp only [Fin.le_iff_val_le_val]
        have hz := z.isLt
        omega
      simp only [Finset.filter_true_of_mem (fun z _ => htop z), hcard]
      exact le_rfl
  · intro h x
    by_cases hx : x.val = 0
    · have hbot : ∀ z : Fin n, x ≤ z := by
        intro z
        simp only [Fin.le_iff_val_le_val, hx, Nat.zero_le]
      simp only [Finset.filter_true_of_mem (fun z _ => hbot z), hcard]
      exact le_rfl
    · have hxpos : 0 < x.val := Nat.pos_of_ne_zero hx
      let p : Fin n := ⟨x.val - 1, by omega⟩
      have hXpart := Finset.card_filter_add_card_filter_not
        (s := X) (p := fun z => z ≤ p)
      have hYpart := Finset.card_filter_add_card_filter_not
        (s := Y) (p := fun z => z ≤ p)
      have hXfilter : (X.filter fun z => ¬z ≤ p) = X.filter fun z => x ≤ z := by
        ext z
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hzX, hzp⟩
          refine ⟨hzX, ?_⟩
          simp only [Fin.le_iff_val_le_val, p] at hzp
          simp only [Fin.le_iff_val_le_val]
          omega
        · rintro ⟨hzX, hxz⟩
          refine ⟨hzX, ?_⟩
          simp only [Fin.le_iff_val_le_val, p]
          simp only [Fin.le_iff_val_le_val] at hxz
          omega
      have hYfilter : (Y.filter fun z => ¬z ≤ p) = Y.filter fun z => x ≤ z := by
        ext z
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hzY, hzp⟩
          refine ⟨hzY, ?_⟩
          simp only [Fin.le_iff_val_le_val, p] at hzp
          simp only [Fin.le_iff_val_le_val]
          omega
        · rintro ⟨hzY, hxz⟩
          refine ⟨hzY, ?_⟩
          simp only [Fin.le_iff_val_le_val, p]
          simp only [Fin.le_iff_val_le_val] at hxz
          omega
      rw [hXfilter] at hXpart
      rw [hYfilter] at hYpart
      have hp := h p
      omega

/-- On equicardinal finsets, complement-and-reverse preserves (rather than reverses) Gale order. -/
theorem galeLE_dualSet_iff {n : ℕ} {X Y : Finset (Fin n)}
    (hcard : X.card = Y.card) :
    GaleLE X Y ↔ GaleLE (dualSet X) (dualSet Y) := by
  have hdualcard : (dualSet X).card = (dualSet Y).card := by
    simp [card_dualSet, hcard]
  rw [iff_comm, galeLE_iff_lowerCard_ge hdualcard]
  constructor
  · intro h t
    have ht := h (dualElem t)
    rw [card_filter_dualSet_le, card_filter_dualSet_le] at ht
    let S := Finset.univ.filter fun z : Fin n => t ≤ z
    have hSX : X ∩ S = X.filter fun z => t ≤ z := by
      ext z
      simp [S]
    have hSY : Y ∩ S = Y.filter fun z => t ≤ z := by
      ext z
      simp [S]
    have hXSle : (X ∩ S).card ≤ S.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hYSle : (Y ∩ S).card ≤ S.card :=
      Finset.card_le_card Finset.inter_subset_right
    simp only [dualElem_dualElem] at ht
    change (S \ Y).card ≤ (S \ X).card at ht
    rw [Finset.card_sdiff, Finset.card_sdiff, hSX, hSY] at ht
    rw [hSX] at hXSle
    rw [hSY] at hYSle
    omega
  · intro h x
    rw [card_filter_dualSet_le, card_filter_dualSet_le]
    let S := Finset.univ.filter fun z : Fin n => dualElem x ≤ z
    change (S \ Y).card ≤ (S \ X).card
    have hSX : X ∩ S = X.filter fun z => dualElem x ≤ z := by
      ext z
      simp [S]
    have hSY : Y ∩ S = Y.filter fun z => dualElem x ≤ z := by
      ext z
      simp [S]
    have hXSle : (X ∩ S).card ≤ S.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hYSle : (Y ∩ S).card ≤ S.card :=
      Finset.card_le_card Finset.inter_subset_right
    rw [Finset.card_sdiff, Finset.card_sdiff, hSX, hSY]
    rw [hSX] at hXSle
    rw [hSY] at hYSle
    have hx := h (dualElem x)
    omega

/-- Complement-and-reverse is a bijection from rank `k` subsets to rank `n - k` subsets. -/
def dualSetRankEquiv {n k : ℕ} (hk : k ≤ n) :
    {X : Finset (Fin n) // X.card = k} ≃
      {Y : Finset (Fin n) // Y.card = n - k} where
  toFun X := ⟨dualSet X, by simp [card_dualSet, X.prop]⟩
  invFun Y := ⟨dualSet Y, by rw [card_dualSet, Y.prop]; omega⟩
  left_inv X := by apply Subtype.ext; simp
  right_inv Y := by apply Subtype.ext; simp

/-- The dual family, obtained by applying `dualSet` memberwise. -/
def dualFamily {n : ℕ} (F : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  F.image dualSet

@[simp] theorem mem_dualFamily {n : ℕ} {F : Finset (Finset (Fin n))}
    {X : Finset (Fin n)} : X ∈ dualFamily F ↔ dualSet X ∈ F := by
  rw [dualFamily, Finset.mem_image]
  constructor
  · rintro ⟨Y, hY, hYX⟩
    have h := congrArg dualSet hYX
    simp only [dualSet_dualSet] at h
    exact h ▸ hY
  · intro hX
    exact ⟨dualSet X, hX, dualSet_dualSet X⟩

@[simp] theorem dualFamily_dualFamily {n : ℕ} (F : Finset (Finset (Fin n))) :
    dualFamily (dualFamily F) = F := by
  ext X
  simp

/-- Dualizing a shifted rank-`k` family gives a shifted rank-`n-k` family. -/
theorem isShifted_dualFamily {n k : ℕ} {F : Finset (Finset (Fin n))}
    (hF : IsShifted F k) : IsShifted (dualFamily F) (n - k) := by
  rw [isShifted_iff_isGaleIdeal] at hF ⊢
  rcases hF with ⟨hne, hcard, hdown⟩
  obtain ⟨X, hXF⟩ := hne
  have hk : k ≤ n := by
    have hXle := Finset.card_le_univ X
    rw [hcard X hXF] at hXle
    simpa using hXle
  refine ⟨⟨dualSet X, Finset.mem_image.mpr ⟨X, hXF, rfl⟩⟩, ?_, ?_⟩
  · intro Y hY
    have hDYcard := hcard (dualSet Y) (mem_dualFamily.mp hY)
    rw [card_dualSet] at hDYcard
    have hYle := Finset.card_le_univ Y
    have hYle' : Y.card ≤ n := by simpa only [Fintype.card_fin] using hYle
    omega
  · intro Y hY B hBcard hBY
    apply mem_dualFamily.mpr
    have hDYF : dualSet Y ∈ F := mem_dualFamily.mp hY
    have hDBcard : (dualSet B).card = k := by
      rw [card_dualSet, hBcard]
      omega
    have hYcard : Y.card = n - k := by
      have hDYcard := hcard (dualSet Y) hDYF
      rw [card_dualSet] at hDYcard
      have hYle := Finset.card_le_univ Y
      have hYle' : Y.card ≤ n := by simpa only [Fintype.card_fin] using hYle
      omega
    apply hdown (dualSet Y) hDYF (dualSet B) hDBcard
    exact (galeLE_dualSet_iff (hBcard.trans hYcard.symm)).mp hBY

/-- The vertex equivalence induced by complement-and-reverse. -/
def dualExchangeEquiv {n : ℕ} (F : Finset (Finset (Fin n))) :
    ExchangeV F ≃ ExchangeV (dualFamily F) where
  toFun X := ⟨dualSet X.val, Finset.mem_image.mpr ⟨X.val, X.prop, rfl⟩⟩
  invFun Y := ⟨dualSet Y.val, mem_dualFamily.mp Y.prop⟩
  left_inv X := by apply Subtype.ext; simp
  right_inv Y := by apply Subtype.ext; simp

/-- Complement-and-reverse is an isomorphism of exchange graphs. -/
def exchangeGraph_dualIso {n : ℕ} (F : Finset (Finset (Fin n))) :
    exchangeGraph F ≃g exchangeGraph (dualFamily F) where
  toEquiv := dualExchangeEquiv F
  map_rel_iff' := by
    intro A B
    simp only [exchangeGraph, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨hne, hrel⟩
      refine ⟨fun hAB => hne (congrArg (dualExchangeEquiv F) hAB), ?_⟩
      simpa [dualExchangeEquiv, card_dualSet_symmDiff] using hrel
    · rintro ⟨hne, hrel⟩
      refine ⟨fun hAB => hne ((dualExchangeEquiv F).injective hAB), ?_⟩
      simpa [dualExchangeEquiv, card_dualSet_symmDiff] using hrel

/-- The duality carries the layer containing `e` onto the layer avoiding `e*`. -/
theorem image_layerAbove_dualSet {n : ℕ} (F : Finset (Finset (Fin n))) (e : Fin n) :
    (layerAbove F e).image dualSet = layerBelow (dualFamily F) (dualElem e) := by
  ext X
  constructor
  · intro hX
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨hYF, heY⟩ := Finset.mem_filter.mp hY
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨Y, hYF, rfl⟩, ?_⟩
    simpa using heY
  · intro hX
    obtain ⟨hXF, heX⟩ := Finset.mem_filter.mp hX
    refine Finset.mem_image.mpr ⟨dualSet X, ?_, by simp⟩
    apply Finset.mem_filter.mpr
    exact ⟨mem_dualFamily.mp hXF, mem_dualSet.mpr heX⟩

/-- The duality carries the layer avoiding `e` onto the layer containing `e*`. -/
theorem image_layerBelow_dualSet {n : ℕ} (F : Finset (Finset (Fin n))) (e : Fin n) :
    (layerBelow F e).image dualSet = layerAbove (dualFamily F) (dualElem e) := by
  ext X
  constructor
  · intro hX
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨hYF, heY⟩ := Finset.mem_filter.mp hY
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨Y, hYF, rfl⟩, ?_⟩
    exact mem_dualSet.mpr (by simpa using heY)
  · intro hX
    obtain ⟨hXF, heX⟩ := Finset.mem_filter.mp hX
    refine Finset.mem_image.mpr ⟨dualSet X, ?_, by simp⟩
    apply Finset.mem_filter.mpr
    refine ⟨mem_dualFamily.mp hXF, ?_⟩
    intro heDX
    exact (mem_dualSet.mp heDX) heX

universe v

theorem isCliqueSum_map_iso {V : Type u} {W : Type v}
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H) {u v : V}
    (h : G.IsCliqueSum u v) : H.IsCliqueSum (φ u) (φ v) := by
  rcases h with ⟨huv, hu, hv, side, htrue, hfalse, hside⟩
  refine ⟨φ.injective.ne huv, ?_, ?_, side ∘ φ.symm, ?_, ?_, ?_⟩
  · intro w hw
    have hw' : φ.symm w ≠ u := by
      intro hwu
      apply hw
      calc
        w = φ (φ.symm w) := (φ.apply_symm_apply w).symm
        _ = φ u := congrArg φ hwu
    simpa using φ.map_rel_iff.mpr (hu (φ.symm w) hw')
  · intro w hw
    have hw' : φ.symm w ≠ v := by
      intro hwv
      apply hw
      calc
        w = φ (φ.symm w) := (φ.apply_symm_apply w).symm
        _ = φ v := congrArg φ hwv
    simpa using φ.map_rel_iff.mpr (hv (φ.symm w) hw')
  · obtain ⟨a, hau, hav, ha⟩ := htrue
    exact ⟨φ a, φ.injective.ne hau, φ.injective.ne hav, by simpa using ha⟩
  · obtain ⟨b, hbu, hbv, hb⟩ := hfalse
    exact ⟨φ b, φ.injective.ne hbu, φ.injective.ne hbv, by simpa using hb⟩
  · intro a b hau hav hbu hbv hab
    have hau' : φ.symm a ≠ u := by
      intro h
      apply hau
      calc
        a = φ (φ.symm a) := (φ.apply_symm_apply a).symm
        _ = φ u := congrArg φ h
    have hav' : φ.symm a ≠ v := by
      intro h
      apply hav
      calc
        a = φ (φ.symm a) := (φ.apply_symm_apply a).symm
        _ = φ v := congrArg φ h
    have hbu' : φ.symm b ≠ u := by
      intro h
      apply hbu
      calc
        b = φ (φ.symm b) := (φ.apply_symm_apply b).symm
        _ = φ u := congrArg φ h
    have hbv' : φ.symm b ≠ v := by
      intro h
      apply hbv
      calc
        b = φ (φ.symm b) := (φ.apply_symm_apply b).symm
        _ = φ v := congrArg φ h
    have hab' : φ.symm a ≠ φ.symm b := fun h => hab (φ.symm.injective h)
    rw [← φ.symm.map_rel_iff]
    exact hside (φ.symm a) (φ.symm b) hau' hav' hbu' hbv' hab'

theorem isCliqueSum_iso_iff {V : Type u} {W : Type v}
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H) {u v : V} :
    G.IsCliqueSum u v ↔ H.IsCliqueSum (φ u) (φ v) := by
  constructor
  · exact isCliqueSum_map_iso φ
  · intro h
    simpa using isCliqueSum_map_iso φ.symm h

/-- Clique-sum status, with its ordered universal pair, is preserved by the duality. -/
theorem isCliqueSum_dual_iff {n : ℕ} {F : Finset (Finset (Fin n))}
    (u v : ExchangeV F) :
    IsCliqueSum F u v ↔
      IsCliqueSum (dualFamily F) (dualExchangeEquiv F u) (dualExchangeEquiv F v) := by
  exact isCliqueSum_iso_iff (exchangeGraph_dualIso F)

/- **crossing lemma**, `STEP_LEMMA_2026-08-15.md` §0.

For a shifted `F`, distinct `A, B ∈ F` that are **not** the exception, and **every** `e ∈ A ∆ B`
oriented so `e ∈ A`, there is a valid crossing pair `(Y, X)`: `Y` in the containing layer, `X = Y − e +
ξ`
in the avoiding layer, with `Y` dodging the containing layer's forbidden set and `X` the avoiding layer's.

**The dodge is the FULL one of the paper's Theorem 7.11** — `Y ∉ S^e` and `X ∉ S^{¬e}`, not merely
`Y ≠ A` and `X ≠ B`.

STRENGTHENED 2026-08-16, and the previous weak form is recorded as a defect rather than quietly
replaced. Until today this theorem asserted only the endpoint half of the dodge, on the stated
grounds that "naming `Y_f` and `X_f` requires the layer-bottom translation table of §3 and that
table is index-bearing". **That reasoning was wrong in two ways.**

*It did not match the paper.* Manuscript Theorem 7.11 states `W ∉ S^e`, and `STEP_LEMMA` §§4–5
proves that. So the Lean was stating something strictly weaker than the theorem it names — the same
defect class as `HladikFink.lean` stating Theorem 3.3 about the wrong object.

*And the weak form is not enough to close the induction*, which is how it was found (Lean wave 6,
2026-08-16): `Y ≠ A` fixes distinct endpoints but does not stop `Y.erase e` from being the *other*
universal vertex of a clique-sum link, and there the induction hypothesis supplies no path at all.

**Naming `Y_f` never needed the table.** `S^e` has two members exactly when the containing layer's graph has the
clique-sum shape with `A` dominating, and then `S^e` is that dominating pair — so `Y ∉ S^e` is exactly
`Y ≠ A` together with "`{A, Y}` is not the containing layer's clique-sum universal pair", which is
`¬ IsCliqueSum (layerAbove F e) ..`. `IsCliqueSum` is purely graph-theoretic (it takes no
`IsShifted` hypothesis and mentions no index), so the dodge is index-free. The table is needed to
*prove* this lemma, not to state it — and that is the safe place for it, because Lean rejects a
wrong proof while nothing rejects a wrong statement.

The equivalence `Y ∉ S^e ⟺ Y ≠ A ∧ ¬ IsCliqueSum (layerAbove F e) A Y`: if the layer is a yFamily
with `A` dominating, `IsCliqueSum .. A Y` holds exactly when `Y` is the other dominating vertex,
i.e. `Y = Y_f`; otherwise it is false for every `Y`, matching `S^e = {A}`. The singleton layer is
the `card = 1` disjunct. This graph-theoretic reading of the barred sets is the one the manuscript
endorses (§7.9, "the condition on `L` may equally be read on `J(F¹)`"), and it is what both
computational seals of Theorem 7.11 actually computed — the lane's 409,416 + 40 and the decoupled
427,156, each with 0 violations.

Note the layers are used here only as **graphs**. `layerBelow F e` is NOT `IsShifted` over the
original ground — for `F = {{0},{1}}` and `e = 0` the avoiding layer `{{1}}` fails the decrement
`1 ↦ 0` — so a consumer that needs shiftedness must first transport to the punctured ground
`{x // x ≠ e}`. `IsCliqueSum` needs no such hypothesis. -/

/-! ## 7. Punctured-ground induction for `(Q*)`

The recursion measure is the cardinality of `F.biUnion id`, the finite ground actually used by
the family. After either layer is transported to `{x // x ≠ e}`, its used ground maps injectively
into `(F.biUnion id).erase e`; because `e` belongs to `A`, this makes both recursive measures
strictly smaller. -/

private abbrev Punctured (e : α) := {x : α // x ≠ e}

private def punctureSet (e : α) (X : Finset α) : Finset (Punctured e) :=
  X.subtype (fun x => x ≠ e)

private def liftPuncturedSet {e : α} (X : Finset (Punctured e)) : Finset α :=
  X.map (Function.Embedding.subtype _)

@[simp] private theorem punctureSet_liftPuncturedSet {e : α} (X : Finset (Punctured e)) :
    punctureSet e (liftPuncturedSet X) = X := by
  ext x
  simp [punctureSet, liftPuncturedSet, x.property]

private theorem liftPuncturedSet_punctureSet_of_notMem {e : α} {X : Finset α}
    (heX : e ∉ X) :
    liftPuncturedSet (punctureSet e X) = X := by
  apply Finset.subtype_map_of_mem
  intro x hx hxe
  exact heX (hxe ▸ hx)

private theorem liftPuncturedSet_punctureSet {e : α} (X : Finset α) :
    liftPuncturedSet (punctureSet e X) = X.erase e := by
  rw [show liftPuncturedSet (punctureSet e X) = X.filter (fun x => x ≠ e) by
    exact Finset.subtype_map (fun x => x ≠ e)]
  ext x
  simp [and_comm]

private def puncturedLower (F : Finset (Finset α)) (e : α) :
    Finset (Finset (Punctured e)) :=
  (layerBelow F e).image (punctureSet e)

private def puncturedLink (F : Finset (Finset α)) (e : α) :
    Finset (Finset (Punctured e)) :=
  (layerAbove F e).image (punctureSet e)

@[simp] private theorem mem_puncturedLower_iff {F : Finset (Finset α)} {e : α}
    {X : Finset (Punctured e)} :
    X ∈ puncturedLower F e ↔ liftPuncturedSet X ∈ F := by
  constructor
  · intro hX
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨hYF, heY⟩ := Finset.mem_filter.mp hY
    rw [liftPuncturedSet_punctureSet_of_notMem heY]
    exact hYF
  · intro hX
    apply Finset.mem_image.mpr
    refine ⟨liftPuncturedSet X, ?_, punctureSet_liftPuncturedSet X⟩
    exact Finset.mem_filter.mpr ⟨hX, by simp [liftPuncturedSet]⟩

@[simp] private theorem mem_puncturedLink_iff {F : Finset (Finset α)} {e : α}
    {X : Finset (Punctured e)} :
    X ∈ puncturedLink F e ↔ insert e (liftPuncturedSet X) ∈ F := by
  constructor
  · intro hX
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨hYF, heY⟩ := Finset.mem_filter.mp hY
    rw [liftPuncturedSet_punctureSet, Finset.insert_erase heY]
    exact hYF
  · intro hX
    apply Finset.mem_image.mpr
    refine ⟨insert e (liftPuncturedSet X), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hX, Finset.mem_insert_self _ _⟩
    · ext x
      simp [punctureSet, liftPuncturedSet, x.property]

private theorem isShifted_puncturedLower {F : Finset (Finset α)} {κ : ℕ} {e : α}
    (hF : IsShifted F κ) (hne : (layerBelow F e).Nonempty) :
    IsShifted (puncturedLower F e) κ := by
  rcases hF with ⟨_hFne, hcard, hshift⟩
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨X, hX⟩ := hne
    exact ⟨punctureSet e X, Finset.mem_image.mpr ⟨X, hX, rfl⟩⟩
  · intro X hX
    rw [mem_puncturedLower_iff] at hX
    have h := hcard (liftPuncturedSet X) hX
    simpa [liftPuncturedSet] using h
  · intro X hX i j hjX hij hiX
    rw [mem_puncturedLower_iff] at hX ⊢
    have hmem :
        insert i.val ((liftPuncturedSet X).erase j.val) ∈ F :=
      hshift (liftPuncturedSet X) hX i.val j.val
        (by simpa [liftPuncturedSet, j.property] using hjX) hij
        (by simpa [liftPuncturedSet, i.property] using hiX)
    convert hmem using 1
    ext x
    simp [liftPuncturedSet]

private theorem isShifted_puncturedLink {F : Finset (Finset α)} {κ : ℕ} {e : α}
    (hF : IsShifted F κ) (hne : (layerAbove F e).Nonempty) :
    IsShifted (puncturedLink F e) (κ - 1) := by
  rcases hF with ⟨_hFne, hcard, hshift⟩
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨X, hX⟩ := hne
    exact ⟨punctureSet e X, Finset.mem_image.mpr ⟨X, hX, rfl⟩⟩
  · intro X hX
    rw [mem_puncturedLink_iff] at hX
    have h := hcard (insert e (liftPuncturedSet X)) hX
    have he : e ∉ liftPuncturedSet X := by simp [liftPuncturedSet]
    rw [Finset.card_insert_of_notMem he] at h
    have hlift : (liftPuncturedSet X).card = X.card := by simp [liftPuncturedSet]
    omega
  · intro X hX i j hjX hij hiX
    rw [mem_puncturedLink_iff] at hX ⊢
    have hjLift : j.val ∈ liftPuncturedSet X := by
      simpa [liftPuncturedSet, j.property] using hjX
    have hiLift : i.val ∉ liftPuncturedSet X := by
      simpa [liftPuncturedSet, i.property] using hiX
    have hmem :
        insert i.val ((insert e (liftPuncturedSet X)).erase j.val) ∈ F :=
      hshift (insert e (liftPuncturedSet X)) hX i.val j.val
        (Finset.mem_insert_of_mem hjLift) hij (by simp [i.property, hiLift])
    have hlift :
        liftPuncturedSet (insert i (X.erase j)) =
          insert i.val ((liftPuncturedSet X).erase j.val) := by
      ext x
      simp [liftPuncturedSet, i.property, j.property]
    rw [hlift]
    rw [Finset.insert_comm e i.val]
    rw [Finset.erase_insert_of_ne (a := e) (b := j.val) (Ne.symm j.property)] at hmem
    exact hmem

/-! ### 7.1 Ordered coordinates on a finite ground

The manuscript's `[j]` is encoded as `initialSegment G j`, the `j` smallest elements of the
finite ground `G` in its inherited order.  Concretely, `groundRank G x` counts the elements of `G`
strictly below `x`, and the initial segment keeps exactly the elements of rank below `j`.  This
choice keeps every statement over the ambient arbitrary `LinearOrder α`; unlike a global switch to
`Fin G.card`, it also lets the layer formulas continue to name the original element `e` directly.

The three examples pin the 1-indexed reading used in the paper before any general table theorem:
the first three points of `{1,2,3,4,5}` are `{1,2,3}`; after deleting `2`, the first two are
`{1,3}`; after deleting `4`, the first two remain `{1,2}`. -/

/-- The zero-based order rank of `x` inside a finite ground `G`. -/
def groundRank (G : Finset α) (x : α) : ℕ :=
  (G.filter fun y => y < x).card

/-- `initialSegment G j` is the paper's `[j]`: the `j` smallest elements of `G`. -/
def initialSegment (G : Finset α) (j : ℕ) : Finset α :=
  G.filter fun x => groundRank G x < j

example : initialSegment ({1, 2, 3, 4, 5} : Finset ℕ) 3 = {1, 2, 3} := by
  decide

example : initialSegment (({1, 2, 3, 4, 5} : Finset ℕ).erase 2) 2 = {1, 3} := by
  decide

example : initialSegment (({1, 2, 3, 4, 5} : Finset ℕ).erase 4) 2 = {1, 2} := by
  decide

/-- The increasing enumeration of `G` has rank equal to its `Fin` index. -/
theorem groundRank_orderEmbOfFin (G : Finset α) (i : Fin G.card) :
    groundRank G (G.orderEmbOfFin rfl i) = i := by
  let emb := G.orderEmbOfFin rfl
  have heq : G.filter (fun y => y < emb i) = (Finset.Iio i).map emb.toEmbedding := by
    ext y
    constructor
    · intro hy
      have hyG : y ∈ G := (Finset.mem_filter.mp hy).1
      let q : Fin G.card := (G.orderIsoOfFin rfl).symm ⟨y, hyG⟩
      have hyq : emb q = y := by
        exact congrArg Subtype.val ((G.orderIsoOfFin rfl).apply_symm_apply ⟨y, hyG⟩)
      apply Finset.mem_map.mpr
      refine ⟨q, ?_, hyq⟩
      rw [Finset.mem_Iio]
      exact emb.lt_iff_lt.mp (hyq.trans_lt (Finset.mem_filter.mp hy).2)
    · intro hy
      obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hy
      exact Finset.mem_filter.mpr ⟨Finset.orderEmbOfFin_mem G rfl q,
        emb.lt_iff_lt.mpr (Finset.mem_Iio.mp hq)⟩
  rw [groundRank, heq, Finset.card_map, Fin.card_Iio]

/-- Membership in an initial segment, read through the increasing enumeration of its ground. -/
theorem initialSegment_orderEmbOfFin_mem_iff (G : Finset α) (j : ℕ)
    (i : Fin G.card) :
    G.orderEmbOfFin rfl i ∈ initialSegment G j ↔ (i : ℕ) < j := by
  simp [initialSegment, Finset.orderEmbOfFin_mem, groundRank_orderEmbOfFin]

/-- Every initial segment is contained in its ground. -/
theorem initialSegment_subset (G : Finset α) (j : ℕ) : initialSegment G j ⊆ G := by
  exact Finset.filter_subset _ _

/-- An initial segment whose requested length fits in the ground has that length. -/
theorem card_initialSegment_of_le {G : Finset α} {j : ℕ} (hj : j ≤ G.card) :
    (initialSegment G j).card = j := by
  let emb := G.orderEmbOfFin rfl
  have heq : initialSegment G j =
      (Finset.univ.filter fun i : Fin G.card => (i : ℕ) < j).map emb.toEmbedding := by
    ext x
    constructor
    · intro hx
      have hxG : x ∈ G := initialSegment_subset G j hx
      let i : Fin G.card := (G.orderIsoOfFin rfl).symm ⟨x, hxG⟩
      have hxi : emb i = x := by
        exact congrArg Subtype.val ((G.orderIsoOfFin rfl).apply_symm_apply ⟨x, hxG⟩)
      apply Finset.mem_map.mpr
      refine ⟨i, ?_, hxi⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (initialSegment_orderEmbOfFin_mem_iff G j i).mp (hxi ▸ hx)
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
      change emb i ∈ initialSegment G j
      rw [show emb = G.orderEmbOfFin rfl from rfl,
        initialSegment_orderEmbOfFin_mem_iff]
      exact (Finset.mem_filter.mp hi).2
  rw [heq, Finset.card_map]
  by_cases hjeq : j = G.card
  · subst j
    simp
  · have hjlt : j < G.card := lt_of_le_of_ne hj hjeq
    let b : Fin G.card := ⟨j, hjlt⟩
    have hfilter : (Finset.univ.filter fun i : Fin G.card => (i : ℕ) < j) =
        Finset.Iio b := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
      change ((i : ℕ) < j) ↔ (i : ℕ) < j
      rfl
    rw [hfilter, Fin.card_Iio]

/-- Initial segments are lower-closed inside their ground. -/
theorem initialSegment_lowerClosed {G : Finset α} {j : ℕ} :
    ∀ x ∈ initialSegment G j, ∀ y ∈ G, y < x → y ∈ initialSegment G j := by
  intro x hx y hyG hyx
  let i : Fin G.card := (G.orderIsoOfFin rfl).symm ⟨x, initialSegment_subset G j hx⟩
  let q : Fin G.card := (G.orderIsoOfFin rfl).symm ⟨y, hyG⟩
  have hxi : G.orderEmbOfFin rfl i = x := by
    exact congrArg Subtype.val
      ((G.orderIsoOfFin rfl).apply_symm_apply ⟨x, initialSegment_subset G j hx⟩)
  have hyq : G.orderEmbOfFin rfl q = y := by
    exact congrArg Subtype.val ((G.orderIsoOfFin rfl).apply_symm_apply ⟨y, hyG⟩)
  rw [← hyq, initialSegment_orderEmbOfFin_mem_iff]
  have hqi : q < i := (G.orderEmbOfFin rfl).lt_iff_lt.mp (hyq.trans_lt (hyx.trans_eq hxi.symm))
  exact (show (q : ℕ) < (i : ℕ) from hqi).trans
    ((initialSegment_orderEmbOfFin_mem_iff G j i).mp (hxi ▸ hx))

/-- The rank of a member of a finite ground is strictly below the ground cardinality. -/
theorem groundRank_lt_card_of_mem {G : Finset α} {x : α} (hx : x ∈ G) :
    groundRank G x < G.card := by
  rw [groundRank]
  apply Finset.card_lt_card
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro hback
  have : x ∈ G.filter fun y => y < x := hback hx
  exact (lt_irrefl x) (Finset.mem_filter.mp this).2

/-- A lower-closed `j`-subset of `G` is its initial segment of length `j`. -/
theorem initialSegment_eq_of_subset_card_lowerClosed {G X : Finset α} {j : ℕ}
    (hXG : X ⊆ G) (hcard : X.card = j)
    (hclosed : ∀ x ∈ X, ∀ y ∈ G, y < x → y ∈ X) :
    initialSegment G j = X := by
  have hjG : j ≤ G.card := by rw [← hcard]; exact Finset.card_le_card hXG
  apply Finset.Subset.antisymm
  · intro x hx
    by_contra hxX
    have hsub : X ⊆ initialSegment G j := by
      intro y hyX
      have hyG := hXG hyX
      by_cases hyx : y < x
      · exact initialSegment_lowerClosed (G := G) (j := j) x hx y hyG hyx
      · have hxy : x < y := lt_of_le_of_ne (le_of_not_gt hyx)
          (Ne.symm (fun h => hxX (h ▸ hyX)))
        exact (hxX (hclosed y hyX x (initialSegment_subset G j hx) hxy)).elim
    have hle : (initialSegment G j).card ≤ X.card := by
      rw [card_initialSegment_of_le hjG, hcard]
    have heq := Finset.eq_of_subset_of_card_le hsub hle
    exact hxX (heq ▸ hx)
  · intro x hxX
    have hcardInit := card_initialSegment_of_le hjG
    by_contra hxInit
    have hsub : initialSegment G j ⊆ X := by
      intro y hy
      have hyG := initialSegment_subset G j hy
      by_cases hyx : y < x
      · exact hclosed x hxX y hyG hyx
      · have hxy : x < y := lt_of_le_of_ne (le_of_not_gt hyx)
          (Ne.symm (fun h => hxInit (h ▸ hy)))
        exact (hxInit (initialSegment_lowerClosed (G := G) (j := j)
          y hy x (hXG hxX) hxy)).elim
    have hle : X.card ≤ (initialSegment G j).card := by rw [hcardInit, hcard]
    have heq := Finset.eq_of_subset_of_card_le hsub hle
    exact hxInit (heq.symm ▸ hxX)

/-- The finite ground actually used by a family. -/
def usedGround (F : Finset (Finset α)) : Finset α := F.biUnion id

/-- **FAITHFULNESS.** For a shifted family the used ground is downward closed in the ambient
order, which is what lets the manuscript print `initialSegment (usedGround F) j` as `[j]`. -/
theorem usedGround_downwardClosed {F : Finset (Finset α)} {κ : ℕ} (hF : IsShifted F κ)
    {e : α} (he : e ∈ usedGround F) {x : α} (hxe : x < e) : x ∈ usedGround F := by
  rw [usedGround, Finset.mem_biUnion] at he ⊢
  obtain ⟨W, hWF, heW⟩ := he
  by_cases hxW : x ∈ W
  · exact ⟨W, hWF, hxW⟩
  · have hshift := hF.2.2 W hWF x e heW hxe hxW
    exact ⟨insert x (W.erase e), hshift, Finset.mem_insert_self x _⟩

/-- Each `initialSegment` of a downward-closed ground is itself downward closed, so the manuscript's
`[j]` and `initialSegment (usedGround F) j` denote the same set. -/
theorem initialSegment_downwardClosed {G : Finset α} (hG : ∀ e ∈ G, ∀ x : α, x < e → x ∈ G)
    {j : ℕ} {y : α} (hy : y ∈ initialSegment G j) {x : α} (hxy : x < y) :
    x ∈ initialSegment G j := by
  have hyG : y ∈ G := initialSegment_subset G j hy
  exact initialSegment_lowerClosed (G := G) (j := j) y hy x (hG y hyG x hxy) hxy

/-- The canonical second `k`-set: the first `k-1` points and the point in position `k+1`. -/
def secondInitialSegment (G : Finset α) (k : ℕ) : Finset α :=
  initialSegment G (k - 1) ∪ (initialSegment G (k + 1) \ initialSegment G k)

/-- The (normally singleton) set in the paper's 1-indexed position `p`. -/
def groundPosition (G : Finset α) (p : ℕ) : Finset α :=
  initialSegment G p \ initialSegment G (p - 1)

/-- Initial segments are monotone in their requested length. -/
theorem initialSegment_mono (G : Finset α) : Monotone (initialSegment G) := by
  intro a b hab x hx
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
    (Finset.mem_filter.mp hx).2.trans_le hab⟩

/-- The intersection of the canonical bottom pair is the first `k-1` ground points. -/
theorem initialSegment_inter_secondInitialSegment (G : Finset α) (k : ℕ) :
    initialSegment G k ∩ secondInitialSegment G k = initialSegment G (k - 1) := by
  have hsub : initialSegment G (k - 1) ⊆ initialSegment G k :=
    initialSegment_mono G (Nat.sub_le k 1)
  ext x
  simp only [secondInitialSegment, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro ⟨hxk, hxsmall | ⟨_, hxnot⟩⟩
    · exact hxsmall
    · exact (hxnot hxk).elim
  · intro hxsmall
    exact ⟨hsub hxsmall, Or.inl hxsmall⟩

/-- The union of the canonical bottom pair is the first `k+1` ground points. -/
theorem initialSegment_union_secondInitialSegment (G : Finset α) (k : ℕ) :
    initialSegment G k ∪ secondInitialSegment G k = initialSegment G (k + 1) := by
  have hsubK : initialSegment G k ⊆ initialSegment G (k + 1) :=
    initialSegment_mono G (by omega)
  have hsubPred : initialSegment G (k - 1) ⊆ initialSegment G (k + 1) :=
    initialSegment_mono G (by omega)
  ext x
  simp only [secondInitialSegment, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (hxk | hxsmall | ⟨hxsucc, _⟩)
    · exact hsubK hxk
    · exact hsubPred hxsmall
    · exact hxsucc
  · intro hxsucc
    by_cases hxk : x ∈ initialSegment G k
    · exact Or.inl hxk
    · exact Or.inr (Or.inr ⟨hxsucc, hxk⟩)

/-- Outer parameters are downward closed: replacing the exceptional point by a smaller point
outside the fixed core stays in a shifted family. -/
theorem outerArm_down_closed {F : Finset (Finset α)} {k : ℕ}
    (hF : IsShifted F k) {C : Finset α} {a a' : α}
    (haF : insert a C ∈ F) (haC : a ∉ C) (ha'C : a' ∉ C) (haa' : a' < a) :
    insert a' C ∈ F := by
  have haMem : a ∈ insert a C := Finset.mem_insert_self _ _
  have ha'NotMem : a' ∉ insert a C := by simp [haa'.ne, ha'C]
  have hshift := hF.2.2 (insert a C) haF a' a haMem haa' ha'NotMem
  simpa [Finset.erase_insert, haC] using hshift

/-- Inner parameters are upward closed.  If deleting `i` gives a family member and `i < i'`,
then shiftedness replaces the retained `i'` by `i`, hence gives the member deleting `i'`.
This is the direction-sensitive half of arm contiguity. -/
theorem innerArm_up_closed {F : Finset (Finset α)} {k : ℕ}
    (hF : IsShifted F k) {U : Finset α} {i i' : α}
    (hiF : U.erase i ∈ F) (hiU : i ∈ U) (hi'U : i' ∈ U) (hii' : i < i') :
    U.erase i' ∈ F := by
  have hi'Mem : i' ∈ U.erase i := Finset.mem_erase.mpr ⟨hii'.ne', hi'U⟩
  have hiNotMem : i ∉ U.erase i := Finset.notMem_erase _ _
  have hshift := hF.2.2 (U.erase i) hiF i i' hi'Mem hii' hiNotMem
  have hset : insert i ((U.erase i).erase i') = U.erase i' := by
    ext x
    by_cases hxi : x = i
    · subst x
      simp [hii'.ne, hiU]
    · simp [hxi]
  rwa [hset] at hshift

/-- At `k = 3`, deleting the larger index `2` is Gale-below deleting the smaller index `1`:
`{1,3,4} ≼ {2,3,4}`. -/
example : GaleLE ({1, 3, 4} : Finset ℕ) {2, 3, 4} := by
  exact galeLE_singleDecrement (X := ({2, 3, 4} : Finset ℕ)) (i := 1) (j := 2)
    (by decide) (by omega) (by decide)

/-- At `k = 4`, deleting `4` is Gale-below deleting `2` from `[5]`:
`{1,2,3,5} ≼ {1,3,4,5}`. -/
example : GaleLE ({1, 2, 3, 5} : Finset ℕ) {1, 3, 4, 5} := by
  have h := galeLE_singleDecrement (X := ({1, 3, 4, 5} : Finset ℕ)) (i := 2) (j := 4)
    (by decide) (by omega) (by decide)
  rw [show insert 2 (({1, 3, 4, 5} : Finset ℕ).erase 4) = {1, 2, 3, 5} by decide] at h
  exact h

/-- If a deleted point lies in `[j]`, the first `j` surviving points are `[j+1] \ {e}`. -/
theorem initialSegment_erase_eq_erase_succ_of_mem {G : Finset α} {e : α} {j : ℕ}
    (hcard : j + 1 ≤ G.card) (he : e ∈ initialSegment G j) :
    initialSegment (G.erase e) j = (initialSegment G (j + 1)).erase e := by
  apply initialSegment_eq_of_subset_card_lowerClosed
  · intro x hx
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1,
      initialSegment_subset G (j + 1) (Finset.mem_of_mem_erase hx)⟩
  · rw [Finset.card_erase_of_mem ((initialSegment_mono G (Nat.le_succ j)) he),
      card_initialSegment_of_le hcard]
    omega
  · intro x hx y hyG hyx
    apply Finset.mem_erase.mpr
    refine ⟨(Finset.mem_erase.mp hyG).1, ?_⟩
    exact initialSegment_lowerClosed (G := G) (j := j + 1) x
      (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hyG) hyx

/-- If a deleted point lies outside `[j]`, the first `j` points do not change. -/
theorem initialSegment_erase_eq_self_of_notMem {G : Finset α} {e : α} {j : ℕ}
    (hcard : j ≤ G.card) (he : e ∉ initialSegment G j) :
    initialSegment (G.erase e) j = initialSegment G j := by
  apply initialSegment_eq_of_subset_card_lowerClosed
  · intro x hx
    exact Finset.mem_erase.mpr ⟨fun hxe => he (hxe ▸ hx), initialSegment_subset G j hx⟩
  · exact card_initialSegment_of_le hcard
  · intro x hx y hyG hyx
    exact initialSegment_lowerClosed (G := G) (j := j) x hx y
      (Finset.mem_of_mem_erase hyG) hyx

/-- Deleting the unique point of `[j]` outside `[j-1]` leaves `[j-1]`. -/
theorem initialSegment_erase_eq_prev_of_top {G : Finset α} {e : α} {j : ℕ}
    (hj : 1 ≤ j) (hcard : j ≤ G.card)
    (he : e ∈ initialSegment G j) (hePrev : e ∉ initialSegment G (j - 1)) :
    (initialSegment G j).erase e = initialSegment G (j - 1) := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    apply Finset.mem_erase.mpr
    refine ⟨fun hxe => hePrev (hxe ▸ hx), ?_⟩
    exact initialSegment_mono G (Nat.sub_le j 1) hx
  · rw [Finset.card_erase_of_mem he, card_initialSegment_of_le hcard,
      card_initialSegment_of_le (by omega : j - 1 ≤ G.card)]

/-- Adjoining the unique next point to `[j]` gives `[j+1]`. -/
theorem initialSegment_insert_eq_succ_of_top {G : Finset α} {e : α} {j : ℕ}
    (hcard : j + 1 ≤ G.card)
    (he : e ∈ initialSegment G (j + 1)) (hePrev : e ∉ initialSegment G j) :
    insert e (initialSegment G j) = initialSegment G (j + 1) := by
  have herase : (initialSegment G (j + 1)).erase e = initialSegment G j := by
    simpa using initialSegment_erase_eq_prev_of_top
      (G := G) (e := e) (j := j + 1) (by omega) hcard he hePrev
  rw [← herase]
  exact Finset.insert_erase he

/-- Uniform form of the first `j-1` points after deleting any point of `[j]`. -/
theorem initialSegment_erase_pred_eq_erase_of_mem {G : Finset α} {e : α} {j : ℕ}
    (hj : 1 ≤ j) (hcard : j ≤ G.card) (he : e ∈ initialSegment G j) :
    initialSegment (G.erase e) (j - 1) = (initialSegment G j).erase e := by
  by_cases hePrev : e ∈ initialSegment G (j - 1)
  · simpa [show j - 1 + 1 = j by omega] using
      initialSegment_erase_eq_erase_succ_of_mem (G := G) (e := e)
        (j := j - 1) (by omega) hePrev
  · rw [initialSegment_erase_eq_self_of_notMem (by omega) hePrev,
      ← initialSegment_erase_eq_prev_of_top hj hcard he hePrev]

/-- If `e` is the point in position `p`, then `groundPosition G p = {e}`. -/
theorem groundPosition_eq_singleton_of_top {G : Finset α} {e : α} {p : ℕ}
    (hp : 1 ≤ p) (hcard : p ≤ G.card)
    (he : e ∈ initialSegment G p) (hePrev : e ∉ initialSegment G (p - 1)) :
    groundPosition G p = {e} := by
  rw [groundPosition]
  have hins : insert e (initialSegment G (p - 1)) = initialSegment G p := by
    have hsucc : p - 1 + 1 = p := by omega
    have he' : e ∈ initialSegment G (p - 1 + 1) := by rwa [hsucc]
    simpa [hsucc] using initialSegment_insert_eq_succ_of_top (G := G) (e := e)
      (j := p - 1) (by omega) he' hePrev
  rw [← hins]
  ext x
  simp [hePrev]

/-- Removing the penultimate position from `[k]` gives the canonical second `(k-1)`-set. -/
theorem secondInitialSegment_pred_eq_initial_sdiff_position_pred
    (G : Finset α) {k : ℕ} (hk : 2 ≤ k) :
    secondInitialSegment G (k - 1) =
      initialSegment G k \ groundPosition G (k - 1) := by
  rw [secondInitialSegment, groundPosition]
  have hsubsub : k - 1 - 1 = k - 2 := by omega
  have hsubadd : k - 1 + 1 = k := by omega
  rw [hsubsub, hsubadd]
  have hsub₁ : initialSegment G (k - 2) ⊆ initialSegment G (k - 1) :=
    initialSegment_mono G (by omega)
  have hsub₂ : initialSegment G (k - 1) ⊆ initialSegment G k :=
    initialSegment_mono G (by omega)
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff]
  have h₁ : x ∈ initialSegment G (k - 2) → x ∈ initialSegment G (k - 1) :=
    fun h => hsub₁ (a := x) h
  have h₂ : x ∈ initialSegment G (k - 1) → x ∈ initialSegment G k :=
    fun h => hsub₂ (a := x) h
  tauto

/-- Coordinate expansion of `[k+1] \ {k-1}` into the surviving three blocks. -/
theorem initialSegment_succ_sdiff_position_pred (G : Finset α) {k : ℕ} (hk : 2 ≤ k) :
    initialSegment G (k + 1) \ groundPosition G (k - 1) =
      (initialSegment G (k - 2) ∪ groundPosition G k) ∪ groundPosition G (k + 1) := by
  simp only [groundPosition]
  have hsubsub : k - 1 - 1 = k - 2 := by omega
  have hsuccsub : k + 1 - 1 = k := by omega
  rw [hsubsub, hsuccsub]
  have hsub₁ : initialSegment G (k - 2) ⊆ initialSegment G (k - 1) :=
    initialSegment_mono G (by omega)
  have hsub₂ : initialSegment G (k - 1) ⊆ initialSegment G k :=
    initialSegment_mono G (by omega)
  have hsub₃ : initialSegment G k ⊆ initialSegment G (k + 1) :=
    initialSegment_mono G (by omega)
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff]
  have h₁ : x ∈ initialSegment G (k - 2) → x ∈ initialSegment G (k - 1) :=
    fun h => hsub₁ (a := x) h
  have h₂ : x ∈ initialSegment G (k - 1) → x ∈ initialSegment G k :=
    fun h => hsub₂ (a := x) h
  have h₃ : x ∈ initialSegment G k → x ∈ initialSegment G (k + 1) :=
    fun h => hsub₃ (a := x) h
  tauto

/-- The second initial set after deleting a point in `[k]`: the first column of the `m₂(F⁰)` row. -/
theorem secondInitialSegment_erase_of_mem_initial {G : Finset α} {e : α} {k : ℕ}
    (hk : 1 ≤ k) (hcard : k + 2 ≤ G.card) (he : e ∈ initialSegment G k) :
    secondInitialSegment (G.erase e) k =
      (initialSegment G k).erase e ∪ groundPosition G (k + 2) := by
  have hfirst : initialSegment (G.erase e) (k - 1) =
      (initialSegment G k).erase e := by
    by_cases he' : e ∈ initialSegment G (k - 1)
    · simpa [show k - 1 + 1 = k by omega] using
        initialSegment_erase_eq_erase_succ_of_mem (G := G) (e := e)
          (j := k - 1) (by omega) he'
    · rw [initialSegment_erase_eq_self_of_notMem (by omega) he',
        ← initialSegment_erase_eq_prev_of_top hk (by omega) he he']
  rw [secondInitialSegment, groundPosition]
  rw [hfirst]
  rw [initialSegment_erase_eq_erase_succ_of_mem (by omega) he]
  rw [initialSegment_erase_eq_erase_succ_of_mem (by omega)
    ((initialSegment_mono G (by omega : k ≤ k + 1)) he)]
  have hk1 : k + 1 + 1 = k + 2 := by omega
  have hk2 : k + 2 - 1 = k + 1 := by omega
  rw [hk1, hk2]
  ext x
  by_cases hxe : x = e
  · subst x
    simp [he, (initialSegment_mono G (by omega : k ≤ k + 1)) he]
  · simp [hxe]

/-- The second initial set when `e` is the point in position `k+1`: the middle `m₂(F⁰)` column. -/
theorem secondInitialSegment_erase_of_top_initial {G : Finset α} {e : α} {k : ℕ}
    (hk : 1 ≤ k) (hcard : k + 2 ≤ G.card)
    (heTop : e ∈ initialSegment G (k + 1)) (he : e ∉ initialSegment G k) :
    secondInitialSegment (G.erase e) k =
      initialSegment G (k - 1) ∪ groundPosition G (k + 2) := by
  rw [secondInitialSegment, groundPosition]
  rw [initialSegment_erase_eq_self_of_notMem (by omega)
    (fun hem => he ((initialSegment_mono G (by omega : k - 1 ≤ k)) hem))]
  rw [initialSegment_erase_eq_self_of_notMem (by omega) he]
  rw [initialSegment_erase_eq_erase_succ_of_mem (by omega) heTop]
  have hInsert : insert e (initialSegment G k) = initialSegment G (k + 1) :=
    initialSegment_insert_eq_succ_of_top (by omega) heTop he
  have hkm1 : k + 1 + 1 = k + 2 := by omega
  have hk2 : k + 2 - 1 = k + 1 := by omega
  rw [hkm1, hk2, ← hInsert]
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
  tauto

/-- Deleting beyond `[k+1]` leaves the canonical second `k`-set unchanged. -/
theorem secondInitialSegment_erase_of_notMem_initialSucc {G : Finset α} {e : α} {k : ℕ}
    (hk : 1 ≤ k) (hcard : k + 1 ≤ G.card) (he : e ∉ initialSegment G (k + 1)) :
    secondInitialSegment (G.erase e) k = secondInitialSegment G k := by
  rw [secondInitialSegment, secondInitialSegment]
  rw [initialSegment_erase_eq_self_of_notMem (by omega)
    (fun hem => he ((initialSegment_mono G (by omega : k - 1 ≤ k + 1)) hem))]
  rw [initialSegment_erase_eq_self_of_notMem (by omega)
    (fun hem => he ((initialSegment_mono G (by omega : k ≤ k + 1)) hem))]
  rw [initialSegment_erase_eq_self_of_notMem hcard he]

/-- A Gale-least member of a shifted family is the initial `k`-set of its used ground. -/
theorem galeLeast_eq_initialSegment {F : Finset (Finset α)} {k : ℕ}
    (hF : IsShifted F k) {m : Finset α} (hm : IsGaleLeast F m) :
    m = initialSegment (usedGround F) k := by
  symm
  apply initialSegment_eq_of_subset_card_lowerClosed
  · intro x hx
    rw [usedGround, Finset.mem_biUnion]
    exact ⟨m, hm.1, hx⟩
  · exact hF.2.1 m hm.1
  · intro x hx y _hyG hyx
    by_contra hym
    have hD : insert y (m.erase x) ∈ F := hF.2.2 m hm.1 y x hx hyx hym
    have hle := toColex_le_of_galeLE (hm.2 _ hD)
    have hlt := toColex_singleDecrement_lt hx hyx hym
    exact (not_lt_of_ge hle) hlt

/-- Gale-least members of shifted families are lower-closed in the whole ambient order. -/
theorem galeLeast_lowerClosed {F : Finset (Finset α)} {k : ℕ}
    (hF : IsShifted F k) {m : Finset α} (hm : IsGaleLeast F m)
    {x y : α} (hx : x ∈ m) (hyx : y < x) : y ∈ m := by
  by_contra hym
  have hD : insert y (m.erase x) ∈ F := hF.2.2 m hm.1 y x hx hyx hym
  have hle := toColex_le_of_galeLE (hm.2 _ hD)
  exact ((not_lt_of_ge hle) (toColex_singleDecrement_lt hx hyx hym)).elim

/-- A Gale-second member is the first `k-1` points together with the point in position `k+1`. -/
theorem galeSecondLeast_eq_secondInitialSegment {F : Finset (Finset α)} {k : ℕ}
    (hF : IsShifted F k) (h2 : 2 ≤ F.card) {m₁ m₂ : Finset α}
    (hm₁ : IsGaleLeast F m₁) (hm₂ : IsGaleSecondLeast F m₁ m₂) :
    m₂ = secondInitialSegment (usedGround F) k := by
  obtain ⟨b₁, b₂, hb₁, hb₂, i, j, hib₁, hib₂, hjb₂, hjb₁, hij,
      hb₂repr, himax, hjmin⟩ := exists_gale_bottom_pair_with_boundary hF h2
  have hm₁b₁ : m₁ = b₁ := isGaleLeast_unique hm₁ hb₁
  have hm₂b₂ : m₂ = b₂ := by
    apply isGaleSecondLeast_unique (m := m₁) hm₂
    rw [hm₁b₁]
    exact hb₂
  rw [hm₂b₂, secondInitialSegment]
  let G := usedGround F
  have hb₁init : b₁ = initialSegment G k := galeLeast_eq_initialSegment hF hb₁
  have hb₁card : b₁.card = k := hF.2.1 b₁ hb₁.1
  have hkpos : 0 < k := by rw [← hb₁card]; exact Finset.card_pos.mpr ⟨i, hib₁⟩
  have hb₁G : b₁ ⊆ G := by
    intro x hx
    simp only [G, usedGround, Finset.mem_biUnion]
    exact ⟨b₁, hb₁.1, hx⟩
  have hjG : j ∈ G := by
    simp only [G, usedGround, Finset.mem_biUnion]
    exact ⟨b₂, hb₂.1, hjb₂⟩
  have heraseInit : b₁.erase i = initialSegment G (k - 1) := by
    symm
    apply initialSegment_eq_of_subset_card_lowerClosed
    · exact (Finset.erase_subset _ _).trans hb₁G
    · rw [Finset.card_erase_of_mem hib₁, hb₁card]
    · intro x hx y hyG hyx
      have hxb₁ := Finset.mem_of_mem_erase hx
      have hyb₁ : y ∈ b₁ := by
        have hyi : y < i := hyx.trans_le (himax x hxb₁)
        exact hjmin y (hyi.trans hij)
      apply Finset.mem_erase.mpr
      exact ⟨(hyx.trans_le (himax x hxb₁)).ne, hyb₁⟩
  have hinsertInit : insert j b₁ = initialSegment G (k + 1) := by
    symm
    apply initialSegment_eq_of_subset_card_lowerClosed
    · exact Finset.insert_subset hjG hb₁G
    · rw [Finset.card_insert_of_notMem hjb₁, hb₁card]
    · intro x hx y hyG hyx
      rcases Finset.mem_insert.mp hx with rfl | hxb₁
      · exact Finset.mem_insert.mpr (Or.inr (hjmin y hyx))
      · by_cases hyb₁ : y ∈ b₁
        · exact Finset.mem_insert.mpr (Or.inr hyb₁)
        · have hD : insert y (b₁.erase x) ∈ F := hF.2.2 b₁ hb₁.1 y x hxb₁ hyx hyb₁
          have hle := toColex_le_of_galeLE (hb₁.2 _ hD)
          exact ((not_lt_of_ge hle) (toColex_singleDecrement_lt hxb₁ hyx hyb₁)).elim
  rw [← heraseInit, ← hinsertInit, ← hb₁init, hb₂repr]
  ext x
  simp [hjb₁]

/-- A Gale-least member on the punctured type, lifted back to `α`, is the initial segment of the
ambient ground with `e` removed.  The containment hypothesis is the reusable interface shared by
the avoiding layer and the link. -/
theorem punctured_galeLeast_lift_eq_initialSegment
    {e : α} {P : Finset (Finset (Punctured e))} {G : Finset α} {k : ℕ}
    (hP : IsShifted P k) (hPG : ∀ X ∈ P, liftPuncturedSet X ⊆ G)
    {m : Finset (Punctured e)} (hm : IsGaleLeast P m) :
    liftPuncturedSet m = initialSegment (G.erase e) k := by
  symm
  apply initialSegment_eq_of_subset_card_lowerClosed
  · intro x hx
    obtain ⟨xp, hxp, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_erase.mpr ⟨xp.property,
      hPG m hm.1 (Finset.mem_map.mpr ⟨xp, hxp, rfl⟩)⟩
  · simpa [liftPuncturedSet] using hP.2.1 m hm.1
  · intro x hx y hyG hyx
    obtain ⟨xp, hxp, rfl⟩ := Finset.mem_map.mp hx
    have hye : y ≠ e := (Finset.mem_erase.mp hyG).1
    let yp : Punctured e := ⟨y, hye⟩
    have hyp : yp ∈ m := galeLeast_lowerClosed hP hm hxp hyx
    exact Finset.mem_map.mpr ⟨yp, hyp, rfl⟩

/-- The analogous lifted formula for a Gale-second member on a punctured ground. -/
theorem punctured_galeSecondLeast_lift_eq_secondInitialSegment
    {e : α} {P : Finset (Finset (Punctured e))} {G : Finset α} {k : ℕ}
    (hP : IsShifted P k) (h2 : 2 ≤ P.card)
    (hPG : ∀ X ∈ P, liftPuncturedSet X ⊆ G)
    {m₁ m₂ : Finset (Punctured e)}
    (hm₁ : IsGaleLeast P m₁) (hm₂ : IsGaleSecondLeast P m₁ m₂) :
    liftPuncturedSet m₂ = secondInitialSegment (G.erase e) k := by
  obtain ⟨b₁, b₂, hb₁, hb₂, i, j, hib₁, hib₂, hjb₂, hjb₁, hij,
      hb₂repr, himax, hjmin⟩ := exists_gale_bottom_pair_with_boundary hP h2
  have hm₁b₁ : m₁ = b₁ := isGaleLeast_unique hm₁ hb₁
  have hm₂b₂ : m₂ = b₂ := by
    apply isGaleSecondLeast_unique (m := m₁) hm₂
    rw [hm₁b₁]
    exact hb₂
  rw [hm₂b₂, secondInitialSegment]
  let H := G.erase e
  have hb₁init : liftPuncturedSet b₁ = initialSegment H k :=
    punctured_galeLeast_lift_eq_initialSegment hP hPG hb₁
  have hb₁card : b₁.card = k := hP.2.1 b₁ hb₁.1
  have hkpos : 0 < k := by rw [← hb₁card]; exact Finset.card_pos.mpr ⟨i, hib₁⟩
  have hb₁H : liftPuncturedSet b₁ ⊆ H := by
    intro x hx
    obtain ⟨xp, hxp, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_erase.mpr ⟨xp.property,
      hPG b₁ hb₁.1 (Finset.mem_map.mpr ⟨xp, hxp, rfl⟩)⟩
  have hjH : j.val ∈ H := by
    have hjLift : j.val ∈ liftPuncturedSet b₂ :=
      Finset.mem_map.mpr ⟨j, hjb₂, rfl⟩
    exact Finset.mem_erase.mpr ⟨j.property, hPG b₂ hb₂.1 hjLift⟩
  have heraseLift :
      liftPuncturedSet (b₁.erase i) = (liftPuncturedSet b₁).erase i.val := by
    ext x
    simp [liftPuncturedSet]
  have hinsertLift :
      liftPuncturedSet (insert j b₁) = insert j.val (liftPuncturedSet b₁) := by
    ext x
    simp [liftPuncturedSet]
  have hjNotLift : j.val ∉ liftPuncturedSet b₁ := by
    intro hj
    obtain ⟨q, hqb₁, hqj⟩ := Finset.mem_map.mp hj
    apply hjb₁
    have hq : q = j := Subtype.ext hqj
    rwa [← hq]
  have heraseInit : (liftPuncturedSet b₁).erase i.val = initialSegment H (k - 1) := by
    symm
    apply initialSegment_eq_of_subset_card_lowerClosed
    · exact (Finset.erase_subset _ _).trans hb₁H
    · have hiLift : i.val ∈ liftPuncturedSet b₁ :=
        Finset.mem_map.mpr ⟨i, hib₁, rfl⟩
      rw [Finset.card_erase_of_mem hiLift]
      simp [liftPuncturedSet, hb₁card]
    · intro x hx y hyH hyx
      have hxLift := Finset.mem_of_mem_erase hx
      obtain ⟨xp, hxb₁, hxpval⟩ := Finset.mem_map.mp hxLift
      change xp.val = x at hxpval
      let yp : Punctured e := ⟨y, (Finset.mem_erase.mp hyH).1⟩
      have hyp : yp ∈ b₁ := galeLeast_lowerClosed hP hb₁ hxb₁
        (show y < xp.val by rw [hxpval]; exact hyx)
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_map.mpr ⟨yp, hyp, rfl⟩⟩
      have hxi : xp.val ≤ i.val := himax _ hxb₁
      exact ((show y < xp.val by rw [hxpval]; exact hyx).trans_le hxi).ne
  have hinsertInit :
      insert j.val (liftPuncturedSet b₁) = initialSegment H (k + 1) := by
    symm
    apply initialSegment_eq_of_subset_card_lowerClosed
    · exact Finset.insert_subset hjH hb₁H
    · rw [Finset.card_insert_of_notMem hjNotLift]
      simp [liftPuncturedSet, hb₁card]
    · intro x hx y hyH hyx
      rcases Finset.mem_insert.mp hx with rfl | hxb₁Lift
      · let yp : Punctured e := ⟨y, (Finset.mem_erase.mp hyH).1⟩
        have hyp : yp ∈ b₁ := hjmin yp hyx
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_map.mpr ⟨yp, hyp, rfl⟩))
      · obtain ⟨xp, hxp, hxpval⟩ := Finset.mem_map.mp hxb₁Lift
        change xp.val = x at hxpval
        let yp : Punctured e := ⟨y, (Finset.mem_erase.mp hyH).1⟩
        have hyp : yp ∈ b₁ := galeLeast_lowerClosed hP hb₁ hxp
          (show y < xp.val by rw [hxpval]; exact hyx)
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_map.mpr ⟨yp, hyp, rfl⟩))
  have hinsertEraseLift :
      liftPuncturedSet (insert j (b₁.erase i)) =
        insert j.val (liftPuncturedSet (b₁.erase i)) := by
    ext x
    simp [liftPuncturedSet]
  rw [← heraseInit, ← hinsertInit, ← hb₁init, ← heraseLift, hb₂repr,
    hinsertEraseLift]
  ext x
  simp [hjNotLift, or_comm]

/-! ### 7.2 The avoiding-layer rows -/

/-- The `m₁(F⁰)` row before splitting according to the position of `e`. -/
theorem layerBelow_galeLeast_lift_eq_initialSegment_erase
    {F : Finset (Finset α)} {k : ℕ} {e : α}
    (hF : IsShifted F k) (hne : (layerBelow F e).Nonempty)
    {m : Finset (Punctured e)} (hm : IsGaleLeast (puncturedLower F e) m) :
    liftPuncturedSet m = initialSegment ((usedGround F).erase e) k := by
  refine punctured_galeLeast_lift_eq_initialSegment
    (isShifted_puncturedLower hF hne) ?_ hm
  intro X hX x hx
  rw [usedGround, Finset.mem_biUnion]
  exact ⟨liftPuncturedSet X, mem_puncturedLower_iff.mp hX, hx⟩

/-- The `m₂(F⁰)` row before splitting according to the position of `e`. -/
theorem layerBelow_galeSecondLeast_lift_eq_secondInitialSegment_erase
    {F : Finset (Finset α)} {k : ℕ} {e : α}
    (hF : IsShifted F k) (hne : (layerBelow F e).Nonempty)
    (h2 : 2 ≤ (puncturedLower F e).card)
    {m₁ m₂ : Finset (Punctured e)}
    (hm₁ : IsGaleLeast (puncturedLower F e) m₁)
    (hm₂ : IsGaleSecondLeast (puncturedLower F e) m₁ m₂) :
    liftPuncturedSet m₂ = secondInitialSegment ((usedGround F).erase e) k := by
  refine punctured_galeSecondLeast_lift_eq_secondInitialSegment
    (isShifted_puncturedLower hF hne) h2 ?_ hm₁ hm₂
  intro X hX x hx
  rw [usedGround, Finset.mem_biUnion]
  exact ⟨liftPuncturedSet X, mem_puncturedLower_iff.mp hX, hx⟩

/-- First `m₁(F⁰)` column: if `e ≤ k`, then `m₁(F⁰) = [k+1] \ {e}`. -/
theorem layerBelow_m1_of_mem_initial
    {F : Finset (Finset α)} {k : ℕ} {e : α}
    (hF : IsShifted F k) (hne : (layerBelow F e).Nonempty)
    (hcard : k + 1 ≤ (usedGround F).card) (he : e ∈ initialSegment (usedGround F) k)
    {m : Finset (Punctured e)} (hm : IsGaleLeast (puncturedLower F e) m) :
    liftPuncturedSet m = (initialSegment (usedGround F) (k + 1)).erase e := by
  rw [layerBelow_galeLeast_lift_eq_initialSegment_erase hF hne hm]
  exact initialSegment_erase_eq_erase_succ_of_mem hcard he

/-- Middle `m₁(F⁰)` column: if `e = k+1`, then `m₁(F⁰) = [k]`. -/
theorem layerBelow_m1_of_top_initial
    {F : Finset (Finset α)} {k : ℕ} {e : α}
    (hF : IsShifted F k) (hne : (layerBelow F e).Nonempty)
    (hcard : k ≤ (usedGround F).card) (he : e ∉ initialSegment (usedGround F) k)
    {m : Finset (Punctured e)} (hm : IsGaleLeast (puncturedLower F e) m) :
    liftPuncturedSet m = initialSegment (usedGround F) k := by
  rw [layerBelow_galeLeast_lift_eq_initialSegment_erase hF hne hm]
  exact initialSegment_erase_eq_self_of_notMem hcard he

/-- Last `m₁(F⁰)` column: the same `[k]` formula holds whenever `e ≥ k+2`. -/
theorem layerBelow_m1_of_notMem_initialSucc
    {F : Finset (Finset α)} {k : ℕ} {e : α}
    (hF : IsShifted F k) (hne : (layerBelow F e).Nonempty)
    (hcard : k ≤ (usedGround F).card)
    (he : e ∉ initialSegment (usedGround F) (k + 1))
    {m : Finset (Punctured e)} (hm : IsGaleLeast (puncturedLower F e) m) :
    liftPuncturedSet m = initialSegment (usedGround F) k := by
  apply layerBelow_m1_of_top_initial hF hne hcard
  · exact fun hek => he (initialSegment_mono (usedGround F) (by omega) hek)
  · exact hm

/-- First `m₂(F⁰)` column: `([k] \ {e}) ∪ {k+2}` in the encoded notation. -/
theorem layerBelow_m2_of_mem_initial
    {F : Finset (Finset α)} {k : ℕ} {e : α}
    (hF : IsShifted F k) (hne : (layerBelow F e).Nonempty)
    (h2 : 2 ≤ (puncturedLower F e).card) (hk : 1 ≤ k)
    (hcard : k + 2 ≤ (usedGround F).card) (he : e ∈ initialSegment (usedGround F) k)
    {m₁ m₂ : Finset (Punctured e)}
    (hm₁ : IsGaleLeast (puncturedLower F e) m₁)
    (hm₂ : IsGaleSecondLeast (puncturedLower F e) m₁ m₂) :
    liftPuncturedSet m₂ =
      (initialSegment (usedGround F) k).erase e ∪ groundPosition (usedGround F) (k + 2) := by
  rw [layerBelow_galeSecondLeast_lift_eq_secondInitialSegment_erase hF hne h2 hm₁ hm₂]
  exact secondInitialSegment_erase_of_mem_initial hk hcard he

/-- Middle `m₂(F⁰)` column: `[k-1] ∪ {k+2}` when `e = k+1`. -/
theorem layerBelow_m2_of_top_initial
    {F : Finset (Finset α)} {k : ℕ} {e : α}
    (hF : IsShifted F k) (hne : (layerBelow F e).Nonempty)
    (h2 : 2 ≤ (puncturedLower F e).card) (hk : 1 ≤ k)
    (hcard : k + 2 ≤ (usedGround F).card)
    (heTop : e ∈ initialSegment (usedGround F) (k + 1))
    (he : e ∉ initialSegment (usedGround F) k)
    {m₁ m₂ : Finset (Punctured e)}
    (hm₁ : IsGaleLeast (puncturedLower F e) m₁)
    (hm₂ : IsGaleSecondLeast (puncturedLower F e) m₁ m₂) :
    liftPuncturedSet m₂ =
      initialSegment (usedGround F) (k - 1) ∪ groundPosition (usedGround F) (k + 2) := by
  rw [layerBelow_galeSecondLeast_lift_eq_secondInitialSegment_erase hF hne h2 hm₁ hm₂]
  exact secondInitialSegment_erase_of_top_initial hk hcard heTop he

/-- Last `m₂(F⁰)` column: deleting beyond `[k+1]` leaves the original canonical `m₂`. -/
theorem layerBelow_m2_of_notMem_initialSucc
    {F : Finset (Finset α)} {k : ℕ} {e : α}
    (hF : IsShifted F k) (hne : (layerBelow F e).Nonempty)
    (h2 : 2 ≤ (puncturedLower F e).card) (hk : 1 ≤ k)
    (hcard : k + 1 ≤ (usedGround F).card)
    (he : e ∉ initialSegment (usedGround F) (k + 1))
    {m₁ m₂ : Finset (Punctured e)}
    (hm₁ : IsGaleLeast (puncturedLower F e) m₁)
    (hm₂ : IsGaleSecondLeast (puncturedLower F e) m₁ m₂) :
    liftPuncturedSet m₂ = secondInitialSegment (usedGround F) k := by
  rw [layerBelow_galeSecondLeast_lift_eq_secondInitialSegment_erase hF hne h2 hm₁ hm₂]
  exact secondInitialSegment_erase_of_notMem_initialSucc hk hcard he

/-! ### 7.3 The lifted link rows -/

/-- The lifted `m₁(L)` formula before the positional split. -/
theorem link_galeLeast_lift_eq_initialSegment_erase
    {F : Finset (Finset α)} {k : ℕ} {e : α}
    (hF : IsShifted F k) (hne : (layerAbove F e).Nonempty)
    {m : Finset (Punctured e)} (hm : IsGaleLeast (puncturedLink F e) m) :
    insert e (liftPuncturedSet m) =
      insert e (initialSegment ((usedGround F).erase e) (k - 1)) := by
  congr 1
  refine punctured_galeLeast_lift_eq_initialSegment
    (isShifted_puncturedLink hF hne) ?_ hm
  intro X hX x hx
  rw [usedGround, Finset.mem_biUnion]
  exact ⟨insert e (liftPuncturedSet X), mem_puncturedLink_iff.mp hX,
    Finset.mem_insert_of_mem hx⟩

/-- The lifted `m₂(L)` formula before the positional split. -/
theorem link_galeSecondLeast_lift_eq_secondInitialSegment_erase
    {F : Finset (Finset α)} {k : ℕ} {e : α}
    (hF : IsShifted F k) (hne : (layerAbove F e).Nonempty)
    (h2 : 2 ≤ (puncturedLink F e).card)
    {m₁ m₂ : Finset (Punctured e)}
    (hm₁ : IsGaleLeast (puncturedLink F e) m₁)
    (hm₂ : IsGaleSecondLeast (puncturedLink F e) m₁ m₂) :
    insert e (liftPuncturedSet m₂) =
      insert e (secondInitialSegment ((usedGround F).erase e) (k - 1)) := by
  congr 1
  refine punctured_galeSecondLeast_lift_eq_secondInitialSegment
    (isShifted_puncturedLink hF hne) h2 ?_ hm₁ hm₂
  intro X hX x hx
  rw [usedGround, Finset.mem_biUnion]
  exact ⟨insert e (liftPuncturedSet X), mem_puncturedLink_iff.mp hX,
    Finset.mem_insert_of_mem hx⟩

/-- First `μ₁` column: if `e ≤ k`, the lifted least link member is `[k]`. -/
theorem link_mu1_of_mem_initial
    {F : Finset (Finset α)} {k : ℕ} {e : α}
    (hF : IsShifted F k) (hne : (layerAbove F e).Nonempty)
    (hk : 1 ≤ k) (hcard : k ≤ (usedGround F).card)
    (he : e ∈ initialSegment (usedGround F) k)
    {m : Finset (Punctured e)} (hm : IsGaleLeast (puncturedLink F e) m) :
    insert e (liftPuncturedSet m) = initialSegment (usedGround F) k := by
  rw [link_galeLeast_lift_eq_initialSegment_erase hF hne hm]
  rw [initialSegment_erase_pred_eq_erase_of_mem hk hcard he]
  exact Finset.insert_erase he

/-- Middle `μ₁` column: if `e = k+1`, the lift is the original canonical `m₂`. -/
theorem link_mu1_of_top_initialSucc
    {F : Finset (Finset α)} {k : ℕ} {e : α}
    (hF : IsShifted F k) (hne : (layerAbove F e).Nonempty)
    (hk : 1 ≤ k) (hcard : k + 1 ≤ (usedGround F).card)
    (heTop : e ∈ initialSegment (usedGround F) (k + 1))
    (he : e ∉ initialSegment (usedGround F) k)
    {m : Finset (Punctured e)} (hm : IsGaleLeast (puncturedLink F e) m) :
    insert e (liftPuncturedSet m) = secondInitialSegment (usedGround F) k := by
  rw [link_galeLeast_lift_eq_initialSegment_erase hF hne hm]
  rw [initialSegment_erase_eq_self_of_notMem (by omega)
    (fun hem => he (initialSegment_mono (usedGround F) (by omega) hem))]
  rw [secondInitialSegment]
  change insert e (initialSegment (usedGround F) (k - 1)) =
    initialSegment (usedGround F) (k - 1) ∪ groundPosition (usedGround F) (k + 1)
  rw [groundPosition_eq_singleton_of_top (by omega) hcard heTop he]
  ext x
  simp [or_comm]

/-- Last `μ₁` column: for `e ≥ k+2`, the lift is `[k-1] ∪ {e}`. -/
theorem link_mu1_of_notMem_initialSucc
    {F : Finset (Finset α)} {k : ℕ} {e : α}
    (hF : IsShifted F k) (hne : (layerAbove F e).Nonempty)
    (hk : 1 ≤ k) (hcard : k - 1 ≤ (usedGround F).card)
    (he : e ∉ initialSegment (usedGround F) (k + 1))
    {m : Finset (Punctured e)} (hm : IsGaleLeast (puncturedLink F e) m) :
    insert e (liftPuncturedSet m) =
      insert e (initialSegment (usedGround F) (k - 1)) := by
  rw [link_galeLeast_lift_eq_initialSegment_erase hF hne hm]
  rw [initialSegment_erase_eq_self_of_notMem hcard
    (fun hem => he (initialSegment_mono (usedGround F) (by omega) hem))]

/-- First `μ₂` subcolumn: for `e ≤ k-1`, the lifted second link member is the original
canonical `m₂`. -/
theorem link_mu2_of_mem_initialPred
    {F : Finset (Finset α)} {k : ℕ} {e : α}
    (hF : IsShifted F k) (hne : (layerAbove F e).Nonempty)
    (h2 : 2 ≤ (puncturedLink F e).card) (hk : 2 ≤ k)
    (hcard : k + 1 ≤ (usedGround F).card)
    (he : e ∈ initialSegment (usedGround F) (k - 1))
    {m₁ m₂ : Finset (Punctured e)}
    (hm₁ : IsGaleLeast (puncturedLink F e) m₁)
    (hm₂ : IsGaleSecondLeast (puncturedLink F e) m₁ m₂) :
    insert e (liftPuncturedSet m₂) = secondInitialSegment (usedGround F) k := by
  rw [link_galeSecondLeast_lift_eq_secondInitialSegment_erase hF hne h2 hm₁ hm₂]
  rw [secondInitialSegment_erase_of_mem_initial (by omega) (by omega) he]
  have harith : k - 1 + 2 = k + 1 := by omega
  rw [harith]
  rw [secondInitialSegment]
  change insert e ((initialSegment (usedGround F) (k - 1)).erase e ∪
      groundPosition (usedGround F) (k + 1)) =
    initialSegment (usedGround F) (k - 1) ∪ groundPosition (usedGround F) (k + 1)
  ext x
  by_cases hxe : x = e
  · subst x
    simp [he]
  · simp [hxe]

/-- `μ₂` at `e = k`: `[k+1] \ {k-1}`. -/
theorem link_mu2_of_top_initial
    {F : Finset (Finset α)} {k : ℕ} {e : α}
    (hF : IsShifted F k) (hne : (layerAbove F e).Nonempty)
    (h2 : 2 ≤ (puncturedLink F e).card) (hk : 2 ≤ k)
    (hcard : k + 1 ≤ (usedGround F).card)
    (heTop : e ∈ initialSegment (usedGround F) k)
    (he : e ∉ initialSegment (usedGround F) (k - 1))
    {m₁ m₂ : Finset (Punctured e)}
    (hm₁ : IsGaleLeast (puncturedLink F e) m₁)
    (hm₂ : IsGaleSecondLeast (puncturedLink F e) m₁ m₂) :
    insert e (liftPuncturedSet m₂) =
      initialSegment (usedGround F) (k + 1) \ groundPosition (usedGround F) (k - 1) := by
  rw [link_galeSecondLeast_lift_eq_secondInitialSegment_erase hF hne h2 hm₁ hm₂]
  have harith : k - 1 + 1 = k := by omega
  have heTop' : e ∈ initialSegment (usedGround F) (k - 1 + 1) := by rwa [harith]
  rw [secondInitialSegment_erase_of_top_initial (by omega) (by omega) heTop' he]
  have hplus : k - 1 + 2 = k + 1 := by omega
  have hminus : k - 1 - 1 = k - 2 := by omega
  rw [hplus, hminus]
  rw [initialSegment_succ_sdiff_position_pred (usedGround F) hk]
  rw [groundPosition_eq_singleton_of_top (by omega) (by omega) heTop he]
  ext x
  simp [or_assoc, or_left_comm, or_comm]

/-- `μ₂` at `e = k+1`: the same `[k+1] \ {k-1}` formula. -/
theorem link_mu2_of_top_initialSucc
    {F : Finset (Finset α)} {k : ℕ} {e : α}
    (hF : IsShifted F k) (hne : (layerAbove F e).Nonempty)
    (h2 : 2 ≤ (puncturedLink F e).card) (hk : 2 ≤ k)
    (hcard : k + 1 ≤ (usedGround F).card)
    (heTop : e ∈ initialSegment (usedGround F) (k + 1))
    (he : e ∉ initialSegment (usedGround F) k)
    {m₁ m₂ : Finset (Punctured e)}
    (hm₁ : IsGaleLeast (puncturedLink F e) m₁)
    (hm₂ : IsGaleSecondLeast (puncturedLink F e) m₁ m₂) :
    insert e (liftPuncturedSet m₂) =
      initialSegment (usedGround F) (k + 1) \ groundPosition (usedGround F) (k - 1) := by
  rw [link_galeSecondLeast_lift_eq_secondInitialSegment_erase hF hne h2 hm₁ hm₂]
  have harith : k - 1 + 1 = k := by omega
  have he' : e ∉ initialSegment (usedGround F) (k - 1 + 1) := by rwa [harith]
  rw [secondInitialSegment_erase_of_notMem_initialSucc (by omega) (by omega) he']
  rw [secondInitialSegment_pred_eq_initial_sdiff_position_pred (usedGround F) hk]
  have hInsert : insert e (initialSegment (usedGround F) k) =
      initialSegment (usedGround F) (k + 1) :=
    initialSegment_insert_eq_succ_of_top hcard heTop he
  have hnotPos : e ∉ groundPosition (usedGround F) (k - 1) := by
    intro hep
    have hem : e ∈ initialSegment (usedGround F) (k - 1) :=
      (Finset.mem_sdiff.mp hep).1
    exact he (initialSegment_mono (usedGround F) (by omega) hem)
  rw [← hInsert]
  ext x
  by_cases hxe : x = e
  · subst x
    simp [hnotPos]
  · simp [hxe]

/-- Last `μ₂` column: `([k] \ {k-1}) ∪ {e}` for `e ≥ k+2`. -/
theorem link_mu2_of_notMem_initialSucc
    {F : Finset (Finset α)} {k : ℕ} {e : α}
    (hF : IsShifted F k) (hne : (layerAbove F e).Nonempty)
    (h2 : 2 ≤ (puncturedLink F e).card) (hk : 2 ≤ k)
    (hcard : k ≤ (usedGround F).card)
    (he : e ∉ initialSegment (usedGround F) (k + 1))
    {m₁ m₂ : Finset (Punctured e)}
    (hm₁ : IsGaleLeast (puncturedLink F e) m₁)
    (hm₂ : IsGaleSecondLeast (puncturedLink F e) m₁ m₂) :
    insert e (liftPuncturedSet m₂) =
      insert e (initialSegment (usedGround F) k \
        groundPosition (usedGround F) (k - 1)) := by
  rw [link_galeSecondLeast_lift_eq_secondInitialSegment_erase hF hne h2 hm₁ hm₂]
  have harith : k - 1 + 1 = k := by omega
  have hcard' : k - 1 + 1 ≤ (usedGround F).card := by rwa [harith]
  have he' : e ∉ initialSegment (usedGround F) (k - 1 + 1) := by
    rw [harith]
    exact fun hem => he (initialSegment_mono (usedGround F) (by omega) hem)
  rw [secondInitialSegment_erase_of_notMem_initialSucc (by omega) hcard' he']
  rw [secondInitialSegment_pred_eq_initial_sdiff_position_pred (usedGround F) hk]

/-! ### 7.4 The index-bearing half of Lemma 3 -/

/-- A clique-sum of rank `k` uses at least `k+1` ground points: its two distinct universal
`k`-sets already have a union of that size. -/
theorem cliqueSum_usedGround_card {F : Finset (Finset α)} {k : ℕ}
    (hF : IsShifted F k) {u v : ExchangeV F} (hbad : IsCliqueSum F u v) :
    k + 1 ≤ (usedGround F).card := by
  have huv : u ≠ v := hbad.1
  have huvVal : u.val ≠ v.val := fun h => huv (Subtype.ext h)
  have hcardEq : u.val.card = v.val.card :=
    (hF.2.1 u.val u.prop).trans (hF.2.1 v.val v.prop).symm
  have hdiff : (u.val \ v.val).Nonempty := Finset.sdiff_nonempty.mpr (by
    intro hsub
    exact huvVal (Finset.eq_of_subset_of_card_le hsub hcardEq.ge))
  obtain ⟨x, hx⟩ := hdiff
  have hproper : v.val ⊂ u.val ∪ v.val := by
    refine ⟨Finset.subset_union_right, ?_⟩
    intro hback
    exact (Finset.mem_sdiff.mp hx).2
      (hback (Finset.mem_union_left _ (Finset.mem_sdiff.mp hx).1))
  have hUnionGround : u.val ∪ v.val ⊆ usedGround F := by
    intro y hy
    rw [usedGround, Finset.mem_biUnion]
    rcases Finset.mem_union.mp hy with hyu | hyv
    · exact ⟨u.val, u.prop, hyu⟩
    · exact ⟨v.val, v.prop, hyv⟩
  have hlt := Finset.card_lt_card hproper
  have hle := Finset.card_le_card hUnionGround
  rw [hF.2.1 v.val v.prop] at hlt
  omega

/-- The unordered universal pair of a clique-sum is the canonical coordinate pair
`([k], [k-1] ∪ {k+1})` on its used ground. -/
theorem cliqueSum_universalPair_coordinates {F : Finset (Finset α)} {k : ℕ}
    (hF : IsShifted F k) {u v : ExchangeV F} (hbad : IsCliqueSum F u v) :
    (u.val = initialSegment (usedGround F) k ∧
        v.val = secondInitialSegment (usedGround F) k) ∨
      (v.val = initialSegment (usedGround F) k ∧
        u.val = secondInitialSegment (usedGround F) k) := by
  have huv : u ≠ v := hbad.1
  have huvVal : u.val ≠ v.val := fun h => huv (Subtype.ext h)
  have hpairsub : {u.val, v.val} ⊆ F := by
    intro Y hY
    rcases Finset.mem_insert.mp hY with rfl | hY
    · exact u.prop
    · have hYv : Y = v.val := by simpa using hY
      exact hYv ▸ v.prop
  have htwo : 2 ≤ F.card := by
    have hle := Finset.card_le_card hpairsub
    simpa [Finset.card_pair huvVal] using hle
  rcases lemma2_universalPair_is_galeLeast hF hbad with
    ⟨huLeast, hvSecond⟩ | ⟨hvLeast, huSecond⟩
  · exact Or.inl ⟨galeLeast_eq_initialSegment hF huLeast,
      galeSecondLeast_eq_secondInitialSegment hF htwo huLeast hvSecond⟩
  · exact Or.inr ⟨galeLeast_eq_initialSegment hF hvLeast,
      galeSecondLeast_eq_secondInitialSegment hF htwo hvLeast huSecond⟩

/-- Coordinate form of every non-universal member of a clique-sum.  The first alternative is a
outer member with its exceptional point strictly beyond `[k+1]`; the second is an inner member
obtained by deleting a point of `[k-1]`. -/
theorem lemma3_arm_member_coordinates {F : Finset (Finset α)} {k : ℕ}
    (hF : IsShifted F k) {u v : ExchangeV F} (hbad : IsCliqueSum F u v) :
    ∀ X : ExchangeV F, X ≠ u → X ≠ v →
      (∃ a ∈ usedGround F,
          a ∉ initialSegment (usedGround F) (k + 1) ∧
          X.val = insert a (initialSegment (usedGround F) (k - 1))) ∨
      (∃ i ∈ initialSegment (usedGround F) (k - 1),
          X.val = (initialSegment (usedGround F) (k + 1)).erase i) := by
  let G := usedGround F
  have hpairCoord :
      (u.val = initialSegment G k ∧ v.val = secondInitialSegment G k) ∨
      (v.val = initialSegment G k ∧ u.val = secondInitialSegment G k) := by
    exact cliqueSum_universalPair_coordinates hF hbad
  have hUVinter : u.val ∩ v.val = initialSegment G (k - 1) := by
    rcases hpairCoord with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · rw [hu, hv, initialSegment_inter_secondInitialSegment]
    · rw [hu, hv, Finset.inter_comm, initialSegment_inter_secondInitialSegment]
  have hUVunion : u.val ∪ v.val = initialSegment G (k + 1) := by
    rcases hpairCoord with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · rw [hu, hv, initialSegment_union_secondInitialSegment]
    · rw [hu, hv, Finset.union_comm, initialSegment_union_secondInitialSegment]
  have hGcard : k + 1 ≤ G.card := cliqueSum_usedGround_card hF hbad
  have hCcard : (initialSegment G (k - 1)).card = k - 1 :=
    card_initialSegment_of_le (by omega)
  have hUcard : (initialSegment G (k + 1)).card = k + 1 :=
    card_initialSegment_of_le hGcard
  have hCsubU : initialSegment G (k - 1) ⊆ initialSegment G (k + 1) :=
    initialSegment_mono G (by omega)
  intro X hXu hXv
  have harms := lemma3_two_arms hF hbad X hXu hXv
  rw [hUVinter, hUVunion] at harms
  rcases prop_xor_of_ne harms with ⟨hP, hnotQ⟩ | ⟨hnotP, hQ⟩
  · obtain ⟨a, haX, haU⟩ := Finset.not_subset.mp hnotQ
    have haG : a ∈ G := by
      change a ∈ usedGround F
      rw [usedGround, Finset.mem_biUnion]
      exact ⟨X.val, X.prop, haX⟩
    have haC : a ∉ initialSegment G (k - 1) := fun ha => haU (hCsubU ha)
    have hsub : insert a (initialSegment G (k - 1)) ⊆ X.val :=
      Finset.insert_subset haX hP
    have hrepr : X.val = insert a (initialSegment G (k - 1)) := by
      symm
      apply Finset.eq_of_subset_of_card_le hsub
      rw [Finset.card_insert_of_notMem haC, hCcard, hF.2.1 X.val X.prop]
      have hk : 0 < k := by
        rw [← hF.2.1 X.val X.prop]
        exact Finset.card_pos.mpr ⟨a, haX⟩
      omega
    exact Or.inl ⟨a, haG, haU, hrepr⟩
  · obtain ⟨i, hiC, hiX⟩ := Finset.not_subset.mp hnotP
    have hiU : i ∈ initialSegment G (k + 1) := hCsubU hiC
    have hrepr : X.val = (initialSegment G (k + 1)).erase i := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        exact Finset.mem_erase.mpr ⟨fun hxi => hiX (hxi ▸ hx), hQ hx⟩
      · rw [Finset.card_erase_of_mem hiU, hUcard, hF.2.1 X.val X.prop]
        omega
    exact Or.inr ⟨i, hiC, hrepr⟩

/-- Both coordinate arms of a clique-sum are nonempty.  The two witnesses supplied by the
clique-sum's Boolean sides cannot have the same coordinate form, because members with a common
codimension-one core (or upper cover) are adjacent whereas opposite sides are not. -/
theorem lemma3_coordinate_arms_nonempty {F : Finset (Finset α)} {k : ℕ}
    (hF : IsShifted F k) {u v : ExchangeV F} (hbad : IsCliqueSum F u v) :
    (∃ a ∈ usedGround F,
        a ∉ initialSegment (usedGround F) (k + 1) ∧
        insert a (initialSegment (usedGround F) (k - 1)) ∈ F) ∧
      (∃ i ∈ initialSegment (usedGround F) (k - 1),
        (initialSegment (usedGround F) (k + 1)).erase i ∈ F) := by
  let G := usedGround F
  have hbadCopy := hbad
  rcases hbad with ⟨_huv, _huUniv, _hvUniv, side, htrue, hfalse, hside⟩
  obtain ⟨T, hTu, hTv, hTtrue⟩ := htrue
  obtain ⟨R, hRu, hRv, hRfalse⟩ := hfalse
  have hTR : T ≠ R := by
    intro hEq
    have hsides := congrArg side hEq
    have : true = false := hTtrue.symm.trans (hsides.trans hRfalse)
    simp at this
  have hnotAdj : ¬(exchangeGraph F).Adj T R := by
    intro hAdj
    have hsides := (hside T R hTu hTv hRu hRv hTR).1 hAdj
    have : true = false := hTtrue.symm.trans (hsides.trans hRfalse)
    simp at this
  have hCsubU : initialSegment G (k - 1) ⊆ initialSegment G (k + 1) :=
    initialSegment_mono G (by omega)
  have hTcoord := lemma3_arm_member_coordinates hF hbadCopy T hTu hTv
  have hRcoord := lemma3_arm_member_coordinates hF hbadCopy R hRu hRv
  rcases hTcoord with hTP | hTQ <;> rcases hRcoord with hRP | hRQ
  · obtain ⟨a, haG, haU, hTrepr⟩ := hTP
    obtain ⟨b, hbG, hbU, hRrepr⟩ := hRP
    change a ∈ G at haG
    change a ∉ initialSegment G (k + 1) at haU
    change T.val = insert a (initialSegment G (k - 1)) at hTrepr
    change b ∈ G at hbG
    change b ∉ initialSegment G (k + 1) at hbU
    change R.val = insert b (initialSegment G (k - 1)) at hRrepr
    have haC : a ∉ initialSegment G (k - 1) := fun ha => haU (hCsubU ha)
    have hbC : b ∉ initialSegment G (k - 1) := fun hb => hbU (hCsubU hb)
    have hAdj : (exchangeGraph F).Adj T R :=
      exchangeGraph_adj_of_common_lowerCover
        (C := initialSegment G (k - 1)) T.prop R.prop
        (by rw [hTrepr]; exact Finset.subset_insert _ _)
        (by rw [hRrepr]; exact Finset.subset_insert _ _)
        (by rw [hTrepr, Finset.card_insert_of_notMem haC])
        (by rw [hRrepr, Finset.card_insert_of_notMem hbC])
        (fun h => hTR (Subtype.ext h))
    exact (hnotAdj hAdj).elim
  · obtain ⟨a, haG, haU, hTrepr⟩ := hTP
    obtain ⟨i, hiC, hRrepr⟩ := hRQ
    refine ⟨⟨a, haG, haU, ?_⟩, ⟨i, hiC, ?_⟩⟩
    · rw [← hTrepr]
      exact T.prop
    · rw [← hRrepr]
      exact R.prop
  · obtain ⟨i, hiC, hTrepr⟩ := hTQ
    obtain ⟨a, haG, haU, hRrepr⟩ := hRP
    refine ⟨⟨a, haG, haU, ?_⟩, ⟨i, hiC, ?_⟩⟩
    · rw [← hRrepr]
      exact R.prop
    · rw [← hTrepr]
      exact T.prop
  · obtain ⟨i, hiC, hTrepr⟩ := hTQ
    obtain ⟨j, hjC, hRrepr⟩ := hRQ
    change i ∈ initialSegment G (k - 1) at hiC
    change T.val = (initialSegment G (k + 1)).erase i at hTrepr
    change j ∈ initialSegment G (k - 1) at hjC
    change R.val = (initialSegment G (k + 1)).erase j at hRrepr
    have hiU : i ∈ initialSegment G (k + 1) := hCsubU hiC
    have hjU : j ∈ initialSegment G (k + 1) := hCsubU hjC
    have hAdj : (exchangeGraph F).Adj T R :=
      exchangeGraph_adj_of_common_upperCover
        (U := initialSegment G (k + 1)) T.prop R.prop
        (by rw [hTrepr]; exact Finset.erase_subset _ _)
        (by rw [hRrepr]; exact Finset.erase_subset _ _)
        (by
          rw [hTrepr, Finset.card_erase_of_mem hiU]
          have hpos : 0 < (initialSegment G (k + 1)).card :=
            Finset.card_pos.mpr ⟨i, hiU⟩
          omega)
        (by
          rw [hRrepr, Finset.card_erase_of_mem hjU]
          have hpos : 0 < (initialSegment G (k + 1)).card :=
            Finset.card_pos.mpr ⟨j, hjU⟩
          omega)
        (fun h => hTR (Subtype.ext h))
    exact (hnotAdj hAdj).elim

/-- The outer arm of the coordinate yFamily with upper endpoint `r`.  The endpoint is an element of
the ordered ground; on `[n]`, the source condition says exactly `k+2 ≤ a ≤ r`. -/
def yOuterArm (G : Finset α) (k : ℕ) (r : α) : Finset (Finset α) :=
  (G.filter fun a => a ∉ initialSegment G (k + 1) ∧ a ≤ r).image
    fun a => insert a (initialSegment G (k - 1))

/-- The inner arm of the coordinate yFamily with lower endpoint `s`.  On `[n]`, the source
condition says exactly `s ≤ i ≤ k-1`. -/
def yInnerArm (G : Finset α) (k : ℕ) (s : α) : Finset (Finset α) :=
  ((initialSegment G (k - 1)).filter fun i => s ≤ i).image
    fun i => (initialSegment G (k + 1)).erase i

/-- The yFamily `F(k; r, s)` on an arbitrary finite linearly ordered ground. -/
def yFamily (G : Finset α) (k : ℕ) (r s : α) : Finset (Finset α) :=
  ({initialSegment G k, secondInitialSegment G k} ∪ yOuterArm G k r) ∪
    yInnerArm G k s

/-- **Section 7.5.** A coordinate yFamily on a downward-closed ground is a shifted family of
rank `k`. -/
theorem yFamily_isShifted {G : Finset α} (hG : ∀ e ∈ G, ∀ x : α, x < e → x ∈ G)
    {k : ℕ} {r s : α} (hk : 2 ≤ k)
    (hrG : r ∈ G) (hrU : r ∉ initialSegment G (k + 1))
    (hsC : s ∈ initialSegment G (k - 1)) :
    IsShifted (yFamily G k r s) k := by
  let C := initialSegment G (k - 1)
  let I := initialSegment G k
  let U := initialSegment G (k + 1)
  let M₂ := secondInitialSegment G k
  let P := yOuterArm G k r
  let Q := yInnerArm G k s
  let F := yFamily G k r s
  have hrRank : k + 1 ≤ groundRank G r := by
    change r ∉ G.filter (fun x => groundRank G x < k + 1) at hrU
    simpa [hrG] using hrU
  have hGcard : k + 2 ≤ G.card := by
    have hrLt := groundRank_lt_card_of_mem hrG
    omega
  have hCcard : C.card = k - 1 := card_initialSegment_of_le (by omega)
  have hIcard : I.card = k := card_initialSegment_of_le (by omega)
  have hUcard : U.card = k + 1 := card_initialSegment_of_le (by omega)
  have hCI : C ⊆ I := initialSegment_mono G (by omega)
  have hIU : I ⊆ U := initialSegment_mono G (by omega)
  have hCU : C ⊆ U := hCI.trans hIU
  have hCM₂ : C ⊆ M₂ := by
    intro x hx
    have hx' : x ∈ I ∩ M₂ := by
      rw [initialSegment_inter_secondInitialSegment]
      exact hx
    exact (Finset.mem_inter.mp hx').2
  have hM₂U : M₂ ⊆ U := by
    intro x hx
    have hx' : x ∈ I ∪ M₂ := Finset.mem_union_right I hx
    rwa [initialSegment_union_secondInitialSegment] at hx'
  have hM₂card : M₂.card = k := by
    have hcard := Finset.card_union_add_card_inter I M₂
    rw [initialSegment_union_secondInitialSegment,
      initialSegment_inter_secondInitialSegment, hUcard, hCcard, hIcard] at hcard
    omega
  have hIF : I ∈ F := by
    change I ∈ ({I, M₂} ∪ P) ∪ Q
    simp
  have hM₂F : M₂ ∈ F := by
    change M₂ ∈ ({I, M₂} ∪ P) ∪ Q
    simp
  have hsQ : U.erase s ∈ Q := by
    change U.erase s ∈ (C.filter fun a => s ≤ a).image (fun a => U.erase a)
    exact Finset.mem_image.mpr
      ⟨s, Finset.mem_filter.mpr ⟨hsC, le_rfl⟩, rfl⟩
  have hsF : U.erase s ∈ F := by
    change U.erase s ∈ ({I, M₂} ∪ P) ∪ Q
    exact Finset.mem_union_right _ hsQ
  have mem_cases {X : Finset α} (hXF : X ∈ F) :
      X = I ∨ X = M₂ ∨ X ∈ P ∨ X ∈ Q := by
    change X ∈ ({I, M₂} ∪ P) ∪ Q at hXF
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hXF
    tauto
  have outer_repr {X : Finset α} (hXP : X ∈ P) :
      ∃ a : α, a ∈ G ∧ a ∉ U ∧ a ≤ r ∧ X = insert a C := by
    change X ∈ (G.filter fun a => a ∉ U ∧ a ≤ r).image
      (fun a => insert a C) at hXP
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hXP
    exact ⟨a, (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2.1,
      (Finset.mem_filter.mp ha).2.2, rfl⟩
  have inner_repr {X : Finset α} (hXQ : X ∈ Q) :
      ∃ a : α, a ∈ C ∧ s ≤ a ∧ X = U.erase a := by
    change X ∈ (C.filter fun a => s ≤ a).image (fun a => U.erase a) at hXQ
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hXQ
    exact ⟨a, (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2, rfl⟩
  have initial_eq_insert_of_mem_middle {a : α} (haI : a ∈ I) (haC : a ∉ C) :
      insert a C = I := by
    have hsucc : k - 1 + 1 = k := by omega
    have haI' : a ∈ initialSegment G (k - 1 + 1) := by
      rwa [hsucc]
    have h := initialSegment_insert_eq_succ_of_top
      (G := G) (e := a) (j := k - 1) (by omega) haI' haC
    simpa [hsucc] using h
  have second_eq_insert_of_mem_top {a : α} (haU : a ∈ U) (haI : a ∉ I) :
      M₂ = insert a C := by
    have htop : insert a I = U :=
      initialSegment_insert_eq_succ_of_top (G := G) (e := a) (j := k)
        (by omega) haU haI
    have haC : a ∉ C := fun haC => haI (hCI haC)
    change C ∪ (U \ I) = insert a C
    rw [← htop]
    ext x
    by_cases hxa : x = a
    · subst x
      simp [haI, haC]
    · simp [hxa]
  have second_eq_erase_of_mem_middle {a : α} (haI : a ∈ I) (haC : a ∉ C) :
      M₂ = U.erase a := by
    have hmiddle : insert a C = I := initial_eq_insert_of_mem_middle haI haC
    have herase : I.erase a = C := by
      rw [← hmiddle]
      simp [haC]
    change C ∪ (U \ I) = U.erase a
    rw [← herase]
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_erase]
    have hIUx : x ∈ I → x ∈ U := fun hx => hIU hx
    have haIx : x = a → x ∈ I := fun h => h ▸ haI
    tauto
  have initial_eq_erase_of_mem_top {a : α} (haU : a ∈ U) (haI : a ∉ I) :
      U.erase a = I := by
    have htop : insert a I = U :=
      initialSegment_insert_eq_succ_of_top (G := G) (e := a) (j := k)
        (by omega) haU haI
    rw [← htop]
    simp [haI]
  refine ⟨⟨U.erase s, hsF⟩, ?_, ?_⟩
  · intro X hXF
    rcases mem_cases hXF with rfl | rfl | hXP | hXQ
    · exact hIcard
    · exact hM₂card
    · obtain ⟨a, _haG, haU, _har, rfl⟩ := outer_repr hXP
      rw [Finset.card_insert_of_notMem (fun haC => haU (hCU haC)), hCcard]
      omega
    · obtain ⟨a, haC, _hsa, rfl⟩ := inner_repr hXQ
      rw [Finset.card_erase_of_mem (hCU haC), hUcard]
      omega
  · intro X hXF i j hjX hij hiX
    rcases mem_cases hXF with rfl | rfl | hXP | hXQ
    · exact (hiX (initialSegment_downwardClosed hG hjX hij)).elim
    · have hjParts : j ∈ C ∨ (j ∈ U ∧ j ∉ I) := by
        simpa [M₂, secondInitialSegment] using hjX
      rcases hjParts with hjC | ⟨hjU, hjI⟩
      · exact (hiX (hCM₂ (initialSegment_downwardClosed hG hjC hij))).elim
      · have hiU : i ∈ U := initialSegment_downwardClosed hG hjU hij
        have hiI : i ∈ I := by
          by_contra hiI
          apply hiX
          change i ∈ C ∪ (U \ I)
          simp [hiU, hiI]
        have hiC : i ∉ C := fun hiC => hiX (hCM₂ hiC)
        have hM₂repr : M₂ = insert j C := second_eq_insert_of_mem_top hjU hjI
        have hIrepr : insert i C = I := initial_eq_insert_of_mem_middle hiI hiC
        have hjC : j ∉ C := fun hjC => hjI (hCI hjC)
        have hset : insert i (M₂.erase j) = I := by
          rw [hM₂repr]
          simp [hjC, hIrepr]
        rw [hset]
        exact hIF
    · obtain ⟨a, haG, haU, har, rfl⟩ := outer_repr hXP
      have haC : a ∉ C := fun haC => haU (hCU haC)
      have hja : j = a := by
        rcases Finset.mem_insert.mp hjX with hja | hjC
        · exact hja
        · exact (hiX (Finset.mem_insert_of_mem
            (initialSegment_downwardClosed hG hjC hij))).elim
      subst j
      have hiC : i ∉ C := fun hiC => hiX (Finset.mem_insert_of_mem hiC)
      have hiG : i ∈ G := hG a haG i hij
      by_cases hiI : i ∈ I
      · have hset : insert i ((insert a C).erase a) = I := by
          simp [haC, initial_eq_insert_of_mem_middle hiI hiC]
        rw [hset]
        exact hIF
      · by_cases hiU : i ∈ U
        · have hset : insert i ((insert a C).erase a) = M₂ := by
            simp [haC, ← second_eq_insert_of_mem_top hiU hiI]
          rw [hset]
          exact hM₂F
        · have hiP : insert i C ∈ P := by
            change insert i C ∈
              (G.filter fun b => b ∉ U ∧ b ≤ r).image (fun b => insert b C)
            exact Finset.mem_image.mpr
              ⟨i, Finset.mem_filter.mpr ⟨hiG, hiU, le_trans (le_of_lt hij) har⟩, rfl⟩
          have hiF : insert i C ∈ F := by
            change insert i C ∈ ({I, M₂} ∪ P) ∪ Q
            exact Finset.mem_union_left Q (Finset.mem_union_right _ hiP)
          simpa [haC] using hiF
    · obtain ⟨a, haC, hsa, rfl⟩ := inner_repr hXQ
      have haU : a ∈ U := hCU haC
      have hjU : j ∈ U := Finset.mem_of_mem_erase hjX
      have hja : j ≠ a := (Finset.mem_erase.mp hjX).1
      have hiU : i ∈ U := initialSegment_downwardClosed hG hjU hij
      have hia : i = a := by
        by_contra hia
        exact hiX (Finset.mem_erase.mpr ⟨hia, hiU⟩)
      subst i
      have hset : insert a ((U.erase a).erase j) = U.erase j := by
        ext x
        by_cases hxa : x = a
        · subst x
          simp [hja.symm, haU]
        · simp [hxa]
      rw [hset]
      by_cases hjC : j ∈ C
      · have hjQ : U.erase j ∈ Q := by
          change U.erase j ∈ (C.filter fun b => s ≤ b).image (fun b => U.erase b)
          exact Finset.mem_image.mpr
            ⟨j, Finset.mem_filter.mpr ⟨hjC, hsa.trans (le_of_lt hij)⟩, rfl⟩
        change U.erase j ∈ ({I, M₂} ∪ P) ∪ Q
        exact Finset.mem_union_right _ hjQ
      · by_cases hjI : j ∈ I
        · rw [← second_eq_erase_of_mem_middle hjI hjC]
          exact hM₂F
        · rw [initial_eq_erase_of_mem_top hjU hjI]
          exact hIF

/-! ### Lemma 7.10's arm exchange

The duality of Section 7.8 carries a yFamily to a yFamily "with the two arms exchanged". Until
2026-08-24 the tree held only the containment identity that clause is proved FROM —
`innerArm_dual_iff_outerArm` and its converse — and **nothing related `yInnerArm` or `yOuterArm` to
the duality at all**, which a blind reading of the Lean found
(`results/2026-08-24_blind_back_translation.md`). These four lemmas state the clause itself.

The ground is `Fin n` taken whole, which is where Section 7.8's reversal lives, and the hypothesis
`k + 2 ≤ n` is the one `yFamily_isShifted` already carries as `hGcard`. It is not decoration: with
truncated subtraction the statement is **false** for `k > n`, since the dual rank `n - k` collapses
to zero while the inner arm does not. -/

private theorem groundRank_univ_fin {n : ℕ} (e : Fin n) :
    groundRank Finset.univ e = e.val := by
  rw [groundRank]
  have hu : Finset.univ.filter (fun z : Fin n => z < e) = Finset.Iio e := by
    ext z
    simp
  rw [hu, Fin.card_Iio]

/-- On the full ground, the initial segment of size `j` dualizes to the initial segment of
size `n - j`. -/
theorem dualSet_initialSegment_univ {n : ℕ} (j : ℕ) :
    dualSet (initialSegment (Finset.univ : Finset (Fin n)) j)
      = initialSegment (Finset.univ : Finset (Fin n)) (n - j) := by
  classical
  ext e
  have he : e.val < n := e.isLt
  simp only [mem_dualSet, initialSegment, Finset.mem_filter, Finset.mem_univ, true_and,
    groundRank_univ_fin, not_lt, dualElem_val]
  omega

/-- The dual of an inner-arm member is an outer-arm member: deleting `i` from `[k+1]` dualizes to
adjoining `i*` to `[n − k − 1]`. -/
theorem dualSet_erase_initialSegment_univ {n : ℕ} (k : ℕ) (i : Fin n) :
    dualSet ((initialSegment (Finset.univ : Finset (Fin n)) (k + 1)).erase i)
      = insert (dualElem i) (initialSegment (Finset.univ : Finset (Fin n)) (n - (k + 1))) := by
  classical
  ext e
  have he : e.val < n := e.isLt
  have hi : i.val < n := i.isLt
  simp only [mem_dualSet, Finset.mem_erase, initialSegment, Finset.mem_filter, Finset.mem_univ,
    true_and, groundRank_univ_fin, Finset.mem_insert, not_and, not_lt, dualElem_val]
  constructor
  · intro h
    by_cases hei : e = dualElem i
    · exact Or.inl hei
    · refine Or.inr ?_
      have hne : dualElem e ≠ i := by
        intro hcon
        exact hei (by rw [← hcon, dualElem_dualElem])
      have := h hne
      omega
  · rintro (rfl | h)
    · intro hne
      exact absurd (by simp) hne
    · intro _
      omega

/-- The index sets of the two arms correspond under `i ↦ i*`. -/
theorem innerIndex_image_dualElem {n k : ℕ} (hk : k + 2 ≤ n) (s : Fin n) :
    ((initialSegment (Finset.univ : Finset (Fin n)) (k - 1)).filter fun i => s ≤ i).image dualElem
      = (Finset.univ : Finset (Fin n)).filter
          fun a => a ∉ initialSegment (Finset.univ : Finset (Fin n)) (n - k + 1) ∧ a ≤ dualElem s := by
  classical
  ext a
  have ha : a.val < n := a.isLt
  have hs : s.val < n := s.isLt
  simp only [Finset.mem_image, Finset.mem_filter, initialSegment, Finset.mem_univ, true_and,
    groundRank_univ_fin, not_lt, Fin.le_def, dualElem_val]
  constructor
  · rintro ⟨i, ⟨hik, hsi⟩, rfl⟩
    have hi : i.val < n := i.isLt
    have hd : (dualElem i).val = n - (i.val + 1) := dualElem_val i
    omega
  · rintro ⟨hak, has⟩
    have hd : (dualElem a).val = n - (a.val + 1) := dualElem_val a
    refine ⟨dualElem a, ⟨?_, ?_⟩, by simp⟩
    · omega
    · omega

/-- **Lemma 7.10, the arm exchange.** Under duality the inner arm of a coordinate yFamily maps
onto the outer arm of the dual, with the endpoint carried across by `s ↦ s*`. -/
theorem image_dualSet_yInnerArm {n k : ℕ} (hk : k + 2 ≤ n) (s : Fin n) :
    (yInnerArm (Finset.univ : Finset (Fin n)) k s).image dualSet
      = yOuterArm (Finset.univ : Finset (Fin n)) (n - k) (dualElem s) := by
  classical
  rw [yInnerArm, yOuterArm, Finset.image_image, ← innerIndex_image_dualElem hk s,
    Finset.image_image]
  refine Finset.image_congr ?_
  intro i _
  simp only [Function.comp_apply]
  rw [dualSet_erase_initialSegment_univ, Nat.sub_sub]

/-- **Lemma 7.10, the arm exchange, other direction.** The outer arm maps onto the dual's inner
arm. Derived from `image_dualSet_yInnerArm` at the dual rank rather than re-proved. -/
theorem image_dualSet_yOuterArm {n k : ℕ} (hk2 : 2 ≤ k) (hk : k + 2 ≤ n) (r : Fin n) :
    (yOuterArm (Finset.univ : Finset (Fin n)) k r).image dualSet
      = yInnerArm (Finset.univ : Finset (Fin n)) (n - k) (dualElem r) := by
  classical
  have hk' : (n - k) + 2 ≤ n := by omega
  have hback : n - (n - k) = k := by omega
  have h := image_dualSet_yInnerArm (n := n) hk' (dualElem r)
  rw [hback, dualElem_dualElem] at h
  rw [← h, Finset.image_image]
  rw [show (dualSet ∘ dualSet : Finset (Fin n) → Finset (Fin n)) = id by
        funext X; simp [Function.comp_apply]]
  exact Finset.image_id

/-- **Theorem 7.6, converse direction.** A coordinate yFamily with both arms nonempty is a
clique-sum. Its universal pair is the canonical bottom pair, and its two off-pair cliques
are exactly `yOuterArm G k r` and `yInnerArm G k s`. -/
theorem yFamily_isCliqueSum {G : Finset α} {k : ℕ} {r s : α}
    (hrG : r ∈ G) (hrU : r ∉ initialSegment G (k + 1))
    (hsC : s ∈ initialSegment G (k - 1)) :
    ∃ (hm₁ : initialSegment G k ∈ yFamily G k r s)
        (hm₂ : secondInitialSegment G k ∈ yFamily G k r s),
      IsCliqueSum (yFamily G k r s)
          ⟨initialSegment G k, hm₁⟩ ⟨secondInitialSegment G k, hm₂⟩ ∧
      (yOuterArm G k r).Nonempty ∧ (yInnerArm G k s).Nonempty ∧
      Disjoint (yOuterArm G k r) (yInnerArm G k s) ∧
      (∀ X : ExchangeV (yFamily G k r s),
        X ≠ ⟨initialSegment G k, hm₁⟩ →
        X ≠ ⟨secondInitialSegment G k, hm₂⟩ →
        X.val ∈ yOuterArm G k r ∨ X.val ∈ yInnerArm G k s) ∧
      (∀ A B : ExchangeV (yFamily G k r s),
        A ≠ ⟨initialSegment G k, hm₁⟩ →
        A ≠ ⟨secondInitialSegment G k, hm₂⟩ →
        B ≠ ⟨initialSegment G k, hm₁⟩ →
        B ≠ ⟨secondInitialSegment G k, hm₂⟩ → A ≠ B →
        ((exchangeGraph (yFamily G k r s)).Adj A B ↔
          ((A.val ∈ yOuterArm G k r ∧ B.val ∈ yOuterArm G k r) ∨
           (A.val ∈ yInnerArm G k s ∧ B.val ∈ yInnerArm G k s)))) := by
  let C := initialSegment G (k - 1)
  let I := initialSegment G k
  let U := initialSegment G (k + 1)
  let M₂ := secondInitialSegment G k
  let P := yOuterArm G k r
  let Q := yInnerArm G k s
  let F := yFamily G k r s
  have hrRank : k + 1 ≤ groundRank G r := by
    change r ∉ G.filter (fun x => groundRank G x < k + 1) at hrU
    simpa [hrG] using hrU
  have hGcard : k + 2 ≤ G.card := by
    have hrLt := groundRank_lt_card_of_mem hrG
    omega
  have hk : 2 ≤ k := by
    change s ∈ G.filter (fun x => groundRank G x < k - 1) at hsC
    have hsRank := (Finset.mem_filter.mp hsC).2
    omega
  have hCcard : C.card = k - 1 := card_initialSegment_of_le (by omega)
  have hIcard : I.card = k := card_initialSegment_of_le (by omega)
  have hUcard : U.card = k + 1 := card_initialSegment_of_le (by omega)
  have hCI : C ⊆ I := initialSegment_mono G (by omega)
  have hIU : I ⊆ U := initialSegment_mono G (by omega)
  have hCU : C ⊆ U := hCI.trans hIU
  have hCM₂ : C ⊆ M₂ := by
    intro x hx
    have hx' : x ∈ I ∩ M₂ := by
      rw [initialSegment_inter_secondInitialSegment]
      exact hx
    exact (Finset.mem_inter.mp hx').2
  have hM₂U : M₂ ⊆ U := by
    intro x hx
    have hx' : x ∈ I ∪ M₂ := Finset.mem_union_right I hx
    rwa [initialSegment_union_secondInitialSegment] at hx'
  have hM₂card : M₂.card = k := by
    have hcard := Finset.card_union_add_card_inter I M₂
    rw [initialSegment_union_secondInitialSegment,
      initialSegment_inter_secondInitialSegment, hUcard, hCcard, hIcard] at hcard
    omega
  have hIM₂ : I ≠ M₂ := by
    intro hEq
    have hEq' : initialSegment G k = secondInitialSegment G k := hEq
    have hCUeq : C = U := by
      change initialSegment G (k - 1) = initialSegment G (k + 1)
      rw [← initialSegment_inter_secondInitialSegment G k,
        ← initialSegment_union_secondInitialSegment G k, hEq']
      simp
    have := congrArg Finset.card hCUeq
    rw [hCcard, hUcard] at this
    omega
  have hm₁F : I ∈ F := by
    change I ∈ ({I, M₂} ∪ P) ∪ Q
    simp
  have hm₂F : M₂ ∈ F := by
    change M₂ ∈ ({I, M₂} ∪ P) ∪ Q
    simp
  have hrP : insert r C ∈ P := by
    change insert r C ∈
      (G.filter fun a => a ∉ U ∧ a ≤ r).image (fun a => insert a C)
    exact Finset.mem_image.mpr
      ⟨r, Finset.mem_filter.mpr ⟨hrG, hrU, le_rfl⟩, rfl⟩
  have hsQ : U.erase s ∈ Q := by
    change U.erase s ∈
      (C.filter fun i => s ≤ i).image (fun i => U.erase i)
    exact Finset.mem_image.mpr
      ⟨s, Finset.mem_filter.mpr ⟨hsC, le_rfl⟩, rfl⟩
  have hPne : P.Nonempty := ⟨insert r C, hrP⟩
  have hQne : Q.Nonempty := ⟨U.erase s, hsQ⟩
  have hrPF : insert r C ∈ F := by
    change insert r C ∈ ({I, M₂} ∪ P) ∪ Q
    exact Finset.mem_union_left Q (Finset.mem_union_right _ hrP)
  have hsQF : U.erase s ∈ F := by
    change U.erase s ∈ ({I, M₂} ∪ P) ∪ Q
    exact Finset.mem_union_right _ hsQ
  have outer_repr {X : Finset α} (hXP : X ∈ P) :
      ∃ a : α, a ∈ G ∧ a ∉ U ∧ a ≤ r ∧ X = insert a C := by
    change X ∈ (G.filter fun a => a ∉ U ∧ a ≤ r).image
      (fun a => insert a C) at hXP
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hXP
    exact ⟨a, (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2.1,
      (Finset.mem_filter.mp ha).2.2, rfl⟩
  have inner_repr {X : Finset α} (hXQ : X ∈ Q) :
      ∃ i : α, i ∈ C ∧ s ≤ i ∧ X = U.erase i := by
    change X ∈ (C.filter fun i => s ≤ i).image (fun i => U.erase i) at hXQ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hXQ
    exact ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2, rfl⟩
  have hPQ : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro X hXP hXQ
    obtain ⟨a, _haG, haU, _har, rfl⟩ := outer_repr hXP
    obtain ⟨i, hiC, _hsi, hEq⟩ := inner_repr hXQ
    have haLeft : a ∈ insert a C := Finset.mem_insert_self _ _
    have haRight : a ∈ U.erase i := hEq ▸ haLeft
    exact haU (Finset.mem_of_mem_erase haRight)
  have mem_cases {X : Finset α} (hXF : X ∈ F) :
      X = I ∨ X = M₂ ∨ X ∈ P ∨ X ∈ Q := by
    change X ∈ ({I, M₂} ∪ P) ∪ Q at hXF
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hXF
    tauto
  have arm_cases (X : ExchangeV F)
      (hXI : X ≠ ⟨I, hm₁F⟩) (hXM₂ : X ≠ ⟨M₂, hm₂F⟩) :
      X.val ∈ P ∨ X.val ∈ Q := by
    rcases mem_cases X.prop with hX | hX | hX | hX
    · exact (hXI (Subtype.ext hX)).elim
    · exact (hXM₂ (Subtype.ext hX)).elim
    · exact Or.inl hX
    · exact Or.inr hX
  have outer_adj {A B : ExchangeV F} (hAP : A.val ∈ P) (hBP : B.val ∈ P)
      (hAB : A ≠ B) : (exchangeGraph F).Adj A B := by
    obtain ⟨a, _haG, haU, _har, hA⟩ := outer_repr hAP
    obtain ⟨b, _hbG, hbU, _hbr, hB⟩ := outer_repr hBP
    apply exchangeGraph_adj_of_common_lowerCover (C := C) A.prop B.prop
      (by rw [hA]; exact Finset.subset_insert _ _)
      (by rw [hB]; exact Finset.subset_insert _ _)
    · rw [hA, Finset.card_insert_of_notMem (fun haC => haU (hCU haC)), hCcard]
    · rw [hB, Finset.card_insert_of_notMem (fun hbC => hbU (hCU hbC)), hCcard]
    · exact fun h => hAB (Subtype.ext h)
  have inner_adj {A B : ExchangeV F} (hAQ : A.val ∈ Q) (hBQ : B.val ∈ Q)
      (hAB : A ≠ B) : (exchangeGraph F).Adj A B := by
    obtain ⟨i, hiC, _hsi, hA⟩ := inner_repr hAQ
    obtain ⟨j, hjC, _hsj, hB⟩ := inner_repr hBQ
    have hiU : i ∈ U := hCU hiC
    have hjU : j ∈ U := hCU hjC
    apply exchangeGraph_adj_of_common_upperCover (U := U) A.prop B.prop
      (by rw [hA]; exact Finset.erase_subset _ _)
      (by rw [hB]; exact Finset.erase_subset _ _)
    · rw [hA, Finset.card_erase_of_mem hiU, hUcard]
      omega
    · rw [hB, Finset.card_erase_of_mem hjU, hUcard]
      omega
    · exact fun h => hAB (Subtype.ext h)
  have cross_not_adj {A B : ExchangeV F} (hAP : A.val ∈ P) (hBQ : B.val ∈ Q) :
      ¬ (exchangeGraph F).Adj A B := by
    obtain ⟨a, _haG, haU, _har, hA⟩ := outer_repr hAP
    obtain ⟨i, hiC, _hsi, hB⟩ := inner_repr hBQ
    have hiU : i ∈ U := hCU hiC
    have haC : a ∉ C := fun h => haU (hCU h)
    have hAcard : A.val.card = k := by
      rw [hA, Finset.card_insert_of_notMem haC, hCcard]
      omega
    have hBcard : B.val.card = k := by
      rw [hB, Finset.card_erase_of_mem hiU, hUcard]
      omega
    intro hAdj
    have hone := card_sdiff_eq_one_of_adj_of_card_eq
      (F := F) (A := A) (B := B) (hAcard.trans hBcard.symm) hAdj
    have hai : a ≠ i := fun h => haU (h ▸ hiU)
    have hpair : ({a, i} : Finset α) ⊆ A.val \ B.val := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hxa | hxi
      · subst x
        apply Finset.mem_sdiff.mpr
        refine ⟨hA ▸ Finset.mem_insert_self _ _, ?_⟩
        rw [hB]
        exact fun haB => haU (Finset.mem_of_mem_erase haB)
      · have hxi' : x = i := by simpa using hxi
        subst x
        apply Finset.mem_sdiff.mpr
        refine ⟨hA ▸ Finset.mem_insert_of_mem hiC, ?_⟩
        rw [hB]
        exact Finset.notMem_erase _ _
    have htwo := Finset.card_le_card hpair
    rw [Finset.card_pair hai, hone] at htwo
    omega
  have arms_adj (A B : ExchangeV F)
      (hAI : A ≠ ⟨I, hm₁F⟩) (hAM₂ : A ≠ ⟨M₂, hm₂F⟩)
      (hBI : B ≠ ⟨I, hm₁F⟩) (hBM₂ : B ≠ ⟨M₂, hm₂F⟩) (hAB : A ≠ B) :
      ((exchangeGraph F).Adj A B ↔
        ((A.val ∈ P ∧ B.val ∈ P) ∨ (A.val ∈ Q ∧ B.val ∈ Q))) := by
    rcases arm_cases A hAI hAM₂ with hAP | hAQ <;>
      rcases arm_cases B hBI hBM₂ with hBP | hBQ
    · constructor
      · exact fun _ => Or.inl ⟨hAP, hBP⟩
      · exact fun _ => outer_adj hAP hBP hAB
    · have hAnQ : A.val ∉ Q := fun hAQ => Finset.disjoint_left.mp hPQ hAP hAQ
      have hBnP : B.val ∉ P := fun hBP => Finset.disjoint_left.mp hPQ hBP hBQ
      constructor
      · exact fun hAdj => (cross_not_adj hAP hBQ hAdj).elim
      · rintro (⟨_, hBP⟩ | ⟨hAQ, _⟩)
        · exact (hBnP hBP).elim
        · exact (hAnQ hAQ).elim
    · have hAnP : A.val ∉ P := fun hAP => Finset.disjoint_left.mp hPQ hAP hAQ
      have hBnQ : B.val ∉ Q := fun hBQ => Finset.disjoint_left.mp hPQ hBP hBQ
      have hnot : ¬ (exchangeGraph F).Adj A B := by
        intro hAdj
        exact cross_not_adj hBP hAQ hAdj.symm
      constructor
      · exact fun hAdj => (hnot hAdj).elim
      · rintro (⟨hAP, _⟩ | ⟨_, hBQ⟩)
        · exact (hAnP hAP).elim
        · exact (hBnQ hBQ).elim
    · constructor
      · exact fun _ => Or.inr ⟨hAQ, hBQ⟩
      · exact fun _ => inner_adj hAQ hBQ hAB
  have hm₁Univ : (exchangeGraph F).IsUniversalVertex ⟨I, hm₁F⟩ := by
    intro X hXI
    have hXIval : X.val ≠ I := fun h => hXI (Subtype.ext h)
    rcases mem_cases X.prop with hX | hX | hXP | hXQ
    · exact (hXIval hX).elim
    · apply exchangeGraph_adj_of_common_lowerCover hm₁F X.prop hCI
        (by rw [hX]; exact hCM₂)
      · rw [hIcard, hCcard]
        omega
      · rw [hX, hM₂card, hCcard]
        omega
      · exact hXIval.symm
    · obtain ⟨a, _haG, haU, _har, hX⟩ := outer_repr hXP
      apply exchangeGraph_adj_of_common_lowerCover hm₁F X.prop hCI
        (by rw [hX]; exact Finset.subset_insert _ _)
      · rw [hIcard, hCcard]
        omega
      · rw [hX, Finset.card_insert_of_notMem (fun haC => haU (hCU haC)), hCcard]
      · exact hXIval.symm
    · obtain ⟨i, hiC, _hsi, hX⟩ := inner_repr hXQ
      have hiU : i ∈ U := hCU hiC
      apply exchangeGraph_adj_of_common_upperCover hm₁F X.prop hIU
        (by rw [hX]; exact Finset.erase_subset _ _)
      · rw [hUcard, hIcard]
      · rw [hX, Finset.card_erase_of_mem hiU, hUcard]
        omega
      · exact hXIval.symm
  have hm₂Univ : (exchangeGraph F).IsUniversalVertex ⟨M₂, hm₂F⟩ := by
    intro X hXM₂
    have hXM₂val : X.val ≠ M₂ := fun h => hXM₂ (Subtype.ext h)
    rcases mem_cases X.prop with hX | hX | hXP | hXQ
    · apply exchangeGraph_adj_of_common_lowerCover (C := C) hm₂F X.prop hCM₂
        (by rw [hX]; exact hCI)
      · rw [hM₂card, hCcard]
        omega
      · rw [hX, hIcard, hCcard]
        omega
      · exact hXM₂val.symm
    · exact (hXM₂val hX).elim
    · obtain ⟨a, _haG, haU, _har, hX⟩ := outer_repr hXP
      apply exchangeGraph_adj_of_common_lowerCover hm₂F X.prop hCM₂
        (by rw [hX]; exact Finset.subset_insert _ _)
      · rw [hM₂card, hCcard]
        omega
      · rw [hX, Finset.card_insert_of_notMem (fun haC => haU (hCU haC)), hCcard]
      · exact hXM₂val.symm
    · obtain ⟨i, hiC, _hsi, hX⟩ := inner_repr hXQ
      have hiU : i ∈ U := hCU hiC
      apply exchangeGraph_adj_of_common_upperCover hm₂F X.prop hM₂U
        (by rw [hX]; exact Finset.erase_subset _ _)
      · rw [hUcard, hM₂card]
      · rw [hX, Finset.card_erase_of_mem hiU, hUcard]
        omega
      · exact hXM₂val.symm
  let side : ExchangeV F → Bool := fun X => decide (X.val ∈ P)
  have hbad : IsCliqueSum F ⟨I, hm₁F⟩ ⟨M₂, hm₂F⟩ := by
    refine ⟨fun h => hIM₂ (congrArg Subtype.val h), hm₁Univ, hm₂Univ,
      side, ?_, ?_, ?_⟩
    · let A : ExchangeV F := ⟨insert r C, hrPF⟩
      refine ⟨A, ?_, ?_, ?_⟩
      · intro h
        have hval : insert r C = I := congrArg Subtype.val h
        have hrI : r ∈ I := hval ▸ Finset.mem_insert_self r C
        exact hrU (hIU hrI)
      · intro h
        have hval : insert r C = M₂ := congrArg Subtype.val h
        have hrM₂ : r ∈ M₂ := hval ▸ Finset.mem_insert_self r C
        exact hrU (hM₂U hrM₂)
      · simp [side, A, hrP]
    · let B : ExchangeV F := ⟨U.erase s, hsQF⟩
      have hsI : s ∈ I := hCI hsC
      have hsM₂ : s ∈ M₂ := hCM₂ hsC
      have hBnP : B.val ∉ P := fun hBP =>
        Finset.disjoint_left.mp hPQ hBP hsQ
      refine ⟨B, ?_, ?_, ?_⟩
      · intro h
        have hval : U.erase s = I := congrArg Subtype.val h
        have hsB : s ∈ U.erase s := hval.symm ▸ hsI
        exact (Finset.notMem_erase s U) hsB
      · intro h
        have hval : U.erase s = M₂ := congrArg Subtype.val h
        have hsB : s ∈ U.erase s := hval.symm ▸ hsM₂
        exact (Finset.notMem_erase s U) hsB
      · simp [side, hBnP]
    · intro A B hAI hAM₂ hBI hBM₂ hAB
      have hArms := arm_cases A hAI hAM₂
      have hBarms := arm_cases B hBI hBM₂
      rw [arms_adj A B hAI hAM₂ hBI hBM₂ hAB]
      rcases hArms with hAP | hAQ <;> rcases hBarms with hBP | hBQ
      · simp [side, hAP, hBP]
      · have hAnQ : A.val ∉ Q := fun h => Finset.disjoint_left.mp hPQ hAP h
        have hBnP : B.val ∉ P := fun h => Finset.disjoint_left.mp hPQ h hBQ
        simp [side, hAP, hAnQ, hBnP]
      · have hAnP : A.val ∉ P := fun h => Finset.disjoint_left.mp hPQ h hAQ
        have hBnQ : B.val ∉ Q := fun h => Finset.disjoint_left.mp hPQ hBP h
        simp [side, hAQ, hAnP, hBP, hBnQ]
      · have hAnP : A.val ∉ P := fun h => Finset.disjoint_left.mp hPQ h hAQ
        have hBnP : B.val ∉ P := fun h => Finset.disjoint_left.mp hPQ h hBQ
        simp [side, hAnP, hBnP, hAQ, hBQ]
  change ∃ (hm₁ : I ∈ F) (hm₂ : M₂ ∈ F), _
  refine ⟨hm₁F, hm₂F, hbad, hPne, hQne, hPQ, arm_cases, arms_adj⟩

/-- **Lemma 3, index-bearing forward half.** Every shifted clique-sum is a coordinate Y-family.
Both endpoints are realized (`r` lies beyond `[k+1]`, and `s` lies in `[k-1]`), so both arms in
both arms of the displayed Y-family are nonempty. -/
theorem lemma3_arms_are_contiguous {F : Finset (Finset α)} {k : ℕ}
    (hF : IsShifted F k) {u v : ExchangeV F} (hbad : IsCliqueSum F u v) :
    ∃ r s : α,
      r ∈ usedGround F ∧ r ∉ initialSegment (usedGround F) (k + 1) ∧
      s ∈ initialSegment (usedGround F) (k - 1) ∧
      F = yFamily (usedGround F) k r s := by
  let G := usedGround F
  let C := initialSegment G (k - 1)
  let U := initialSegment G (k + 1)
  let Pidx := G.filter fun a => a ∉ U ∧ insert a C ∈ F
  let Qidx := C.filter fun i => U.erase i ∈ F
  obtain ⟨⟨a₀, ha₀G, ha₀U, ha₀F⟩, ⟨i₀, hi₀C, hi₀F⟩⟩ :=
    lemma3_coordinate_arms_nonempty hF hbad
  change a₀ ∈ G at ha₀G
  change a₀ ∉ U at ha₀U
  change insert a₀ C ∈ F at ha₀F
  change i₀ ∈ C at hi₀C
  change U.erase i₀ ∈ F at hi₀F
  have hPne : Pidx.Nonempty := by
    refine ⟨a₀, ?_⟩
    exact Finset.mem_filter.mpr ⟨ha₀G, ha₀U, ha₀F⟩
  have hQne : Qidx.Nonempty := by
    refine ⟨i₀, ?_⟩
    exact Finset.mem_filter.mpr ⟨hi₀C, hi₀F⟩
  let r := Pidx.max' hPne
  let s := Qidx.min' hQne
  have hrP : r ∈ Pidx := by exact Finset.max'_mem _ _
  have hsQ : s ∈ Qidx := by exact Finset.min'_mem _ _
  have hrData : r ∈ G ∧ r ∉ U ∧ insert r C ∈ F := Finset.mem_filter.mp hrP
  have hsData : s ∈ C ∧ U.erase s ∈ F := Finset.mem_filter.mp hsQ
  have hCsubU : C ⊆ U := by
    exact initialSegment_mono G (by omega)
  have hpairCoord := cliqueSum_universalPair_coordinates hF hbad
  change
    (u.val = initialSegment G k ∧ v.val = secondInitialSegment G k) ∨
      (v.val = initialSegment G k ∧ u.val = secondInitialSegment G k) at hpairCoord
  have hm₁F : initialSegment G k ∈ F := by
    rcases hpairCoord with ⟨hu, _hv⟩ | ⟨hv, _hu⟩
    · rw [← hu]
      exact u.prop
    · rw [← hv]
      exact v.prop
  have hm₂F : secondInitialSegment G k ∈ F := by
    rcases hpairCoord with ⟨_hu, hv⟩ | ⟨_hv, hu⟩
    · rw [← hv]
      exact v.prop
    · rw [← hu]
      exact u.prop
  refine ⟨r, s, hrData.1, hrData.2.1, hsData.1, ?_⟩
  change F = yFamily G k r s
  apply Finset.Subset.antisymm
  · intro X hXF
    let XV : ExchangeV F := ⟨X, hXF⟩
    by_cases hXu : XV = u
    · have hX : X = u.val := congrArg Subtype.val hXu
      rw [hX, yFamily]
      rcases hpairCoord with ⟨hu, _hv⟩ | ⟨_hv, hu⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simp [hu]))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simp [hu]))
    by_cases hXv : XV = v
    · have hX : X = v.val := congrArg Subtype.val hXv
      rw [hX, yFamily]
      rcases hpairCoord with ⟨_hu, hv⟩ | ⟨hv, _hu⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simp [hv]))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simp [hv]))
    have hcoord := lemma3_arm_member_coordinates hF hbad XV hXu hXv
    rcases hcoord with ⟨a, haG, haU, hXrepr⟩ | ⟨i, hiC, hXrepr⟩
    · change a ∈ G at haG
      change a ∉ U at haU
      change X = insert a C at hXrepr
      have haP : a ∈ Pidx := by
        exact Finset.mem_filter.mpr ⟨haG, haU, hXrepr ▸ hXF⟩
      have har : a ≤ r := by
        change a ≤ Pidx.max' hPne
        exact Finset.le_max' Pidx a haP
      rw [yFamily]
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      rw [yOuterArm]
      apply Finset.mem_image.mpr
      exact ⟨a, Finset.mem_filter.mpr ⟨haG, haU, har⟩, hXrepr.symm⟩
    · change i ∈ C at hiC
      change X = U.erase i at hXrepr
      have hiQ : i ∈ Qidx := Finset.mem_filter.mpr ⟨hiC, hXrepr ▸ hXF⟩
      have hsi : s ≤ i := by
        change Qidx.min' hQne ≤ i
        exact Finset.min'_le Qidx i hiQ
      rw [yFamily]
      apply Finset.mem_union_right
      rw [yInnerArm]
      apply Finset.mem_image.mpr
      exact ⟨i, Finset.mem_filter.mpr ⟨hiC, hsi⟩, hXrepr.symm⟩
  · intro X hX
    rw [yFamily] at hX
    rcases Finset.mem_union.mp hX with hcenterOrP | hQ
    · rcases Finset.mem_union.mp hcenterOrP with hcenter | hP
      · rcases Finset.mem_insert.mp hcenter with hXm₁ | hXm₂
        · exact hXm₁ ▸ hm₁F
        · have hXm₂' : X = secondInitialSegment G k := by simpa using hXm₂
          exact hXm₂' ▸ hm₂F
      · rw [yOuterArm] at hP
        obtain ⟨a, haSource, rfl⟩ := Finset.mem_image.mp hP
        obtain ⟨haG, haU, har⟩ := Finset.mem_filter.mp haSource
        by_cases harEq : a = r
        · simpa [harEq] using hrData.2.2
        · have harLt : a < r := lt_of_le_of_ne har harEq
          exact outerArm_down_closed hF hrData.2.2
            (fun hrC => hrData.2.1 (hCsubU hrC))
            (fun haC => haU (hCsubU haC)) harLt
    · rw [yInnerArm] at hQ
      obtain ⟨i, hiSource, rfl⟩ := Finset.mem_image.mp hQ
      obtain ⟨hiC, hsi⟩ := Finset.mem_filter.mp hiSource
      by_cases hsiEq : s = i
      · simpa [hsiEq] using hsData.2
      · have hsiLt : s < i := lt_of_le_of_ne hsi hsiEq
        exact innerArm_up_closed hF hsData.2 (hCsubU hsData.1) (hCsubU hiC) hsiLt

/-- Transport of the yFamily classification from a punctured ordered type back to an ambient ground
which avoids the puncture.  This is the common engine for the avoiding-layer and lifted-link rows. -/
theorem punctured_cliqueSum_lift_eq_yFamily
    {e : α} {P : Finset (Finset (Punctured e))} {H : Finset α} {k : ℕ}
    (hP : IsShifted P k) (hPH : ∀ X ∈ P, liftPuncturedSet X ⊆ H)
    (heH : e ∉ H) {u v : ExchangeV P} (hbad : IsCliqueSum P u v) :
    ∃ r s : Punctured e,
      r.val ∈ H ∧ r.val ∉ initialSegment H (k + 1) ∧
      s.val ∈ initialSegment H (k - 1) ∧
      P.image liftPuncturedSet = yFamily H k r.val s.val := by
  let GP := usedGround P
  let C₀ := initialSegment GP (k - 1)
  let U₀ := initialSegment GP (k + 1)
  let C := initialSegment H (k - 1)
  let U := initialSegment H (k + 1)
  have huv : u ≠ v := hbad.1
  have huvVal : u.val ≠ v.val := fun h => huv (Subtype.ext h)
  have hpairsub : {u.val, v.val} ⊆ P := by
    intro X hX
    rcases Finset.mem_insert.mp hX with rfl | hX
    · exact u.prop
    · have hXv : X = v.val := by simpa using hX
      exact hXv ▸ v.prop
  have htwo : 2 ≤ P.card := by
    have hle := Finset.card_le_card hpairsub
    simpa [Finset.card_pair huvVal] using hle
  have hInitLift : liftPuncturedSet (initialSegment GP k) = initialSegment H k := by
    rcases lemma2_universalPair_is_galeLeast hP hbad with
      ⟨huLeast, _hvSecond⟩ | ⟨hvLeast, _huSecond⟩
    · rw [← galeLeast_eq_initialSegment hP huLeast]
      simpa [Finset.erase_eq_of_notMem heH] using
        punctured_galeLeast_lift_eq_initialSegment hP hPH huLeast
    · rw [← galeLeast_eq_initialSegment hP hvLeast]
      simpa [Finset.erase_eq_of_notMem heH] using
        punctured_galeLeast_lift_eq_initialSegment hP hPH hvLeast
  have hSecondLift :
      liftPuncturedSet (secondInitialSegment GP k) = secondInitialSegment H k := by
    rcases lemma2_universalPair_is_galeLeast hP hbad with
      ⟨huLeast, hvSecond⟩ | ⟨hvLeast, huSecond⟩
    · rw [← galeSecondLeast_eq_secondInitialSegment hP htwo huLeast hvSecond]
      simpa [Finset.erase_eq_of_notMem heH] using
        punctured_galeSecondLeast_lift_eq_secondInitialSegment
          hP htwo hPH huLeast hvSecond
    · rw [← galeSecondLeast_eq_secondInitialSegment hP htwo hvLeast huSecond]
      simpa [Finset.erase_eq_of_notMem heH] using
        punctured_galeSecondLeast_lift_eq_secondInitialSegment
          hP htwo hPH hvLeast huSecond
  have hLiftInter (A B : Finset (Punctured e)) :
      liftPuncturedSet (A ∩ B) = liftPuncturedSet A ∩ liftPuncturedSet B := by
    ext x
    by_cases hxe : x = e
    · subst x
      simp [liftPuncturedSet]
    · simp [liftPuncturedSet, hxe]
  have hLiftUnion (A B : Finset (Punctured e)) :
      liftPuncturedSet (A ∪ B) = liftPuncturedSet A ∪ liftPuncturedSet B := by
    ext x
    by_cases hxe : x = e
    · subst x
      simp [liftPuncturedSet]
    · simp [liftPuncturedSet, hxe]
  have val_mem_lift_iff (a : Punctured e) (X : Finset (Punctured e)) :
      a.val ∈ liftPuncturedSet X ↔ a ∈ X := by
    constructor
    · intro h
      obtain ⟨b, hb, hba⟩ := Finset.mem_map.mp h
      have : b = a := Subtype.ext hba
      simpa [this] using hb
    · intro ha
      exact Finset.mem_map.mpr ⟨a, ha, rfl⟩
  have hCLift : liftPuncturedSet C₀ = C := by
    calc
      liftPuncturedSet C₀ =
          liftPuncturedSet (initialSegment GP k ∩ secondInitialSegment GP k) := by
            rw [initialSegment_inter_secondInitialSegment]
      _ = liftPuncturedSet (initialSegment GP k) ∩
          liftPuncturedSet (secondInitialSegment GP k) := hLiftInter _ _
      _ = initialSegment H k ∩ secondInitialSegment H k := by
        rw [hInitLift, hSecondLift]
      _ = C := initialSegment_inter_secondInitialSegment H k
  have hULift : liftPuncturedSet U₀ = U := by
    calc
      liftPuncturedSet U₀ =
          liftPuncturedSet (initialSegment GP k ∪ secondInitialSegment GP k) := by
            rw [initialSegment_union_secondInitialSegment]
      _ = liftPuncturedSet (initialSegment GP k) ∪
          liftPuncturedSet (secondInitialSegment GP k) := hLiftUnion _ _
      _ = initialSegment H k ∪ secondInitialSegment H k := by
        rw [hInitLift, hSecondLift]
      _ = U := initialSegment_union_secondInitialSegment H k
  have hCsubU : C ⊆ U := initialSegment_mono H (by omega)
  obtain ⟨r, s, hrGP, hrU₀, hsC₀, hclass⟩ := lemma3_arms_are_contiguous hP hbad
  change r ∈ GP at hrGP
  change r ∉ U₀ at hrU₀
  change s ∈ C₀ at hsC₀
  change P = yFamily GP k r s at hclass
  have usedValMemH : ∀ {a : Punctured e}, a ∈ GP → a.val ∈ H := by
    intro a ha
    change a ∈ usedGround P at ha
    rw [usedGround, Finset.mem_biUnion] at ha
    obtain ⟨X, hXP, haX⟩ := ha
    exact hPH X hXP (Finset.mem_map.mpr ⟨a, haX, rfl⟩)
  have hrH : r.val ∈ H := usedValMemH hrGP
  have hrU : r.val ∉ U := by
    intro hr
    have : r.val ∈ liftPuncturedSet U₀ := hULift.symm ▸ hr
    exact hrU₀ ((val_mem_lift_iff r U₀).mp this)
  have hsC : s.val ∈ C := by
    rw [← hCLift]
    exact Finset.mem_map.mpr ⟨s, hsC₀, rfl⟩
  refine ⟨r, s, hrH, hrU, hsC, ?_⟩
  apply Finset.Subset.antisymm
  · intro X hX
    obtain ⟨Xp, hXpP, rfl⟩ := Finset.mem_image.mp hX
    rw [hclass] at hXpP
    rcases Finset.mem_union.mp hXpP with hcenterOrP | hQ
    · rcases Finset.mem_union.mp hcenterOrP with hcenter | hOuter
      · rcases Finset.mem_insert.mp hcenter with hInit | hSecond
        · have hEq : Xp = initialSegment GP k := hInit
          rw [hEq, hInitLift, yFamily]
          exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simp))
        · have hEq : Xp = secondInitialSegment GP k := by simpa using hSecond
          rw [hEq, hSecondLift, yFamily]
          exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simp))
      · rw [yOuterArm] at hOuter
        obtain ⟨a, haSource, rfl⟩ := Finset.mem_image.mp hOuter
        obtain ⟨haGP, haU₀, har⟩ := Finset.mem_filter.mp haSource
        have haH : a.val ∈ H := usedValMemH haGP
        have haU : a.val ∉ U := by
          intro ha
          have : a.val ∈ liftPuncturedSet U₀ := hULift.symm ▸ ha
          exact haU₀ ((val_mem_lift_iff a U₀).mp this)
        have hLift : liftPuncturedSet (insert a C₀) = insert a.val C := by
          ext x
          rw [← hCLift]
          simp [liftPuncturedSet]
        rw [hLift, yFamily]
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        rw [yOuterArm]
        exact Finset.mem_image.mpr
          ⟨a.val, Finset.mem_filter.mpr ⟨haH, haU, har⟩, rfl⟩
    · rw [yInnerArm] at hQ
      obtain ⟨i, hiSource, rfl⟩ := Finset.mem_image.mp hQ
      obtain ⟨hiC₀, hsi⟩ := Finset.mem_filter.mp hiSource
      have hiC : i.val ∈ C := by
        rw [← hCLift]
        exact Finset.mem_map.mpr ⟨i, hiC₀, rfl⟩
      have hLift : liftPuncturedSet (U₀.erase i) = U.erase i.val := by
        ext x
        rw [← hULift]
        simp [liftPuncturedSet]
      rw [hLift, yFamily]
      apply Finset.mem_union_right
      rw [yInnerArm]
      exact Finset.mem_image.mpr
        ⟨i.val, Finset.mem_filter.mpr ⟨hiC, hsi⟩, rfl⟩
  · intro X hX
    rw [yFamily] at hX
    rcases Finset.mem_union.mp hX with hcenterOrP | hQ
    · rcases Finset.mem_union.mp hcenterOrP with hcenter | hOuter
      · rcases Finset.mem_insert.mp hcenter with hInit | hSecond
        · apply Finset.mem_image.mpr
          refine ⟨initialSegment GP k, ?_, ?_⟩
          · rw [hclass, yFamily]
            exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simp))
          · exact hInitLift.trans hInit.symm
        · have hSecond' : X = secondInitialSegment H k := by simpa using hSecond
          apply Finset.mem_image.mpr
          refine ⟨secondInitialSegment GP k, ?_, ?_⟩
          · rw [hclass, yFamily]
            exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simp))
          · exact hSecondLift.trans hSecond'.symm
      · rw [yOuterArm] at hOuter
        obtain ⟨a, haSource, rfl⟩ := Finset.mem_image.mp hOuter
        obtain ⟨haH, haU, har⟩ := Finset.mem_filter.mp haSource
        let ap : Punctured e := ⟨a, fun hae => heH (hae ▸ haH)⟩
        have hapLe : ap ≤ r := har
        have hrSet : insert r C₀ ∈ P := by
          rw [hclass, yFamily]
          apply Finset.mem_union_left
          apply Finset.mem_union_right
          rw [yOuterArm]
          exact Finset.mem_image.mpr
            ⟨r, Finset.mem_filter.mpr ⟨hrGP, hrU₀, le_rfl⟩, rfl⟩
        have hrC₀ : r ∉ C₀ := by
          intro hrC
          have hrValC : r.val ∈ C := hCLift ▸ (val_mem_lift_iff r C₀).mpr hrC
          exact hrU (hCsubU hrValC)
        have hapC₀ : ap ∉ C₀ := by
          intro haC
          have haValC : ap.val ∈ C := hCLift ▸ (val_mem_lift_iff ap C₀).mpr haC
          exact haU (hCsubU haValC)
        have hapSet : insert ap C₀ ∈ P := by
          by_cases hEq : ap = r
          · simpa [hEq] using hrSet
          · exact outerArm_down_closed hP hrSet hrC₀ hapC₀
              (lt_of_le_of_ne hapLe hEq)
        apply Finset.mem_image.mpr
        refine ⟨insert ap C₀, hapSet, ?_⟩
        calc
          liftPuncturedSet (insert ap C₀) = insert ap.val (liftPuncturedSet C₀) := by
            ext x
            simp [liftPuncturedSet]
          _ = insert a C := by rw [hCLift]
    · rw [yInnerArm] at hQ
      obtain ⟨i, hiSource, rfl⟩ := Finset.mem_image.mp hQ
      obtain ⟨hiC, hsi⟩ := Finset.mem_filter.mp hiSource
      have hiH : i ∈ H := initialSegment_subset H (k + 1) (hCsubU hiC)
      let ip : Punctured e := ⟨i, fun hie => heH (hie ▸ hiH)⟩
      have hipC₀ : ip ∈ C₀ := by
        have : i ∈ liftPuncturedSet C₀ := hCLift.symm ▸ hiC
        exact (val_mem_lift_iff ip C₀).mp this
      have hsSet : U₀.erase s ∈ P := by
        rw [hclass, yFamily]
        apply Finset.mem_union_right
        rw [yInnerArm]
        exact Finset.mem_image.mpr
          ⟨s, Finset.mem_filter.mpr ⟨hsC₀, le_rfl⟩, rfl⟩
      have hipSet : U₀.erase ip ∈ P := by
        by_cases hEq : s = ip
        · simpa [hEq] using hsSet
        · exact innerArm_up_closed hP hsSet
            (initialSegment_mono GP (by omega) hsC₀)
            (initialSegment_mono GP (by omega) hipC₀)
            (lt_of_le_of_ne hsi hEq)
      apply Finset.mem_image.mpr
      refine ⟨U₀.erase ip, hipSet, ?_⟩
      calc
        liftPuncturedSet (U₀.erase ip) = (liftPuncturedSet U₀).erase ip.val := by
          ext x
          simp [liftPuncturedSet]
        _ = U.erase i := by rw [hULift]

/-- An avoiding layer that is a clique-sum, classified on the punctured ground and read back in
the original type. -/
theorem layerBelow_cliqueSum_yFamily_row
    {F : Finset (Finset α)} {k : ℕ} {e : α}
    (hF : IsShifted F k) (hne : (layerBelow F e).Nonempty)
    {u v : ExchangeV (puncturedLower F e)}
    (hbad : IsCliqueSum (puncturedLower F e) u v) :
    ∃ r s : Punctured e,
      r.val ∈ (usedGround F).erase e ∧
      r.val ∉ initialSegment ((usedGround F).erase e) (k + 1) ∧
      s.val ∈ initialSegment ((usedGround F).erase e) (k - 1) ∧
      layerBelow F e = yFamily ((usedGround F).erase e) k r.val s.val := by
  let H := (usedGround F).erase e
  have hP := isShifted_puncturedLower hF hne
  have hPH : ∀ X ∈ puncturedLower F e, liftPuncturedSet X ⊆ H := by
    intro X hX x hx
    apply Finset.mem_erase.mpr
    refine ⟨?_, ?_⟩
    · obtain ⟨xp, _hxp, hval⟩ := Finset.mem_map.mp hx
      exact hval ▸ xp.property
    · rw [usedGround, Finset.mem_biUnion]
      exact ⟨liftPuncturedSet X, mem_puncturedLower_iff.mp hX, hx⟩
  obtain ⟨r, s, hrH, hrU, hsC, hclass⟩ :=
    punctured_cliqueSum_lift_eq_yFamily hP hPH (Finset.notMem_erase _ _) hbad
  refine ⟨r, s, hrH, hrU, hsC, ?_⟩
  change layerBelow F e = yFamily H k r.val s.val
  rw [← hclass]
  ext X
  constructor
  · intro hX
    apply Finset.mem_image.mpr
    refine ⟨punctureSet e X, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨X, hX, rfl⟩
    · exact liftPuncturedSet_punctureSet_of_notMem (Finset.mem_filter.mp hX).2
  · intro hX
    obtain ⟨Xp, hXp, rfl⟩ := Finset.mem_image.mp hX
    exact Finset.mem_filter.mpr
      ⟨mem_puncturedLower_iff.mp hXp, by simp [liftPuncturedSet]⟩

/-- A link that is a clique-sum, classified on the punctured ground and lifted back into the
containing layer. -/
theorem link_cliqueSum_yFamily_row
    {F : Finset (Finset α)} {k : ℕ} {e : α}
    (hF : IsShifted F k) (hne : (layerAbove F e).Nonempty)
    {u v : ExchangeV (puncturedLink F e)}
    (hbad : IsCliqueSum (puncturedLink F e) u v) :
    ∃ r s : Punctured e,
      r.val ∈ (usedGround F).erase e ∧
      r.val ∉ initialSegment ((usedGround F).erase e) k ∧
      s.val ∈ initialSegment ((usedGround F).erase e) (k - 2) ∧
      layerAbove F e =
        (yFamily ((usedGround F).erase e) (k - 1) r.val s.val).image
          (fun X => insert e X) := by
  let H := (usedGround F).erase e
  have hP := isShifted_puncturedLink hF hne
  have hPH : ∀ X ∈ puncturedLink F e, liftPuncturedSet X ⊆ H := by
    intro X hX x hx
    apply Finset.mem_erase.mpr
    refine ⟨?_, ?_⟩
    · obtain ⟨xp, _hxp, hval⟩ := Finset.mem_map.mp hx
      exact hval ▸ xp.property
    · rw [usedGround, Finset.mem_biUnion]
      exact ⟨insert e (liftPuncturedSet X), mem_puncturedLink_iff.mp hX,
        Finset.mem_insert_of_mem hx⟩
  obtain ⟨r, s, hrH, hrU, hsC, hclass⟩ :=
    punctured_cliqueSum_lift_eq_yFamily hP hPH (Finset.notMem_erase _ _) hbad
  have hk : 2 ≤ k := by
    have hslt : groundRank H s.val < k - 1 - 1 := (Finset.mem_filter.mp hsC).2
    omega
  have hrU' : r.val ∉ initialSegment H k := by
    have harith : k - 1 + 1 = k := by
      omega
    rwa [harith] at hrU
  have hsC' : s.val ∈ initialSegment H (k - 2) := by
    have harith : k - 1 - 1 = k - 2 := by omega
    rwa [harith] at hsC
  refine ⟨r, s, hrH, hrU', hsC', ?_⟩
  change layerAbove F e = (yFamily H (k - 1) r.val s.val).image fun X => insert e X
  rw [← hclass]
  ext X
  constructor
  · intro hX
    apply Finset.mem_image.mpr
    refine ⟨liftPuncturedSet (punctureSet e X), ?_, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨punctureSet e X, Finset.mem_image.mpr ⟨X, hX, rfl⟩, rfl⟩
    · rw [liftPuncturedSet_punctureSet, Finset.insert_erase (Finset.mem_filter.mp hX).2]
  · intro hX
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨Xp, hXp, rfl⟩ := Finset.mem_image.mp hY
    exact Finset.mem_filter.mpr
      ⟨mem_puncturedLink_iff.mp hXp, Finset.mem_insert_self _ _⟩

/-- The ambient-coordinate outer arm in the `F⁰` yFamily row at `e = k`. -/
def lowerOuterArmAtK (G : Finset α) (k : ℕ) (r : α) : Finset (Finset α) :=
  (G.filter fun a => a ∉ initialSegment G (k + 2) ∧ a ≤ r).image
    fun a => insert a (initialSegment G (k - 1))

/-- The ambient-coordinate inner arm in the `F⁰` yFamily row at `e = k`. -/
def lowerInnerArmAtK (G : Finset α) (k : ℕ) (e s : α) : Finset (Finset α) :=
  ((initialSegment G (k - 1)).filter fun i => s ≤ i).image
    fun i => ((initialSegment G (k + 2)).erase e).erase i

/-- The `F⁰` yFamily-arm row at `e = k`, in the `initialSegment` encoding.  Its outer source is
exactly the original-ground interval `k+3 ≤ a ≤ r`, and its inner members are
`([k+2] \ {e}) \ {i}` for `s ≤ i ≤ k-1`. -/
theorem layerBelow_yFamily_arms_at_k
    {F : Finset (Finset α)} {k : ℕ} {e : α}
    (hF : IsShifted F k) (hne : (layerBelow F e).Nonempty)
    (heTop : e ∈ initialSegment (usedGround F) k)
    (hePrev : e ∉ initialSegment (usedGround F) (k - 1))
    {u v : ExchangeV (puncturedLower F e)}
    (hbad : IsCliqueSum (puncturedLower F e) u v) :
    ∃ r s : Punctured e,
      r.val ∈ usedGround F ∧ r.val ∉ initialSegment (usedGround F) (k + 2) ∧
      s.val ∈ initialSegment (usedGround F) (k - 1) ∧
      layerBelow F e =
        ({(initialSegment (usedGround F) (k + 1)).erase e,
            (initialSegment (usedGround F) k).erase e ∪
              groundPosition (usedGround F) (k + 2)} ∪
          lowerOuterArmAtK (usedGround F) k r.val) ∪
          lowerInnerArmAtK (usedGround F) k e s.val := by
  let G := usedGround F
  let H := G.erase e
  obtain ⟨r, s, hrH, hrOutside, hsH, hrow⟩ :=
    layerBelow_cliqueSum_yFamily_row hF hne hbad
  change r.val ∈ H at hrH
  change r.val ∉ initialSegment H (k + 1) at hrOutside
  change s.val ∈ initialSegment H (k - 1) at hsH
  change layerBelow F e = yFamily H k r.val s.val at hrow
  have heG : e ∈ G := initialSegment_subset G k heTop
  have hrRank : k + 1 ≤ groundRank H r.val := by
    exact le_of_not_gt (fun h => hrOutside (Finset.mem_filter.mpr ⟨hrH, h⟩))
  have hHcard : k + 2 ≤ H.card := by
    have := groundRank_lt_card_of_mem hrH
    omega
  have hGcard : k + 2 ≤ G.card := by
    exact hHcard.trans (Finset.card_le_card (Finset.erase_subset e G))
  have heK : e ∈ initialSegment G (k + 1) :=
    initialSegment_mono G (by omega) heTop
  have heK2 : e ∈ initialSegment G (k + 2) :=
    initialSegment_mono G (by omega) heTop
  have hCore : initialSegment H (k - 1) = initialSegment G (k - 1) :=
    initialSegment_erase_eq_self_of_notMem (by omega) hePrev
  have hBottom : initialSegment H k = (initialSegment G (k + 1)).erase e :=
    initialSegment_erase_eq_erase_succ_of_mem (by omega) heTop
  have hUpper : initialSegment H (k + 1) = (initialSegment G (k + 2)).erase e :=
    initialSegment_erase_eq_erase_succ_of_mem hGcard heK
  have hSecond : secondInitialSegment H k =
      (initialSegment G k).erase e ∪ groundPosition G (k + 2) :=
    secondInitialSegment_erase_of_mem_initial (by
      have hslt : groundRank H s.val < k - 1 := (Finset.mem_filter.mp hsH).2
      omega) (by omega) heTop
  have hrG : r.val ∈ G := Finset.mem_of_mem_erase hrH
  have hrOutsideG : r.val ∉ initialSegment G (k + 2) := by
    intro hr
    exact hrOutside (hUpper ▸ Finset.mem_erase.mpr ⟨r.property, hr⟩)
  have hsG : s.val ∈ initialSegment G (k - 1) := hCore ▸ hsH
  have hOuter : yOuterArm H k r.val = lowerOuterArmAtK G k r.val := by
    rw [yOuterArm, lowerOuterArmAtK, hCore, hUpper]
    have hSource :
        H.filter (fun a => a ∉ (initialSegment G (k + 2)).erase e ∧ a ≤ r.val) =
          G.filter (fun a => a ∉ initialSegment G (k + 2) ∧ a ≤ r.val) := by
      change (G.erase e).filter
          (fun a => a ∉ (initialSegment G (k + 2)).erase e ∧ a ≤ r.val) = _
      ext a
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨hae, haG⟩, haOut, har⟩
        exact ⟨haG, fun ha => haOut ⟨hae, ha⟩, har⟩
      · rintro ⟨haG, haOut, har⟩
        exact ⟨⟨fun hae => haOut (hae ▸ heK2), haG⟩,
          fun ha => haOut ha.2, har⟩
    rw [hSource]
  have hInner : yInnerArm H k s.val = lowerInnerArmAtK G k e s.val := by
    rw [yInnerArm, lowerInnerArmAtK, hCore, hUpper]
  refine ⟨r, s, hrG, hrOutsideG, hsG, ?_⟩
  rw [hrow, yFamily, hBottom, hSecond, hOuter, hInner]

/-- The lifted outer arm in the link rows at `e = k-1`, `k`, or `k+1`. -/
def linkOuterArmAmbient (G : Finset α) (k : ℕ) (e r : α) : Finset (Finset α) :=
  (G.filter fun a => a ∉ initialSegment G (k + 1) ∧ a ≤ r).image
    fun a => insert e (insert a (initialSegment G (k - 2)))

/-- The lifted inner arm, common to the three link rows. -/
def linkInnerArmAmbient (G : Finset α) (k : ℕ) (s : α) : Finset (Finset α) :=
  ((initialSegment G (k - 2)).filter fun i => s ≤ i).image
    fun i => (initialSegment G (k + 1)).erase i

/-- Common calculation for the link rows at `e = k-1` and `e = k`. -/
theorem link_yFamily_arms_of_mem_initial
    {F : Finset (Finset α)} {k : ℕ} {e : α}
    (hF : IsShifted F k) (hne : (layerAbove F e).Nonempty)
    (he : e ∈ initialSegment (usedGround F) k)
    (heCore : e ∉ initialSegment (usedGround F) (k - 2))
    {u v : ExchangeV (puncturedLink F e)}
    (hbad : IsCliqueSum (puncturedLink F e) u v) :
    ∃ r s : Punctured e,
      r.val ∈ usedGround F ∧ r.val ∉ initialSegment (usedGround F) (k + 1) ∧
      s.val ∈ initialSegment (usedGround F) (k - 2) ∧
      layerAbove F e =
        (yFamily ((usedGround F).erase e) (k - 1) r.val s.val).image
          (fun X => insert e X) ∧
      (yOuterArm ((usedGround F).erase e) (k - 1) r.val).image
          (fun X => insert e X) =
        linkOuterArmAmbient (usedGround F) k e r.val ∧
      (yInnerArm ((usedGround F).erase e) (k - 1) s.val).image
          (fun X => insert e X) =
        linkInnerArmAmbient (usedGround F) k s.val := by
  let G := usedGround F
  let H := G.erase e
  obtain ⟨r, s, hrH, hrOutside, hsH, hrow⟩ :=
    link_cliqueSum_yFamily_row hF hne hbad
  change r.val ∈ H at hrH
  change r.val ∉ initialSegment H k at hrOutside
  change s.val ∈ initialSegment H (k - 2) at hsH
  change layerAbove F e = (yFamily H (k - 1) r.val s.val).image
    (fun X => insert e X) at hrow
  have heG : e ∈ G := initialSegment_subset G k he
  have hrRank : k ≤ groundRank H r.val := by
    exact le_of_not_gt (fun h => hrOutside (Finset.mem_filter.mpr ⟨hrH, h⟩))
  have hHcard : k + 1 ≤ H.card := by
    have := groundRank_lt_card_of_mem hrH
    omega
  have hGcard : k + 1 ≤ G.card :=
    hHcard.trans (Finset.card_le_card (Finset.erase_subset e G))
  have hk : 2 ≤ k := by
    have hslt : groundRank H s.val < k - 2 := (Finset.mem_filter.mp hsH).2
    omega
  have heK1 : e ∈ initialSegment G (k + 1) := initialSegment_mono G (by omega) he
  have hCore : initialSegment H (k - 2) = initialSegment G (k - 2) :=
    initialSegment_erase_eq_self_of_notMem (by omega) heCore
  have hUpper : initialSegment H k = (initialSegment G (k + 1)).erase e :=
    initialSegment_erase_eq_erase_succ_of_mem hGcard he
  have hrG : r.val ∈ G := Finset.mem_of_mem_erase hrH
  have hrOutsideG : r.val ∉ initialSegment G (k + 1) := by
    intro hr
    exact hrOutside (hUpper ▸ Finset.mem_erase.mpr ⟨r.property, hr⟩)
  have hsG : s.val ∈ initialSegment G (k - 2) := hCore ▸ hsH
  have hOuter : (yOuterArm H (k - 1) r.val).image (fun X => insert e X) =
      linkOuterArmAmbient G k e r.val := by
    have harith₁ : k - 1 - 1 = k - 2 := by omega
    have harith₂ : k - 1 + 1 = k := by omega
    rw [yOuterArm, linkOuterArmAmbient, harith₁, harith₂, hCore, hUpper]
    have hSource :
        H.filter (fun a => a ∉ (initialSegment G (k + 1)).erase e ∧ a ≤ r.val) =
          G.filter (fun a => a ∉ initialSegment G (k + 1) ∧ a ≤ r.val) := by
      change (G.erase e).filter
          (fun a => a ∉ (initialSegment G (k + 1)).erase e ∧ a ≤ r.val) = _
      ext a
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨hae, haG⟩, haOut, har⟩
        exact ⟨haG, fun ha => haOut ⟨hae, ha⟩, har⟩
      · rintro ⟨haG, haOut, har⟩
        exact ⟨⟨fun hae => haOut (hae ▸ heK1), haG⟩, fun ha => haOut ha.2, har⟩
    rw [hSource]
    ext X
    constructor
    · intro hX
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hX
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hY
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    · intro hX
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hX
      exact Finset.mem_image.mpr
        ⟨insert a (initialSegment G (k - 2)), Finset.mem_image.mpr ⟨a, ha, rfl⟩, rfl⟩
  have hInner : (yInnerArm H (k - 1) s.val).image (fun X => insert e X) =
      linkInnerArmAmbient G k s.val := by
    have harith₁ : k - 1 - 1 = k - 2 := by omega
    have harith₂ : k - 1 + 1 = k := by omega
    rw [yInnerArm, linkInnerArmAmbient, harith₁, harith₂, hCore, hUpper]
    ext X
    constructor
    · intro hX
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hX
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hY
      apply Finset.mem_image.mpr
      refine ⟨i, hi, ?_⟩
      have hie : i ≠ e := fun hie => heCore (hie ▸ (Finset.mem_filter.mp hi).1)
      symm
      ext x
      simp only [Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro (rfl | ⟨hxi, hxe, hxU⟩)
        · exact ⟨Ne.symm hie, heK1⟩
        · exact ⟨hxi, hxU⟩
      · rintro ⟨hxi, hxU⟩
        by_cases hxe : x = e
        · exact Or.inl hxe
        · exact Or.inr ⟨hxi, hxe, hxU⟩
    · intro hX
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hX
      apply Finset.mem_image.mpr
      refine ⟨((initialSegment G (k + 1)).erase e).erase i, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
      · have hie : i ≠ e := fun hie => heCore (hie ▸ (Finset.mem_filter.mp hi).1)
        ext x
        simp only [Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro (rfl | ⟨hxi, hxe, hxU⟩)
          · exact ⟨Ne.symm hie, heK1⟩
          · exact ⟨hxi, hxU⟩
        · rintro ⟨hxi, hxU⟩
          by_cases hxe : x = e
          · exact Or.inl hxe
          · exact Or.inr ⟨hxi, hxe, hxU⟩
  exact ⟨r, s, hrG, hrOutsideG, hsG, hrow, hOuter, hInner⟩

/-- The lifted-link yFamily-arm row at `e = k`. -/
theorem link_yFamily_arms_at_k
    {F : Finset (Finset α)} {k : ℕ} {e : α}
    (hF : IsShifted F k) (hne : (layerAbove F e).Nonempty)
    (heTop : e ∈ initialSegment (usedGround F) k)
    (hePrev : e ∉ initialSegment (usedGround F) (k - 1))
    {u v : ExchangeV (puncturedLink F e)}
    (hbad : IsCliqueSum (puncturedLink F e) u v) :
    ∃ r s : Punctured e,
      r.val ∈ usedGround F ∧ r.val ∉ initialSegment (usedGround F) (k + 1) ∧
      s.val ∈ initialSegment (usedGround F) (k - 2) ∧
      layerAbove F e =
        (yFamily ((usedGround F).erase e) (k - 1) r.val s.val).image
          (fun X => insert e X) ∧
      (yOuterArm ((usedGround F).erase e) (k - 1) r.val).image
          (fun X => insert e X) =
        linkOuterArmAmbient (usedGround F) k e r.val ∧
      (yInnerArm ((usedGround F).erase e) (k - 1) s.val).image
          (fun X => insert e X) =
        linkInnerArmAmbient (usedGround F) k s.val := by
  apply link_yFamily_arms_of_mem_initial hF hne heTop
  · intro heCore
    exact hePrev (initialSegment_mono (usedGround F) (by omega) heCore)
  · exact hbad

/-- At `e = k-1`, the displayed lifted outer sets simplify from
`[k-2] ∪ {e,a}` to `[k-1] ∪ {a}`. -/
def linkOuterArmAtPred (G : Finset α) (k : ℕ) (r : α) : Finset (Finset α) :=
  (G.filter fun a => a ∉ initialSegment G (k + 1) ∧ a ≤ r).image
    fun a => insert a (initialSegment G (k - 1))

/-- The lifted-link yFamily-arm row at `e = k-1`. -/
theorem link_yFamily_arms_at_k_pred
    {F : Finset (Finset α)} {k : ℕ} {e : α}
    (hF : IsShifted F k) (hne : (layerAbove F e).Nonempty)
    (heTop : e ∈ initialSegment (usedGround F) (k - 1))
    (hePrev : e ∉ initialSegment (usedGround F) (k - 2))
    {u v : ExchangeV (puncturedLink F e)}
    (hbad : IsCliqueSum (puncturedLink F e) u v) :
    ∃ r s : Punctured e,
      r.val ∈ usedGround F ∧ r.val ∉ initialSegment (usedGround F) (k + 1) ∧
      s.val ∈ initialSegment (usedGround F) (k - 2) ∧
      layerAbove F e =
        (yFamily ((usedGround F).erase e) (k - 1) r.val s.val).image
          (fun X => insert e X) ∧
      (yOuterArm ((usedGround F).erase e) (k - 1) r.val).image
          (fun X => insert e X) = linkOuterArmAtPred (usedGround F) k r.val ∧
      (yInnerArm ((usedGround F).erase e) (k - 1) s.val).image
          (fun X => insert e X) = linkInnerArmAmbient (usedGround F) k s.val := by
  let G := usedGround F
  have heK : e ∈ initialSegment G k := initialSegment_mono G (by omega) heTop
  obtain ⟨r, s, hrG, hrOut, hsG, hrow, hOuter, hInner⟩ :=
    link_yFamily_arms_of_mem_initial hF hne heK hePrev hbad
  change r.val ∈ G at hrG
  change r.val ∉ initialSegment G (k + 1) at hrOut
  change s.val ∈ initialSegment G (k - 2) at hsG
  have hrRank : k + 1 ≤ groundRank G r.val := by
    exact le_of_not_gt (fun h => hrOut (Finset.mem_filter.mpr ⟨hrG, h⟩))
  have hGcard : k + 2 ≤ G.card := by
    have := groundRank_lt_card_of_mem hrG
    omega
  have hk : 3 ≤ k := by
    have hslt : groundRank G s.val < k - 2 := (Finset.mem_filter.mp hsG).2
    omega
  have hInsert : insert e (initialSegment G (k - 2)) = initialSegment G (k - 1) := by
    have harith : k - 2 + 1 = k - 1 := by omega
    have heTop' : e ∈ initialSegment G (k - 2 + 1) := by rwa [harith]
    simpa [harith] using initialSegment_insert_eq_succ_of_top
      (G := G) (e := e) (j := k - 2) (by omega) heTop' hePrev
  have hOuter' : linkOuterArmAmbient G k e r.val = linkOuterArmAtPred G k r.val := by
    rw [linkOuterArmAmbient, linkOuterArmAtPred]
    apply Finset.image_congr
    intro a ha
    change insert e (insert a (initialSegment G (k - 2))) =
      insert a (initialSegment G (k - 1))
    rw [Finset.insert_comm e a, hInsert]
  exact ⟨r, s, hrG, hrOut, hsG, hrow, hOuter.trans hOuter', hInner⟩

/-- The lifted-link yFamily-arm row at `e = k+1` (the optional fourth row in the checker). -/
theorem link_yFamily_arms_at_k_succ
    {F : Finset (Finset α)} {k : ℕ} {e : α}
    (hF : IsShifted F k) (hne : (layerAbove F e).Nonempty)
    (heTop : e ∈ initialSegment (usedGround F) (k + 1))
    (hePrev : e ∉ initialSegment (usedGround F) k)
    {u v : ExchangeV (puncturedLink F e)}
    (hbad : IsCliqueSum (puncturedLink F e) u v) :
    ∃ r s : Punctured e,
      r.val ∈ usedGround F ∧ r.val ∉ initialSegment (usedGround F) (k + 1) ∧
      s.val ∈ initialSegment (usedGround F) (k - 2) ∧
      layerAbove F e =
        (yFamily ((usedGround F).erase e) (k - 1) r.val s.val).image
          (fun X => insert e X) ∧
      (yOuterArm ((usedGround F).erase e) (k - 1) r.val).image
          (fun X => insert e X) =
        linkOuterArmAmbient (usedGround F) k e r.val ∧
      (yInnerArm ((usedGround F).erase e) (k - 1) s.val).image
          (fun X => insert e X) =
        linkInnerArmAmbient (usedGround F) k s.val := by
  let G := usedGround F
  let H := G.erase e
  obtain ⟨r, s, hrH, hrOutside, hsH, hrow⟩ := link_cliqueSum_yFamily_row hF hne hbad
  change r.val ∈ H at hrH
  change r.val ∉ initialSegment H k at hrOutside
  change s.val ∈ initialSegment H (k - 2) at hsH
  change layerAbove F e = (yFamily H (k - 1) r.val s.val).image
    (fun X => insert e X) at hrow
  have heG : e ∈ G := initialSegment_subset G (k + 1) heTop
  have hrRank : k ≤ groundRank H r.val := by
    exact le_of_not_gt (fun h => hrOutside (Finset.mem_filter.mpr ⟨hrH, h⟩))
  have hHcard : k + 1 ≤ H.card := by
    have := groundRank_lt_card_of_mem hrH
    omega
  have hGcard : k + 1 ≤ G.card :=
    hHcard.trans (Finset.card_le_card (Finset.erase_subset e G))
  have hk : 3 ≤ k := by
    have hslt : groundRank H s.val < k - 2 := (Finset.mem_filter.mp hsH).2
    omega
  have heCore : e ∉ initialSegment G (k - 2) := fun h =>
    hePrev (initialSegment_mono G (by omega) h)
  have hCore : initialSegment H (k - 2) = initialSegment G (k - 2) :=
    initialSegment_erase_eq_self_of_notMem (by omega) heCore
  have hUpper : initialSegment H k = initialSegment G k :=
    initialSegment_erase_eq_self_of_notMem (by omega) hePrev
  have hInsert : insert e (initialSegment G k) = initialSegment G (k + 1) :=
    initialSegment_insert_eq_succ_of_top hGcard heTop hePrev
  have hrG : r.val ∈ G := Finset.mem_of_mem_erase hrH
  have hrOutsideG : r.val ∉ initialSegment G (k + 1) := by
    intro hr
    have hrInsert : r.val ∈ insert e (initialSegment G k) := hInsert.symm ▸ hr
    rcases Finset.mem_insert.mp hrInsert with hre | hrK
    · exact r.property hre
    · exact hrOutside (hUpper ▸ hrK)
  have hsG : s.val ∈ initialSegment G (k - 2) := hCore ▸ hsH
  have hOuter : (yOuterArm H (k - 1) r.val).image (fun X => insert e X) =
      linkOuterArmAmbient G k e r.val := by
    have harith₁ : k - 1 - 1 = k - 2 := by omega
    have harith₂ : k - 1 + 1 = k := by omega
    rw [yOuterArm, linkOuterArmAmbient, harith₁, harith₂, hCore, hUpper]
    have hSource :
        H.filter (fun a => a ∉ initialSegment G k ∧ a ≤ r.val) =
          G.filter (fun a => a ∉ initialSegment G (k + 1) ∧ a ≤ r.val) := by
      change (G.erase e).filter (fun a => a ∉ initialSegment G k ∧ a ≤ r.val) = _
      ext a
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨hae, haG⟩, haK, har⟩
        refine ⟨haG, ?_, har⟩
        intro haK1
        have haInsert : a ∈ insert e (initialSegment G k) := hInsert.symm ▸ haK1
        rcases Finset.mem_insert.mp haInsert with hae' | ha
        · exact hae hae'
        · exact haK ha
      · rintro ⟨haG, haK1, har⟩
        exact ⟨⟨fun hae => haK1 (hae ▸ heTop), haG⟩,
          fun ha => haK1 (initialSegment_mono G (by omega) ha), har⟩
    rw [hSource]
    ext X
    constructor
    · intro hX
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hX
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hY
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    · intro hX
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hX
      exact Finset.mem_image.mpr
        ⟨insert a (initialSegment G (k - 2)), Finset.mem_image.mpr ⟨a, ha, rfl⟩, rfl⟩
  have hInner : (yInnerArm H (k - 1) s.val).image (fun X => insert e X) =
      linkInnerArmAmbient G k s.val := by
    have harith₁ : k - 1 - 1 = k - 2 := by omega
    have harith₂ : k - 1 + 1 = k := by omega
    rw [yInnerArm, linkInnerArmAmbient, harith₁, harith₂, hCore, hUpper]
    ext X
    constructor
    · intro hX
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hX
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hY
      apply Finset.mem_image.mpr
      refine ⟨i, hi, ?_⟩
      have hie : i ≠ e := fun hie => heCore (hie ▸ (Finset.mem_filter.mp hi).1)
      have hei : e ≠ i := Ne.symm hie
      ext x
      rw [← hInsert]
      simp only [Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨hxi, hxe | hxK⟩
        · exact Or.inl hxe
        · exact Or.inr ⟨hxi, hxK⟩
      · rintro (hxe | ⟨hxi, hxK⟩)
        · subst x
          exact ⟨hei, Or.inl rfl⟩
        · exact ⟨hxi, Or.inr hxK⟩
    · intro hX
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hX
      apply Finset.mem_image.mpr
      refine ⟨(initialSegment G k).erase i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, ?_⟩
      have hie : i ≠ e := fun hie => heCore (hie ▸ (Finset.mem_filter.mp hi).1)
      have hei : e ≠ i := Ne.symm hie
      ext x
      rw [← hInsert]
      simp only [Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro (hxe | ⟨hxi, hxK⟩)
        · subst x
          exact ⟨hei, Or.inl rfl⟩
        · exact ⟨hxi, Or.inr hxK⟩
      · rintro ⟨hxi, hxe | hxK⟩
        · exact Or.inl hxe
        · exact Or.inr ⟨hxi, hxK⟩
  exact ⟨r, s, hrG, hrOutsideG, hsG, hrow, hOuter, hInner⟩

private theorem card_punctureSet_symmDiff {e : α} {A B : Finset α}
    (he : e ∈ A ↔ e ∈ B) :
    (punctureSet e A ∆ punctureSet e B).card = (A ∆ B).card := by
  have hnot : e ∉ A ∆ B := by
    intro h
    rw [Finset.mem_symmDiff] at h
    rcases h with ⟨heA, heB⟩ | ⟨heB, heA⟩
    · exact heB (he.mp heA)
    · exact heA (he.mpr heB)
  have heq : punctureSet e A ∆ punctureSet e B = punctureSet e (A ∆ B) := by
    ext x
    simp only [Finset.mem_symmDiff, punctureSet, Finset.mem_subtype]
  rw [heq]
  have hc := congrArg Finset.card (liftPuncturedSet_punctureSet_of_notMem hnot)
  simpa [liftPuncturedSet] using hc

private def lowerVertexEquiv (F : Finset (Finset α)) (e : α) :
    ExchangeV (layerBelow F e) ≃ ExchangeV (puncturedLower F e) where
  toFun X := ⟨punctureSet e X.val, Finset.mem_image.mpr ⟨X.val, X.prop, rfl⟩⟩
  invFun X := ⟨liftPuncturedSet X.val, Finset.mem_filter.mpr
    ⟨mem_puncturedLower_iff.mp X.prop, by simp [liftPuncturedSet]⟩⟩
  left_inv X := by
    apply Subtype.ext
    exact liftPuncturedSet_punctureSet_of_notMem (Finset.mem_filter.mp X.prop).2
  right_inv X := by
    apply Subtype.ext
    exact punctureSet_liftPuncturedSet X.val

private def linkVertexEquiv (F : Finset (Finset α)) (e : α) :
    ExchangeV (layerAbove F e) ≃ ExchangeV (puncturedLink F e) where
  toFun X := ⟨punctureSet e X.val, Finset.mem_image.mpr ⟨X.val, X.prop, rfl⟩⟩
  invFun X := ⟨insert e (liftPuncturedSet X.val), by
    change insert e (liftPuncturedSet X.val) ∈ F.filter (fun X => e ∈ X)
    exact Finset.mem_filter.mpr
      ⟨mem_puncturedLink_iff.mp X.prop, Finset.mem_insert_self _ _⟩⟩
  left_inv X := by
    apply Subtype.ext
    change insert e (liftPuncturedSet (punctureSet e X.val)) = X.val
    rw [liftPuncturedSet_punctureSet]
    exact Finset.insert_erase (Finset.mem_filter.mp X.prop).2
  right_inv X := by
    apply Subtype.ext
    change punctureSet e (insert e (liftPuncturedSet X.val)) = X.val
    ext x
    simp [punctureSet, liftPuncturedSet, x.property]

private def exchangeGraph_puncturedLowerIso (F : Finset (Finset α)) (e : α) :
    exchangeGraph (layerBelow F e) ≃g exchangeGraph (puncturedLower F e) where
  toEquiv := lowerVertexEquiv F e
  map_rel_iff' := by
    intro A B
    simp only [exchangeGraph, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨hne, hcard⟩
      refine ⟨by simpa using hne, ?_⟩
      change ((punctureSet e A.val ∆ punctureSet e B.val).card = 2 ∨
        (punctureSet e B.val ∆ punctureSet e A.val).card = 2) at hcard
      rw [card_punctureSet_symmDiff,
        card_punctureSet_symmDiff] at hcard
      · exact hcard
      · exact iff_of_false (Finset.mem_filter.mp B.prop).2 (Finset.mem_filter.mp A.prop).2
      · exact iff_of_false (Finset.mem_filter.mp A.prop).2 (Finset.mem_filter.mp B.prop).2
    · rintro ⟨hne, hcard⟩
      refine ⟨by simpa using hne, ?_⟩
      change ((punctureSet e A.val ∆ punctureSet e B.val).card = 2 ∨
        (punctureSet e B.val ∆ punctureSet e A.val).card = 2)
      rw [card_punctureSet_symmDiff,
        card_punctureSet_symmDiff]
      · exact hcard
      · exact iff_of_false (Finset.mem_filter.mp B.prop).2 (Finset.mem_filter.mp A.prop).2
      · exact iff_of_false (Finset.mem_filter.mp A.prop).2 (Finset.mem_filter.mp B.prop).2

private def exchangeGraph_puncturedLinkIso (F : Finset (Finset α)) (e : α) :
    exchangeGraph (layerAbove F e) ≃g exchangeGraph (puncturedLink F e) where
  toEquiv := linkVertexEquiv F e
  map_rel_iff' := by
    intro A B
    simp only [exchangeGraph, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨hne, hcard⟩
      refine ⟨by simpa using hne, ?_⟩
      change ((punctureSet e A.val ∆ punctureSet e B.val).card = 2 ∨
        (punctureSet e B.val ∆ punctureSet e A.val).card = 2) at hcard
      rw [card_punctureSet_symmDiff,
        card_punctureSet_symmDiff] at hcard
      · exact hcard
      · exact iff_of_true (Finset.mem_filter.mp B.prop).2 (Finset.mem_filter.mp A.prop).2
      · exact iff_of_true (Finset.mem_filter.mp A.prop).2 (Finset.mem_filter.mp B.prop).2
    · rintro ⟨hne, hcard⟩
      refine ⟨by simpa using hne, ?_⟩
      change ((punctureSet e A.val ∆ punctureSet e B.val).card = 2 ∨
        (punctureSet e B.val ∆ punctureSet e A.val).card = 2)
      rw [card_punctureSet_symmDiff,
        card_punctureSet_symmDiff]
      · exact hcard
      · exact iff_of_true (Finset.mem_filter.mp B.prop).2 (Finset.mem_filter.mp A.prop).2
      · exact iff_of_true (Finset.mem_filter.mp A.prop).2 (Finset.mem_filter.mp B.prop).2

private def familyGround (F : Finset (Finset α)) : Finset α := F.biUnion id

private theorem punctured_familyGround_lt {F : Finset (Finset α)} {e : α}
    {P : Finset (Finset (Punctured e))}
    (hP : ∀ X ∈ P,
      liftPuncturedSet X ∈ F ∨ insert e (liftPuncturedSet X) ∈ F)
    (he : e ∈ familyGround F) :
    (familyGround P).card < (familyGround F).card := by
  have hsub :
      (familyGround P).map (Function.Embedding.subtype _) ⊆ (familyGround F).erase e := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    apply Finset.mem_erase.mpr
    refine ⟨y.property, ?_⟩
    rw [familyGround, Finset.mem_biUnion] at hy ⊢
    obtain ⟨X, hXP, hyX⟩ := hy
    rcases hP X hXP with hXF | hXF
    · exact ⟨liftPuncturedSet X, hXF,
        Finset.mem_map.mpr ⟨y, hyX, rfl⟩⟩
    · exact ⟨insert e (liftPuncturedSet X), hXF,
        Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨y, hyX, rfl⟩)⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_map] at hle
  have hlt : ((familyGround F).erase e).card < (familyGround F).card := by
    rw [Finset.card_erase_of_mem he]
    have hpos := Finset.card_pos.mpr ⟨e, he⟩
    omega
  omega

private theorem puncturedLower_familyGround_lt {F : Finset (Finset α)} {e : α}
    (he : e ∈ familyGround F) :
    (familyGround (puncturedLower F e)).card < (familyGround F).card := by
  apply punctured_familyGround_lt (P := puncturedLower F e) (fun X hX => ?_) he
  exact Or.inl (mem_puncturedLower_iff.mp hX)

private theorem puncturedLink_familyGround_lt {F : Finset (Finset α)} {e : α}
    (he : e ∈ familyGround F) :
    (familyGround (puncturedLink F e)).card < (familyGround F).card := by
  apply punctured_familyGround_lt (P := puncturedLink F e) (fun X hX => ?_) he
  exact Or.inr (mem_puncturedLink_iff.mp hX)

private theorem hasHamPath_iso_iff {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H) (u v : V) :
    HasHamPath G u v ↔ HasHamPath H (φ u) (φ v) := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.map φ.toHom, hp.map φ.toHom φ.toEquiv.bijective⟩
  · rintro ⟨p, hp⟩
    have h : HasHamPath G (φ.symm (φ u)) (φ.symm (φ v)) :=
      ⟨p.map φ.symm.toHom, hp.map φ.symm.toHom φ.symm.toEquiv.bijective⟩
    simpa using h

private def layerAboveHom (F : Finset (Finset α)) (e : α) :
    exchangeGraph (layerAbove F e) →g exchangeGraph F where
  toFun X := ⟨X.val, (Finset.mem_filter.mp X.prop).1⟩
  map_rel' := by
    intro X Y h
    simpa [exchangeGraph] using h

private def layerBelowHom (F : Finset (Finset α)) (e : α) :
    exchangeGraph (layerBelow F e) →g exchangeGraph F where
  toFun X := ⟨X.val, (Finset.mem_filter.mp X.prop).1⟩
  map_rel' := by
    intro X Y h
    simpa [exchangeGraph] using h

private theorem layerAboveHom_injective (F : Finset (Finset α)) (e : α) :
    Function.Injective (layerAboveHom F e) := by
  intro X Y h
  apply Subtype.ext
  exact congrArg (fun z : ExchangeV F => z.val) h

private theorem layerBelowHom_injective (F : Finset (Finset α)) (e : α) :
    Function.Injective (layerBelowHom F e) := by
  intro X Y h
  apply Subtype.ext
  exact congrArg (fun z : ExchangeV F => z.val) h

/-- The two recursive Hamilton paths splice across the crossing edge. -/
private theorem hamPath_of_layer_splice {F : Finset (Finset α)} {e : α}
    (A Y : ExchangeV (layerAbove F e)) (X B : ExchangeV (layerBelow F e))
    (hAY : HasHamPath (exchangeGraph (layerAbove F e)) A Y)
    (hXB : HasHamPath (exchangeGraph (layerBelow F e)) X B)
    (hYX : (exchangeGraph F).Adj (layerAboveHom F e Y) (layerBelowHom F e X)) :
    HasHamPath (exchangeGraph F) (layerAboveHom F e A) (layerBelowHom F e B) := by
  rcases hAY with ⟨p, hp⟩
  rcases hXB with ⟨q, hq⟩
  let P := p.map (layerAboveHom F e)
  let Q := q.map (layerBelowHom F e)
  apply hamPath_of_two_walk_splice P Q
  · exact SimpleGraph.Walk.map_isPath_of_injective
      (layerAboveHom_injective F e) hp.isPath
  · exact SimpleGraph.Walk.map_isPath_of_injective
      (layerBelowHom_injective F e) hq.isPath
  · exact hYX
  · intro z hz
    rcases hz with ⟨hzP, hzQ⟩
    simp only [P, SimpleGraph.Walk.support_map] at hzP
    simp only [Q, SimpleGraph.Walk.support_map] at hzQ
    obtain ⟨a, ha, haz⟩ := List.mem_map.mp hzP
    obtain ⟨b, hb, hbz⟩ := List.mem_map.mp hzQ
    have hez : e ∈ z.val := by
      rw [← congrArg Subtype.val haz]
      exact (Finset.mem_filter.mp a.prop).2
    have hnez : e ∉ z.val := by
      rw [← congrArg Subtype.val hbz]
      exact (Finset.mem_filter.mp b.prop).2
    exact hnez hez
  · intro z
    by_cases hez : e ∈ z.val
    · left
      simp only [P, SimpleGraph.Walk.support_map]
      let zA : ExchangeV (layerAbove F e) :=
        ⟨z.val, Finset.mem_filter.mpr ⟨z.prop, hez⟩⟩
      exact List.mem_map.mpr ⟨zA, hp.mem_support zA, by apply Subtype.ext; rfl⟩
    · right
      simp only [Q, SimpleGraph.Walk.support_map]
      let zB : ExchangeV (layerBelow F e) :=
        ⟨z.val, Finset.mem_filter.mpr ⟨z.prop, hez⟩⟩
      exact List.mem_map.mpr ⟨zB, hq.mem_support zB, by apply Subtype.ext; rfl⟩

private theorem nodup_isChain_of_complete {V : Type*} {G : SimpleGraph V}
    (hcomplete : ∀ x y : V, x ≠ y → G.Adj x y) :
    ∀ {l : List V}, l.Nodup → l.IsChain G.Adj
  | [], _ => .nil
  | [_], _ => .singleton _
  | x :: y :: zs, h => by
      apply List.IsChain.cons_cons
      · apply hcomplete x y
        intro hxy
        exact (List.nodup_cons.mp h).1 (by simp [hxy])
      · exact nodup_isChain_of_complete hcomplete (List.nodup_cons.mp h).2

private theorem hasHamPath_of_complete {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hcomplete : ∀ x y : V, x ≠ y → G.Adj x y)
    (u v : V) (huv : u ≠ v) : HasHamPath G u v := by
  let route : List V := u :: (((Finset.univ.erase u).erase v).toList ++ [v])
  have hrouteNe : route ≠ [] := by simp [route]
  have hrouteNodup : route.Nodup := by
    rw [show route = u :: (((Finset.univ.erase u).erase v).toList ++ [v]) from rfl,
      List.nodup_cons]
    refine ⟨by simp [huv], ?_⟩
    rw [List.nodup_append]
    refine ⟨Finset.nodup_toList _, by simp, ?_⟩
    intro x hx y hy hxy
    simp only [List.mem_singleton] at hy
    subst y
    subst x
    simpa using hx
  have hrouteChain : route.IsChain G.Adj :=
    nodup_isChain_of_complete hcomplete hrouteNodup
  have hhead : route.head hrouteNe = u := by simp [route]
  have hlast : route.getLast hrouteNe = v := by simp [route]
  let p : G.Walk u v :=
    (SimpleGraph.Walk.ofSupport route hrouteNe hrouteChain).copy hhead hlast
  refine ⟨p, ?_⟩
  have hpath : p.IsPath := SimpleGraph.Walk.IsPath.mk' (by
    simpa [p, SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_ofSupport] using hrouteNodup)
  apply hpath.isHamiltonian_of_mem
  intro z
  have hz : z ∈ route := by
    by_cases hzu : z = u
    · simp [route, hzu]
    by_cases hzv : z = v
    · simp [route, hzv]
    · simp [route, hzu, hzv]
  simpa [p, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_ofSupport] using hz

private theorem exchangeGraph_complete_of_rank_le_one {F : Finset (Finset α)} {κ : ℕ}
    (hF : IsShifted F κ) (hκ : κ ≤ 1) :
    ∀ A B : ExchangeV F, A ≠ B → (exchangeGraph F).Adj A B := by
  intro A B hAB
  have hcardA := hF.2.1 A.val A.prop
  have hcardB := hF.2.1 B.val B.prop
  have hdiffne : (A.val \ B.val).Nonempty := Finset.sdiff_nonempty.mpr (by
    intro hsub
    apply hAB
    apply Subtype.ext
    exact Finset.eq_of_subset_of_card_le hsub (by omega))
  have hdiffle : (A.val \ B.val).card ≤ 1 := by
    exact (Finset.card_le_card (Finset.sdiff_subset)).trans (by omega)
  have hdiffcard : (A.val \ B.val).card = 1 := by
    have hpos := Finset.card_pos.mpr hdiffne
    omega
  simp only [exchangeGraph, SimpleGraph.fromRel_adj]
  exact ⟨hAB, Or.inl ((card_symmDiff_eq_two_iff (by omega)).2 hdiffcard)⟩

private theorem exchangeGraph_complete_of_card_le_three {F : Finset (Finset α)} {κ : ℕ}
    (hF : IsShifted F κ) (h2 : 2 ≤ F.card) (hle : F.card ≤ 3) :
    ∀ A B : ExchangeV F, A ≠ B → (exchangeGraph F).Adj A B := by
  obtain ⟨m₁, m₂, hm₁, hm₂, hadj⟩ := exists_adjacent_gale_bottom_pair hF h2
  by_cases hcard2 : F.card = 2
  · have hpair : F = {m₁, m₂} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro X hX
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX
        rcases hX with rfl | rfl
        · exact hm₁.1
        · exact hm₂.1
      · rw [hcard2, Finset.card_pair hm₂.2.1.symm]
    intro A B hAB
    have hA : A.val = m₁ ∨ A.val = m₂ := by simpa [hpair] using A.prop
    have hB : B.val = m₁ ∨ B.val = m₂ := by simpa [hpair] using B.prop
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · exact (hAB (Subtype.ext (hA.trans hB.symm))).elim
    · rw [show A = ⟨m₁, hm₁.1⟩ from Subtype.ext hA,
          show B = ⟨m₂, hm₂.1⟩ from Subtype.ext hB]
      exact hadj
    · rw [show A = ⟨m₂, hm₂.1⟩ from Subtype.ext hA,
          show B = ⟨m₁, hm₁.1⟩ from Subtype.ext hB]
      exact hadj.symm
    · exact (hAB (Subtype.ext (hA.trans hB.symm))).elim
  · have hcard3 : F.card = 3 := by omega
    obtain ⟨_m₁, _m₂, _hm₁, _hm₂, _h2, h3⟩ := lemma1_bottom hF h2
    exact h3 hcard3

private theorem hasHamPath_of_family_card_one {F : Finset (Finset α)}
    (hcard : F.card = 1) (A B : ExchangeV F) :
    HasHamPath (exchangeGraph F) A B := by
  obtain ⟨X, hF⟩ := Finset.card_eq_one.mp hcard
  have huniq : ∀ Z : ExchangeV F, Z = A := by
    intro Z
    apply Subtype.ext
    have hZ := Z.prop
    have hA := A.prop
    simp [hF] at hZ hA
    simpa using hZ.trans hA.symm
  have hAB : B = A := huniq B
  rw [hAB]
  refine ⟨SimpleGraph.Walk.nil, ?_⟩
  intro Z
  rw [huniq Z]
  simp

private theorem isCliqueSum_swap {V : Type*} {G : SimpleGraph V} {u v : V}
    (h : G.IsCliqueSum u v) : G.IsCliqueSum v u := by
  rcases h with ⟨huv, hu, hv, side, ⟨a, hau, hav, ha⟩,
    ⟨b, hbu, hbv, hb⟩, hside⟩
  refine ⟨huv.symm, hv, hu, side, ⟨a, hav, hau, ha⟩,
    ⟨b, hbv, hbu, hb⟩, ?_⟩
  intro a b hav hau hbv hbu hab
  exact hside a b hau hav hbu hbv hab

/-! ## 8. Stage-two crossing analysis: barred sets, degenerate layers, and range reduction -/

/-- The graph-level barred set at an endpoint.  It is the endpoint itself together with any vertex
which can be its ordered partner in a clique-sum. -/
private noncomputable def crossingBarred (L : Finset (Finset α)) (A : Finset α) :
    Finset (Finset α) :=
  by
    classical
    exact L.filter fun X =>
      X = A ∨ ∃ (hA : A ∈ L) (hX : X ∈ L), IsCliqueSum L ⟨A, hA⟩ ⟨X, hX⟩

private theorem mem_crossingBarred_iff {L : Finset (Finset α)} {A X : Finset α} :
    X ∈ crossingBarred L A ↔
      X ∈ L ∧
        (X = A ∨ ∃ (hA : A ∈ L) (hX : X ∈ L),
          IsCliqueSum L ⟨A, hA⟩ ⟨X, hX⟩) := by
  simp [crossingBarred]

/-- A clique-sum has no universal vertices beyond its displayed two endpoints. -/
private theorem cliqueSum_universal_eq_endpoint
    {V : Type*} {G : SimpleGraph V} {u v w : V}
    (hbad : G.IsCliqueSum u v) (hw : G.IsUniversalVertex w) :
    w = u ∨ w = v := by
  by_cases hwu : w = u
  · exact Or.inl hwu
  right
  rcases hbad with ⟨_huv, _hu, _hv, side,
    ⟨a, hau, hav, ha⟩, ⟨b, hbu, hbv, hb⟩, hside⟩
  by_contra hwv
  have hab : a ≠ b := by
    intro habEq
    subst b
    simp_all
  cases hsw : side w with
  | false =>
      have hwa : w ≠ a := by
        intro hwaEq
        subst a
        simp_all
      have hadj : G.Adj w a := hw a hwa.symm
      have hsides : side w = side a :=
        (hside w a hwu hwv hau hav hwa).mp hadj
      simp_all
  | true =>
      have hwb : w ≠ b := by
        intro hwbEq
        subst b
        simp_all
      have hadj : G.Adj w b := hw b hwb.symm
      have hsides : side w = side b :=
        (hside w b hwu hwv hbu hbv hwb).mp hadj
      simp_all

private theorem cliqueSum_second_unique
    {V : Type*} {G : SimpleGraph V} {u v w : V}
    (huv : G.IsCliqueSum u v) (huw : G.IsCliqueSum u w) : v = w := by
  rcases cliqueSum_universal_eq_endpoint huv huw.2.2.1 with hwu | hwv
  · exact (huw.1 hwu.symm).elim
  · exact hwv.symm

/-- The two universal vertices and the two nonempty sides give four distinct vertices. -/
private theorem cliqueSum_four_le_card
    {L : Finset (Finset α)} {u v : ExchangeV L}
    (hbad : IsCliqueSum L u v) : 4 ≤ L.card := by
  rcases hbad with ⟨huv, _hu, _hv, side,
    ⟨a, hau, hav, ha⟩, ⟨b, hbu, hbv, hb⟩, _hside⟩
  have hab : a ≠ b := by
    intro habEq
    subst b
    simp_all
  have huvVal : u.val ≠ v.val := fun h => huv (Subtype.ext h)
  have huaVal : u.val ≠ a.val := fun h => hau (Subtype.ext h.symm)
  have hubVal : u.val ≠ b.val := fun h => hbu (Subtype.ext h.symm)
  have hvaVal : v.val ≠ a.val := fun h => hav (Subtype.ext h.symm)
  have hvbVal : v.val ≠ b.val := fun h => hbv (Subtype.ext h.symm)
  have habVal : a.val ≠ b.val := fun h => hab (Subtype.ext h)
  have hsub : ({u.val, v.val, a.val, b.val} : Finset (Finset α)) ⊆ L := by
    intro X hX
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX
    rcases hX with rfl | rfl | rfl | rfl
    · exact u.prop
    · exact v.prop
    · exact a.prop
    · exact b.prop
  have hcard := Finset.card_le_card hsub
  simpa [huvVal, huaVal, hubVal, hvaVal, hvbVal, habVal] using hcard

private theorem crossingBarred_subset {L : Finset (Finset α)} {A : Finset α} :
    crossingBarred L A ⊆ L := by
  intro X hX
  exact (mem_crossingBarred_iff.mp hX).1

/-- The graph-level barred set has at most two members. -/
private theorem crossingBarred_card_le_two {L : Finset (Finset α)} {A : Finset α}
    (hA : A ∈ L) : (crossingBarred L A).card ≤ 2 := by
  by_cases hpartner : ∃ (Y : Finset α) (hY : Y ∈ L),
      IsCliqueSum L ⟨A, hA⟩ ⟨Y, hY⟩
  · obtain ⟨Y, hY, hbadY⟩ := hpartner
    have hsub : crossingBarred L A ⊆ {A, Y} := by
      intro X hX
      rcases (mem_crossingBarred_iff.mp hX).2 with rfl | ⟨hA', hX', hbadX⟩
      · simp
      · have hEq : (⟨X, hX'⟩ : ExchangeV L) = ⟨Y, hY⟩ :=
          cliqueSum_second_unique hbadX hbadY
        have : X = Y := congrArg Subtype.val hEq
        simp [this]
    have hpair : ({A, Y} : Finset (Finset α)).card ≤ 2 := by
      by_cases hAY : A = Y <;> simp [hAY]
    exact (Finset.card_le_card hsub).trans hpair
  · have hsub : crossingBarred L A ⊆ {A} := by
      intro X hX
      rcases (mem_crossingBarred_iff.mp hX).2 with rfl | ⟨hA', hX', hbadX⟩
      · simp
      · exact (hpartner ⟨X, hX', hbadX⟩).elim
    exact (Finset.card_le_card hsub).trans (by simp)

/-- The two-member barred case can occur only when the layer has at least four members. -/
private theorem crossingBarred_two_forces_four {L : Finset (Finset α)} {A : Finset α}
    (hA : A ∈ L) (hcard : (crossingBarred L A).card = 2) : 4 ≤ L.card := by
  by_contra hlt
  have hnpartner : ¬ ∃ (Y : Finset α) (hY : Y ∈ L),
      IsCliqueSum L ⟨A, hA⟩ ⟨Y, hY⟩ := by
    rintro ⟨Y, hY, hbad⟩
    exact hlt (cliqueSum_four_le_card hbad)
  have hEq : crossingBarred L A = {A} := by
    apply Finset.Subset.antisymm
    · intro X hX
      rcases (mem_crossingBarred_iff.mp hX).2 with rfl | ⟨hA', hX', hbadX⟩
      · simp
      · exact (hnpartner ⟨X, hX', hbadX⟩).elim
    · intro X hX
      have hXA : X = A := by simpa using hX
      subst X
      exact mem_crossingBarred_iff.mpr ⟨hA, Or.inl rfl⟩
  rw [hEq] at hcard
  simp at hcard

/-- Statement `(∗)`: every layer with at least two members has a member outside its barred set. -/
private theorem exists_mem_not_crossingBarred {L : Finset (Finset α)} {A : Finset α}
    (hA : A ∈ L) (hL : 2 ≤ L.card) : ∃ X ∈ L, X ∉ crossingBarred L A := by
  by_contra hnone
  have hsub : L ⊆ crossingBarred L A := by
    intro X hX
    by_contra hXout
    exact hnone ⟨X, hX, hXout⟩
  have hEq : L = crossingBarred L A := Finset.Subset.antisymm hsub crossingBarred_subset
  have hbarLe : (crossingBarred L A).card ≤ 2 := crossingBarred_card_le_two hA
  have hbarTwo : (crossingBarred L A).card = 2 := by
    have hbarGe : 2 ≤ (crossingBarred L A).card := by
      rw [← hEq]
      exact hL
    omega
  have hfour : 4 ≤ L.card := crossingBarred_two_forces_four hA hbarTwo
  rw [hEq] at hfour
  omega

/-- Failure of the crossing assertion, expressed using the graph-level barred sets. -/
private def crossingFailure (F : Finset (Finset α)) (A B : Finset α) (e : α) : Prop :=
  ¬ ∃ W X : Finset α, ∃ ξ : α,
      W ∈ layerAbove F e ∧ X ∈ layerBelow F e ∧
      ξ ≠ e ∧ ξ ∉ W ∧ X = insert ξ (W.erase e) ∧
      ((layerAbove F e).card = 1 ∨ W ∉ crossingBarred (layerAbove F e) A) ∧
      ((layerBelow F e).card = 1 ∨ X ∉ crossingBarred (layerBelow F e) B)

private theorem crossingFailure_crossing_target_mem_crossingBarred
    {F : Finset (Finset α)} {A B W X : Finset α} {e ξ : α}
    (hfail : crossingFailure F A B e)
    (hW : W ∈ layerAbove F e) (hX : X ∈ layerBelow F e)
    (hξe : ξ ≠ e) (hξW : ξ ∉ W) (hform : X = insert ξ (W.erase e))
    (hWallowed : (layerAbove F e).card = 1 ∨ W ∉ crossingBarred (layerAbove F e) A) :
    X ∈ crossingBarred (layerBelow F e) B := by
  by_contra hXout
  apply hfail
  exact ⟨W, X, ξ, hW, hX, hξe, hξW, hform, hWallowed, Or.inr hXout⟩

private theorem exists_cliqueSum_of_crossingBarred_card_two
    {L : Finset (Finset α)} {A : Finset α} (hA : A ∈ L)
    (hcard : (crossingBarred L A).card = 2) :
    ∃ (Y : Finset α) (hY : Y ∈ L), IsCliqueSum L ⟨A, hA⟩ ⟨Y, hY⟩ := by
  by_contra hnone
  have hEq : crossingBarred L A = {A} := by
    apply Finset.Subset.antisymm
    · intro X hX
      rcases (mem_crossingBarred_iff.mp hX).2 with rfl | ⟨hA', hX', hbadX⟩
      · simp
      · exact (hnone ⟨X, hX', hbadX⟩).elim
    · intro X hX
      have hXA : X = A := by simpa using hX
      subst X
      exact mem_crossingBarred_iff.mpr ⟨hA, Or.inl rfl⟩
  rw [hEq] at hcard
  simp at hcard

/-- Under failure, every downward crossing target of an unbarred containing-layer member is barred in the avoiding layer. -/
private theorem crossingFailure_down_target_mem_crossingBarred
    {F : Finset (Finset α)} {k : ℕ} (hF : IsShifted F k)
    {A B W : Finset α} {e ξ : α}
    (hfail : crossingFailure F A B e)
    (hW : W ∈ layerAbove F e) (hWout : W ∉ crossingBarred (layerAbove F e) A)
    (hξe : ξ < e) (hξW : ξ ∉ W) :
    insert ξ (W.erase e) ∈ crossingBarred (layerBelow F e) B := by
  have hWF : W ∈ F := (Finset.mem_filter.mp hW).1
  have heW : e ∈ W := (Finset.mem_filter.mp hW).2
  let X := insert ξ (W.erase e)
  have hXF : X ∈ F := hF.2.2 W hWF ξ e heW hξe hξW
  have heX : e ∉ X := by simp [X, hξe.ne']
  have hXbelow : X ∈ layerBelow F e := Finset.mem_filter.mpr ⟨hXF, heX⟩
  by_contra hXout
  apply hfail
  exact ⟨W, X, ξ, hW, hXbelow, hξe.ne, hξW, rfl,
    Or.inr hWout, Or.inr hXout⟩

/-- Under failure, every upward crossing source of an unbarred avoiding-layer member is barred in the containing layer. -/
private theorem crossingFailure_up_source_mem_crossingBarred
    {F : Finset (Finset α)} {k : ℕ} (hF : IsShifted F k)
    {A B Z : Finset α} {e ξ : α}
    (hfail : crossingFailure F A B e)
    (hZ : Z ∈ layerBelow F e) (hZout : Z ∉ crossingBarred (layerBelow F e) B)
    (hξZ : ξ ∈ Z) (heξ : e < ξ) :
    insert e (Z.erase ξ) ∈ crossingBarred (layerAbove F e) A := by
  have hZF : Z ∈ F := (Finset.mem_filter.mp hZ).1
  have heZ : e ∉ Z := (Finset.mem_filter.mp hZ).2
  let W := insert e (Z.erase ξ)
  have hWF : W ∈ F := hF.2.2 Z hZF e ξ hξZ heξ heZ
  have heW : e ∈ W := Finset.mem_insert_self _ _
  have hWabove : W ∈ layerAbove F e := Finset.mem_filter.mpr ⟨hWF, heW⟩
  have hξW : ξ ∉ W := by simp [W, heξ.ne', hξZ]
  have hrestore : Z = insert ξ (W.erase e) := by
    simp [W, heZ, hξZ, heξ.ne]
  by_contra hWout
  apply hfail
  exact ⟨W, Z, ξ, hWabove, hZ, heξ.ne', hξW, hrestore,
    Or.inr hWout, Or.inr hZout⟩

/-- The downward half of `(∗∗)`: the missing lower points inject into the lower barred set. -/
private theorem crossingFailure_down_count_le_two
    {F : Finset (Finset α)} {k : ℕ} (hF : IsShifted F k)
    {A B W : Finset α} {e : α}
    (hfail : crossingFailure F A B e)
    (hW : W ∈ layerAbove F e) (hWout : W ∉ crossingBarred (layerAbove F e) A)
    (hB : B ∈ layerBelow F e) :
    (((usedGround F).filter fun ξ => ξ < e) \ W).card ≤
        (crossingBarred (layerBelow F e) B).card ∧
      (crossingBarred (layerBelow F e) B).card ≤ 2 := by
  let D := (usedGround F).filter (fun ξ => ξ < e) \ W
  let target := fun ξ : α => insert ξ (W.erase e)
  have hinj : Set.InjOn target (D : Set α) := by
    intro x hx y hy hxy
    have hxW : x ∉ W := (Finset.mem_sdiff.mp hx).2
    have hxErase : x ∉ W.erase e := fun h => hxW (Finset.mem_of_mem_erase h)
    exact (Finset.insert_inj hxErase).mp hxy
  have hsub : D.image target ⊆ crossingBarred (layerBelow F e) B := by
    intro X hX
    obtain ⟨ξ, hξD, rfl⟩ := Finset.mem_image.mp hX
    have hξe : ξ < e := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hξD).1).2
    have hξW : ξ ∉ W := (Finset.mem_sdiff.mp hξD).2
    exact crossingFailure_down_target_mem_crossingBarred hF hfail hW hWout hξe hξW
  constructor
  · change D.card ≤ _
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hsub
  · exact crossingBarred_card_le_two hB

/-- The upward half of `(∗∗)`: the retained upper points inject into the upper barred set. -/
private theorem crossingFailure_up_count_le_two
    {F : Finset (Finset α)} {k : ℕ} (hF : IsShifted F k)
    {A B Z : Finset α} {e : α}
    (hfail : crossingFailure F A B e)
    (hZ : Z ∈ layerBelow F e) (hZout : Z ∉ crossingBarred (layerBelow F e) B)
    (hA : A ∈ layerAbove F e) :
    (Z.filter fun ξ => e < ξ).card ≤ (crossingBarred (layerAbove F e) A).card ∧
      (crossingBarred (layerAbove F e) A).card ≤ 2 := by
  let U := Z.filter fun ξ => e < ξ
  let source := fun ξ : α => insert e (Z.erase ξ)
  have hinj : Set.InjOn source (U : Set α) := by
    intro x hx y hy hxy
    have hxZ : x ∈ Z := (Finset.mem_filter.mp hx).1
    have _hyZ : y ∈ Z := (Finset.mem_filter.mp hy).1
    have hex : e < x := (Finset.mem_filter.mp hx).2
    by_contra hxyNe
    have hxLeft : x ∉ source x := by simp [source, hex.ne', hxZ]
    have hxRight : x ∈ source y := by simp [source, hex.ne', hxZ, hxyNe]
    exact hxLeft (hxy ▸ hxRight)
  have hsub : U.image source ⊆ crossingBarred (layerAbove F e) A := by
    intro W hW
    obtain ⟨ξ, hξU, rfl⟩ := Finset.mem_image.mp hW
    have hξZ : ξ ∈ Z := (Finset.mem_filter.mp hξU).1
    have heξ : e < ξ := (Finset.mem_filter.mp hξU).2
    exact crossingFailure_up_source_mem_crossingBarred hF hfail hZ hZout hξZ heξ
  constructor
  · change U.card ≤ _
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hsub
  · exact crossingBarred_card_le_two hA

/-- Case 1: if both layers are singletons, their two members form the required crossing. -/
private theorem not_crossingFailure_of_layer_cards_one
    {F : Finset (Finset α)} {k : ℕ} (hF : IsShifted F k)
    {A B : ExchangeV F} (hAB : A ≠ B) {e : α}
    (heA : e ∈ A.val) (heB : e ∉ B.val)
    (hAbove : (layerAbove F e).card = 1)
    (hBelow : (layerBelow F e).card = 1) :
    ¬ crossingFailure F A.val B.val e := by
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := F) (p := fun X => e ∈ X)
  have hFcard : F.card = 2 := by
    change (layerAbove F e).card + (layerBelow F e).card = F.card at hpartition
    omega
  have htwo : 2 ≤ F.card := by omega
  have hAdj : (exchangeGraph F).Adj A B :=
    exchangeGraph_complete_of_card_le_three hF htwo (by omega) A B hAB
  have hsymm : (A.val ∆ B.val).card = 2 := by
    simp only [exchangeGraph, SimpleGraph.fromRel_adj] at hAdj
    rcases hAdj.2 with h | h
    · exact h
    · simpa [symmDiff_comm] using h
  have hcardAB : A.val.card = B.val.card :=
    (hF.2.1 A.val A.prop).trans (hF.2.1 B.val B.prop).symm
  have hABone : (A.val \ B.val).card = 1 :=
    (card_symmDiff_eq_two_iff hcardAB).mp hsymm
  have hBAsymm : (B.val ∆ A.val).card = 2 := by
    simpa [symmDiff_comm] using hsymm
  have hBAone : (B.val \ A.val).card = 1 :=
    (card_symmDiff_eq_two_iff hcardAB.symm).mp hBAsymm
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hABone
  have heDiff : e ∈ A.val \ B.val := Finset.mem_sdiff.mpr ⟨heA, heB⟩
  have hep : e = p := by
    have : e ∈ ({p} : Finset α) := hp ▸ heDiff
    simpa using this
  have hABdiff : A.val \ B.val = {e} := by simpa [hep] using hp
  obtain ⟨ξ, hξ⟩ := Finset.card_eq_one.mp hBAone
  have hξDiff : ξ ∈ B.val \ A.val := by simp [hξ]
  have hξA : ξ ∉ A.val := (Finset.mem_sdiff.mp hξDiff).2
  have hξe : ξ ≠ e := fun h => hξA (h ▸ heA)
  have hBform : B.val = insert ξ (A.val.erase e) :=
    eq_insert_erase_of_sdiff_eq_singletons hξ hABdiff
  have hAabove : A.val ∈ layerAbove F e := Finset.mem_filter.mpr ⟨A.prop, heA⟩
  have hBbelow : B.val ∈ layerBelow F e := Finset.mem_filter.mpr ⟨B.prop, heB⟩
  intro hfail
  apply hfail
  exact ⟨A.val, B.val, ξ, hAabove, hBbelow, hξe, hξA, hBform,
    Or.inl hAbove, Or.inl hBelow⟩

/-- Case 2: a singleton containing layer and a nonsingleton avoiding layer cannot fail. -/
private theorem not_crossingFailure_of_upper_singleton
    {F : Finset (Finset α)} {k : ℕ} (hF : IsShifted F k)
    {A B : ExchangeV F} {e : α} (heA : e ∈ A.val) (heB : e ∉ B.val)
    (hAbove : (layerAbove F e).card = 1)
    (hBelow : 2 ≤ (layerBelow F e).card) :
    ¬ crossingFailure F A.val B.val e := by
  let L := layerBelow F e
  let P := puncturedLower F e
  let Q := puncturedLink F e
  let G := usedGround F
  let H := G.erase e
  let C := initialSegment H (k - 1)
  have hAabove : A.val ∈ layerAbove F e := Finset.mem_filter.mpr ⟨A.prop, heA⟩
  have hBbelow : B.val ∈ L := Finset.mem_filter.mpr ⟨B.prop, heB⟩
  have hAboveNe : (layerAbove F e).Nonempty := ⟨A.val, hAabove⟩
  change 2 ≤ L.card at hBelow
  have hBelowNe : L.Nonempty := ⟨B.val, hBbelow⟩
  have hLowerCardEq : L.card = P.card := by
    simpa [L, P] using Fintype.card_congr (lowerVertexEquiv F e)
  have hLinkCardEq : (layerAbove F e).card = Q.card := by
    simpa [Q] using Fintype.card_congr (linkVertexEquiv F e)
  have hPtwo : 2 ≤ P.card := by omega
  have hQone : Q.card = 1 := by omega
  let μ := punctureSet e A.val
  have hμQ : μ ∈ Q := Finset.mem_image.mpr ⟨A.val, hAabove, rfl⟩
  have hμLeast : IsGaleLeast Q μ := by
    refine ⟨hμQ, ?_⟩
    intro Y hY
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hQone
    have hμq : μ = q := by
      have : μ ∈ ({q} : Finset (Finset (Punctured e))) := hq ▸ hμQ
      simpa using this
    have hYq : Y = q := by
      have : Y ∈ ({q} : Finset (Finset (Punctured e))) := hq ▸ hY
      simpa using this
    rw [hYq, ← hμq]
    exact galeLE_refl μ
  have hAform : A.val = insert e C := by
    have hrow := link_galeLeast_lift_eq_initialSegment_erase hF hAboveNe hμLeast
    change insert e (liftPuncturedSet μ) = insert e C at hrow
    rw [show liftPuncturedSet μ = A.val.erase e by
      exact liftPuncturedSet_punctureSet A.val, Finset.insert_erase heA] at hrow
    exact hrow
  have hPshift : IsShifted P k := isShifted_puncturedLower hF hBelowNe
  obtain ⟨m₁, m₂, hm₁, hm₂, _i, _j, _him₁, _him₂, _hjm₂, _hjm₁,
      _hij, _hm₂repr, _himax, _hjmin⟩ :=
    exists_gale_bottom_pair_with_boundary hPshift hPtwo
  let X₁ := liftPuncturedSet m₁
  let X₂ := liftPuncturedSet m₂
  have hX₁below : X₁ ∈ L := by
    change liftPuncturedSet m₁ ∈ layerBelow F e
    exact Finset.mem_filter.mpr
      ⟨mem_puncturedLower_iff.mp hm₁.1, by simp [liftPuncturedSet]⟩
  have hX₂below : X₂ ∈ L := by
    change liftPuncturedSet m₂ ∈ layerBelow F e
    exact Finset.mem_filter.mpr
      ⟨mem_puncturedLower_iff.mp hm₂.1, by simp [liftPuncturedSet]⟩
  have hX₁coord : X₁ = initialSegment H k := by
    exact layerBelow_galeLeast_lift_eq_initialSegment_erase hF hBelowNe hm₁
  have hX₂coord : X₂ = secondInitialSegment H k := by
    exact layerBelow_galeSecondLeast_lift_eq_secondInitialSegment_erase
      hF hBelowNe hPtwo hm₁ hm₂
  have hX₁card : X₁.card = k := by
    simpa [X₁, liftPuncturedSet] using hPshift.2.1 m₁ hm₁.1
  have hX₂card : X₂.card = k := by
    simpa [X₂, liftPuncturedSet] using hPshift.2.1 m₂ hm₂.1
  have hX₁subH : X₁ ⊆ H := by
    intro x hx
    apply Finset.mem_erase.mpr
    refine ⟨?_, ?_⟩
    · obtain ⟨xp, _hxp, hval⟩ := Finset.mem_map.mp hx
      exact hval ▸ xp.property
    · change x ∈ usedGround F
      rw [usedGround, Finset.mem_biUnion]
      exact ⟨X₁, (Finset.mem_filter.mp hX₁below).1, hx⟩
  have hHcard : k ≤ H.card := by
    have := Finset.card_le_card hX₁subH
    omega
  have hCcard : C.card = k - 1 := card_initialSegment_of_le (by omega)
  have hCsubX₁ : C ⊆ X₁ := by
    rw [hX₁coord]
    exact initialSegment_mono H (Nat.sub_le k 1)
  have hCsubX₂ : C ⊆ X₂ := by
    rw [hX₂coord, secondInitialSegment]
    exact fun x hx => Finset.mem_union_left _ hx
  have hkpos : 1 ≤ k := by
    rw [← hF.2.1 A.val A.prop]
    exact Finset.one_le_card.mpr ⟨e, heA⟩
  have extend (X : Finset α) (hXcard : X.card = k) (hCX : C ⊆ X) :
      ∃ ξ : α, ξ ∈ X ∧ ξ ∉ C ∧ X = insert ξ C := by
    have hdiffcard : (X \ C).card = 1 := by
      rw [Finset.card_sdiff_of_subset hCX, hXcard, hCcard]
      omega
    obtain ⟨ξ, hdiff⟩ := Finset.card_eq_one.mp hdiffcard
    have hξdiff : ξ ∈ X \ C := by simp [hdiff]
    refine ⟨ξ, (Finset.mem_sdiff.mp hξdiff).1, (Finset.mem_sdiff.mp hξdiff).2, ?_⟩
    apply Finset.Subset.antisymm
    · intro x hx
      by_cases hxC : x ∈ C
      · exact Finset.mem_insert.mpr (Or.inr hxC)
      · have hxdiff : x ∈ X \ C := Finset.mem_sdiff.mpr ⟨hx, hxC⟩
        have hxξ : x = ξ := by simpa [hdiff] using hxdiff
        exact Finset.mem_insert.mpr (Or.inl hxξ)
    · exact Finset.insert_subset (Finset.mem_sdiff.mp hξdiff).1 hCX
  obtain ⟨ξ₁, hξ₁X, hξ₁C, hX₁form⟩ := extend X₁ hX₁card hCsubX₁
  obtain ⟨ξ₂, hξ₂X, hξ₂C, hX₂form⟩ := extend X₂ hX₂card hCsubX₂
  have hX₁X₂ : X₁ ≠ X₂ := by
    intro hEq
    apply hm₂.2.1
    have := congrArg (punctureSet e) hEq
    simpa [X₁, X₂] using this.symm
  have heC : e ∉ C := by
    intro heC'
    exact (Finset.mem_erase.mp (initialSegment_subset H (k - 1) heC')).1 rfl
  have hAerase : A.val.erase e = C := by
    rw [hAform]
    simp [heC]
  have target_barred {X : Finset α} {ξ : α}
      (hXbelow : X ∈ L) (hξX : ξ ∈ X) (hξC : ξ ∉ C)
      (hXform : X = insert ξ C) (hfail : crossingFailure F A.val B.val e) :
      X ∈ crossingBarred L B.val := by
    have heX : e ∉ X := (Finset.mem_filter.mp hXbelow).2
    have hξe : ξ ≠ e := fun h => heX (h ▸ hξX)
    have hξA : ξ ∉ A.val := by
      rw [hAform]
      simp [hξe, hξC]
    apply crossingFailure_crossing_target_mem_crossingBarred hfail hAabove hXbelow
      hξe hξA
    · simpa [hAerase] using hXform
    · exact Or.inl hAbove
  intro hfail
  have hX₁bar : X₁ ∈ crossingBarred L B.val :=
    target_barred hX₁below hξ₁X hξ₁C hX₁form hfail
  have hX₂bar : X₂ ∈ crossingBarred L B.val :=
    target_barred hX₂below hξ₂X hξ₂C hX₂form hfail
  have hbarGe : 2 ≤ (crossingBarred L B.val).card := by
    have hsub : ({X₁, X₂} : Finset (Finset α)) ⊆ crossingBarred L B.val := by
      intro X hX
      rcases Finset.mem_insert.mp hX with rfl | hX
      · exact hX₁bar
      · have hXX₂ : X = X₂ := by simpa using hX
        exact hXX₂ ▸ hX₂bar
    have := Finset.card_le_card hsub
    simpa [hX₁X₂] using this
  have hbarLe : (crossingBarred L B.val).card ≤ 2 := crossingBarred_card_le_two hBbelow
  have hbarTwo : (crossingBarred L B.val).card = 2 := by omega
  obtain ⟨Y, hYL, hbadL⟩ :=
    exists_cliqueSum_of_crossingBarred_card_two hBbelow hbarTwo
  let bV : ExchangeV L := ⟨B.val, hBbelow⟩
  let yV : ExchangeV L := ⟨Y, hYL⟩
  have hbadL' : IsCliqueSum L bV yV := by simpa [bV, yV] using hbadL
  have hbadP : IsCliqueSum P
      (exchangeGraph_puncturedLowerIso F e bV)
      (exchangeGraph_puncturedLowerIso F e yV) :=
    isCliqueSum_map_iso (exchangeGraph_puncturedLowerIso F e) hbadL'
  obtain ⟨r, s, hrH, hrOut, hsH, hrow⟩ :=
    layerBelow_cliqueSum_yFamily_row hF hBelowNe hbadP
  change r.val ∈ H at hrH
  change r.val ∉ initialSegment H (k + 1) at hrOut
  change s.val ∈ initialSegment H (k - 1) at hsH
  change L = yFamily H k r.val s.val at hrow
  let X₃ := insert r.val C
  have hrC : r.val ∉ C := by
    intro hr
    exact hrOut (initialSegment_mono H (by omega) hr)
  have hX₃below : X₃ ∈ L := by
    rw [hrow, yFamily]
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    rw [yOuterArm]
    exact Finset.mem_image.mpr
      ⟨r.val, Finset.mem_filter.mpr ⟨hrH, hrOut, le_rfl⟩, rfl⟩
  have hrX₃ : r.val ∈ X₃ := Finset.mem_insert_self _ _
  have hX₃bar : X₃ ∈ crossingBarred L B.val :=
    target_barred hX₃below hrX₃ hrC rfl hfail
  have hX₁subU : X₁ ⊆ initialSegment H (k + 1) := by
    rw [hX₁coord]
    exact initialSegment_mono H (by omega)
  have hX₂subU : X₂ ⊆ initialSegment H (k + 1) := by
    rw [hX₂coord, secondInitialSegment]
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact initialSegment_mono H (by omega) hx
    · exact (Finset.mem_sdiff.mp hx).1
  have hX₃X₁ : X₃ ≠ X₁ := by
    intro hEq
    exact hrOut (hX₁subU (hEq ▸ hrX₃))
  have hX₃X₂ : X₃ ≠ X₂ := by
    intro hEq
    exact hrOut (hX₂subU (hEq ▸ hrX₃))
  have hthreeSub : ({X₁, X₂, X₃} : Finset (Finset α)) ⊆ crossingBarred L B.val := by
    intro X hX
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX
    rcases hX with rfl | rfl | rfl
    · exact hX₁bar
    · exact hX₂bar
    · exact hX₃bar
  have hthreeCard : ({X₁, X₂, X₃} : Finset (Finset α)).card = 3 := by
    have hX₁not : X₁ ∉ ({X₂, X₃} : Finset (Finset α)) := by
      simp [hX₁X₂, hX₃X₁.symm]
    have hX₂not : X₂ ∉ ({X₃} : Finset (Finset α)) := by
      simp [hX₃X₂.symm]
    rw [Finset.card_insert_of_notMem hX₁not, Finset.card_insert_of_notMem hX₂not]
    simp
  have := Finset.card_le_card hthreeSub
  rw [hthreeCard, hbarTwo] at this
  omega

private theorem mem_crossingBarred_dual_iff {n : ℕ}
    {L : Finset (Finset (Fin n))} {A X : Finset (Fin n)} :
    X ∈ crossingBarred L A ↔
      dualSet X ∈ crossingBarred (dualFamily L) (dualSet A) := by
  constructor
  · intro hX
    rcases mem_crossingBarred_iff.mp hX with ⟨hXL, hXA | hbad⟩
    · apply mem_crossingBarred_iff.mpr
      refine ⟨Finset.mem_image.mpr ⟨X, hXL, rfl⟩, Or.inl ?_⟩
      exact congrArg dualSet hXA
    · obtain ⟨hA, hX', hbad⟩ := hbad
      apply mem_crossingBarred_iff.mpr
      refine ⟨Finset.mem_image.mpr ⟨X, hXL, rfl⟩, Or.inr ?_⟩
      refine ⟨Finset.mem_image.mpr ⟨A, hA, rfl⟩,
        Finset.mem_image.mpr ⟨X, hX', rfl⟩, ?_⟩
      simpa [dualExchangeEquiv] using
        (isCliqueSum_dual_iff (⟨A, hA⟩ : ExchangeV L) ⟨X, hX'⟩).mp hbad
  · intro hDX
    rcases mem_crossingBarred_iff.mp hDX with ⟨hDXL, hDXA | hbad⟩
    · apply mem_crossingBarred_iff.mpr
      refine ⟨by simpa using mem_dualFamily.mp hDXL, Or.inl ?_⟩
      have := congrArg dualSet hDXA
      simpa using this
    · obtain ⟨hDA, hDX', hbad⟩ := hbad
      have hA : A ∈ L := by simpa using mem_dualFamily.mp hDA
      have hX : X ∈ L := by simpa using mem_dualFamily.mp hDX'
      apply mem_crossingBarred_iff.mpr
      refine ⟨hX, Or.inr ⟨hA, hX, ?_⟩⟩
      have hforward :=
        (isCliqueSum_dual_iff (⟨A, hA⟩ : ExchangeV L) ⟨X, hX⟩).mpr
      simpa [dualExchangeEquiv] using hforward hbad

/-- Case 3, obtained from Case 2 by complement-and-reverse duality. -/
private theorem not_crossingFailure_of_lower_singleton_dual
    {n k : ℕ} {F : Finset (Finset (Fin n))} (hF : IsShifted F k)
    {A B : ExchangeV F} {e : Fin n} (heA : e ∈ A.val) (heB : e ∉ B.val)
    (hAbove : 2 ≤ (layerAbove F e).card)
    (hBelow : (layerBelow F e).card = 1) :
    ¬ crossingFailure F A.val B.val e := by
  classical
  let Fd := dualFamily F
  let ed := dualElem e
  let Ad : ExchangeV Fd := dualExchangeEquiv F B
  let Bd : ExchangeV Fd := dualExchangeEquiv F A
  have hdualInj : Function.Injective (@dualSet n) := by
    intro X Y hXY
    have := congrArg dualSet hXY
    simpa using this
  have hAboveCard : (layerAbove Fd ed).card = (layerBelow F e).card := by
    have himage := image_layerBelow_dualSet F e
    change (layerBelow F e).image dualSet = layerAbove Fd ed at himage
    rw [← himage, Finset.card_image_of_injective _ hdualInj]
  have hBelowCard : (layerBelow Fd ed).card = (layerAbove F e).card := by
    have himage := image_layerAbove_dualSet F e
    change (layerAbove F e).image dualSet = layerBelow Fd ed at himage
    rw [← himage, Finset.card_image_of_injective _ hdualInj]
  have hAdMem : ed ∈ Ad.val := by
    change dualElem e ∈ dualSet B.val
    simpa using heB
  have hBdNotMem : ed ∉ Bd.val := by
    change dualElem e ∉ dualSet A.val
    simpa using heA
  have hFd : IsShifted Fd (n - k) := isShifted_dualFamily hF
  have hNoDualFailure : ¬ crossingFailure Fd Ad.val Bd.val ed :=
    not_crossingFailure_of_upper_singleton hFd hAdMem hBdNotMem
      (hAboveCard.trans hBelow) (by omega)
  intro hfail
  apply hNoDualFailure
  intro hcross
  apply hfail
  rcases hcross with ⟨Wd, Xd, ξd, hWd, hXd, hξde, hξdW, hXdform,
    hWdAllowed, hXdAllowed⟩
  let W := dualSet Xd
  let X := dualSet Wd
  let ξ := dualElem ξd
  have hWF : W ∈ F := by
    change dualSet Xd ∈ F
    exact mem_dualFamily.mp (Finset.mem_filter.mp hXd).1
  have heW : e ∈ W := by
    change e ∈ dualSet Xd
    simpa [ed] using (Finset.mem_filter.mp hXd).2
  have hWabove : W ∈ layerAbove F e := Finset.mem_filter.mpr ⟨hWF, heW⟩
  have hXF : X ∈ F := by
    change dualSet Wd ∈ F
    exact mem_dualFamily.mp (Finset.mem_filter.mp hWd).1
  have heX : e ∉ X := by
    change e ∉ dualSet Wd
    simpa [ed] using (Finset.mem_filter.mp hWd).2
  have hXbelow : X ∈ layerBelow F e := Finset.mem_filter.mpr ⟨hXF, heX⟩
  have hξe : ξ ≠ e := by
    intro h
    apply hξde
    have := congrArg dualElem h
    simpa [ξ, ed] using this
  have hξXd : ξd ∈ Xd := hXdform ▸ Finset.mem_insert_self _ _
  have hedWd : ed ∈ Wd := (Finset.mem_filter.mp hWd).2
  have hξW : ξ ∉ W := by
    intro h
    have hnot := mem_dualSet.mp h
    apply hnot
    simpa [ξ] using hξXd
  have hform : X = insert ξ (W.erase e) := by
    change dualSet Wd = insert (dualElem ξd) ((dualSet Xd).erase e)
    ext z
    simp only [mem_dualSet, Finset.mem_insert, Finset.mem_erase]
    rw [hXdform]
    simp only [Finset.mem_insert, Finset.mem_erase]
    by_cases hzξ : z = dualElem ξd
    · subst z
      simp [ed, hξdW]
    by_cases hze : z = e
    · subst z
      have heWd : dualElem e ∈ Wd := by simpa [ed] using hedWd
      simp [heWd, hzξ]
    have hdzξ : dualElem z ≠ ξd := by
      intro h
      apply hzξ
      have := congrArg dualElem h
      simpa using this
    have hdze : dualElem z ≠ ed := by
      intro h
      apply hze
      have := congrArg dualElem h
      simpa [ed] using this
    simp [hzξ, hze, hdzξ, hdze]
  have hDualLower : dualFamily (layerBelow F e) = layerAbove Fd ed := by
    simpa [dualFamily, Fd, ed] using image_layerBelow_dualSet F e
  have hDualAbove : dualFamily (layerAbove F e) = layerBelow Fd ed := by
    simpa [dualFamily, Fd, ed] using image_layerAbove_dualSet F e
  have hXAllowed : (layerBelow F e).card = 1 ∨
      X ∉ crossingBarred (layerBelow F e) B.val := by
    rcases hWdAllowed with hcard | hnot
    · exact Or.inl (by omega)
    · right
      intro hbar
      have hdbar := (mem_crossingBarred_dual_iff (L := layerBelow F e)
        (A := B.val) (X := X)).mp hbar
      rw [hDualLower] at hdbar
      apply hnot
      simpa [X, Ad, dualExchangeEquiv] using hdbar
  have hWAllowed : (layerAbove F e).card = 1 ∨
      W ∉ crossingBarred (layerAbove F e) A.val := by
    rcases hXdAllowed with hcard | hnot
    · exact Or.inl (by omega)
    · right
      intro hbar
      have hdbar := (mem_crossingBarred_dual_iff (L := layerAbove F e)
        (A := A.val) (X := W)).mp hbar
      rw [hDualAbove] at hdbar
      apply hnot
      simpa [W, Bd, dualExchangeEquiv] using hdbar
  exact ⟨W, X, ξ, hWabove, hXbelow, hξe, hξW, hform, hWAllowed, hXAllowed⟩

/-- In the main case, failure confines the one-indexed position of `e` to
`k-1 ≤ groundRank(e)+1 ≤ k+2`. -/
private theorem crossingFailure_range_reduction
    {F : Finset (Finset α)} {k : ℕ} (hF : IsShifted F k)
    {A B : Finset α} {e : α}
    (hfail : crossingFailure F A B e)
    (hA : A ∈ layerAbove F e) (hB : B ∈ layerBelow F e)
    (hAbove : 2 ≤ (layerAbove F e).card)
    (hBelow : 2 ≤ (layerBelow F e).card) :
    k - 1 ≤ groundRank (usedGround F) e + 1 ∧
      groundRank (usedGround F) e + 1 ≤ k + 2 := by
  obtain ⟨W, hW, hWout⟩ := exists_mem_not_crossingBarred hA hAbove
  obtain ⟨Z, hZ, hZout⟩ := exists_mem_not_crossingBarred hB hBelow
  have hdBounds := crossingFailure_down_count_le_two hF hfail hW hWout hB
  have huBounds := crossingFailure_up_count_le_two hF hfail hZ hZout hA
  have hdle : (((usedGround F).filter fun ξ => ξ < e) \ W).card ≤ 2 :=
    hdBounds.1.trans hdBounds.2
  have hule : (Z.filter fun ξ => e < ξ).card ≤ 2 :=
    huBounds.1.trans huBounds.2
  let G := usedGround F
  let S := G.filter fun ξ => ξ < e
  have hWF : W ∈ F := (Finset.mem_filter.mp hW).1
  have heW : e ∈ W := (Finset.mem_filter.mp hW).2
  have hWcard : W.card = k := hF.2.1 W hWF
  have hInterSub : S ∩ W ⊆ W.erase e := by
    intro x hx
    obtain ⟨hxS, hxW⟩ := Finset.mem_inter.mp hx
    have hxe : x ≠ e := (Finset.mem_filter.mp hxS).2.ne
    exact Finset.mem_erase.mpr ⟨hxe, hxW⟩
  have hInterLe : (S ∩ W).card ≤ k - 1 := by
    have hle := Finset.card_le_card hInterSub
    rw [Finset.card_erase_of_mem heW, hWcard] at hle
    exact hle
  have hSpart : (S \ W).card + (S ∩ W).card = S.card :=
    Finset.card_sdiff_add_card_inter S W
  have hSCard : S.card = groundRank G e := rfl
  have hkpos : 1 ≤ k := by
    rw [← hWcard]
    exact Finset.one_le_card.mpr ⟨e, heW⟩
  have hrankUpper : groundRank G e + 1 ≤ k + 2 := by
    change (S \ W).card ≤ 2 at hdle
    have hRankLe : groundRank G e ≤ 2 + (k - 1) := by
      rw [← hSCard, ← hSpart]
      exact Nat.add_le_add hdle hInterLe
    omega
  have hZF : Z ∈ F := (Finset.mem_filter.mp hZ).1
  have heZ : e ∉ Z := (Finset.mem_filter.mp hZ).2
  have hZcard : Z.card = k := hF.2.1 Z hZF
  have hZG : Z ⊆ G := by
    intro x hx
    change x ∈ usedGround F
    rw [usedGround, Finset.mem_biUnion]
    exact ⟨Z, hZF, hx⟩
  have hBelowSub : Z.filter (fun ξ => ξ < e) ⊆ S := by
    intro x hx
    obtain ⟨hxZ, hxe⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hZG hxZ, hxe⟩
  have hBelowLe : (Z.filter fun ξ => ξ < e).card ≤ groundRank G e := by
    rw [← hSCard]
    exact Finset.card_le_card hBelowSub
  have hnotFilter : Z.filter (fun ξ => ¬ ξ < e) = Z.filter (fun ξ => e < ξ) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hxZ, hxNot⟩
      have hex : e ≠ x := fun h => heZ (h ▸ hxZ)
      exact ⟨hxZ, lt_of_le_of_ne (le_of_not_gt hxNot) hex⟩
    · rintro ⟨hxZ, hex⟩
      exact ⟨hxZ, not_lt_of_ge hex.le⟩
  have hZpart := Finset.card_filter_add_card_filter_not
    (s := Z) (p := fun ξ => ξ < e)
  rw [hnotFilter, hZcard] at hZpart
  have hrankLower : k - 1 ≤ groundRank G e + 1 := by omega
  exact ⟨hrankLower, hrankUpper⟩

/-! ### 8.1 Elementary tools for the four remaining positional regimes -/

private theorem mem_usedGround_of_mem_family {F : Finset (Finset α)}
    {X : Finset α} (hXF : X ∈ F) : X ⊆ usedGround F := by
  intro x hx
  rw [usedGround, Finset.mem_biUnion]
  exact ⟨X, hXF, hx⟩

private theorem groundRank_lt_groundRank_of_lt {G : Finset α} {x y : α}
    (hxG : x ∈ G) (hyG : y ∈ G) (hxy : x < y) :
    groundRank G x < groundRank G y := by
  rw [groundRank, groundRank]
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro z hz
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2.trans hxy⟩
  · intro hback
    have hxRight : x ∈ G.filter fun z => z < y :=
      Finset.mem_filter.mpr ⟨hxG, hxy⟩
    have hxLeft := hback hxRight
    exact (lt_irrefl x) (Finset.mem_filter.mp hxLeft).2

private theorem lt_of_groundRank_lt_groundRank {G : Finset α} {x y : α}
    (hxG : x ∈ G) (hyG : y ∈ G)
    (hRank : groundRank G x < groundRank G y) : x < y := by
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · exact hxy
  · subst y
    exact (lt_irrefl _ hRank).elim
  · have := groundRank_lt_groundRank_of_lt hyG hxG hyx
    omega

private theorem mem_initialSegment_of_groundRank_lt {G : Finset α} {x : α} {j : ℕ}
    (hxG : x ∈ G) (hRank : groundRank G x < j) : x ∈ initialSegment G j := by
  exact Finset.mem_filter.mpr ⟨hxG, hRank⟩

private theorem groundRank_eq_of_mem_notMem_initialSegments
    {G : Finset α} {x : α} {j : ℕ}
    (hxTop : x ∈ initialSegment G (j + 1))
    (hxPrev : x ∉ initialSegment G j) : groundRank G x = j := by
  have hlt : groundRank G x < j + 1 := (Finset.mem_filter.mp hxTop).2
  have hnot : ¬groundRank G x < j := by
    intro h
    exact hxPrev (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxTop).1, h⟩)
  omega

private theorem crossingBarred_nonempty {L : Finset (Finset α)} {A : Finset α}
    (hA : A ∈ L) : (crossingBarred L A).Nonempty := by
  refine ⟨A, mem_crossingBarred_iff.mpr ⟨hA, Or.inl rfl⟩⟩

private theorem crossingBarred_eq_singleton_of_card_one
    {L : Finset (Finset α)} {A : Finset α} (hA : A ∈ L)
    (hcard : (crossingBarred L A).card = 1) : crossingBarred L A = {A} := by
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard
  have hAq : A = q := by
    have : A ∈ ({q} : Finset (Finset α)) := hq ▸
      mem_crossingBarred_iff.mpr ⟨hA, Or.inl rfl⟩
    simpa using this
  simpa [hAq] using hq

private theorem crossingBarred_eq_pair_of_cliqueSum
    {L : Finset (Finset α)} {A Y : Finset α} {hA : A ∈ L} {hY : Y ∈ L}
    (hbad : IsCliqueSum L ⟨A, hA⟩ ⟨Y, hY⟩) :
    crossingBarred L A = {A, Y} := by
  apply Finset.Subset.antisymm
  · intro X hX
    rcases (mem_crossingBarred_iff.mp hX).2 with rfl | ⟨hA', hX', hbadX⟩
    · simp
    · have hEq : (⟨X, hX'⟩ : ExchangeV L) = ⟨Y, hY⟩ :=
        cliqueSum_second_unique hbadX hbad
      have : X = Y := congrArg Subtype.val hEq
      simp [this]
  · intro X hX
    rcases Finset.mem_insert.mp hX with rfl | hX
    · exact mem_crossingBarred_iff.mpr ⟨hA, Or.inl rfl⟩
    · have hXY : X = Y := by simpa using hX
      subst X
      exact mem_crossingBarred_iff.mpr ⟨hY, Or.inr ⟨hA, hY, hbad⟩⟩

private theorem crossingBarred_card_eq_one_or_two
    {L : Finset (Finset α)} {A : Finset α} (hA : A ∈ L) :
    (crossingBarred L A).card = 1 ∨ (crossingBarred L A).card = 2 := by
  have hpos : 0 < (crossingBarred L A).card :=
    Finset.card_pos.mpr (crossingBarred_nonempty hA)
  have hle := crossingBarred_card_le_two hA
  omega

private theorem puncturedLink_card_eq_layerAbove_card
    {F : Finset (Finset α)} {e : α} :
    (puncturedLink F e).card = (layerAbove F e).card := by
  simpa using (Fintype.card_congr (linkVertexEquiv F e)).symm

private theorem puncturedLower_card_eq_layerBelow_card
    {F : Finset (Finset α)} {e : α} :
    (puncturedLower F e).card = (layerBelow F e).card := by
  simpa using (Fintype.card_congr (lowerVertexEquiv F e)).symm

private theorem lift_link_puncture {F : Finset (Finset α)} {e : α}
    {W : Finset α} (hW : W ∈ layerAbove F e) :
    insert e (liftPuncturedSet (punctureSet e W)) = W := by
  rw [liftPuncturedSet_punctureSet]
  exact Finset.insert_erase (Finset.mem_filter.mp hW).2

private theorem lift_lower_puncture {F : Finset (Finset α)} {e : α}
    {Z : Finset α} (hZ : Z ∈ layerBelow F e) :
    liftPuncturedSet (punctureSet e Z) = Z := by
  exact liftPuncturedSet_punctureSet_of_notMem (Finset.mem_filter.mp hZ).2

private theorem raw_link_cliqueSum_to_punctured
    {F : Finset (Finset α)} {e : α} {A Y : Finset α}
    {hA : A ∈ layerAbove F e} {hY : Y ∈ layerAbove F e}
    (hbad : IsCliqueSum (layerAbove F e) ⟨A, hA⟩ ⟨Y, hY⟩) :
    IsCliqueSum (puncturedLink F e)
      (exchangeGraph_puncturedLinkIso F e ⟨A, hA⟩)
      (exchangeGraph_puncturedLinkIso F e ⟨Y, hY⟩) := by
  exact isCliqueSum_map_iso (exchangeGraph_puncturedLinkIso F e) hbad

private theorem raw_lower_cliqueSum_to_punctured
    {F : Finset (Finset α)} {e : α} {B Z : Finset α}
    {hB : B ∈ layerBelow F e} {hZ : Z ∈ layerBelow F e}
    (hbad : IsCliqueSum (layerBelow F e) ⟨B, hB⟩ ⟨Z, hZ⟩) :
    IsCliqueSum (puncturedLower F e)
      (exchangeGraph_puncturedLowerIso F e ⟨B, hB⟩)
      (exchangeGraph_puncturedLowerIso F e ⟨Z, hZ⟩) := by
  exact isCliqueSum_map_iso (exchangeGraph_puncturedLowerIso F e) hbad

/-! ### 8.2 The regime `e = k-1` -/

private theorem not_crossingFailure_of_rank_succ_eq_pred
    {F : Finset (Finset α)} {k : ℕ} (hF : IsShifted F k)
    {A B : Finset α} {e : α}
    (hA : A ∈ layerAbove F e) (hB : B ∈ layerBelow F e)
    (hAbove : 2 ≤ (layerAbove F e).card)
    (hBelow : 2 ≤ (layerBelow F e).card)
    (hpos : groundRank (usedGround F) e + 1 = k - 1) :
    ¬ crossingFailure F A B e := by
  intro hfail
  let G := usedGround F
  let L₁ := layerAbove F e
  let L₀ := layerBelow F e
  let M₁ := initialSegment G k
  let M₂ := secondInitialSegment G k
  let Zc := (initialSegment G (k + 1)).erase e
  have heA : e ∈ A := (Finset.mem_filter.mp hA).2
  have heG : e ∈ G :=
    mem_usedGround_of_mem_family (Finset.mem_filter.mp hA).1 heA
  have heRank : groundRank G e = k - 2 := by
    change groundRank (usedGround F) e = k - 2
    omega
  have hk : 2 ≤ k := by omega
  have heTop : e ∈ initialSegment G (k - 1) := by
    exact mem_initialSegment_of_groundRank_lt heG (by omega)
  have hePrev : e ∉ initialSegment G (k - 2) := by
    intro he
    have := (Finset.mem_filter.mp he).2
    omega
  obtain ⟨Z₀, hZ₀, hZ₀out⟩ := exists_mem_not_crossingBarred hB hBelow
  have high_card_ge_two (Z : Finset α) (hZ : Z ∈ L₀) :
      2 ≤ (Z.filter fun ξ => e < ξ).card := by
    have hZF : Z ∈ F := (Finset.mem_filter.mp hZ).1
    have heZ : e ∉ Z := (Finset.mem_filter.mp hZ).2
    have hZcard : Z.card = k := hF.2.1 Z hZF
    have hZG : Z ⊆ G := mem_usedGround_of_mem_family hZF
    have hlowSub : Z.filter (fun ξ => ξ < e) ⊆ G.filter (fun ξ => ξ < e) := by
      intro x hx
      exact Finset.mem_filter.mpr
        ⟨hZG (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
    have hlowLe : (Z.filter fun ξ => ξ < e).card ≤ k - 2 := by
      have := Finset.card_le_card hlowSub
      change (Z.filter fun ξ => ξ < e).card ≤ groundRank G e at this
      omega
    have hnotFilter : Z.filter (fun ξ => ¬ ξ < e) = Z.filter (fun ξ => e < ξ) := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hxZ, hxNot⟩
        have hex : e ≠ x := fun h => heZ (h ▸ hxZ)
        exact ⟨hxZ, lt_of_le_of_ne (le_of_not_gt hxNot) hex⟩
      · rintro ⟨hxZ, hex⟩
        exact ⟨hxZ, not_lt_of_ge hex.le⟩
    have hpart := Finset.card_filter_add_card_filter_not
      (s := Z) (p := fun ξ => ξ < e)
    rw [hnotFilter, hZcard] at hpart
    omega
  have hZ₀high : 2 ≤ (Z₀.filter fun ξ => e < ξ).card :=
    high_card_ge_two Z₀ hZ₀
  have hup₀ := crossingFailure_up_count_le_two hF hfail hZ₀ hZ₀out hA
  have hbar₁two : (crossingBarred L₁ A).card = 2 := by
    change (crossingBarred (layerAbove F e) A).card = 2
    omega
  obtain ⟨Y, hY, hbadRaw⟩ := exists_cliqueSum_of_crossingBarred_card_two hA hbar₁two
  have hbarRaw : crossingBarred L₁ A = {A, Y} := crossingBarred_eq_pair_of_cliqueSum hbadRaw
  have hbadP := raw_link_cliqueSum_to_punctured hbadRaw
  obtain ⟨r, s, hrG, hrOut, hsG, hrow, hOuter, hInner⟩ :=
    link_yFamily_arms_at_k_pred hF ⟨A, hA⟩ heTop hePrev hbadP
  change r.val ∈ G at hrG
  change r.val ∉ initialSegment G (k + 1) at hrOut
  change s.val ∈ initialSegment G (k - 2) at hsG
  change L₁ =
    (yFamily (G.erase e) (k - 1) r.val s.val).image (fun X => insert e X) at hrow
  change (yOuterArm (G.erase e) (k - 1) r.val).image (fun X => insert e X) =
    linkOuterArmAtPred G k r.val at hOuter
  change (yInnerArm (G.erase e) (k - 1) s.val).image (fun X => insert e X) =
    linkInnerArmAmbient G k s.val at hInner
  have hk3 : 3 ≤ k := by
    have := (Finset.mem_filter.mp hsG).2
    omega
  have hGcard : k + 2 ≤ G.card := by
    have hrRank : k + 1 ≤ groundRank G r.val := by
      exact le_of_not_gt (fun h => hrOut (Finset.mem_filter.mpr ⟨hrG, h⟩))
    have := groundRank_lt_card_of_mem hrG
    omega
  have hPtwo : 2 ≤ (puncturedLink F e).card := by
    rw [puncturedLink_card_eq_layerAbove_card]
    exact hAbove
  have hGcardK : k ≤ (usedGround F).card := by
    change k ≤ G.card
    omega
  have hGcardK1 : k + 1 ≤ (usedGround F).card := by
    change k + 1 ≤ G.card
    omega
  have hpairCoord :
      (A = M₁ ∧ Y = M₂) ∨ (Y = M₁ ∧ A = M₂) := by
    rcases lemma2_universalPair_is_galeLeast
        (isShifted_puncturedLink hF ⟨A, hA⟩) hbadP with hAY | hYA
    · left
      rcases hAY with ⟨hLeast, hSecond⟩
      have hAcoord := link_mu1_of_mem_initial hF ⟨A, hA⟩ (by omega) hGcardK
        (initialSegment_mono G (by omega) heTop) hLeast
      have hYcoord := link_mu2_of_mem_initialPred hF ⟨A, hA⟩ hPtwo hk hGcardK1
        heTop hLeast hSecond
      change insert e (liftPuncturedSet (punctureSet e A)) = M₁ at hAcoord
      change insert e (liftPuncturedSet (punctureSet e Y)) = M₂ at hYcoord
      exact ⟨(lift_link_puncture hA).symm.trans hAcoord,
        (lift_link_puncture hY).symm.trans hYcoord⟩
    · right
      rcases hYA with ⟨hLeast, hSecond⟩
      have hYcoord := link_mu1_of_mem_initial hF ⟨A, hA⟩ (by omega) hGcardK
        (initialSegment_mono G (by omega) heTop) hLeast
      have hAcoord := link_mu2_of_mem_initialPred hF ⟨A, hA⟩ hPtwo hk hGcardK1
        heTop hLeast hSecond
      change insert e (liftPuncturedSet (punctureSet e Y)) = M₁ at hYcoord
      change insert e (liftPuncturedSet (punctureSet e A)) = M₂ at hAcoord
      exact ⟨(lift_link_puncture hY).symm.trans hYcoord,
        (lift_link_puncture hA).symm.trans hAcoord⟩
  have hbar₁ : crossingBarred L₁ A = {M₁, M₂} := by
    rw [hbarRaw]
    rcases hpairCoord with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Finset.pair_comm]
  have hMne : M₁ ≠ M₂ := by
    intro hEq
    have hcardPair : ({M₁, M₂} : Finset (Finset α)).card = 1 := by simp [hEq]
    rw [hbar₁, hcardPair] at hbar₁two
    omega
  have lower_unique : ∀ Z : Finset α, Z ∈ L₀ →
      Z ∉ crossingBarred L₀ B → Z = Zc := by
    intro Z hZ hZout
    let U := Z.filter fun ξ => e < ξ
    let source := fun ξ : α => insert e (Z.erase ξ)
    have hUge : 2 ≤ U.card := high_card_ge_two Z hZ
    have hup := crossingFailure_up_count_le_two hF hfail hZ hZout hA
    have hbarCard : (crossingBarred (layerAbove F e) A).card = 2 := by
      change (crossingBarred L₁ A).card = 2
      exact hbar₁two
    have hUcard : U.card = 2 := by
      change 2 ≤ (Z.filter fun ξ => e < ξ).card at hUge
      change (Z.filter fun ξ => e < ξ).card = 2
      omega
    have hinj : Set.InjOn source (U : Set α) := by
      intro x hx y hy hxy
      have hxZ : x ∈ Z := (Finset.mem_filter.mp hx).1
      have hex : e < x := (Finset.mem_filter.mp hx).2
      by_contra hxyNe
      have hxLeft : x ∉ source x := by simp [source, hex.ne', hxZ]
      have hxRight : x ∈ source y := by
        have hyZ : y ∈ Z := (Finset.mem_filter.mp hy).1
        have hey : e < y := (Finset.mem_filter.mp hy).2
        simp [source, hex.ne', hxZ, hxyNe]
      exact hxLeft (hxy ▸ hxRight)
    have himageSub : U.image source ⊆ {M₁, M₂} := by
      intro W hW
      obtain ⟨ξ, hξU, rfl⟩ := Finset.mem_image.mp hW
      have hξZ : ξ ∈ Z := (Finset.mem_filter.mp hξU).1
      have heξ : e < ξ := (Finset.mem_filter.mp hξU).2
      have hbar := crossingFailure_up_source_mem_crossingBarred hF hfail hZ hZout hξZ heξ
      rw [hbar₁] at hbar
      exact hbar
    have himageCard : (U.image source).card = 2 := by
      rw [Finset.card_image_of_injOn hinj, hUcard]
    have hpairCard : ({M₁, M₂} : Finset (Finset α)).card = 2 := by simp [hMne]
    have himageEq : U.image source = {M₁, M₂} := by
      apply Finset.eq_of_subset_of_card_le himageSub
      rw [himageCard, hpairCard]
    have hM₁image : M₁ ∈ U.image source := by rw [himageEq]; simp
    have hM₂image : M₂ ∈ U.image source := by rw [himageEq]; simp
    obtain ⟨ξ, hξU, hξSource⟩ := Finset.mem_image.mp hM₁image
    obtain ⟨η, hηU, hηSource⟩ := Finset.mem_image.mp hM₂image
    have hξZ : ξ ∈ Z := (Finset.mem_filter.mp hξU).1
    have heξ : e < ξ := (Finset.mem_filter.mp hξU).2
    have hηZ : η ∈ Z := (Finset.mem_filter.mp hηU).1
    have heη : e < η := (Finset.mem_filter.mp hηU).2
    have hξη : ξ ≠ η := by
      intro h
      subst η
      exact hMne (hξSource.symm.trans hηSource)
    have hηM₁ : η ∈ M₁ := by
      rw [← hξSource]
      simp [source, heη.ne', hηZ, hξη.symm]
    have hξM₂ : ξ ∈ M₂ := by
      rw [← hηSource]
      simp [source, heξ.ne', hξZ, hξη]
    have hξNotM₁ : ξ ∉ M₁ := by
      intro hξM₁
      have : ξ ∈ source ξ := hξSource ▸ hξM₁
      exact (by simp [source, heξ.ne', hξZ] : ξ ∉ source ξ) this
    have hξTop : ξ ∈ initialSegment G (k + 1) := by
      change ξ ∈ secondInitialSegment G k at hξM₂
      rcases Finset.mem_union.mp hξM₂ with hsmall | htop
      · exact initialSegment_mono G (by omega) hsmall
      · exact (Finset.mem_sdiff.mp htop).1
    have hInsertXi : insert ξ (initialSegment G k) = initialSegment G (k + 1) :=
      initialSegment_insert_eq_succ_of_top (by omega) hξTop hξNotM₁
    have hZrepr : Z = insert ξ (M₁.erase e) := by
      have heZ : e ∉ Z := (Finset.mem_filter.mp hZ).2
      apply Finset.Subset.antisymm
      · intro x hx
        by_cases hxξ : x = ξ
        · exact Finset.mem_insert.mpr (Or.inl hxξ)
        · apply Finset.mem_insert.mpr
          apply Or.inr
          apply Finset.mem_erase.mpr
          refine ⟨fun hxe => heZ (hxe ▸ hx), ?_⟩
          rw [← hξSource]
          exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hxξ, hx⟩))
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hξZ
        · have hxM₁ := (Finset.mem_erase.mp hx).2
          have hxSource : x ∈ source ξ := hξSource ▸ hxM₁
          rcases Finset.mem_insert.mp hxSource with hxe | hxErase
          · exact ((Finset.mem_erase.mp hx).1 hxe).elim
          · exact Finset.mem_of_mem_erase hxErase
    rw [hZrepr]
    change insert ξ ((initialSegment G k).erase e) =
      (initialSegment G (k + 1)).erase e
    rw [← hInsertXi]
    ext x
    simp only [Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro (rfl | ⟨hxe, hxI⟩)
      · exact ⟨heξ.ne', Or.inl rfl⟩
      · exact ⟨hxe, Or.inr hxI⟩
    · rintro ⟨hxe, rfl | hxI⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hxe, hxI⟩
  have hL₀sub : L₀ ⊆ crossingBarred L₀ B ∪ {Zc} := by
    intro Z hZ
    by_cases hZbar : Z ∈ crossingBarred L₀ B
    · exact Finset.mem_union_left _ hZbar
    · apply Finset.mem_union_right
      simpa [lower_unique Z hZ hZbar]
  have hL₀cardLe : L₀.card ≤ 3 := by
    calc
      L₀.card ≤ (crossingBarred L₀ B ∪ {Zc}).card := Finset.card_le_card hL₀sub
      _ ≤ (crossingBarred L₀ B).card + ({Zc} : Finset (Finset α)).card :=
        Finset.card_union_le _ _
      _ ≤ 3 := by
        have hle := crossingBarred_card_le_two hB
        change (crossingBarred L₀ B).card ≤ 2 at hle
        simp only [Finset.card_singleton]
        omega
  have hbar₀one : (crossingBarred L₀ B).card = 1 := by
    rcases crossingBarred_card_eq_one_or_two hB with hOne | hTwo
    · exact hOne
    · have hfour := crossingBarred_two_forces_four hB hTwo
      change 4 ≤ L₀.card at hfour
      omega
  have hbar₀ : crossingBarred L₀ B = {B} :=
    crossingBarred_eq_singleton_of_card_one hB hbar₀one
  have hZcMem : Zc ∈ L₀ := by
    rw [← lower_unique Z₀ hZ₀ hZ₀out]
    exact hZ₀
  have hZcOut : Zc ∉ crossingBarred L₀ B := by
    rw [← lower_unique Z₀ hZ₀ hZ₀out]
    exact hZ₀out
  have hZcB : Zc ≠ B := by
    intro h
    apply hZcOut
    rw [hbar₀, h]
    simp
  have hL₀eq : L₀ = {B, Zc} := by
    apply Finset.Subset.antisymm
    · intro Z hZ
      by_cases hZbar : Z ∈ crossingBarred L₀ B
      · rw [hbar₀] at hZbar
        have : Z = B := by simpa using hZbar
        simp [this]
      · have := lower_unique Z hZ hZbar
        simp [this]
    · intro Z hZ
      rcases Finset.mem_insert.mp hZ with h | h
      · exact h ▸ hB
      · have : Z = Zc := by simpa using h
        exact this ▸ hZcMem
  have hL₀card : L₀.card = 2 := by rw [hL₀eq]; simp [hZcB.symm]
  have hP₀two : 2 ≤ (puncturedLower F e).card := by
    rw [puncturedLower_card_eq_layerBelow_card]
    change 2 ≤ L₀.card
    omega
  have hP₀shift : IsShifted (puncturedLower F e) k :=
    isShifted_puncturedLower hF ⟨B, hB⟩
  obtain ⟨m₁, m₂, hm₁, hm₂, _i, _j, _him₁, _him₂, _hjm₂, _hjm₁,
      _hij, _hm₂repr, _himax, _hjmin⟩ :=
    exists_gale_bottom_pair_with_boundary hP₀shift hP₀two
  have heK : e ∈ initialSegment G k := initialSegment_mono G (by omega) heTop
  have hm₁coord := layerBelow_m1_of_mem_initial hF ⟨B, hB⟩
    (show k + 1 ≤ (usedGround F).card by change k + 1 ≤ G.card; omega) heK hm₁
  change liftPuncturedSet m₁ = Zc at hm₁coord
  have hm₂coord := layerBelow_m2_of_mem_initial hF ⟨B, hB⟩ hP₀two (by omega)
    (show k + 2 ≤ (usedGround F).card by change k + 2 ≤ G.card; omega)
    heK hm₁ hm₂
  have hm₂below : liftPuncturedSet m₂ ∈ L₀ := by
    change liftPuncturedSet m₂ ∈ layerBelow F e
    exact Finset.mem_filter.mpr
      ⟨mem_puncturedLower_iff.mp hm₂.1, by simp [liftPuncturedSet]⟩
  have hm₂neZc : liftPuncturedSet m₂ ≠ Zc := by
    intro hEq
    apply hm₂.2.1
    have := congrArg (punctureSet e) (hEq.trans hm₁coord.symm)
    simpa using this
  have hm₂eqB : liftPuncturedSet m₂ = B := by
    rw [hL₀eq] at hm₂below
    rcases Finset.mem_insert.mp hm₂below with h | h
    · exact h
    · have : liftPuncturedSet m₂ = Zc := by simpa using h
      exact (hm₂neZc this).elim
  have hBcoord :
      B = (initialSegment G k).erase e ∪ groundPosition G (k + 2) := by
    change liftPuncturedSet m₂ =
      (initialSegment G k).erase e ∪ groundPosition G (k + 2) at hm₂coord
    exact hm₂eqB.symm.trans hm₂coord
  let W := (initialSegment G (k + 1)).erase s.val
  have hWambient : W ∈ linkInnerArmAmbient G k s.val := by
    rw [linkInnerArmAmbient]
    exact Finset.mem_image.mpr
      ⟨s.val, Finset.mem_filter.mpr ⟨hsG, le_rfl⟩, rfl⟩
  have hWinnerImage : W ∈
      (yInnerArm (G.erase e) (k - 1) s.val).image (fun X => insert e X) := by
    rw [hInner]
    exact hWambient
  have hW : W ∈ L₁ := by
    rw [hrow]
    obtain ⟨T, hTinner, hTW⟩ := Finset.mem_image.mp hWinnerImage
    apply Finset.mem_image.mpr
    refine ⟨T, ?_, hTW⟩
    rw [yFamily]
    exact Finset.mem_union_right _ hTinner
  have hsM₁ : s.val ∈ M₁ :=
    initialSegment_mono G (by omega) hsG
  have hsM₂ : s.val ∈ M₂ := by
    change s.val ∈ secondInitialSegment G k
    apply Finset.mem_union.mpr
    exact Or.inl (initialSegment_mono G (by omega) hsG)
  have hsK1 : s.val ∈ initialSegment G (k + 1) :=
    initialSegment_mono G (by omega) hsG
  have hsW : s.val ∉ W := Finset.notMem_erase _ _
  have hWM₁ : W ≠ M₁ := by
    intro h
    exact hsW (h ▸ hsM₁)
  have hWM₂ : W ≠ M₂ := by
    intro h
    exact hsW (h ▸ hsM₂)
  have hWout : W ∉ crossingBarred L₁ A := by
    rw [hbar₁]
    simp [hWM₁, hWM₂]
  have hsG' : s.val ∈ G := initialSegment_subset G (k - 2) hsG
  have hsRank : groundRank G s.val < k - 2 := (Finset.mem_filter.mp hsG).2
  have hse : s.val < e := by
    apply lt_of_groundRank_lt_groundRank hsG' heG
    omega
  have htarget : insert s.val (W.erase e) = Zc := by
    change insert s.val (((initialSegment G (k + 1)).erase s.val).erase e) =
      (initialSegment G (k + 1)).erase e
    ext x
    by_cases hxs : x = s.val
    · subst x
      simp [hse.ne, hsK1]
    · simp [hxs]
  have htargetBar := crossingFailure_down_target_mem_crossingBarred hF hfail hW hWout hse hsW
  rw [htarget, hbar₀] at htargetBar
  have hEq : Zc = B := by simpa using htargetBar
  exact hZcB hEq

/-! ### 8.3 The regime `e = k`: configurations (b) and (c) -/

private theorem not_crossingFailure_at_k_of_left_one_right_two
    {F : Finset (Finset α)} {k : ℕ} (hF : IsShifted F k)
    {A B : Finset α} {e : α}
    (hA : A ∈ layerAbove F e) (hB : B ∈ layerBelow F e)
    (hAbove : 2 ≤ (layerAbove F e).card)
    (hBelow : 2 ≤ (layerBelow F e).card)
    (hpos : groundRank (usedGround F) e + 1 = k)
    (hbar₁one : (crossingBarred (layerAbove F e) A).card = 1)
    (hbar₀two : (crossingBarred (layerBelow F e) B).card = 2) :
    ¬ crossingFailure F A B e := by
  intro hfail
  let G := usedGround F
  let L₁ := layerAbove F e
  let L₀ := layerBelow F e
  let N₁ := (initialSegment G (k + 1)).erase e
  let N₂ := (initialSegment G k).erase e ∪ groundPosition G (k + 2)
  have heA : e ∈ A := (Finset.mem_filter.mp hA).2
  have heG : e ∈ G :=
    mem_usedGround_of_mem_family (Finset.mem_filter.mp hA).1 heA
  have heRank : groundRank G e = k - 1 := by
    change groundRank (usedGround F) e = k - 1
    omega
  have hk : 1 ≤ k := by omega
  have heTop : e ∈ initialSegment G k :=
    mem_initialSegment_of_groundRank_lt heG (by omega)
  have hePrev : e ∉ initialSegment G (k - 1) := by
    intro h
    have := (Finset.mem_filter.mp h).2
    omega
  have hbar₁ : crossingBarred L₁ A = {A} :=
    crossingBarred_eq_singleton_of_card_one hA hbar₁one
  obtain ⟨Y, hY, hbadRaw⟩ := exists_cliqueSum_of_crossingBarred_card_two hB hbar₀two
  have hbarRaw : crossingBarred L₀ B = {B, Y} := crossingBarred_eq_pair_of_cliqueSum hbadRaw
  have hbadP := raw_lower_cliqueSum_to_punctured hbadRaw
  obtain ⟨r, s, hrG, hrOut, hsG, hrow⟩ :=
    layerBelow_yFamily_arms_at_k hF ⟨B, hB⟩ heTop hePrev hbadP
  change r.val ∈ G at hrG
  change r.val ∉ initialSegment G (k + 2) at hrOut
  change s.val ∈ initialSegment G (k - 1) at hsG
  change L₀ =
    ({(initialSegment G (k + 1)).erase e,
        (initialSegment G k).erase e ∪ groundPosition G (k + 2)} ∪
      lowerOuterArmAtK G k r.val) ∪ lowerInnerArmAtK G k e s.val at hrow
  have hk2 : 2 ≤ k := by
    have := (Finset.mem_filter.mp hsG).2
    omega
  have hGcard : k + 3 ≤ G.card := by
    have hrRank : k + 2 ≤ groundRank G r.val := by
      exact le_of_not_gt (fun h => hrOut (Finset.mem_filter.mpr ⟨hrG, h⟩))
    have := groundRank_lt_card_of_mem hrG
    omega
  have hPtwo : 2 ≤ (puncturedLower F e).card := by
    rw [puncturedLower_card_eq_layerBelow_card]
    exact hBelow
  have hpairCoord :
      (B = N₁ ∧ Y = N₂) ∨ (Y = N₁ ∧ B = N₂) := by
    rcases lemma2_universalPair_is_galeLeast
        (isShifted_puncturedLower hF ⟨B, hB⟩) hbadP with hBY | hYB
    · left
      rcases hBY with ⟨hLeast, hSecond⟩
      have hBcoord := layerBelow_m1_of_mem_initial hF ⟨B, hB⟩
        (show k + 1 ≤ (usedGround F).card by change k + 1 ≤ G.card; omega)
        heTop hLeast
      have hYcoord := layerBelow_m2_of_mem_initial hF ⟨B, hB⟩ hPtwo hk
        (show k + 2 ≤ (usedGround F).card by change k + 2 ≤ G.card; omega)
        heTop hLeast hSecond
      change liftPuncturedSet (punctureSet e B) = N₁ at hBcoord
      change liftPuncturedSet (punctureSet e Y) = N₂ at hYcoord
      exact ⟨(lift_lower_puncture hB).symm.trans hBcoord,
        (lift_lower_puncture hY).symm.trans hYcoord⟩
    · right
      rcases hYB with ⟨hLeast, hSecond⟩
      have hYcoord := layerBelow_m1_of_mem_initial hF ⟨B, hB⟩
        (show k + 1 ≤ (usedGround F).card by change k + 1 ≤ G.card; omega)
        heTop hLeast
      have hBcoord := layerBelow_m2_of_mem_initial hF ⟨B, hB⟩ hPtwo hk
        (show k + 2 ≤ (usedGround F).card by change k + 2 ≤ G.card; omega)
        heTop hLeast hSecond
      change liftPuncturedSet (punctureSet e Y) = N₁ at hYcoord
      change liftPuncturedSet (punctureSet e B) = N₂ at hBcoord
      exact ⟨(lift_lower_puncture hY).symm.trans hYcoord,
        (lift_lower_puncture hB).symm.trans hBcoord⟩
  have hbar₀ : crossingBarred L₀ B = {N₁, N₂} := by
    rw [hbarRaw]
    rcases hpairCoord with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Finset.pair_comm]
  let Z := ((initialSegment G (k + 2)).erase e).erase s.val
  have hZinner : Z ∈ lowerInnerArmAtK G k e s.val := by
    rw [lowerInnerArmAtK]
    exact Finset.mem_image.mpr
      ⟨s.val, Finset.mem_filter.mpr ⟨hsG, le_rfl⟩, rfl⟩
  have hZ : Z ∈ L₀ := by
    rw [hrow]
    exact Finset.mem_union_right _ hZinner
  have hsN₁ : s.val ∈ N₁ := by
    exact Finset.mem_erase.mpr
      ⟨s.property, initialSegment_mono G (by omega) hsG⟩
  have hsN₂ : s.val ∈ N₂ := by
    apply Finset.mem_union_left
    exact Finset.mem_erase.mpr
      ⟨s.property, initialSegment_mono G (by omega) hsG⟩
  have hsZ : s.val ∉ Z := Finset.notMem_erase _ _
  have hZN₁ : Z ≠ N₁ := by intro h; exact hsZ (h ▸ hsN₁)
  have hZN₂ : Z ≠ N₂ := by intro h; exact hsZ (h ▸ hsN₂)
  have hZout : Z ∉ crossingBarred L₀ B := by
    rw [hbar₀]
    simp [hZN₁, hZN₂]
  let ip : Fin G.card := ⟨k, by omega⟩
  let iq : Fin G.card := ⟨k + 1, by omega⟩
  let p := G.orderEmbOfFin rfl ip
  let q := G.orderEmbOfFin rfl iq
  have hpG : p ∈ G := Finset.orderEmbOfFin_mem G rfl ip
  have hqG : q ∈ G := Finset.orderEmbOfFin_mem G rfl iq
  have hpRank : groundRank G p = k := by
    simpa [p, ip] using groundRank_orderEmbOfFin G ip
  have hqRank : groundRank G q = k + 1 := by
    simpa [q, iq] using groundRank_orderEmbOfFin G iq
  have hep : e < p := lt_of_groundRank_lt_groundRank heG hpG (by omega)
  have heq : e < q := lt_of_groundRank_lt_groundRank heG hqG (by omega)
  have hpTop : p ∈ initialSegment G (k + 2) :=
    mem_initialSegment_of_groundRank_lt hpG (by omega)
  have hqTop : q ∈ initialSegment G (k + 2) :=
    mem_initialSegment_of_groundRank_lt hqG (by omega)
  have hsRank : groundRank G s.val < k - 1 := (Finset.mem_filter.mp hsG).2
  have hps : p ≠ s.val := by
    intro h
    have hr := congrArg (groundRank G) h
    omega
  have hqs : q ≠ s.val := by
    intro h
    have hr := congrArg (groundRank G) h
    omega
  have hpZ : p ∈ Z := by simp [Z, hep.ne', hps, hpTop]
  have hqZ : q ∈ Z := by simp [Z, heq.ne', hqs, hqTop]
  have hpHigh : p ∈ Z.filter fun ξ => e < ξ := Finset.mem_filter.mpr ⟨hpZ, hep⟩
  have hqHigh : q ∈ Z.filter fun ξ => e < ξ := Finset.mem_filter.mpr ⟨hqZ, heq⟩
  have hpq : p ≠ q := by
    intro h
    have hr := congrArg (groundRank G) h
    omega
  have hHighTwo : 2 ≤ (Z.filter fun ξ => e < ξ).card := by
    have := Finset.one_lt_card.mpr ⟨p, hpHigh, q, hqHigh, hpq⟩
    omega
  have hup := crossingFailure_up_count_le_two hF hfail hZ hZout hA
  omega

private theorem not_crossingFailure_at_k_of_left_two
    {F : Finset (Finset α)} {k : ℕ} (hF : IsShifted F k)
    {A B : Finset α} {e : α}
    (hA : A ∈ layerAbove F e) (hB : B ∈ layerBelow F e)
    (hAbove : 2 ≤ (layerAbove F e).card)
    (hBelow : 2 ≤ (layerBelow F e).card)
    (hpos : groundRank (usedGround F) e + 1 = k)
    (hbar₁two : (crossingBarred (layerAbove F e) A).card = 2) :
    ¬ crossingFailure F A B e := by
  intro hfail
  let G := usedGround F
  let L₁ := layerAbove F e
  let L₀ := layerBelow F e
  let M₁ := initialSegment G k
  let M₂ := initialSegment G (k + 1) \ groundPosition G (k - 1)
  let N₁ := (initialSegment G (k + 1)).erase e
  let N₂ := (initialSegment G k).erase e ∪ groundPosition G (k + 2)
  have heA : e ∈ A := (Finset.mem_filter.mp hA).2
  have heG : e ∈ G :=
    mem_usedGround_of_mem_family (Finset.mem_filter.mp hA).1 heA
  have heRank : groundRank G e = k - 1 := by
    change groundRank (usedGround F) e = k - 1
    omega
  have hk : 1 ≤ k := by omega
  have heTop : e ∈ initialSegment G k :=
    mem_initialSegment_of_groundRank_lt heG (by omega)
  have hePrev : e ∉ initialSegment G (k - 1) := by
    intro h
    have := (Finset.mem_filter.mp h).2
    omega
  obtain ⟨Y₁, hY₁, hbadRaw₁⟩ :=
    exists_cliqueSum_of_crossingBarred_card_two hA hbar₁two
  have hbarRaw₁ : crossingBarred L₁ A = {A, Y₁} := crossingBarred_eq_pair_of_cliqueSum hbadRaw₁
  have hbadP₁ := raw_link_cliqueSum_to_punctured hbadRaw₁
  obtain ⟨r₁, s₁, hr₁G, hr₁Out, hs₁G, hrow₁, hOuter₁, hInner₁⟩ :=
    link_yFamily_arms_at_k hF ⟨A, hA⟩ heTop hePrev hbadP₁
  change r₁.val ∈ G at hr₁G
  change r₁.val ∉ initialSegment G (k + 1) at hr₁Out
  change s₁.val ∈ initialSegment G (k - 2) at hs₁G
  change L₁ =
    (yFamily (G.erase e) (k - 1) r₁.val s₁.val).image (fun X => insert e X) at hrow₁
  change (yOuterArm (G.erase e) (k - 1) r₁.val).image (fun X => insert e X) =
    linkOuterArmAmbient G k e r₁.val at hOuter₁
  change (yInnerArm (G.erase e) (k - 1) s₁.val).image (fun X => insert e X) =
    linkInnerArmAmbient G k s₁.val at hInner₁
  have hk3 : 3 ≤ k := by
    have := (Finset.mem_filter.mp hs₁G).2
    omega
  have hGcard : k + 2 ≤ G.card := by
    have hrRank : k + 1 ≤ groundRank G r₁.val := by
      exact le_of_not_gt (fun h => hr₁Out (Finset.mem_filter.mpr ⟨hr₁G, h⟩))
    have := groundRank_lt_card_of_mem hr₁G
    omega
  have hP₁two : 2 ≤ (puncturedLink F e).card := by
    rw [puncturedLink_card_eq_layerAbove_card]
    exact hAbove
  have hpairCoord₁ :
      (A = M₁ ∧ Y₁ = M₂) ∨ (Y₁ = M₁ ∧ A = M₂) := by
    rcases lemma2_universalPair_is_galeLeast
        (isShifted_puncturedLink hF ⟨A, hA⟩) hbadP₁ with hAY | hYA
    · left
      rcases hAY with ⟨hLeast, hSecond⟩
      have hAcoord := link_mu1_of_mem_initial hF ⟨A, hA⟩ (by omega)
        (show k ≤ (usedGround F).card by change k ≤ G.card; omega) heTop hLeast
      have hYcoord := link_mu2_of_top_initial hF ⟨A, hA⟩ hP₁two (by omega)
        (show k + 1 ≤ (usedGround F).card by change k + 1 ≤ G.card; omega)
        heTop hePrev hLeast hSecond
      change insert e (liftPuncturedSet (punctureSet e A)) = M₁ at hAcoord
      change insert e (liftPuncturedSet (punctureSet e Y₁)) = M₂ at hYcoord
      exact ⟨(lift_link_puncture hA).symm.trans hAcoord,
        (lift_link_puncture hY₁).symm.trans hYcoord⟩
    · right
      rcases hYA with ⟨hLeast, hSecond⟩
      have hYcoord := link_mu1_of_mem_initial hF ⟨A, hA⟩ (by omega)
        (show k ≤ (usedGround F).card by change k ≤ G.card; omega) heTop hLeast
      have hAcoord := link_mu2_of_top_initial hF ⟨A, hA⟩ hP₁two (by omega)
        (show k + 1 ≤ (usedGround F).card by change k + 1 ≤ G.card; omega)
        heTop hePrev hLeast hSecond
      change insert e (liftPuncturedSet (punctureSet e Y₁)) = M₁ at hYcoord
      change insert e (liftPuncturedSet (punctureSet e A)) = M₂ at hAcoord
      exact ⟨(lift_link_puncture hY₁).symm.trans hYcoord,
        (lift_link_puncture hA).symm.trans hAcoord⟩
  have hbar₁ : crossingBarred L₁ A = {M₁, M₂} := by
    rw [hbarRaw₁]
    rcases hpairCoord₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Finset.pair_comm]
  have arm_mem (T : Finset α)
      (hT : T ∈ (yOuterArm (G.erase e) (k - 1) r₁.val).image
        (fun X => insert e X) ∨
        T ∈ (yInnerArm (G.erase e) (k - 1) s₁.val).image
          (fun X => insert e X)) : T ∈ L₁ := by
    rw [hrow₁]
    rcases hT with hT | hT
    · obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hT
      apply Finset.mem_image.mpr
      refine ⟨U, ?_, rfl⟩
      rw [yFamily]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ hU)
    · obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hT
      apply Finset.mem_image.mpr
      refine ⟨U, ?_, rfl⟩
      rw [yFamily]
      exact Finset.mem_union_right _ hU
  let Wq := (initialSegment G (k + 1)).erase s₁.val
  have hWqAmbient : Wq ∈ linkInnerArmAmbient G k s₁.val := by
    rw [linkInnerArmAmbient]
    exact Finset.mem_image.mpr
      ⟨s₁.val, Finset.mem_filter.mpr ⟨hs₁G, le_rfl⟩, rfl⟩
  have hWqImage : Wq ∈
      (yInnerArm (G.erase e) (k - 1) s₁.val).image (fun X => insert e X) := by
    rw [hInner₁]
    exact hWqAmbient
  have hWq : Wq ∈ L₁ := arm_mem Wq (Or.inr hWqImage)
  let Wp := insert e (insert r₁.val (initialSegment G (k - 2)))
  have hWpAmbient : Wp ∈ linkOuterArmAmbient G k e r₁.val := by
    rw [linkOuterArmAmbient]
    exact Finset.mem_image.mpr
      ⟨r₁.val, Finset.mem_filter.mpr ⟨hr₁G, hr₁Out, le_rfl⟩, rfl⟩
  have hWpImage : Wp ∈
      (yOuterArm (G.erase e) (k - 1) r₁.val).image (fun X => insert e X) := by
    rw [hOuter₁]
    exact hWpAmbient
  have hWp : Wp ∈ L₁ := arm_mem Wp (Or.inl hWpImage)
  have hM₁sub : M₁ ⊆ initialSegment G (k + 1) := initialSegment_mono G (by omega)
  have hM₂sub : M₂ ⊆ initialSegment G (k + 1) := Finset.sdiff_subset
  have hrWp : r₁.val ∈ Wp := by simp [Wp]
  have hWpM₁ : Wp ≠ M₁ := by intro h; exact hr₁Out (hM₁sub (h ▸ hrWp))
  have hWpM₂ : Wp ≠ M₂ := by intro h; exact hr₁Out (hM₂sub (h ▸ hrWp))
  have hs₁M₁ : s₁.val ∈ M₁ := initialSegment_mono G (by omega) hs₁G
  have hs₁NotPos : s₁.val ∉ groundPosition G (k - 1) := by
    intro h
    exact (Finset.mem_sdiff.mp h).2 (initialSegment_mono G (by omega) hs₁G)
  have hs₁M₂ : s₁.val ∈ M₂ :=
    Finset.mem_sdiff.mpr ⟨initialSegment_mono G (by omega) hs₁G, hs₁NotPos⟩
  have hs₁Wq : s₁.val ∉ Wq := Finset.notMem_erase _ _
  have hWqM₁ : Wq ≠ M₁ := by intro h; exact hs₁Wq (h ▸ hs₁M₁)
  have hWqM₂ : Wq ≠ M₂ := by intro h; exact hs₁Wq (h ▸ hs₁M₂)
  have hWpOut : Wp ∉ crossingBarred L₁ A := by rw [hbar₁]; simp [hWpM₁, hWpM₂]
  have hWqOut : Wq ∉ crossingBarred L₁ A := by rw [hbar₁]; simp [hWqM₁, hWqM₂]
  let it : Fin G.card := ⟨k - 2, by omega⟩
  let t := G.orderEmbOfFin rfl it
  have htG : t ∈ G := Finset.orderEmbOfFin_mem G rfl it
  have htRank : groundRank G t = k - 2 := by
    simpa [t, it] using groundRank_orderEmbOfFin G it
  have hte : t < e := lt_of_groundRank_lt_groundRank htG heG (by omega)
  have htTop : t ∈ initialSegment G (k - 1) :=
    mem_initialSegment_of_groundRank_lt htG (by omega)
  have htCore : t ∉ initialSegment G (k - 2) := by
    intro h
    have := (Finset.mem_filter.mp h).2
    omega
  have htr : t ≠ r₁.val := by
    intro h
    exact hr₁Out (h ▸ initialSegment_mono G (by omega) htTop)
  have htWp : t ∉ Wp := by simp [Wp, hte.ne, htr, htCore]
  have hs₁e : s₁.val < e := by
    apply lt_of_groundRank_lt_groundRank
      (initialSegment_subset G (k - 2) hs₁G) heG
    have := (Finset.mem_filter.mp hs₁G).2
    omega
  have hs₁K1 : s₁.val ∈ initialSegment G (k + 1) :=
    initialSegment_mono G (by omega) hs₁G
  have hTq : insert s₁.val (Wq.erase e) = N₁ := by
    change insert s₁.val (((initialSegment G (k + 1)).erase s₁.val).erase e) =
      (initialSegment G (k + 1)).erase e
    ext x
    by_cases hxs : x = s₁.val
    · subst x
      simp [hs₁e.ne, hs₁K1]
    · simp [hxs]
  have hInsertT : insert t (initialSegment G (k - 2)) = initialSegment G (k - 1) := by
    have harith : k - 2 + 1 = k - 1 := by omega
    simpa [harith] using initialSegment_insert_eq_succ_of_top
      (G := G) (e := t) (j := k - 2) (by omega) (by simpa [harith] using htTop) htCore
  let Tp := insert r₁.val (initialSegment G (k - 1))
  have hTp : insert t (Wp.erase e) = Tp := by
    have heCore : e ∉ initialSegment G (k - 2) := by
      intro h
      exact hePrev (initialSegment_mono G (by omega) h)
    have her : e ≠ r₁.val := r₁.property.symm
    have heInner : e ∉ insert r₁.val (initialSegment G (k - 2)) := by
      simp [her, heCore]
    change insert t ((insert e (insert r₁.val (initialSegment G (k - 2)))).erase e) =
      insert r₁.val (initialSegment G (k - 1))
    rw [Finset.erase_insert heInner, Finset.insert_comm t r₁.val, hInsertT]
  have hTqBar := crossingFailure_down_target_mem_crossingBarred hF hfail hWq hWqOut hs₁e hs₁Wq
  have hTpBar := crossingFailure_down_target_mem_crossingBarred hF hfail hWp hWpOut hte htWp
  rw [hTq] at hTqBar
  rw [hTp] at hTpBar
  have hrTp : r₁.val ∈ Tp := Finset.mem_insert_self _ _
  have hrN₁ : r₁.val ∉ N₁ := by
    intro h
    exact hr₁Out (initialSegment_mono G (by omega) (Finset.mem_of_mem_erase h))
  have hTpN₁ : Tp ≠ N₁ := by intro h; exact hrN₁ (h ▸ hrTp)
  have hbar₀ge : 2 ≤ (crossingBarred L₀ B).card := by
    have hsub : ({Tp, N₁} : Finset (Finset α)) ⊆ crossingBarred L₀ B := by
      intro X hX
      rcases Finset.mem_insert.mp hX with h | h
      · exact h ▸ hTpBar
      · have : X = N₁ := by simpa using h
        exact this ▸ hTqBar
    have := Finset.card_le_card hsub
    simpa [hTpN₁] using this
  have hbar₀two : (crossingBarred L₀ B).card = 2 := by
    have hle := crossingBarred_card_le_two hB
    change (crossingBarred L₀ B).card ≤ 2 at hle
    omega
  obtain ⟨Y₀, hY₀, hbadRaw₀⟩ :=
    exists_cliqueSum_of_crossingBarred_card_two hB hbar₀two
  have hbarRaw₀ : crossingBarred L₀ B = {B, Y₀} := crossingBarred_eq_pair_of_cliqueSum hbadRaw₀
  have hbadP₀ := raw_lower_cliqueSum_to_punctured hbadRaw₀
  obtain ⟨r₀, s₀, hr₀G, hr₀Out, hs₀G, hrow₀⟩ :=
    layerBelow_yFamily_arms_at_k hF ⟨B, hB⟩ heTop hePrev hbadP₀
  change r₀.val ∈ G at hr₀G
  change r₀.val ∉ initialSegment G (k + 2) at hr₀Out
  change s₀.val ∈ initialSegment G (k - 1) at hs₀G
  change L₀ =
    ({(initialSegment G (k + 1)).erase e,
        (initialSegment G k).erase e ∪ groundPosition G (k + 2)} ∪
      lowerOuterArmAtK G k r₀.val) ∪ lowerInnerArmAtK G k e s₀.val at hrow₀
  have hGcard3 : k + 3 ≤ G.card := by
    have hrRank : k + 2 ≤ groundRank G r₀.val := by
      exact le_of_not_gt (fun h => hr₀Out (Finset.mem_filter.mpr ⟨hr₀G, h⟩))
    have := groundRank_lt_card_of_mem hr₀G
    omega
  have hP₀two : 2 ≤ (puncturedLower F e).card := by
    rw [puncturedLower_card_eq_layerBelow_card]
    exact hBelow
  have hpairCoord₀ :
      (B = N₁ ∧ Y₀ = N₂) ∨ (Y₀ = N₁ ∧ B = N₂) := by
    rcases lemma2_universalPair_is_galeLeast
        (isShifted_puncturedLower hF ⟨B, hB⟩) hbadP₀ with hBY | hYB
    · left
      rcases hBY with ⟨hLeast, hSecond⟩
      have hBcoord := layerBelow_m1_of_mem_initial hF ⟨B, hB⟩
        (show k + 1 ≤ (usedGround F).card by change k + 1 ≤ G.card; omega)
        heTop hLeast
      have hYcoord := layerBelow_m2_of_mem_initial hF ⟨B, hB⟩ hP₀two hk
        (show k + 2 ≤ (usedGround F).card by change k + 2 ≤ G.card; omega)
        heTop hLeast hSecond
      change liftPuncturedSet (punctureSet e B) = N₁ at hBcoord
      change liftPuncturedSet (punctureSet e Y₀) = N₂ at hYcoord
      exact ⟨(lift_lower_puncture hB).symm.trans hBcoord,
        (lift_lower_puncture hY₀).symm.trans hYcoord⟩
    · right
      rcases hYB with ⟨hLeast, hSecond⟩
      have hYcoord := layerBelow_m1_of_mem_initial hF ⟨B, hB⟩
        (show k + 1 ≤ (usedGround F).card by change k + 1 ≤ G.card; omega)
        heTop hLeast
      have hBcoord := layerBelow_m2_of_mem_initial hF ⟨B, hB⟩ hP₀two hk
        (show k + 2 ≤ (usedGround F).card by change k + 2 ≤ G.card; omega)
        heTop hLeast hSecond
      change liftPuncturedSet (punctureSet e Y₀) = N₁ at hYcoord
      change liftPuncturedSet (punctureSet e B) = N₂ at hBcoord
      exact ⟨(lift_lower_puncture hY₀).symm.trans hYcoord,
        (lift_lower_puncture hB).symm.trans hBcoord⟩
  have hbar₀ : crossingBarred L₀ B = {N₁, N₂} := by
    rw [hbarRaw₀]
    rcases hpairCoord₀ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Finset.pair_comm]
  let Z := ((initialSegment G (k + 2)).erase e).erase s₀.val
  have hZinner : Z ∈ lowerInnerArmAtK G k e s₀.val := by
    rw [lowerInnerArmAtK]
    exact Finset.mem_image.mpr
      ⟨s₀.val, Finset.mem_filter.mpr ⟨hs₀G, le_rfl⟩, rfl⟩
  have hZ : Z ∈ L₀ := by rw [hrow₀]; exact Finset.mem_union_right _ hZinner
  have hs₀N₁ : s₀.val ∈ N₁ := Finset.mem_erase.mpr
    ⟨s₀.property, initialSegment_mono G (by omega) hs₀G⟩
  have hs₀N₂ : s₀.val ∈ N₂ := Finset.mem_union_left _ (Finset.mem_erase.mpr
    ⟨s₀.property, initialSegment_mono G (by omega) hs₀G⟩)
  have hs₀Z : s₀.val ∉ Z := Finset.notMem_erase _ _
  have hZN₁ : Z ≠ N₁ := by intro h; exact hs₀Z (h ▸ hs₀N₁)
  have hZN₂ : Z ≠ N₂ := by intro h; exact hs₀Z (h ▸ hs₀N₂)
  have hZout : Z ∉ crossingBarred L₀ B := by rw [hbar₀]; simp [hZN₁, hZN₂]
  let ip : Fin G.card := ⟨k, by omega⟩
  let iq : Fin G.card := ⟨k + 1, by omega⟩
  let p := G.orderEmbOfFin rfl ip
  let q := G.orderEmbOfFin rfl iq
  have hpG : p ∈ G := Finset.orderEmbOfFin_mem G rfl ip
  have hqG : q ∈ G := Finset.orderEmbOfFin_mem G rfl iq
  have hpRank : groundRank G p = k := by
    simpa [p, ip] using groundRank_orderEmbOfFin G ip
  have hqRank : groundRank G q = k + 1 := by
    simpa [q, iq] using groundRank_orderEmbOfFin G iq
  have hep : e < p := lt_of_groundRank_lt_groundRank heG hpG (by omega)
  have hpTop : p ∈ initialSegment G (k + 2) :=
    mem_initialSegment_of_groundRank_lt hpG (by omega)
  have hqTop : q ∈ initialSegment G (k + 2) :=
    mem_initialSegment_of_groundRank_lt hqG (by omega)
  have hpq : p ≠ q := by
    intro h
    have hr := congrArg (groundRank G) h
    omega
  have hs₀Rank : groundRank G s₀.val < k - 1 := (Finset.mem_filter.mp hs₀G).2
  have hps₀ : p ≠ s₀.val := by
    intro h
    have hr := congrArg (groundRank G) h
    omega
  have hqs₀ : q ≠ s₀.val := by
    intro h
    have hr := congrArg (groundRank G) h
    omega
  have hpZ : p ∈ Z := by simp [Z, hep.ne', hps₀, hpTop]
  have hqZ : q ∈ Z := by
    have heq : e ≠ q := by
      intro h
      have hr := congrArg (groundRank G) h
      omega
    simp [Z, heq.symm, hqs₀, hqTop]
  let V := insert e (Z.erase p)
  have hqV : q ∈ V := by simp [V, hpq.symm, hqZ]
  have hqNotUpper : q ∉ initialSegment G (k + 1) := by
    intro h
    have := (Finset.mem_filter.mp h).2
    omega
  have hVM₁ : V ≠ M₁ := by
    intro h
    exact hqNotUpper (initialSegment_mono G (by omega) (h ▸ hqV))
  have hVM₂ : V ≠ M₂ := by
    intro h
    exact hqNotUpper (Finset.sdiff_subset (h ▸ hqV))
  have hVbar := crossingFailure_up_source_mem_crossingBarred hF hfail hZ hZout hpZ hep
  change V ∈ crossingBarred L₁ A at hVbar
  rw [hbar₁] at hVbar
  simp [hVM₁, hVM₂] at hVbar

/-! ### 8.4 The regime `e = k`: configuration (a) forces the exception -/

private theorem cliqueSum_of_crossingFailure_at_k_of_barred_singletons
    {F : Finset (Finset α)} {k : ℕ} (hF : IsShifted F k)
    {A B : Finset α} {e : α}
    (hA : A ∈ layerAbove F e) (hB : B ∈ layerBelow F e)
    (hAbove : 2 ≤ (layerAbove F e).card)
    (hBelow : 2 ≤ (layerBelow F e).card)
    (hpos : groundRank (usedGround F) e + 1 = k)
    (hbar₁one : (crossingBarred (layerAbove F e) A).card = 1)
    (hbar₀one : (crossingBarred (layerBelow F e) B).card = 1)
    (hfail : crossingFailure F A B e) :
    IsCliqueSum F
      ⟨A, (Finset.mem_filter.mp hA).1⟩ ⟨B, (Finset.mem_filter.mp hB).1⟩ := by
  let G := usedGround F
  let L₁ := layerAbove F e
  let L₀ := layerBelow F e
  let C := initialSegment G (k - 1)
  let I := initialSegment G k
  let U := initialSegment G (k + 1)
  have heA : e ∈ A := (Finset.mem_filter.mp hA).2
  have heB : e ∉ B := (Finset.mem_filter.mp hB).2
  have hAF : A ∈ F := (Finset.mem_filter.mp hA).1
  have hBF : B ∈ F := (Finset.mem_filter.mp hB).1
  have hAcard : A.card = k := hF.2.1 A hAF
  have hBcard : B.card = k := hF.2.1 B hBF
  have heG : e ∈ G := mem_usedGround_of_mem_family hAF heA
  have heRank : groundRank G e = k - 1 := by
    change groundRank (usedGround F) e = k - 1
    omega
  have hk : 1 ≤ k := by omega
  have heTop : e ∈ I := mem_initialSegment_of_groundRank_lt heG (by omega)
  have hePrev : e ∉ C := by
    intro h
    have := (Finset.mem_filter.mp h).2
    omega
  have hGcardK : k ≤ G.card := by
    have := groundRank_lt_card_of_mem heG
    omega
  have hCcard : C.card = k - 1 := card_initialSegment_of_le (by omega)
  have hIcard : I.card = k := card_initialSegment_of_le hGcardK
  have hInsertE : insert e C = I := by
    have harith : k - 1 + 1 = k := by omega
    simpa [harith] using initialSegment_insert_eq_succ_of_top
      (G := G) (e := e) (j := k - 1) (by omega)
      (by simpa [harith] using heTop) hePrev
  have hbar₁ : crossingBarred L₁ A = {A} :=
    crossingBarred_eq_singleton_of_card_one hA hbar₁one
  have hbar₀ : crossingBarred L₀ B = {B} :=
    crossingBarred_eq_singleton_of_card_one hB hbar₀one
  have lower_high_ge_one (Z : Finset α) (hZ : Z ∈ L₀) :
      1 ≤ (Z.filter fun ξ => e < ξ).card := by
    have hZF : Z ∈ F := (Finset.mem_filter.mp hZ).1
    have heZ : e ∉ Z := (Finset.mem_filter.mp hZ).2
    have hZcard : Z.card = k := hF.2.1 Z hZF
    have hZG : Z ⊆ G := mem_usedGround_of_mem_family hZF
    have hlowSub : Z.filter (fun ξ => ξ < e) ⊆ G.filter (fun ξ => ξ < e) := by
      intro x hx
      exact Finset.mem_filter.mpr
        ⟨hZG (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
    have hlowLe : (Z.filter fun ξ => ξ < e).card ≤ k - 1 := by
      have := Finset.card_le_card hlowSub
      change (Z.filter fun ξ => ξ < e).card ≤ groundRank G e at this
      omega
    have hnotFilter : Z.filter (fun ξ => ¬ ξ < e) = Z.filter (fun ξ => e < ξ) := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hxZ, hxNot⟩
        have hex : e ≠ x := fun h => heZ (h ▸ hxZ)
        exact ⟨hxZ, lt_of_le_of_ne (le_of_not_gt hxNot) hex⟩
      · rintro ⟨hxZ, hex⟩
        exact ⟨hxZ, not_lt_of_ge hex.le⟩
    have hpart := Finset.card_filter_add_card_filter_not
      (s := Z) (p := fun ξ => ξ < e)
    rw [hnotFilter, hZcard] at hpart
    omega
  obtain ⟨Z₀, hZ₀, hZ₀out⟩ := exists_mem_not_crossingBarred hB hBelow
  have hZ₀highGe := lower_high_ge_one Z₀ hZ₀
  have hup₀ := crossingFailure_up_count_le_two hF hfail hZ₀ hZ₀out hA
  have hZ₀highCard : (Z₀.filter fun ξ => e < ξ).card = 1 := by
    omega
  obtain ⟨ζ₀, hζ₀eq⟩ := Finset.card_eq_one.mp hZ₀highCard
  have hζ₀high : ζ₀ ∈ Z₀.filter fun ξ => e < ξ := by simp [hζ₀eq]
  have hζ₀Z : ζ₀ ∈ Z₀ := (Finset.mem_filter.mp hζ₀high).1
  have heζ₀ : e < ζ₀ := (Finset.mem_filter.mp hζ₀high).2
  have hsource₀ := crossingFailure_up_source_mem_crossingBarred hF hfail hZ₀ hZ₀out hζ₀Z heζ₀
  have hsource₀eq : insert e (Z₀.erase ζ₀) = A := by
    rw [hbar₁] at hsource₀
    simpa using hsource₀
  have hAnoHigh : ∀ x ∈ A, ¬ e < x := by
    intro x hxA hex
    have hxSource : x ∈ insert e (Z₀.erase ζ₀) := hsource₀eq.symm ▸ hxA
    rcases Finset.mem_insert.mp hxSource with hxe | hxErase
    · exact (lt_irrefl e) (hxe ▸ hex)
    · have hxZ : x ∈ Z₀ := Finset.mem_of_mem_erase hxErase
      have hxHigh : x ∈ Z₀.filter fun ξ => e < ξ := Finset.mem_filter.mpr ⟨hxZ, hex⟩
      have hxζ : x = ζ₀ := by
        have : x ∈ ({ζ₀} : Finset α) := hζ₀eq ▸ hxHigh
        simpa using this
      exact (Finset.mem_erase.mp hxErase).1 hxζ
  have hAsubI : A ⊆ I := by
    intro x hxA
    have hxG : x ∈ G := mem_usedGround_of_mem_family hAF hxA
    have hxe : x ≤ e := le_of_not_gt (hAnoHigh x hxA)
    apply mem_initialSegment_of_groundRank_lt hxG
    rcases hxe.eq_or_lt with rfl | hxe
    · omega
    · have := groundRank_lt_groundRank_of_lt hxG heG hxe
      omega
  have hAeq : A = I := by
    apply Finset.eq_of_subset_of_card_le hAsubI
    rw [hAcard, hIcard]
  have hAerase : A.erase e = C := by
    rw [hAeq, ← hInsertE]
    simp [hePrev]
  have lower_repr : ∀ Z : Finset α, Z ∈ L₀ → Z ≠ B →
      ∃ ζ : α, e < ζ ∧ Z = insert ζ C := by
    intro Z hZ hZB
    have hZout : Z ∉ crossingBarred L₀ B := by rw [hbar₀]; simpa [hZB]
    have hhighGe := lower_high_ge_one Z hZ
    have hup := crossingFailure_up_count_le_two hF hfail hZ hZout hA
    have hhighCard : (Z.filter fun ξ => e < ξ).card = 1 := by omega
    obtain ⟨ζ, hζeq⟩ := Finset.card_eq_one.mp hhighCard
    have hζhigh : ζ ∈ Z.filter fun ξ => e < ξ := by simp [hζeq]
    have hζZ : ζ ∈ Z := (Finset.mem_filter.mp hζhigh).1
    have heζ : e < ζ := (Finset.mem_filter.mp hζhigh).2
    have hsource := crossingFailure_up_source_mem_crossingBarred hF hfail hZ hZout hζZ heζ
    have hsourceEq : insert e (Z.erase ζ) = A := by
      rw [hbar₁] at hsource
      simpa using hsource
    refine ⟨ζ, heζ, ?_⟩
    apply Finset.Subset.antisymm
    · intro x hxZ
      by_cases hxζ : x = ζ
      · exact Finset.mem_insert.mpr (Or.inl hxζ)
      · apply Finset.mem_insert.mpr
        apply Or.inr
        have hxe : x ≠ e := fun h => (Finset.mem_filter.mp hZ).2 (h ▸ hxZ)
        have hxA : x ∈ A := by
          rw [← hsourceEq]
          exact Finset.mem_insert.mpr
            (Or.inr (Finset.mem_erase.mpr ⟨hxζ, hxZ⟩))
        rw [← hAerase]
        exact Finset.mem_erase.mpr ⟨hxe, hxA⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxC
      · exact hζZ
      · have hxErase : x ∈ A.erase e := hAerase.symm ▸ hxC
        have hxA : x ∈ A := Finset.mem_of_mem_erase hxErase
        have hxSource : x ∈ insert e (Z.erase ζ) := hsourceEq ▸ hxA
        rcases Finset.mem_insert.mp hxSource with hxe | hxErase
        · have heC : e ∈ C := hxe ▸ hxC
          exact (hePrev heC).elim
        · exact Finset.mem_of_mem_erase hxErase
  have hPreEq : G.filter (fun x => x < e) = C := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxG, hxe⟩ := Finset.mem_filter.mp hx
      apply mem_initialSegment_of_groundRank_lt hxG
      have := groundRank_lt_groundRank_of_lt hxG heG hxe
      omega
    · intro hx
      have hxG := initialSegment_subset G (k - 1) hx
      have hxRank := (Finset.mem_filter.mp hx).2
      have hxe := lt_of_groundRank_lt_groundRank hxG heG (by omega)
      exact Finset.mem_filter.mpr ⟨hxG, hxe⟩
  have upper_missing_one : ∀ W : Finset α, W ∈ L₁ → W ≠ A →
      ((G.filter fun x => x < e) \ W).card = 1 := by
    intro W hW hWA
    obtain ⟨hle, _⟩ := crossingFailure_down_count_le_two hF hfail hW (by
      rw [hbar₁]
      simpa [hWA]) hB
    have hleOne : ((G.filter fun x => x < e) \ W).card ≤ 1 := by
      change ((G.filter fun x => x < e) \ W).card ≤
        (crossingBarred L₀ B).card at hle
      have hbarCard : (crossingBarred L₀ B).card = 1 := by
        change (crossingBarred (layerBelow F e) B).card = 1
        exact hbar₀one
      omega
    have hneZero : ((G.filter fun x => x < e) \ W).card ≠ 0 := by
      intro hzero
      have hsub : C ⊆ W := by
        intro x hxC
        have hxPre : x ∈ G.filter fun x => x < e := hPreEq.symm ▸ hxC
        by_contra hxW
        have hxDiff : x ∈ (G.filter fun x => x < e) \ W :=
          Finset.mem_sdiff.mpr ⟨hxPre, hxW⟩
        have : x ∈ (∅ : Finset α) := (Finset.card_eq_zero.mp hzero) ▸ hxDiff
        simp at this
      have heW : e ∈ W := (Finset.mem_filter.mp hW).2
      have hIsub : I ⊆ W := by rw [← hInsertE]; exact Finset.insert_subset heW hsub
      have hWcard : W.card = k := hF.2.1 W (Finset.mem_filter.mp hW).1
      have hEq : W = I := by
        symm
        apply Finset.eq_of_subset_of_card_le hIsub
        rw [hWcard, hIcard]
      exact hWA (hEq.trans hAeq.symm)
    omega
  obtain ⟨W₀, hW₀, hW₀out⟩ := exists_mem_not_crossingBarred hA hAbove
  have hW₀A : W₀ ≠ A := by
    intro h
    apply hW₀out
    rw [hbar₁, h]
    simp
  have hD₀card := upper_missing_one W₀ hW₀ hW₀A
  obtain ⟨ξ₀, hD₀eq⟩ := Finset.card_eq_one.mp hD₀card
  have hξ₀D : ξ₀ ∈ (G.filter fun x => x < e) \ W₀ := by simp [hD₀eq]
  have hξ₀Pre : ξ₀ ∈ G.filter fun x => x < e := (Finset.mem_sdiff.mp hξ₀D).1
  have hξ₀W : ξ₀ ∉ W₀ := (Finset.mem_sdiff.mp hξ₀D).2
  have hξ₀e : ξ₀ < e := (Finset.mem_filter.mp hξ₀Pre).2
  have htarget₀ := crossingFailure_down_target_mem_crossingBarred hF hfail hW₀ hW₀out hξ₀e hξ₀W
  have htarget₀eq : insert ξ₀ (W₀.erase e) = B := by
    rw [hbar₀] at htarget₀
    simpa using htarget₀
  have hW₀repr : W₀ = insert e (B.erase ξ₀) := by
    apply Finset.Subset.antisymm
    · intro x hxW
      by_cases hxe : x = e
      · exact Finset.mem_insert.mpr (Or.inl hxe)
      · apply Finset.mem_insert.mpr
        apply Or.inr
        apply Finset.mem_erase.mpr
        refine ⟨fun hx => hξ₀W (hx ▸ hxW), ?_⟩
        rw [← htarget₀eq]
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hxe, hxW⟩))
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (Finset.mem_filter.mp hW₀).2
      · have hxB := (Finset.mem_erase.mp hx).2
        have hxTarget : x ∈ insert ξ₀ (W₀.erase e) := htarget₀eq ▸ hxB
        rcases Finset.mem_insert.mp hxTarget with h | h
        · exact ((Finset.mem_erase.mp hx).1 h).elim
        · exact Finset.mem_of_mem_erase h
  have hCsubB : C ⊆ B := by
    intro x hxC
    have hxPre : x ∈ G.filter fun x => x < e := hPreEq.symm ▸ hxC
    by_cases hxξ : x = ξ₀
    · rw [← htarget₀eq, hxξ]
      exact Finset.mem_insert_self _ _
    · have hxW : x ∈ W₀ := by
        by_contra hxNot
        have hxD : x ∈ (G.filter fun x => x < e) \ W₀ :=
          Finset.mem_sdiff.mpr ⟨hxPre, hxNot⟩
        have : x ∈ ({ξ₀} : Finset α) := hD₀eq ▸ hxD
        exact hxξ (by simpa using this)
      rw [← htarget₀eq]
      exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hxPre).2.ne, hxW⟩))
  have hBdiffCard : (B \ C).card = 1 := by
    rw [Finset.card_sdiff_of_subset hCsubB, hBcard, hCcard]
    omega
  obtain ⟨γ, hγdiffEq⟩ := Finset.card_eq_one.mp hBdiffCard
  have hγdiff : γ ∈ B \ C := by simp [hγdiffEq]
  have hγB : γ ∈ B := (Finset.mem_sdiff.mp hγdiff).1
  have hγC : γ ∉ C := (Finset.mem_sdiff.mp hγdiff).2
  have hBeq : B = insert γ C := by
    apply Finset.Subset.antisymm
    · intro x hxB
      by_cases hxC : x ∈ C
      · exact Finset.mem_insert.mpr (Or.inr hxC)
      · have hxDiff : x ∈ B \ C := Finset.mem_sdiff.mpr ⟨hxB, hxC⟩
        have : x ∈ ({γ} : Finset α) := hγdiffEq ▸ hxDiff
        exact Finset.mem_insert.mpr (Or.inl (by simpa using this))
    · exact Finset.insert_subset hγB hCsubB
  have hγG : γ ∈ G := mem_usedGround_of_mem_family hBF hγB
  have heγ : e < γ := by
    rcases lt_trichotomy e γ with h | h | h
    · exact h
    · exact (heB (h ▸ hγB)).elim
    · have hγPre : γ ∈ G.filter fun x => x < e := Finset.mem_filter.mpr ⟨hγG, h⟩
      exact (hγC (hPreEq ▸ hγPre)).elim
  have hγRankLower : k ≤ groundRank G γ := by
    have := groundRank_lt_groundRank_of_lt heG hγG heγ
    omega
  have hGcardK1 : k + 1 ≤ G.card := by
    have := groundRank_lt_card_of_mem hγG
    omega
  have hγTop : γ ∈ U := by
    by_contra hγNot
    have hγRankHigh : k + 1 ≤ groundRank G γ := by
      exact le_of_not_gt (fun h => hγNot (Finset.mem_filter.mpr ⟨hγG, h⟩))
    let ip : Fin G.card := ⟨k, by omega⟩
    let p := G.orderEmbOfFin rfl ip
    have hpG : p ∈ G := Finset.orderEmbOfFin_mem G rfl ip
    have hpRank : groundRank G p = k := by
      simpa [p, ip] using groundRank_orderEmbOfFin G ip
    have hpγ : p < γ := lt_of_groundRank_lt_groundRank hpG hγG (by omega)
    have hpC : p ∉ C := by
      intro h
      have := (Finset.mem_filter.mp h).2
      omega
    have hpB : p ∉ B := by
      rw [hBeq]
      simp [hpC, hpγ.ne]
    have hγξ : γ ≠ ξ₀ := by
      intro h
      subst γ
      exact hγC (hPreEq ▸ hξ₀Pre)
    have hγW₀ : γ ∈ W₀ := by
      have hγtarget : γ ∈ insert ξ₀ (W₀.erase e) := htarget₀eq ▸ hγB
      rcases Finset.mem_insert.mp hγtarget with h | h
      · exact (hγξ h).elim
      · exact Finset.mem_of_mem_erase h
    have hep : e < p := lt_of_groundRank_lt_groundRank heG hpG (by omega)
    have hpW₀ : p ∉ W₀ := by
      intro hpW
      apply hpB
      rw [← htarget₀eq]
      exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_erase.mpr ⟨hep.ne', hpW⟩))
    let W' := insert p (W₀.erase γ)
    have hW'F : W' ∈ F := hF.2.2 W₀ (Finset.mem_filter.mp hW₀).1
      p γ hγW₀ hpγ hpW₀
    have heW' : e ∈ W' := by
      apply Finset.mem_insert.mpr
      apply Or.inr
      exact Finset.mem_erase.mpr ⟨heγ.ne, (Finset.mem_filter.mp hW₀).2⟩
    have hW' : W' ∈ L₁ := Finset.mem_filter.mpr ⟨hW'F, heW'⟩
    have hξW' : ξ₀ ∉ W' := by
      have hξp : ξ₀ ≠ p := by
        intro h
        have hr := congrArg (groundRank G) h
        have hξRank := groundRank_lt_groundRank_of_lt
          (Finset.mem_filter.mp hξ₀Pre).1 heG hξ₀e
        omega
      simp [W', hξp, hξ₀W]
    have hW'A : W' ≠ A := by
      intro h
      have hξA : ξ₀ ∈ A := by
        rw [hAeq, ← hInsertE]
        exact Finset.mem_insert.mpr (Or.inr (hPreEq ▸ hξ₀Pre))
      exact hξW' (h ▸ hξA)
    have hW'out : W' ∉ crossingBarred L₁ A := by rw [hbar₁]; simpa [hW'A]
    have htarget' := crossingFailure_down_target_mem_crossingBarred hF hfail hW' hW'out
      hξ₀e hξW'
    have htarget'Eq : insert ξ₀ (W'.erase e) = B := by
      rw [hbar₀] at htarget'
      simpa using htarget'
    have htarget'Form : insert ξ₀ (W'.erase e) = insert p C := by
      have hξC : ξ₀ ∈ C := hPreEq ▸ hξ₀Pre
      have hξp : ξ₀ ≠ p := by
        intro h
        have hr := congrArg (groundRank G) h
        have hξRank := groundRank_lt_groundRank_of_lt
          (Finset.mem_filter.mp hξ₀Pre).1 heG hξ₀e
        omega
      ext x
      simp only [W', hW₀repr, hBeq, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro (rfl | ⟨_hxe, rfl | ⟨_hxγ, rfl | ⟨_hxξ, rfl | hxC⟩⟩⟩)
        · exact Or.inr hξC
        · exact Or.inl rfl
        · exact (_hxe rfl).elim
        · exact (_hxγ rfl).elim
        · exact Or.inr hxC
      · rintro (rfl | hxC)
        · exact Or.inr ⟨hep.ne', Or.inl rfl⟩
        · by_cases hxξ : x = ξ₀
          · exact Or.inl hxξ
          · have hxe : x ≠ e := fun h => hePrev (h ▸ hxC)
            by_cases hxp : x = p
            · exact Or.inr ⟨hxe, Or.inl hxp⟩
            · have hxγ : x ≠ γ := fun h => hγC (h ▸ hxC)
              exact Or.inr ⟨hxe, Or.inr ⟨hxγ, Or.inr ⟨hxξ, Or.inr hxC⟩⟩⟩
    have hγTarget : γ ∈ insert ξ₀ (W'.erase e) := htarget'Eq ▸ hγB
    rw [htarget'Form] at hγTarget
    have hγp : γ ≠ p := hpγ.ne'
    have : γ ∈ C := by simpa [hγp] using hγTarget
    exact hγC this
  have hγNotI : γ ∉ I := by
    intro h
    have := (Finset.mem_filter.mp h).2
    omega
  have hInsertGamma : insert γ I = U :=
    initialSegment_insert_eq_succ_of_top hGcardK1 hγTop hγNotI
  have hPosGamma : groundPosition G (k + 1) = {γ} := by
    exact groundPosition_eq_singleton_of_top (by omega) hGcardK1 hγTop hγNotI
  have hBeqM₂ : B = secondInitialSegment G k := by
    change U \ I = {γ} at hPosGamma
    rw [hBeq, secondInitialSegment]
    change insert γ C = C ∪ (U \ I)
    rw [hPosGamma]
    ext x
    simp [or_comm]
  have hUcard : U.card = k + 1 := card_initialSegment_of_le hGcardK1
  have hUform : U = insert γ (insert e C) := by
    rw [← hInsertGamma, ← hInsertE]
  have upper_repr : ∀ W : Finset α, W ∈ L₁ → W ≠ A →
      ∃ ξ ∈ C, W = U.erase ξ := by
    intro W hW hWA
    have hDcard := upper_missing_one W hW hWA
    obtain ⟨ξ, hDeq⟩ := Finset.card_eq_one.mp hDcard
    have hξD : ξ ∈ (G.filter fun x => x < e) \ W := by simp [hDeq]
    have hξPre : ξ ∈ G.filter fun x => x < e := (Finset.mem_sdiff.mp hξD).1
    have hξW : ξ ∉ W := (Finset.mem_sdiff.mp hξD).2
    have hξe : ξ < e := (Finset.mem_filter.mp hξPre).2
    have hWout : W ∉ crossingBarred L₁ A := by rw [hbar₁]; simpa [hWA]
    have htarget := crossingFailure_down_target_mem_crossingBarred hF hfail hW hWout hξe hξW
    have htargetEq : insert ξ (W.erase e) = B := by
      rw [hbar₀] at htarget
      simpa using htarget
    have hWrepr : W = insert e (B.erase ξ) := by
      apply Finset.Subset.antisymm
      · intro x hxW
        by_cases hxe : x = e
        · exact Finset.mem_insert.mpr (Or.inl hxe)
        · apply Finset.mem_insert.mpr
          apply Or.inr
          apply Finset.mem_erase.mpr
          refine ⟨fun hx => hξW (hx ▸ hxW), ?_⟩
          rw [← htargetEq]
          exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hxe, hxW⟩))
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact (Finset.mem_filter.mp hW).2
        · have hxB := (Finset.mem_erase.mp hx).2
          have hxTarget : x ∈ insert ξ (W.erase e) := htargetEq ▸ hxB
          rcases Finset.mem_insert.mp hxTarget with h | h
          · exact ((Finset.mem_erase.mp hx).1 h).elim
          · exact Finset.mem_of_mem_erase h
    have hξC : ξ ∈ C := hPreEq ▸ hξPre
    refine ⟨ξ, hξC, ?_⟩
    rw [hWrepr, hBeq, hUform]
    ext x
    simp only [Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro (rfl | ⟨hxξ, rfl | hxC⟩)
      · exact ⟨hξe.ne', Or.inr (Or.inl rfl)⟩
      · exact ⟨hxξ, Or.inl rfl⟩
      · exact ⟨hxξ, Or.inr (Or.inr hxC)⟩
    · rintro ⟨hxξ, rfl | rfl | hxC⟩
      · exact Or.inr ⟨hxξ, Or.inl rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hxξ, Or.inr hxC⟩
  have hZ₀B : Z₀ ≠ B := by
    intro h
    apply hZ₀out
    rw [hbar₀, h]
    simp
  have hZ₀A : Z₀ ≠ A := by
    intro h
    exact (Finset.mem_filter.mp hZ₀).2 (h ▸ heA)
  have hW₀B : W₀ ≠ B := by
    intro h
    exact heB (h ▸ (Finset.mem_filter.mp hW₀).2)
  let AV : ExchangeV F := ⟨A, hAF⟩
  let BV : ExchangeV F := ⟨B, hBF⟩
  let WV : ExchangeV F := ⟨W₀, (Finset.mem_filter.mp hW₀).1⟩
  let ZV : ExchangeV F := ⟨Z₀, (Finset.mem_filter.mp hZ₀).1⟩
  have hAB : AV ≠ BV := by
    intro h
    have hval : A = B := by simpa [AV, BV] using congrArg Subtype.val h
    exact heB (hval ▸ heA)
  have common_lower_adj {X Y : Finset α} (hXF : X ∈ F) (hYF : Y ∈ F)
      (hCX : C ⊆ X) (hCY : C ⊆ Y) (hXY : X ≠ Y) :
      (exchangeGraph F).Adj (⟨X, hXF⟩ : ExchangeV F) ⟨Y, hYF⟩ := by
    apply exchangeGraph_adj_of_common_lowerCover hXF hYF hCX hCY
    · rw [hF.2.1 X hXF, hCcard]
      omega
    · rw [hF.2.1 Y hYF, hCcard]
      omega
    · exact hXY
  have common_upper_adj {X Y : Finset α} (hXF : X ∈ F) (hYF : Y ∈ F)
      (hXU : X ⊆ U) (hYU : Y ⊆ U) (hXY : X ≠ Y) :
      (exchangeGraph F).Adj (⟨X, hXF⟩ : ExchangeV F) ⟨Y, hYF⟩ := by
    apply exchangeGraph_adj_of_common_upperCover hXF hYF hXU hYU
    · rw [hUcard, hF.2.1 X hXF]
    · rw [hUcard, hF.2.1 Y hYF]
    · exact hXY
  have hCsubI : C ⊆ I := initialSegment_mono G (by omega)
  have hIsubU : I ⊆ U := initialSegment_mono G (by omega)
  have hCsubU : C ⊆ U := hCsubI.trans hIsubU
  have hAsubU : A ⊆ U := hAeq ▸ hIsubU
  have hBsubU : B ⊆ U := by
    rw [hBeq, hUform]
    intro x hx
    simp only [Finset.mem_insert] at hx ⊢
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (Or.inr hx)
  have hAuniv : (exchangeGraph F).IsUniversalVertex AV := by
    intro X hXA
    by_cases heX : e ∈ X.val
    · have hXL₁ : X.val ∈ L₁ := Finset.mem_filter.mpr ⟨X.prop, heX⟩
      have hXneA : X.val ≠ A := by
        intro h
        apply hXA
        apply Subtype.ext
        simpa [AV] using h
      obtain ⟨ξ, hξC, hXrepr⟩ := upper_repr X.val hXL₁ hXneA
      apply common_upper_adj hAF X.prop hAsubU
        (by rw [hXrepr]; exact Finset.erase_subset _ _)
      intro h
      apply hXA
      apply Subtype.ext
      simpa [AV] using h.symm
    · have hXL₀ : X.val ∈ L₀ := Finset.mem_filter.mpr ⟨X.prop, heX⟩
      by_cases hXeqB : X.val = B
      · apply common_lower_adj hAF X.prop
          (by rw [hAeq, ← hInsertE]; exact Finset.subset_insert _ _)
          (by rw [hXeqB]; exact hCsubB)
        intro h
        apply hXA
        apply Subtype.ext
        simpa [AV] using h.symm
      · obtain ⟨ζ, heζ, hXrepr⟩ := lower_repr X.val hXL₀ hXeqB
        apply common_lower_adj hAF X.prop
          (by rw [hAeq, ← hInsertE]; exact Finset.subset_insert _ _)
          (by rw [hXrepr]; exact Finset.subset_insert _ _)
        intro h
        apply hXA
        apply Subtype.ext
        simpa [AV] using h.symm
  have hBuniv : (exchangeGraph F).IsUniversalVertex BV := by
    intro X hXB
    by_cases heX : e ∈ X.val
    · have hXL₁ : X.val ∈ L₁ := Finset.mem_filter.mpr ⟨X.prop, heX⟩
      by_cases hXeqA : X.val = A
      · apply common_upper_adj hBF X.prop hBsubU (by rw [hXeqA]; exact hAsubU)
        intro h
        apply hXB
        apply Subtype.ext
        simpa [BV] using h.symm
      · obtain ⟨ξ, hξC, hXrepr⟩ := upper_repr X.val hXL₁ hXeqA
        apply common_upper_adj hBF X.prop hBsubU
          (by rw [hXrepr]; exact Finset.erase_subset _ _)
        intro h
        apply hXB
        apply Subtype.ext
        simpa [BV] using h.symm
    · have hXL₀ : X.val ∈ L₀ := Finset.mem_filter.mpr ⟨X.prop, heX⟩
      have hXneB : X.val ≠ B := by
        intro h
        apply hXB
        apply Subtype.ext
        simpa [BV] using h
      obtain ⟨ζ, heζ, hXrepr⟩ := lower_repr X.val hXL₀ hXneB
      apply common_lower_adj hBF X.prop hCsubB
        (by rw [hXrepr]; exact Finset.subset_insert _ _)
      intro h
      apply hXB
      apply Subtype.ext
      simpa [BV] using h.symm
  refine ⟨hAB, hAuniv, hBuniv, (fun X => decide (e ∈ X.val)), ?_, ?_, ?_⟩
  · refine ⟨WV, ?_, ?_, ?_⟩
    · exact fun h => hW₀A (congrArg Subtype.val h)
    · exact fun h => hW₀B (congrArg Subtype.val h)
    · simp [WV, (Finset.mem_filter.mp hW₀).2]
  · refine ⟨ZV, ?_, ?_, ?_⟩
    · exact fun h => hZ₀A (congrArg Subtype.val h)
    · exact fun h => hZ₀B (congrArg Subtype.val h)
    · simp [ZV, (Finset.mem_filter.mp hZ₀).2]
  · intro X Y hXA hXB hYA hYB hXY
    have hXneA : X.val ≠ A := by
      intro h; apply hXA; apply Subtype.ext; simpa [AV] using h
    have hXneB : X.val ≠ B := by
      intro h; apply hXB; apply Subtype.ext; simpa [BV] using h
    have hYneA : Y.val ≠ A := by
      intro h; apply hYA; apply Subtype.ext; simpa [AV] using h
    have hYneB : Y.val ≠ B := by
      intro h; apply hYB; apply Subtype.ext; simpa [BV] using h
    by_cases heX : e ∈ X.val <;> by_cases heY : e ∈ Y.val
    · have hXL₁ : X.val ∈ L₁ := Finset.mem_filter.mpr ⟨X.prop, heX⟩
      have hYL₁ : Y.val ∈ L₁ := Finset.mem_filter.mpr ⟨Y.prop, heY⟩
      obtain ⟨ξ, hξC, hXrepr⟩ := upper_repr X.val hXL₁ hXneA
      obtain ⟨η, hηC, hYrepr⟩ := upper_repr Y.val hYL₁ hYneA
      have hAdj := common_upper_adj X.prop Y.prop
        (by rw [hXrepr]; exact Finset.erase_subset _ _)
        (by rw [hYrepr]; exact Finset.erase_subset _ _)
        (fun h => hXY (Subtype.ext h))
      simp [heX, heY, hAdj]
    · have hXL₁ : X.val ∈ L₁ := Finset.mem_filter.mpr ⟨X.prop, heX⟩
      have hYL₀ : Y.val ∈ L₀ := Finset.mem_filter.mpr ⟨Y.prop, heY⟩
      obtain ⟨ξ, hξC, hXrepr⟩ := upper_repr X.val hXL₁ hXneA
      obtain ⟨ζ, heζ, hYrepr⟩ := lower_repr Y.val hYL₀ hYneB
      have hζγ : ζ ≠ γ := by
        intro h
        apply hYneB
        rw [hYrepr, hBeq, h]
      have heXdiff : e ∈ X.val \ Y.val := Finset.mem_sdiff.mpr ⟨heX, heY⟩
      have hγX : γ ∈ X.val := by
        rw [hXrepr, hUform]
        exact Finset.mem_erase.mpr
          ⟨fun h => hγC (h ▸ hξC), Finset.mem_insert_self _ _⟩
      have hγY : γ ∉ Y.val := by rw [hYrepr]; simp [hζγ.symm, hγC]
      have hγdiff : γ ∈ X.val \ Y.val := Finset.mem_sdiff.mpr ⟨hγX, hγY⟩
      have heγne : e ≠ γ := heγ.ne
      have htwo : 2 ≤ (X.val \ Y.val).card := by
        have := Finset.one_lt_card.mpr ⟨e, heXdiff, γ, hγdiff, heγne⟩
        omega
      have hnotAdj : ¬(exchangeGraph F).Adj X Y := by
        intro hAdj
        simp only [exchangeGraph, SimpleGraph.fromRel_adj] at hAdj
        have hcardEq : X.val.card = Y.val.card :=
          (hF.2.1 X.val X.prop).trans (hF.2.1 Y.val Y.prop).symm
        have hsymm : (X.val ∆ Y.val).card = 2 := by
          rcases hAdj.2 with h | h
          · exact h
          · simpa [symmDiff_comm] using h
        have hone := (card_symmDiff_eq_two_iff hcardEq).mp hsymm
        omega
      simp [heX, heY, hnotAdj]
    · have hXL₀ : X.val ∈ L₀ := Finset.mem_filter.mpr ⟨X.prop, heX⟩
      have hYL₁ : Y.val ∈ L₁ := Finset.mem_filter.mpr ⟨Y.prop, heY⟩
      obtain ⟨ζ, heζ, hXrepr⟩ := lower_repr X.val hXL₀ hXneB
      obtain ⟨ξ, hξC, hYrepr⟩ := upper_repr Y.val hYL₁ hYneA
      have hζγ : ζ ≠ γ := by
        intro h
        apply hXneB
        rw [hXrepr, hBeq, h]
      have heYdiff : e ∈ Y.val \ X.val := Finset.mem_sdiff.mpr ⟨heY, heX⟩
      have hγY : γ ∈ Y.val := by
        rw [hYrepr, hUform]
        exact Finset.mem_erase.mpr
          ⟨fun h => hγC (h ▸ hξC), Finset.mem_insert_self _ _⟩
      have hγX : γ ∉ X.val := by rw [hXrepr]; simp [hζγ.symm, hγC]
      have hγdiff : γ ∈ Y.val \ X.val := Finset.mem_sdiff.mpr ⟨hγY, hγX⟩
      have heγne : e ≠ γ := heγ.ne
      have htwo : 2 ≤ (Y.val \ X.val).card := by
        have := Finset.one_lt_card.mpr ⟨e, heYdiff, γ, hγdiff, heγne⟩
        omega
      have hnotAdj : ¬(exchangeGraph F).Adj X Y := by
        intro hAdj
        simp only [exchangeGraph, SimpleGraph.fromRel_adj] at hAdj
        have hcardEq : Y.val.card = X.val.card :=
          (hF.2.1 Y.val Y.prop).trans (hF.2.1 X.val X.prop).symm
        have hsymm : (Y.val ∆ X.val).card = 2 := by
          rcases hAdj.2 with h | h
          · simpa [symmDiff_comm] using h
          · exact h
        have hone := (card_symmDiff_eq_two_iff hcardEq).mp hsymm
        omega
      simp [heX, heY, hnotAdj]
    · have hXL₀ : X.val ∈ L₀ := Finset.mem_filter.mpr ⟨X.prop, heX⟩
      have hYL₀ : Y.val ∈ L₀ := Finset.mem_filter.mpr ⟨Y.prop, heY⟩
      obtain ⟨ζ, heζ, hXrepr⟩ := lower_repr X.val hXL₀ hXneB
      obtain ⟨η, heη, hYrepr⟩ := lower_repr Y.val hYL₀ hYneB
      have hAdj := common_lower_adj X.prop Y.prop
        (by rw [hXrepr]; exact Finset.subset_insert _ _)
        (by rw [hYrepr]; exact Finset.subset_insert _ _)
        (fun h => hXY (Subtype.ext h))
      simp [heX, heY, hAdj]

/-- The middle regime: the two barred-card choices on each side give exactly configurations
(a)--(c).  The sole non-contradictory configuration forces the excluded clique-sum. -/
private theorem not_crossingFailure_at_k
    {F : Finset (Finset α)} {k : ℕ} (hF : IsShifted F k)
    {A B : ExchangeV F} {e : α}
    (heA : e ∈ A.val) (heB : e ∉ B.val)
    (hAbove : 2 ≤ (layerAbove F e).card)
    (hBelow : 2 ≤ (layerBelow F e).card)
    (hpos : groundRank (usedGround F) e + 1 = k)
    (hnotexc : ¬ IsCliqueSum F A B) :
    ¬ crossingFailure F A.val B.val e := by
  have hA : A.val ∈ layerAbove F e := Finset.mem_filter.mpr ⟨A.prop, heA⟩
  have hB : B.val ∈ layerBelow F e := Finset.mem_filter.mpr ⟨B.prop, heB⟩
  rcases crossingBarred_card_eq_one_or_two hA with hbar₁one | hbar₁two
  · rcases crossingBarred_card_eq_one_or_two hB with hbar₀one | hbar₀two
    · intro hfail
      apply hnotexc
      simpa using cliqueSum_of_crossingFailure_at_k_of_barred_singletons
        hF hA hB hAbove hBelow hpos hbar₁one hbar₀one hfail
    · exact not_crossingFailure_at_k_of_left_one_right_two
        hF hA hB hAbove hBelow hpos hbar₁one hbar₀two
  · exact not_crossingFailure_at_k_of_left_two
      hF hA hB hAbove hBelow hpos hbar₁two

/-! ### 8.5 Canonical finite-ground relabelling

The public lemma is polymorphic in the ambient order, whereas `dualSet` deliberately lives on
`Fin n`.  We therefore relabel the finite ground actually used by the family with its increasing
enumeration.  No ambient point outside that ground enters the relabelled family. -/

private def groundIndexSet (G : Finset α) (X : Finset α) : Finset (Fin G.card) :=
  (X.subtype fun x => x ∈ G).map (G.orderIsoOfFin rfl).symm.toEmbedding

private def groundLiftSet (G : Finset α) (X : Finset (Fin G.card)) : Finset α :=
  X.map (G.orderEmbOfFin rfl).toEmbedding

private def groundIndexFamily (G : Finset α) (F : Finset (Finset α)) :
    Finset (Finset (Fin G.card)) :=
  F.image (groundIndexSet G)

@[simp] private theorem mem_groundIndexSet_iff (G : Finset α) (X : Finset α)
    (i : Fin G.card) :
    i ∈ groundIndexSet G X ↔ G.orderEmbOfFin rfl i ∈ X := by
  simp [groundIndexSet]

@[simp] private theorem mem_groundLiftSet_iff (G : Finset α) (X : Finset (Fin G.card))
    (x : α) :
    x ∈ groundLiftSet G X ↔
      ∃ i ∈ X, G.orderEmbOfFin rfl i = x := by
  simp [groundLiftSet]

@[simp] private theorem orderEmb_mem_groundLiftSet_iff (G : Finset α)
    (X : Finset (Fin G.card)) (i : Fin G.card) :
    G.orderEmbOfFin rfl i ∈ groundLiftSet G X ↔ i ∈ X := by
  simp [groundLiftSet]

private theorem groundLiftSet_groundIndexSet_of_subset (G : Finset α) (X : Finset α)
    (hXG : X ⊆ G) :
    groundLiftSet G (groundIndexSet G X) = X := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, hix⟩ := mem_groundLiftSet_iff G _ x |>.mp hx
    exact hix ▸ (mem_groundIndexSet_iff G X i).mp hi
  · intro hx
    let i : Fin G.card := (G.orderIsoOfFin rfl).symm ⟨x, hXG hx⟩
    have hix : G.orderEmbOfFin rfl i = x := by
      exact congrArg Subtype.val ((G.orderIsoOfFin rfl).apply_symm_apply ⟨x, hXG hx⟩)
    apply (mem_groundLiftSet_iff G _ x).mpr
    exact ⟨i, (mem_groundIndexSet_iff G X i).mpr (hix ▸ hx), hix⟩

@[simp] private theorem groundIndexSet_groundLiftSet (G : Finset α)
    (X : Finset (Fin G.card)) :
    groundIndexSet G (groundLiftSet G X) = X := by
  ext i
  rw [mem_groundIndexSet_iff]
  simp [groundLiftSet]

private theorem groundIndexSet_injective_on_subsets (G : Finset α)
    {X Y : Finset α} (hXG : X ⊆ G) (hYG : Y ⊆ G)
    (h : groundIndexSet G X = groundIndexSet G Y) : X = Y := by
  rw [← groundLiftSet_groundIndexSet_of_subset G X hXG,
    ← groundLiftSet_groundIndexSet_of_subset G Y hYG, h]

private theorem card_groundLiftSet (G : Finset α) (X : Finset (Fin G.card)) :
    (groundLiftSet G X).card = X.card := by
  exact Finset.card_map _

private theorem card_groundIndexSet_of_subset (G : Finset α) (X : Finset α)
    (hXG : X ⊆ G) :
    (groundIndexSet G X).card = X.card := by
  rw [← card_groundLiftSet G (groundIndexSet G X),
    groundLiftSet_groundIndexSet_of_subset G X hXG]

private theorem groundIndexSet_symmDiff (G : Finset α) {X Y : Finset α}
    (hXG : X ⊆ G) (hYG : Y ⊆ G) :
    groundIndexSet G (X ∆ Y) = groundIndexSet G X ∆ groundIndexSet G Y := by
  ext i
  simp only [mem_groundIndexSet_iff, Finset.mem_symmDiff]

private theorem card_groundIndexSet_symmDiff (G : Finset α) {X Y : Finset α}
    (hXG : X ⊆ G) (hYG : Y ⊆ G) :
    (groundIndexSet G X ∆ groundIndexSet G Y).card = (X ∆ Y).card := by
  rw [← groundIndexSet_symmDiff G hXG hYG]
  apply card_groundIndexSet_of_subset
  intro x hx
  rcases Finset.mem_symmDiff.mp hx with hx | hx
  · exact hXG hx.1
  · exact hYG hx.1

private theorem mem_groundIndexFamily_iff (G : Finset α) {F : Finset (Finset α)}
    (hFG : ∀ X ∈ F, X ⊆ G) (Y : Finset (Fin G.card)) :
    Y ∈ groundIndexFamily G F ↔ groundLiftSet G Y ∈ F := by
  constructor
  · intro hY
    rw [groundIndexFamily] at hY
    obtain ⟨X, hXF, rfl⟩ := Finset.mem_image.mp hY
    rw [groundLiftSet_groundIndexSet_of_subset G X (hFG X hXF)]
    exact hXF
  · intro hYF
    rw [groundIndexFamily]
    exact Finset.mem_image.mpr
      ⟨groundLiftSet G Y, hYF, groundIndexSet_groundLiftSet G Y⟩

private theorem groundIndexSet_mem_groundIndexFamily (G : Finset α)
    {F : Finset (Finset α)} {X : Finset α} (hXF : X ∈ F) :
    groundIndexSet G X ∈ groundIndexFamily G F :=
  Finset.mem_image.mpr ⟨X, hXF, rfl⟩

private theorem isShifted_groundIndexFamily (G : Finset α)
    {F : Finset (Finset α)} {k : ℕ} (hF : IsShifted F k)
    (hFG : ∀ X ∈ F, X ⊆ G) :
    IsShifted (groundIndexFamily G F) k := by
  refine ⟨Finset.image_nonempty.mpr hF.1, ?_, ?_⟩
  · intro Y hY
    obtain ⟨X, hXF, rfl⟩ := Finset.mem_image.mp hY
    rw [card_groundIndexSet_of_subset G X (hFG X hXF)]
    exact hF.2.1 X hXF
  · intro Y hY i j hjY hij hiY
    have hYF : groundLiftSet G Y ∈ F :=
      (mem_groundIndexFamily_iff G hFG Y).mp hY
    have hjLift : G.orderEmbOfFin rfl j ∈ groundLiftSet G Y := by
      simp [groundLiftSet, hjY]
    have hiLift : G.orderEmbOfFin rfl i ∉ groundLiftSet G Y := by
      simpa [groundLiftSet] using hiY
    have hshift := hF.2.2 (groundLiftSet G Y) hYF
      (G.orderEmbOfFin rfl i) (G.orderEmbOfFin rfl j) hjLift
      ((G.orderEmbOfFin rfl).lt_iff_lt.mpr hij) hiLift
    apply (mem_groundIndexFamily_iff G hFG _).mpr
    simpa [groundLiftSet] using hshift

private def groundIndexExchangeEquiv (G : Finset α) (F : Finset (Finset α))
    (hFG : ∀ X ∈ F, X ⊆ G) :
    ExchangeV F ≃ ExchangeV (groundIndexFamily G F) where
  toFun X := ⟨groundIndexSet G X.val, groundIndexSet_mem_groundIndexFamily G X.prop⟩
  invFun Y := ⟨groundLiftSet G Y.val, (mem_groundIndexFamily_iff G hFG Y.val).mp Y.prop⟩
  left_inv X := by
    apply Subtype.ext
    exact groundLiftSet_groundIndexSet_of_subset G X.val (hFG X.val X.prop)
  right_inv Y := by
    apply Subtype.ext
    exact groundIndexSet_groundLiftSet G Y.val

private def exchangeGraph_groundIndexIso (G : Finset α) (F : Finset (Finset α))
    (hFG : ∀ X ∈ F, X ⊆ G) :
    exchangeGraph F ≃g exchangeGraph (groundIndexFamily G F) where
  toEquiv := groundIndexExchangeEquiv G F hFG
  map_rel_iff' := by
    intro X Y
    simp only [exchangeGraph, SimpleGraph.fromRel_adj]
    have hXG := hFG X.val X.prop
    have hYG := hFG Y.val Y.prop
    constructor
    · rintro ⟨hXY, hcard | hcard⟩
      · have hne : X ≠ Y := by
          intro h
          exact hXY (congrArg (groundIndexExchangeEquiv G F hFG) h)
        refine ⟨hne, Or.inl ?_⟩
        simpa [groundIndexExchangeEquiv,
          card_groundIndexSet_symmDiff G hXG hYG] using hcard
      · have hne : X ≠ Y := by
          intro h
          exact hXY (congrArg (groundIndexExchangeEquiv G F hFG) h)
        refine ⟨hne, Or.inr ?_⟩
        simpa [groundIndexExchangeEquiv,
          card_groundIndexSet_symmDiff G hYG hXG] using hcard
    · rintro ⟨hXY, hcard | hcard⟩
      · have hne : (groundIndexExchangeEquiv G F hFG X) ≠
            groundIndexExchangeEquiv G F hFG Y := by
          intro h
          apply hXY
          apply Subtype.ext
          apply groundIndexSet_injective_on_subsets G hXG hYG
          exact congrArg Subtype.val h
        refine ⟨hne, Or.inl ?_⟩
        simpa [groundIndexExchangeEquiv,
          card_groundIndexSet_symmDiff G hXG hYG] using hcard
      · have hne : (groundIndexExchangeEquiv G F hFG X) ≠
            groundIndexExchangeEquiv G F hFG Y := by
          intro h
          apply hXY
          apply Subtype.ext
          apply groundIndexSet_injective_on_subsets G hXG hYG
          exact congrArg Subtype.val h
        refine ⟨hne, Or.inr ?_⟩
        simpa [groundIndexExchangeEquiv,
          card_groundIndexSet_symmDiff G hYG hXG] using hcard

private theorem card_groundIndexFamily (G : Finset α) {F : Finset (Finset α)}
    (hFG : ∀ X ∈ F, X ⊆ G) :
    (groundIndexFamily G F).card = F.card := by
  simpa using (Fintype.card_congr (groundIndexExchangeEquiv G F hFG)).symm

private theorem groundIndexFamily_layerAbove (G : Finset α)
    {F : Finset (Finset α)} (hFG : ∀ X ∈ F, X ⊆ G)
    {e : α} (heG : e ∈ G) :
    groundIndexFamily G (layerAbove F e) =
      layerAbove (groundIndexFamily G F)
        ((G.orderIsoOfFin rfl).symm ⟨e, heG⟩) := by
  let ie : Fin G.card := (G.orderIsoOfFin rfl).symm ⟨e, heG⟩
  have hie : G.orderEmbOfFin rfl ie = e := by
    exact congrArg Subtype.val ((G.orderIsoOfFin rfl).apply_symm_apply ⟨e, heG⟩)
  have hLayer : ∀ X ∈ layerAbove F e, X ⊆ G :=
    fun X hX => hFG X (Finset.mem_filter.mp hX).1
  ext Y
  rw [mem_groundIndexFamily_iff G hLayer Y]
  simp only [layerAbove, Finset.mem_filter]
  rw [mem_groundIndexFamily_iff G hFG Y]
  constructor
  · rintro ⟨hYF, heY⟩
    refine ⟨hYF, ?_⟩
    apply (orderEmb_mem_groundLiftSet_iff G Y ie).mp
    exact hie ▸ heY
  · rintro ⟨hYF, hieY⟩
    refine ⟨hYF, ?_⟩
    have := (orderEmb_mem_groundLiftSet_iff G Y ie).mpr hieY
    exact hie ▸ this

private theorem groundIndexFamily_layerBelow (G : Finset α)
    {F : Finset (Finset α)} (hFG : ∀ X ∈ F, X ⊆ G)
    {e : α} (heG : e ∈ G) :
    groundIndexFamily G (layerBelow F e) =
      layerBelow (groundIndexFamily G F)
        ((G.orderIsoOfFin rfl).symm ⟨e, heG⟩) := by
  let ie : Fin G.card := (G.orderIsoOfFin rfl).symm ⟨e, heG⟩
  have hie : G.orderEmbOfFin rfl ie = e := by
    exact congrArg Subtype.val ((G.orderIsoOfFin rfl).apply_symm_apply ⟨e, heG⟩)
  have hLayer : ∀ X ∈ layerBelow F e, X ⊆ G :=
    fun X hX => hFG X (Finset.mem_filter.mp hX).1
  ext Y
  rw [mem_groundIndexFamily_iff G hLayer Y]
  simp only [layerBelow, Finset.mem_filter]
  rw [mem_groundIndexFamily_iff G hFG Y]
  constructor
  · rintro ⟨hYF, heY⟩
    refine ⟨hYF, ?_⟩
    intro hieY
    apply heY
    have hmem := (orderEmb_mem_groundLiftSet_iff G Y ie).mpr hieY
    exact hie ▸ hmem
  · rintro ⟨hYF, hieY⟩
    refine ⟨hYF, ?_⟩
    intro heY
    apply hieY
    apply (orderEmb_mem_groundLiftSet_iff G Y ie).mp
    exact hie ▸ heY

private theorem usedGround_groundIndexFamily_usedGround
    (F : Finset (Finset α)) :
    usedGround (groundIndexFamily (usedGround F) F) = Finset.univ := by
  let G := usedGround F
  ext i
  simp only [Finset.mem_univ, iff_true]
  change i ∈ (groundIndexFamily G F).biUnion id
  rw [Finset.mem_biUnion]
  have hiG : G.orderEmbOfFin rfl i ∈ G := Finset.orderEmbOfFin_mem G rfl i
  change G.orderEmbOfFin rfl i ∈ usedGround F at hiG
  rw [usedGround, Finset.mem_biUnion] at hiG
  obtain ⟨X, hXF, hiX⟩ := hiG
  exact ⟨groundIndexSet G X, groundIndexSet_mem_groundIndexFamily G hXF,
    (mem_groundIndexSet_iff G X i).mpr hiX⟩

private theorem mem_crossingBarred_groundIndex_of_mem
    (G : Finset α) {L : Finset (Finset α)}
    (hLG : ∀ X ∈ L, X ⊆ G) {A X : Finset α}
    (hAG : A ⊆ G) (hXG : X ⊆ G)
    (hXbar : X ∈ crossingBarred L A) :
    groundIndexSet G X ∈
      crossingBarred (groundIndexFamily G L) (groundIndexSet G A) := by
  rcases mem_crossingBarred_iff.mp hXbar with ⟨hXL, hXA | hbad⟩
  · apply mem_crossingBarred_iff.mpr
    exact ⟨groundIndexSet_mem_groundIndexFamily G hXL,
      Or.inl (congrArg (groundIndexSet G) hXA)⟩
  · obtain ⟨hAL, hXL', hbad⟩ := hbad
    have hbad' := isCliqueSum_map_iso (exchangeGraph_groundIndexIso G L hLG) hbad
    apply mem_crossingBarred_iff.mpr
    refine ⟨groundIndexSet_mem_groundIndexFamily G hXL, Or.inr
      ⟨groundIndexSet_mem_groundIndexFamily G hAL,
        groundIndexSet_mem_groundIndexFamily G hXL', ?_⟩⟩
    change (exchangeGraph (groundIndexFamily G L)).IsCliqueSum
      ⟨groundIndexSet G A, _⟩ ⟨groundIndexSet G X, _⟩
    convert hbad' using 1 <;> apply Subtype.ext <;> rfl

/-- Relabelling a failed step by the increasing enumeration of a finite containing ground preserves
failure.  The contrapositive transports a crossing back to the original ambient order. -/
private theorem crossingFailure_groundIndex
    (G : Finset α) {F : Finset (Finset α)}
    (hFG : ∀ X ∈ F, X ⊆ G) {A B : Finset α} {e : α}
    (hAG : A ⊆ G) (hBG : B ⊆ G) (heG : e ∈ G)
    (hfail : crossingFailure F A B e) :
    crossingFailure (groundIndexFamily G F) (groundIndexSet G A) (groundIndexSet G B)
      ((G.orderIsoOfFin rfl).symm ⟨e, heG⟩) := by
  let ie : Fin G.card := (G.orderIsoOfFin rfl).symm ⟨e, heG⟩
  have hie : G.orderEmbOfFin rfl ie = e := by
    exact congrArg Subtype.val ((G.orderIsoOfFin rfl).apply_symm_apply ⟨e, heG⟩)
  have hAboveSub : ∀ X ∈ layerAbove F e, X ⊆ G :=
    fun X hX => hFG X (Finset.mem_filter.mp hX).1
  have hBelowSub : ∀ X ∈ layerBelow F e, X ⊆ G :=
    fun X hX => hFG X (Finset.mem_filter.mp hX).1
  have hAboveEq := groundIndexFamily_layerAbove G hFG heG
  have hBelowEq := groundIndexFamily_layerBelow G hFG heG
  intro hcross
  apply hfail
  rcases hcross with ⟨Wi, Xi, ξi, hWi, hXi, hξie, hξiW, hXiform,
    hWiAllowed, hXiAllowed⟩
  let W := groundLiftSet G Wi
  let X := groundLiftSet G Xi
  let ξ := G.orderEmbOfFin rfl ξi
  have hWF : W ∈ F := by
    apply (mem_groundIndexFamily_iff G hFG Wi).mp
    exact (Finset.mem_filter.mp hWi).1
  have heW : e ∈ W := by
    change e ∈ groundLiftSet G Wi
    have hiWi : ie ∈ Wi := (Finset.mem_filter.mp hWi).2
    exact hie ▸ (orderEmb_mem_groundLiftSet_iff G Wi ie).mpr hiWi
  have hWabove : W ∈ layerAbove F e := Finset.mem_filter.mpr ⟨hWF, heW⟩
  have hXF : X ∈ F := by
    apply (mem_groundIndexFamily_iff G hFG Xi).mp
    exact (Finset.mem_filter.mp hXi).1
  have heX : e ∉ X := by
    change e ∉ groundLiftSet G Xi
    intro heXi
    have hiXi : ie ∈ Xi := (orderEmb_mem_groundLiftSet_iff G Xi ie).mp (hie ▸ heXi)
    exact (Finset.mem_filter.mp hXi).2 hiXi
  have hXbelow : X ∈ layerBelow F e := Finset.mem_filter.mpr ⟨hXF, heX⟩
  have hξe : ξ ≠ e := by
    intro h
    apply hξie
    apply (G.orderEmbOfFin rfl).injective
    exact h.trans hie.symm
  have hξW : ξ ∉ W := by
    change G.orderEmbOfFin rfl ξi ∉ groundLiftSet G Wi
    simpa [groundLiftSet] using hξiW
  have hform : X = insert ξ (W.erase e) := by
    change groundLiftSet G Xi =
      insert (G.orderEmbOfFin rfl ξi) ((groundLiftSet G Wi).erase e)
    rw [hXiform]
    simp only [groundLiftSet, Finset.map_insert, Finset.map_erase]
    have hie' : (G.orderEmbOfFin rfl).toEmbedding
        ((G.orderIsoOfFin rfl).symm ⟨e, heG⟩) = e := by
      simpa [ie] using hie
    rw [hie']
    rfl
  have hWAllowed : (layerAbove F e).card = 1 ∨
      W ∉ crossingBarred (layerAbove F e) A := by
    rcases hWiAllowed with hcard | hnot
    · left
      rw [← card_groundIndexFamily G hAboveSub, hAboveEq]
      exact hcard
    · right
      intro hbar
      have hbarI := mem_crossingBarred_groundIndex_of_mem G hAboveSub hAG
        (hFG W hWF) hbar
      rw [hAboveEq] at hbarI
      apply hnot
      simpa [W] using hbarI
  have hXAllowed : (layerBelow F e).card = 1 ∨
      X ∉ crossingBarred (layerBelow F e) B := by
    rcases hXiAllowed with hcard | hnot
    · left
      rw [← card_groundIndexFamily G hBelowSub, hBelowEq]
      exact hcard
    · right
      intro hbar
      have hbarI := mem_crossingBarred_groundIndex_of_mem G hBelowSub hBG
        (hFG X hXF) hbar
      rw [hBelowEq] at hbarI
      apply hnot
      simpa [X] using hbarI
  exact ⟨W, X, ξ, hWabove, hXbelow, hξe, hξW, hform, hWAllowed, hXAllowed⟩

/-! ### 8.6 The two upper regimes by `dualSet` -/

/-- Failure is carried to failure after complement-and-reverse, with the oriented endpoints
swapped.  This is the reusable transport already exercised by Case 3, now factored for the two
remaining positional regimes. -/
private theorem crossingFailure_dual
    {n : ℕ} {F : Finset (Finset (Fin n))} {A B : Finset (Fin n)} {e : Fin n}
    (hfail : crossingFailure F A B e) :
    crossingFailure (dualFamily F) (dualSet B) (dualSet A) (dualElem e) := by
  intro hcross
  apply hfail
  rcases hcross with ⟨Wd, Xd, ξd, hWd, hXd, hξde, hξdW, hXdform,
    hWdAllowed, hXdAllowed⟩
  let W := dualSet Xd
  let X := dualSet Wd
  let ξ := dualElem ξd
  have hWF : W ∈ F := by
    change dualSet Xd ∈ F
    exact mem_dualFamily.mp (Finset.mem_filter.mp hXd).1
  have heW : e ∈ W := by
    change e ∈ dualSet Xd
    simpa using (Finset.mem_filter.mp hXd).2
  have hWabove : W ∈ layerAbove F e := Finset.mem_filter.mpr ⟨hWF, heW⟩
  have hXF : X ∈ F := by
    change dualSet Wd ∈ F
    exact mem_dualFamily.mp (Finset.mem_filter.mp hWd).1
  have heX : e ∉ X := by
    change e ∉ dualSet Wd
    simpa using (Finset.mem_filter.mp hWd).2
  have hXbelow : X ∈ layerBelow F e := Finset.mem_filter.mpr ⟨hXF, heX⟩
  have hξe : ξ ≠ e := by
    intro h
    apply hξde
    have := congrArg dualElem h
    simpa [ξ] using this
  have hξXd : ξd ∈ Xd := hXdform ▸ Finset.mem_insert_self _ _
  have hedWd : dualElem e ∈ Wd := (Finset.mem_filter.mp hWd).2
  have hξW : ξ ∉ W := by
    intro h
    have hnot := mem_dualSet.mp h
    apply hnot
    simpa [ξ] using hξXd
  have hform : X = insert ξ (W.erase e) := by
    change dualSet Wd = insert (dualElem ξd) ((dualSet Xd).erase e)
    ext z
    simp only [mem_dualSet, Finset.mem_insert, Finset.mem_erase]
    rw [hXdform]
    simp only [Finset.mem_insert, Finset.mem_erase]
    by_cases hzξ : z = dualElem ξd
    · subst z
      simp [hξdW]
    by_cases hze : z = e
    · subst z
      have heWd : dualElem e ∈ Wd := hedWd
      simp [heWd, hzξ]
    have hdzξ : dualElem z ≠ ξd := by
      intro h
      apply hzξ
      have := congrArg dualElem h
      simpa using this
    have hdze : dualElem z ≠ dualElem e := by
      intro h
      exact hze (dualElem_injective h)
    simp [hzξ, hze, hdzξ, hdze]
  have hDualLower : dualFamily (layerBelow F e) =
      layerAbove (dualFamily F) (dualElem e) := by
    simpa [dualFamily] using image_layerBelow_dualSet F e
  have hDualAbove : dualFamily (layerAbove F e) =
      layerBelow (dualFamily F) (dualElem e) := by
    simpa [dualFamily] using image_layerAbove_dualSet F e
  have hXAllowed : (layerBelow F e).card = 1 ∨
      X ∉ crossingBarred (layerBelow F e) B := by
    rcases hWdAllowed with hcard | hnot
    · left
      have himage := image_layerBelow_dualSet F e
      have hinj : Function.Injective (@dualSet n) := by
        intro P Q hPQ
        have := congrArg dualSet hPQ
        simpa using this
      rw [← himage, Finset.card_image_of_injective _ hinj] at hcard
      exact hcard
    · right
      intro hbar
      have hdbar := (mem_crossingBarred_dual_iff (L := layerBelow F e)
        (A := B) (X := X)).mp hbar
      rw [hDualLower] at hdbar
      apply hnot
      simpa [X] using hdbar
  have hWAllowed : (layerAbove F e).card = 1 ∨
      W ∉ crossingBarred (layerAbove F e) A := by
    rcases hXdAllowed with hcard | hnot
    · left
      have himage := image_layerAbove_dualSet F e
      have hinj : Function.Injective (@dualSet n) := by
        intro P Q hPQ
        have := congrArg dualSet hPQ
        simpa using this
      rw [← himage, Finset.card_image_of_injective _ hinj] at hcard
      exact hcard
    · right
      intro hbar
      have hdbar := (mem_crossingBarred_dual_iff (L := layerAbove F e)
        (A := A) (X := W)).mp hbar
      rw [hDualAbove] at hdbar
      apply hnot
      simpa [W] using hdbar
  exact ⟨W, X, ξ, hWabove, hXbelow, hξe, hξW, hform, hWAllowed, hXAllowed⟩

/-- Every point strictly below `e*` is still used after dualizing: its primal mate is strictly
above `e`, and shifting `e` into `B` supplies a member omitting that mate when necessary. -/
private theorem groundRank_dualFamily_dualElem
    {n k : ℕ} {F : Finset (Finset (Fin n))} (hF : IsShifted F k)
    {B : Finset (Fin n)} (hBF : B ∈ F) {e : Fin n} (heB : e ∉ B) :
    groundRank (usedGround (dualFamily F)) (dualElem e) = (dualElem e).val := by
  have hfilter : (usedGround (dualFamily F)).filter (fun z => z < dualElem e) =
      Finset.univ.filter (fun z : Fin n => z < dualElem e) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun hz => hz.2
    · intro hz
      refine ⟨?_, hz⟩
      let y := dualElem z
      have hey : e < y := by
        change e < dualElem z
        exact Fin.lt_rev_iff.mp hz
      by_cases hyB : y ∈ B
      · let X := insert e (B.erase y)
        have hXF : X ∈ F := hF.2.2 B hBF e y hyB hey heB
        have hyX : y ∉ X := by simp [X, hey.ne', hyB]
        rw [usedGround, Finset.mem_biUnion]
        refine ⟨dualSet X, Finset.mem_image.mpr ⟨X, hXF, rfl⟩, ?_⟩
        exact mem_dualSet.mpr (by simpa [y] using hyX)
      · rw [usedGround, Finset.mem_biUnion]
        refine ⟨dualSet B, Finset.mem_image.mpr ⟨B, hBF, rfl⟩, ?_⟩
        exact mem_dualSet.mpr (by simpa [y] using hyB)
  rw [groundRank, hfilter]
  have hu : Finset.univ.filter (fun z : Fin n => z < dualElem e) =
      Finset.Iio (dualElem e) := by
    ext z
    simp
  rw [hu, Fin.card_Iio]

/-- The regimes `e = k+1` and `e = k+2`, transported respectively to `e* = k*` and
`e* = k*-1`.  There is no second hand proof of either regime. -/
private theorem not_crossingFailure_of_upper_regimes_dual
    {n k : ℕ} {F : Finset (Finset (Fin n))} (hF : IsShifted F k)
    (hground : usedGround F = Finset.univ)
    {A B : ExchangeV F} {e : Fin n}
    (heA : e ∈ A.val) (heB : e ∉ B.val)
    (hAbove : 2 ≤ (layerAbove F e).card)
    (hBelow : 2 ≤ (layerBelow F e).card)
    (hpos : groundRank (usedGround F) e + 1 = k + 1 ∨
      groundRank (usedGround F) e + 1 = k + 2)
    (hnotexc : ¬ IsCliqueSum F A B) :
    ¬ crossingFailure F A.val B.val e := by
  let Fd := dualFamily F
  let ed := dualElem e
  let Ad : ExchangeV Fd := dualExchangeEquiv F B
  let Bd : ExchangeV Fd := dualExchangeEquiv F A
  have hdualInj : Function.Injective (@dualSet n) := by
    intro X Y hXY
    have := congrArg dualSet hXY
    simpa using this
  have hAboveCard : (layerAbove Fd ed).card = (layerBelow F e).card := by
    have himage := image_layerBelow_dualSet F e
    change (layerBelow F e).image dualSet = layerAbove Fd ed at himage
    rw [← himage, Finset.card_image_of_injective _ hdualInj]
  have hBelowCard : (layerBelow Fd ed).card = (layerAbove F e).card := by
    have himage := image_layerAbove_dualSet F e
    change (layerAbove F e).image dualSet = layerBelow Fd ed at himage
    rw [← himage, Finset.card_image_of_injective _ hdualInj]
  have hAdMem : ed ∈ Ad.val := by
    change dualElem e ∈ dualSet B.val
    simpa using heB
  have hBdNotMem : ed ∉ Bd.val := by
    change dualElem e ∉ dualSet A.val
    simpa using heA
  have hAdAbove : Ad.val ∈ layerAbove Fd ed :=
    Finset.mem_filter.mpr ⟨Ad.prop, hAdMem⟩
  have hBdBelow : Bd.val ∈ layerBelow Fd ed :=
    Finset.mem_filter.mpr ⟨Bd.prop, hBdNotMem⟩
  have hFd : IsShifted Fd (n - k) := isShifted_dualFamily hF
  have hnotDual : ¬ IsCliqueSum Fd Ad Bd := by
    intro hbad
    have hbadBA : IsCliqueSum F B A := by
      apply (isCliqueSum_dual_iff B A).mpr
      simpa [Ad, Bd, dualExchangeEquiv] using hbad
    exact hnotexc (isCliqueSum_swap hbadBA)
  have hk : k ≤ n := by
    have hAle := Finset.card_le_univ A.val
    rw [hF.2.1 A.val A.prop] at hAle
    simpa using hAle
  have heRank : groundRank (usedGround F) e = e.val := by
    rw [hground]
    exact groundRank_univ_fin e
  have hdRank : groundRank (usedGround Fd) ed = ed.val := by
    exact groundRank_dualFamily_dualElem hF B.prop heB
  intro hfail
  have hfaild : crossingFailure Fd Ad.val Bd.val ed := by
    simpa [Fd, Ad, Bd, ed, dualExchangeEquiv] using crossingFailure_dual hfail
  rcases hpos with hpos | hpos
  · have hdpos : groundRank (usedGround Fd) ed + 1 = n - k := by
      rw [hdRank, dualElem_val]
      omega
    exact not_crossingFailure_at_k hFd hAdMem hBdNotMem
      (hAboveCard ▸ hBelow) (hBelowCard ▸ hAbove) hdpos hnotDual hfaild
  · have hdpos : groundRank (usedGround Fd) ed + 1 = (n - k) - 1 := by
      rw [hdRank, dualElem_val]
      omega
    exact not_crossingFailure_of_rank_succ_eq_pred hFd hAdAbove hBdBelow
      (hAboveCard ▸ hBelow) (hBelowCard ▸ hAbove) hdpos hfaild

/-! ### 8.7 Exhaustion and assembly -/

private theorem not_crossingFailure_fin
    {n k : ℕ} {F : Finset (Finset (Fin n))} (hF : IsShifted F k)
    (hground : usedGround F = Finset.univ)
    {A B : ExchangeV F} (hAB : A ≠ B) (hnotexc : ¬ IsCliqueSum F A B)
    {e : Fin n} (heA : e ∈ A.val) (heB : e ∉ B.val) :
    ¬ crossingFailure F A.val B.val e := by
  have hA : A.val ∈ layerAbove F e := Finset.mem_filter.mpr ⟨A.prop, heA⟩
  have hB : B.val ∈ layerBelow F e := Finset.mem_filter.mpr ⟨B.prop, heB⟩
  have hAbovePos : 0 < (layerAbove F e).card := Finset.card_pos.mpr ⟨A.val, hA⟩
  have hBelowPos : 0 < (layerBelow F e).card := Finset.card_pos.mpr ⟨B.val, hB⟩
  have hAboveCases : (layerAbove F e).card = 1 ∨
      2 ≤ (layerAbove F e).card := by omega
  have hBelowCases : (layerBelow F e).card = 1 ∨
      2 ≤ (layerBelow F e).card := by omega
  rcases hAboveCases with hAboveOne | hAboveTwo
  · rcases hBelowCases with hBelowOne | hBelowTwo
    · exact not_crossingFailure_of_layer_cards_one hF hAB heA heB hAboveOne hBelowOne
    · exact not_crossingFailure_of_upper_singleton hF heA heB hAboveOne hBelowTwo
  · rcases hBelowCases with hBelowOne | hBelowTwo
    · exact not_crossingFailure_of_lower_singleton_dual hF heA heB hAboveTwo hBelowOne
    · intro hfail
      obtain ⟨hrangeLow, hrangeHigh⟩ :=
        crossingFailure_range_reduction hF hfail hA hB hAboveTwo hBelowTwo
      have hpositions :
          groundRank (usedGround F) e + 1 = k - 1 ∨
          groundRank (usedGround F) e + 1 = k ∨
          groundRank (usedGround F) e + 1 = k + 1 ∨
          groundRank (usedGround F) e + 1 = k + 2 := by
        omega
      rcases hpositions with hpred | hk | hsucc | hsuccsucc
      · exact not_crossingFailure_of_rank_succ_eq_pred
          hF hA hB hAboveTwo hBelowTwo hpred hfail
      · exact not_crossingFailure_at_k hF heA heB hAboveTwo hBelowTwo hk hnotexc hfail
      · exact not_crossingFailure_of_upper_regimes_dual hF hground heA heB
          hAboveTwo hBelowTwo (Or.inl hsucc) hnotexc hfail
      · exact not_crossingFailure_of_upper_regimes_dual hF hground heA heB
          hAboveTwo hBelowTwo (Or.inr hsuccsucc) hnotexc hfail

private theorem not_crossingFailure_general
    {F : Finset (Finset α)} {k : ℕ} (hF : IsShifted F k)
    {A B : ExchangeV F} (hAB : A ≠ B) (hnotexc : ¬ IsCliqueSum F A B)
    {e : α} (heA : e ∈ A.val) (heB : e ∉ B.val) :
    ¬ crossingFailure F A.val B.val e := by
  let G := usedGround F
  have hFG : ∀ X ∈ F, X ⊆ G := fun X hX => mem_usedGround_of_mem_family hX
  have hAG : A.val ⊆ G := hFG A.val A.prop
  have hBG : B.val ⊆ G := hFG B.val B.prop
  have heG : e ∈ G := hAG heA
  let Fi := groundIndexFamily G F
  let Ai : ExchangeV Fi := groundIndexExchangeEquiv G F hFG A
  let Bi : ExchangeV Fi := groundIndexExchangeEquiv G F hFG B
  let ie : Fin G.card := (G.orderIsoOfFin rfl).symm ⟨e, heG⟩
  have hFi : IsShifted Fi k := isShifted_groundIndexFamily G hF hFG
  have hground : usedGround Fi = Finset.univ := by
    simpa [Fi, G] using usedGround_groundIndexFamily_usedGround F
  have hAiBi : Ai ≠ Bi := by
    intro h
    exact hAB ((groundIndexExchangeEquiv G F hFG).injective h)
  have hnoti : ¬ IsCliqueSum Fi Ai Bi := by
    intro hbad
    apply hnotexc
    exact (isCliqueSum_iso_iff (exchangeGraph_groundIndexIso G F hFG)).mpr hbad
  have hie : G.orderEmbOfFin rfl ie = e := by
    exact congrArg Subtype.val ((G.orderIsoOfFin rfl).apply_symm_apply ⟨e, heG⟩)
  have hieAi : ie ∈ Ai.val := by
    change ie ∈ groundIndexSet G A.val
    rw [mem_groundIndexSet_iff]
    exact hie ▸ heA
  have hieBi : ie ∉ Bi.val := by
    change ie ∉ groundIndexSet G B.val
    rw [mem_groundIndexSet_iff]
    exact hie ▸ heB
  have hNoIndexed : ¬ crossingFailure Fi Ai.val Bi.val ie :=
    not_crossingFailure_fin hFi hground hAiBi hnoti hieAi hieBi
  intro hfail
  apply hNoIndexed
  simpa [Fi, Ai, Bi, ie, groundIndexExchangeEquiv] using
    crossingFailure_groundIndex G hFG hAG hBG heG hfail

/-- **crossing lemma**, `STEP_LEMMA_2026-08-15.md` §0. -/
theorem crossingLemma {F : Finset (Finset α)} {κ : ℕ} (hF : IsShifted F κ)
    {A B : ExchangeV F} (hAB : A ≠ B) (hnotexc : ¬ IsCliqueSum F A B)
    (e : α) (heA : e ∈ A.val) (heB : e ∉ B.val) :
    ∃ Y X : Finset α, ∃ ξ : α,
      Y ∈ layerAbove F e ∧ X ∈ layerBelow F e ∧
      ξ ≠ e ∧ ξ ∉ Y ∧ X = insert ξ (Y.erase e) ∧
      ((layerAbove F e).card = 1 ∨
        (Y ≠ A.val ∧ ∀ (hA : A.val ∈ layerAbove F e) (hY : Y ∈ layerAbove F e),
          ¬ IsCliqueSum (layerAbove F e) ⟨A.val, hA⟩ ⟨Y, hY⟩)) ∧
      ((layerBelow F e).card = 1 ∨
        (X ≠ B.val ∧ ∀ (hB : B.val ∈ layerBelow F e) (hX : X ∈ layerBelow F e),
          ¬ IsCliqueSum (layerBelow F e) ⟨B.val, hB⟩ ⟨X, hX⟩)) := by
  have hNoFailure := not_crossingFailure_general hF hAB hnotexc heA heB
  have hcross := Classical.not_not.mp hNoFailure
  rcases hcross with ⟨Y, X, ξ, hY, hX, hξe, hξY, hform, hYallow, hXallow⟩
  refine ⟨Y, X, ξ, hY, hX, hξe, hξY, hform, ?_, ?_⟩
  · rcases hYallow with hcard | hYout
    · exact Or.inl hcard
    · right
      refine ⟨?_, ?_⟩
      · intro hYA
        apply hYout
        exact mem_crossingBarred_iff.mpr ⟨hY, Or.inl hYA⟩
      · intro hA' hY' hbad
        apply hYout
        exact mem_crossingBarred_iff.mpr ⟨hY, Or.inr ⟨hA', hY', hbad⟩⟩
  · rcases hXallow with hcard | hXout
    · exact Or.inl hcard
    · right
      refine ⟨?_, ?_⟩
      · intro hXB
        apply hXout
        exact mem_crossingBarred_iff.mpr ⟨hX, Or.inl hXB⟩
      · intro hB' hX' hbad
        apply hXout
        exact mem_crossingBarred_iff.mpr ⟨hX, Or.inr ⟨hB', hX', hbad⟩⟩

/-- The existence half of `(Q*)` -- that a Hamilton path DOES exist off the exception --
universally quantified over the ground type so strong induction
can recurse from `α` to the punctured subtype `{x // x ≠ e}`. -/
private theorem qstarPositiveAux (n : ℕ) :
    ∀ (β : Type u) [LinearOrder β] [DecidableEq β]
      {F : Finset (Finset β)} {κ : ℕ},
      IsShifted F κ → ∀ A B : ExchangeV F, A ≠ B →
      ¬ IsCliqueSum F A B → (familyGround F).card = n →
      HasHamPath (exchangeGraph F) A B := by
  induction n using Nat.strong_induction_on
  rename_i n ih
  intro β _ _ F κ hF A B hAB hnot hmeasure
  classical
  have h2 : 2 ≤ F.card := by
    have hsub : {A.val, B.val} ⊆ F := by
      intro X hX
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl
      · exact A.prop
      · exact B.prop
    have hle := Finset.card_le_card hsub
    have hvalne : A.val ≠ B.val := fun h => hAB (Subtype.ext h)
    simpa [Finset.card_pair hvalne] using hle
  by_cases hsmall : F.card ≤ 3
  · exact hasHamPath_of_complete
      (exchangeGraph_complete_of_card_le_three hF h2 hsmall) A B hAB
  by_cases hrank : κ ≤ 1
  · exact hasHamPath_of_complete
      (exchangeGraph_complete_of_rank_le_one hF hrank) A B hAB
  have hcardAB : A.val.card = B.val.card :=
    (hF.2.1 A.val A.prop).trans (hF.2.1 B.val B.prop).symm
  have hdiff : (A.val \ B.val).Nonempty := Finset.sdiff_nonempty.mpr (by
    intro hsub
    apply hAB
    apply Subtype.ext
    exact Finset.eq_of_subset_of_card_le hsub hcardAB.ge)
  obtain ⟨e, he⟩ := hdiff
  have heA : e ∈ A.val := (Finset.mem_sdiff.mp he).1
  have heB : e ∉ B.val := (Finset.mem_sdiff.mp he).2
  obtain ⟨Y, X, ξ, hYabove, hXbelow, hξe, hξY, hXeq, hupper, hlower⟩ :=
    crossingLemma hF hAB hnot e heA heB
  have hAabove : A.val ∈ layerAbove F e := Finset.mem_filter.mpr ⟨A.prop, heA⟩
  have hBbelow : B.val ∈ layerBelow F e := Finset.mem_filter.mpr ⟨B.prop, heB⟩
  let A₁ : ExchangeV (layerAbove F e) := ⟨A.val, hAabove⟩
  let Y₁ : ExchangeV (layerAbove F e) := ⟨Y, hYabove⟩
  let X₀ : ExchangeV (layerBelow F e) := ⟨X, hXbelow⟩
  let B₀ : ExchangeV (layerBelow F e) := ⟨B.val, hBbelow⟩
  have heGround : e ∈ familyGround F := by
    rw [familyGround, Finset.mem_biUnion]
    exact ⟨A.val, A.prop, heA⟩
  have hpathUpper : HasHamPath (exchangeGraph (layerAbove F e)) A₁ Y₁ := by
    rcases hupper with hsingle | hdodge
    · exact hasHamPath_of_family_card_one hsingle A₁ Y₁
    · have hne : A₁ ≠ Y₁ := by
        intro h
        exact hdodge.1 (congrArg Subtype.val h).symm
      let φ := exchangeGraph_puncturedLinkIso F e
      have hnotLayer : ¬ IsCliqueSum (layerAbove F e) A₁ Y₁ :=
        hdodge.2 hAabove hYabove
      have hnotPunctured :
          ¬ IsCliqueSum (puncturedLink F e) (φ A₁) (φ Y₁) := by
        intro hbad
        exact hnotLayer ((isCliqueSum_iso_iff φ).mpr hbad)
      have hshifted := isShifted_puncturedLink hF ⟨A.val, hAabove⟩
      have hlt : (familyGround (puncturedLink F e)).card < n := by
        rw [← hmeasure]
        exact puncturedLink_familyGround_lt heGround
      have hp := ih _ hlt (Punctured e) hshifted (φ A₁) (φ Y₁)
        (fun h => hne (φ.injective h)) hnotPunctured rfl
      exact (hasHamPath_iso_iff φ A₁ Y₁).mpr hp
  have hpathLower : HasHamPath (exchangeGraph (layerBelow F e)) X₀ B₀ := by
    rcases hlower with hsingle | hdodge
    · exact hasHamPath_of_family_card_one hsingle X₀ B₀
    · have hne : X₀ ≠ B₀ := by
        intro h
        exact hdodge.1 (congrArg Subtype.val h)
      let φ := exchangeGraph_puncturedLowerIso F e
      have hnotLayer : ¬ IsCliqueSum (layerBelow F e) X₀ B₀ := by
        intro hbad
        exact hdodge.2 hBbelow hXbelow (isCliqueSum_swap hbad)
      have hnotPunctured :
          ¬ IsCliqueSum (puncturedLower F e) (φ X₀) (φ B₀) := by
        intro hbad
        exact hnotLayer ((isCliqueSum_iso_iff φ).mpr hbad)
      have hshifted := isShifted_puncturedLower hF ⟨B.val, hBbelow⟩
      have hlt : (familyGround (puncturedLower F e)).card < n := by
        rw [← hmeasure]
        exact puncturedLower_familyGround_lt heGround
      have hp := ih _ hlt (Punctured e) hshifted (φ X₀) (φ B₀)
        (fun h => hne (φ.injective h)) hnotPunctured rfl
      exact (hasHamPath_iso_iff φ X₀ B₀).mpr hp
  have hcross :
      (exchangeGraph F).Adj (layerAboveHom F e Y₁) (layerBelowHom F e X₀) := by
    exact exchangeGraph_adj_of_replacement
      (Finset.mem_filter.mp hYabove).1 (Finset.mem_filter.mp hXbelow).1
      (Finset.mem_filter.mp hYabove).2 hξY hξe hXeq
  simpa [A₁, B₀, layerAboveHom, layerBelowHom] using
    hamPath_of_layer_splice A₁ Y₁ X₀ B₀ hpathUpper hpathLower hcross

private theorem qstarPositive {F : Finset (Finset α)} {κ : ℕ}
    (hF : IsShifted F κ) (A B : ExchangeV F) (hAB : A ≠ B)
    (hnot : ¬ IsCliqueSum F A B) :
    HasHamPath (exchangeGraph F) A B := by
  exact qstarPositiveAux (familyGround F).card α hF A B hAB hnot rfl

/-- **`(Q*)`**, `QSTAR_DESIGN_2026-08-15.md` §1.

For every shifted family `F` and all `A ≠ B ∈ F`, `J(F)` has a Hamilton `A`–`B` path **except**
exactly when `F` is a clique-sum and `{A, B}` is its universal pair.

Status in the prose: proven at lead + decoupled-adversary + computation level, relative to a named
trust surface; NOT referee-final. Its chain cites no external theorem. -/
theorem qstar {F : Finset (Finset α)} {κ : ℕ} (hF : IsShifted F κ) (A B : ExchangeV F)
    (hAB : A ≠ B) :
    HasHamPath (exchangeGraph F) A B ↔ ¬ IsCliqueSum F A B := by
  constructor
  · intro hpath hbad
    exact no_hamPath_of_cliqueSum hbad hpath
  · exact qstarPositive hF A B hAB

/-- **The other pairs of a clique-sum**, recorded after Corollary 7.8 in the manuscript rather than
as part of Lemma 7.4: at a clique-sum every pair OTHER than the universal pair does have a Hamilton
path between it.  Derived from `qstar`, which is how the manuscript presents it -- Lemma 7.4 there is
the obstruction alone. -/
theorem hamPath_of_cliqueSum_of_other_pair {F : Finset (Finset α)} {κ : ℕ}
    (hF : IsShifted F κ) {u v A B : ExchangeV F} (hbad : IsCliqueSum F u v)
    (hAB : A ≠ B) (hother : ({A, B} : Finset (ExchangeV F)) ≠ {u, v}) :
    HasHamPath (exchangeGraph F) A B := by
  apply (qstar hF A B hAB).2
  intro hbadAB
  apply hother
  have hA := cliqueSum_universal_eq_endpoint hbad hbadAB.2.1
  have hB := cliqueSum_universal_eq_endpoint hbad hbadAB.2.2.1
  rcases hA with hAu | hAv <;> rcases hB with hBu | hBv
  · exact (hAB (hAu.trans hBu.symm)).elim
  · simpa [hAu, hBv]
  · simpa [hAv, hBu, Finset.pair_comm]
  · exact (hAB (hAv.trans hBv.symm)).elim

/-- **Corollary 7.8.** If a shifted family is not a yFamily, its exchange graph is
Hamilton-connected. -/
theorem not_yFamily_isHamConnected {F : Finset (Finset α)} {κ : ℕ} (hF : IsShifted F κ)
    (hnotYFamily : ¬ ∃ r s : α,
      r ∈ usedGround F ∧ r ∉ initialSegment (usedGround F) (κ + 1) ∧
      s ∈ initialSegment (usedGround F) (κ - 1) ∧
      F = yFamily (usedGround F) κ r s) :
    IsHamConnected (exchangeGraph F) := by
  intro A B hAB
  apply (qstar hF A B hAB).2
  intro hbad
  exact hnotYFamily (lemma3_arms_are_contiguous hF hbad)

/-- **Corollary 7.9, first clause.** A clique-sum has two Gale-incomparable Gale-maximal
members, one in each of its two coordinate yFamily arms. -/
theorem cliqueSum_exists_incomparable_galeMaximal
    {F : Finset (Finset α)} {κ : ℕ} (hF : IsShifted F κ)
    {u v : ExchangeV F} (hbad : IsCliqueSum F u v) :
    ∃ (r s : α) (X Y : Finset α),
      r ∈ usedGround F ∧
      r ∉ initialSegment (usedGround F) (κ + 1) ∧
      s ∈ initialSegment (usedGround F) (κ - 1) ∧
      F = yFamily (usedGround F) κ r s ∧
      X ∈ yOuterArm (usedGround F) κ r ∧
      X ∈ F ∧ (∀ Z ∈ F, GaleLE X Z → Z = X) ∧
      Y ∈ yInnerArm (usedGround F) κ s ∧
      Y ∈ F ∧ (∀ Z ∈ F, GaleLE Y Z → Z = Y) ∧
      ¬ GaleLE X Y ∧ ¬ GaleLE Y X := by
  classical
  obtain ⟨r, s, hrG, hrOut, hsC, hclass⟩ := lemma3_arms_are_contiguous hF hbad
  let G := usedGround F
  let I := initialSegment G κ
  let M₂ := secondInitialSegment G κ
  let C := initialSegment G (κ - 1)
  let U := initialSegment G (κ + 1)
  let P := yOuterArm G κ r
  let Q := yInnerArm G κ s
  change r ∈ G at hrG
  change r ∉ U at hrOut
  change s ∈ C at hsC
  change F = yFamily G κ r s at hclass
  obtain ⟨X, hXF, hXcolex⟩ := Finset.exists_max_image F toColex hF.1
  have hXmax : ∀ Z ∈ F, GaleLE X Z → Z = X := by
    intro Z hZF hXZ
    apply toColex.injective
    exact le_antisymm (hXcolex Z hZF) (toColex_le_of_galeLE hXZ)
  have hnotGreatest : ¬ ∀ Z ∈ F, GaleLE Z X := by
    intro hgreatest
    have hprincipal : ∀ Z, Z ∈ F ↔ (Z.card = κ ∧ GaleLE Z X) := by
      intro Z
      constructor
      · intro hZF
        exact ⟨hF.2.1 Z hZF, hgreatest Z hZF⟩
      · rintro ⟨hZcard, hZX⟩
        exact (isShifted_iff_isGaleIdeal F κ).mp hF |>.2.2 X hXF Z hZcard hZX
    exact not_isCliqueSum_of_principal hF X hprincipal u v hbad
  push Not at hnotGreatest
  obtain ⟨Z₀, hZ₀F, hZ₀X⟩ := hnotGreatest
  let R := F.filter fun Z => ¬ GaleLE Z X
  have hRne : R.Nonempty := ⟨Z₀, Finset.mem_filter.mpr ⟨hZ₀F, hZ₀X⟩⟩
  obtain ⟨Y, hYR, hYcolex⟩ := Finset.exists_max_image R toColex hRne
  have hYF : Y ∈ F := (Finset.mem_filter.mp hYR).1
  have hYX : ¬ GaleLE Y X := (Finset.mem_filter.mp hYR).2
  have hYmax : ∀ Z ∈ F, GaleLE Y Z → Z = Y := by
    intro Z hZF hYZ
    have hZX : ¬ GaleLE Z X := by
      intro hZX
      exact hYX (galeLE_trans hYZ hZX)
    have hZR : Z ∈ R := Finset.mem_filter.mpr ⟨hZF, hZX⟩
    apply toColex.injective
    exact le_antisymm (hYcolex Z hZR) (toColex_le_of_galeLE hYZ)
  have hXY : ¬ GaleLE X Y := by
    intro hXY
    have hYXeq : Y = X := hXmax Y hYF hXY
    exact hYX (hYXeq.symm ▸ galeLE_refl X)
  have htwo : 2 ≤ F.card := by
    have := cliqueSum_four_le_card hbad
    omega
  have hbottom : IsGaleLeast F I ∧ IsGaleSecondLeast F I M₂ := by
    rcases lemma2_universalPair_is_galeLeast hF hbad with
      ⟨huLeast, hvSecond⟩ | ⟨hvLeast, huSecond⟩
    · have huEq : u.val = I := by
        simpa [I, G] using galeLeast_eq_initialSegment hF huLeast
      have hvEq : v.val = M₂ := by
        simpa [M₂, G] using
          galeSecondLeast_eq_secondInitialSegment hF htwo huLeast hvSecond
      constructor
      · rw [← huEq]
        exact huLeast
      · rw [← huEq, ← hvEq]
        exact hvSecond
    · have hvEq : v.val = I := by
        simpa [I, G] using galeLeast_eq_initialSegment hF hvLeast
      have huEq : u.val = M₂ := by
        simpa [M₂, G] using
          galeSecondLeast_eq_secondInitialSegment hF htwo hvLeast huSecond
      constructor
      · rw [← hvEq]
        exact hvLeast
      · rw [← hvEq, ← huEq]
        exact huSecond
  have hXneI : X ≠ I := by
    intro hXI
    subst X
    exact hXY (hbottom.1.2 Y hYF)
  have hXneM₂ : X ≠ M₂ := by
    intro hXM₂
    subst X
    by_cases hYI : Y = I
    · subst Y
      exact hYX (hbottom.1.2 M₂ hbottom.2.1)
    · exact hXY (hbottom.2.2.2 Y hYF hYI)
  have hYneI : Y ≠ I := by
    intro hYI
    subst Y
    exact hYX (hbottom.1.2 X hXF)
  have hYneM₂ : Y ≠ M₂ := by
    intro hYM₂
    subst Y
    by_cases hXI : X = I
    · subst X
      exact hXY (hbottom.1.2 M₂ hbottom.2.1)
    · exact hYX (hbottom.2.2.2 X hXF hXI)
  have arm_cases {Z : Finset α} (hZF : Z ∈ F) (hZI : Z ≠ I) (hZM₂ : Z ≠ M₂) :
      Z ∈ P ∨ Z ∈ Q := by
    have hZF' := hZF
    rw [hclass] at hZF'
    change Z ∈ ({I, M₂} ∪ P) ∪ Q at hZF'
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hZF'
    rcases hZF' with ((hZI' | hZM₂') | hZP) | hZQ
    · exact (hZI hZI').elim
    · exact (hZM₂ hZM₂').elim
    · exact Or.inl hZP
    · exact Or.inr hZQ
  have hCsubU : C ⊆ U := initialSegment_mono G (by omega)
  have outer_comparable {A B : Finset α} (hAP : A ∈ P) (hBP : B ∈ P) :
      GaleLE A B ∨ GaleLE B A := by
    change A ∈ yOuterArm G κ r at hAP
    change B ∈ yOuterArm G κ r at hBP
    rw [yOuterArm] at hAP hBP
    obtain ⟨a, haSource, rfl⟩ := Finset.mem_image.mp hAP
    obtain ⟨b, hbSource, rfl⟩ := Finset.mem_image.mp hBP
    have haU : a ∉ U := (Finset.mem_filter.mp haSource).2.1
    have hbU : b ∉ U := (Finset.mem_filter.mp hbSource).2.1
    have haC : a ∉ C := fun haC => haU (hCsubU haC)
    have hbC : b ∉ C := fun hbC => hbU (hCsubU hbC)
    rcases le_total a b with hab | hba
    · by_cases heq : a = b
      · subst b
        exact Or.inl (galeLE_refl _)
      · left
        have hdec := galeLE_singleDecrement
          (X := insert b C) (i := a) (j := b) (Finset.mem_insert_self _ _)
          (lt_of_le_of_ne hab heq) (by simp [haC, heq])
        simpa [hbC] using hdec
    · by_cases heq : b = a
      · subst b
        exact Or.inl (galeLE_refl _)
      · right
        have hdec := galeLE_singleDecrement
          (X := insert a C) (i := b) (j := a) (Finset.mem_insert_self _ _)
          (lt_of_le_of_ne hba heq) (by simp [hbC, heq])
        simpa [haC] using hdec
  have inner_comparable {A B : Finset α} (hAQ : A ∈ Q) (hBQ : B ∈ Q) :
      GaleLE A B ∨ GaleLE B A := by
    change A ∈ yInnerArm G κ s at hAQ
    change B ∈ yInnerArm G κ s at hBQ
    rw [yInnerArm] at hAQ hBQ
    obtain ⟨i, hiSource, rfl⟩ := Finset.mem_image.mp hAQ
    obtain ⟨j, hjSource, rfl⟩ := Finset.mem_image.mp hBQ
    have hiU : i ∈ U := hCsubU (Finset.mem_filter.mp hiSource).1
    have hjU : j ∈ U := hCsubU (Finset.mem_filter.mp hjSource).1
    have restore_other {x y : α} (hxU : x ∈ U) (hxy : x ≠ y) :
        insert x ((U.erase x).erase y) = U.erase y := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro (rfl | ⟨hzy, _hzx, hzU⟩)
        · exact ⟨hxy, hxU⟩
        · exact ⟨hzy, hzU⟩
      · rintro ⟨hzy, hzU⟩
        by_cases hzx : z = x
        · exact Or.inl hzx
        · exact Or.inr ⟨hzy, hzx, hzU⟩
    rcases le_total i j with hij | hji
    · by_cases heq : i = j
      · subst j
        exact Or.inl (galeLE_refl _)
      · right
        have hlt : i < j := lt_of_le_of_ne hij heq
        have hdec := galeLE_singleDecrement
          (X := U.erase i) (i := i) (j := j)
          (Finset.mem_erase.mpr ⟨hlt.ne', hjU⟩) hlt (Finset.notMem_erase _ _)
        rw [restore_other hiU hlt.ne] at hdec
        exact hdec
    · by_cases heq : j = i
      · subst j
        exact Or.inl (galeLE_refl _)
      · left
        have hlt : j < i := lt_of_le_of_ne hji heq
        have hdec := galeLE_singleDecrement
          (X := U.erase j) (i := j) (j := i)
          (Finset.mem_erase.mpr ⟨hlt.ne', hiU⟩) hlt (Finset.notMem_erase _ _)
        rw [restore_other hjU hlt.ne] at hdec
        exact hdec
  rcases arm_cases hXF hXneI hXneM₂ with hXP | hXQ <;>
    rcases arm_cases hYF hYneI hYneM₂ with hYP | hYQ
  · rcases outer_comparable hXP hYP with h | h
    · exact (hXY h).elim
    · exact (hYX h).elim
  · exact ⟨r, s, X, Y, hrG, hrOut, hsC, hclass,
      hXP, hXF, hXmax, hYQ, hYF, hYmax, hXY, hYX⟩
  · exact ⟨r, s, Y, X, hrG, hrOut, hsC, hclass,
      hYP, hYF, hYmax, hXQ, hXF, hXmax, hYX, hXY⟩
  · rcases inner_comparable hXQ hYQ with h | h
    · exact (hXY h).elim
    · exact (hYX h).elim

/-- **Lemma 7.1(b).** On `[n]`, a one-position gap in a one-point lift of `[k]`
forces the canonical second member `m₂`; its sole single decrement is `m₁ = [k]`.
The positions are expressed with the zero-based `groundRank` convention. -/
theorem lemma7_1b_one_decrement {n k : ℕ} {i a : Fin n}
    (hi : i ∈ initialSegment (Finset.univ : Finset (Fin n)) k)
    (ha : a ∉ initialSegment (Finset.univ : Finset (Fin n)) k)
    (hgap : groundRank (Finset.univ : Finset (Fin n)) a =
      groundRank (Finset.univ : Finset (Fin n)) i + 1) :
    let m₁ := initialSegment (Finset.univ : Finset (Fin n)) k
    let W := insert a (m₁.erase i)
    W = secondInitialSegment Finset.univ k ∧ singleDecrements W = {m₁} := by
  let m₁ := initialSegment (Finset.univ : Finset (Fin n)) k
  let W := insert a (m₁.erase i)
  have hiVal : i.val < k := by
    change i ∈ (Finset.univ : Finset (Fin n)).filter
      (fun x => groundRank Finset.univ x < k) at hi
    simpa [groundRank_univ_fin] using (Finset.mem_filter.mp hi).2
  have haVal : k ≤ a.val := by
    change a ∉ (Finset.univ : Finset (Fin n)).filter
      (fun x => groundRank Finset.univ x < k) at ha
    simpa [groundRank_univ_fin] using ha
  have hgapVal : a.val = i.val + 1 := by
    simpa [groundRank_univ_fin] using hgap
  have hiTop : i.val + 1 = k := by omega
  have haTop : a.val = k := by omega
  have hia : i < a := by exact_mod_cast (show i.val < a.val by omega)
  have hiM₁ : i ∈ m₁ := hi
  have haM₁ : a ∉ m₁ := ha
  have hIic : m₁ = Finset.Iic i := by
    ext x
    simp [m₁, initialSegment, groundRank_univ_fin, Fin.ext_iff]
    omega
  have hIoo : Finset.Ioo i a = ∅ := by
    ext x
    simp [Fin.ext_iff]
    omega
  have hIoc : Finset.Ioc i i = ∅ := by simp
  have hrestore : insert i (W.erase a) = m₁ := by
    simp [W, haM₁, hiM₁]
  have hWm₂ : W = secondInitialSegment Finset.univ k := by
    ext x
    simp [W, m₁, secondInitialSegment, initialSegment, groundRank_univ_fin,
      Fin.ext_iff]
    omega
  have hcensus := singleDecrements_insert_erase_Iic
    (i := i) (k := i) (a := a) le_rfl hia
  rw [← hIic] at hcensus
  change singleDecrements W = _ at hcensus
  rw [hIoo, hIoc] at hcensus
  simp only [Finset.insert_empty, Finset.image_singleton, Finset.image_empty,
    Finset.union_empty] at hcensus
  rw [hrestore] at hcensus
  exact ⟨hWm₂, hcensus⟩

/-- **Lemma 7.1(c).** On `[n]`, a two-position gap gives exactly the two forms in
the manuscript (only the second survives when `k = 1`), and in either form the
single-decrement set is exactly `{m₁, m₂}`. -/
theorem lemma7_1c_two_decrements {n k : ℕ} {i a : Fin n}
    (hi : i ∈ initialSegment (Finset.univ : Finset (Fin n)) k)
    (ha : a ∉ initialSegment (Finset.univ : Finset (Fin n)) k)
    (hgap : groundRank (Finset.univ : Finset (Fin n)) a =
      groundRank (Finset.univ : Finset (Fin n)) i + 2) :
    let m₁ := initialSegment (Finset.univ : Finset (Fin n)) k
    let m₂ := secondInitialSegment (Finset.univ : Finset (Fin n)) k
    let W := insert a (m₁.erase i)
    (((k = 1 ∧ W = groundPosition Finset.univ 3) ∨
        (2 ≤ k ∧
          (W = (m₁ \ groundPosition Finset.univ (k - 1)) ∪
              groundPosition Finset.univ (k + 1) ∨
           W = initialSegment Finset.univ (k - 1) ∪
              groundPosition Finset.univ (k + 2)))) ∧
      singleDecrements W = {m₁, m₂}) := by
  let m₁ := initialSegment (Finset.univ : Finset (Fin n)) k
  let m₂ := secondInitialSegment (Finset.univ : Finset (Fin n)) k
  let W := insert a (m₁.erase i)
  have hiVal : i.val < k := by
    change i ∈ (Finset.univ : Finset (Fin n)).filter
      (fun x => groundRank Finset.univ x < k) at hi
    simpa [groundRank_univ_fin] using (Finset.mem_filter.mp hi).2
  have haVal : k ≤ a.val := by
    change a ∉ (Finset.univ : Finset (Fin n)).filter
      (fun x => groundRank Finset.univ x < k) at ha
    simpa [groundRank_univ_fin] using ha
  have hgapVal : a.val = i.val + 2 := by
    simpa [groundRank_univ_fin] using hgap
  have hiM₁ : i ∈ m₁ := hi
  have haM₁ : a ∉ m₁ := ha
  have hrestore : insert i (W.erase a) = m₁ := by
    simp [W, haM₁, hiM₁]
  by_cases htop : i.val + 1 = k
  · have haPos : a.val = k + 1 := by omega
    let b : Fin n := ⟨k, by omega⟩
    have hib : i < b := by exact_mod_cast (show i.val < b.val by simp [b]; omega)
    have hba : b < a := by exact_mod_cast (show b.val < a.val by simp [b]; omega)
    have hbMem : b ∈ initialSegment (Finset.univ : Finset (Fin n)) (k + 1) := by
      simp [initialSegment, groundRank_univ_fin, b]
    have hbNot : b ∉ m₁ := by
      simp [m₁, initialSegment, groundRank_univ_fin, b]
    have hIic : m₁ = Finset.Iic i := by
      ext x
      simp [m₁, initialSegment, groundRank_univ_fin, Fin.ext_iff]
      omega
    have hIoo : Finset.Ioo i a = {b} := by
      ext x
      simp [b, Fin.ext_iff]
      omega
    have hIoc : Finset.Ioc i i = ∅ := by simp
    have hbGap : groundRank (Finset.univ : Finset (Fin n)) b =
        groundRank (Finset.univ : Finset (Fin n)) i + 1 := by
      simp [groundRank_univ_fin, b]
      omega
    have hbSecond := (lemma7_1b_one_decrement
      (i := i) (a := b) hi hbNot hbGap).1
    change insert b (m₁.erase i) = m₂ at hbSecond
    have hreplaceB : insert b (W.erase a) = m₂ := by
      simpa [W, haM₁] using hbSecond
    have hcensus := singleDecrements_insert_erase_Iic
      (i := i) (k := i) (a := a) le_rfl (hib.trans hba)
    rw [← hIic] at hcensus
    change singleDecrements W = _ at hcensus
    rw [hIoo, hIoc] at hcensus
    simp only [Finset.image_insert, Finset.image_singleton, Finset.image_empty,
      Finset.union_empty] at hcensus
    rw [hrestore, hreplaceB] at hcensus
    have hform :
        (k = 1 ∧ W = groundPosition Finset.univ 3) ∨
          (2 ≤ k ∧
            (W = (m₁ \ groundPosition Finset.univ (k - 1)) ∪
                groundPosition Finset.univ (k + 1) ∨
             W = initialSegment Finset.univ (k - 1) ∪
                groundPosition Finset.univ (k + 2))) := by
      by_cases hk1 : k = 1
      · left
        refine ⟨hk1, ?_⟩
        ext x
        simp [W, m₁, groundPosition, initialSegment, groundRank_univ_fin,
          Fin.ext_iff]
        omega
      · right
        refine ⟨by omega, Or.inr ?_⟩
        ext x
        simp [W, m₁, groundPosition, initialSegment, groundRank_univ_fin,
          Fin.ext_iff]
        omega
    exact ⟨hform, by simpa [Finset.pair_comm] using hcensus⟩
  · have hiPenult : i.val + 2 = k := by omega
    have haPos : a.val = k := by omega
    have hk : 2 ≤ k := by omega
    let j : Fin n := ⟨k - 1, by omega⟩
    have hij : i < j := by
      exact_mod_cast (show i.val < j.val by simp [j]; omega)
    have hja : j < a := by
      exact_mod_cast (show j.val < a.val by simp [j]; omega)
    have hjm₁ : j ∈ m₁ := by
      simp [m₁, initialSegment, groundRank_univ_fin, j]
      omega
    have haNot : a ∉ m₁ := ha
    have hIic : m₁ = Finset.Iic j := by
      ext x
      simp [m₁, initialSegment, groundRank_univ_fin, j, Fin.ext_iff]
      omega
    have hIoo : Finset.Ioo j a = ∅ := by
      ext x
      simp [j, Fin.ext_iff]
      omega
    have hIoc : Finset.Ioc i j = {j} := by
      ext x
      simp [j, Fin.ext_iff]
      omega
    have hjGap : groundRank (Finset.univ : Finset (Fin n)) a =
        groundRank (Finset.univ : Finset (Fin n)) j + 1 := by
      simp [groundRank_univ_fin, j]
      omega
    have hjSecond := (lemma7_1b_one_decrement
      (i := j) (a := a) hjm₁ haNot hjGap).1
    change insert a (m₁.erase j) = m₂ at hjSecond
    have hsecond : insert i (W.erase j) = m₂ := by
      change insert i ((insert a (m₁.erase i)).erase j) = m₂
      rw [insert_erase_insert_erase hiM₁ hjm₁ haM₁ hij.ne]
      exact hjSecond
    have hcensus := singleDecrements_insert_erase_Iic
      (i := i) (k := j) (a := a) hij.le hja
    rw [← hIic] at hcensus
    change singleDecrements W = _ at hcensus
    rw [hIoo, hIoc] at hcensus
    simp only [Finset.insert_empty, Finset.image_singleton] at hcensus
    rw [hrestore, hsecond] at hcensus
    have hform :
        (k = 1 ∧ W = groundPosition Finset.univ 3) ∨
          (2 ≤ k ∧
            (W = (m₁ \ groundPosition Finset.univ (k - 1)) ∪
                groundPosition Finset.univ (k + 1) ∨
             W = initialSegment Finset.univ (k - 1) ∪
                groundPosition Finset.univ (k + 2))) := by
      right
      refine ⟨hk, Or.inl ?_⟩
      ext x
      simp [W, m₁, groundPosition, initialSegment, groundRank_univ_fin,
        Fin.ext_iff]
      omega
    exact ⟨hform, by simpa [Finset.pair_comm] using hcensus⟩

/-- **Lemma 7.1(d).** If a `k`-subset `W` of `[n]` has at least two elements outside the
initial segment `[k]`, then `W` has at least four distinct single decrements. -/
theorem lemma7_1d_four_decrements {n k : ℕ} {W : Finset (Fin n)}
    (hWcard : W.card = k)
    (htwo : 2 ≤ (W \ initialSegment (Finset.univ : Finset (Fin n)) k).card) :
    4 ≤ (singleDecrements W).card := by
  let m₁ := initialSegment (Finset.univ : Finset (Fin n)) k
  have hk : k ≤ n := by
    rw [← hWcard]
    simpa using Finset.card_le_card (Finset.subset_univ W)
  apply four_le_card_singleDecrements_of_two_outside
      (m₁ := m₁) (W := W) (htwo := htwo)
  · rw [card_initialSegment_of_le (by simpa using hk), hWcard]
  · intro p hp a ha
    have hpVal : p.val < k := by
      change p ∈ (Finset.univ : Finset (Fin n)).filter
        (fun x => groundRank Finset.univ x < k) at hp
      simpa [groundRank_univ_fin] using (Finset.mem_filter.mp hp).2
    have haVal : k ≤ a.val := by
      change a ∉ (Finset.univ : Finset (Fin n)).filter
        (fun x => groundRank Finset.univ x < k) at ha
      simpa [groundRank_univ_fin] using ha
    exact_mod_cast (show p.val < a.val by omega)

/-- **Corollary — the exception is invisible in the principal case.** Every clique-sum is
non-principal (it has two incomparable Gale-maximal elements), so on a principal ideal `(Q*)` has no
exception and gives Hamilton-connectivity outright.

This is the statement offered to the pancyclicity and tournament lanes on 2026-08-15: where they
cite Naddef–Pulleyblank for Hamilton-connectivity of a shifted/Schubert matroid basis graph, `(Q*)`
supplies the same conclusion from a chain with no external citation. -/
theorem qstar_no_exception_of_principal {F : Finset (Finset α)} {κ : ℕ} (hF : IsShifted F κ)
    (M : Finset α) (hprincipal : ∀ X, X ∈ F ↔ (X.card = κ ∧ GaleLE X M)) :
    IsHamConnected (exchangeGraph F) := by
  intro A B hAB
  exact (qstar hF A B hAB).2 (not_isCliqueSum_of_principal hF M hprincipal A B)

/-- **The principal case, stated on its own terms.** The members of `F` dominated by a single `M`
form a shifted family, and `(Q*)` gives Hamilton-connectivity there with no exception. This is the
statement other lanes in this development can cite in place of a matroid basis-graph theorem, and it
is proved from `qstar` alone. -/
theorem qstar_principal_isHamConnected {κ : ℕ} (M : Finset α)
    (F : Finset (Finset α)) (hF : ∀ X, X ∈ F ↔ (X.card = κ ∧ GaleLE X M)) (hne : F.Nonempty) :
    IsHamConnected (exchangeGraph F) := by
  exact qstar_no_exception_of_principal (isShifted_of_principal M hF hne) M hF

/-- **Corollary 7.9, in the form the manuscript prints it.** A shifted family with a Gale-greatest
member is never a clique-sum, and its Johnson graph is Hamilton-connected.

This exists because the printed corollary hypothesizes a **greatest member**, while
`qstar_no_exception_of_principal` hypothesizes the **principal equation**
`X ∈ F ↔ (X.card = κ ∧ GaleLE X M)`.  The two are NOT equivalent, and the direction matters: under
shiftedness the greatest-member hypotheses imply the equation, which is what the proof below does,
but the equation does not imply them — it never forces `M.card = κ`, hence never forces `M ∈ F`.  So
the printed hypothesis is the stronger one and this theorem is the weaker statement; what was missing
was not generality but the bridge, since no declaration carried that derivation together with the
printed conclusion. -/
theorem qstar_hamConnected_of_galeGreatest {F : Finset (Finset α)} {κ : ℕ} (hF : IsShifted F κ)
    {M : Finset α} (hMF : M ∈ F) (hgreatest : ∀ X ∈ F, GaleLE X M) :
    (∀ u v : ExchangeV F, ¬ IsCliqueSum F u v) ∧ IsHamConnected (exchangeGraph F) := by
  have hprincipal : ∀ X, X ∈ F ↔ (X.card = κ ∧ GaleLE X M) := by
    intro X
    refine ⟨fun hXF => ⟨hF.2.1 X hXF, hgreatest X hXF⟩, ?_⟩
    rintro ⟨hcard, hXM⟩
    exact ((isShifted_iff_isGaleIdeal F κ).1 hF).2.2 M hMF X hcard hXM
  exact ⟨not_isCliqueSum_of_principal hF M hprincipal,
         qstar_no_exception_of_principal hF M hprincipal⟩

end Brualdi.RealizationGraph.QStar
