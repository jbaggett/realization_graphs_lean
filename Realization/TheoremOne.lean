/-
Copyright (c) 2026 Jeffrey S. Baggett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey S. Baggett
-/
import BrualdiLean.Ledger
import Realization.CrownBase
import Realization.Defs
import Realization.Prism
import Mathlib.Combinatorics.SimpleGraph.Clique

set_option autoImplicit false
set_option linter.style.header false
set_option linter.style.nativeDecide false

namespace Brualdi.RealizationGraph

open Brualdi.Ledger

universe u

/-!
Theorem 1 glue for the realization-graph paper.

Barrus's 2016 Theorem 9 is an isomorphism classification: every bipartite/triangle-free
realization graph is a Cartesian product of complete transposition graphs, with at most one
exceptional `K_{6,6} - 6K_2` crown factor.  The fully faithful Lean statement would quantify over
the isomorphism target chosen by that classification.  To keep this glue honest and lightweight,
we factor the citation exactly as the paper uses it: Barrus reduces the realization graph to the
normalized product families below, and the machine-checked composition theorem proves those
families maximally Hamiltonian.

The normalization removes `CT_1` factors, since they are one-vertex factors and do not change the
Cartesian product.  The no-crown empty product is the one-vertex graph; the crown branch permits
an empty CT list, giving the crown itself.
-/

/-- Recursive Cartesian product of complete transposition graphs over a fixed leaf graph. -/
abbrev CTLeafProductVertex (ranks : List Nat) (X : Type) : Type :=
  match ranks with
  | [] => X
  | a :: tail => Equiv.Perm (Fin a) × CTLeafProductVertex tail X

instance instDecidableEqCTLeafProductVertex (ranks : List Nat) (X : Type) [DecidableEq X] :
    DecidableEq (CTLeafProductVertex ranks X) := by
  induction ranks with
  | nil =>
      change DecidableEq X
      infer_instance
  | cons a tail ih =>
      letI := ih
      change DecidableEq (Equiv.Perm (Fin a) × CTLeafProductVertex tail X)
      infer_instance

instance instFintypeCTLeafProductVertex (ranks : List Nat) (X : Type) [Fintype X] :
    Fintype (CTLeafProductVertex ranks X) := by
  induction ranks with
  | nil =>
      change Fintype X
      infer_instance
  | cons a tail ih =>
      letI := ih
      change Fintype (Equiv.Perm (Fin a) × CTLeafProductVertex tail X)
      infer_instance

/-- The graph product `CT_{r₁} □ ... □ CT_{rₙ} □ B`. -/
def CTLeafProductGraph {X : Type} (ranks : List Nat) (B : SimpleGraph X) :
    SimpleGraph (CTLeafProductVertex ranks X) :=
  match ranks with
  | [] => B
  | a :: tail => CompleteTranspositionGraph a □ CTLeafProductGraph tail B

/-- The xor product colouring on `CT_{r₁} □ ... □ CT_{rₙ} □ B`. -/
def CTLeafProductColor {X : Type} (ranks : List Nat) (colB : X → Bool) :
    CTLeafProductVertex ranks X → Bool :=
  match ranks with
  | [] => colB
  | a :: tail => fun x =>
      Bool.xor (CompleteTranspositionColor a x.1) (CTLeafProductColor tail colB x.2)

abbrev CTCrownProductGraph (ranks : List Nat) :
    SimpleGraph (CTLeafProductVertex ranks CrownV) :=
  CTLeafProductGraph ranks crownGraph

abbrev CTCrownProductColor (ranks : List Nat) :
    CTLeafProductVertex ranks CrownV → Bool :=
  CTLeafProductColor ranks crownColor

private theorem empty_ctProduct_mh : IsMH (CTProductGraph []) := by
  change IsMH (⊥ : SimpleGraph PUnit)
  exact Or.inl fun u v huv => (huv (Subsingleton.elim u v)).elim

private theorem ctProduct_nonempty (ranks : List Nat) (hne : ranks ≠ []) :
    Nonempty (CTProductVertex ranks) :=
  ctProductVertex_nonempty ranks hne

private theorem ctProduct_has_edge :
    ∀ (ranks : List Nat), ranks ≠ [] → (∀ a ∈ ranks, 2 ≤ a) →
      ∃ u v : CTProductVertex ranks, (CTProductGraph ranks).Adj u v
  | [], hne, _ => absurd rfl hne
  | [a], _, hall => by
      change ∃ u v : Equiv.Perm (Fin a), (CompleteTranspositionGraph a).Adj u v
      have ha : 2 ≤ a := hall a (by simp)
      let i : Fin a := ⟨0, by omega⟩
      let j : Fin a := ⟨1, by omega⟩
      have hij : i ≠ j := by
        simp [i, j, Fin.ext_iff]
      refine ⟨1, Equiv.swap i j, ?_⟩
      show (SimpleGraph.fromRel _).Adj _ _
      rw [SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl ?_⟩
      · intro h
        have hs : i = j := by
          simpa [Equiv.swap_apply_left, hij] using
            congrArg (fun σ : Equiv.Perm (Fin a) => σ i) h
        exact hij hs
      · simp only [inv_one, one_mul]
        exact ⟨i, j, hij, rfl⟩
  | a :: b :: tail, _, hall => by
      change ∃ u v : Equiv.Perm (Fin a) × CTProductVertex (b :: tail),
        (CompleteTranspositionGraph a □ CTProductGraph (b :: tail)).Adj u v
      have ha : 2 ≤ a := hall a (by simp)
      let i : Fin a := ⟨0, by omega⟩
      let j : Fin a := ⟨1, by omega⟩
      have hij : i ≠ j := by
        simp [i, j, Fin.ext_iff]
      obtain ⟨x⟩ : Nonempty (CTProductVertex (b :: tail)) :=
        ctProductVertex_nonempty (b :: tail) (by simp)
      refine ⟨(1, x), (Equiv.swap i j, x), ?_⟩
      rw [SimpleGraph.boxProd_adj]
      refine Or.inl ⟨?_, rfl⟩
      show (SimpleGraph.fromRel _).Adj _ _
      rw [SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl ?_⟩
      · intro h
        have hs : i = j := by
          simpa [Equiv.swap_apply_left, hij] using
            congrArg (fun σ : Equiv.Perm (Fin a) => σ i) h
        exact hij hs
      · simp only [inv_one, one_mul]
        exact ⟨i, j, hij, rfl⟩

private theorem two_mul_pred_le_card_perm_ge2 {a : Nat} (ha : 2 ≤ a) :
    2 * (a - 1) ≤ Fintype.card (Equiv.Perm (Fin a)) := by
  rw [Fintype.card_perm, Fintype.card_fin]
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have hb : 1 ≤ b := by omega
  have h1 : 2 * (b + 1 - 1) ≤ (b + 1) * b := by
    rw [Nat.add_sub_cancel]
    exact Nat.mul_le_mul_right b (by omega : 2 ≤ b + 1)
  have h2 : b ≤ b.factorial := Nat.self_le_factorial b
  calc
    2 * (b + 1 - 1) ≤ (b + 1) * b := h1
    _ ≤ (b + 1) * b.factorial := Nat.mul_le_mul_left _ h2
    _ = (b + 1).factorial := (Nat.factorial_succ b).symm

private theorem ctProduct_hamLaceable (ranks : List Nat) (hne : ranks ≠ [])
    (hall : ∀ a ∈ ranks, 2 ≤ a) :
    IsHamLaceable (CTProductGraph ranks) (CTProductColor ranks) := by
  classical
  have hEq : IsEquitableBipartite (CTProductGraph ranks) (CTProductColor ranks) :=
    ctProduct_equitable_aux ranks hne hall
  by_cases hcard2 : Fintype.card (CTProductVertex ranks) = 2
  · exact laceable_card_two (CTProductColor ranks) hcard2 (ctProduct_has_edge ranks hne hall)
  · have hpos : 0 < Fintype.card (CTProductVertex ranks) :=
      Fintype.card_pos_iff.mpr (ctProduct_nonempty ranks hne)
    obtain ⟨hd, tl, hr⟩ := List.exists_cons_of_ne_nil hne
    have hhd : 2 ≤ hd := by
      subst hr
      exact hall hd (by simp)
    have heven : Even (Fintype.card (CTProductVertex ranks)) := by
      subst hr
      simpa [Nat.card_eq_fintype_card] using (ctProductVertex_card_even hhd)
    have h4 : 4 ≤ Fintype.card (CTProductVertex ranks) := by
      rcases heven with ⟨k, hk⟩
      omega
    exact paired_two_opposite_to_hamLaceable hEq
      (ctProduct_paired_two_of_ranks ranks hne hall) h4

/-- A normalized nonempty product of complete transposition graphs is maximally Hamiltonian. -/
theorem ctProduct_maximally_hamiltonian (ranks : List Nat) (hne : ranks ≠ [])
    (hall : ∀ a ∈ ranks, 2 ≤ a) :
    IsMH (CTProductGraph ranks) := by
  classical
  have hEq : IsEquitableBipartite (CTProductGraph ranks) (CTProductColor ranks) :=
    ctProduct_equitable_aux ranks hne hall
  exact Or.inr ⟨CTProductColor ranks, hEq.1,
    surjective_of_equitable_nonempty hEq (ctProduct_nonempty ranks hne),
    ctProduct_hamLaceable ranks hne hall⟩

private theorem crown_proper : IsProper2Coloring crownGraph crownColor := by
  intro u v huv
  exact huv.1

private theorem crown_surjective : Function.Surjective crownColor := by
  intro b
  cases b
  · refine ⟨0, ?_⟩
    simp [crownColor]
  · refine ⟨6, ?_⟩
    simp [crownColor]

private theorem crown_equitable : IsEquitableBipartite crownGraph crownColor := by
  refine ⟨crown_proper, ?_⟩
  decide

private theorem crown_hamLaceable : IsHamLaceable crownGraph crownColor := by
  have hcard : 4 ≤ Fintype.card CrownV := by
    change 4 ≤ Fintype.card (Fin 12)
    norm_num
  exact paired_two_opposite_to_hamLaceable crown_equitable
    (paired_two_of_spanning2 crown_spanning2_laceable) hcard

private theorem ctBox_equitable {X : Type} [DecidableEq X] [Fintype X]
    (a : Nat) (ha : 2 ≤ a) {B : SimpleGraph X} {colB : X → Bool}
    (hBprop : IsProper2Coloring B colB) :
    IsEquitableBipartite (CompleteTranspositionGraph a □ B)
      (fun x : Equiv.Perm (Fin a) × X => Bool.xor (CompleteTranspositionColor a x.1) (colB x.2)) := by
  classical
  refine ⟨boxProd_proper_color (completeTransposition_equitable a ha).1 hBprop, ?_⟩
  let i : Fin a := ⟨0, by omega⟩
  let j : Fin a := ⟨1, by omega⟩
  have hij : i ≠ j := by
    simp [i, j, Fin.ext_iff]
  let c : Equiv.Perm (Fin a) := Equiv.swap i j
  have hc : Equiv.Perm.sign c = -1 := Equiv.Perm.sign_swap hij
  have hcc : c * c = 1 := Equiv.swap_mul_self i j
  apply Fintype.card_congr
  refine ⟨fun x => ⟨(c * x.1.1, x.1.2), ?_⟩,
    fun y => ⟨(c * y.1.1, y.1.2), ?_⟩, ?_, ?_⟩
  · have hflip :
        Bool.xor (CompleteTranspositionColor a (c * x.1.1)) (colB x.1.2) =
          !(Bool.xor (CompleteTranspositionColor a x.1.1) (colB x.1.2)) := by
      rw [ctColor_neg a hc]
      cases CompleteTranspositionColor a x.1.1 <;> cases colB x.1.2 <;> rfl
    change Bool.xor (CompleteTranspositionColor a (c * x.1.1)) (colB x.1.2) = true
    rw [hflip]
    simpa using x.2
  · have hflip :
        Bool.xor (CompleteTranspositionColor a (c * y.1.1)) (colB y.1.2) =
          !(Bool.xor (CompleteTranspositionColor a y.1.1) (colB y.1.2)) := by
      rw [ctColor_neg a hc]
      cases CompleteTranspositionColor a y.1.1 <;> cases colB y.1.2 <;> rfl
    change Bool.xor (CompleteTranspositionColor a (c * y.1.1)) (colB y.1.2) = false
    rw [hflip]
    simpa using y.2
  · intro x
    apply Subtype.ext
    refine Prod.ext ?_ rfl
    show c * (c * x.1.1) = x.1.1
    rw [← mul_assoc, hcc, one_mul]
  · intro y
    apply Subtype.ext
    refine Prod.ext ?_ rfl
    show c * (c * y.1.1) = y.1.1
    rw [← mul_assoc, hcc, one_mul]

private theorem ctLeafProduct_nonempty {X : Type} [Nonempty X] :
    ∀ ranks : List Nat, Nonempty (CTLeafProductVertex ranks X)
  | [] => by
      change Nonempty X
      infer_instance
  | _ :: tail => by
      obtain ⟨x⟩ := ctLeafProduct_nonempty (X := X) tail
      exact ⟨(1, x)⟩

private theorem ctLeafProduct_even {X : Type} [Fintype X]
    (hX : Even (Fintype.card X)) :
    ∀ ranks : List Nat, Even (Fintype.card (CTLeafProductVertex ranks X))
  | [] => hX
  | a :: tail => by
      have htail := ctLeafProduct_even hX tail
      change Even (Fintype.card (Equiv.Perm (Fin a) × CTLeafProductVertex tail X))
      rw [Fintype.card_prod]
      exact htail.mul_left _

private theorem ctLeafProduct_proper {X : Type} [DecidableEq X]
    {B : SimpleGraph X} {colB : X → Bool}
    (hB : IsProper2Coloring B colB) :
    ∀ ranks : List Nat, (∀ a ∈ ranks, 2 ≤ a) →
      IsProper2Coloring (CTLeafProductGraph ranks B) (CTLeafProductColor ranks colB)
  | [], _ => hB
  | a :: tail, hall => by
      have ha : 2 ≤ a := hall a (by simp)
      have htail : IsProper2Coloring (CTLeafProductGraph tail B)
          (CTLeafProductColor tail colB) :=
        ctLeafProduct_proper hB tail (fun b hb => hall b (List.mem_cons_of_mem a hb))
      change IsProper2Coloring (CompleteTranspositionGraph a □ CTLeafProductGraph tail B)
        (fun x : Equiv.Perm (Fin a) × CTLeafProductVertex tail X =>
          Bool.xor (CompleteTranspositionColor a x.1) (CTLeafProductColor tail colB x.2))
      exact boxProd_proper_color (completeTransposition_equitable a ha).1 htail

private theorem ctLeafProduct_surjective {X : Type} [DecidableEq X]
    {colB : X → Bool} (hB : Function.Surjective colB) :
    ∀ ranks : List Nat, Function.Surjective (CTLeafProductColor ranks colB)
  | [], b => hB b
  | a :: tail, b => by
      let σ : Equiv.Perm (Fin a) := 1
      have htail := ctLeafProduct_surjective hB tail
      by_cases hσ : CompleteTranspositionColor a σ = false
      · obtain ⟨x, hx⟩ := htail b
        refine ⟨(σ, x), ?_⟩
        simp [CTLeafProductColor, hσ, hx]
      · have hσt : CompleteTranspositionColor a σ = true := by
          cases h : CompleteTranspositionColor a σ <;> simp_all
        obtain ⟨x, hx⟩ := htail (!b)
        refine ⟨(σ, x), ?_⟩
        cases b <;> simp [CTLeafProductColor, hσt, hx]

private theorem ctLeafProduct_equitable {X : Type} [DecidableEq X] [Fintype X]
    {B : SimpleGraph X} {colB : X → Bool} (hB : IsEquitableBipartite B colB) :
    ∀ ranks : List Nat, (∀ a ∈ ranks, 2 ≤ a) →
      IsEquitableBipartite (CTLeafProductGraph ranks B) (CTLeafProductColor ranks colB)
  | [], _ => hB
  | a :: tail, hall => by
      have ha : 2 ≤ a := hall a (by simp)
      have htail : IsProper2Coloring (CTLeafProductGraph tail B)
          (CTLeafProductColor tail colB) :=
        ctLeafProduct_proper hB.1 tail (fun b hb => hall b (List.mem_cons_of_mem a hb))
      change IsEquitableBipartite (CompleteTranspositionGraph a □ CTLeafProductGraph tail B)
        (fun x : Equiv.Perm (Fin a) × CTLeafProductVertex tail X =>
          Bool.xor (CompleteTranspositionColor a x.1) (CTLeafProductColor tail colB x.2))
      exact ctBox_equitable a ha htail

private theorem ctLeafProduct_card_guard {X : Type} [Fintype X] [Nonempty X]
    (a : Nat) (tail : List Nat) (ha : 2 ≤ a) :
    2 * (a - 1) ≤ Fintype.card (CTLeafProductVertex (a :: tail) X) := by
  change 2 * (a - 1) ≤ Fintype.card (Equiv.Perm (Fin a) × CTLeafProductVertex tail X)
  rw [Fintype.card_prod]
  exact le_trans (two_mul_pred_le_card_perm_ge2 ha)
    (Nat.le_mul_of_pos_right _ (Fintype.card_pos_iff.mpr (ctLeafProduct_nonempty tail)))

private theorem ctLeafProduct_card_leaf_le {X : Type} [Fintype X] [Nonempty X] :
    ∀ ranks : List Nat, Fintype.card X ≤ Fintype.card (CTLeafProductVertex ranks X)
  | [] => le_rfl
  | a :: tail => by
      change Fintype.card X ≤
        Fintype.card (Equiv.Perm (Fin a) × CTLeafProductVertex tail X)
      rw [Fintype.card_prod]
      exact le_trans (ctLeafProduct_card_leaf_le tail) (by
        rw [Nat.mul_comm]
        exact Nat.le_mul_of_pos_right _ Fintype.card_pos)

private theorem ctTwo_adj_iff_ne : ∀ x y : Equiv.Perm (Fin 2),
    (CompleteTranspositionGraph 2).Adj x y ↔ x ≠ y := by
  decide

private noncomputable def ctTwoTopIso :
    CompleteTranspositionGraph 2 ≃g (⊤ : SimpleGraph (Fin 2)) where
  toEquiv :=
    (Equiv.ofBijective (CompleteTranspositionColor 2) (by
      apply (Fintype.bijective_iff_surjective_and_card _).2
      constructor
      · exact surjective_of_equitable_nonempty
          (completeTransposition_equitable 2 (by omega)) inferInstance
      · rw [Fintype.card_perm, Fintype.card_fin]
        decide)).trans finTwoEquiv.symm
  map_rel_iff' := by
    intro x y
    simpa only [SimpleGraph.top_adj, ne_eq, EmbeddingLike.apply_eq_iff_eq] using
      (ctTwo_adj_iff_ne x y).symm

@[simp]
private theorem ctTwoTopIso_color (x : Equiv.Perm (Fin 2)) :
    decide (ctTwoTopIso x = 1) = CompleteTranspositionColor 2 x := by
  change decide (finTwoEquiv.symm (CompleteTranspositionColor 2 x) = 1) =
    CompleteTranspositionColor 2 x
  cases CompleteTranspositionColor 2 x <;> decide

private theorem ctLeafProduct_hamLaceable {X : Type} [DecidableEq X] [Fintype X] [Nonempty X]
    {B : SimpleGraph X} {colB : X → Bool}
    (hBprop : IsProper2Coloring B colB) (hBsurj : Function.Surjective colB)
    (hBeq : IsEquitableBipartite B colB) (hBham : IsHamLaceable B colB)
    (hBeven : Even (Fintype.card X)) :
    ∀ ranks : List Nat, (∀ a ∈ ranks, 2 ≤ a) →
      IsHamLaceable (CTLeafProductGraph ranks B) (CTLeafProductColor ranks colB)
  | [], _ => hBham
  | a :: tail, hall => by
      have ha : 2 ≤ a := hall a (by simp)
      have htailAll : ∀ b ∈ tail, 2 ≤ b := fun b hb => hall b (List.mem_cons_of_mem a hb)
      have hTailProp : IsProper2Coloring (CTLeafProductGraph tail B)
          (CTLeafProductColor tail colB) :=
        ctLeafProduct_proper hBprop tail htailAll
      have hTailSurj : Function.Surjective (CTLeafProductColor tail colB) :=
        ctLeafProduct_surjective hBsurj tail
      have hTailHam : IsHamLaceable (CTLeafProductGraph tail B)
          (CTLeafProductColor tail colB) :=
        ctLeafProduct_hamLaceable hBprop hBsurj hBeq hBham hBeven tail htailAll
      have hTailEven : Even (Fintype.card (CTLeafProductVertex tail X)) :=
        ctLeafProduct_even hBeven tail
      have hTailEvenNat : Even (Nat.card (CTLeafProductVertex tail X)) := by
        simpa [Nat.card_eq_fintype_card] using hTailEven
      have hTree : IsColemanTree
          (CompleteTranspositionGraph a □ CTLeafProductGraph tail B) a :=
        ctBox_tree (X := CTLeafProductVertex tail X)
          (B := CTLeafProductGraph tail B) (colB := CTLeafProductColor tail colB)
          hTailProp hTailSurj hTailHam (Or.inr hTailEvenNat) a (by omega)
      have hEq : IsEquitableBipartite (CTLeafProductGraph (a :: tail) B)
          (CTLeafProductColor (a :: tail) colB) :=
        ctLeafProduct_equitable hBeq (a :: tail) hall
      have hBig : IsPairedKDPCForOpposite (CTLeafProductGraph (a :: tail) B)
          (CTLeafProductColor (a :: tail) colB) (a - 1) := by
        simpa [CTLeafProductGraph, CTLeafProductColor] using
          (coleman_thm15 (CompleteTranspositionGraph a □ CTLeafProductGraph tail B)
            (fun x : Equiv.Perm (Fin a) × CTLeafProductVertex tail X =>
              Bool.xor (CompleteTranspositionColor a x.1) (CTLeafProductColor tail colB x.2))
            a (by omega) hTree
            (by simpa [CTLeafProductGraph, CTLeafProductColor] using hEq.1))
      have hOne : IsPairedKDPCForOpposite (CTLeafProductGraph (a :: tail) B)
          (CTLeafProductColor (a :: tail) colB) 1 :=
        prop11c (CTLeafProductGraph (a :: tail) B) (CTLeafProductColor (a :: tail) colB)
          hEq hBig (by decide : 1 ≤ 1) (by omega)
          (ctLeafProduct_card_guard a tail ha)
      exact paired_one_opposite_iff_hamLaceable.mp hOne

private theorem ctLeafProduct_paired_two {X : Type} [DecidableEq X] [Fintype X] [Nonempty X]
    {B : SimpleGraph X} {colB : X → Bool}
    (hBprop : IsProper2Coloring B colB) (hBsurj : Function.Surjective colB)
    (hBeq : IsEquitableBipartite B colB) (hBham : IsHamLaceable B colB)
    (hBtwo : IsPairedKDPCForOpposite B colB 2) (hBeven : Even (Fintype.card X))
    (hBcard : 4 ≤ Fintype.card X) :
    ∀ ranks : List Nat, (∀ a ∈ ranks, 2 ≤ a) →
      IsPairedKDPCForOpposite (CTLeafProductGraph ranks B)
        (CTLeafProductColor ranks colB) 2
  | [], _ => hBtwo
  | a :: tail, hall => by
      have ha : 2 ≤ a := hall a (by simp)
      have htailAll : ∀ b ∈ tail, 2 ≤ b := fun b hb => hall b (List.mem_cons_of_mem a hb)
      have hTailProp : IsProper2Coloring (CTLeafProductGraph tail B)
          (CTLeafProductColor tail colB) :=
        ctLeafProduct_proper hBprop tail htailAll
      have hTailSurj : Function.Surjective (CTLeafProductColor tail colB) :=
        ctLeafProduct_surjective hBsurj tail
      have hTailEq : IsEquitableBipartite (CTLeafProductGraph tail B)
          (CTLeafProductColor tail colB) :=
        ctLeafProduct_equitable hBeq tail htailAll
      have hTailHam : IsHamLaceable (CTLeafProductGraph tail B)
          (CTLeafProductColor tail colB) :=
        ctLeafProduct_hamLaceable hBprop hBsurj hBeq hBham hBeven tail htailAll
      have hTailTwo : IsPairedKDPCForOpposite (CTLeafProductGraph tail B)
          (CTLeafProductColor tail colB) 2 :=
        ctLeafProduct_paired_two hBprop hBsurj hBeq hBham hBtwo hBeven hBcard tail htailAll
      by_cases ha2 : a = 2
      · subst a
        have h4Tail : 4 ≤ Fintype.card (CTLeafProductVertex tail X) :=
          le_trans hBcard (ctLeafProduct_card_leaf_le tail)
        let e : (CompleteTranspositionGraph 2 □ CTLeafProductGraph tail B) ≃g
            (CTLeafProductGraph tail B □ (⊤ : SimpleGraph (Fin 2))) :=
          (boxProdCongrRight ctTwoTopIso (CTLeafProductGraph tail B)).trans
            (SimpleGraph.boxProdComm _ _)
        have hcol : ∀ v : Equiv.Perm (Fin 2) × CTLeafProductVertex tail X,
            Brualdi.RealizationGraph.Prism.prismColor (CTLeafProductColor tail colB) (e v) =
              Bool.xor (CompleteTranspositionColor 2 v.1)
                (CTLeafProductColor tail colB v.2) := by
          rintro ⟨σ, x⟩
          change Bool.xor (CTLeafProductColor tail colB x)
              (decide (ctTwoTopIso σ = 1)) =
            Bool.xor (CompleteTranspositionColor 2 σ) (CTLeafProductColor tail colB x)
          rw [ctTwoTopIso_color, Bool.xor_comm]
        simpa [CTLeafProductGraph, CTLeafProductColor] using
          (pairedKDPC_iso e
            (fun v : Equiv.Perm (Fin 2) × CTLeafProductVertex tail X =>
              Bool.xor (CompleteTranspositionColor 2 v.1)
                (CTLeafProductColor tail colB v.2))
            (Brualdi.RealizationGraph.Prism.prismColor (CTLeafProductColor tail colB)) hcol
            (Brualdi.RealizationGraph.Prism.prism_paired_two_proved hTailEq h4Tail hTailTwo))
      · have ha3 : 3 ≤ a := by omega
        have hTailEven : Even (Fintype.card (CTLeafProductVertex tail X)) :=
          ctLeafProduct_even hBeven tail
        have hTailEvenNat : Even (Nat.card (CTLeafProductVertex tail X)) := by
          simpa [Nat.card_eq_fintype_card] using hTailEven
        have hTree : IsColemanTree
            (CompleteTranspositionGraph a □ CTLeafProductGraph tail B) a :=
          ctBox_tree (X := CTLeafProductVertex tail X)
            (B := CTLeafProductGraph tail B) (colB := CTLeafProductColor tail colB)
            hTailProp hTailSurj hTailHam (Or.inr hTailEvenNat) a (by omega)
        have hEq : IsEquitableBipartite (CTLeafProductGraph (a :: tail) B)
            (CTLeafProductColor (a :: tail) colB) :=
          ctLeafProduct_equitable hBeq (a :: tail) hall
        have hBig : IsPairedKDPCForOpposite (CTLeafProductGraph (a :: tail) B)
            (CTLeafProductColor (a :: tail) colB) (a - 1) := by
          simpa [CTLeafProductGraph, CTLeafProductColor] using
            (coleman_thm15 (CompleteTranspositionGraph a □ CTLeafProductGraph tail B)
              (fun x : Equiv.Perm (Fin a) × CTLeafProductVertex tail X =>
                Bool.xor (CompleteTranspositionColor a x.1) (CTLeafProductColor tail colB x.2))
              a (by omega) hTree
              (by simpa [CTLeafProductGraph, CTLeafProductColor] using hEq.1))
        exact prop11c (CTLeafProductGraph (a :: tail) B)
          (CTLeafProductColor (a :: tail) colB) hEq hBig
          (by decide : 1 ≤ 2) (by omega)
          (ctLeafProduct_card_guard a tail ha)

/-- A normalized product of CT graphs with one optional crown leaf is maximally Hamiltonian. -/
theorem ctCrownProduct_maximally_hamiltonian (ranks : List Nat)
    (hall : ∀ a ∈ ranks, 2 ≤ a) :
    IsMH (CTCrownProductGraph ranks) := by
  classical
  have hCrownEven : Even (Fintype.card CrownV) := by
    change Even (Fintype.card (Fin 12))
    norm_num
  exact Or.inr ⟨CTCrownProductColor ranks,
    ctLeafProduct_proper crown_proper ranks hall,
    ctLeafProduct_surjective crown_surjective ranks,
    ctLeafProduct_hamLaceable crown_proper crown_surjective crown_equitable
      crown_hamLaceable hCrownEven ranks hall⟩

private theorem ctCrownProduct_spanning2_laceable (ranks : List Nat)
    (hall : ∀ a ∈ ranks, 2 ≤ a) :
    IsSpanning2DPCOpposite (CTCrownProductGraph ranks) (CTCrownProductColor ranks) := by
  classical
  have hCrownEven : Even (Fintype.card CrownV) := by
    change Even (Fintype.card (Fin 12))
    norm_num
  have hCrownCard : 4 ≤ Fintype.card CrownV := by
    change 4 ≤ Fintype.card (Fin 12)
    norm_num
  exact spanning2_of_paired_two_opposite
    (ctLeafProduct_paired_two crown_proper crown_surjective crown_equitable
      crown_hamLaceable (paired_two_of_spanning2 crown_spanning2_laceable)
      hCrownEven hCrownCard ranks hall)

/-- The normalized product families appearing in Barrus's bipartite classification are MH. -/
def BarrusProductsMaximallyHamiltonian : Prop :=
  IsMH (CTProductGraph []) ∧
  (∀ ranks : List Nat, ranks ≠ [] → (∀ a ∈ ranks, 2 ≤ a) →
    IsMH (CTProductGraph ranks)) ∧
  (∀ ranks : List Nat, (∀ a ∈ ranks, 2 ≤ a) →
    IsMH (CTCrownProductGraph ranks))

theorem barrus_products_maximally_hamiltonian :
    BarrusProductsMaximallyHamiltonian :=
  ⟨empty_ctProduct_mh, ctProduct_maximally_hamiltonian, ctCrownProduct_maximally_hamiltonian⟩

def IsBipartiteRealizationGraph {V : Type u} [Fintype V] [DecidableEq V] (d : V → ℕ) :
    Prop :=
  letI := Classical.decEq (Realization d)
  ∃ col : Realization d → Bool, IsProper2Coloring (RealizationGraph d) col

/-- The realization graph is triangle-free, in the standard graph-theoretic sense. -/
def IsTriangleFreeRealizationGraph {V : Type u} [Fintype V] [DecidableEq V]
    (d : V → ℕ) : Prop :=
  letI := Classical.decEq (Realization d)
  (RealizationGraph d).CliqueFree 3

def IsMaximallyHamiltonianRealizationGraph {V : Type u} [Fintype V] [DecidableEq V]
    (d : V → ℕ) : Prop :=
  letI := Classical.decEq (Realization d)
  IsMH (RealizationGraph d)

/--
**CITED — Barrus.** Michael D. Barrus, *On realization graphs of degree sequences*,
Discrete Mathematics 339 (2016), Theorem 9. Verbatim statement:

> Let `d` be the degree sequence of a simple graph. The following are equivalent:
> (a) `G(d)` is bipartite; (b) `G(d)` is triangle-free; (c) `G(d)` is the Cartesian product of
> transposition graphs and at most one copy of `K_{6,6} − 6K_2`; (d) `d` is the degree sequence of a
> pseudo-split matrogenic graph.

Bibliography key: `Barrus2016`. DOI: `10.1016/j.disc.2016.03.012`.

Local source pin:
`/mnt/c/Users/jbaggett/Zotero/storage/K9GEJRI5/Barrus - 2016 - On realization graphs of degree sequences.pdf`,
SHA-256 `2064be20bab734c24528a1fba0635c0524eb8c6b8a361812326f4e7cc6c88643`.

Formal scope: only the equivalence (a) ↔ (b) is consumed here.  The cited graphicality clause is
not carried in this declaration because, when `Realization d` is empty, both sides hold vacuously.
-/
axiom barrus_theorem9_bipartite_iff_triangleFree {V : Type u} [Fintype V] [DecidableEq V]
    (d : V → ℕ) :
    IsBipartiteRealizationGraph d ↔ IsTriangleFreeRealizationGraph d

/--
**CITED — Barrus.** Michael D. Barrus, *On realization graphs of degree sequences*,
Discrete Mathematics 339 (2016), Theorem 9. Verbatim statement:

> Let `d` be the degree sequence of a simple graph. The following are equivalent:
> (a) `G(d)` is bipartite; (b) `G(d)` is triangle-free; (c) `G(d)` is the Cartesian product of
> transposition graphs and at most one copy of `K_{6,6} − 6K_2`; (d) `d` is the degree sequence of a
> pseudo-split matrogenic graph.

Bibliography key: `Barrus2016`. DOI: `10.1016/j.disc.2016.03.012`.

Local source pin:
`/mnt/c/Users/jbaggett/Zotero/storage/K9GEJRI5/Barrus - 2016 - On realization graphs of degree sequences.pdf`,
SHA-256 `2064be20bab734c24528a1fba0635c0524eb8c6b8a361812326f4e7cc6c88643`.

Formal scope: only the equivalence (a) ↔ (c) is consumed here.  The graphicality hypothesis is
carried explicitly because the normalized CT and crown-product targets are always nonempty.
-/
axiom barrus_theorem9_bipartite_classification {V : Type u} [Fintype V] [DecidableEq V]
    (d : V → ℕ) (hgraphical : Nonempty (Realization d))
    (hbip : IsBipartiteRealizationGraph d) :
    ∃ ranks : List ℕ, (∀ a ∈ ranks, 2 ≤ a) ∧
      (Nonempty (RealizationGraph d ≃g CTProductGraph ranks) ∨
       Nonempty (RealizationGraph d ≃g CTCrownProductGraph ranks))

/-- A realization is determined by its graph field; this low-priority instance keeps the
Theorem-One API self-contained while allowing counting modules to supply their preferred instance. -/
noncomputable instance (priority := 100) theoremOneRealizationFintype
    {V : Type u} [Fintype V] [DecidableEq V] (d : V → ℕ) : Fintype (Realization d) :=
  Fintype.ofInjective Realization.graph (by
    intro G H h
    cases G with
    | mk graphG decG degreeG =>
      cases H with
      | mk graphH decH degreeH =>
        dsimp at h
        subst graphH
        congr
        exact Subsingleton.elim _ _)

/-- Corollary 3.3: every nontrivial bipartite realization graph is spanning-2-laceable. -/
theorem corollary_3_3 {V : Type u} [Fintype V] [DecidableEq V] (d : V → ℕ)
    [Fintype (Realization d)]
    (hbip : IsBipartiteRealizationGraph d) (hcard : 2 ≤ Fintype.card (Realization d)) :
    ∃ col : Realization d → Bool, IsProper2Coloring (RealizationGraph d) col ∧
      IsSpanning2DPCOpposite (RealizationGraph d) col := by
  classical
  have hgraphical : Nonempty (Realization d) :=
    Fintype.card_pos_iff.mp (by omega)
  obtain ⟨ranks, hall, hprod | hcrown⟩ :=
    barrus_theorem9_bipartite_classification d hgraphical hbip
  · obtain ⟨e⟩ := hprod
    have hne : ranks ≠ [] := by
      intro hranks
      subst ranks
      have hcards : Fintype.card (Realization d) = Fintype.card (CTProductVertex []) :=
        Fintype.card_congr e.toEquiv
      simp [CTProductVertex] at hcards
      omega
    let col : Realization d → Bool := fun x => CTProductColor ranks (e x)
    have hproper : IsProper2Coloring (RealizationGraph d) col := by
      intro x y hxy
      exact (ctProduct_equitable_aux ranks hne hall).1 (e x) (e y) (e.map_adj_iff.mpr hxy)
    refine ⟨col, hproper, spanning2_iso_invariant e (fun _ => rfl) ?_⟩
    exact spanning2_of_paired_two_opposite (ctProduct_paired_two_of_ranks ranks hne hall)
  · obtain ⟨e⟩ := hcrown
    let col : Realization d → Bool := fun x => CTCrownProductColor ranks (e x)
    have hproper : IsProper2Coloring (RealizationGraph d) col := by
      intro x y hxy
      exact (ctLeafProduct_proper crown_proper ranks hall) (e x) (e y)
        (e.map_adj_iff.mpr hxy)
    exact ⟨col, hproper, spanning2_iso_invariant e (fun _ => rfl)
      (ctCrownProduct_spanning2_laceable ranks hall)⟩

private theorem connected_of_hamConnected {W : Type*} [DecidableEq W] [Fintype W]
    {G : SimpleGraph W} (hcard : 2 ≤ Fintype.card W) (hconn : IsHamConnected G) :
    G.Connected := by
  letI : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  refine ⟨?_⟩
  intro u v
  by_cases huv : u = v
  · subst v
    exact SimpleGraph.Reachable.refl u
  · obtain ⟨p, -⟩ := hconn u v huv
    exact p.reachable

private theorem connected_of_hamLaceable_surjective {W : Type*} [DecidableEq W]
    {G : SimpleGraph W} {col : W → Bool} (hsurj : Function.Surjective col)
    (hlace : IsHamLaceable G col) : G.Connected := by
  obtain ⟨z, hz⟩ := hsurj false
  letI : Nonempty W := ⟨z⟩
  refine ⟨?_⟩
  intro u v
  by_cases hsame : col u = col v
  · obtain ⟨w, hw⟩ := hsurj (!(col u))
    have huw : col u ≠ col w := by
      rw [hw]
      cases col u <;> decide
    have hvw : col v ≠ col w := by
      rw [← hsame]
      exact huw
    obtain ⟨p, -⟩ := hlace u w huw
    obtain ⟨q, -⟩ := hlace v w hvw
    exact p.reachable.trans q.reachable.symm
  · obtain ⟨p, -⟩ := hlace u v hsame
    exact p.reachable

private theorem surjective_of_proper_connected {W : Type*} [DecidableEq W] [Fintype W]
    {G : SimpleGraph W} {col : W → Bool} (hcard : 2 ≤ Fintype.card W)
    (hconn : G.Connected) (hproper : IsProper2Coloring G col) :
    Function.Surjective col := by
  letI : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨u⟩ := hconn.nonempty
  obtain ⟨v, huv⟩ := hconn.preconnected.exists_adj_of_nontrivial u
  have hne : col u ≠ col v := hproper u v huv
  intro b
  by_cases hb : b = col u
  · exact ⟨u, hb.symm⟩
  · exact ⟨v, by
      cases hcu : col u <;> cases hcv : col v <;> cases hbb : b <;> simp_all⟩

private theorem proper2Coloring_eq_or_flip_of_connected {W : Type*} {G : SimpleGraph W}
    (hconn : G.Connected) {c1 c2 : W → Bool} (h1 : IsProper2Coloring G c1)
    (h2 : IsProper2Coloring G c2) :
    (∀ v, c1 v = c2 v) ∨ (∀ v, c1 v = !(c2 v)) := by
  classical
  have step : ∀ u v, G.Adj u v → ((c1 u = c2 u) ↔ (c1 v = c2 v)) := by
    intro u v huv
    have e1 := h1 u v huv
    have e2 := h2 u v huv
    cases hc1u : c1 u <;> cases hc1v : c1 v <;>
      cases hc2u : c2 u <;> cases hc2v : c2 v <;> simp_all
  have key : ∀ u v, G.Reachable u v → ((c1 u = c2 u) ↔ (c1 v = c2 v)) := by
    intro u v hr
    obtain ⟨w⟩ := hr
    induction w with
    | nil => exact Iff.rfl
    | cons h p ih => exact (step _ _ h).trans ih
  obtain ⟨v0⟩ := hconn.nonempty
  by_cases h0 : c1 v0 = c2 v0
  · left
    intro v
    exact (key v0 v (hconn.preconnected v0 v)).mp h0
  · right
    intro v
    have hv : ¬(c1 v = c2 v) := fun h =>
      h0 ((key v0 v (hconn.preconnected v0 v)).mpr h)
    cases hc2 : c2 v <;> cases hc1 : c1 v <;> simp_all

private theorem spanning2_of_proper2_connected {W : Type*} {G : SimpleGraph W}
    {col col' : W → Bool} (hconn : G.Connected) (hcol : IsProper2Coloring G col)
    (hcol' : IsProper2Coloring G col') (hspan : IsSpanning2DPCOpposite G col) :
    IsSpanning2DPCOpposite G col' := by
  rcases proper2Coloring_eq_or_flip_of_connected hconn hcol' hcol with heq | hflip
  · intro a₁ b₁ a₂ b₂ hc₁ hc₂ ha₁a₂ ha₁b₂ hb₁a₂ hb₁b₂ ha₁b₁ ha₂b₂
    apply hspan a₁ b₁ a₂ b₂
    · rw [← heq a₁, ← heq b₁]
      exact hc₁
    · rw [← heq a₂, ← heq b₂]
      exact hc₂
    · exact ha₁a₂
    · exact ha₁b₂
    · exact hb₁a₂
    · exact hb₁b₂
    · exact ha₁b₁
    · exact ha₂b₂
  · intro a₁ b₁ a₂ b₂ hc₁ hc₂ ha₁a₂ ha₁b₂ hb₁a₂ hb₁b₂ ha₁b₁ ha₂b₂
    apply hspan a₁ b₁ a₂ b₂
    · have h := hc₁
      rw [hflip a₁, hflip b₁] at h
      simpa using h
    · have h := hc₂
      rw [hflip a₂, hflip b₂] at h
      simpa using h
    · exact ha₁a₂
    · exact ha₁b₂
    · exact hb₁a₂
    · exact hb₁b₂
    · exact ha₁b₁
    · exact ha₂b₂

noncomputable instance (priority := 100) theoremOneRealizationDecidableEq
    {V : Type u} [Fintype V] [DecidableEq V] {d : V → ℕ} : DecidableEq (Realization d) :=
  Classical.decEq _

/-- A realization graph satisfying the induction hypothesis is ready for the Cartesian-product
lift: the non-bipartite branch comes from `IsMH`, and Corollary 3.3 supplies the extra paired cover
in the bipartite branch. -/
theorem factorReady_of_realizationGraph {V : Type u} [Fintype V] [DecidableEq V]
    (d : V → ℕ) [Fintype (Realization d)] [DecidableEq (Realization d)]
    (hMH : IsMH (RealizationGraph d)) (hcard : 2 ≤ Fintype.card (Realization d)) :
    FactorReady (RealizationGraph d) := by
  classical
  by_cases hbip : ∃ col, IsProper2Coloring (RealizationGraph d) col
  · rcases hMH with hham | ⟨col, hproper, hsurj, hlace⟩
    · obtain ⟨col, hproper, hspan⟩ := corollary_3_3 d hbip hcard
      have hconn : (RealizationGraph d).Connected :=
        connected_of_hamConnected hcard hham
      have hsurj : Function.Surjective col :=
        surjective_of_proper_connected hcard hconn hproper
      have hlace : IsHamLaceable (RealizationGraph d) col := fun u v huv =>
        hham u v (fun huv' => huv (congrArg col huv'))
      exact Or.inr ⟨col, hproper, hsurj, hlace, hspan⟩
    · obtain ⟨col', hproper', hspan'⟩ := corollary_3_3 d hbip hcard
      have hconn : (RealizationGraph d).Connected :=
        connected_of_hamLaceable_surjective hsurj hlace
      exact Or.inr ⟨col, hproper, hsurj, hlace,
        spanning2_of_proper2_connected hconn hproper' hproper hspan'⟩
  · rcases hMH with hham | ⟨col, hproper, -, -⟩
    · exact Or.inl ⟨hbip, hham⟩
    · exact absurd ⟨col, hproper⟩ hbip

/-- CITED: Barrus 2016, Theorem 9, used in the normalized product-reduction form described
above.  The cited theorem includes the triangle-free iff bipartite equivalence for realization
graphs and the classification of the bipartite cases into the normalized product families.
Consequently, a triangle-free realization graph is maximally Hamiltonian once
`CT_{k₁} □ ... □ CT_{kᵣ}` and
`CT_{k₁} □ ... □ CT_{kᵣ} □ (K_{6,6} - 6K₂)` are known to be maximally Hamiltonian.

This is the classification-to-Hamiltonicity axiom in this file; the separate declaration above
exposes only Theorem 9's bipartite ↔ triangle-free equivalence. -/
theorem barrus_theorem9_triangle_free_classification {V : Type u} [Fintype V] [DecidableEq V]
    (d : V → ℕ)
    (hgraphical : Nonempty (Realization d))
    (htriangleFree : IsTriangleFreeRealizationGraph d)
    (hproducts : BarrusProductsMaximallyHamiltonian) :
    IsMaximallyHamiltonianRealizationGraph d
  := by
  classical
  have hbip : IsBipartiteRealizationGraph d :=
    (barrus_theorem9_bipartite_iff_triangleFree d).mpr htriangleFree
  obtain ⟨ranks, hall, hprod | hcrown⟩ :=
    barrus_theorem9_bipartite_classification d hgraphical hbip
  · obtain ⟨e⟩ := hprod
    by_cases hranks : ranks = []
    · subst ranks
      exact isMH_iso e hproducts.1
    · exact isMH_iso e (hproducts.2.1 ranks hranks hall)
  · obtain ⟨e⟩ := hcrown
    exact isMH_iso e (hproducts.2.2 ranks hall)

/-- Theorem 1.1: every triangle-free realization graph is maximally Hamiltonian. -/
theorem theorem_one {V : Type u} [Fintype V] [DecidableEq V] (d : V → ℕ)
    (htriangleFree : IsTriangleFreeRealizationGraph d) :
    IsMaximallyHamiltonianRealizationGraph d := by
  classical
  by_cases hempty : IsEmpty (Realization d)
  · refine Or.inl ?_
    intro G _ _
    exact (hempty.false G).elim
  · have hgraphical : Nonempty (Realization d) := not_isEmpty_iff.mp hempty
    exact barrus_theorem9_triangle_free_classification d hgraphical htriangleFree
      barrus_products_maximally_hamiltonian

#print axioms theorem_one
#print axioms corollary_3_3
#print axioms factorReady_of_realizationGraph
#print axioms Brualdi.Ledger.brualdi_MH

end Brualdi.RealizationGraph
