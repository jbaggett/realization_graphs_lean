/-
Copyright (c) 2026 Jeffrey S. Baggett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey S. Baggett
-/
/-
  Two-block splice, abstract graph-theory layer.

  This file is deliberately not imported by `BrualdiLean.lean` or by the Brualdi mainline.
  It uses the repository's `HasHamPath` / `IsHamConnected` definitions, but no
  realization-graph definitions.
-/
import BrualdiLean.ColemanDefs

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace Brualdi.Ledger

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/-! ## Basic list-to-Hamilton-path packaging -/

/-- The natural inclusion hom from an induced subgraph to the ambient graph. -/
def induceInclusion (G : SimpleGraph V) (S : Set V) : G.induce S →g G where
  toFun := fun x => x.1
  map_rel' := by
    intro x y hxy
    exact hxy

theorem induceInclusion_injective (G : SimpleGraph V) (S : Set V) :
    Function.Injective (induceInclusion G S) := by
  intro x y hxy
  exact Subtype.ext hxy

theorem walk_support_head?_eq {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    p.support.head? = some u := by
  rw [List.head?_eq_some_head p.support_ne_nil]
  exact congrArg some (SimpleGraph.Walk.head_support p)

theorem walk_support_getLast?_eq {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    p.support.getLast? = some v := by
  rw [List.getLast?_eq_getLast_of_ne_nil p.support_ne_nil]
  exact congrArg some (SimpleGraph.Walk.getLast_support p)

theorem mem_mapped_induce_support {G : SimpleGraph V} {S : Set V}
    {u v : S} (p : (G.induce S).Walk u v) {x : V} :
    x ∈ (p.map (induceInclusion G S)).support ↔
      ∃ hx : x ∈ S, (⟨x, hx⟩ : S) ∈ p.support := by
  rw [SimpleGraph.Walk.support_map]
  constructor
  · intro hx
    rcases List.mem_map.mp hx with ⟨y, hy, hyx⟩
    let hxS : x ∈ S := by rw [← hyx]; exact y.2
    refine ⟨hxS, ?_⟩
    have hy_sub : y = (⟨x, hxS⟩ : S) := Subtype.ext hyx
    simpa [hy_sub] using hy
  · rintro ⟨hxS, hx⟩
    exact List.mem_map.mpr ⟨⟨x, hxS⟩, hx, rfl⟩

theorem mapped_induce_support_subset {G : SimpleGraph V} {S : Set V}
    {u v : S} (p : (G.induce S).Walk u v) {x : V}
    (hx : x ∈ (p.map (induceInclusion G S)).support) : x ∈ S :=
  (mem_mapped_induce_support p).mp hx |>.1

private theorem hasHamPath_of_list {G : SimpleGraph V} (l : List V) {u v : V}
    (hhead : l.head? = some u) (hlast : l.getLast? = some v)
    (hchain : l.IsChain G.Adj) (hnodup : l.Nodup) (hcover : ∀ x : V, x ∈ l) :
    HasHamPath G u v := by
  have hl_ne : l ≠ [] := by
    intro hnil
    rw [hnil] at hhead
    simp at hhead
  let p₀ : G.Walk (l.head hl_ne) (l.getLast hl_ne) :=
    SimpleGraph.Walk.ofSupport l hl_ne hchain
  have hstart : l.head hl_ne = u := by
    have hsome : some (l.head hl_ne) = some u :=
      (List.head?_eq_some_head hl_ne).symm.trans hhead
    exact Option.some.inj hsome
  have hend : l.getLast hl_ne = v := by
    have hsome : some (l.getLast hl_ne) = some v :=
      (List.getLast?_eq_getLast_of_ne_nil hl_ne).symm.trans hlast
    exact Option.some.inj hsome
  let p : G.Walk u v := p₀.copy hstart hend
  refine ⟨p, ?_⟩
  have hp₀_support : p₀.support = l := by simp [p₀]
  have hp₀_path : p₀.IsPath := SimpleGraph.Walk.IsPath.mk' (by
    rw [hp₀_support]
    exact hnodup)
  have hp₀_ham : p₀.IsHamiltonian := hp₀_path.isHamiltonian_of_mem (fun x => by
    rw [hp₀_support]
    exact hcover x)
  intro x
  simpa [p, SimpleGraph.Walk.support_copy] using hp₀_ham x

/-- Splice two disjoint paths across one edge and package the result as a Hamilton path. -/
theorem hamPath_of_two_walk_splice {G : SimpleGraph V} {x a b y : V}
    (P : G.Walk x a) (Q : G.Walk b y)
    (hP : P.IsPath) (hQ : Q.IsPath) (hab : G.Adj a b)
    (hdisj : ∀ z : V, ¬ (z ∈ P.support ∧ z ∈ Q.support))
    (hcover : ∀ z : V, z ∈ P.support ∨ z ∈ Q.support) :
    HasHamPath G x y := by
  let l : List V := P.support ++ Q.support
  refine hasHamPath_of_list l ?_ ?_ ?_ ?_ ?_
  · simp [l, walk_support_head?_eq P]
  · simp [l, List.getLast?_append_of_ne_nil P.support Q.support_ne_nil,
      walk_support_getLast?_eq Q]
  · apply List.IsChain.append P.isChain_adj_support Q.isChain_adj_support
    intro u hu v hv
    rw [walk_support_getLast?_eq P] at hu
    rw [walk_support_head?_eq Q] at hv
    simp at hu hv
    subst u
    subst v
    exact hab
  · change (P.support ++ Q.support).Nodup
    rw [List.nodup_append]
    refine ⟨hP.support_nodup, hQ.support_nodup, ?_⟩
    intro u hu v hv huv
    subst v
    exact hdisj u ⟨hu, hv⟩
  · intro z
    change z ∈ P.support ++ Q.support
    rw [List.mem_append]
    exact hcover z

/-- Splice three pairwise-disjoint paths across two connector edges. -/
theorem hamPath_of_three_walk_splice {G : SimpleGraph V} {x a b c d y : V}
    (P : G.Walk x a) (Q : G.Walk b c) (R : G.Walk d y)
    (hP : P.IsPath) (hQ : Q.IsPath) (hR : R.IsPath)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hPQ : ∀ z : V, ¬ (z ∈ P.support ∧ z ∈ Q.support))
    (hPR : ∀ z : V, ¬ (z ∈ P.support ∧ z ∈ R.support))
    (hQR : ∀ z : V, ¬ (z ∈ Q.support ∧ z ∈ R.support))
    (hcover : ∀ z : V, z ∈ P.support ∨ z ∈ Q.support ∨ z ∈ R.support) :
    HasHamPath G x y := by
  let l : List V := (P.support ++ Q.support) ++ R.support
  refine hasHamPath_of_list l ?_ ?_ ?_ ?_ ?_
  · simp [l, walk_support_head?_eq P]
  · simp [l, walk_support_getLast?_eq R]
  · have hPQchain : (P.support ++ Q.support).IsChain G.Adj := by
      apply List.IsChain.append P.isChain_adj_support Q.isChain_adj_support
      intro u hu v hv
      rw [walk_support_getLast?_eq P] at hu
      rw [walk_support_head?_eq Q] at hv
      simp at hu hv
      subst u
      subst v
      exact hab
    apply List.IsChain.append hPQchain R.isChain_adj_support
    intro u hu v hv
    rw [List.getLast?_append_of_ne_nil P.support Q.support_ne_nil,
      walk_support_getLast?_eq Q] at hu
    rw [walk_support_head?_eq R] at hv
    simp at hu hv
    subst u
    subst v
    exact hcd
  · change ((P.support ++ Q.support) ++ R.support).Nodup
    rw [List.nodup_append]
    refine ⟨?_, hR.support_nodup, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hP.support_nodup, hQ.support_nodup, ?_⟩
      intro u hu v hv huv
      subst v
      exact hPQ u ⟨hu, hv⟩
    · intro u hu v hv huv
      rw [List.mem_append] at hu
      subst v
      rcases hu with hu | hu
      · exact hPR u ⟨hu, hv⟩
      · exact hQR u ⟨hu, hv⟩
  · intro z
    change z ∈ (P.support ++ Q.support) ++ R.support
    rw [List.mem_append, List.mem_append]
    rcases hcover z with hzP | hzQ | hzR
    · exact Or.inl (Or.inl hzP)
    · exact Or.inl (Or.inr hzQ)
    · exact Or.inr hzR

/-! ## P(3) and connector matchings -/

/-- Flexible paired 2-DPC with threshold `τ`, using finite endpoint sets. -/
def FlexiblePaired2DPC (G : SimpleGraph V) (τ : ℕ) : Prop :=
  ∀ X Y : V, X ≠ Y →
    ∀ A₁ A₂ : Finset V,
      (∀ z, z ∈ A₁ → z ≠ X ∧ z ≠ Y) →
      (∀ z, z ∈ A₂ → z ≠ X ∧ z ≠ Y) →
      τ ≤ A₁.card → τ ≤ A₂.card →
      ∃ a₁, a₁ ∈ A₁ ∧ ∃ a₂, a₂ ∈ A₂ ∧ a₁ ≠ a₂ ∧
        ∃ P : G.Walk X a₁, ∃ Q : G.Walk a₂ Y,
          P.IsPath ∧ Q.IsPath ∧
          (∀ z : V, z ∈ P.support ∨ z ∈ Q.support) ∧
          (∀ z : V, ¬ (z ∈ P.support ∧ z ∈ Q.support))

/-- The threshold used by Lemma TS. -/
abbrev FlexiblePaired2DPC3 (G : SimpleGraph V) : Prop :=
  FlexiblePaired2DPC G 3

/-- Five disjoint connector edges between two blocks. -/
structure ConnectorMatching5 (G : SimpleGraph V) (A B : Set V) where
  left : Fin 5 → V
  right : Fin 5 → V
  left_mem : ∀ i, left i ∈ A
  right_mem : ∀ i, right i ∈ B
  adj : ∀ i, G.Adj (left i) (right i)
  left_injective : Function.Injective left
  right_injective : Function.Injective right

namespace ConnectorMatching5

def flip {G : SimpleGraph V} {A B : Set V} (M : ConnectorMatching5 G A B) :
    ConnectorMatching5 G B A where
  left := M.right
  right := M.left
  left_mem := M.right_mem
  right_mem := M.left_mem
  adj := fun i => (M.adj i).symm
  left_injective := M.right_injective
  right_injective := M.left_injective

end ConnectorMatching5

private theorem filter_eq_card_le_one {ι α : Type*} [Fintype ι] [DecidableEq α]
    {f : ι → α} (hf : Function.Injective f) (x : α) :
    ((Finset.univ : Finset ι).filter (fun i => f i = x)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  exact hf (ha.2.trans hb.2.symm)

private theorem connector_bad_card_le_two {G : SimpleGraph V} {A B : Set V}
    (M : ConnectorMatching5 G A B) (X Y : V) :
    ((Finset.univ : Finset (Fin 5)).filter
      (fun i => M.left i = X ∨ M.right i = Y)).card ≤ 2 := by
  classical
  rw [Finset.filter_or]
  calc
    (((Finset.univ : Finset (Fin 5)).filter (fun i => M.left i = X)) ∪
        ((Finset.univ : Finset (Fin 5)).filter (fun i => M.right i = Y))).card
        ≤ ((Finset.univ : Finset (Fin 5)).filter (fun i => M.left i = X)).card +
          ((Finset.univ : Finset (Fin 5)).filter (fun i => M.right i = Y)).card :=
          Finset.card_union_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add
          (filter_eq_card_le_one (ι := Fin 5) M.left_injective X)
          (filter_eq_card_le_one (ι := Fin 5) M.right_injective Y)
    _ = 2 := by norm_num

private theorem connector_exists_avoiding {G : SimpleGraph V} {A B : Set V}
    (M : ConnectorMatching5 G A B) (X Y : V) :
    ∃ i : Fin 5, M.left i ≠ X ∧ M.right i ≠ Y := by
  classical
  let bad : Finset (Fin 5) :=
    (Finset.univ : Finset (Fin 5)).filter (fun i => M.left i = X ∨ M.right i = Y)
  have hbad : bad.card ≤ 2 := by
    simpa [bad] using connector_bad_card_le_two M X Y
  have hbad_lt : bad.card < (Finset.univ : Finset (Fin 5)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  rcases Finset.exists_mem_notMem_of_card_lt_card hbad_lt with ⟨i, _hi, hibad⟩
  refine ⟨i, ?_, ?_⟩
  · intro h
    exact hibad (by simp [bad, h])
  · intro h
    exact hibad (by simp [bad, h])

/-! ## The two-block splice cases -/

/-- Case 1 of Lemma TS: endpoints in different blocks. -/
theorem twoBlock_splice_cross {G : SimpleGraph V} {A B : Set V}
    (hcover : ∀ v : V, v ∈ A ∨ v ∈ B) (hAB : Disjoint A B)
    (hA : IsHamConnected (G.induce A)) (hB : IsHamConnected (G.induce B))
    (M : ConnectorMatching5 G A B)
    {X Y : V} (hX : X ∈ A) (hY : Y ∈ B) :
    HasHamPath G X Y := by
  classical
  rcases connector_exists_avoiding M X Y with ⟨i, hix, hiy⟩
  let XA : A := ⟨X, hX⟩
  let aA : A := ⟨M.left i, M.left_mem i⟩
  let bB : B := ⟨M.right i, M.right_mem i⟩
  let YB : B := ⟨Y, hY⟩
  have hXAa : XA ≠ aA := by
    intro h
    exact hix (congrArg Subtype.val h).symm
  have hbY : bB ≠ YB := by
    intro h
    exact hiy (congrArg Subtype.val h)
  rcases hA XA aA hXAa with ⟨PA, hPAham⟩
  rcases hB bB YB hbY with ⟨PB, hPBham⟩
  let P : G.Walk X (M.left i) := PA.map (induceInclusion G A)
  let Q : G.Walk (M.right i) Y := PB.map (induceInclusion G B)
  refine hamPath_of_two_walk_splice P Q
    (SimpleGraph.Walk.map_isPath_of_injective (induceInclusion_injective G A) hPAham.isPath)
    (SimpleGraph.Walk.map_isPath_of_injective (induceInclusion_injective G B) hPBham.isPath)
    (M.adj i) ?_ ?_
  · intro z hz
    exact (Set.disjoint_left.mp hAB)
      (mapped_induce_support_subset PA hz.1)
      (mapped_induce_support_subset PB hz.2)
  · intro z
    rcases hcover z with hzA | hzB
    · left
      change z ∈ (PA.map (induceInclusion G A)).support
      rw [mem_mapped_induce_support PA]
      exact ⟨hzA, hPAham.mem_support ⟨z, hzA⟩⟩
    · right
      change z ∈ (PB.map (induceInclusion G B)).support
      rw [mem_mapped_induce_support PB]
      exact ⟨hzB, hPBham.mem_support ⟨z, hzB⟩⟩

private def availableLeftEndpoints {G : SimpleGraph V} {A B : Set V}
    (M : ConnectorMatching5 G A B) (X Y : V) : Finset A :=
  ((Finset.univ : Finset (Fin 5)).filter
    (fun i => M.left i ≠ X ∧ M.left i ≠ Y)).image
      (fun i => (⟨M.left i, M.left_mem i⟩ : A))

private theorem left_endpoint_bad_card_le_two {G : SimpleGraph V} {A B : Set V}
    (M : ConnectorMatching5 G A B) (X Y : V) :
    ((Finset.univ : Finset (Fin 5)).filter
      (fun i => M.left i = X ∨ M.left i = Y)).card ≤ 2 := by
  classical
  rw [Finset.filter_or]
  calc
    (((Finset.univ : Finset (Fin 5)).filter (fun i => M.left i = X)) ∪
        ((Finset.univ : Finset (Fin 5)).filter (fun i => M.left i = Y))).card
        ≤ ((Finset.univ : Finset (Fin 5)).filter (fun i => M.left i = X)).card +
          ((Finset.univ : Finset (Fin 5)).filter (fun i => M.left i = Y)).card :=
          Finset.card_union_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add
          (filter_eq_card_le_one (ι := Fin 5) M.left_injective X)
          (filter_eq_card_le_one (ι := Fin 5) M.left_injective Y)
    _ = 2 := by norm_num

private theorem availableLeftEndpoints_card_ge_three {G : SimpleGraph V} {A B : Set V}
    (M : ConnectorMatching5 G A B) (X Y : V) :
    3 ≤ (availableLeftEndpoints M X Y).card := by
  classical
  let good : Finset (Fin 5) :=
    (Finset.univ : Finset (Fin 5)).filter (fun i => M.left i ≠ X ∧ M.left i ≠ Y)
  let bad : Finset (Fin 5) :=
    (Finset.univ : Finset (Fin 5)).filter (fun i => M.left i = X ∨ M.left i = Y)
  have hbad : bad.card ≤ 2 := by
    simpa [bad] using left_endpoint_bad_card_le_two M X Y
  have hsplit : good.card + bad.card = 5 := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 5)))
      (p := fun i => M.left i = X ∨ M.left i = Y)
    have hnot :
        ((Finset.univ : Finset (Fin 5)).filter
          (fun i => ¬ (M.left i = X ∨ M.left i = Y))) = good := by
      ext i
      simp [good, not_or]
    have hbad' :
        ((Finset.univ : Finset (Fin 5)).filter
          (fun i => M.left i = X ∨ M.left i = Y)) = bad := rfl
    rw [hnot, hbad', Finset.card_univ, Fintype.card_fin] at h
    omega
  have himage : (availableLeftEndpoints M X Y).card = good.card := by
    change (((Finset.univ : Finset (Fin 5)).filter
      (fun i => M.left i ≠ X ∧ M.left i ≠ Y)).image
        (fun i => (⟨M.left i, M.left_mem i⟩ : A))).card = good.card
    rw [show ((Finset.univ : Finset (Fin 5)).filter
      (fun i => M.left i ≠ X ∧ M.left i ≠ Y)) = good from rfl]
    exact Finset.card_image_of_injective _ (fun i j hij => by
      exact M.left_injective (congrArg Subtype.val hij))
  omega

private theorem availableLeftEndpoints_avoids {G : SimpleGraph V} {A B : Set V}
    (M : ConnectorMatching5 G A B) {X Y : V} (hX : X ∈ A) (hY : Y ∈ A) {z : A}
    (hz : z ∈ availableLeftEndpoints M X Y) :
    z ≠ (⟨X, hX⟩ : A) ∧ z ≠ (⟨Y, hY⟩ : A) := by
  rcases Finset.mem_image.mp hz with ⟨i, hi, hzi⟩
  rw [Finset.mem_filter] at hi
  constructor
  · intro h
    exact hi.2.1 (by
      exact congrArg Subtype.val (hzi.trans h))
  · intro h
    exact hi.2.2 (by
      exact congrArg Subtype.val (hzi.trans h))

private theorem same_block_splice_from_data {G : SimpleGraph V} {A B : Set V}
    (hcover : ∀ v : V, v ∈ A ∨ v ∈ B) (hAB : Disjoint A B)
    {X Y a₁ a₂ b₁ b₂ : V}
    (hX : X ∈ A) (hY : Y ∈ A) (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (P₁ : (G.induce A).Walk ⟨X, hX⟩ ⟨a₁, ha₁⟩)
    (P₂ : (G.induce A).Walk ⟨a₂, ha₂⟩ ⟨Y, hY⟩)
    (Q : (G.induce B).Walk ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩)
    (hP₁ : P₁.IsPath) (hP₂ : P₂.IsPath) (hQ : Q.IsHamiltonian)
    (hAcover : ∀ z : A, z ∈ P₁.support ∨ z ∈ P₂.support)
    (hAdisj : ∀ z : A, ¬ (z ∈ P₁.support ∧ z ∈ P₂.support))
    (ha₁b₁ : G.Adj a₁ b₁) (hb₂a₂ : G.Adj b₂ a₂) :
    HasHamPath G X Y := by
  let P₁G : G.Walk X a₁ := P₁.map (induceInclusion G A)
  let QG : G.Walk b₁ b₂ := Q.map (induceInclusion G B)
  let P₂G : G.Walk a₂ Y := P₂.map (induceInclusion G A)
  refine hamPath_of_three_walk_splice P₁G QG P₂G
    (SimpleGraph.Walk.map_isPath_of_injective (induceInclusion_injective G A) hP₁)
    (SimpleGraph.Walk.map_isPath_of_injective (induceInclusion_injective G B) hQ.isPath)
    (SimpleGraph.Walk.map_isPath_of_injective (induceInclusion_injective G A) hP₂)
    ha₁b₁ hb₂a₂ ?_ ?_ ?_ ?_
  · intro z hz
    exact (Set.disjoint_left.mp hAB)
      (mapped_induce_support_subset P₁ hz.1)
      (mapped_induce_support_subset Q hz.2)
  · intro z hz
    change z ∈ (P₁.map (induceInclusion G A)).support ∧
      z ∈ (P₂.map (induceInclusion G A)).support at hz
    rw [mem_mapped_induce_support P₁] at hz
    rw [mem_mapped_induce_support P₂] at hz
    rcases hz with ⟨⟨hzA₁, hzP₁⟩, ⟨_hzA₂, hzP₂⟩⟩
    exact hAdisj ⟨z, hzA₁⟩ ⟨hzP₁, by simpa using hzP₂⟩
  · intro z hz
    exact (Set.disjoint_left.mp hAB)
      (mapped_induce_support_subset P₂ hz.2)
      (mapped_induce_support_subset Q hz.1)
  · intro z
    rcases hcover z with hzA | hzB
    · rcases hAcover ⟨z, hzA⟩ with hzP₁ | hzP₂
      · left
        change z ∈ (P₁.map (induceInclusion G A)).support
        rw [mem_mapped_induce_support P₁]
        exact ⟨hzA, hzP₁⟩
      · right
        right
        change z ∈ (P₂.map (induceInclusion G A)).support
        rw [mem_mapped_induce_support P₂]
        exact ⟨hzA, hzP₂⟩
    · right
      left
      change z ∈ (Q.map (induceInclusion G B)).support
      rw [mem_mapped_induce_support Q]
      exact ⟨hzB, hQ.mem_support ⟨z, hzB⟩⟩

/-- Case 2 of Lemma TS: endpoints in the same block. -/
theorem twoBlock_splice_same {G : SimpleGraph V} {A B : Set V}
    (hcover : ∀ v : V, v ∈ A ∨ v ∈ B) (hAB : Disjoint A B)
    (hB : IsHamConnected (G.induce B)) (hAP3 : FlexiblePaired2DPC3 (G.induce A))
    (M : ConnectorMatching5 G A B)
    {X Y : V} (hX : X ∈ A) (hY : Y ∈ A) (hXY : X ≠ Y) :
    HasHamPath G X Y := by
  classical
  let XA : A := ⟨X, hX⟩
  let YA : A := ⟨Y, hY⟩
  let S : Finset A := availableLeftEndpoints M X Y
  have hS₁ : ∀ z, z ∈ S → z ≠ XA ∧ z ≠ YA := by
    intro z hz
    simpa [S, XA, YA] using availableLeftEndpoints_avoids M hX hY hz
  have hScard : 3 ≤ S.card := by
    simpa [S] using availableLeftEndpoints_card_ge_three M X Y
  rcases hAP3 XA YA (by
      intro h
      exact hXY (congrArg Subtype.val h))
      S S hS₁ hS₁ hScard hScard with
    ⟨a₁A, ha₁S, a₂A, ha₂S, ha₁a₂, P₁, P₂, hP₁, hP₂, hAcover, hAdisj⟩
  rcases Finset.mem_image.mp ha₁S with ⟨i, hi, hi_eq⟩
  rcases Finset.mem_image.mp ha₂S with ⟨j, hj, hj_eq⟩
  let b₁B : B := ⟨M.right i, M.right_mem i⟩
  let b₂B : B := ⟨M.right j, M.right_mem j⟩
  have hb₁b₂ : b₁B ≠ b₂B := by
    intro hb
    have hij : i = j := M.right_injective (congrArg Subtype.val hb)
    apply ha₁a₂
    rw [← hi_eq, ← hj_eq, hij]
  rcases hB b₁B b₂B hb₁b₂ with ⟨Q, hQham⟩
  exact same_block_splice_from_data hcover hAB hX hY a₁A.2 a₂A.2
    (M.right_mem i) (M.right_mem j)
    P₁
    P₂
    Q
    hP₁
    hP₂
    hQham
    hAcover
    hAdisj
    (by
      have hval := congrArg Subtype.val hi_eq
      simpa [← hval] using M.adj i)
    (by
      have hval := congrArg Subtype.val hj_eq
      simpa [← hval] using (M.adj j).symm)

/-- Lemma TS: the two-block splice theorem. -/
theorem twoBlock_splice {G : SimpleGraph V} {A B : Set V}
    (hcover : ∀ v : V, v ∈ A ∨ v ∈ B) (hAB : Disjoint A B)
    (hA : IsHamConnected (G.induce A)) (hB : IsHamConnected (G.induce B))
    (hAP3 : FlexiblePaired2DPC3 (G.induce A))
    (hBP3 : FlexiblePaired2DPC3 (G.induce B))
    (M : ConnectorMatching5 G A B) :
    IsHamConnected G := by
  intro X Y hXY
  rcases hcover X with hXA | hXB
  · rcases hcover Y with hYA | hYB
    · exact twoBlock_splice_same hcover hAB hB hAP3 M hXA hYA hXY
    · exact twoBlock_splice_cross hcover hAB hA hB M hXA hYB
  · rcases hcover Y with hYA | hYB
    · exact twoBlock_splice_cross
        (G := G) (A := B) (B := A)
        (fun v => by
          rcases hcover v with hvA | hvB
          · exact Or.inr hvA
          · exact Or.inl hvB)
        hAB.symm hB hA (M.flip) hXB hYA
    · exact twoBlock_splice_same
        (G := G) (A := B) (B := A)
        (fun v => by
          rcases hcover v with hvA | hvB
          · exact Or.inr hvA
          · exact Or.inl hvB)
        hAB.symm hA hBP3 (M.flip) hXB hYB hXY

end Brualdi.Ledger
