/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey S. Baggett
-/

import Realization.PathWalks
import Mathlib.Data.List.ChainOfFn

/-!
# Three path walks for the snake-lemma B3 base case

This file extends `PathWalks` with the C3/B3 path-cover demand and the clean separable
case.  It stays in the same lightweight layer: path-graph walks plus list visit counts.
-/

set_option autoImplicit false

namespace Brualdi.RealizationGraph.PathWalks

open SimpleGraph

/-- A vertex lies in the closed interval spanned by two endpoints of the path. -/
def InEndpointInterval {N : ℕ} (a b v : Fin N) : Prop :=
  min a.val b.val ≤ v.val ∧ v.val ≤ max a.val b.val

instance instDecidableInEndpointInterval {N : ℕ} (a b v : Fin N) :
    Decidable (InEndpointInterval a b v) := by
  unfold InEndpointInterval
  infer_instance

/-- The three endpoint intervals cover the path. -/
def EndpointIntervalsCover₃ {N : ℕ}
    (a₁ b₁ a₂ b₂ a₃ b₃ : Fin N) : Prop :=
  ∀ v : Fin N,
    InEndpointInterval a₁ b₁ v ∨ InEndpointInterval a₂ b₂ v ∨
      InEndpointInterval a₃ b₃ v

/-- The three endpoint intervals are pairwise disjoint. -/
def EndpointIntervalsDisjoint₃ {N : ℕ}
    (a₁ b₁ a₂ b₂ a₃ b₃ : Fin N) : Prop :=
  (∀ v : Fin N, InEndpointInterval a₁ b₁ v → InEndpointInterval a₂ b₂ v → False) ∧
  (∀ v : Fin N, InEndpointInterval a₁ b₁ v → InEndpointInterval a₃ b₃ v → False) ∧
  (∀ v : Fin N, InEndpointInterval a₂ b₂ v → InEndpointInterval a₃ b₃ v → False)

/-- A concrete witness package for the three-walk C3 path demand. -/
structure ThreeWalkCover {N : ℕ} (a₁ b₁ a₂ b₂ a₃ b₃ : Fin N) where
  w₁ : PathWalk N a₁ b₁
  w₂ : PathWalk N a₂ b₂
  w₃ : PathWalk N a₃ b₃
  covers : CoversAll₃ w₁ w₂ w₃
  total_visits_le_three : TotalVisitBound₃ w₁ w₂ w₃ 3
  walk₁_visits_le_two : VisitBound w₁ 2
  walk₂_visits_le_two : VisitBound w₂ 2
  walk₃_visits_le_two : VisitBound w₃ 2

/-- The three-walk cover demand on the path `Fin N`. -/
def ThreeWalkCoverDemand {N : ℕ} (a₁ b₁ a₂ b₂ a₃ b₃ : Fin N) : Prop :=
  Nonempty (ThreeWalkCover a₁ b₁ a₂ b₂ a₃ b₃)

namespace Straight

private def intervalVerticesLE {N : ℕ} (a b : Fin N) (h : a.val ≤ b.val) : List (Fin N) :=
  List.ofFn fun t : Fin (b.val - a.val).succ =>
    ⟨a.val + t.val, by
      have ht : t.val < (b.val - a.val).succ := t.isLt
      omega⟩

private theorem intervalVerticesLE_ne_nil {N : ℕ} (a b : Fin N) (h : a.val ≤ b.val) :
    intervalVerticesLE a b h ≠ [] := by
  simp [intervalVerticesLE]

private theorem intervalVerticesLE_head {N : ℕ} (a b : Fin N) (h : a.val ≤ b.val) :
    (intervalVerticesLE a b h).head (intervalVerticesLE_ne_nil a b h) = a := by
  simp [intervalVerticesLE]

private theorem intervalVerticesLE_getLast {N : ℕ} (a b : Fin N) (h : a.val ≤ b.val) :
    (intervalVerticesLE a b h).getLast (intervalVerticesLE_ne_nil a b h) = b := by
  change (List.ofFn (fun t : Fin (b.val - a.val).succ =>
    (⟨a.val + t.val, by
      have ht : t.val < (b.val - a.val).succ := t.isLt
      omega⟩ : Fin N))).getLast _ = b
  rw [List.getLast_ofFn_succ]
  apply Fin.ext
  simp
  omega

private theorem intervalVerticesLE_chain {N : ℕ} (a b : Fin N) (h : a.val ≤ b.val) :
    (intervalVerticesLE a b h).IsChain (SimpleGraph.pathGraph N).Adj := by
  rw [intervalVerticesLE, List.isChain_ofFn]
  intro i hi
  rw [SimpleGraph.pathGraph_adj]
  left
  simp
  omega

private def upwardWalk {N : ℕ} (a b : Fin N) (h : a.val ≤ b.val) : PathWalk N a b :=
  (SimpleGraph.Walk.ofSupport
      (intervalVerticesLE a b h)
      (intervalVerticesLE_ne_nil a b h)
      (intervalVerticesLE_chain a b h)).copy
    (intervalVerticesLE_head a b h)
    (intervalVerticesLE_getLast a b h)

private theorem upwardWalk_vertices {N : ℕ} (a b : Fin N) (h : a.val ≤ b.val) :
    (upwardWalk a b h).vertices = intervalVerticesLE a b h := by
  simp [upwardWalk, PathWalk.vertices]

private theorem intervalVerticesLE_mem_iff {N : ℕ} {a b v : Fin N} (h : a.val ≤ b.val) :
    v ∈ intervalVerticesLE a b h ↔ a.val ≤ v.val ∧ v.val ≤ b.val := by
  rw [intervalVerticesLE, List.mem_ofFn']
  constructor
  · rintro ⟨t, ht⟩
    have hv : v.val = a.val + t.val := by
      simpa using (congrArg Fin.val ht).symm
    constructor <;> omega
  · rintro ⟨hav, hvb⟩
    refine ⟨⟨v.val - a.val, by omega⟩, ?_⟩
    apply Fin.ext
    simp
    omega

private theorem intervalVerticesLE_nodup {N : ℕ} (a b : Fin N) (h : a.val ≤ b.val) :
    (intervalVerticesLE a b h).Nodup := by
  rw [intervalVerticesLE]
  exact List.nodup_ofFn_ofInjective (by
    intro x y hxy
    apply Fin.ext
    have := congrArg Fin.val hxy
    simp at this
    omega)

private theorem intervalVerticesLE_count {N : ℕ} (a b v : Fin N) (h : a.val ≤ b.val) :
    (intervalVerticesLE a b h).count v =
      if a.val ≤ v.val ∧ v.val ≤ b.val then 1 else 0 := by
  by_cases hv : a.val ≤ v.val ∧ v.val ≤ b.val
  · rw [if_pos hv]
    exact List.count_eq_one_of_mem (intervalVerticesLE_nodup a b h)
      ((intervalVerticesLE_mem_iff h).mpr hv)
  · rw [if_neg hv]
    exact List.count_eq_zero_of_not_mem (fun hmem => hv ((intervalVerticesLE_mem_iff h).mp hmem))

private theorem upwardWalk_visits {N : ℕ} (a b v : Fin N) (h : a.val ≤ b.val) :
    visits (upwardWalk a b h) v =
      if a.val ≤ v.val ∧ v.val ≤ b.val then 1 else 0 := by
  rw [visits, upwardWalk_vertices]
  exact intervalVerticesLE_count a b v h

end Straight

/-- The monotone straight walk between two vertices of a path. -/
def straightWalk {N : ℕ} (a b : Fin N) : PathWalk N a b :=
  if h : a.val ≤ b.val then
    Straight.upwardWalk a b h
  else
    (Straight.upwardWalk b a (Nat.le_of_not_ge h)).reverse

/--
The straight walk visits exactly the closed interval between its endpoints, and visits each
such vertex once.
-/
theorem straightWalk_visits {N : ℕ} (a b v : Fin N) :
    visits (straightWalk a b) v =
      if InEndpointInterval a b v then 1 else 0 := by
  unfold straightWalk
  by_cases h : a.val ≤ b.val
  · rw [dif_pos h, Straight.upwardWalk_visits]
    by_cases hv : a.val ≤ v.val ∧ v.val ≤ b.val
    · simp [InEndpointInterval, h, hv]
    · simp [InEndpointInterval, h]
  · rw [dif_neg h]
    have hba : b.val ≤ a.val := Nat.le_of_not_ge h
    rw [visits, PathWalk.vertices, SimpleGraph.Walk.support_reverse]
    have hcount_reverse :
        (Straight.upwardWalk b a hba).vertices.reverse.count v =
          (Straight.upwardWalk b a hba).vertices.count v := by
      exact (List.reverse_perm (Straight.upwardWalk b a hba).vertices).count_eq v
    rw [hcount_reverse]
    change visits (Straight.upwardWalk b a hba) v =
      if InEndpointInterval a b v then 1 else 0
    rw [Straight.upwardWalk_visits]
    by_cases hv : b.val ≤ v.val ∧ v.val ≤ a.val
    · simp [InEndpointInterval, hba, hv]
    · simp [InEndpointInterval, hba]

theorem straightWalk_covers_iff {N : ℕ} (a b v : Fin N) :
    Covers (straightWalk a b) v ↔ InEndpointInterval a b v := by
  rw [Covers, ← List.count_pos_iff, ← visits, straightWalk_visits]
  by_cases h : InEndpointInterval a b v <;> simp [h]

theorem straightWalk_visitBound_two {N : ℕ} (a b : Fin N) :
    VisitBound (straightWalk a b) 2 := by
  intro v
  rw [straightWalk_visits]
  by_cases h : InEndpointInterval a b v <;> simp [h]

theorem straightWalk_visitBound_one {N : ℕ} (a b : Fin N) :
    VisitBound (straightWalk a b) 1 := by
  intro v
  rw [straightWalk_visits]
  by_cases h : InEndpointInterval a b v <;> simp [h]

private theorem straightWalk_visit_eq_zero_of_not_interval {N : ℕ} {a b v : Fin N}
    (h : ¬ InEndpointInterval a b v) : visits (straightWalk a b) v = 0 := by
  rw [straightWalk_visits, if_neg h]

private theorem straightWalk_visit_eq_one_of_interval {N : ℕ} {a b v : Fin N}
    (h : InEndpointInterval a b v) : visits (straightWalk a b) v = 1 := by
  rw [straightWalk_visits, if_pos h]

private theorem separable_total_visits_le_one_at {N : ℕ}
    {a₁ b₁ a₂ b₂ a₃ b₃ v : Fin N}
    (hdisj : EndpointIntervalsDisjoint₃ a₁ b₁ a₂ b₂ a₃ b₃) :
    visits (straightWalk a₁ b₁) v + visits (straightWalk a₂ b₂) v +
        visits (straightWalk a₃ b₃) v ≤ 1 := by
  rcases hdisj with ⟨h12, h13, h23⟩
  by_cases h1 : InEndpointInterval a₁ b₁ v
  · have h2 : ¬ InEndpointInterval a₂ b₂ v := fun h => h12 v h1 h
    have h3 : ¬ InEndpointInterval a₃ b₃ v := fun h => h13 v h1 h
    simp [straightWalk_visit_eq_one_of_interval h1,
      straightWalk_visit_eq_zero_of_not_interval h2,
      straightWalk_visit_eq_zero_of_not_interval h3]
  · by_cases h2 : InEndpointInterval a₂ b₂ v
    · have h3 : ¬ InEndpointInterval a₃ b₃ v := fun h => h23 v h2 h
      simp [straightWalk_visit_eq_zero_of_not_interval h1,
        straightWalk_visit_eq_one_of_interval h2,
        straightWalk_visit_eq_zero_of_not_interval h3]
    · by_cases h3 : InEndpointInterval a₃ b₃ v
      · simp [straightWalk_visit_eq_zero_of_not_interval h1,
          straightWalk_visit_eq_zero_of_not_interval h2,
          straightWalk_visit_eq_one_of_interval h3]
      · simp [straightWalk_visit_eq_zero_of_not_interval h1,
          straightWalk_visit_eq_zero_of_not_interval h2,
          straightWalk_visit_eq_zero_of_not_interval h3]

/--
Separable B3: if the three endpoint intervals cover the path and are pairwise disjoint, the
three straight interval walks satisfy the C3 demand.  The total visit count is in fact at most
`1` at each vertex, hence also at most `2` as required by the separable bulk case.
-/
theorem B3_separable {N : ℕ} {a₁ b₁ a₂ b₂ a₃ b₃ : Fin N}
    (hcover : EndpointIntervalsCover₃ a₁ b₁ a₂ b₂ a₃ b₃)
    (hdisj : EndpointIntervalsDisjoint₃ a₁ b₁ a₂ b₂ a₃ b₃) :
    ∃ w₁ : PathWalk N a₁ b₁, ∃ w₂ : PathWalk N a₂ b₂, ∃ w₃ : PathWalk N a₃ b₃,
      CoversAll₃ w₁ w₂ w₃ ∧ TotalVisitBound₃ w₁ w₂ w₃ 2 ∧
        VisitBound w₁ 2 ∧ VisitBound w₂ 2 ∧ VisitBound w₃ 2 := by
  refine ⟨straightWalk a₁ b₁, straightWalk a₂ b₂, straightWalk a₃ b₃, ?_⟩
  constructor
  · intro v
    rcases hcover v with h | h | h
    · exact Or.inl ((straightWalk_covers_iff a₁ b₁ v).mpr h)
    · exact Or.inr (Or.inl ((straightWalk_covers_iff a₂ b₂ v).mpr h))
    · exact Or.inr (Or.inr ((straightWalk_covers_iff a₃ b₃ v).mpr h))
  constructor
  · intro v
    exact le_trans (separable_total_visits_le_one_at (v := v) hdisj) (by norm_num)
  exact ⟨straightWalk_visitBound_two a₁ b₁, straightWalk_visitBound_two a₂ b₂,
    straightWalk_visitBound_two a₃ b₃⟩

/-- The separable branch as an inhabitant of the three-walk B3 demand. -/
theorem B3_separable_demand {N : ℕ} {a₁ b₁ a₂ b₂ a₃ b₃ : Fin N}
    (hcover : EndpointIntervalsCover₃ a₁ b₁ a₂ b₂ a₃ b₃)
    (hdisj : EndpointIntervalsDisjoint₃ a₁ b₁ a₂ b₂ a₃ b₃) :
    ThreeWalkCoverDemand a₁ b₁ a₂ b₂ a₃ b₃ := by
  rcases B3_separable (N := N) hcover hdisj with
    ⟨w₁, w₂, w₃, hcov, htotal₂, hb₁, hb₂, hb₃⟩
  refine ⟨⟨w₁, w₂, w₃, hcov, ?_, hb₁, hb₂, hb₃⟩⟩
  intro v
  exact le_trans (htotal₂ v) (by norm_num)

/-! ## Reduction skeleton for the non-separable B3 branches -/

/--
Reduction skeleton: if two walks are already supplied with total visit cap `2`, a third straight
walk whose interval avoids every vertex where the two-walk construction uses two visits upgrades
the pair to a three-walk cover with total cap `3`.
-/
theorem B3_reduction_from_two_walks {N : ℕ}
    {a₁ b₁ a₂ b₂ a₃ b₃ : Fin N}
    (w₁ : PathWalk N a₁ b₁) (w₂ : PathWalk N a₂ b₂)
    (hcover₂ : ∀ v : Fin N,
      Covers w₁ v ∨ Covers w₂ v ∨ InEndpointInterval a₃ b₃ v)
    (htotal₂ : TotalVisitBound₂ w₁ w₂ 2)
    (havoid : ∀ v : Fin N, InEndpointInterval a₃ b₃ v →
      visits w₁ v + visits w₂ v ≤ 2)
    (hb₁ : VisitBound w₁ 2) (hb₂ : VisitBound w₂ 2) :
    ThreeWalkCoverDemand a₁ b₁ a₂ b₂ a₃ b₃ := by
  let w₃ : PathWalk N a₃ b₃ := straightWalk a₃ b₃
  refine ⟨⟨w₁, w₂, w₃, ?_, ?_, hb₁, hb₂, straightWalk_visitBound_two a₃ b₃⟩⟩
  · intro v
    rcases hcover₂ v with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ((straightWalk_covers_iff a₃ b₃ v).mpr h))
  · intro v
    by_cases hv : InEndpointInterval a₃ b₃ v
    · rw [straightWalk_visit_eq_one_of_interval hv]
      have hpair := havoid v hv
      omega
    · rw [straightWalk_visit_eq_zero_of_not_interval hv]
      have hpair := htotal₂ v
      omega

/--
Concentration skeleton: when the third prescribed pair is concentrated at one vertex, the
zero-length walk can absorb that confined segment.  The remaining two walks must already cover
the rest within total cap `2`, and must leave one unit of capacity at the concentration vertex.
-/
theorem B3_concentrated_third_from_two_walks {N : ℕ}
    {a₁ b₁ a₂ b₂ c : Fin N}
    (w₁ : PathWalk N a₁ b₁) (w₂ : PathWalk N a₂ b₂)
    (hcover₂ : ∀ v : Fin N, Covers w₁ v ∨ Covers w₂ v ∨ v = c)
    (htotal₂ : TotalVisitBound₂ w₁ w₂ 2)
    (hb₁ : VisitBound w₁ 2) (hb₂ : VisitBound w₂ 2) :
    ThreeWalkCoverDemand a₁ b₁ a₂ b₂ c c := by
  refine ⟨⟨w₁, w₂, nil c, ?_, ?_, hb₁, hb₂, ?_⟩⟩
  · intro v
    rcases hcover₂ v with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by simpa [Covers] using h))
  · intro v
    by_cases hv : v = c
    · subst v
      rw [visits_nil_self]
      have hpair := htotal₂ c
      omega
    · rw [visits_nil_ne hv]
      have hpair := htotal₂ v
      omega
  · intro v
    by_cases hv : v = c
    · subst v
      simp [visits_nil_self]
    · simp [visits_nil_ne hv]

end Brualdi.RealizationGraph.PathWalks
