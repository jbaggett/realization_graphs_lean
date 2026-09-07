/-
Copyright (c) 2026 Jeffrey S. Baggett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey S. Baggett
-/
import BrualdiLean.ColemanDefs
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.Count
import Mathlib.Tactic

/-!
# Path walks for the snake-lemma base checks

This file deliberately lives under `RealizationGraph` but imports only the definitions layer
(`ColemanDefs`) and mathlib graph-walk infrastructure.  It does not import `Ledger` or the
`brualdi_MH` theorem.

The path-base walk model is mathlib's walk type in `SimpleGraph.pathGraph N`.  Its `support` is
the requested list of visited vertices; consecutive support entries are adjacent path vertices,
and the zero-length walk is `Walk.nil`, whose support is the singleton list.

The corrected B1 distinct-end statement and the printed B2 coincidence table from
`next_paper/draft_snake_lemma.md` are formalized below.  Rows 0--7 have explicit constructions;
row 8 is ruled out for every path and every interior common anchor.  The original `P₃` witness is
retained as a concrete sanity check for the general obstruction.
-/

set_option autoImplicit false

namespace Brualdi.RealizationGraph.PathWalks

open SimpleGraph
open Brualdi.Ledger

/-- A walk on the path graph `P_N`, from `i` to `j`. -/
abbrev PathWalk (N : ℕ) (i j : Fin N) : Type :=
  (SimpleGraph.pathGraph N).Walk i j

/-- The list of vertices visited by a path walk. -/
abbrev PathWalk.vertices {N : ℕ} {i j : Fin N} (w : PathWalk N i j) : List (Fin N) :=
  w.support

/-- The number of times a path walk visits a vertex. -/
def visits {N : ℕ} {i j : Fin N} (w : PathWalk N i j) (v : Fin N) : ℕ :=
  w.vertices.count v

@[simp]
theorem visits_copy {N : ℕ} {i j i' j' : Fin N} (w : PathWalk N i j)
    (hi : i = i') (hj : j = j') (v : Fin N) :
    visits (w.copy hi hj) v = visits w v := by
  simp [visits]

/-- A path walk covers a vertex when it occurs in its support list. -/
def Covers {N : ℕ} {i j : Fin N} (w : PathWalk N i j) (v : Fin N) : Prop :=
  v ∈ w.vertices

/-- A path walk covers every vertex of `P_N`. -/
def CoversAll {N : ℕ} {i j : Fin N} (w : PathWalk N i j) : Prop :=
  ∀ v : Fin N, Covers w v

/-- The union of two path walks covers every vertex of `P_N`. -/
def CoversAll₂ {N : ℕ} {i₁ j₁ i₂ j₂ : Fin N}
    (w₁ : PathWalk N i₁ j₁) (w₂ : PathWalk N i₂ j₂) : Prop :=
  ∀ v : Fin N, Covers w₁ v ∨ Covers w₂ v

/-- The union of three path walks covers every vertex of `P_N`. -/
def CoversAll₃ {N : ℕ} {i₁ j₁ i₂ j₂ i₃ j₃ : Fin N}
    (w₁ : PathWalk N i₁ j₁) (w₂ : PathWalk N i₂ j₂) (w₃ : PathWalk N i₃ j₃) : Prop :=
  ∀ v : Fin N, Covers w₁ v ∨ Covers w₂ v ∨ Covers w₃ v

/-- A per-walk visit cap. -/
def VisitBound {N : ℕ} {i j : Fin N} (w : PathWalk N i j) (k : ℕ) : Prop :=
  ∀ v : Fin N, visits w v ≤ k

/-- A combined visit cap for two walks. -/
def TotalVisitBound₂ {N : ℕ} {i₁ j₁ i₂ j₂ : Fin N}
    (w₁ : PathWalk N i₁ j₁) (w₂ : PathWalk N i₂ j₂) (k : ℕ) : Prop :=
  ∀ v : Fin N, visits w₁ v + visits w₂ v ≤ k

/-- A combined visit cap for three walks. -/
def TotalVisitBound₃ {N : ℕ} {i₁ j₁ i₂ j₂ i₃ j₃ : Fin N}
    (w₁ : PathWalk N i₁ j₁) (w₂ : PathWalk N i₂ j₂) (w₃ : PathWalk N i₃ j₃)
    (k : ℕ) : Prop :=
  ∀ v : Fin N, visits w₁ v + visits w₂ v + visits w₃ v ≤ k

/-- The zero-length path walk at a vertex. -/
def nil {N : ℕ} (v : Fin N) : PathWalk N v v :=
  SimpleGraph.Walk.nil

@[simp]
theorem vertices_nil {N : ℕ} (v : Fin N) :
    (nil v).vertices = [v] :=
  rfl

@[simp]
theorem visits_nil_self {N : ℕ} (v : Fin N) :
    visits (nil v) v = 1 := by
  simp [visits]

@[simp]
theorem visits_nil_ne {N : ℕ} {v w : Fin N} (h : w ≠ v) :
    visits (nil v) w = 0 := by
  rw [visits, vertices_nil]
  exact List.count_eq_zero_of_not_mem (by simpa using h)

@[simp]
theorem covers_nil_iff {N : ℕ} (v w : Fin N) :
    Covers (nil v) w ↔ w = v := by
  simp [Covers]

/-! ## Straight path walks and the corrected B1 statement -/

/-- A vertex lies in the closed interval spanned by two endpoints of the path. -/
def PWInEndpointInterval {N : ℕ} (a b v : Fin N) : Prop :=
  min a.val b.val ≤ v.val ∧ v.val ≤ max a.val b.val

instance instDecidablePWInEndpointInterval {N : ℕ} (a b v : Fin N) :
    Decidable (PWInEndpointInterval a b v) := by
  unfold PWInEndpointInterval
  infer_instance

namespace StraightLocal

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

end StraightLocal

/-- The monotone straight walk between two vertices of a path. -/
def pwStraightWalk {N : ℕ} (a b : Fin N) : PathWalk N a b :=
  if h : a.val ≤ b.val then
    StraightLocal.upwardWalk a b h
  else
    (StraightLocal.upwardWalk b a (Nat.le_of_not_ge h)).reverse

theorem pwStraightWalk_visits {N : ℕ} (a b v : Fin N) :
    visits (pwStraightWalk a b) v =
      if PWInEndpointInterval a b v then 1 else 0 := by
  unfold pwStraightWalk
  by_cases h : a.val ≤ b.val
  · rw [dif_pos h, StraightLocal.upwardWalk_visits]
    by_cases hv : a.val ≤ v.val ∧ v.val ≤ b.val
    · simp [PWInEndpointInterval, h, hv]
    · simp [PWInEndpointInterval, h]
  · rw [dif_neg h]
    have hba : b.val ≤ a.val := Nat.le_of_not_ge h
    rw [visits, PathWalk.vertices, SimpleGraph.Walk.support_reverse]
    have hcount_reverse :
        (StraightLocal.upwardWalk b a hba).vertices.reverse.count v =
          (StraightLocal.upwardWalk b a hba).vertices.count v := by
      exact (List.reverse_perm (StraightLocal.upwardWalk b a hba).vertices).count_eq v
    rw [hcount_reverse]
    change visits (StraightLocal.upwardWalk b a hba) v =
      if PWInEndpointInterval a b v then 1 else 0
    rw [StraightLocal.upwardWalk_visits]
    by_cases hv : b.val ≤ v.val ∧ v.val ≤ a.val
    · simp [PWInEndpointInterval, hba, hv]
    · simp [PWInEndpointInterval, hba]

theorem pwStraightWalk_covers_iff {N : ℕ} (a b v : Fin N) :
    Covers (pwStraightWalk a b) v ↔ PWInEndpointInterval a b v := by
  rw [Covers, ← List.count_pos_iff, ← visits, pwStraightWalk_visits]
  by_cases h : PWInEndpointInterval a b v <;> simp [h]

private theorem visits_append_le {N : ℕ} {a b c : Fin N}
    (p : PathWalk N a b) (q : PathWalk N b c) (v : Fin N) :
    visits (p.append q) v ≤ visits p v + visits q v := by
  unfold visits PathWalk.vertices
  rw [SimpleGraph.Walk.support_append]
  simp only [List.count_append]
  have htail : q.support.tail.count v ≤ q.support.count v := by
    exact List.Sublist.count_le v (List.tail_sublist q.support)
  omega

private theorem visits_append_append_le {N : ℕ} {a b c d : Fin N}
    (p : PathWalk N a b) (q : PathWalk N b c) (r : PathWalk N c d) (v : Fin N) :
    visits ((p.append q).append r) v ≤ visits p v + visits q v + visits r v := by
  have h₁ := visits_append_le (p.append q) r v
  have h₂ := visits_append_le p q v
  omega

private def pathFirst {N : ℕ} (hN : 0 < N) : Fin N :=
  ⟨0, hN⟩

private def pathLast {N : ℕ} (hN : 0 < N) : Fin N :=
  ⟨N - 1, by omega⟩

/-- B1 walk for `i ≤ j`: `i → 0 → N-1 → j`. -/
def B1ForwardWalk {N : ℕ} (hN : 0 < N) (i j : Fin N) : PathWalk N i j :=
  ((pwStraightWalk i (pathFirst hN)).append
    (pwStraightWalk (pathFirst hN) (pathLast hN))).append
      (pwStraightWalk (pathLast hN) j)

/-- B1 walk for `j ≤ i`: `i → N-1 → 0 → j`. -/
def B1BackwardWalk {N : ℕ} (hN : 0 < N) (i j : Fin N) : PathWalk N i j :=
  ((pwStraightWalk i (pathLast hN)).append
    (pwStraightWalk (pathLast hN) (pathFirst hN))).append
      (pwStraightWalk (pathFirst hN) j)

private theorem first_last_interval_all {N : ℕ} (hN : 0 < N) (v : Fin N) :
    PWInEndpointInterval (pathFirst hN) (pathLast hN) v := by
  simp [PWInEndpointInterval, pathFirst, pathLast]
  omega

private theorem last_first_interval_all {N : ℕ} (hN : 0 < N) (v : Fin N) :
    PWInEndpointInterval (pathLast hN) (pathFirst hN) v := by
  simp [PWInEndpointInterval, pathFirst, pathLast]
  omega

theorem B1ForwardWalk_coversAll {N : ℕ} (hN : 0 < N) (i j : Fin N) :
    CoversAll (B1ForwardWalk hN i j) := by
  intro v
  unfold B1ForwardWalk
  have hmid : Covers (pwStraightWalk (pathFirst hN) (pathLast hN)) v :=
    (pwStraightWalk_covers_iff (pathFirst hN) (pathLast hN) v).mpr
      (first_last_interval_all hN v)
  exact (SimpleGraph.Walk.mem_support_append_iff _ _).mpr
    (Or.inl ((SimpleGraph.Walk.mem_support_append_iff _ _).mpr (Or.inr hmid)))

theorem B1BackwardWalk_coversAll {N : ℕ} (hN : 0 < N) (i j : Fin N) :
    CoversAll (B1BackwardWalk hN i j) := by
  intro v
  unfold B1BackwardWalk
  have hmid : Covers (pwStraightWalk (pathLast hN) (pathFirst hN)) v :=
    (pwStraightWalk_covers_iff (pathLast hN) (pathFirst hN) v).mpr
      (last_first_interval_all hN v)
  exact (SimpleGraph.Walk.mem_support_append_iff _ _).mpr
    (Or.inl ((SimpleGraph.Walk.mem_support_append_iff _ _).mpr (Or.inr hmid)))

theorem B1ForwardWalk_visitBound_two_of_lt {N : ℕ} (hN : 0 < N)
    {i j : Fin N} (hij : i.val < j.val) :
    VisitBound (B1ForwardWalk hN i j) 2 := by
  intro v
  unfold B1ForwardWalk
  have hle := visits_append_append_le
    (pwStraightWalk i (pathFirst hN))
    (pwStraightWalk (pathFirst hN) (pathLast hN))
    (pwStraightWalk (pathLast hN) j) v
  rw [pwStraightWalk_visits, pwStraightWalk_visits, pwStraightWalk_visits] at hle
  have hsum :
      (if PWInEndpointInterval i (pathFirst hN) v then 1 else 0) +
          (if PWInEndpointInterval (pathFirst hN) (pathLast hN) v then 1 else 0) +
            (if PWInEndpointInterval (pathLast hN) j v then 1 else 0) ≤ 2 := by
    simp [PWInEndpointInterval, pathFirst, pathLast]
    split_ifs <;> omega
  exact le_trans hle hsum

theorem B1BackwardWalk_visitBound_two_of_gt {N : ℕ} (hN : 0 < N)
    {i j : Fin N} (hji : j.val < i.val) :
    VisitBound (B1BackwardWalk hN i j) 2 := by
  intro v
  unfold B1BackwardWalk
  have hle := visits_append_append_le
    (pwStraightWalk i (pathLast hN))
    (pwStraightWalk (pathLast hN) (pathFirst hN))
    (pwStraightWalk (pathFirst hN) j) v
  rw [pwStraightWalk_visits, pwStraightWalk_visits, pwStraightWalk_visits] at hle
  have hsum :
      (if PWInEndpointInterval i (pathLast hN) v then 1 else 0) +
          (if PWInEndpointInterval (pathLast hN) (pathFirst hN) v then 1 else 0) +
            (if PWInEndpointInterval (pathFirst hN) j v then 1 else 0) ≤ 2 := by
    simp [PWInEndpointInterval, pathFirst, pathLast]
    split_ifs <;> omega
  exact le_trans hle hsum

/-- Corrected B1, distinct-end version: one path walk covers the row path with visits `≤ 2`. -/
theorem B1_distinct_ends {N : ℕ} (hN : 0 < N) {i j : Fin N} (hij : i ≠ j) :
    ∃ w : PathWalk N i j, CoversAll w ∧ VisitBound w 2 := by
  have hval : i.val ≠ j.val := by
    intro h
    exact hij (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · exact ⟨B1ForwardWalk hN i j, B1ForwardWalk_coversAll hN i j,
      B1ForwardWalk_visitBound_two_of_lt hN hlt⟩
  · exact ⟨B1BackwardWalk hN i j, B1BackwardWalk_coversAll hN i j,
      B1BackwardWalk_visitBound_two_of_gt hN hgt⟩

/-- Corrected B1, equal-end convention: the shared start/end is allowed three visits. -/
theorem B1_equal_ends_visitBound_three {N : ℕ} (hN : 0 < N) (i : Fin N) :
    ∃ w : PathWalk N i i, CoversAll w ∧ VisitBound w 3 := by
  refine ⟨B1ForwardWalk hN i i, B1ForwardWalk_coversAll hN i i, ?_⟩
  intro v
  unfold B1ForwardWalk
  have hle := visits_append_append_le
    (pwStraightWalk i (pathFirst hN))
    (pwStraightWalk (pathFirst hN) (pathLast hN))
    (pwStraightWalk (pathLast hN) i) v
  rw [pwStraightWalk_visits, pwStraightWalk_visits, pwStraightWalk_visits] at hle
  have hsum :
      (if PWInEndpointInterval i (pathFirst hN) v then 1 else 0) +
          (if PWInEndpointInterval (pathFirst hN) (pathLast hN) v then 1 else 0) +
            (if PWInEndpointInterval (pathLast hN) i v then 1 else 0) ≤ 3 := by
    split_ifs <;> omega
  exact le_trans hle hsum

/-! ## The explicit B2 coincidence table

The row numbers and constructions in this section are those of
`next_paper/draft_snake_lemma.md`, with Lean's zero-based `Fin N` vertices in place of the
paper's rows `1, …, N`.  A construction is a pair whose type already records its stated ends.
-/

/-- A proof-independent choice of the printed distinct-end B1 walk. -/
def B1Walk {N : ℕ} (hN : 0 < N) (i j : Fin N) : PathWalk N i j :=
  if i.val < j.val then B1ForwardWalk hN i j else B1BackwardWalk hN i j

theorem B1Walk_coversAll {N : ℕ} (hN : 0 < N) (i j : Fin N) :
    CoversAll (B1Walk hN i j) := by
  unfold B1Walk
  split_ifs
  · exact B1ForwardWalk_coversAll hN i j
  · exact B1BackwardWalk_coversAll hN i j

theorem B1Walk_visitBound_two_of_ne {N : ℕ} (hN : 0 < N) {i j : Fin N}
    (hij : i ≠ j) : VisitBound (B1Walk hN i j) 2 := by
  unfold B1Walk
  split_ifs with hlt
  · exact B1ForwardWalk_visitBound_two_of_lt hN hlt
  · apply B1BackwardWalk_visitBound_two_of_gt hN
    have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    omega

/-- The printed `CLOSED(x)` device: `x → 0 → N-1 → x`. -/
def closedPathWalk {N : ℕ} (hN : 0 < N) (x : Fin N) : PathWalk N x x :=
  B1ForwardWalk hN x x

theorem closedPathWalk_coversAll {N : ℕ} (hN : 0 < N) (x : Fin N) :
    CoversAll (closedPathWalk hN x) :=
  B1ForwardWalk_coversAll hN x x

theorem closedPathWalk_visitBound_three {N : ℕ} (hN : 0 < N) (x : Fin N) :
    VisitBound (closedPathWalk hN x) 3 := by
  intro v
  unfold closedPathWalk B1ForwardWalk
  have hle := visits_append_append_le
    (pwStraightWalk x (pathFirst hN))
    (pwStraightWalk (pathFirst hN) (pathLast hN))
    (pwStraightWalk (pathLast hN) x) v
  rw [pwStraightWalk_visits, pwStraightWalk_visits, pwStraightWalk_visits] at hle
  split_ifs at hle <;> omega

theorem closedPathWalk_visits_le_two_of_ne {N : ℕ} (hN : 0 < N) (x v : Fin N)
    (hvx : v ≠ x) : visits (closedPathWalk hN x) v ≤ 2 := by
  unfold closedPathWalk B1ForwardWalk
  have hle := visits_append_append_le
    (pwStraightWalk x (pathFirst hN))
    (pwStraightWalk (pathFirst hN) (pathLast hN))
    (pwStraightWalk (pathLast hN) x) v
  rw [pwStraightWalk_visits, pwStraightWalk_visits, pwStraightWalk_visits] at hle
  have hsum :
      (if PWInEndpointInterval x (pathFirst hN) v then 1 else 0) +
          (if PWInEndpointInterval (pathFirst hN) (pathLast hN) v then 1 else 0) +
            (if PWInEndpointInterval (pathLast hN) x v then 1 else 0) ≤ 2 := by
    simp only [PWInEndpointInterval, pathFirst, pathLast, Fin.val_mk]
    split_ifs <;> simp_all only [Fin.ne_iff_vne] <;> omega
  exact le_trans hle hsum

/-- A two-leg walk which covers the path from its left end through both prescribed ends. -/
def leftCoverWalk {N : ℕ} (hN : 0 < N) (i j : Fin N) : PathWalk N i j :=
  (pwStraightWalk i (pathFirst hN)).append (pwStraightWalk (pathFirst hN) j)

/-- A two-leg walk which covers both prescribed ends through the right end of the path. -/
def rightCoverWalk {N : ℕ} (hN : 0 < N) (i j : Fin N) : PathWalk N i j :=
  (pwStraightWalk i (pathLast hN)).append (pwStraightWalk (pathLast hN) j)

theorem leftCoverWalk_visits_le {N : ℕ} (hN : 0 < N) (i j v : Fin N) :
    visits (leftCoverWalk hN i j) v ≤
      (if v.val ≤ i.val then 1 else 0) + (if v.val ≤ j.val then 1 else 0) := by
  unfold leftCoverWalk
  have hle := visits_append_le
    (pwStraightWalk i (pathFirst hN)) (pwStraightWalk (pathFirst hN) j) v
  rw [pwStraightWalk_visits, pwStraightWalk_visits] at hle
  simpa [PWInEndpointInterval, pathFirst] using hle

theorem rightCoverWalk_visits_le {N : ℕ} (hN : 0 < N) (i j v : Fin N) :
    visits (rightCoverWalk hN i j) v ≤
      (if i.val ≤ v.val then 1 else 0) + (if j.val ≤ v.val then 1 else 0) := by
  unfold rightCoverWalk
  have hle := visits_append_le
    (pwStraightWalk i (pathLast hN)) (pwStraightWalk (pathLast hN) j) v
  rw [pwStraightWalk_visits, pwStraightWalk_visits] at hle
  have hiN : i.val ≤ N - 1 := by omega
  have hjN : j.val ≤ N - 1 := by omega
  have hvN : v.val ≤ N - 1 := by omega
  simpa [PWInEndpointInterval, pathLast, hiN, hjN, hvN] using hle

theorem leftCoverWalk_visitBound_two {N : ℕ} (hN : 0 < N) (i j : Fin N) :
    VisitBound (leftCoverWalk hN i j) 2 := by
  intro v
  have := leftCoverWalk_visits_le hN i j v
  split_ifs at this <;> omega

theorem rightCoverWalk_visitBound_two {N : ℕ} (hN : 0 < N) (i j : Fin N) :
    VisitBound (rightCoverWalk hN i j) 2 := by
  intro v
  have := rightCoverWalk_visits_le hN i j v
  split_ifs at this <;> omega

theorem leftCoverWalk_covers_of_le_max {N : ℕ} (hN : 0 < N) (i j v : Fin N)
    (hv : v.val ≤ max i.val j.val) : Covers (leftCoverWalk hN i j) v := by
  unfold leftCoverWalk
  unfold Covers
  rw [SimpleGraph.Walk.mem_support_append_iff]
  by_cases hvi : v.val ≤ i.val
  · left
    exact (pwStraightWalk_covers_iff i (pathFirst hN) v).mpr (by
      simp [PWInEndpointInterval, pathFirst, hvi])
  · right
    have hvj : v.val ≤ j.val := by omega
    exact (pwStraightWalk_covers_iff (pathFirst hN) j v).mpr (by
      simp [PWInEndpointInterval, pathFirst, hvj])

theorem rightCoverWalk_covers_of_min_le {N : ℕ} (hN : 0 < N) (i j v : Fin N)
    (hv : min i.val j.val ≤ v.val) : Covers (rightCoverWalk hN i j) v := by
  unfold rightCoverWalk
  unfold Covers
  rw [SimpleGraph.Walk.mem_support_append_iff]
  by_cases hiv : i.val ≤ v.val
  · left
    exact (pwStraightWalk_covers_iff i (pathLast hN) v).mpr (by
      simp [PWInEndpointInterval, pathLast, hiv]
      omega)
  · right
    have hjv : j.val ≤ v.val := by omega
    exact (pwStraightWalk_covers_iff (pathLast hN) j v).mpr (by
      simp [PWInEndpointInterval, pathLast, hjv]
      omega)

/-- Exact visit accounting for append: the common endpoint is counted by both pieces but only
once by the appended support. -/
theorem visits_append_add_join {N : ℕ} {a b c : Fin N}
    (p : PathWalk N a b) (q : PathWalk N b c) (v : Fin N) :
    visits (p.append q) v + (if v = b then 1 else 0) = visits p v + visits q v := by
  unfold visits PathWalk.vertices
  rw [SimpleGraph.Walk.support_append, List.count_append]
  have hs := congrArg (fun l : List (Fin N) => l.count v) (q.cons_tail_support)
  simp only [List.count_cons] at hs
  by_cases hv : v = b
  · subst v
    simp at hs ⊢
    omega
  · have hb : b ≠ v := Ne.symm hv
    simp [hv, hb] at hs ⊢
    omega

theorem closedPathWalk_visits_self_of_endpoint {N : ℕ} (hN2 : 2 ≤ N) (x : Fin N)
    (hx : x.val = 0 ∨ x.val = N - 1) : visits (closedPathWalk (by omega) x) x = 2 := by
  let hN : 0 < N := by omega
  change visits (closedPathWalk hN x) x = 2
  have hfl : pathFirst hN ≠ pathLast hN := by
    intro heq
    have := congrArg Fin.val heq
    simp [pathFirst, pathLast] at this
    omega
  have hlf : pathLast hN ≠ pathFirst hN := Ne.symm hfl
  rcases hx with hx | hx
  · have hxf : x = pathFirst hN := by
      apply Fin.ext
      simpa [pathFirst] using hx
    subst x
    unfold closedPathWalk B1ForwardWalk
    have h12 := visits_append_add_join
      (pwStraightWalk (pathFirst hN) (pathFirst hN))
      (pwStraightWalk (pathFirst hN) (pathLast hN)) (pathFirst hN)
    have h123 := visits_append_add_join
      ((pwStraightWalk (pathFirst hN) (pathFirst hN)).append
        (pwStraightWalk (pathFirst hN) (pathLast hN)))
      (pwStraightWalk (pathLast hN) (pathFirst hN)) (pathFirst hN)
    rw [pwStraightWalk_visits, pwStraightWalk_visits] at h12
    rw [pwStraightWalk_visits] at h123
    have hp11 : PWInEndpointInterval (pathFirst hN) (pathFirst hN) (pathFirst hN) := by
      simp [PWInEndpointInterval]
    have hp1l : PWInEndpointInterval (pathFirst hN) (pathLast hN) (pathFirst hN) := by
      simp [PWInEndpointInterval, pathFirst, pathLast]
    have hpl1 : PWInEndpointInterval (pathLast hN) (pathFirst hN) (pathFirst hN) := by
      simp [PWInEndpointInterval, pathFirst, pathLast]
    simp [hp11, hp1l, hpl1, hfl] at h12 h123
    omega
  · have hxl : x = pathLast hN := by
      apply Fin.ext
      simpa [pathLast] using hx
    subst x
    unfold closedPathWalk B1ForwardWalk
    have h12 := visits_append_add_join
      (pwStraightWalk (pathLast hN) (pathFirst hN))
      (pwStraightWalk (pathFirst hN) (pathLast hN)) (pathLast hN)
    have h123 := visits_append_add_join
      ((pwStraightWalk (pathLast hN) (pathFirst hN)).append
        (pwStraightWalk (pathFirst hN) (pathLast hN)))
      (pwStraightWalk (pathLast hN) (pathLast hN)) (pathLast hN)
    rw [pwStraightWalk_visits, pwStraightWalk_visits] at h12
    rw [pwStraightWalk_visits] at h123
    have hpl1 : PWInEndpointInterval (pathLast hN) (pathFirst hN) (pathLast hN) := by
      simp [PWInEndpointInterval, pathFirst, pathLast]
    have hp1l : PWInEndpointInterval (pathFirst hN) (pathLast hN) (pathLast hN) := by
      simp [PWInEndpointInterval, pathFirst, pathLast]
    have hpll : PWInEndpointInterval (pathLast hN) (pathLast hN) (pathLast hN) := by
      simp [PWInEndpointInterval]
    simp [hpl1, hp1l, hpll, hlf] at h12 h123
    omega

theorem closedPathWalk_endpoint_visitBound_two {N : ℕ} (hN2 : 2 ≤ N) (x : Fin N)
    (hx : x.val = 0 ∨ x.val = N - 1) :
    VisitBound (closedPathWalk (by omega) x) 2 := by
  intro v
  by_cases hvx : v = x
  · subst v
    rw [closedPathWalk_visits_self_of_endpoint hN2 x hx]
  · exact closedPathWalk_visits_le_two_of_ne (by omega) x v hvx

/-- The right-hand `W` in separated pattern 1, beginning at the first row after the split. -/
def rightSplitWalk {N : ℕ} (hN : 0 < N) (t c d : Fin N) : PathWalk N c d :=
  ((pwStraightWalk c t).append (pwStraightWalk t (pathLast hN))).append
    (pwStraightWalk (pathLast hN) d)

theorem rightSplitWalk_covers_of_le {N : ℕ} (hN : 0 < N) (t c d v : Fin N)
    (htv : t.val ≤ v.val) : Covers (rightSplitWalk hN t c d) v := by
  unfold rightSplitWalk Covers
  rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.mem_support_append_iff]
  left
  right
  exact (pwStraightWalk_covers_iff t (pathLast hN) v).mpr (by
    simp [PWInEndpointInterval, pathLast, htv]
    omega)

theorem rightSplitWalk_visitBound_two {N : ℕ} (hN : 0 < N) {t c d : Fin N}
    (htc : t.val ≤ c.val) (hcd : c.val < d.val) :
    VisitBound (rightSplitWalk hN t c d) 2 := by
  intro v
  unfold rightSplitWalk
  have hle := visits_append_append_le
    (pwStraightWalk c t) (pwStraightWalk t (pathLast hN))
    (pwStraightWalk (pathLast hN) d) v
  rw [pwStraightWalk_visits, pwStraightWalk_visits, pwStraightWalk_visits] at hle
  have hsum :
      (if PWInEndpointInterval c t v then 1 else 0) +
          (if PWInEndpointInterval t (pathLast hN) v then 1 else 0) +
            (if PWInEndpointInterval (pathLast hN) d v then 1 else 0) ≤ 2 := by
    simp only [PWInEndpointInterval, pathLast, Fin.val_mk]
    split_ifs <;> omega
  exact le_trans hle hsum

theorem rightSplitWalk_visits_eq_zero_of_lt {N : ℕ} (hN : 0 < N) {t c d v : Fin N}
    (htc : t.val ≤ c.val) (htd : t.val ≤ d.val) (htv : v.val < t.val) :
    visits (rightSplitWalk hN t c d) v = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold rightSplitWalk
  have hle := visits_append_append_le
    (pwStraightWalk c t) (pwStraightWalk t (pathLast hN))
    (pwStraightWalk (pathLast hN) d) v
  rw [pwStraightWalk_visits, pwStraightWalk_visits, pwStraightWalk_visits] at hle
  have hsum :
      (if PWInEndpointInterval c t v then 1 else 0) +
          (if PWInEndpointInterval t (pathLast hN) v then 1 else 0) +
            (if PWInEndpointInterval (pathLast hN) d v then 1 else 0) = 0 := by
    simp only [PWInEndpointInterval, pathLast, Fin.val_mk]
    split_ifs <;> omega
  omega

/-- Row 0, pattern 1: the four distinct ends occur in separated order. -/
structure B2Row0SeparatedHyp {N : ℕ} (a b c d : Fin N) : Prop where
  hab : a.val < b.val
  hbc : b.val < c.val
  hcd : c.val < d.val

private def row0SplitStart {N : ℕ} {b c : Fin N} (hbc : b.val < c.val) : Fin N :=
  ⟨b.val + 1, by omega⟩

/-- The printed row-0 separated SPLIT construction. -/
def B2Row0SeparatedConstruction {N : ℕ} (hN : 0 < N) (a b c d : Fin N)
    (h : B2Row0SeparatedHyp a b c d) : PathWalk N a b × PathWalk N c d :=
  (leftCoverWalk hN a b, rightSplitWalk hN (row0SplitStart h.hbc) c d)

theorem B2Row0SeparatedConstruction_spec {N : ℕ} (hN : 0 < N) (a b c d : Fin N)
    (h : B2Row0SeparatedHyp a b c d) :
    let W := B2Row0SeparatedConstruction hN a b c d h
    CoversAll₂ W.1 W.2 ∧ TotalVisitBound₂ W.1 W.2 2 ∧
      VisitBound W.1 3 ∧ VisitBound W.2 3 := by
  rcases h with ⟨hab, hbc, hcd⟩
  dsimp [B2Row0SeparatedConstruction]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    by_cases hv : v.val ≤ b.val
    · left
      exact leftCoverWalk_covers_of_le_max hN a b v (le_trans hv (Nat.le_max_right _ _))
    · right
      apply rightSplitWalk_covers_of_le hN (row0SplitStart hbc) c d v
      change b.val + 1 ≤ v.val
      omega
  · intro v
    by_cases hv : v.val ≤ b.val
    · have hleft := leftCoverWalk_visitBound_two hN a b v
      have hright := rightSplitWalk_visits_eq_zero_of_lt hN
        (t := row0SplitStart hbc) (c := c) (d := d) (v := v) (by
          change b.val + 1 ≤ c.val
          omega) (by
          change b.val + 1 ≤ d.val
          omega) (by
          change v.val < b.val + 1
          omega)
      omega
    · have hleft := leftCoverWalk_visits_le hN a b v
      have hright := rightSplitWalk_visitBound_two hN
        (t := row0SplitStart hbc) (c := c) (d := d) (by
          change b.val + 1 ≤ c.val
          omega) hcd v
      simp only [show ¬v.val ≤ a.val by omega, if_false, hv, zero_add] at hleft
      omega
  · intro v
    exact le_trans (leftCoverWalk_visitBound_two hN a b v) (by omega)
  · intro v
    exact le_trans (rightSplitWalk_visitBound_two hN
      (t := row0SplitStart hbc) (c := c) (d := d) (by
        change b.val + 1 ≤ c.val
        omega) hcd v) (by omega)

/-- The exact coincidence assumptions for row 1 (`a = b` only). -/
structure B2Row1Hyp {N : ℕ} (a b c d : Fin N) : Prop where
  hab : a = b
  hac : a ≠ c
  had : a ≠ d
  hcd : c ≠ d

/-- The printed row-1 construction `NIL(a) + B1(c → d)`. -/
def B2Row1Construction {N : ℕ} (hN : 0 < N) (a b c d : Fin N)
    (h : B2Row1Hyp a b c d) : PathWalk N a b × PathWalk N c d :=
  ((nil a).copy rfl h.hab, B1Walk hN c d)

theorem B2Row1Construction_spec {N : ℕ} (hN : 0 < N) (a b c d : Fin N)
    (h : B2Row1Hyp a b c d) :
    let W := B2Row1Construction hN a b c d h
    CoversAll₂ W.1 W.2 ∧ TotalVisitBound₂ W.1 W.2 3 ∧
      (∀ v, v ≠ a → visits W.1 v + visits W.2 v ≤ 2) ∧
      VisitBound W.1 3 ∧ VisitBound W.2 3 := by
  rcases h with ⟨rfl, hac, had, hcd⟩
  dsimp only [B2Row1Construction]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v
    right
    exact B1Walk_coversAll hN c d v
  · intro v
    have hB1 := B1Walk_visitBound_two_of_ne hN hcd v
    by_cases hva : v = a
    · subst v
      simp only [visits_copy, visits_nil_self]
      omega
    · rw [visits_copy, visits_nil_ne hva]
      omega
  · intro v hva
    rw [visits_copy, visits_nil_ne hva]
    simpa using B1Walk_visitBound_two_of_ne hN hcd v
  · intro v
    by_cases hva : v = a
    · subst v
      simp
    · simp [visits_nil_ne hva]
  · intro v
    exact le_trans (B1Walk_visitBound_two_of_ne hN hcd v) (by omega)

/-- The rows on which row 2 permits total visit count three.  This is the transit interval
from the common end to the nearer of `b,d` when both unmatched ends lie on the same side. -/
def B2Row2Transit {N : ℕ} (a b d v : Fin N) : Prop :=
  (a.val ≤ min b.val d.val ∧ a.val ≤ v.val ∧ v.val ≤ min b.val d.val) ∨
  (max b.val d.val ≤ a.val ∧ max b.val d.val ≤ v.val ∧ v.val ≤ a.val)

theorem left_right_total_visits_le_three {N : ℕ} (hN : 0 < N) (a l r v : Fin N)
    (hlr : l.val < r.val) :
    visits (leftCoverWalk hN a l) v + visits (rightCoverWalk hN a r) v ≤ 3 := by
  have hl := leftCoverWalk_visits_le hN a l v
  have hr := rightCoverWalk_visits_le hN a r v
  have hsum :
      (if v.val ≤ a.val then 1 else 0) + (if v.val ≤ l.val then 1 else 0) +
        ((if a.val ≤ v.val then 1 else 0) + (if r.val ≤ v.val then 1 else 0)) ≤ 3 := by
    split_ifs <;> omega
  omega

theorem left_right_total_visits_le_two_off_transit {N : ℕ} (hN : 0 < N)
    (a l r v : Fin N) (hlr : l.val < r.val) (hoff : ¬ B2Row2Transit a l r v) :
    visits (leftCoverWalk hN a l) v + visits (rightCoverWalk hN a r) v ≤ 2 := by
  have hl := leftCoverWalk_visits_le hN a l v
  have hr := rightCoverWalk_visits_le hN a r v
  unfold B2Row2Transit at hoff
  simp only [Nat.min_eq_left (Nat.le_of_lt hlr), Nat.max_eq_right (Nat.le_of_lt hlr)] at hoff
  split_ifs at hl hr <;> omega

theorem left_right_coversAll {N : ℕ} (hN : 0 < N) (a l r : Fin N) :
    CoversAll₂ (leftCoverWalk hN a l) (rightCoverWalk hN a r) := by
  intro v
  by_cases hva : v.val ≤ a.val
  · left
    exact leftCoverWalk_covers_of_le_max hN a l v
      (le_trans hva (Nat.le_max_left _ _))
  · right
    exact rightCoverWalk_covers_of_min_le hN a r v
      (le_trans (Nat.min_le_left _ _) (by omega))

/-- The exact coincidence assumptions for row 2 (`a = c` only). -/
structure B2Row2Hyp {N : ℕ} (a b c d : Fin N) : Prop where
  hac : a = c
  hab : a ≠ b
  had : a ≠ d
  hbd : b ≠ d

/-- The printed row-2 split.  The smaller of `b,d` receives the left `W`; the other walk
receives the right `W`, so its initial leg is precisely the printed TRANSIT. -/
def B2Row2Construction {N : ℕ} (hN : 0 < N) (a b c d : Fin N)
    (_h : B2Row2Hyp a b c d) : PathWalk N a b × PathWalk N c d :=
  if b.val < d.val then
    (leftCoverWalk hN a b, rightCoverWalk hN c d)
  else
    (rightCoverWalk hN a b, leftCoverWalk hN c d)

theorem B2Row2Construction_spec {N : ℕ} (hN : 0 < N) (a b c d : Fin N)
    (h : B2Row2Hyp a b c d) :
    let W := B2Row2Construction hN a b c d h
    CoversAll₂ W.1 W.2 ∧ TotalVisitBound₂ W.1 W.2 3 ∧
      (∀ v, ¬ B2Row2Transit a b d v → visits W.1 v + visits W.2 v ≤ 2) ∧
      VisitBound W.1 3 ∧ VisitBound W.2 3 := by
  rcases h with ⟨rfl, hab, had, hbd⟩
  dsimp only [B2Row2Construction]
  split_ifs with hlt
  · refine ⟨left_right_coversAll hN a b d, ?_, ?_, ?_, ?_⟩
    · intro v
      exact left_right_total_visits_le_three hN a b d v hlt
    · intro v hoff
      exact left_right_total_visits_le_two_off_transit hN a b d v hlt hoff
    · intro v
      exact le_trans (leftCoverWalk_visitBound_two hN a b v) (by omega)
    · intro v
      exact le_trans (rightCoverWalk_visitBound_two hN a d v) (by omega)
  · have hdl : d.val < b.val := by
      have hval : b.val ≠ d.val := fun hval => hbd (Fin.ext hval)
      omega
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro v
      have hc := left_right_coversAll hN a d b v
      exact hc.symm
    · intro v
      have ht := left_right_total_visits_le_three hN a d b v hdl
      simpa only [Prod.fst, Prod.snd, add_comm] using ht
    · intro v hoff
      have ht := left_right_total_visits_le_two_off_transit hN a d b v hdl (by
        simpa [B2Row2Transit, Nat.min_comm, Nat.max_comm] using hoff)
      simpa only [Prod.fst, Prod.snd, add_comm] using ht
    · intro v
      exact le_trans (rightCoverWalk_visitBound_two hN a b v) (by omega)
    · intro v
      exact le_trans (leftCoverWalk_visitBound_two hN a d v) (by omega)

/-- The exact coincidence assumptions for row 3. -/
structure B2Row3Hyp {N : ℕ} (a b c d : Fin N) : Prop where
  hab : a = b
  hcd : c = d
  hac : a ≠ c

/-- The printed row-3 construction `NIL(a) + CLOSED(c)`. -/
def B2Row3Construction {N : ℕ} (hN : 0 < N) (a b c d : Fin N)
    (h : B2Row3Hyp a b c d) : PathWalk N a b × PathWalk N c d :=
  ((nil a).copy rfl h.hab, (closedPathWalk hN c).copy rfl h.hcd)

theorem B2Row3Construction_spec {N : ℕ} (hN : 0 < N) (a b c d : Fin N)
    (h : B2Row3Hyp a b c d) :
    let W := B2Row3Construction hN a b c d h
    CoversAll₂ W.1 W.2 ∧ TotalVisitBound₂ W.1 W.2 3 ∧
      (∀ v, v ≠ a → v ≠ c → visits W.1 v + visits W.2 v ≤ 2) ∧
      VisitBound W.1 3 ∧ VisitBound W.2 3 := by
  rcases h with ⟨rfl, rfl, hac⟩
  dsimp only [B2Row3Construction]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v
    right
    exact closedPathWalk_coversAll hN c v
  · intro v
    by_cases hvc : v = c
    · subst v
      have hne : c ≠ a := hac.symm
      rw [visits_copy, visits_nil_ne hne, visits_copy]
      simpa using closedPathWalk_visitBound_three hN c c
    · have hc := closedPathWalk_visits_le_two_of_ne hN c v hvc
      by_cases hva : v = a
      · subst v
        simp only [visits_copy, visits_nil_self]
        omega
      · rw [visits_copy, visits_nil_ne hva, visits_copy]
        omega
  · intro v hva hvc
    rw [visits_copy, visits_nil_ne hva, visits_copy]
    simpa using closedPathWalk_visits_le_two_of_ne hN c v hvc
  · intro v
    rw [visits_copy]
    by_cases hva : v = a <;> simp [hva, visits_nil_ne]
  · intro v
    rw [visits_copy]
    exact closedPathWalk_visitBound_three hN c v

/-- The two possible cross-pair orientations in row 4. -/
structure B2Row4Hyp {N : ℕ} (a b c d : Fin N) : Prop where
  shape : (a = c ∧ b = d) ∨ (a = d ∧ b = c)
  hab : a ≠ b

/-- The printed row-4 construction: B1 on the first pair and STRAIGHT on the second. -/
def B2Row4Construction {N : ℕ} (hN : 0 < N) (a b c d : Fin N)
    (_h : B2Row4Hyp a b c d) : PathWalk N a b × PathWalk N c d :=
  (B1Walk hN a b, pwStraightWalk c d)

theorem B2Row4Construction_spec {N : ℕ} (hN : 0 < N) (a b c d : Fin N)
    (h : B2Row4Hyp a b c d) :
    let W := B2Row4Construction hN a b c d h
    CoversAll₂ W.1 W.2 ∧ TotalVisitBound₂ W.1 W.2 3 ∧
      (∀ v, ¬ PWInEndpointInterval a b v → visits W.1 v + visits W.2 v ≤ 2) ∧
      VisitBound W.1 3 ∧ VisitBound W.2 3 := by
  rcases h with ⟨hshape, hab⟩
  rcases hshape with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · dsimp only [B2Row4Construction]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro v
      left
      exact B1Walk_coversAll hN a b v
    · intro v
      have hB := B1Walk_visitBound_two_of_ne hN hab v
      rw [pwStraightWalk_visits]
      split_ifs <;> omega
    · intro v hoff
      rw [pwStraightWalk_visits, if_neg hoff, Nat.add_zero]
      exact B1Walk_visitBound_two_of_ne hN hab v
    · intro v
      exact le_trans (B1Walk_visitBound_two_of_ne hN hab v) (by omega)
    · intro v
      rw [pwStraightWalk_visits]
      split_ifs <;> omega
  · dsimp only [B2Row4Construction]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro v
      left
      exact B1Walk_coversAll hN a b v
    · intro v
      have hB := B1Walk_visitBound_two_of_ne hN hab v
      rw [pwStraightWalk_visits]
      have hint : PWInEndpointInterval b a v ↔ PWInEndpointInterval a b v := by
        simp [PWInEndpointInterval, min_comm, max_comm]
      split_ifs <;> omega
    · intro v hoff
      rw [pwStraightWalk_visits]
      have hoff' : ¬ PWInEndpointInterval b a v := by
        simpa [PWInEndpointInterval, min_comm, max_comm] using hoff
      rw [if_neg hoff', Nat.add_zero]
      exact B1Walk_visitBound_two_of_ne hN hab v
    · intro v
      exact le_trans (B1Walk_visitBound_two_of_ne hN hab v) (by omega)
    · intro v
      rw [pwStraightWalk_visits]
      split_ifs <;> omega

/-- The exact coincidence assumptions for row 5 (`a = b = c ≠ d`). -/
structure B2Row5Hyp {N : ℕ} (a b c d : Fin N) : Prop where
  hab : a = b
  hac : a = c
  had : a ≠ d

/-- The printed row-5 construction `NIL(a) + B1(a → d)`. -/
def B2Row5Construction {N : ℕ} (hN : 0 < N) (a b c d : Fin N)
    (h : B2Row5Hyp a b c d) : PathWalk N a b × PathWalk N c d :=
  ((nil a).copy rfl h.hab, B1Walk hN c d)

theorem B2Row5Construction_spec {N : ℕ} (hN : 0 < N) (a b c d : Fin N)
    (h : B2Row5Hyp a b c d) :
    let W := B2Row5Construction hN a b c d h
    CoversAll₂ W.1 W.2 ∧ TotalVisitBound₂ W.1 W.2 3 ∧
      (∀ v, v ≠ a → visits W.1 v + visits W.2 v ≤ 2) ∧
      VisitBound W.1 3 ∧ VisitBound W.2 3 := by
  rcases h with ⟨rfl, rfl, had⟩
  dsimp only [B2Row5Construction]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v
    right
    exact B1Walk_coversAll hN a d v
  · intro v
    have hB := B1Walk_visitBound_two_of_ne hN had v
    by_cases hva : v = a
    · subst v
      simp only [visits_copy, visits_nil_self]
      omega
    · rw [visits_copy, visits_nil_ne hva]
      omega
  · intro v hva
    rw [visits_copy, visits_nil_ne hva]
    simpa using B1Walk_visitBound_two_of_ne hN had v
  · intro v
    rw [visits_copy]
    by_cases hva : v = a <;> simp [hva, visits_nil_ne]
  · intro v
    exact le_trans (B1Walk_visitBound_two_of_ne hN had v) (by omega)

/-- The exact coincidence assumptions for row 6 (`a = c = d ≠ b`). -/
structure B2Row6Hyp {N : ℕ} (a b c d : Fin N) : Prop where
  hac : a = c
  hcd : c = d
  hab : a ≠ b

/-- The printed row-6 construction, in the endpoint order of the table: `B1(a → b) + NIL(c)`. -/
def B2Row6Construction {N : ℕ} (hN : 0 < N) (a b c d : Fin N)
    (h : B2Row6Hyp a b c d) : PathWalk N a b × PathWalk N c d :=
  (B1Walk hN a b, (nil c).copy rfl h.hcd)

theorem B2Row6Construction_spec {N : ℕ} (hN : 0 < N) (a b c d : Fin N)
    (h : B2Row6Hyp a b c d) :
    let W := B2Row6Construction hN a b c d h
    CoversAll₂ W.1 W.2 ∧ TotalVisitBound₂ W.1 W.2 3 ∧
      (∀ v, v ≠ c → visits W.1 v + visits W.2 v ≤ 2) ∧
      VisitBound W.1 3 ∧ VisitBound W.2 3 := by
  rcases h with ⟨rfl, rfl, hab⟩
  dsimp only [B2Row6Construction]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v
    left
    exact B1Walk_coversAll hN a b v
  · intro v
    have hB := B1Walk_visitBound_two_of_ne hN hab v
    by_cases hva : v = a
    · subst v
      simp only [visits_copy, visits_nil_self]
      omega
    · rw [visits_copy, visits_nil_ne hva]
      omega
  · intro v hva
    rw [visits_copy, visits_nil_ne hva, Nat.add_zero]
    exact B1Walk_visitBound_two_of_ne hN hab v
  · intro v
    exact le_trans (B1Walk_visitBound_two_of_ne hN hab v) (by omega)
  · intro v
    rw [visits_copy]
    by_cases hva : v = a <;> simp [hva, visits_nil_ne]

/-- The exact coincidence and endpoint assumptions for row 7. -/
structure B2Row7Hyp {N : ℕ} (a b c d : Fin N) : Prop where
  hab : a = b
  hac : a = c
  had : a = d
  endpoint : a.val = 0 ∨ a.val = N - 1

/-- The printed row-7 construction `NIL(a) + CLOSED(a)`. -/
def B2Row7Construction {N : ℕ} (hN : 0 < N) (a b c d : Fin N)
    (h : B2Row7Hyp a b c d) : PathWalk N a b × PathWalk N c d :=
  ((nil a).copy rfl h.hab, (closedPathWalk hN a).copy h.hac h.had)

theorem B2Row7Construction_spec {N : ℕ} (hN2 : 2 ≤ N) (a b c d : Fin N)
    (h : B2Row7Hyp a b c d) :
    let W := B2Row7Construction (by omega) a b c d h
    CoversAll₂ W.1 W.2 ∧ TotalVisitBound₂ W.1 W.2 3 ∧
      visits W.1 a + visits W.2 a = 3 ∧
      (∀ v, v ≠ a → visits W.1 v + visits W.2 v ≤ 2) ∧
      VisitBound W.1 3 ∧ VisitBound W.2 3 := by
  rcases h with ⟨rfl, rfl, rfl, hend⟩
  dsimp only [B2Row7Construction]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    right
    exact closedPathWalk_coversAll (by omega) a v
  · intro v
    have hc := closedPathWalk_endpoint_visitBound_two hN2 a hend v
    by_cases hva : v = a
    · subst v
      simp only [visits_copy, visits_nil_self]
      omega
    · rw [visits_copy, visits_nil_ne hva, visits_copy]
      omega
  · rw [visits_copy, visits_nil_self, visits_copy,
      closedPathWalk_visits_self_of_endpoint hN2 a hend]
  · intro v hva
    rw [visits_copy, visits_nil_ne hva, visits_copy, Nat.zero_add]
    exact closedPathWalk_endpoint_visitBound_two hN2 a hend v
  · intro v
    rw [visits_copy]
    by_cases hva : v = a <;> simp [hva, visits_nil_ne]
  · intro v
    rw [visits_copy]
    exact le_trans (closedPathWalk_endpoint_visitBound_two hN2 a hend v) (by omega)

/-! ### Row 8: the general interior obstruction -/

/-- A path walk from strictly below `a` to strictly above `a` must visit `a`. -/
theorem pathWalk_covers_between {N : ℕ} {x y a : Fin N} (w : PathWalk N x y)
    (hxa : x.val < a.val) (hay : a.val < y.val) : Covers w a := by
  induction w with
  | nil => omega
  | @cons u v z hadj w ih =>
    by_cases hva : v.val < a.val
    · unfold Covers at ih ⊢
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
      exact Or.inr (ih hva hay)
    · have hadj' := SimpleGraph.pathGraph_adj.mp hadj
      have hval : v.val = a.val := by
        rcases hadj' with h | h <;> omega
      have heq : v = a := Fin.ext hval
      unfold Covers
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
      right
      simpa [heq] using w.start_mem_support

theorem visits_append_eq_add_of_ne {N : ℕ} {x y z a : Fin N}
    (p : PathWalk N x y) (q : PathWalk N y z) (hay : a ≠ y) :
    visits (p.append q) a = visits p a + visits q a := by
  have h := visits_append_add_join p q a
  simpa [hay] using h

theorem one_le_visits_start {N : ℕ} {x y : Fin N} (w : PathWalk N x y) :
    1 ≤ visits w x := by
  rw [visits, List.one_le_count_iff]
  exact w.start_mem_support

theorem one_le_visits_end {N : ℕ} {x y : Fin N} (w : PathWalk N x y) :
    1 ≤ visits w y := by
  rw [visits, List.one_le_count_iff]
  exact w.end_mem_support

/-- Any nontrivial excursion of a closed walk contributes a second anchor visit. -/
theorem closedWalk_two_le_visits_of_covers_ne {N : ℕ} {a v : Fin N}
    (w : PathWalk N a a) (hva : v ≠ a) (hv : Covers w v) : 2 ≤ visits w a := by
  have hn : ¬ w.Nil := by
    intro hw
    have hs : w.support = [a] := SimpleGraph.Walk.nil_iff_support_eq.mp hw
    unfold Covers at hv
    change v ∈ w.support at hv
    rw [hs, List.mem_singleton] at hv
    exact hva hv
  have hend : a ∈ w.support.tail := w.end_mem_tail_support hn
  unfold visits PathWalk.vertices
  rw [← w.cons_tail_support, List.count_cons]
  simp only [beq_self_eq_true, ↓reduceIte]
  have ht : 1 ≤ w.support.tail.count a := List.one_le_count_iff.mpr hend
  omega

/-- A closed path walk which reaches both sides of its anchor visits that anchor at least three
times.  The middle occurrence is forced by the path separator. -/
theorem closedWalk_three_le_visits_of_covers_both_sides {N : ℕ}
    {a l r : Fin N} (w : PathWalk N a a) (hla : l.val < a.val) (har : a.val < r.val)
    (hl : Covers w l) (hr : Covers w r) : 3 ≤ visits w a := by
  have hal : a ≠ l := by
    intro h
    have := congrArg Fin.val h
    omega
  have har_ne : a ≠ r := by
    intro h
    have := congrArg Fin.val h
    omega
  unfold Covers at hl hr
  rcases SimpleGraph.Walk.mem_support_iff_exists_append.mp hl with ⟨p, q, rfl⟩
  rw [SimpleGraph.Walk.mem_support_append_iff] at hr
  rcases hr with hrp | hrq
  · rcases SimpleGraph.Walk.mem_support_iff_exists_append.mp hrp with ⟨pr, s, rfl⟩
    have hsaRev : Covers s.reverse a := pathWalk_covers_between s.reverse hla har
    have hsa : Covers s a := by
      unfold Covers at hsaRev ⊢
      simpa using hsaRev
    have hpr := one_le_visits_start pr
    have hs : 1 ≤ visits s a := by
      rw [visits, List.one_le_count_iff]
      exact hsa
    have hq := one_le_visits_end q
    have he1 := visits_append_eq_add_of_ne pr s har_ne
    have he2 := visits_append_eq_add_of_ne (pr.append s) q hal
    omega
  · rcases SimpleGraph.Walk.mem_support_iff_exists_append.mp hrq with ⟨s, qr, rfl⟩
    have hsa : Covers s a := pathWalk_covers_between s hla har
    have hp := one_le_visits_start p
    have hs : 1 ≤ visits s a := by
      rw [visits, List.one_le_count_iff]
      exact hsa
    have hqr := one_le_visits_end qr
    have he1 := visits_append_eq_add_of_ne s qr har_ne
    have he2 := visits_append_eq_add_of_ne p (s.append qr) hal
    omega

/-- Row 8, generally: two closed walks based at an interior row and jointly covering the path
have at least four total visits at their common anchor. -/
theorem B2Row8_total_visits_ge_four {N : ℕ} {a : Fin N}
    (ha0 : 0 < a.val) (haN : a.val < N - 1)
    (w₁ w₂ : PathWalk N a a) (hcover : CoversAll₂ w₁ w₂) :
    4 ≤ visits w₁ a + visits w₂ a := by
  let hN : 0 < N := by omega
  let l : Fin N := pathFirst hN
  let r : Fin N := pathLast hN
  have hla : l.val < a.val := by simp [l, pathFirst, ha0]
  have har : a.val < r.val := by simpa [r, pathLast] using haN
  have hl := hcover l
  have hr := hcover r
  rcases hl with h₁l | h₂l <;> rcases hr with h₁r | h₂r
  · have h₁ := closedWalk_three_le_visits_of_covers_both_sides w₁ hla har h₁l h₁r
    have h₂ := one_le_visits_start w₂
    omega
  · have h₁ := closedWalk_two_le_visits_of_covers_ne w₁ (by
      intro h
      have := congrArg Fin.val h
      omega) h₁l
    have h₂ := closedWalk_two_le_visits_of_covers_ne w₂ (by
      intro h
      have := congrArg Fin.val h
      omega) h₂r
    omega
  · have h₁ := closedWalk_two_le_visits_of_covers_ne w₁ (by
      intro h
      have := congrArg Fin.val h
      omega) h₁r
    have h₂ := closedWalk_two_le_visits_of_covers_ne w₂ (by
      intro h
      have := congrArg Fin.val h
      omega) h₂l
    omega
  · have h₂ := closedWalk_three_le_visits_of_covers_both_sides w₂ hla har h₂l h₂r
    have h₁ := one_le_visits_start w₁
    omega

/-- The interior closed excursion on `P₃` forced by trying to cover both sides from the middle. -/
def closedMiddleExcursion : PathWalk 3 (1 : Fin 3) (1 : Fin 3) :=
  have h10 : (SimpleGraph.pathGraph 3).Adj (1 : Fin 3) (0 : Fin 3) := by
    rw [SimpleGraph.pathGraph_adj]
    norm_num
  have h01 : (SimpleGraph.pathGraph 3).Adj (0 : Fin 3) (1 : Fin 3) := by
    rw [SimpleGraph.pathGraph_adj]
    norm_num
  have h12 : (SimpleGraph.pathGraph 3).Adj (1 : Fin 3) (2 : Fin 3) := by
    rw [SimpleGraph.pathGraph_adj]
    norm_num
  have h21 : (SimpleGraph.pathGraph 3).Adj (2 : Fin 3) (1 : Fin 3) := by
    rw [SimpleGraph.pathGraph_adj]
    norm_num
  SimpleGraph.Walk.cons h10
    (SimpleGraph.Walk.cons h01
      (SimpleGraph.Walk.cons h12
        (SimpleGraph.Walk.cons h21
          SimpleGraph.Walk.nil)))

@[simp]
theorem closedMiddleExcursion_vertices :
    closedMiddleExcursion.vertices =
      [(1 : Fin 3), (0 : Fin 3), (1 : Fin 3), (2 : Fin 3), (1 : Fin 3)] :=
  by simp [closedMiddleExcursion]

/-- The draft B1 construction `1 → 0 → 2 → 1` on `P₃` has three visits at the start/end. -/
theorem closedMiddleExcursion_visits_middle :
    visits closedMiddleExcursion (1 : Fin 3) = 3 := by
  rw [visits, closedMiddleExcursion_vertices]
  have h12 : (1 : Fin 3) ≠ (2 : Fin 3) := by
    intro h
    have := congrArg Fin.val h
    norm_num at this
  simp [h12]

/-- In the current support-counting model, the B2 full-concentration zero-length plus excursion
device gives four total middle visits on `P₃`, not the printed bound three. -/
theorem B2_fullConcentration_nil_closed_visits_middle :
    visits (nil (1 : Fin 3)) (1 : Fin 3) +
      visits closedMiddleExcursion (1 : Fin 3) = 4 := by
  simp [closedMiddleExcursion_visits_middle]

/-- The same concrete walk covers every vertex of `P₃`. -/
theorem closedMiddleExcursion_coversAll :
    CoversAll closedMiddleExcursion := by
  intro v
  fin_cases v <;> simp [Covers]

/-! ## Hamilton-connected graphs have Hamilton cycles -/

private theorem hamPath_not_nil_of_card_ge_three {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {s t : V} {P : G.Walk s t} (hP : P.IsHamiltonian)
    (hcard : 3 ≤ Fintype.card V) : ¬ P.Nil := by
  intro hnil
  have hlen : P.length = Fintype.card V - 1 := hP.length_eq
  have hzero : P.length = 0 := SimpleGraph.Walk.length_eq_zero_iff.mpr hnil
  omega

/--
A Hamilton-connected finite simple graph on at least three vertices has a Hamilton cycle.

The proof extracts one edge from an arbitrary Hamilton path, then takes a Hamilton path between
the endpoints of that edge and closes it with the edge.
-/
theorem hamCycle_of_hamConnected {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} (hcard : 3 ≤ Fintype.card V) (hHC : IsHamConnected G) :
    G.IsHamiltonian := by
  classical
  intro _hnotSingleton
  obtain ⟨a⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨b, hba⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) a
  obtain ⟨P, hP⟩ := hHC a b hba.symm
  have hPnotNil : ¬ P.Nil := hamPath_not_nil_of_card_ge_three hP hcard
  have hadj : G.Adj a P.snd := P.adj_snd hPnotNil
  have ha_snd : a ≠ P.snd := G.ne_of_adj hadj
  obtain ⟨Q, hQ⟩ := hHC a P.snd ha_snd
  let C : G.Walk a a := Q.concat hadj.symm
  refine ⟨a, C, ?_⟩
  have hCnotNil : ¬ C.Nil := by
    intro hnil
    exact SimpleGraph.Walk.concat_ne_nil Q hadj.symm hnil.eq_nil
  have hC_support : C.support = Q.support ++ [a] := by
    simp [C, SimpleGraph.Walk.support_concat]
  have hC_tail_support : C.tail.support = Q.support.tail ++ [a] := by
    rw [SimpleGraph.Walk.support_tail_of_not_nil C hCnotNil, hC_support]
    exact List.tail_append_of_ne_nil (SimpleGraph.Walk.support_ne_nil Q)
  have hQ_path : Q.IsPath := hQ.isPath
  have hQ_nodup : Q.support.Nodup := hQ_path.support_nodup
  have ha_not_tail : a ∉ Q.support.tail := by
    have hcons : (a :: Q.support.tail).Nodup := by
      simpa [SimpleGraph.Walk.cons_tail_support Q] using hQ_nodup
    simpa using (List.nodup_cons.mp hcons).1
  have htail_nodup : (Q.support.tail ++ [a]).Nodup := by
    rw [List.nodup_append]
    constructor
    · exact hQ_nodup.tail
    constructor
    · simp
    · intro x hx y hy hxy
      rw [List.mem_singleton] at hy
      subst y
      exact ha_not_tail (hxy ▸ hx)
  have hC_tail_path : C.tail.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hC_tail_support]
    exact htail_nodup
  have hC_len : 3 ≤ C.length := by
    have hQlen : Q.length = Fintype.card V - 1 := hQ.length_eq
    simp [C, SimpleGraph.Walk.length_concat, hQlen]
    omega
  have hC_cycle : C.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    exact ⟨hC_tail_path, hC_len⟩
  have hC_tail_ham : C.tail.IsHamiltonian := by
    refine hC_tail_path.isHamiltonian_of_mem ?_
    intro v
    rw [hC_tail_support]
    by_cases hv : v = a
    · simp [hv]
    · have hvQ : v ∈ Q.support := hQ.mem_support v
      have hvTail : v ∈ Q.support.tail := by
        rw [← SimpleGraph.Walk.cons_tail_support Q] at hvQ
        rcases List.mem_cons.mp hvQ with hhead | htail
        · exact (hv hhead).elim
        · exact htail
      simp [hvTail, hv]
  exact ⟨hC_cycle, hC_tail_ham⟩

#print axioms B1_distinct_ends
#print axioms B1_equal_ends_visitBound_three
#print axioms B2_fullConcentration_nil_closed_visits_middle

/-! Foundations audit for every theorem added by the explicit B2-table formalization. -/
#print axioms visits_copy
#print axioms B1Walk_coversAll
#print axioms B1Walk_visitBound_two_of_ne
#print axioms closedPathWalk_coversAll
#print axioms closedPathWalk_visitBound_three
#print axioms closedPathWalk_visits_le_two_of_ne
#print axioms leftCoverWalk_visits_le
#print axioms rightCoverWalk_visits_le
#print axioms leftCoverWalk_visitBound_two
#print axioms rightCoverWalk_visitBound_two
#print axioms leftCoverWalk_covers_of_le_max
#print axioms rightCoverWalk_covers_of_min_le
#print axioms visits_append_add_join
#print axioms closedPathWalk_visits_self_of_endpoint
#print axioms closedPathWalk_endpoint_visitBound_two
#print axioms rightSplitWalk_covers_of_le
#print axioms rightSplitWalk_visitBound_two
#print axioms rightSplitWalk_visits_eq_zero_of_lt
#print axioms B2Row0SeparatedConstruction_spec
#print axioms B2Row1Construction_spec
#print axioms left_right_total_visits_le_three
#print axioms left_right_total_visits_le_two_off_transit
#print axioms left_right_coversAll
#print axioms B2Row2Construction_spec
#print axioms B2Row3Construction_spec
#print axioms B2Row4Construction_spec
#print axioms B2Row5Construction_spec
#print axioms B2Row6Construction_spec
#print axioms B2Row7Construction_spec
#print axioms pathWalk_covers_between
#print axioms visits_append_eq_add_of_ne
#print axioms one_le_visits_start
#print axioms one_le_visits_end
#print axioms closedWalk_two_le_visits_of_covers_ne
#print axioms closedWalk_three_le_visits_of_covers_both_sides
#print axioms B2Row8_total_visits_ge_four

end Brualdi.RealizationGraph.PathWalks
