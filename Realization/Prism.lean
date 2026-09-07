/-
Copyright (c) 2026 Jeffrey S. Baggett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey S. Baggett
-/
/-
  The prism's path vocabulary — `SECTION5_PRODUCT_LIFTING_COMPLETE.md` §5, Theorem 5.1.

  ## Why this file exists, and what the reuse audit found

  Theorem 5.1 is the `K₂` prism for paired-2-DPC: `OP2(H) → OP2(K₂ □ H)` for `H` balanced of order
  at least four.  **No existing machinery reaches it**, and that was checked rather than assumed
  (2026-08-06):

  * `ctProduct_paired_two_of_ranks` and `hypercube_ctProduct_paired_two` are CT-product specific.
    The tournament's factors are `deltaInterchangeGraph b`, and the bridge into the CT encoding is
    Paper 1's structure theorem for 0–1 interchange graphs, which does not apply here.
  * `coleman_thm15` gives `IsPairedKDPCForOpposite _ _ (a - 1)` from `a` welded copies, so at the
    prism's TWO copies it reaches only `k = 1` — Hamilton-laceability, not OP2.  This is exactly why
    §5 calls `K₂` "that genuine exceptional factor" and writes it its own proof.
  * `Thm15.lean`'s `rank3_case1`–`rank3_case6` do conclude `IsPairedDPC (weldGraph ell …) 2`, and
    the prism IS `weldGraph 2` with identity matchings — but their demands are `MonoDemand`
    (same-coloured pairs), and OP2's are opposite-coloured.  Different statement.

  So §5's case analysis has to be formalized.  Recorded here so the search is not re-run.

  ## The shape the formalization takes

  `WalkOfList.isPairedDPC_of_chains` is the interface: *produce two chained vertex lists with
  prescribed ends, jointly duplicate-free and jointly of size `|V|`, and stop.*  This file supplies
  the other three sides of that trade — extracting lists from a cover one is GIVEN, lifting a list
  into a layer of the prism, and the rung adjacencies that join layers — so that each of §5's cases
  is list surgery rather than walk construction.
-/

import BrualdiLean.Ledger

set_option autoImplicit false

namespace Brualdi.RealizationGraph.Prism

open SimpleGraph Brualdi.Ledger

/-! ## Realization-owned support for the prism proof

These declarations are copied from the generic product-balance and walk/list support used by the
original prism proof, so this module has no dependency on the tournament lane.
-/

variable {W₁ W₂ : Type} [Fintype W₁] [Fintype W₂] [DecidableEq W₁] [DecidableEq W₂]

/-- The xor colouring splits `W₁ × W₂` by whether the two coordinates agree.  Stated as a card
    identity because that is what both balance proofs below consume. -/
private theorem card_xor_false (colA : W₁ → Bool) (colB : W₂ → Bool) :
    Fintype.card {p : W₁ × W₂ // (Bool.xor (colA p.1) (colB p.2)) = false}
      = Fintype.card {x : W₁ // colA x = false} * Fintype.card {y : W₂ // colB y = false}
        + Fintype.card {x : W₁ // colA x = true} * Fintype.card {y : W₂ // colB y = true} := by
  classical
  simp only [Fintype.card_subtype]
  rw [← Finset.card_product, ← Finset.card_product, ← Finset.card_union_of_disjoint]
  · apply Finset.card_bij (fun p _ => (p.1, p.2))
    · rintro ⟨a, b⟩ hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [Finset.mem_union, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
        true_and]
      revert hp; cases colA a <;> cases colB b <;> simp
    · rintro ⟨a, b⟩ _ ⟨c, d⟩ _ h; exact h
    · rintro ⟨a, b⟩ hp
      simp only [Finset.mem_union, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
        true_and] at hp
      refine ⟨(a, b), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  · rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rw [h1.1] at h2; exact Bool.false_ne_true h2.1

private theorem card_xor_true (colA : W₁ → Bool) (colB : W₂ → Bool) :
    Fintype.card {p : W₁ × W₂ // (Bool.xor (colA p.1) (colB p.2)) = true}
      = Fintype.card {x : W₁ // colA x = false} * Fintype.card {y : W₂ // colB y = true}
        + Fintype.card {x : W₁ // colA x = true} * Fintype.card {y : W₂ // colB y = false} := by
  classical
  simp only [Fintype.card_subtype]
  rw [← Finset.card_product, ← Finset.card_product, ← Finset.card_union_of_disjoint]
  · apply Finset.card_bij (fun p _ => (p.1, p.2))
    · rintro ⟨a, b⟩ hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [Finset.mem_union, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
        true_and]
      revert hp; cases colA a <;> cases colB b <;> simp
    · rintro ⟨a, b⟩ _ ⟨c, d⟩ _ h; exact h
    · rintro ⟨a, b⟩ hp
      simp only [Finset.mem_union, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
        true_and] at hp
      refine ⟨(a, b), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  · rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rw [h1.1] at h2; exact Bool.false_ne_true h2.1
/-- **M3 — the prism of a bipartite graph is balanced**, and needs no balance hypothesis at all:
    each product colour takes one copy of each colour class of `A`, so both have exactly `|W₁|`
    vertices whatever `A`'s split. -/
theorem prism_equitable {A : SimpleGraph W₁} {colA : W₁ → Bool}
    (hA : IsProper2Coloring A colA) :
    IsEquitableBipartite (A □ (⊤ : SimpleGraph (Fin 2)))
      (fun p => Bool.xor (colA p.1) (decide (p.2 = 1))) := by
  have hB : IsProper2Coloring (⊤ : SimpleGraph (Fin 2)) (fun i : Fin 2 => decide (i = 1)) := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp_all
  refine ⟨fun p q hpq => boxProd_proper_color (fun u v h => hA u v h) (fun u v h => hB u v h)
    p q hpq, ?_⟩
  have hf := card_xor_false colA (fun i : Fin 2 => decide (i = 1))
  have ht := card_xor_true colA (fun i : Fin 2 => decide (i = 1))
  have h0 : Fintype.card {y : Fin 2 // (decide (y = 1)) = false} = 1 := by decide
  have h1 : Fintype.card {y : Fin 2 // (decide (y = 1)) = true} = 1 := by decide
  rw [h0, h1] at hf ht
  show Fintype.card {p : W₁ × Fin 2 // (Bool.xor (colA p.1) (decide (p.2 = 1))) = false}
      = Fintype.card {p : W₁ × Fin 2 // (Bool.xor (colA p.1) (decide (p.2 = 1))) = true}
  rw [hf, ht]
/-- **Isomorphic factors give isomorphic products.**  Mathlib has `boxProdComm` and `boxProdAssoc`
    but no congruence, and the decomposable case needs one: `IsDecomposableScore` hands over an
    isomorphism onto a product of INTERCHANGE graphs, and an order-two factor has to be replaced by
    `⊤ (Fin 2)` inside it before `prism_bipancyclic` will apply. -/
def boxProdCongr {α β α' β' : Type} {A : SimpleGraph α} {B : SimpleGraph β} {A' : SimpleGraph α'}
    {B' : SimpleGraph β'} (e₁ : A ≃g A') (e₂ : B ≃g B') : (A □ B) ≃g (A' □ B') where
  toEquiv := e₁.toEquiv.prodCongr e₂.toEquiv
  map_rel_iff' := by
    rintro ⟨a, b⟩ ⟨c, d⟩
    simp only [Equiv.prodCongr_apply, Prod.map_apply, SimpleGraph.boxProd_adj,
      RelIso.coe_fn_toEquiv, e₁.map_adj_iff, e₂.map_adj_iff, EmbeddingLike.apply_eq_iff_eq]

variable {V : Type} [Fintype V] [DecidableEq V]
/-- **G5 — an order-two factor IS `K₂`.**  `IsDecomposableScore` guarantees only `1 < card`, while
    `prism_paired_two` is stated about `A □ ⊤ (Fin 2)`; this is the bridge between them.  One edge
    is enough — with two vertices it is the only edge there is. -/
theorem nonempty_iso_top_two (G : SimpleGraph V) (hcard : Fintype.card V = 2)
    (hedge : ∃ u v, G.Adj u v) : Nonempty (G ≃g (⊤ : SimpleGraph (Fin 2))) := by
  classical
  obtain ⟨u, v, huv⟩ := hedge
  have hne : u ≠ v := G.ne_of_adj huv
  -- the two endpoints exhaust the vertex set, so any two distinct vertices ARE those two
  have hfull : ({u, v} : Finset V) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton, hcard]
  have hmem : ∀ x : V, x = u ∨ x = v := by
    intro x
    have : x ∈ ({u, v} : Finset V) := by rw [hfull]; exact Finset.mem_univ x
    simpa using this
  have hadj : ∀ a b : V, a ≠ b → G.Adj a b := by
    intro a b hab
    rcases hmem a with rfl | rfl <;> rcases hmem b with rfl | rfl
    · exact absurd rfl hab
    · exact huv
    · exact huv.symm
    · exact absurd rfl hab
  refine ⟨⟨Fintype.equivFinOfCardEq hcard, ?_⟩⟩
  intro a b
  simp only [SimpleGraph.top_adj, ne_eq, Equiv.apply_eq_iff_eq]
  exact ⟨fun h => hadj a b h, fun h => G.ne_of_adj h⟩

omit [Fintype V] [DecidableEq V] in
/-- **G6 — OP2 survives a global colour complement.**  Needed where `parityColor` has to be matched
    against the product's xor colouring after transporting across a decomposition isomorphism: the
    two agree up to a constant, and `OppositeDemand` asks only that each prescribed pair DIFFERS. -/
theorem pairedKDPC_xor_const {G : SimpleGraph V} {col : V → Bool} {k : ℕ} (c : Bool)
    (h : IsPairedKDPCForOpposite G col k) :
    IsPairedKDPCForOpposite G (fun v => Bool.xor c (col v)) k := by
  intro s t hd
  refine h s t ⟨fun i => ?_, hd.2.1, hd.2.2.1, hd.2.2.2⟩
  have := hd.1 i
  cases c <;> cases hx : col (s i) <;> cases hy : col (t i) <;> simp_all

/-! ## The paired side's bases and bookkeeping

`pairedKDPC_xor_const` above says OP2 survives a global complement.  For a CONNECTED graph that is
the whole story — a proper 2-colouring is determined up to complement — so OP2 does not depend on
WHICH proper colouring is used, and the assembly never has to match colourings by hand. -/

/-- **OP2 does not depend on the choice of proper 2-colouring**, for a connected graph.  This is
    what removes every colouring side-condition from the general-`s` induction: the decomposition
    isomorphism transports SOME proper colouring, and this says any other will do. -/
theorem pairedKDPC_of_proper2 {G : SimpleGraph V} {col col' : V → Bool} {k : ℕ}
    (hconn : G.Connected) (hc : IsProper2Coloring G col) (hc' : IsProper2Coloring G col')
    (h : IsPairedKDPCForOpposite G col k) : IsPairedKDPCForOpposite G col' k := by
  rcases proper2Coloring_eq_or_flip hconn hc' hc with heq | hflip
  · intro s t hd
    exact h s t ⟨fun i => by rw [← heq, ← heq]; exact hd.1 i, hd.2.1, hd.2.2.1, hd.2.2.2⟩
  · have := pairedKDPC_xor_const (G := G) (col := col) (k := k) true h
    intro s t hd
    refine this s t ⟨fun i => ?_, hd.2.1, hd.2.2.1, hd.2.2.2⟩
    have h1 := hd.1 i
    rw [hflip, hflip] at h1
    simpa using h1

/-- `CT₂` is `K₂`: two permutations of `Fin 2`, and they differ by a transposition. -/
theorem ct2_iso_top : Nonempty (CompleteTranspositionGraph 2 ≃g (⊤ : SimpleGraph (Fin 2))) := by
  classical
  refine nonempty_iso_top_two _ (by rw [Fintype.card_perm, Fintype.card_fin]; rfl)
    ⟨1, Equiv.swap 0 1, ?_⟩
  refine SimpleGraph.fromRel_adj .. |>.mpr ⟨by decide, Or.inl ?_⟩
  exact ⟨0, 1, by decide, by decide⟩

/-- **`Q₂ = C₄` has OP2 — the all-`K₂` base of the paired induction**, and it comes from the
    FLAGSHIP rather than from a fresh finite check.  `hypercube_ctProduct_paired_two` already gives
    OP2 for every hypercube in the CT-product encoding, proved from foundations; `CTProductGraph
    [2,2]` is `CT₂ □ CT₂`, and `CT₂` is `K₂`.  Reuse-first: the alternative was a second witness
    table for a graph the flagship already covers.

    Stated for an ARBITRARY proper 2-colouring, which is what the caller has after transporting
    `parityColor` across a decomposition isomorphism. -/
theorem c4_paired_two (col : Fin 2 × Fin 2 → Bool)
    (hc : IsProper2Coloring ((⊤ : SimpleGraph (Fin 2)) □ (⊤ : SimpleGraph (Fin 2))) col) :
    IsPairedKDPCForOpposite ((⊤ : SimpleGraph (Fin 2)) □ (⊤ : SimpleGraph (Fin 2))) col 2 := by
  classical
  obtain ⟨e2⟩ := ct2_iso_top
  -- `CTProductGraph [2,2] = CT₂ □ CT₂ ≃g K₂ □ K₂`
  have ebig : ((⊤ : SimpleGraph (Fin 2)) □ (⊤ : SimpleGraph (Fin 2)))
      ≃g CTProductGraph [2, 2] := (boxProdCongr e2 e2).symm
  have hCT : IsPairedKDPCForOpposite (CTProductGraph [2, 2]) (CTProductColor [2, 2]) 2 :=
    hypercube_ctProduct_paired_two [2, 2] (by simp) (by decide)
  have hpull : IsPairedKDPCForOpposite ((⊤ : SimpleGraph (Fin 2)) □ (⊤ : SimpleGraph (Fin 2)))
      (fun v => CTProductColor [2, 2] (ebig v)) 2 :=
    pairedKDPC_iso ebig _ _ (fun _ => rfl) hCT
  have hconn : ((⊤ : SimpleGraph (Fin 2)) □ (⊤ : SimpleGraph (Fin 2))).Connected :=
    (SimpleGraph.connected_top (V := Fin 2)).boxProd (SimpleGraph.connected_top (V := Fin 2))
  refine pairedKDPC_of_proper2 hconn ?_ hc hpull
  have hprod : IsProper2Coloring (CTProductGraph [2, 2]) (CTProductColor [2, 2]) :=
    (ctProduct_equitable_aux [2, 2] (by simp) (by decide)).1
  intro u v huv
  exact hprod _ _ (ebig.map_adj_iff.mpr huv)

/-- **The transfer that removes all colouring bookkeeping from the assembly.**  Move OP2 back along
    a decomposition isomorphism AND onto the colouring the conclusion actually names, in one step.
    Both halves are needed together: the isomorphism delivers OP2 for the pulled-back colouring,
    which is proper but is not syntactically `parityColor`, and for a connected graph that
    difference is at most a global complement. -/
theorem pairedTwo_transfer {V' : Type} [Fintype V'] [DecidableEq V'] {G : SimpleGraph V}
    {H : SimpleGraph V'} {col : V → Bool} {colH : V' → Bool} {k : ℕ} (e : G ≃g H) (hconn : G.Connected) (hc : IsProper2Coloring G col)
    (hcH : IsProper2Coloring H colH) (h : IsPairedKDPCForOpposite H colH k) :
    IsPairedKDPCForOpposite G col k :=
  pairedKDPC_of_proper2 hconn (fun _ _ huv => hcH _ _ (e.map_adj_iff.mpr huv)) hc
    (pairedKDPC_iso e _ _ (fun _ => rfl) h)

/-! ## Turning chained vertex lists into paired covers -/

variable {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Walk along a list of vertices starting at `a`, if every consecutive pair is adjacent. -/
def walkOfList (a : V) : List V → Option ((b : V) × G.Walk a b)
  | [] => some ⟨a, SimpleGraph.Walk.nil⟩
  | b :: rest =>
      if h : G.Adj a b then
        (walkOfList b rest).map fun p => ⟨p.1, SimpleGraph.Walk.cons h p.2⟩
      else none

omit [DecidableEq V] in
/-- The walk built from `l` has support `a :: l`. -/
theorem support_walkOfList (a : V) (l : List V) {b : V} {w : G.Walk a b}
    (h : walkOfList G a l = some ⟨b, w⟩) : w.support = a :: l := by
  induction l generalizing a b w with
  | nil =>
      simp only [walkOfList, Option.some.injEq] at h
      obtain ⟨rfl, hw⟩ := Sigma.mk.injEq .. ▸ h
      subst hw
      simp
  | cons c rest ih =>
      simp only [walkOfList] at h
      split at h
      · rename_i hadj
        cases hrec : walkOfList G c rest with
        | none => simp [hrec] at h
        | some p =>
            rw [hrec] at h
            simp only [Option.map_some, Option.some.injEq] at h
            obtain ⟨rfl, hw⟩ := Sigma.mk.injEq .. ▸ h
            subst hw
            simpa using ih c hrec
      · simp at h

/-- Decidable check that `l`, read from `a`, walks to `b`.  Defined THROUGH `walkOfList` so that a
    passing check yields the walk itself with no gap to bridge. -/
def walksTo (a b : V) (l : List V) : Bool :=
  match walkOfList G a l with
  | some p => decide (p.1 = b)
  | none => false

/-- A passing check produces the walk, with its support pinned to the list. -/
theorem exists_walk_of_walksTo {a b : V} {l : List V} (h : walksTo G a b l = true) :
    ∃ w : G.Walk a b, w.support = a :: l := by
  unfold walksTo at h
  cases hw : walkOfList G a l with
  | none => rw [hw] at h; simp at h
  | some p =>
      rw [hw] at h
      simp only [decide_eq_true_eq] at h
      subst h
      exact ⟨p.2, support_walkOfList G a l hw⟩

variable [Fintype V]

/-- The full certificate check for one paired-2 demand: two lists with the prescribed heads, each
    walking to its prescribed target, jointly duplicate-free and of total length `|V|`.  Nodup on
    the
    concatenation gives BOTH `IsPath` on each side and disjointness between them; the length then
    gives spanning. -/
def coversDemand (a₁ b₁ a₂ b₂ : V) (p q : List V) : Bool :=
  (p.head? == some a₁) && (q.head? == some a₂) &&
  walksTo G a₁ b₁ p.tail && walksTo G a₂ b₂ q.tail &&
  decide (p ++ q).Nodup && ((p ++ q).length == Fintype.card V)

theorem isPairedDPC_of_coversDemand {a₁ b₁ a₂ b₂ : V} {p q : List V}
    (h : coversDemand G a₁ b₁ a₂ b₂ p q = true) :
    Brualdi.Ledger.IsPairedDPC G 2 ![a₁, a₂] ![b₁, b₂] := by
  simp only [coversDemand, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hp0, hq0⟩, hw1⟩, hw2⟩, hnd⟩, hlen⟩ := h
  obtain ⟨w₁, hs₁⟩ := exists_walk_of_walksTo G hw1
  obtain ⟨w₂, hs₂⟩ := exists_walk_of_walksTo G hw2
  have hp : a₁ :: p.tail = p := by
    cases p with
    | nil => simp at hp0
    | cons x xs => simp at hp0; simp [hp0]
  have hq : a₂ :: q.tail = q := by
    cases q with
    | nil => simp at hq0
    | cons x xs => simp at hq0; simp [hq0]
  rw [hp] at hs₁
  rw [hq] at hs₂
  have hndp : p.Nodup := (List.nodup_append.mp hnd).1
  have hndq : q.Nodup := (List.nodup_append.mp hnd).2.1
  have hdisj := (List.nodup_append.mp hnd).2.2
  have hspan : ∀ x : V, x ∈ p ++ q := by
    intro x
    have hcard : (p ++ q).toFinset.card = Fintype.card V := by
      rw [List.toFinset_card_of_nodup hnd, hlen]
    have : (p ++ q).toFinset = Finset.univ := Finset.eq_univ_of_card _ hcard
    have hx : x ∈ (p ++ q).toFinset := this ▸ Finset.mem_univ x
    simpa using hx
  refine ⟨fun i => match i with | 0 => w₁ | 1 => w₂, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa [SimpleGraph.Walk.isPath_def, hs₁] using hndp
    · simpa [SimpleGraph.Walk.isPath_def, hs₂] using hndq
  · intro x
    rcases List.mem_append.mp (hspan x) with hx | hx
    · exact ⟨0, by simpa [hs₁] using hx⟩
    · exact ⟨1, by simpa [hs₂] using hx⟩
  · intro i j hij x hx
    obtain ⟨hxi, hxj⟩ := hx
    fin_cases i <;> fin_cases j
    · exact hij rfl
    · exact hdisj x (by simpa [hs₁] using hxi) x (by simpa [hs₂] using hxj) rfl
    · exact hdisj x (by simpa [hs₁] using hxj) x (by simpa [hs₂] using hxi) rfl
    · exact hij rfl

/-! ## From chained vertex lists to a paired cover

`Sec5`'s fibration layer states its runs as `List.IsChain G.Adj` vertex lists, and everything a
skeleton assembles arrives in that form.  These two turn such lists into `IsPairedDPC` without the
caller ever touching `SimpleGraph.Walk` — which is the whole interface a weld or portal argument
needs from this file. -/

/-- The join between list-level chaining and the walk checker. -/
theorem walksTo_of_isChain : ∀ (l : List V) (a b : V),
    (a :: l).IsChain G.Adj → (a :: l).getLast? = some b → walksTo G a b l = true
  | [], a, b, _, hlast => by
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      simp [walksTo, walkOfList]
  | c :: rest, a, b, hchain, hlast => by
      have hadj : G.Adj a c := by
        cases hchain with
        | cons_cons h _ => exact h
      have hrest : (c :: rest).IsChain G.Adj := by
        cases hchain with
        | cons_cons _ h => exact h
      have hlast' : (c :: rest).getLast? = some b := by
        rwa [List.getLast?_cons_cons] at hlast
      have ih := walksTo_of_isChain rest c b hrest hlast'
      unfold walksTo at ih ⊢
      cases hw : walkOfList G c rest with
      | none => rw [hw] at ih; simp at ih
      | some pw =>
          rw [hw] at ih
          simp only [decide_eq_true_eq] at ih
          simp [walkOfList, hadj, hw, ih]

/-- **The assembly theorem.**  Two chained vertex lists with prescribed ends, jointly duplicate-free
    and jointly of size `|V|`, ARE a spanning paired cover.

    This is the interface every skeleton construction should target: produce two chained lists and
    stop.  Nothing downstream of a fibration argument needs to build a `Walk` by hand. -/
theorem isPairedDPC_of_chains {a₁ b₁ a₂ b₂ : V} {p q : List V}
    (hp : (a₁ :: p).IsChain G.Adj) (hq : (a₂ :: q).IsChain G.Adj)
    (hpl : (a₁ :: p).getLast? = some b₁) (hql : (a₂ :: q).getLast? = some b₂)
    (hnd : ((a₁ :: p) ++ (a₂ :: q)).Nodup)
    (hlen : ((a₁ :: p) ++ (a₂ :: q)).length = Fintype.card V) :
    Brualdi.Ledger.IsPairedDPC G 2 ![a₁, a₂] ![b₁, b₂] := by
  refine isPairedDPC_of_coversDemand G (p := a₁ :: p) (q := a₂ :: q) ?_
  have h1 : walksTo G a₁ b₁ p = true := walksTo_of_isChain G p a₁ b₁ hp hpl
  have h2 : walksTo G a₂ b₂ q = true := walksTo_of_isChain G q a₂ b₂ hq hql
  simp only [coversDemand, h1, h2, List.head?_cons, List.tail_cons, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq, and_true, true_and]
  exact ⟨by simpa using hnd, by simpa using hlen⟩

/-! ## Symmetries of a paired-2 demand

  A certificate table only needs ONE representative per demand up to these symmetries.  Expanding
  them in the generated data instead was measured and rejected: at V = 14 it grew the table from 882
  rows to 7056 and the definition alone went from 29 s to over 3 min while still exhausting the
  recursion limit, and V = 24 would need ~70 000 rows.  Doing the symmetry once, here, is what makes
  the canonical tables sufficient at every base size. -/

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
/-- Reversing the first thread. -/
theorem isPairedDPC2_reverse_fst {a₁ b₁ a₂ b₂ : V}
    (h : Brualdi.Ledger.IsPairedDPC G 2 ![a₁, a₂] ![b₁, b₂]) :
    Brualdi.Ledger.IsPairedDPC G 2 ![b₁, a₂] ![a₁, b₂] := by
  obtain ⟨P, hpath, hspan, hdisj⟩ := h
  refine ⟨fun i => match i with | 0 => (P 0).reverse | 1 => P 1, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · simpa using (hpath 0).reverse
    · simpa using hpath 1
  · intro x
    obtain ⟨i, hi⟩ := hspan x
    fin_cases i
    · exact ⟨0, by simpa [SimpleGraph.Walk.support_reverse] using hi⟩
    · exact ⟨1, by simpa using hi⟩
  · intro i j hij x hx
    obtain ⟨hxi, hxj⟩ := hx
    refine hdisj i j hij x ⟨?_, ?_⟩ <;> fin_cases i <;> fin_cases j <;>
      simp_all [SimpleGraph.Walk.support_reverse]

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
/-- Reversing the second thread. -/
theorem isPairedDPC2_reverse_snd {a₁ b₁ a₂ b₂ : V}
    (h : Brualdi.Ledger.IsPairedDPC G 2 ![a₁, a₂] ![b₁, b₂]) :
    Brualdi.Ledger.IsPairedDPC G 2 ![a₁, b₂] ![b₁, a₂] := by
  obtain ⟨P, hpath, hspan, hdisj⟩ := h
  refine ⟨fun i => match i with | 0 => P 0 | 1 => (P 1).reverse, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · simpa using hpath 0
    · simpa using (hpath 1).reverse
  · intro x
    obtain ⟨i, hi⟩ := hspan x
    fin_cases i
    · exact ⟨0, by simpa using hi⟩
    · exact ⟨1, by simpa [SimpleGraph.Walk.support_reverse] using hi⟩
  · intro i j hij x hx
    obtain ⟨hxi, hxj⟩ := hx
    refine hdisj i j hij x ⟨?_, ?_⟩ <;> fin_cases i <;> fin_cases j <;>
      simp_all [SimpleGraph.Walk.support_reverse]

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
/-- Exchanging the two threads. -/
theorem isPairedDPC2_swap {a₁ b₁ a₂ b₂ : V}
    (h : Brualdi.Ledger.IsPairedDPC G 2 ![a₁, a₂] ![b₁, b₂]) :
    Brualdi.Ledger.IsPairedDPC G 2 ![a₂, a₁] ![b₂, b₁] := by
  obtain ⟨P, hpath, hspan, hdisj⟩ := h
  refine ⟨fun i => match i with | 0 => P 1 | 1 => P 0, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · simpa using hpath 1
    · simpa using hpath 0
  · intro x
    obtain ⟨i, hi⟩ := hspan x
    fin_cases i
    · exact ⟨1, by simpa using hi⟩
    · exact ⟨0, by simpa using hi⟩
  · intro i j hij x hx
    obtain ⟨hxi, hxj⟩ := hx
    fin_cases i <;> fin_cases j
    · exact hij rfl
    · exact hdisj 1 0 (by decide) x ⟨by simpa using hxi, by simpa using hxj⟩
    · exact hdisj 0 1 (by decide) x ⟨by simpa using hxi, by simpa using hxj⟩
    · exact hij rfl

/-! ## Transport along a graph automorphism

The lever that makes an ORBIT certificate possible: one cover per orbit of demands rather than one
per demand.  At V = 24 that is 49 rows instead of 8,712, and at V = 48 the canonical route does not
fit at all.

It must be PER-DEMAND.  `Thm15.pairedKDPC_iso` transports the whole `IsPairedKDPCForOpposite`
predicate along an isomorphism, which is a tautology when the isomorphism is an automorphism of the
same graph — it says `G` has the property iff `G` does. What is needed instead is that a cover for
ONE demand yields a cover for its image, so that a single stored cover serves a whole orbit. -/

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
/-- A paired DPC for a demand gives one for the image demand, under any automorphism. -/
theorem isPairedDPC_map {k : ℕ} {s t : Fin k → V} (e : G ≃g G)
    (h : Brualdi.Ledger.IsPairedDPC G k s t) :
    Brualdi.Ledger.IsPairedDPC G k (fun i => e (s i)) (fun i => e (t i)) := by
  obtain ⟨P, hpath, hspan, hdisj⟩ := h
  refine ⟨fun i => (P i).map e.toHom, ?_, ?_, ?_⟩
  · intro i
    exact SimpleGraph.Walk.map_isPath_of_injective e.toEquiv.injective (hpath i)
  · intro x
    obtain ⟨i, hi⟩ := hspan (e.symm x)
    refine ⟨i, ?_⟩
    have hmem : e (e.symm x) ∈ ((P i).map e.toHom).support := by
      rw [SimpleGraph.Walk.support_map]
      exact List.mem_map_of_mem hi
    simpa using hmem
  · intro i j hij x hx
    obtain ⟨hxi, hxj⟩ := hx
    rw [SimpleGraph.Walk.support_map] at hxi hxj
    obtain ⟨y, hy, hey⟩ := List.mem_map.mp hxi
    obtain ⟨z, hz, hez⟩ := List.mem_map.mp hxj
    have hyz : y = z := by
      have h' : e.toHom y = e.toHom z := hey.trans hez.symm
      simpa using h'
    subst hyz
    exact hdisj i j hij y ⟨hy, hz⟩

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
/-- The `k = 2` form, in the `![·, ·]` shape the certificates use. -/
theorem isPairedDPC2_map (e : G ≃g G) {a₁ b₁ a₂ b₂ : V}
    (h : Brualdi.Ledger.IsPairedDPC G 2 ![a₁, a₂] ![b₁, b₂]) :
    Brualdi.Ledger.IsPairedDPC G 2 ![e a₁, e a₂] ![e b₁, e b₂] := by
  have h2 := isPairedDPC_map G e h
  have hs : (fun i => e (![a₁, a₂] i)) = ![e a₁, e a₂] := by funext i; fin_cases i <;> rfl
  have ht : (fun i => e (![b₁, b₂] i)) = ![e b₁, e b₂] := by funext i; fin_cases i <;> rfl
  rwa [hs, ht] at h2

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
/-- **The form an orbit certificate consumes.**  A cover for the ORBIT REPRESENTATIVE `e · d` yields
    one for `d` itself, by transporting back along `e.symm`.  So the table stores one cover per
    orbit, and each demand names the automorphism that carries it to its representative. -/
theorem isPairedDPC2_of_rep (e : G ≃g G) {a₁ b₁ a₂ b₂ : V}
    (h : Brualdi.Ledger.IsPairedDPC G 2 ![e a₁, e a₂] ![e b₁, e b₂]) :
    Brualdi.Ledger.IsPairedDPC G 2 ![a₁, a₂] ![b₁, b₂] := by
  have h2 := isPairedDPC2_map G e.symm h
  simpa using h2

/-! ## Prism paths -/

open SimpleGraph Brualdi.Ledger

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Extraction: a cover you are GIVEN, as lists

The exact inverse of `isPairedDPC_of_chains`, and the direction §5 needs at every step: each case
applies `OP2(H)` inside a layer and then operates on the resulting paths. -/

/-- A path's support is a chained, duplicate-free list running between its ends. -/
theorem support_chain {G : SimpleGraph W} {a b : W} (p : G.Walk a b) (hp : p.IsPath) :
    p.support.IsChain G.Adj ∧ p.support.Nodup ∧ p.support.head? = some a
      ∧ p.support.getLast? = some b :=
  ⟨p.isChain_adj_support, hp.support_nodup, by rw [List.head?_eq_head p.support_ne_nil]; simp,
    by rw [List.getLast?_eq_getLast_of_ne_nil p.support_ne_nil]; simp⟩

/-- **A paired cover, read back as two lists.**  Chained, with the prescribed ends, jointly
    duplicate-free and jointly exhausting the vertex set — which is precisely the hypothesis list of
    `isPairedDPC_of_chains`, so the two are inverse. -/
theorem chains_of_isPairedDPC {G : SimpleGraph W} {s t : Fin 2 → W}
    (h : IsPairedDPC G 2 s t) :
    ∃ P Q : List W, P.IsChain G.Adj ∧ Q.IsChain G.Adj ∧
      P.head? = some (s 0) ∧ P.getLast? = some (t 0) ∧
      Q.head? = some (s 1) ∧ Q.getLast? = some (t 1) ∧
      (P ++ Q).Nodup ∧ (∀ x : W, x ∈ P ++ Q) := by
  classical
  obtain ⟨p, hpath, hcover, hdisj⟩ := h
  refine ⟨(p 0).support, (p 1).support, (p 0).isChain_adj_support, (p 1).isChain_adj_support,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.head?_eq_head (p 0).support_ne_nil]; simp
  · rw [List.getLast?_eq_getLast_of_ne_nil (p 0).support_ne_nil]; simp
  · rw [List.head?_eq_head (p 1).support_ne_nil]; simp
  · rw [List.getLast?_eq_getLast_of_ne_nil (p 1).support_ne_nil]; simp
  · rw [List.nodup_append]
    refine ⟨(hpath 0).support_nodup, (hpath 1).support_nodup, ?_⟩
    intro a ha b hb hab
    subst hab
    exact hdisj 0 1 (by decide) a ⟨ha, hb⟩
  · intro x
    obtain ⟨i, hi⟩ := hcover x
    fin_cases i
    · exact List.mem_append_left _ hi
    · exact List.mem_append_right _ hi

/-- **A Hamilton path, as a list.**  `IsHamLaceable` gives one between any two opposite-coloured
    vertices; §5 uses it in the lower layer in cases `r = 0` and `r = 1`. -/
theorem hamPath_list {G : SimpleGraph W} {col : W → Bool} (h : IsHamLaceable G col)
    {a b : W} (hab : col a ≠ col b) :
    ∃ L : List W, L.IsChain G.Adj ∧ L.Nodup ∧ L.head? = some a ∧ L.getLast? = some b ∧
      (∀ x : W, x ∈ L) := by
  obtain ⟨p, hp⟩ := h a b hab
  obtain ⟨hchain, hnd, hh, hl⟩ := support_chain p hp.isPath
  exact ⟨p.support, hchain, hnd, hh, hl, fun x => hp.mem_support x⟩

/-! ## Layers and rungs

`H⁰` and `H¹` are the two copies; the edge `u⁰u¹` is the **rung** at `u`.  Every construction in §5
is: lay lists into layers, then join them through rungs. -/

/-- Lift a list into layer `i` of the prism. -/
def inLayer (i : Fin 2) (L : List W) : List (W × Fin 2) := L.map (fun w => (w, i))

@[simp] theorem inLayer_nil (i : Fin 2) : inLayer (W := W) i [] = [] := rfl

@[simp] theorem inLayer_length (i : Fin 2) (L : List W) :
    (inLayer i L).length = L.length := List.length_map ..

@[simp] theorem inLayer_head? (i : Fin 2) (L : List W) :
    (inLayer i L).head? = L.head?.map (fun w => (w, i)) := List.head?_map ..

@[simp] theorem inLayer_getLast? (i : Fin 2) (L : List W) :
    (inLayer i L).getLast? = L.getLast?.map (fun w => (w, i)) := List.getLast?_map ..

@[simp] theorem mem_inLayer {i : Fin 2} {L : List W} {p : W × Fin 2} :
    p ∈ inLayer i L ↔ p.1 ∈ L ∧ p.2 = i := by
  constructor
  · intro h
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
    exact ⟨hw, rfl⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨a, b⟩ := p
    cases h2
    exact List.mem_map.mpr ⟨a, h1, rfl⟩

theorem inLayer_nodup {i : Fin 2} {L : List W} (h : L.Nodup) : (inLayer i L).Nodup :=
  h.map (fun _ _ hab => (Prod.mk.injEq .. ▸ hab).1)

/-- A chain stays a chain inside a layer: a layer edge moves only the `H`-coordinate. -/
theorem inLayer_chain {A : SimpleGraph W} {i : Fin 2} {L : List W} (h : L.IsChain A.Adj) :
    (inLayer i L).IsChain (A □ (⊤ : SimpleGraph (Fin 2))).Adj :=
  List.isChain_map_of_isChain _ (fun _ _ hab => SimpleGraph.boxProd_adj.mpr (Or.inl ⟨hab, rfl⟩)) h

/-- **The rung at `u`.**  The one edge of the prism that changes layer, and the only way §5's
    constructions cross between them. -/
theorem rung_adj {A : SimpleGraph W} (u : W) {i j : Fin 2} (hij : i ≠ j) :
    (A □ (⊤ : SimpleGraph (Fin 2))).Adj (u, i) (u, j) :=
  SimpleGraph.boxProd_adj.mpr (Or.inr ⟨by simpa using hij, rfl⟩)

/-- Two layers are disjoint, which is what makes every splice in §5 legal without further
    bookkeeping.  Stated on the lifted lists because that is where it gets used. -/
theorem inLayer_disjoint {i j : Fin 2} (hij : i ≠ j) (L M : List W) :
    ∀ p, p ∈ inLayer i L → p ∈ inLayer j M → False := by
  intro p hp hq
  have h1 := (mem_inLayer.mp hp).2
  have h2 := (mem_inLayer.mp hq).2
  exact hij (h1.symm.trans h2)

/-- The prism's colouring, in the form (5.1) uses: `χ(u^i) = χ_H(u) xor i`. -/
def prismColor (colA : W → Bool) (p : W × Fin 2) : Bool :=
  Bool.xor (colA p.1) (decide (p.2 = 1))

@[simp] theorem prismColor_zero (colA : W → Bool) (u : W) :
    prismColor colA (u, 0) = colA u := by simp [prismColor]

@[simp] theorem prismColor_one (colA : W → Bool) (u : W) :
    prismColor colA (u, 1) = !colA u := by simp [prismColor]

/-- **(5.1) read backwards, in the layer-preserving direction.**  Two vertices in the SAME layer are
    opposite in the prism exactly when their projections are opposite in `H`. -/
theorem prismColor_ne_same_layer {colA : W → Bool} {u v : W} (i : Fin 2) :
    (prismColor colA (u, i) ≠ prismColor colA (v, i)) ↔ colA u ≠ colA v := by
  fin_cases i <;> simp <;> cases colA u <;> cases colA v <;> simp

/-- **(5.5), the case that drives `r = 1` and `r = 2`.**  Two vertices in DIFFERENT layers are
    opposite in the prism exactly when their projections have the SAME colour in `H` — which is why
    a layer-crossing prescribed pair projects to a same-coloured pair, and why §5 has to choose a
    connector rather than reusing the terminals. -/
theorem prismColor_ne_cross {colA : W → Bool} {u v : W} {i j : Fin 2} (hij : i ≠ j) :
    (prismColor colA (u, i) ≠ prismColor colA (v, j)) ↔ colA u = colA v := by
  fin_cases i <;> fin_cases j <;> simp_all

/-- A duplicate-free list that meets every vertex has length `|V|`.  The bridge from "these two
    paths cover `H`" to the length obligation of `isPairedDPC_of_chains`. -/
theorem length_of_nodup_cover {L : List W} (hnd : L.Nodup) (hcov : ∀ x : W, x ∈ L) :
    L.length = Fintype.card W := by
  classical
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  exact Finset.eq_univ_of_forall fun x => List.mem_toFinset.mpr (hcov x)

@[simp] theorem inLayer_append (i : Fin 2) (L M : List W) :
    inLayer i (L ++ M) = inLayer i L ++ inLayer i M := List.map_append ..


/-! ## Connectors

Cases `r = 1` and `r = 2` both have to CHOOSE a vertex of a prescribed colour outside a small
forbidden set — §5 calls these connectors, and they exist for one reason: balance plus the order
bound makes each colour class big enough.  This is the first place `hEq`'s cardinality half is
genuinely spent; up to here only its properness half was used. -/

/-- Balance, as a statement about one colour class: it is exactly half the graph. -/
theorem card_colorClass {A : SimpleGraph W} {colA : W → Bool} (hEq : IsEquitableBipartite A colA)
    (c : Bool) : 2 * (Finset.univ.filter (fun v : W => colA v = c)).card = Fintype.card W := by
  classical
  have key := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset W)) (p := fun v => colA v = true)
  rw [Finset.card_univ] at key
  have hF : (Finset.univ.filter (fun v : W => colA v = false)).card
      = Fintype.card {v : W // colA v = false} := by simp [Fintype.card_subtype]
  have hT : (Finset.univ.filter (fun v : W => colA v = true)).card
      = Fintype.card {v : W // colA v = true} := by simp [Fintype.card_subtype]
  have hNot : (Finset.univ.filter (fun v : W => ¬ (colA v = true))).card
      = (Finset.univ.filter (fun v : W => colA v = false)).card := by
    congr 1; apply Finset.filter_congr; intro x _; simp [Bool.not_eq_true]
  rw [hNot, hF, hT, hEq.2] at key
  cases c
  · rw [hF, hEq.2]; omega
  · rw [hT]; omega

/-- **A connector exists.**  A vertex of the prescribed colour outside any forbidden set that is
    small enough — `2 * (|S| + 1) ≤ |W|` says the colour class has more than `|S|` members.

    `r = 1` uses it with `|S| = 1` (avoid whichever of `a, b` shares the colour), which needs only
    `4 ≤ |W|`; `r = 2`'s main branch uses it with `|S| = 2`, which is where "each colour class has at
    least three vertices" comes from and why `|W| = 4` has to be treated separately. -/
theorem exists_connector {A : SimpleGraph W} {colA : W → Bool} (hEq : IsEquitableBipartite A colA)
    (c : Bool) (S : Finset W) (h : 2 * (S.card + 1) ≤ Fintype.card W) :
    ∃ z : W, colA z = c ∧ z ∉ S := by
  classical
  by_contra hcon
  push Not at hcon
  have hsub : Finset.univ.filter (fun v : W => colA v = c) ⊆ S :=
    fun x hx => hcon x (by simpa using hx)
  have hle := Finset.card_le_card hsub
  have := card_colorClass hEq c
  omega

/-! ## Case `r = 0` of Theorem 5.1 — all four terminals in one layer

§5's first case, and the one that fixes the pattern for the others.  `OP2(H)` covers the FULL layer
`H¹`; one of its two paths is opened at its first edge, and a Hamilton path of `H⁰` is spliced in
between the two rungs there.

Two small departures from the prose, both simplifications:

* The prose says "at least one of those paths contains an edge, because both of its endpoints are
  distinct and opposite-coloured" and then picks such an edge.  Here the FIRST edge of the first
  path always works, so no search is needed — a path whose ends are opposite-coloured has at least
  two entries, and its first two are adjacent.
* The prose splices in the middle and then argues the prescribed endpoints are retained.  Splicing
  at the front makes that automatic: the new list still begins with the same vertex, because
  `x¹` is the old head. -/

/-- **The `r = 0` construction.**  Given the upper layer's cover as lists `x :: y :: B` and `Q`, and
    a Hamilton listing `R` of `H` from `x` to `y`, the two output lists. -/
private def r0Left (x y : W) (B R : List W) : List (W × Fin 2) :=
  (x, 1) :: (inLayer 0 R ++ inLayer 1 (y :: B))

private theorem r0Left_chain {A : SimpleGraph W} {x y : W} {B R : List W}
    (hP : (x :: y :: B).IsChain A.Adj) (hR : R.IsChain A.Adj)
    (hRh : R.head? = some x) (hRl : R.getLast? = some y) :
    (r0Left x y B R).IsChain (A □ (⊤ : SimpleGraph (Fin 2))).Adj := by
  have hy : (y :: B).IsChain A.Adj := hP.tail
  have hseg : (inLayer 0 R ++ inLayer 1 (y :: B)).IsChain
      (A □ (⊤ : SimpleGraph (Fin 2))).Adj := by
    refine List.IsChain.append (inLayer_chain hR) (inLayer_chain hy) ?_
    intro a ha b hb
    rw [inLayer_getLast?, hRl] at ha
    rw [inLayer_head?, List.head?_cons] at hb
    simp only [Option.map_some, Option.mem_def, Option.some.injEq] at ha hb
    subst ha; subst hb
    exact rung_adj y (by decide)
  refine List.isChain_cons.mpr ⟨fun b hb => ?_, hseg⟩
  rw [List.head?_append_of_ne_nil] at hb
  · rw [inLayer_head?, hRh] at hb
    simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hb
    subst hb
    exact rung_adj x (by decide)
  · simp only [ne_eq, inLayer, List.map_eq_nil_iff]
    intro hcon
    rw [hcon] at hRh
    simp at hRh

/-- The demand, projected out of a single layer.  All four terminals share a layer, so the
    projection is injective on them and (5.1) makes the colour condition transfer verbatim. -/
private theorem project_demand {colA : W → Bool} {s t : Fin 2 → W × Fin 2}
    (hd : OppositeDemand (prismColor colA) s t)
    (hs : ∀ i, (s i).2 = 1) (ht : ∀ i, (t i).2 = 1) :
    OppositeDemand colA (fun i => (s i).1) (fun i => (t i).1) := by
  obtain ⟨hcol, hsinj, htinj, hst⟩ := hd
  have hlift : ∀ (u v : W × Fin 2), u.2 = v.2 → u.1 = v.1 → u = v :=
    fun u v h2 h1 => Prod.ext h1 h2
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j hij => ?_, fun i j => ?_⟩
  · have := hcol i
    rw [show s i = ((s i).1, (1 : Fin 2)) from (hs i) ▸ rfl,
        show t i = ((t i).1, (1 : Fin 2)) from (ht i) ▸ rfl] at this
    exact (prismColor_ne_same_layer (colA := colA) 1).mp this
  · exact hsinj (hlift _ _ ((hs i).trans (hs j).symm) hij)
  · exact htinj (hlift _ _ ((ht i).trans (ht j).symm) hij)
  · exact fun hcon => hst i j (hlift _ _ ((hs i).trans (ht j).symm) hcon)

/-- **★ Case `r = 0` of `SECTION5_PRODUCT_LIFTING_COMPLETE.md` Theorem 5.1.**  All four prescribed
    terminals lie in one layer. -/
theorem prism_r0 {A : SimpleGraph W} {colA : W → Bool}
    (hEq : IsEquitableBipartite A colA) (h4 : 4 ≤ Fintype.card W)
    (hpA : IsPairedKDPCForOpposite A colA 2)
    (s t : Fin 2 → W × Fin 2) (hd : OppositeDemand (prismColor colA) s t)
    (hs : ∀ i, (s i).2 = 1) (ht : ∀ i, (t i).2 = 1) :
    IsPairedDPC (A □ (⊤ : SimpleGraph (Fin 2))) 2 s t := by
  classical
  obtain ⟨P, Q, hPc, hQc, hPh, hPl, hQh, hQl, hnd, hcov⟩ :=
    chains_of_isPairedDPC (hpA _ _ (project_demand hd hs ht))
  -- `P` has at least two entries: its ends are distinct, being opposite-coloured
  have hends : (s 0).1 ≠ (t 0).1 := by
    have := (project_demand hd hs ht).2.2.2 0 0
    simpa using this
  obtain ⟨x, rest, hPeq⟩ : ∃ x rest, P = x :: rest := by
    cases P with
    | nil => simp at hPh
    | cons a l => exact ⟨a, l, rfl⟩
  obtain ⟨y, B, hreq⟩ : ∃ y B, rest = y :: B := by
    cases rest with
    | nil =>
        exfalso
        rw [hPeq] at hPh hPl
        simp only [List.head?_cons, Option.some.injEq] at hPh
        simp only [List.getLast?_singleton, Option.some.injEq] at hPl
        exact hends (hPh.symm.trans hPl)
    | cons c l => exact ⟨c, l, rfl⟩
  subst hPeq; subst hreq
  have hxy : A.Adj x y := by
    have := List.isChain_cons.mp hPc
    exact this.1 y rfl
  -- the lower layer's Hamilton path, from `x` to `y`
  obtain ⟨R, hRc, hRnd, hRh, hRl, hRcov⟩ :=
    hamPath_list (paired_two_opposite_to_hamLaceable hEq hpA h4) (hEq.1 x y hxy)
  obtain ⟨q₀, Qt, hQeq⟩ : ∃ q₀ Qt, Q = q₀ :: Qt := by
    cases Q with
    | nil => simp at hQh
    | cons a l => exact ⟨a, l, rfl⟩
  subst hQeq
  -- the ends, in the layer the demand lives in
  have hsx : s 0 = (x, 1) := Prod.ext (by simpa using hPh.symm) (hs 0)
  have hsq : s 1 = (q₀, 1) := Prod.ext (by simpa using hQh.symm) (hs 1)
  have hty : (y :: B).getLast? = some (t 0).1 := by simpa using hPl
  have htq : (q₀ :: Qt).getLast? = some (t 1).1 := by simpa using hQl
  -- the two output lists, and the three obligations of `isPairedDPC_of_chains`
  have hnodup : ((x, (1 : Fin 2)) :: (inLayer 0 R ++ inLayer 1 (y :: B))
      ++ inLayer 1 (q₀ :: Qt)).Nodup := by
    have hmerge : (inLayer 0 R ++ inLayer 1 (y :: B)) ++ inLayer 1 (q₀ :: Qt)
        = inLayer 0 R ++ inLayer 1 ((y :: B) ++ (q₀ :: Qt)) := by
      rw [inLayer_append, List.append_assoc]
    rw [List.cons_append, List.nodup_cons, hmerge]
    have htail : ((y :: B) ++ (q₀ :: Qt)).Nodup := by
      have := hnd
      rw [List.cons_append, List.nodup_cons] at this
      exact this.2
    constructor
    · intro hcon
      rcases List.mem_append.mp hcon with h0 | h1
      · have h2 : (1 : Fin 2) = 0 := (mem_inLayer.mp h0).2
        exact absurd h2 (by decide)
      · have hx : x ∈ (y :: B) ++ (q₀ :: Qt) := (mem_inLayer.mp h1).1
        rw [List.cons_append, List.nodup_cons] at hnd
        exact hnd.1 hx
    · rw [List.nodup_append]
      refine ⟨inLayer_nodup hRnd, inLayer_nodup htail, ?_⟩
      intro a ha b hb hab
      subst hab
      exact inLayer_disjoint (i := 0) (j := 1) (by decide) _ _ a ha hb
  have hlen : ((x, (1 : Fin 2)) :: (inLayer 0 R ++ inLayer 1 (y :: B))
      ++ inLayer 1 (q₀ :: Qt)).length = Fintype.card (W × Fin 2) := by
    have hPQ : ((x :: y :: B) ++ (q₀ :: Qt)).length = Fintype.card W :=
      length_of_nodup_cover hnd hcov
    have hR : R.length = Fintype.card W := length_of_nodup_cover hRnd hRcov
    simp only [List.cons_append, List.length_cons, List.length_append, inLayer_length,
      Fintype.card_prod, Fintype.card_fin] at *
    omega
  -- assemble, then re-fold `![s 0, s 1]` into `s`
  have ht0 : ((t 0).1, (1 : Fin 2)) = t 0 := Prod.ext rfl (ht 0).symm
  have ht1 : ((t 1).1, (1 : Fin 2)) = t 1 := Prod.ext rfl (ht 1).symm
  have hQchain : ((q₀, (1 : Fin 2)) :: inLayer 1 Qt).IsChain
      (A □ (⊤ : SimpleGraph (Fin 2))).Adj := inLayer_chain (A := A) (i := 1) hQc
  have hkey := isPairedDPC_of_chains (G := A □ (⊤ : SimpleGraph (Fin 2)))
    (a₁ := (x, (1 : Fin 2))) (b₁ := t 0) (a₂ := (q₀, (1 : Fin 2))) (b₂ := t 1)
    (p := inLayer 0 R ++ inLayer 1 (y :: B)) (q := inLayer 1 Qt)
    (r0Left_chain hPc hRc hRh hRl)
    hQchain
    (by
      rw [List.getLast?_cons, List.getLast?_append_of_ne_nil, inLayer_getLast?, hty]
      · rw [Option.map_some, ht0]; simp
      · simp only [ne_eq, inLayer, List.map_eq_nil_iff]; simp)
    (by
      show (inLayer 1 (q₀ :: Qt)).getLast? = some (t 1)
      rw [inLayer_getLast?, htq, Option.map_some, ht1])
    hnodup hlen
  have hsfun : s = ![(x, (1 : Fin 2)), (q₀, (1 : Fin 2))] := by
    funext i; fin_cases i
    · simpa using hsx
    · simpa using hsq
  have htfun : t = ![t 0, t 1] := by funext i; fin_cases i <;> rfl
  rw [hsfun, htfun]
  exact hkey

/-! ## Case `r = 1` of Theorem 5.1 — one terminal downstairs

Prose lines 383–400.  **Simpler than `r = 0`, not harder**: nothing is spliced.  A Hamilton path of
the lower layer runs `u` to the connector `z`, the upper layer's `OP2` cover starts one of its paths
at `z`, and the two are joined at the single rung `z⁰z¹`.  The other upper path is untouched.

Stated for the NORMALIZED demand — the lower terminal is the first pair's source.  §5 arranges that
by "naming the unique lower-layer terminal `u⁰`", which in Lean is
`isPairedDPC2_reverse_fst`/`_snd`/`_swap` from `WalkOfList`. -/

/-- **★ Case `r = 1`, normalized.**  `(u⁰, v¹)` and `(a¹, b¹)`. -/
theorem prism_r1_core {A : SimpleGraph W} {colA : W → Bool}
    (hEq : IsEquitableBipartite A colA) (h4 : 4 ≤ Fintype.card W)
    (hpA : IsPairedKDPCForOpposite A colA 2) (u v a b : W)
    (hd : OppositeDemand (prismColor colA)
      ![(u, (0 : Fin 2)), (a, (1 : Fin 2))] ![(v, (1 : Fin 2)), (b, (1 : Fin 2))]) :
    IsPairedDPC (A □ (⊤ : SimpleGraph (Fin 2))) 2
      ![(u, (0 : Fin 2)), (a, (1 : Fin 2))] ![(v, (1 : Fin 2)), (b, (1 : Fin 2))] := by
  classical
  obtain ⟨hcol, hsinj, htinj, hst⟩ := hd
  -- (5.5): the CROSSING pair projects to a SAME-coloured pair, the confined one to opposite
  have huv : colA u = colA v := by
    have := hcol 0
    simp only [Matrix.cons_val_zero] at this
    exact (prismColor_ne_cross (colA := colA) (by decide : (0 : Fin 2) ≠ 1)).mp this
  have hab : colA a ≠ colA b := by
    have := hcol 1
    simp only [Matrix.cons_val_one, Matrix.head_cons] at this
    exact (prismColor_ne_same_layer (colA := colA) 1).mp this
  have hva : v ≠ a := by
    intro hcon
    exact hst 1 0 (by simp [hcon])
  have hvb : v ≠ b := by
    intro hcon
    have hEqt : (![(v, (1 : Fin 2)), (b, (1 : Fin 2))] : Fin 2 → W × Fin 2) 0
        = ![(v, (1 : Fin 2)), (b, (1 : Fin 2))] 1 := by simp [hcon]
    exact absurd (htinj hEqt) (by decide)
  -- the connector: colour opposite `u`, avoiding whichever of `a`, `b` shares it.  Exactly one
  -- does, because `colA a ≠ colA b` — which is why avoiding ONE vertex suffices and `4 ≤ |W|`
  -- rather than `6 ≤ |W|` is enough here.
  set c : Bool := !(colA u) with hcdef
  obtain ⟨w, hwa, hwb, -⟩ : ∃ w : W, (colA a = c → w = a) ∧ (colA a ≠ c → w = b) ∧ colA w = c := by
    by_cases hac : colA a = c
    · exact ⟨a, fun _ => rfl, fun h => absurd hac h, hac⟩
    · refine ⟨b, fun h => absurd h hac, fun _ => rfl, ?_⟩
      cases hca : colA a <;> cases hcb : colA b <;> cases hc : c <;> simp_all
  obtain ⟨z, hzc, hzw⟩ := exists_connector hEq c {w} (by simpa using h4)
  have hza : z ≠ a := by
    by_cases hac : colA a = c
    · rw [hwa hac] at hzw; simpa using hzw
    · intro hcon; exact hac (hcon ▸ hzc)
  have hzb : z ≠ b := by
    by_cases hbc : colA b = c
    · have hac : colA a ≠ c := fun h => hab (h.trans hbc.symm)
      rw [hwb hac] at hzw; simpa using hzw
    · intro hcon; exact hbc (hcon ▸ hzc)
  have hzu : colA z ≠ colA u := by rw [hzc, hcdef]; cases colA u <;> simp
  have hzv : colA z ≠ colA v := by rw [← huv]; exact hzu
  -- the lower layer's Hamilton path `u` to `z`, and the upper layer's cover
  obtain ⟨L, hLc, hLnd, hLh, hLl, hLcov⟩ :=
    hamPath_list (paired_two_opposite_to_hamLaceable hEq hpA h4) hzu.symm
  have hzvne : z ≠ v := fun h => hzv (by rw [h])
  have habne : a ≠ b := fun h => hab (by rw [h])
  have hdemand : OppositeDemand colA ![z, a] ![v, b] := by
    refine ⟨fun i => ?_, fun i j hij => ?_, fun i j hij => ?_, fun i j => ?_⟩
    · fin_cases i
      · exact hzv
      · exact hab
    · fin_cases i <;> fin_cases j <;> simp_all
    · fin_cases i <;> fin_cases j <;> simp_all
    · fin_cases i <;> fin_cases j <;> simp_all [hva.symm]
  obtain ⟨P, Q, hPc, hQc, hPh, hPl, hQh, hQl, hnd, hcov⟩ :=
    chains_of_isPairedDPC (hpA ![z, a] ![v, b] hdemand)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hPh hPl hQh hQl
  -- the two lists: the lower Hamilton path joined to the first upper path at the rung `z⁰z¹`,
  -- and the second upper path untouched
  obtain ⟨Lt, hLeq⟩ : ∃ Lt, L = u :: Lt := by
    cases L with
    | nil => simp at hLh
    | cons d l =>
        simp only [List.head?_cons, Option.some.injEq] at hLh
        exact ⟨l, by rw [hLh]⟩
  obtain ⟨Qt, hQeq⟩ : ∃ Qt, Q = a :: Qt := by
    cases Q with
    | nil => simp at hQh
    | cons d l =>
        simp only [List.head?_cons, Option.some.injEq] at hQh
        exact ⟨l, by rw [hQh]⟩
  subst hLeq; subst hQeq
  have hPne : inLayer 1 P ≠ [] := by
    simp only [ne_eq, inLayer, List.map_eq_nil_iff]
    intro hcon; rw [hcon] at hPh; simp at hPh
  have hchain1 : ((u, (0 : Fin 2)) :: (inLayer 0 Lt ++ inLayer 1 P)).IsChain
      (A □ (⊤ : SimpleGraph (Fin 2))).Adj := by
    have h1 : (inLayer 0 (u :: Lt) ++ inLayer 1 P).IsChain (A □ (⊤ : SimpleGraph (Fin 2))).Adj := by
      refine List.IsChain.append (inLayer_chain hLc) (inLayer_chain hPc) ?_
      intro α hα β hβ
      rw [inLayer_getLast?, hLl] at hα
      rw [inLayer_head?, hPh] at hβ
      simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hα hβ
      subst hα; subst hβ
      exact rung_adj z (by decide)
    exact h1
  have hnodup : ((u, (0 : Fin 2)) :: (inLayer 0 Lt ++ inLayer 1 P)
      ++ inLayer 1 (a :: Qt)).Nodup := by
    have hmerge : inLayer 0 (u :: Lt) ++ (inLayer 1 P ++ inLayer 1 (a :: Qt))
        = inLayer 0 (u :: Lt) ++ inLayer 1 (P ++ (a :: Qt)) := by rw [inLayer_append]
    show (inLayer 0 (u :: Lt) ++ inLayer 1 P ++ inLayer 1 (a :: Qt)).Nodup
    rw [List.append_assoc, hmerge, List.nodup_append]
    refine ⟨inLayer_nodup hLnd, inLayer_nodup hnd, ?_⟩
    intro α hα β hβ hαβ
    subst hαβ
    exact inLayer_disjoint (i := 0) (j := 1) (by decide) _ _ α hα hβ
  have hlen : ((u, (0 : Fin 2)) :: (inLayer 0 Lt ++ inLayer 1 P)
      ++ inLayer 1 (a :: Qt)).length = Fintype.card (W × Fin 2) := by
    have hL : (u :: Lt).length = Fintype.card W := length_of_nodup_cover hLnd hLcov
    have hPQ : (P ++ (a :: Qt)).length = Fintype.card W := length_of_nodup_cover hnd hcov
    simp only [List.cons_append, List.length_cons, List.length_append, inLayer_length,
      Fintype.card_prod, Fintype.card_fin] at *
    omega
  refine isPairedDPC_of_chains (G := A □ (⊤ : SimpleGraph (Fin 2)))
    (a₁ := (u, (0 : Fin 2))) (b₁ := (v, (1 : Fin 2)))
    (a₂ := (a, (1 : Fin 2))) (b₂ := (b, (1 : Fin 2)))
    (p := inLayer 0 Lt ++ inLayer 1 P) (q := inLayer 1 Qt)
    hchain1 (inLayer_chain (A := A) (i := 1) hQc) ?_ ?_ hnodup hlen
  · rw [List.getLast?_cons, List.getLast?_append_of_ne_nil _ hPne, inLayer_getLast?, hPl]
    simp
  · show (inLayer 1 (a :: Qt)).getLast? = some (b, (1 : Fin 2))
    rw [inLayer_getLast?, hQl]
    rfl

/-! ## Case `r = 2`, branch `c = 0` — one whole pair in each layer

Prose lines 411–414.  The cheapest branch in §5, and the cheapest here: a Hamilton path per layer,
nothing joined and nothing spliced.  Both confined pairs are opposite-coloured in `H` by (5.1), so
laceability supplies both paths directly, and the layers are disjoint by construction. -/

/-- **★ Case `r = 2`, `c = 0`.**  `(u⁰, v⁰)` and `(a¹, b¹)` — neither pair crosses. -/
theorem prism_r2_c0_core {A : SimpleGraph W} {colA : W → Bool}
    (hEq : IsEquitableBipartite A colA) (h4 : 4 ≤ Fintype.card W)
    (hpA : IsPairedKDPCForOpposite A colA 2) (u v a b : W)
    (hd : OppositeDemand (prismColor colA)
      ![(u, (0 : Fin 2)), (a, (1 : Fin 2))] ![(v, (0 : Fin 2)), (b, (1 : Fin 2))]) :
    IsPairedDPC (A □ (⊤ : SimpleGraph (Fin 2))) 2
      ![(u, (0 : Fin 2)), (a, (1 : Fin 2))] ![(v, (0 : Fin 2)), (b, (1 : Fin 2))] := by
  classical
  obtain ⟨hcol, -, -, -⟩ := hd
  have huv : colA u ≠ colA v := by
    have := hcol 0
    simp only [Matrix.cons_val_zero] at this
    exact (prismColor_ne_same_layer (colA := colA) 0).mp this
  have hab : colA a ≠ colA b := by
    have := hcol 1
    simp only [Matrix.cons_val_one, Matrix.head_cons] at this
    exact (prismColor_ne_same_layer (colA := colA) 1).mp this
  have hlace := paired_two_opposite_to_hamLaceable hEq hpA h4
  obtain ⟨L, hLc, hLnd, hLh, hLl, hLcov⟩ := hamPath_list hlace huv
  obtain ⟨M, hMc, hMnd, hMh, hMl, hMcov⟩ := hamPath_list hlace hab
  obtain ⟨Lt, hLeq⟩ : ∃ Lt, L = u :: Lt := by
    cases L with
    | nil => simp at hLh
    | cons d l =>
        simp only [List.head?_cons, Option.some.injEq] at hLh
        exact ⟨l, by rw [hLh]⟩
  obtain ⟨Mt, hMeq⟩ : ∃ Mt, M = a :: Mt := by
    cases M with
    | nil => simp at hMh
    | cons d l =>
        simp only [List.head?_cons, Option.some.injEq] at hMh
        exact ⟨l, by rw [hMh]⟩
  subst hLeq; subst hMeq
  refine isPairedDPC_of_chains (G := A □ (⊤ : SimpleGraph (Fin 2)))
    (a₁ := (u, (0 : Fin 2))) (b₁ := (v, (0 : Fin 2)))
    (a₂ := (a, (1 : Fin 2))) (b₂ := (b, (1 : Fin 2)))
    (p := inLayer 0 Lt) (q := inLayer 1 Mt)
    (inLayer_chain (A := A) (i := 0) hLc) (inLayer_chain (A := A) (i := 1) hMc) ?_ ?_ ?_ ?_
  · show (inLayer 0 (u :: Lt)).getLast? = some (v, (0 : Fin 2))
    rw [inLayer_getLast?, hLl]; rfl
  · show (inLayer 1 (a :: Mt)).getLast? = some (b, (1 : Fin 2))
    rw [inLayer_getLast?, hMl]; rfl
  · show (inLayer 0 (u :: Lt) ++ inLayer 1 (a :: Mt)).Nodup
    rw [List.nodup_append]
    refine ⟨inLayer_nodup hLnd, inLayer_nodup hMnd, ?_⟩
    intro α hα β hβ hαβ
    subst hαβ
    exact inLayer_disjoint (i := 0) (j := 1) (by decide) _ _ α hα hβ
  · show (inLayer 0 (u :: Lt) ++ inLayer 1 (a :: Mt)).length = Fintype.card (W × Fin 2)
    have hL : (u :: Lt).length = Fintype.card W := length_of_nodup_cover hLnd hLcov
    have hM : (a :: Mt).length = Fintype.card W := length_of_nodup_cover hMnd hMcov
    simp only [List.length_append, inLayer_length, Fintype.card_prod, Fintype.card_fin] at *
    omega

/-! ## Case `r = 2`, branch `c = 2` — both pairs cross

Prose lines 416–451.  Two connectors, `OP2(H)` applied in EACH layer, and the four resulting paths
joined in pairs through the rungs at `x` and `y`.

**The construction is separated from the CHOICE of connectors**, deliberately.  §5 runs them
together, but they have different costs: the construction below needs only that suitable connectors
exist, while choosing them is where the order hypothesis actually bites — sub-case `χ(u) = χ(a)`
needs each colour class to have two vertices (so `4 ≤ |W|` suffices), sub-case `χ(u) ≠ χ(a)` needs
three (so `6 ≤ |W|`), and `|W| = 4` in that sub-case is what forces `H = C₄` and the `Q₃` check.
Keeping them apart means the `Q₃` work does not have to be redone inside the construction. -/

/-- **★ Case `r = 2`, `c = 2`, given the connectors.**  `(u⁰, v¹)` and `(a⁰, b¹)`, joined through
    the rungs at `x` and `y`.  The hypotheses are exactly (5.9) plus the distinctness that makes
    both demands of (5.10) legal. -/
theorem prism_r2_c2_core {A : SimpleGraph W} {colA : W → Bool}
    (hpA : IsPairedKDPCForOpposite A colA 2) (u v a b x y : W)
    (huv : colA u = colA v) (hab : colA a = colA b)
    (hxu : colA x ≠ colA u) (hya : colA y ≠ colA a)
    (hua : u ≠ a) (hvb : v ≠ b) (hxy : x ≠ y)
    (hxa : x ≠ a) (hyu : y ≠ u) (hxb : x ≠ b) (hyv : y ≠ v) :
    IsPairedDPC (A □ (⊤ : SimpleGraph (Fin 2))) 2
      ![(u, (0 : Fin 2)), (a, (0 : Fin 2))] ![(v, (1 : Fin 2)), (b, (1 : Fin 2))] := by
  classical
  -- the colour bookkeeping: (5.9) plus (5.8) gives every disequality (5.10) needs
  have hxv : colA x ≠ colA v := by rw [← huv]; exact hxu
  have hyb : colA y ≠ colA b := by rw [← hab]; exact hya
  have hxune : x ≠ u := fun h => hxu (by rw [h])
  have hxvne : x ≠ v := fun h => hxv (by rw [h])
  have hyane : y ≠ a := fun h => hya (by rw [h])
  have hybne : y ≠ b := fun h => hyb (by rw [h])
  -- the lower layer's cover: `(u, x)` and `(a, y)`
  obtain ⟨P₀, Q₀, hP₀c, hQ₀c, hP₀h, hP₀l, hQ₀h, hQ₀l, hnd₀, hcov₀⟩ :=
    chains_of_isPairedDPC (hpA ![u, a] ![x, y] (by
      refine ⟨fun i => ?_, fun i j hij => ?_, fun i j hij => ?_, fun i j => ?_⟩
      · fin_cases i
        · exact fun h => hxu h.symm
        · exact fun h => hya h.symm
      · fin_cases i <;> fin_cases j <;> simp_all
      · fin_cases i <;> fin_cases j <;> simp_all
      · fin_cases i <;> fin_cases j <;>
          simp_all [hxune.symm, hyu.symm, hxa.symm, hyane.symm]))
  -- the upper layer's cover: `(x, v)` and `(y, b)`
  obtain ⟨P₁, Q₁, hP₁c, hQ₁c, hP₁h, hP₁l, hQ₁h, hQ₁l, hnd₁, hcov₁⟩ :=
    chains_of_isPairedDPC (hpA ![x, y] ![v, b] (by
      refine ⟨fun i => ?_, fun i j hij => ?_, fun i j hij => ?_, fun i j => ?_⟩
      · fin_cases i
        · exact hxv
        · exact hyb
      · fin_cases i <;> fin_cases j <;> simp_all
      · fin_cases i <;> fin_cases j <;> simp_all
      · fin_cases i <;> fin_cases j <;> simp_all))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hP₀h hP₀l hQ₀h hQ₀l hP₁h hP₁l hQ₁h hQ₁l
  obtain ⟨nd₀P, nd₀Q, dis₀⟩ := List.nodup_append.mp hnd₀
  obtain ⟨nd₁P, nd₁Q, dis₁⟩ := List.nodup_append.mp hnd₁
  obtain ⟨P₀t, hP₀eq⟩ : ∃ P₀t, P₀ = u :: P₀t := by
    cases P₀ with
    | nil => simp at hP₀h
    | cons d l =>
        simp only [List.head?_cons, Option.some.injEq] at hP₀h
        exact ⟨l, by rw [hP₀h]⟩
  obtain ⟨Q₀t, hQ₀eq⟩ : ∃ Q₀t, Q₀ = a :: Q₀t := by
    cases Q₀ with
    | nil => simp at hQ₀h
    | cons d l =>
        simp only [List.head?_cons, Option.some.injEq] at hQ₀h
        exact ⟨l, by rw [hQ₀h]⟩
  subst hP₀eq; subst hQ₀eq
  -- one rung-join, stated once and used for both output paths
  have joinChain : ∀ (S T : List W) (m : W), S.IsChain A.Adj → T.IsChain A.Adj →
      S.getLast? = some m → T.head? = some m →
      (inLayer 0 S ++ inLayer 1 T).IsChain (A □ (⊤ : SimpleGraph (Fin 2))).Adj := by
    intro S T m hS hT hSl hTh
    refine List.IsChain.append (inLayer_chain hS) (inLayer_chain hT) ?_
    intro α hα β hβ
    rw [inLayer_getLast?, hSl] at hα
    rw [inLayer_head?, hTh] at hβ
    simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hα hβ
    subst hα; subst hβ
    exact rung_adj m (by decide)
  have hne1 : inLayer 1 P₁ ≠ [] := by
    simp only [ne_eq, inLayer, List.map_eq_nil_iff]
    intro hcon; rw [hcon] at hP₁h; simp at hP₁h
  have hne2 : inLayer 1 Q₁ ≠ [] := by
    simp only [ne_eq, inLayer, List.map_eq_nil_iff]
    intro hcon; rw [hcon] at hQ₁h; simp at hQ₁h
  refine isPairedDPC_of_chains (G := A □ (⊤ : SimpleGraph (Fin 2)))
    (a₁ := (u, (0 : Fin 2))) (b₁ := (v, (1 : Fin 2)))
    (a₂ := (a, (0 : Fin 2))) (b₂ := (b, (1 : Fin 2)))
    (p := inLayer 0 P₀t ++ inLayer 1 P₁) (q := inLayer 0 Q₀t ++ inLayer 1 Q₁)
    (joinChain _ _ x hP₀c hP₁c hP₀l hP₁h) (joinChain _ _ y hQ₀c hQ₁c hQ₀l hQ₁h) ?_ ?_ ?_ ?_
  · rw [List.getLast?_cons, List.getLast?_append_of_ne_nil _ hne1, inLayer_getLast?, hP₁l]; simp
  · rw [List.getLast?_cons, List.getLast?_append_of_ne_nil _ hne2, inLayer_getLast?, hQ₁l]; simp
  · show ((inLayer 0 (u :: P₀t) ++ inLayer 1 P₁) ++ (inLayer 0 (a :: Q₀t) ++ inLayer 1 Q₁)).Nodup
    have same : ∀ (S T : List W) (i : Fin 2), (∀ α ∈ S, ∀ β ∈ T, α ≠ β) →
        ∀ α ∈ inLayer i S, ∀ β ∈ inLayer i T, α ≠ β := by
      intro S T i hd α hα β hβ hαβ
      subst hαβ
      exact hd α.1 (mem_inLayer.mp hα).1 α.1 (mem_inLayer.mp hβ).1 rfl
    have layerSplit : ∀ (S T : List W), S.Nodup → T.Nodup →
        (inLayer 0 S ++ inLayer 1 T).Nodup := by
      intro S T hS hT
      rw [List.nodup_append]
      refine ⟨inLayer_nodup hS, inLayer_nodup hT, ?_⟩
      intro α hα β hβ hαβ
      subst hαβ
      exact inLayer_disjoint (i := 0) (j := 1) (by decide) _ _ α hα hβ
    rw [List.nodup_append]
    refine ⟨layerSplit _ _ nd₀P nd₁P, layerSplit _ _ nd₀Q nd₁Q, ?_⟩
    intro α hα β hβ hαβ
    subst hαβ
    rcases List.mem_append.mp hα with h0 | h1 <;> rcases List.mem_append.mp hβ with g0 | g1
    · exact same _ _ 0 dis₀ α h0 α g0 rfl
    · exact inLayer_disjoint (i := 0) (j := 1) (by decide) _ _ α h0 g1
    · exact inLayer_disjoint (i := 1) (j := 0) (by decide) _ _ α h1 g0
    · exact same _ _ 1 dis₁ α h1 α g1 rfl
  · show ((inLayer 0 (u :: P₀t) ++ inLayer 1 P₁)
        ++ (inLayer 0 (a :: Q₀t) ++ inLayer 1 Q₁)).length = Fintype.card (W × Fin 2)
    have h0 : ((u :: P₀t) ++ (a :: Q₀t)).length = Fintype.card W :=
      length_of_nodup_cover hnd₀ hcov₀
    have h1 : (P₁ ++ Q₁).length = Fintype.card W := length_of_nodup_cover hnd₁ hcov₁
    simp only [List.cons_append, List.length_cons, List.length_append, inLayer_length,
      Fintype.card_prod, Fintype.card_fin] at *
    omega

/-! ## Choosing the connectors

§5's (5.9), separated from the construction it feeds.  Two sub-cases, and they cost differently:
when the two crossing pairs project to the SAME colour, both connectors live in the other class and
are automatically distinct from all four terminals, so two members suffice; when they project to
DIFFERENT colours, each connector must dodge a two-element set, so three are needed.

That second requirement is the whole reason `|W| = 4` is a separate case in §5. -/

/-- **★ Case `r = 2`, `c = 2`, connectors chosen.**  `6 ≤ |W|` covers both sub-cases; `4 ≤ |W|`
    covers only the same-colour one, which is where the `|W| = 4` split comes from. -/
theorem prism_r2_c2 {A : SimpleGraph W} {colA : W → Bool}
    (hEq : IsEquitableBipartite A colA) (h4 : 4 ≤ Fintype.card W)
    (hpA : IsPairedKDPCForOpposite A colA 2) (u v a b : W)
    (hd : OppositeDemand (prismColor colA)
      ![(u, (0 : Fin 2)), (a, (0 : Fin 2))] ![(v, (1 : Fin 2)), (b, (1 : Fin 2))])
    (hcase : colA u = colA a ∨ 6 ≤ Fintype.card W) :
    IsPairedDPC (A □ (⊤ : SimpleGraph (Fin 2))) 2
      ![(u, (0 : Fin 2)), (a, (0 : Fin 2))] ![(v, (1 : Fin 2)), (b, (1 : Fin 2))] := by
  classical
  obtain ⟨hcol, hsinj, htinj, -⟩ := hd
  -- (5.8): each CROSSING pair projects to a same-coloured pair
  have huv : colA u = colA v := by
    have := hcol 0
    simp only [Matrix.cons_val_zero] at this
    exact (prismColor_ne_cross (colA := colA) (by decide : (0 : Fin 2) ≠ 1)).mp this
  have hab : colA a = colA b := by
    have := hcol 1
    simp only [Matrix.cons_val_one, Matrix.head_cons] at this
    exact (prismColor_ne_cross (colA := colA) (by decide : (0 : Fin 2) ≠ 1)).mp this
  have hua : u ≠ a := by
    intro h
    have he : (![(u, (0 : Fin 2)), (a, (0 : Fin 2))] : Fin 2 → W × Fin 2) 0
        = ![(u, (0 : Fin 2)), (a, (0 : Fin 2))] 1 := by simp [h]
    exact absurd (hsinj he) (by decide)
  have hvb : v ≠ b := by
    intro h
    have he : (![(v, (1 : Fin 2)), (b, (1 : Fin 2))] : Fin 2 → W × Fin 2) 0
        = ![(v, (1 : Fin 2)), (b, (1 : Fin 2))] 1 := by simp [h]
    exact absurd (htinj he) (by decide)
  rcases hcase with hsame | hbig
  · -- both pairs project to the same colour: both connectors go in the OTHER class, and are
    -- distinct from all four terminals for free
    obtain ⟨x, hxc, -⟩ := exists_connector hEq (!colA u) ∅ (by simpa using by omega)
    obtain ⟨y, hyc, hyx⟩ := exists_connector hEq (!colA u) {x} (by simpa using h4)
    have hxu : colA x ≠ colA u := by rw [hxc]; cases colA u <;> simp
    have hya : colA y ≠ colA a := by rw [hyc, ← hsame]; cases colA u <;> simp
    refine prism_r2_c2_core hpA u v a b x y huv hab hxu hya hua hvb
      (fun h => hyx (by simp [h])) ?_ ?_ ?_ ?_
    · exact fun h => hxu (by rw [h, hsame])
    · exact fun h => hya (by rw [h, hsame])
    · exact fun h => hxu (by rw [h]; exact hab.symm.trans hsame.symm)
    · exact fun h => hya (by rw [h]; exact huv.symm.trans hsame)
  · -- different colours: each connector dodges a two-element set, so each class needs three
    by_cases hsame : colA u = colA a
    · obtain ⟨x, hxc, -⟩ := exists_connector hEq (!colA u) ∅ (by simpa using by omega)
      obtain ⟨y, hyc, hyx⟩ := exists_connector hEq (!colA u) {x} (by simpa using h4)
      have hxu : colA x ≠ colA u := by rw [hxc]; cases colA u <;> simp
      have hya : colA y ≠ colA a := by rw [hyc, ← hsame]; cases colA u <;> simp
      refine prism_r2_c2_core hpA u v a b x y huv hab hxu hya hua hvb
        (fun h => hyx (by simp [h])) ?_ ?_ ?_ ?_
      · exact fun h => hxu (by rw [h, hsame])
      · exact fun h => hya (by rw [h, hsame])
      · exact fun h => hxu (by rw [h]; exact hab.symm.trans hsame.symm)
      · exact fun h => hya (by rw [h]; exact huv.symm.trans hsame)
    · obtain ⟨x, hxc, hxS⟩ := exists_connector hEq (colA a) {a, b} (by
        refine le_trans ?_ hbig
        have : ({a, b} : Finset W).card ≤ 2 := Finset.card_insert_le .. |>.trans (by simp)
        omega)
      obtain ⟨y, hyc, hyS⟩ := exists_connector hEq (colA u) {u, v} (by
        refine le_trans ?_ hbig
        have : ({u, v} : Finset W).card ≤ 2 := Finset.card_insert_le .. |>.trans (by simp)
        omega)
      have hxu : colA x ≠ colA u := by rw [hxc]; exact fun h => hsame h.symm
      have hya : colA y ≠ colA a := by rw [hyc]; exact hsame
      have hxa : x ≠ a := fun h => hxS (by simp [h])
      have hxb : x ≠ b := fun h => hxS (by simp [h])
      have hyu : y ≠ u := fun h => hyS (by simp [h])
      have hyv : y ≠ v := fun h => hyS (by simp [h])
      exact prism_r2_c2_core hpA u v a b x y huv hab hxu hya hua hvb
        (fun h => hsame (by rw [← hxc, h, hyc])) hxa hyu hxb hyv

/-! ## The `|W| = 4` case

§5 lines 452–460.  This is where `c = 2`'s connectors run out: with colour classes of size two and
the two crossing pairs projecting to different colours, both classes are exhausted by the terminals.

§5's escape is to observe that `|W| = 4` FORCES `H = K_{2,2} = C₄`, and then to check the prism `Q₃`
directly.  The derivation of `K_{2,2}` uses `OP2` itself and is short; the `Q₃` check is where §5
enumerates five demand orbits, and that is the part worth not repeating — `Q₃` is a hypercube, so
the flagship already has it. -/

/-- **`|W| = 4` forces `H` complete bipartite** — §5 (5.11).  Pair `x` with `y` and the two leftover
    vertices with each other; a spanning two-path cover of four vertices splits `4 − 2 = 2` between
    two paths that each connect opposite colours and so each have positive length.  Both lengths are
    therefore one, which says `xy` is an edge — and `x`, `y` were arbitrary. -/
theorem complete_of_card_four {A : SimpleGraph W} {colA : W → Bool}
    (hEq : IsEquitableBipartite A colA) (hcard : Fintype.card W = 4)
    (hpA : IsPairedKDPCForOpposite A colA 2) :
    ∀ x y : W, colA x ≠ colA y → A.Adj x y := by
  classical
  intro x y hxy
  obtain ⟨x', hx'c, hx'⟩ := exists_connector hEq (colA x) {x} (by simp [hcard])
  obtain ⟨y', hy'c, hy'⟩ := exists_connector hEq (colA y) {y} (by simp [hcard])
  have hx'ne : x' ≠ x := by simpa using hx'
  have hy'ne : y' ≠ y := by simpa using hy'
  have hxy' : colA x ≠ colA y' := by rw [hy'c]; exact hxy
  have hx'y : colA x' ≠ colA y := by rw [hx'c]; exact hxy
  have hx'y' : colA x' ≠ colA y' := by rw [hx'c, hy'c]; exact hxy
  have hxyne : x ≠ y := fun h => hxy (by rw [h])
  have hxy'ne : x ≠ y' := fun h => hxy' (by rw [h])
  have hx'yne : x' ≠ y := fun h => hx'y (by rw [h])
  have hx'y'ne : x' ≠ y' := fun h => hx'y' (by rw [h])
  obtain ⟨P, Q, hPc, -, hPh, hPl, hQh, hQl, hnd, hcov⟩ :=
    chains_of_isPairedDPC (hpA ![x, x'] ![y, y'] (by
      refine ⟨fun i => ?_, fun i j hij => ?_, fun i j hij => ?_, fun i j => ?_⟩
      · fin_cases i
        · exact hxy
        · exact hx'y'
      · fin_cases i <;> fin_cases j <;> simp_all
      · fin_cases i <;> fin_cases j <;> simp_all
      · fin_cases i <;> fin_cases j <;> simp_all))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hPh hPl hQh hQl
  -- the two lengths add to four, and neither can be one, so both are two
  have hsum : P.length + Q.length = 4 := by
    have := length_of_nodup_cover hnd hcov
    rw [hcard] at this; simpa using this
  have hPtwo : 2 ≤ P.length := by
    rcases P with _ | ⟨p, _ | ⟨p', pr⟩⟩
    · simp at hPh
    · simp only [List.head?_cons, Option.some.injEq] at hPh
      simp only [List.getLast?_singleton, Option.some.injEq] at hPl
      exact absurd (hPh.symm.trans hPl) hxyne
    · simp
  have hQtwo : 2 ≤ Q.length := by
    rcases Q with _ | ⟨q, _ | ⟨q', qr⟩⟩
    · simp at hQh
    · simp only [List.head?_cons, Option.some.injEq] at hQh
      simp only [List.getLast?_singleton, Option.some.injEq] at hQl
      exact absurd (hQh.symm.trans hQl) hx'y'ne
    · simp
  have hPlen : P.length = 2 := by omega
  -- a two-entry list with those ends IS the edge
  rcases P with _ | ⟨p, _ | ⟨p', pr⟩⟩
  · simp at hPlen
  · simp at hPlen
  · have : pr = [] := by simpa using hPlen
    subst this
    simp only [List.head?_cons, Option.some.injEq] at hPh
    simp only [List.getLast?_cons, List.getLast?_singleton, Option.some.injEq] at hPl
    subst hPh
    simp only [Option.getD_some] at hPl
    subst hPl
    exact (List.isChain_cons.mp hPc).1 _ rfl


/-- In `⊤ □ ⊤` — that is, in `C₄` — adjacency is exactly "the XOR of the two coordinates differs".
    Which makes it complete bipartite for that colouring, the same shape as a `K_{2,2}`. -/
theorem boxTop_adj_iff_xor (a b : Fin 2 × Fin 2) :
    ((⊤ : SimpleGraph (Fin 2)) □ (⊤ : SimpleGraph (Fin 2))).Adj a b ↔
      (decide (a.1 ≠ a.2) ≠ decide (b.1 ≠ b.2)) := by
  obtain ⟨i, j⟩ := a
  obtain ⟨i', j'⟩ := b
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    simp [SimpleGraph.boxProd_adj]

/-- **`|W| = 4` gives `H ≅ C₄` outright.**  With `K_{2,2}` in hand the labelling is forced: read the
    four vertices round the cycle and they are the four bit-pairs, because in `⊤ □ ⊤` adjacency is
    "the two coordinates' XOR differs", and `H`'s adjacency is "the colours differ".

    Getting the ISOMORPHISM rather than another hand construction is what makes `|W| = 4` cost once
    instead of three times: the three configurations where `c = 2`'s connectors fail are handled
    together with every other demand, by transporting `Q₃` whole. -/
theorem iso_c4_of_card_four {A : SimpleGraph W} {colA : W → Bool}
    (hEq : IsEquitableBipartite A colA) (hcard : Fintype.card W = 4)
    (hcomp : ∀ x y : W, colA x ≠ colA y → A.Adj x y) :
    Nonempty (A ≃g ((⊤ : SimpleGraph (Fin 2)) □ (⊤ : SimpleGraph (Fin 2)))) := by
  classical
  obtain ⟨x₀, hx₀, -⟩ := exists_connector hEq false ∅ (by simp [hcard])
  obtain ⟨x₁, hx₁, hx₁ne⟩ := exists_connector hEq false {x₀} (by simp [hcard])
  obtain ⟨y₀, hy₀, -⟩ := exists_connector hEq true ∅ (by simp [hcard])
  obtain ⟨y₁, hy₁, hy₁ne⟩ := exists_connector hEq true {y₀} (by simp [hcard])
  have hx : x₁ ≠ x₀ := by simpa using hx₁ne
  have hy : y₁ ≠ y₀ := by simpa using hy₁ne
  have hxy : ∀ p q : W, colA p = false → colA q = true → p ≠ q := by
    intro p q hp hq hpq; rw [hpq, hq] at hp; exact Bool.false_ne_true hp.symm
  -- the four exhaust `W`
  have hall : ∀ w : W, w = x₀ ∨ w = x₁ ∨ w = y₀ ∨ w = y₁ := by
    have hcard4 : ({x₀, x₁, y₀, y₁} : Finset W).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hx.symm, hxy x₀ y₀ hx₀ hy₀, hxy x₀ y₁ hx₀ hy₁]),
        Finset.card_insert_of_notMem (by simp [hxy x₁ y₀ hx₁ hy₀, hxy x₁ y₁ hx₁ hy₁]),
        Finset.card_insert_of_notMem (by simp [hy.symm]), Finset.card_singleton]
    have := Finset.eq_univ_of_card _ (by rw [hcard4, hcard])
    intro w
    have hw : w ∈ ({x₀, x₁, y₀, y₁} : Finset W) := by rw [this]; exact Finset.mem_univ w
    simpa using hw
  -- the labelling, round the cycle `x₀ y₀ x₁ y₁`.  Rather than sixteen adjacency cases, note that
  -- BOTH graphs are "adjacent iff the colours differ" — `⊤ □ ⊤` for the XOR of its coordinates —
  -- so it is enough that `f` matches the two colourings, which is four cases.
  set f : W → Fin 2 × Fin 2 := fun w =>
    if w = x₀ then (0, 0) else if w = y₀ then (0, 1) else if w = x₁ then (1, 1) else (1, 0)
    with hf
  have hfx₀ : f x₀ = (0, 0) := by simp [hf]
  have hfy₀ : f y₀ = (0, 1) := by simp [hf, (hxy x₀ y₀ hx₀ hy₀).symm]
  have hfx₁ : f x₁ = (1, 1) := by simp [hf, hx, hxy x₁ y₀ hx₁ hy₀]
  have hfy₁ : f y₁ = (1, 0) := by
    simp [hf, (hxy x₀ y₁ hx₀ hy₁).symm, hy, (hxy x₁ y₁ hx₁ hy₁).symm]
  clear_value f
  clear hf
  have hxorf : ∀ w : W, decide ((f w).1 ≠ (f w).2) = colA w := by
    intro w
    rcases hall w with rfl | rfl | rfl | rfl
    · rw [hfx₀, hx₀]; rfl
    · rw [hfx₁, hx₁]; rfl
    · rw [hfy₀, hy₀]; rfl
    · rw [hfy₁, hy₁]; rfl
  have hinj : Function.Injective f := by
    intro p q hpq
    rcases hall p with rfl | rfl | rfl | rfl <;> rcases hall q with rfl | rfl | rfl | rfl <;>
      first
        | rfl
        | (exfalso
           rw [hfx₀] at hpq <;> skip
           exact absurd hpq (by simp_all))
        | (exfalso; simp only [hfx₀, hfy₀, hfx₁, hfy₁] at hpq; exact absurd hpq (by decide))
  refine ⟨⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr
    ⟨hinj, by simp [hcard]⟩), ?_⟩⟩
  intro p q
  show ((⊤ : SimpleGraph (Fin 2)) □ (⊤ : SimpleGraph (Fin 2))).Adj (f p) (f q) ↔ A.Adj p q
  rw [boxTop_adj_iff_xor, hxorf, hxorf]
  exact ⟨fun h => hcomp p q h, fun h => hEq.1 p q h⟩

/-- **`Q₃` has OP2, from the flagship.**  `CTProductGraph [2,2,2]` is `CT₂ □ (CT₂ □ CT₂)` and `CT₂`
    is `K₂`, so `hypercube_ctProduct_paired_two` delivers this from foundations.  §5 checks it by
    hand through five demand orbits; this is the same reuse `c4_paired_two` already made for `Q₂`,
    one dimension up.

    Stated for an ARBITRARY proper 2-colouring, which is what the caller has after transporting. -/
theorem q3_paired_two (col : (Fin 2 × Fin 2) × Fin 2 → Bool)
    (hc : IsProper2Coloring
      (((⊤ : SimpleGraph (Fin 2)) □ (⊤ : SimpleGraph (Fin 2))) □ (⊤ : SimpleGraph (Fin 2))) col) :
    IsPairedKDPCForOpposite
      (((⊤ : SimpleGraph (Fin 2)) □ (⊤ : SimpleGraph (Fin 2))) □ (⊤ : SimpleGraph (Fin 2)))
      col 2 := by
  classical
  obtain ⟨e2⟩ := ct2_iso_top
  have ebig : (((⊤ : SimpleGraph (Fin 2)) □ (⊤ : SimpleGraph (Fin 2))) □ (⊤ : SimpleGraph (Fin 2)))
      ≃g CTProductGraph [2, 2, 2] :=
    (SimpleGraph.boxProdAssoc _ _ _).trans (boxProdCongr e2.symm (boxProdCongr e2.symm e2.symm))
  have hCT : IsPairedKDPCForOpposite (CTProductGraph [2, 2, 2]) (CTProductColor [2, 2, 2]) 2 :=
    hypercube_ctProduct_paired_two [2, 2, 2] (by simp) (by decide)
  have hpull := pairedKDPC_iso ebig (fun v => CTProductColor [2, 2, 2] (ebig v))
    (CTProductColor [2, 2, 2]) (fun _ => rfl) hCT
  have hconn : (((⊤ : SimpleGraph (Fin 2)) □ (⊤ : SimpleGraph (Fin 2)))
      □ (⊤ : SimpleGraph (Fin 2))).Connected :=
    ((SimpleGraph.connected_top (V := Fin 2)).boxProd
      (SimpleGraph.connected_top (V := Fin 2))).boxProd (SimpleGraph.connected_top (V := Fin 2))
  refine pairedKDPC_of_proper2 hconn ?_ hc hpull
  have hprod : IsProper2Coloring (CTProductGraph [2, 2, 2]) (CTProductColor [2, 2, 2]) :=
    (ctProduct_equitable_aux [2, 2, 2] (by simp) (by decide)).1
  intro u v huv
  exact hprod _ _ (ebig.map_adj_iff.mpr huv)

/-- **★ The `|W| = 4` case of Theorem 5.1, whole.**  `H ≅ C₄`, so the prism is `Q₃` — every demand
    at once, not just the three where `c = 2`'s connectors fail. -/
theorem prism_paired_two_card_four {A : SimpleGraph W} {colA : W → Bool}
    (hEq : IsEquitableBipartite A colA) (hcard : Fintype.card W = 4)
    (hpA : IsPairedKDPCForOpposite A colA 2) :
    IsPairedKDPCForOpposite (A □ (⊤ : SimpleGraph (Fin 2))) (prismColor colA) 2 := by
  classical
  haveI : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨eA⟩ := iso_c4_of_card_four hEq hcard (complete_of_card_four hEq hcard hpA)
  have ebig : (A □ (⊤ : SimpleGraph (Fin 2)))
      ≃g (((⊤ : SimpleGraph (Fin 2)) □ (⊤ : SimpleGraph (Fin 2))) □ (⊤ : SimpleGraph (Fin 2))) :=
    boxProdCongr eA (SimpleGraph.Iso.refl)
  have hconnT : (((⊤ : SimpleGraph (Fin 2)) □ (⊤ : SimpleGraph (Fin 2)))
      □ (⊤ : SimpleGraph (Fin 2))).Connected :=
    ((SimpleGraph.connected_top (V := Fin 2)).boxProd
      (SimpleGraph.connected_top (V := Fin 2))).boxProd (SimpleGraph.connected_top (V := Fin 2))
  have hconn : (A □ (⊤ : SimpleGraph (Fin 2))).Connected := by
    refine ⟨ebig.preconnected_iff.mpr hconnT.preconnected⟩
  have hcolT : IsProper2Coloring
      (((⊤ : SimpleGraph (Fin 2)) □ (⊤ : SimpleGraph (Fin 2))) □ (⊤ : SimpleGraph (Fin 2)))
      (fun p => prismColor colA (ebig.symm p)) := by
    intro u v huv
    exact (prism_equitable hEq.1).1 _ _ (ebig.symm.map_adj_iff.mpr huv)
  exact pairedTwo_transfer ebig hconn (prism_equitable hEq.1).1 hcolT (q3_paired_two _ hcolT)

/-- An opposite-pair demand, taken apart into the eight primitive facts.  Every permuted demand the
    dispatch below needs is rebuilt from these, so the symmetry bookkeeping never has to reason
    about `Fin 2` index shuffling. -/
theorem oppositeDemand_dest {V' : Type} {col : V' → Bool} {p q r s : V'}
    (h : OppositeDemand col ![p, q] ![r, s]) :
    col p ≠ col r ∧ col q ≠ col s ∧ p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s := by
  obtain ⟨hcol, hsinj, htinj, hst⟩ := h
  have h0 := hcol 0
  have h1 := hcol 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1
  refine ⟨h0, h1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hc
    have he : (![p, q] : Fin 2 → V') 0 = ![p, q] 1 := by simpa using hc
    exact absurd (hsinj he) (by decide)
  · exact fun hc => hst 0 0 (by simpa using hc)
  · exact fun hc => hst 0 1 (by simpa using hc)
  · exact fun hc => hst 1 0 (by simpa using hc)
  · exact fun hc => hst 1 1 (by simpa using hc)
  · intro hc
    have he : (![r, s] : Fin 2 → V') 0 = ![r, s] 1 := by simpa using hc
    exact absurd (htinj he) (by decide)

/-- …and put back together.  The inverse of `oppositeDemand_dest`. -/
theorem oppositeDemand_mk {V' : Type} {col : V' → Bool} {p q r s : V'}
    (h1 : col p ≠ col r) (h2 : col q ≠ col s) (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) : OppositeDemand col ![p, q] ![r, s] := by
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j hij => ?_, fun i j => ?_⟩
  · fin_cases i
    · exact h1
    · exact h2
  · fin_cases i <;> fin_cases j <;> simp_all
  · fin_cases i <;> fin_cases j <;> simp_all
  · fin_cases i <;> fin_cases j <;> simp_all

section DemandSymmetry
variable {V' : Type} {col : V' → Bool} {p q r s : V'}

/-- Reversing the first pair, on the demand.  Pairs with `isPairedDPC2_reverse_fst`. -/
theorem oppositeDemand_rev_fst (h : OppositeDemand col ![p, q] ![r, s]) :
    OppositeDemand col ![r, q] ![p, s] :=
  let ⟨c0, c1, d01, d0r, d0s, d1r, d1s, drs⟩ := oppositeDemand_dest h
  oppositeDemand_mk c0.symm c1 d1r.symm d0r.symm drs d01.symm d1s d0s

/-- Reversing the second pair.  Pairs with `isPairedDPC2_reverse_snd`. -/
theorem oppositeDemand_rev_snd (h : OppositeDemand col ![p, q] ![r, s]) :
    OppositeDemand col ![p, s] ![r, q] :=
  let ⟨c0, c1, d01, d0r, d0s, d1r, d1s, drs⟩ := oppositeDemand_dest h
  oppositeDemand_mk c0 c1.symm d0s d0r d01 drs.symm d1s.symm d1r.symm

/-- Exchanging the two pairs.  Pairs with `isPairedDPC2_swap`. -/
theorem oppositeDemand_swapPairs (h : OppositeDemand col ![p, q] ![r, s]) :
    OppositeDemand col ![q, p] ![s, r] :=
  let ⟨c0, c1, d01, d0r, d0s, d1r, d1s, drs⟩ := oppositeDemand_dest h
  oppositeDemand_mk c1 c0 d01.symm d1s d1r d0s d0r drs.symm

end DemandSymmetry


/-! ## The three symmetries, and the sixteen positions

§5 says "swap the layer names if necessary so that `H⁰` contains no more terminals than `H¹`", and
treats `r = 0, 1, 2`.  That normalization is what this section supplies.

Each of the four terminals sits in one of two layers, so there are sixteen positions.  Three
symmetries collapse them onto the four constructions above: reversing within a pair and swapping the
two pairs are `isPairedDPC2_reverse_fst`/`_snd`/`_swap`, already in `WalkOfList`; **flipping the two
layers is the one that was missing**, and it is what makes `r = 3` and `r = 4` cost nothing. -/

/-- **Exchanging the two layers** is an automorphism of the prism. -/
def flipLayer (A : SimpleGraph W) : (A □ (⊤ : SimpleGraph (Fin 2))) ≃g (A □ (⊤ : SimpleGraph (Fin 2))) where
  toEquiv := (Equiv.refl W).prodCongr (Equiv.swap (0 : Fin 2) 1)
  map_rel_iff' := by
    rintro ⟨w, i⟩ ⟨w', i'⟩
    simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply, SimpleGraph.boxProd_adj,
      SimpleGraph.top_adj, ne_eq, Equiv.swap_apply_def]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨h1, by revert h2; fin_cases i <;> fin_cases i' <;> simp⟩
      · exact Or.inr ⟨by revert h1; fin_cases i <;> fin_cases i' <;> simp, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨h1, by rw [h2]⟩
      · exact Or.inr ⟨by revert h1; fin_cases i <;> fin_cases i' <;> simp, h2⟩

@[simp] theorem flipLayer_apply {A : SimpleGraph W} (w : W) (i : Fin 2) :
    flipLayer A (w, i) = (w, Equiv.swap (0 : Fin 2) 1 i) := rfl

/-- Flipping layers COMPLEMENTS the prism colouring — which is exactly why it is harmless:
    `OppositeDemand` asks only that each pair differs. -/
theorem prismColor_flipLayer {A : SimpleGraph W} (colA : W → Bool) (p : W × Fin 2) :
    prismColor colA (flipLayer A p) = !(prismColor colA p) := by
  obtain ⟨w, i⟩ := p
  fin_cases i <;> simp [prismColor, Equiv.swap_apply_def] <;> cases colA w <;> rfl

/-- The demand, flipped.  Used to turn `r = 3` and `r = 4` into `r = 1` and `r = 0`. -/
theorem oppositeDemand_flipLayer {A : SimpleGraph W} {colA : W → Bool} {k : ℕ}
    {s t : Fin k → W × Fin 2} (hd : OppositeDemand (prismColor colA) s t) :
    OppositeDemand (prismColor colA) (fun i => flipLayer A (s i)) (fun i => flipLayer A (t i)) := by
  obtain ⟨hcol, hsinj, htinj, hst⟩ := hd
  refine ⟨fun i => ?_, fun i j hij => hsinj ((flipLayer A).toEquiv.injective hij),
    fun i j hij => htinj ((flipLayer A).toEquiv.injective hij), fun i j hcon =>
      hst i j ((flipLayer A).toEquiv.injective hcon)⟩
  rw [prismColor_flipLayer, prismColor_flipLayer]
  have := hcol i
  cases h1 : prismColor colA (s i) <;> cases h2 : prismColor colA (t i) <;> simp_all

@[simp] theorem flipLayer_zero {A : SimpleGraph W} (w : W) :
    flipLayer A (w, (0 : Fin 2)) = (w, 1) := by
  simp [flipLayer, Equiv.swap_apply_left]

@[simp] theorem flipLayer_one {A : SimpleGraph W} (w : W) :
    flipLayer A (w, (1 : Fin 2)) = (w, 0) := by
  simp [flipLayer, Equiv.swap_apply_right]

/-- The layer flip on a four-terminal demand, in the `![·,·]` shape the dispatch uses. -/
theorem oppositeDemand_flip4 {A : SimpleGraph W} {colA : W → Bool} {a b c d : W × Fin 2}
    (h : OppositeDemand (prismColor colA) ![a, b] ![c, d]) :
    OppositeDemand (prismColor colA)
      ![flipLayer A a, flipLayer A b] ![flipLayer A c, flipLayer A d] := by
  obtain ⟨c0, c1, d01, d0r, d0s, d1r, d1s, drs⟩ := oppositeDemand_dest h
  have hnot : ∀ x y : Bool, x ≠ y → (!x) ≠ (!y) := by decide
  have hinj := (flipLayer A).toEquiv.injective
  exact oppositeDemand_mk
    (by rw [prismColor_flipLayer, prismColor_flipLayer]; exact hnot _ _ c0)
    (by rw [prismColor_flipLayer, prismColor_flipLayer]; exact hnot _ _ c1)
    (fun hc => d01 (hinj hc)) (fun hc => d0r (hinj hc)) (fun hc => d0s (hinj hc))
    (fun hc => d1r (hinj hc)) (fun hc => d1s (hinj hc)) (fun hc => drs (hinj hc))


/-- `prism_r0` in the four-terminal shape, so the dispatch's alternatives contain no nested `by` —
    an elaboration error inside one escapes `first` instead of being backtracked over. -/
theorem prism_r0' {A : SimpleGraph W} {colA : W → Bool}
    (hEq : IsEquitableBipartite A colA) (h4 : 4 ≤ Fintype.card W)
    (hpA : IsPairedKDPCForOpposite A colA 2) (a b c d : W)
    (hd : OppositeDemand (prismColor colA)
      ![(a, (1 : Fin 2)), (b, (1 : Fin 2))] ![(c, (1 : Fin 2)), (d, (1 : Fin 2))]) :
    IsPairedDPC (A □ (⊤ : SimpleGraph (Fin 2))) 2
      ![(a, (1 : Fin 2)), (b, (1 : Fin 2))] ![(c, (1 : Fin 2)), (d, (1 : Fin 2))] :=
  prism_r0 hEq h4 hpA _ _ hd (by intro i; fin_cases i <;> rfl)
    (by intro i; fin_cases i <;> rfl)

/-! ## Theorem 5.1, assembled

Sixteen positions — each of the four terminals is in one of two layers — collapsed onto the four
constructions by the three symmetries.  The dispatch is an alternation rather than sixteen
hand-written cases: each core lemma's CONCLUSION determines its vertex arguments by unification, so
`first` finds the right composition of symmetries on its own.  All that has to be supplied is that
every composition carries an opposite-pair demand to an opposite-pair demand —
`oppositeDemand_rev_fst`/`_rev_snd`/`_swapPairs`/`_flip4`.

The dispatch below is explicit rather than an alternation over symmetry words.  A `first`-based
version was tried and abandoned twice: it is slow (sixteen goals against a few dozen alternatives,
with backtracking), and an elaboration error inside a nested `by` ESCAPES `first` rather than being
backtracked over, so one alternative that fails on fifteen positions aborts the whole search.  The
explicit form also records which symmetry word each position uses, which the search would hide. -/

/-- **★ `SECTION5_PRODUCT_LIFTING_COMPLETE.md` Theorem 5.1, for `6 ≤ |W|`**, in four-terminal form.
    The `|W| = 4` case is `prism_paired_two_card_four`, which goes through `Q₃` instead.

    Sixteen positions, one line each; the comment on each is its layer pattern
    `(source₀, source₁, target₀, target₁)`.  The word of symmetries carrying each position to a core
    lemma was COMPUTED rather than guessed, and that mattered: a first pass at "the obvious"
    compositions was wrong for four of the sixteen, including every position pairing a
    confined-DOWN pair with a crossing one, which needs three symmetries and not one. -/
theorem prism_paired_four {A : SimpleGraph W} {colA : W → Bool}
    (hEq : IsEquitableBipartite A colA) (h6 : 6 ≤ Fintype.card W)
    (hpA : IsPairedKDPCForOpposite A colA 2) (p q r s : W × Fin 2)
    (hd : OppositeDemand (prismColor colA) ![p, q] ![r, s]) :
    IsPairedDPC (A □ (⊤ : SimpleGraph (Fin 2))) 2 ![p, q] ![r, s] := by
  classical
  have h4 : 4 ≤ Fintype.card W := by omega
  obtain ⟨p, ip⟩ := p
  obtain ⟨q, iq⟩ := q
  obtain ⟨r, ir⟩ := r
  obtain ⟨s, is'⟩ := s
  have hfin : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
  rcases hfin ip with rfl | rfl <;> rcases hfin iq with rfl | rfl <;>
    rcases hfin ir with rfl | rfl <;> rcases hfin is' with rfl | rfl
  · -- 0000
    refine isPairedDPC2_of_rep _ (flipLayer A) ?_
    have hd' := oppositeDemand_flip4 (A := A) hd
    simp only [flipLayer_zero, flipLayer_one] at hd' ⊢
    exact prism_r0' hEq h4 hpA _ _ _ _ (hd')
  · -- 0001
    refine isPairedDPC2_of_rep _ (flipLayer A) ?_
    have hd' := oppositeDemand_flip4 (A := A) hd
    simp only [flipLayer_zero, flipLayer_one] at hd' ⊢
    exact isPairedDPC2_reverse_snd _ (isPairedDPC2_swap _ (prism_r1_core hEq h4 hpA _ _ _ _ (oppositeDemand_swapPairs (oppositeDemand_rev_snd (hd')))))
  · -- 0010
    refine isPairedDPC2_of_rep _ (flipLayer A) ?_
    have hd' := oppositeDemand_flip4 (A := A) hd
    simp only [flipLayer_zero, flipLayer_one] at hd' ⊢
    exact isPairedDPC2_reverse_fst _ (prism_r1_core hEq h4 hpA _ _ _ _ (oppositeDemand_rev_fst (hd')))
  · -- 0011
    exact prism_r2_c2 hEq h4 hpA _ _ _ _ (hd) (Or.inr h6)
  · -- 0100
    refine isPairedDPC2_of_rep _ (flipLayer A) ?_
    have hd' := oppositeDemand_flip4 (A := A) hd
    simp only [flipLayer_zero, flipLayer_one] at hd' ⊢
    exact isPairedDPC2_swap _ (prism_r1_core hEq h4 hpA _ _ _ _ (oppositeDemand_swapPairs (hd')))
  · -- 0101
    exact prism_r2_c0_core hEq h4 hpA _ _ _ _ (hd)
  · -- 0110
    exact isPairedDPC2_reverse_snd _ (prism_r2_c2 hEq h4 hpA _ _ _ _ (oppositeDemand_rev_snd (hd)) (Or.inr h6))
  · -- 0111
    exact prism_r1_core hEq h4 hpA _ _ _ _ (hd)
  · -- 1000
    refine isPairedDPC2_of_rep _ (flipLayer A) ?_
    have hd' := oppositeDemand_flip4 (A := A) hd
    simp only [flipLayer_zero, flipLayer_one] at hd' ⊢
    exact prism_r1_core hEq h4 hpA _ _ _ _ (hd')
  · -- 1001
    exact isPairedDPC2_reverse_fst _ (prism_r2_c2 hEq h4 hpA _ _ _ _ (oppositeDemand_rev_fst (hd)) (Or.inr h6))
  · -- 1010
    exact isPairedDPC2_swap _ (prism_r2_c0_core hEq h4 hpA _ _ _ _ (oppositeDemand_swapPairs (hd)))
  · -- 1011
    exact isPairedDPC2_swap _ (prism_r1_core hEq h4 hpA _ _ _ _ (oppositeDemand_swapPairs (hd)))
  · -- 1100
    refine isPairedDPC2_of_rep _ (flipLayer A) ?_
    have hd' := oppositeDemand_flip4 (A := A) hd
    simp only [flipLayer_zero, flipLayer_one] at hd' ⊢
    exact prism_r2_c2 hEq h4 hpA _ _ _ _ (hd') (Or.inr h6)
  · -- 1101
    exact isPairedDPC2_reverse_fst _ (prism_r1_core hEq h4 hpA _ _ _ _ (oppositeDemand_rev_fst (hd)))
  · -- 1110
    exact isPairedDPC2_reverse_snd _ (isPairedDPC2_swap _ (prism_r1_core hEq h4 hpA _ _ _ _ (oppositeDemand_swapPairs (oppositeDemand_rev_snd (hd)))))
  · -- 1111
    exact prism_r0' hEq h4 hpA _ _ _ _ (hd)

/-- **★ Theorem 5.1.**  Both ranges together: `|W| = 4` through `Q₃`, everything larger through the
    sixteen-position dispatch. -/
theorem prism_paired_two_proved {A : SimpleGraph W} {colA : W → Bool}
    (hEq : IsEquitableBipartite A colA) (h4 : 4 ≤ Fintype.card W)
    (hpA : IsPairedKDPCForOpposite A colA 2) :
    IsPairedKDPCForOpposite (A □ (⊤ : SimpleGraph (Fin 2))) (prismColor colA) 2 := by
  classical
  by_cases hsmall : Fintype.card W = 4
  · exact prism_paired_two_card_four hEq hsmall hpA
  · have h6 : 6 ≤ Fintype.card W := by
      have := card_colorClass hEq false
      omega
    intro s t hd
    have hs : s = ![s 0, s 1] := by funext i; fin_cases i <;> rfl
    have ht : t = ![t 0, t 1] := by funext i; fin_cases i <;> rfl
    rw [hs, ht] at hd ⊢
    exact prism_paired_four hEq h6 hpA _ _ _ _ hd

end Brualdi.RealizationGraph.Prism
