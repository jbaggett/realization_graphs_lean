/-
Copyright (c) 2026 Jeffrey S. Baggett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey S. Baggett
-/
import BrualdiLean.RealizationGraph.IntervalLemma
import BrualdiLean.RealizationGraph.InterfaceSaturation
import BrualdiLean.RealizationGraph.SeparatorTheorem
import Mathlib.Data.Fintype.Card

/-!
# Layer capacity (sub-claim L1)

This module mechanizes sub-claim L1 from `next_paper/draft_threading_lemma.md`: every
nonminimum admissible layer at a near-regular pivot has at least two labeled residual
realizations.

## Threshold inputs

* `threshold_iff_unique_realization` is proved here from realization-graph connectivity.
  Mahadev--Peled 1995 also states the equivalence; its verbatim pinning is retained at the
  theorem as a provenance remark.
* `threshold_dominance_maximal` is transferred from the independently proved
  `SeparatorTheorem.ResidualSystem.threshold_dominance_maximal` through an equivalence of
  the two realization carrier types.  No threshold-graph characterization is needed for
  the transfer.

All remaining results, including the explicit `(k,k) -> (k+1,k-1)` dominance raise and
the passage from graphicality to positive realization count, are proved below.
-/

set_option autoImplicit false
set_option linter.style.nativeDecide false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

namespace Brualdi.RealizationGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## Labeled realization count -/

/-- The existing `Realization d` structure is finite: its graph field determines the stored
decidability witness and degree proof up to subsingleton elimination. -/
noncomputable instance realizationFintype (d : V → ℕ) : Fintype (Realization d) :=
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

/-- Number of simple graphs on the fixed label type having degree function `d`. -/
noncomputable def realizationCount (d : V → ℕ) : ℕ :=
  Fintype.card (Realization d)

/-- `SimpleGraph.degree` is independent of the `Fintype` instance used on the neighbor
subtype. -/
private theorem degree_eq_of_fintype_instances (G : SimpleGraph V) (v : V)
    (i j : Fintype (G.neighborSet v)) :
    @SimpleGraph.degree V G v i = @SimpleGraph.degree V G v j := by
  unfold SimpleGraph.degree SimpleGraph.neighborFinset
  rw [@Set.toFinset_card _ _ i, @Set.toFinset_card _ _ j]
  exact @Fintype.card_congr _ _ i j (Equiv.refl _)

theorem graphical_iff_realization_nonempty {d : V → ℕ} :
    Graphical d ↔ Nonempty (Realization d) := by
  constructor
  · intro hd
    exact ⟨realizationOfGraphical hd⟩
  · rintro ⟨G⟩
    exact G.toGraphical

theorem graphical_iff_realizationCount_pos {d : V → ℕ} :
    Graphical d ↔ 0 < realizationCount d := by
  rw [graphical_iff_realization_nonempty]
  exact Fintype.card_pos_iff.symm

private theorem realization_eq_of_graph_eq {d : V → ℕ} (G H : Realization d)
    (h : G.graph = H.graph) : G = H := by
  cases G with
  | mk graphG decG degreeG =>
    cases H with
    | mk graphH decH degreeH =>
      dsimp at h
      subst graphH
      congr
      exact Subsingleton.elim _ _

/-- The bundled main-lane realizations are equivalent to the subtype realizations in
`SeparatorTheorem`.  The forward degree proof uses instance-independence of finite cardinality;
the inverse installs the classical decidability witness used by the subtype development. -/
noncomputable def realizationEquivSeparator (d : V → ℕ) :
    Realization d ≃ SeparatorTheorem.Realization d where
  toFun G := by
    refine ⟨G.graph, ?_⟩
    intro v
    exact (degree_eq_of_fintype_instances G.graph v _ _).trans (G.degree_eq v)
  invFun G := by
    let hG : DecidableRel G.1.Adj := Classical.decRel _
    refine { graph := G.1, adjDecidable := hG, degree_eq := ?_ }
    letI := hG
    exact G.2
  left_inv G := realization_eq_of_graph_eq _ _ rfl
  right_inv G := Subtype.ext rfl

/-- The independently defined capacity is the main lane's labeled realization count. -/
theorem separatorCapacity_eq_realizationCount (d : V → ℕ) :
    SeparatorTheorem.capacity d = realizationCount d := by
  exact (Fintype.card_congr (realizationEquivSeparator d)).symm

/-- The two graphicality predicates agree through their realization carriers. -/
theorem graphical_iff_separatorGraphical (d : V → ℕ) :
    Graphical d ↔ SeparatorTheorem.Graphical d := by
  rw [graphical_iff_realization_nonempty,
    SeparatorTheorem.graphical_iff_realization_nonempty]
  constructor
  · rintro ⟨G⟩
    exact ⟨realizationEquivSeparator d G⟩
  · rintro ⟨G⟩
    exact ⟨(realizationEquivSeparator d).symm G⟩

/-- Relabel a realization along an equivalence whose action carries one degree function to
the other. -/
private noncomputable def realizationComap {d₁ d₂ : V → ℕ} (e : V ≃ V)
    (hdeg : ∀ x, d₁ (e x) = d₂ x) (G : Realization d₁) : Realization d₂ := by
  letI := G.adjDecidable
  refine { graph := G.graph.comap e
           adjDecidable := inferInstance
           degree_eq := ?_ }
  intro x
  rw [comap_equiv_degree, G.degree_eq, hdeg]

/-- Exact labeled realization counts are invariant under relabeling. -/
theorem realizationCount_congr {d₁ d₂ : V → ℕ} (e : V ≃ V)
    (hdeg : ∀ x, d₁ (e x) = d₂ x) :
    realizationCount d₁ = realizationCount d₂ := by
  classical
  let f : Realization d₁ → Realization d₂ := realizationComap e hdeg
  have hinj : Function.Injective f := by
    intro G H hGH
    apply realization_eq_of_graph_eq
    ext x y
    have hadj := congrFun (congrFun (congrArg (fun K => K.graph.Adj) hGH)
      (e.symm x)) (e.symm y)
    simpa [f, realizationComap] using hadj
  have hsurj : Function.Surjective f := by
    intro H
    let hdeg' : ∀ x, d₂ (e.symm x) = d₁ x := by
      intro x
      simpa using (hdeg (e.symm x)).symm
    let G : Realization d₁ := realizationComap e.symm hdeg' H
    refine ⟨G, ?_⟩
    apply realization_eq_of_graph_eq
    ext x y
    simp [f, G, realizationComap]
  exact Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

private def classSelection (p : V → Prop) [DecidablePred p] (S : Finset V) :
    Finset {x : V // p x} :=
  Finset.univ.filter fun x => x.val ∈ S

private theorem classSelection_card (p : V → Prop) [DecidablePred p] (S : Finset V) :
    (classSelection p S).card = (S.filter p).card := by
  classical
  exact Finset.card_bij
    (fun x _ => x.val)
    (by
      intro x hx
      have hxS : x.val ∈ S := by simpa [classSelection] using hx
      exact Finset.mem_filter.mpr ⟨hxS, x.property⟩)
    (by intro a _ b _ h; exact Subtype.ext h)
    (by
      intro x hx
      have hxp : p x := (Finset.mem_filter.mp hx).2
      refine ⟨⟨x, hxp⟩, ?_, rfl⟩
      simp [classSelection, (Finset.mem_filter.mp hx).1])

/-- Two subsets having the same size and the same number of members in a class are carried
to one another by a permutation preserving that class. -/
private theorem exists_class_preserving_equiv
    (p : V → Prop) [DecidablePred p] (S₁ S₂ : Finset V)
    (hcard : S₁.card = S₂.card)
    (hp : (S₁.filter p).card = (S₂.filter p).card) :
    ∃ e : V ≃ V,
      (∀ x, x ∈ S₂ ↔ e x ∈ S₁) ∧ (∀ x, p (e x) ↔ p x) := by
  classical
  let A₁ := classSelection p S₁
  let A₂ := classSelection p S₂
  let B₁ := classSelection (fun x => ¬ p x) S₁
  let B₂ := classSelection (fun x => ¬ p x) S₂
  have hA : A₂.card = A₁.card := by
    dsimp [A₁, A₂]
    rw [classSelection_card, classSelection_card, hp.symm]
  have hB : B₂.card = B₁.card := by
    dsimp [B₁, B₂]
    rw [classSelection_card, classSelection_card]
    have hsplit₁ := Finset.card_filter_add_card_filter_not p (s := S₁)
    have hsplit₂ := Finset.card_filter_add_card_filter_not p (s := S₂)
    omega
  obtain ⟨ep, hep⟩ := Equiv.Perm.exists_map_finset_eq A₂ A₁ hA
  obtain ⟨en, hen⟩ := Equiv.Perm.exists_map_finset_eq B₂ B₁ hB
  let e : V ≃ V := Equiv.Perm.subtypeCongr ep en
  refine ⟨e, ?_, ?_⟩
  · intro x
    by_cases hx : p x
    · have hmem : ep ⟨x, hx⟩ ∈ A₁ ↔ (⟨x, hx⟩ : {x // p x}) ∈ A₂ := by
        rw [← hep]
        simp
      have heq : e x = (ep ⟨x, hx⟩).val :=
        Equiv.Perm.subtypeCongr.left_apply ep en hx
      rw [heq]
      simpa [A₁, A₂, classSelection] using hmem.symm
    · have hmem : en ⟨x, hx⟩ ∈ B₁ ↔ (⟨x, hx⟩ : {x // ¬ p x}) ∈ B₂ := by
        rw [← hen]
        simp
      have heq : e x = (en ⟨x, hx⟩).val :=
        Equiv.Perm.subtypeCongr.right_apply ep en hx
      rw [heq]
      simpa [B₁, B₂, classSelection] using hmem.symm
  · intro x
    by_cases hx : p x
    · have heq : e x = (ep ⟨x, hx⟩).val :=
        Equiv.Perm.subtypeCongr.left_apply ep en hx
      rw [heq]
      exact ⟨fun _ => hx, fun _ => (ep ⟨x, hx⟩).property⟩
    · have heq : e x = (en ⟨x, hx⟩).val :=
        Equiv.Perm.subtypeCongr.right_apply ep en hx
      rw [heq]
      exact ⟨fun h => False.elim ((en ⟨x, hx⟩).property h),
        fun h => False.elim (hx h)⟩

/-- Partition symmetry preserves not only graphicality but the exact labeled realization
count of interval residuals. -/
theorem intervalResidual_realizationCount_eq {d : V → ℕ} {k : ℕ} {v : V}
    (hnear : NearRegular d k) (S₁ S₂ : Finset (Deleted v))
    (hcard : S₁.card = S₂.card)
    (hhigh : highCount d k S₁ = highCount d k S₂) :
    realizationCount (intervalResidual d S₁) =
      realizationCount (intervalResidual d S₂) := by
  classical
  let p : Deleted v → Prop := fun x => d x.val = k + 1
  have hp : (S₁.filter p).card = (S₂.filter p).card := by
    simpa [p, highCount] using hhigh
  obtain ⟨e, hmem, hclass⟩ := exists_class_preserving_equiv p S₁ S₂ hcard hp
  have hamb : ∀ x : Deleted v, d (e x).val = d x.val := by
    intro x
    by_cases hx : p x
    · have hex : p (e x) := (hclass x).mpr hx
      exact hex.trans hx.symm
    · have hxlow : d x.val = k := by
        rcases hnear x.val with h | h
        · exact h
        · exact False.elim (hx h)
      have helow : d (e x).val = k := by
        rcases hnear (e x).val with h | h
        · exact h
        · exact False.elim (hx ((hclass x).mp h))
      exact helow.trans hxlow.symm
  apply realizationCount_congr e
  intro x
  unfold intervalResidual
  rw [hamb]
  by_cases hx : x ∈ S₂
  · rw [if_pos hx, if_pos ((hmem x).mp hx)]
  · rw [if_neg hx, if_neg (fun he => hx ((hmem x).mpr he))]

/-! ## Threshold and dominance vocabulary -/

/-- We choose the no-2-switch characterization as the definition of a threshold degree
function: it is graphical and its realization graph has no edge. -/
def IsThreshold (d : V → ℕ) : Prop :=
  Graphical d ∧ ∀ G H : Realization d, ¬ twoSwitchAdjacent G H

/-- One strict dominance raise: move one unit from `y` to `x`, where the receiving entry is
already no smaller.  The pointwise formulation avoids natural-number subtraction. -/
def DominanceStep (d e : V → ℕ) : Prop :=
  ∃ x y : V, x ≠ y ∧ d y ≤ d x ∧
    e x = d x + 1 ∧ d y = e y + 1 ∧
      ∀ z : V, z ≠ x → z ≠ y → e z = d z

/-- Strict dominance is the transitive closure of unit dominance raises. -/
def StrictlyDominates (e d : V → ℕ) : Prop :=
  Relation.TransGen DominanceStep d e

private theorem dominanceStep_iff_separatorDominanceStep (d e : V → ℕ) :
    DominanceStep d e ↔ SeparatorTheorem.DominanceStep d e := by
  rfl

/-- **PROVENANCE REMARK — Mahadev & Peled, *Threshold Graphs and Related Topics*, Annals of Discrete
Mathematics 56, Elsevier.  Theorem 3.2.1 (§3.2, p. 72).  Verbatim:**

> "A graphical sequence is a threshold sequence if and only if it is strictly unigraphic, i.e., has a
> unique labeled realization."

The book's gloss on "strictly unigraphic", immediately above the theorem: *"if `d = (d1,...,dn)` and
`G = (V,E)` is a graph with `V = {1,...,n}` and `deg(i) = di`, then `E` is completely determined"* —
which is `realizationCount d = 1` on a fixed label type, the form stated here.  `IsThreshold` is
pinned above to the graphical/no-2-switch characterization, matching the book's Theorem 1.2.4
Condition 2 used in its proof.

**Pinning read 2026-08-19** from the full scan (Zotero item `K2TVFMDA`, storage `9D5NAPLL`),
SHA-256 `2f387f01baa83d36f5d8b8289b10b19cf343746fbe3fa014f40bd9df4931bb52`.
Masthead confirmed from the source: *Annals of Discrete Mathematics* **56**, N.V.R. Mahadev
(Northeastern University) and U.N. Peled (University of Illinois at Chicago), Elsevier Science B.V.,
**1995**, ISBN 0 444 89287 7.

An earlier attachment on the same item began at the Preface and carried no masthead, so the year
could not be confirmed from the source and the pin said so.  Jeff supplied the complete scan the same
day; the year is now read off the copyright page rather than inferred from a database, which is the
distinction the Alspach case in `lib/refs/REFERENCE_VETTING.md` exists to enforce. -/
theorem threshold_iff_unique_realization (d : V → ℕ) :
    realizationCount d = 1 ↔ IsThreshold d
    := by
  constructor
  · intro hcount
    obtain ⟨G, hunique⟩ := Fintype.card_eq_one_iff.mp hcount
    refine ⟨G.toGraphical, ?_⟩
    intro H K
    have hHK : H = K := (hunique H).trans (hunique K).symm
    subst K
    change ¬ (RealizationGraph d).Adj H H
    exact (RealizationGraph d).irrefl
  · rintro ⟨hgraphical, hno⟩
    apply Fintype.card_eq_one_iff.mpr
    let G := realizationOfGraphical hgraphical
    refine ⟨G, ?_⟩
    intro H
    obtain ⟨p⟩ := realizationGraph_preconnected H G
    cases p with
    | nil => rfl
    | cons hadj p => exact (hno _ _ hadj).elim

/-- The main lane's threshold predicate agrees with the independent separator development's
predicate because both characterize capacity one on equivalent realization carriers. -/
theorem isThreshold_iff_separatorIsThreshold (d : V → ℕ) :
    IsThreshold d ↔ SeparatorTheorem.IsThreshold d := by
  calc
    IsThreshold d ↔ realizationCount d = 1 := (threshold_iff_unique_realization d).symm
    _ ↔ SeparatorTheorem.capacity d = 1 := by
      rw [separatorCapacity_eq_realizationCount]
    _ ↔ SeparatorTheorem.IsThreshold d :=
      SeparatorTheorem.capacity_one_iff_threshold d

/-- A threshold degree function is dominance-maximal among graphical degree functions.  This is
the needed direction of the former cited equivalence, transferred from `SeparatorTheorem`. -/
theorem threshold_dominance_maximal {d e : V → ℕ}
    (hd : IsThreshold d) (he : Graphical e) : ¬ StrictlyDominates e d := by
  have h := SeparatorTheorem.ResidualSystem.threshold_dominance_maximal
    (isThreshold_iff_separatorIsThreshold d |>.mp hd)
    (graphical_iff_separatorGraphical e |>.mp he)
  unfold SeparatorTheorem.StrictlyDominates at h
  unfold StrictlyDominates
  have hstep : (@SeparatorTheorem.DominanceStep V) = DominanceStep := by
    funext a b
    apply propext
    exact (dominanceStep_iff_separatorDominanceStep a b).symm
  rw [hstep] at h
  exact h

theorem realizationCount_two_le_of_graphical_of_strict_dominator
    {d e : V → ℕ} (hd : Graphical d) (he : Graphical e)
    (hed : StrictlyDominates e d) :
    2 ≤ realizationCount d := by
  have hpos : 0 < realizationCount d := graphical_iff_realizationCount_pos.mp hd
  have hnthreshold : ¬ IsThreshold d := by
    intro hthreshold
    exact threshold_dominance_maximal hthreshold he hed
  have hne_one : realizationCount d ≠ 1 := by
    intro hone
    exact hnthreshold ((threshold_iff_unique_realization d).mp hone)
  omega

/-! ## The explicit three-valued residual raise -/

/-- The residual produced by exchanging an unselected high vertex for a selected low vertex
is strictly dominated by the preceding residual.  Concretely, the two changed residual
entries are `(k,k)` in the new layer and `(k+1,k-1)` in the preceding layer. -/
theorem intervalResidual_predecessor_strictlyDominates
    {d : V → ℕ} {k : ℕ} {v : V} {S : Finset (Deleted v)}
    {x y : Deleted v}
    (hk : 0 < k)
    (hxS : x ∉ S) (hyS : y ∈ S)
    (hxhi : x ∈ highSet d k v) (hylow : y ∈ lowSet d k v) :
    StrictlyDominates (intervalResidual d S)
      (intervalResidual d (insert x (S.erase y))) := by
  classical
  let T : Finset (Deleted v) := insert x (S.erase y)
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hxS hyS
  have hxdeg : d x.val = k + 1 := by simpa using hxhi
  have hydeg : d y.val = k := by simpa using hylow
  have hxT : x ∈ T := by simp [T]
  have hyT : y ∉ T := by simp [T, hxy.symm]
  have hnewx : intervalResidual d T x = k := by
    simp [intervalResidual, hxT, hxdeg]
  have hnewy : intervalResidual d T y = k := by
    simp [intervalResidual, hyT, hydeg]
  have holdx : intervalResidual d S x = k + 1 := by
    simp [intervalResidual, hxS, hxdeg]
  have holdy : intervalResidual d S y = k - 1 := by
    simp [intervalResidual, hyS, hydeg]
  apply Relation.TransGen.single
  refine ⟨x, y, hxy, ?_, ?_, ?_, ?_⟩
  · rw [hnewx, hnewy]
  · rw [holdx, hnewx]
  · rw [hnewy, holdy]
    omega
  · intro z hzx hzy
    unfold intervalResidual
    have hzmem : z ∈ T ↔ z ∈ S := by
      simp [T, hzx, hzy]
    rw [if_congr hzmem rfl]
    rfl

/-! ## Sub-claim L1 -/

/-- **Sub-claim L1.**  For a graphical near-regular degree function and pivot `v`, there is
a minimum admissible layer `a`, and every representative of every feasible layer strictly
above `a` has at least two labeled residual realizations.  Exact count invariance across the
three-valued residual multiset `D_h` is supplied by `intervalResidual_realizationCount_eq`. -/
theorem L1 {d : V → ℕ} {k : ℕ} {v : V} {r : ℕ}
    (hnear : NearRegular d k) (hd : Graphical d) (hr : r = d v) :
    ∃ a : ℕ,
      FeasibleH d k v r a ∧ AdmissibleH d k v r a ∧
        ∀ h : ℕ, FeasibleH d k v r h → a < h →
          ∀ S : Finset (Deleted v), S.card = r → highCount d k S = h →
            2 ≤ realizationCount (intervalResidual d S) := by
  classical
  obtain ⟨a, hfa, haA, hsuffix⟩ := intervalLemma_suffix hnear hd hr
  refine ⟨a, hfa, haA, ?_⟩
  intro h hfh hah
  have hk : 0 < k := by
    by_contra hknot
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hknot
    subst k
    rcases hnear v with hdv0 | hdv1
    · have hr0 : r = 0 := by omega
      have hle : h ≤ r := hfh.2.1
      omega
    · have hr1 : r = 1 := by omega
      have hle : h ≤ r := hfh.2.1
      have ha0 : a = 0 := by omega
      have hA0 : AdmissibleH d 0 v r 0 := by simpa [ha0] using haA
      exact (not_admissible_zero_layer_k0_one hnear hd hr hr1) hA0
  have hprevfeas : FeasibleH d k v r (h - 1) := by
    rcases hfa with ⟨hfaLow, _hfaR, _hfaHigh⟩
    rcases hfh with ⟨_hfhLow, hfhR, hfhHigh⟩
    constructor
    · omega
    constructor <;> omega
  have haprev : a ≤ h - 1 := by omega
  have hprevA : AdmissibleH d k v r (h - 1) :=
    (hsuffix (h - 1) hprevfeas).mpr haprev
  rcases hprevA with ⟨S, hScard, hShigh, hSgraphical⟩
  have hsuccEq : h - 1 + 1 = h := by omega
  have hfeasSucc : FeasibleH d k v r ((h - 1) + 1) := by
    simpa [hsuccEq] using hfh
  obtain ⟨x, hxhi, hxS⟩ :=
    exists_high_not_mem_of_succ_feasible (d := d) (k := k) (v := v)
      (r := r) (h := h - 1) (S := S) hShigh hfeasSucc
  have hprev_lt_r : h - 1 < r := by
    have hh_le_r : h ≤ r := hfh.2.1
    omega
  obtain ⟨y, hyS, hylow⟩ :=
    exists_low_mem_of_card_highCount_lt (d := d) (k := k) (v := v)
      (r := r) (h := h - 1) (S := S) hnear hScard hShigh hprev_lt_r
  let T : Finset (Deleted v) := insert x (S.erase y)
  have hTcard : T.card = r :=
    card_exchange (S := S) (x := x) (y := y) hScard hxS hyS
  have hThigh : highCount d k T = h := by
    have := highCount_exchange (d := d) (k := k) (S := S) (x := x) (y := y)
      hShigh hxS hyS hxhi hylow
    simpa [T, hsuccEq] using this
  have hfun :
      intervalResidual d T =
        Function.update
          (Function.update (intervalResidual d S) x (intervalResidual d S x - 1))
          y (intervalResidual d S y + 1) := by
    simpa [T] using intervalResidual_eq_update_exchange (d := d) (k := k)
      (S := S) (x := x) (y := y) hk hxS hyS hxhi hylow
  have hxres : intervalResidual d S x = k + 1 := by
    have hxdeg : d x.val = k + 1 := by simpa using hxhi
    simp [intervalResidual, hxS, hxdeg]
  have hyres : intervalResidual d S y = k - 1 := by
    have hydeg : d y.val = k := by simpa using hylow
    simp [intervalResidual, hyS, hydeg]
  have htransfer : intervalResidual d S y + 2 ≤ intervalResidual d S x := by
    rw [hxres, hyres]
    omega
  have hTgraphical : Graphical (intervalResidual d T) := by
    rw [hfun]
    exact down_transfer hSgraphical htransfer
  have hdom : StrictlyDominates (intervalResidual d S) (intervalResidual d T) := by
    simpa [T] using intervalResidual_predecessor_strictlyDominates
      (d := d) (k := k) (v := v) (S := S) (x := x) (y := y)
      hk hxS hyS hxhi hylow
  have hcount : 2 ≤ realizationCount (intervalResidual d T) :=
    realizationCount_two_le_of_graphical_of_strict_dominator
      hTgraphical hSgraphical hdom
  intro U hUcard hUhigh
  have hcountEq : realizationCount (intervalResidual d T) =
      realizationCount (intervalResidual d U) :=
    intervalResidual_realizationCount_eq hnear T U
      (hTcard.trans hUcard.symm) (hThigh.trans hUhigh.symm)
  rwa [← hcountEq]

#print axioms L1

end Brualdi.RealizationGraph
