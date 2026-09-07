/-
Copyright (c) 2026 Jeffrey S. Baggett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey S. Baggett
-/
/-
# `(SB+)` and `(ORD)` — statements-first

The two obligations of the one-pass route that no statement in the lane recorded until 2026-08-15,
both since proved. Prose sources, all in `topics/flipgraphs/realization/`:

* `INTERFACE_Q_QSTAR_2026-08-15.md` — how `(SB+)` was found: the route consumes a quotient Hamilton
  path between endpoints it does not choose, and `(Q*)` has an exception class that reaches the main
  line.
* `SBPLUS_ROUTE_2026-08-15.md`, `SBPLUS_CODEX_2026-08-15.md` — the proof of `(SB+)`.
* `ORD_2026-08-15.md` — the proof of `(ORD)`, which removes the unsafe Hladík–Fink Lemma 1.3
  citation from the route.
* `DEPENDENCY_GRAPH_2026-08-15.md` — where both sit in the end-to-end graph.

## REUSE-FIRST audit, run before writing

Everything below was checked against the existing development before a line was written.

* realizations / the realization graph / 2-switch adjacency — `Realization`, `RealizationGraph`,
  `twoSwitchAdjacent` in `Defs.lean`. **Reused.**
* "`S` is a realizable neighborhood of `v`" — `HasRealizationWithNeighborSet`, `Defs.lean:103`.
  **Reused.**
* That this equals residual graphicality — `observation0_delete_direction` and
  `observation0_add_direction` in `Observation0.lean`, **both directions already PROVED.**
  **Reused, and it matters:** the computational `(SB+)` sweep enumerates quotients by exactly this
  equivalence, so that sweep rests on a machine-checked fact and not a measured one.
* Bad template — `SimpleGraph.IsCliqueSum` in `QStar.lean`. **Reused**; it was lifted to graph
  level precisely so this file could share it.
* Hamilton path between a prescribed pair — `HasHamPath`, `ColemanDefs.lean`. **Reused.**
* Neighborhood exchange graph on the deleted subtype — `admissibleExchangeGraph`, formerly
  `BaseStructure.lean:127`. **Not reused**, and as of 2026-08-20 no longer reachable: `BaseStructure`
  was parked into the `ParkedBaseStructure` target with the superseded matroid route, so this target
  now has ONE spelling of the quotient and the old obligation
  `quotientGraph_eq_admissibleExchangeGraph` is moot. The identification that does matter, against
  `QStar.exchangeGraph`, is PROVED as `quotientIsoExchange` below (manuscript Corollary 5.5).

## OPEN OBLIGATIONS OF THIS MODULE, recorded here rather than as declarations

**Why here and not as theorems.** Until 2026-08-16 these three were carried as
`theorem <name> : True := by trivial`. That is a worse mechanism than a `sorry`: such a declaration
compiles green, carries **no** `sorryAx`, and an axiom trace reports it as *"does not depend on any
axioms"* — cleaner than a genuinely proved theorem. Any count of the form "N declarations, 0
`sorryAx`" silently includes it, while it asserts nothing at all. A `sorry` is honest about what it
owes; `True` is not.

This module already records the same lesson one level down: `NoErdosGallaiEquality` once had a
"deliberately-inert body" that was **vacuously true**, which would have made `MainLine` weaker than
intended and `sbPlus` correspondingly *stronger* than the theorem it names. A `True` theorem is that
same mistake at the level of the conclusion instead of the hypothesis.

They are recorded as prose so nothing here can be mistaken for discharged. Each is a genuine
obligation and each should become a real statement once the definitions it needs exist — that is a
worthwhile future wave, and the reason none was written today is that inventing those definitions in
order to host a statement is exactly how a module ends up stating a theorem about the wrong object.

1. **Quotient spelling agreement.** `quotientGraph` agrees with
   `BaseStructure.admissibleExchangeGraph` under the `Deleted v` coercion, so the two spellings in
   this development cannot silently diverge. Needs the coercion.

2. ~~**Faithfulness of the main-line hypothesis.**~~ **DISCHARGED 2026-08-18, and by refutation
   rather than by proof.** This obligation read: *"`NoErdosGallaiEquality` is Tyshkevich
   indecomposability."* It is **false**, measured in both directions — `P₄ = (2,2,1,1)` is
   indecomposable with an Erdős–Gallai equality at `k = 2`, and `(1,1,1,1,0)` is decomposable with
   none. Under the other three `MainLine` hypotheses the error was one-sided: 0 sequences where the
   stand-in claimed more than the paper, **26 of 161** through ground order 7 where it claimed less.
   So it was sound and strictly stronger, and every theorem carrying `MainLine` named a theorem it
   did not prove. `MainLine.indecomposable` now carries `¬ TyshkevichDecomposable`, defined here from
   the definition. What remains is the smaller obligation stated with that definition: Tyshkevich's
   own theorem, that decomposability depends only on the degree sequence.
   `results/2026-08-18_tyshkevich_not_equivalent_to_eg.md`.

This module previously exposed unfinished proofs as `sorry`s, so that every open declaration printed
`sorryAx` rather than looking proved.  The final induction below has now discharged the remaining
ones.  `compute/check_axiom_baseline.py`, updated in the same edit, remains the source of truth rather
than repeating a numeric count here.
-/
import Realization.QStar
import Realization.TightUnion
import Realization.Observation0
import Realization.TheoremOne
import Realization.LemmaRCore
import Realization.QuotientAdjacency
import Realization.TriangleProjection
import Realization.InterfaceSaturation

namespace Brualdi.RealizationGraph.SBPlusOrd

open Brualdi.Ledger
open Brualdi.RealizationGraph
open Brualdi.RealizationGraph
open scoped symmDiff

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## 1. The neighborhood quotient -/

/-- Vertices of the quotient at `v`: the neighborhoods that actually occur in realizations. -/
def QuotientV (d : V → ℕ) (v : V) : Type u :=
  {S : Finset V // HasRealizationWithNeighborSet d v S}

/-- Equality of quotient vertices is decidable classically. Needed only so that `HasHamPath`, which
is stated for a `DecidableEq` vertex type, applies to `quotientGraph` — the same reason
`fibreDecidableEq` exists below. `QuotientV` is a `def` rather than an `abbrev`, so instance search
does not see through it to the underlying subtype of `Finset V`. -/
noncomputable instance quotientDecidableEq (d : V → ℕ) (v : V) :
    DecidableEq (QuotientV d v) := Classical.decEq _

noncomputable instance quotientFintype (d : V → ℕ) (v : V) :
    Fintype (QuotientV d v) := by
  classical
  unfold QuotientV
  exact Fintype.ofFinite _

/-- **The neighborhood quotient at `v`.** Same adjacency as `admissibleExchangeGraph` and as
`QStar.exchangeGraph`: two neighborhoods are joined when their symmetric difference has two
elements.

That this *literal* adjacency coincides with the quotient of `RealizationGraph d` — i.e. that
`S ~ T` iff some realization in the `S`-fibre is 2-switch adjacent to one in the `T`-fibre — is
manuscript Theorem 5.4, restated here as `quotient_adjacency`, and it is **PROVED** on foundations
alone. (This sentence said the opposite until 2026-08-18, having been written while the declaration
was still open and never revisited when it closed. A doc comment that misstates its own
declaration's status is the defect class this lane has on record three times, and it does not become
harmless by erring toward *under*-claiming: §11.4 of the manuscript was written from this sentence.) -/
def quotientGraph (d : V → ℕ) (v : V) : SimpleGraph (QuotientV d v) :=
  SimpleGraph.fromRel fun S T => (S.val ∆ T.val).card = 2

/-- **Manuscript Theorem 5.4, quotient adjacency.** The literal quotient of the realization graph is
the exchange adjacency: distinct neighborhoods at symmetric-difference two are exactly those joined
by an actual 2-switch between their fibres. Swept exhaustively to ground order 8 (7,480 pivots, 0
mismatches) BEFORE it was proved; that sweep is a computational seal, not a proof. **The declaration
is now proved** — trace `[propext, Classical.choice, Quot.sound]`, verified 2026-08-18. The clause
that used to end this sentence, asserting the declaration was still open, went false the moment the
overnight wave closed it and stayed that way for a day.

CORRECTED 2026-08-17, and the previous version is recorded as a defect rather than quietly replaced.
This theorem was stated for **arbitrary** `S T : QuotientV d v` and was **FALSE** in that form, at
`S = T`. Counterexample, found by a Codex wave that correctly refused to edit and lead-verified: take
`d = (0,1,1,1,1)` on five vertices with pivot `v = 0`. The realizations are the three perfect
matchings of `{1,2,3,4}`, all with `N(v) = ∅`, so they lie in one fibre with `S = T = ∅`. Taking
`G = {12,34}` and `H = {13,24}` gives `|E(G) ∆ E(H)| = 4`, a legal 2-switch, so the right side holds;
but the left side is `Adj S S`, false because `fromRel` is irreflexive and `(S ∆ S).card = 0 ≠ 2`.

The missing hypothesis is `S ≠ T`, which manuscript Theorem 5.4 has and this statement had dropped:
the prose reads "let `S ∈ I_v` and `T = S − b + a ∈ I_v`", which entails distinctness. With it the
biconditional is right in both directions — a 2-switch changes `N(v)` by at most one vertex, so
distinct neighborhoods joined by one are at symmetric difference exactly two.

Two further defects in the previous doc comment, both fixed: it called this "the machine-checked
Lemma 4.1" at a time when the declaration was still open, and it numbered the result 4.1 where the
manuscript has 5.4. -/
theorem quotient_adjacency (d : V → ℕ) (v : V) (S T : QuotientV d v) (hST : S ≠ T) :
    (quotientGraph d v).Adj S T ↔
      ∃ G H : Realization d, G.neighborFinset v = S.val ∧ H.neighborFinset v = T.val ∧
        (RealizationGraph d).Adj G H := by
  classical
  constructor
  · intro hAdj
    simp only [quotientGraph, SimpleGraph.fromRel_adj] at hAdj
    have hdiff : (S.val ∆ T.val).card = 2 := by
      rcases hAdj.2 with h | h
      · exact h
      · simpa [symmDiff_comm] using h
    obtain ⟨G₀, hG₀⟩ := S.property
    obtain ⟨H₀, hH₀⟩ := T.property
    have hScard : S.val.card = d v := by
      rw [← hG₀]
      simp [Realization.neighborFinset, SimpleGraph.card_neighborFinset_eq_degree,
        G₀.degree_eq v]
    have hTcard : T.val.card = d v := by
      rw [← hH₀]
      simp [Realization.neighborFinset, SimpleGraph.card_neighborFinset_eq_degree,
        H₀.degree_eq v]
    have hcard : S.val.card = T.val.card := hScard.trans hTcard.symm
    have hbalanced : (T.val \ S.val).card = (S.val \ T.val).card :=
      Finset.card_sdiff_comm hcard.symm
    have hsdiff_card : (S.val \ T.val).card = 1 := by
      rw [Finset.symmDiff_def,
        Finset.card_union_of_disjoint
          (Finset.sdiff_disjoint.mono_right Finset.sdiff_subset)] at hdiff
      omega
    have hsdiff_card' : (T.val \ S.val).card = 1 := by omega
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hsdiff_card
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hsdiff_card'
    have hbST : b ∈ S.val \ T.val := hb.symm.subset (Finset.mem_singleton_self b)
    have haTS : a ∈ T.val \ S.val := ha.symm.subset (Finset.mem_singleton_self a)
    have hbS : b ∈ S.val := (Finset.mem_sdiff.mp hbST).1
    have hbT : b ∉ T.val := (Finset.mem_sdiff.mp hbST).2
    have haT : a ∈ T.val := (Finset.mem_sdiff.mp haTS).1
    have haS : a ∉ S.val := (Finset.mem_sdiff.mp haTS).2
    have hTform : T.val = insert a (S.val.erase b) := by
      ext z
      constructor
      · intro hzT
        by_cases hzS : z ∈ S.val
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨by
            rintro rfl
            exact hbT hzT, hzS⟩))
        · have hz : z ∈ T.val \ S.val := Finset.mem_sdiff.mpr ⟨hzT, hzS⟩
          have : z = a := by simpa [ha] using hz
          exact Finset.mem_insert.mpr (Or.inl this)
      · intro hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact haT
        · obtain ⟨hzb, hzS⟩ := Finset.mem_erase.mp hz
          by_contra hzT
          have hz' : z ∈ S.val \ T.val := Finset.mem_sdiff.mpr ⟨hzS, hzT⟩
          have : z = b := by simpa [hb] using hz'
          exact hzb this
    have htarget :
        HasRealizationWithNeighborSet d v (insert a (S.val.erase b)) := by
      rw [← hTform]
      exact T.property
    obtain ⟨G, H, hG, hH, hadj⟩ :=
      quotient_adjacent hbS haS S.property htarget
    refine ⟨G, H, hG, ?_, hadj⟩
    rw [hTform]
    exact hH
  · rintro ⟨G, H, hG, hH, hAdj⟩
    have hneigh : G.neighborFinset v ≠ H.neighborFinset v := by
      intro h
      apply hST
      apply Subtype.ext
      rw [← hG, ← hH]
      exact h
    let D : SimpleGraph V :=
      { Adj := fun x y ↦ (G.graph.Adj x y ∧ ¬ H.graph.Adj x y) ∨
          (H.graph.Adj x y ∧ ¬ G.graph.Adj x y)
        symm := by
          constructor
          intro x y
          rintro (⟨hGxy, hHxy⟩ | ⟨hHxy, hGxy⟩)
          · exact Or.inl ⟨hGxy.symm, fun h ↦ hHxy h.symm⟩
          · exact Or.inr ⟨hHxy.symm, fun h ↦ hGxy h.symm⟩
        loopless := by
          constructor
          intro x
          simp }
    letI : DecidableRel D.Adj := Classical.decRel _
    have hDneighbor (x : V) :
        D.neighborFinset x = G.neighborFinset x ∆ H.neighborFinset x := by
      ext y
      simp [D, Realization.mem_neighborFinset, Finset.mem_symmDiff]
    have hDedge : D.edgeFinset = G.edgeFinset ∆ H.edgeFinset := by
      ext e
      induction e using Sym2.inductionOn with
      | _ x y =>
          simp [D, Realization.edgeFinset, SimpleGraph.mem_edgeFinset,
            SimpleGraph.mem_edgeSet, Finset.mem_symmDiff]
    change (G.edgeFinset ∆ H.edgeFinset).card = 4 at hAdj
    have hDcard : D.edgeFinset.card = 4 := by
      rw [hDedge]
      exact hAdj
    have hneighbor_card (x : V) :
        (G.neighborFinset x).card = (H.neighborFinset x).card := by
      simp [Realization.neighborFinset, SimpleGraph.card_neighborFinset_eq_degree,
        G.degree_eq x, H.degree_eq x]
    have hdegree (x : V) :
        D.degree x = 2 * (G.neighborFinset x \ H.neighborFinset x).card := by
      rw [SimpleGraph.degree, hDneighbor]
      rw [Finset.symmDiff_def, Finset.card_union_of_disjoint]
      · have hcards := Finset.card_sdiff_comm (hneighbor_card x)
        omega
      · exact Finset.sdiff_disjoint.mono_right Finset.sdiff_subset
    have hdeg_lower : ∀ x ∈ D.support, 2 ≤ D.degree x := by
      intro x hx
      have hpos : 0 < D.degree x := (D.degree_pos_iff_mem_support x).2 hx
      rw [hdegree] at hpos ⊢
      omega
    have hsum : ∑ x ∈ D.support.toFinset, D.degree x = 8 := by
      rw [D.sum_degrees_support_eq_twice_card_edges, hDcard]
    have hv : v ∈ D.support := by
      rw [← D.degree_pos_iff_mem_support v, ← D.card_neighborFinset_eq_degree,
        hDneighbor]
      exact Finset.card_pos.mpr (Finset.symmDiff_nonempty.mpr hneigh)
    have hneighbor_sub : D.neighborFinset v ⊆ D.support.toFinset.erase v := by
      intro x hx
      have hvx : D.Adj v x := by
        simpa [SimpleGraph.mem_neighborFinset] using hx
      exact Finset.mem_erase.mpr
        ⟨hvx.ne.symm, Set.mem_toFinset.mpr hvx.mem_support_right⟩
    have hcard_neighbor_le :
        (D.neighborFinset v).card ≤ (D.support.toFinset.erase v).card :=
      Finset.card_le_card hneighbor_sub
    have hvfin : v ∈ D.support.toFinset := Set.mem_toFinset.mpr hv
    have hsupp_card : D.degree v + 1 ≤ D.support.toFinset.card := by
      rw [D.card_neighborFinset_eq_degree,
        Finset.card_erase_of_mem hvfin] at hcard_neighbor_le
      have hsupp_pos : 0 < D.support.toFinset.card :=
        Finset.card_pos.mpr ⟨v, hvfin⟩
      omega
    have hsupp_bound : 2 * D.support.toFinset.card ≤ 8 := by
      calc
        2 * D.support.toFinset.card = ∑ _x ∈ D.support.toFinset, 2 := by
          simp [Nat.mul_comm]
        _ ≤ ∑ x ∈ D.support.toFinset, D.degree x := by
          exact Finset.sum_le_sum fun x hx ↦
            hdeg_lower x (Set.mem_toFinset.mp hx)
        _ = 8 := hsum
    have hdegv : D.degree v = 2 := by
      have hlower := hdeg_lower v hv
      have htwice := hdegree v
      omega
    have hdiff : (S.val ∆ T.val).card = 2 := by
      rw [← hG, ← hH, ← hDneighbor, D.card_neighborFinset_eq_degree]
      exact hdegv
    simp only [quotientGraph, SimpleGraph.fromRel_adj]
    exact ⟨hST, Or.inl hdiff⟩

/-! ## 1b. THE BRIDGE — attaching `(Q*)` to the quotient (manuscript Theorem 5.3, Corollary 5.5)

**Why this section exists, and why it is the most important gap the lane had.** `QStar.lean` proves
`(Q*)` completely — 252 declarations, no `sorry`, no cited axiom. **It was connected to nothing.**
`qstar` is a theorem about `exchangeGraph F` for a *shifted family* `F`; everything here speaks of
`quotientGraph d v`; and until this section **nothing in Lean said those are the same object**, so
§7's proof could not be invoked about a realization graph at all. Measured 2026-08-18: `qstar`
occurred exactly once outside its own module, inside a doc comment. That `SimpleGraph.IsCliqueSum`
is shared between the two makes the gap easy to miss — shared vocabulary is not a bridge.

**The encoding, which avoids a subtype ground.** The manuscript reads `I_v` as a family of subsets of
`[n−1]`, suggesting the ground `{u : V // u ≠ v}` and a transport across it. That is not needed.
Order **all** of `V` with `v` **maximal** and the rest non-increasing by degree. Then `v` can play
neither role in the shift condition — not `j`, since `j ∈ X` and `v` belongs to no neighborhood of
`v`; and not `i`, since `i < j` would put `v` strictly below something. So `I_v` is shifted as a
family of subsets of `V`, and `QuotientV d v` and `QStar.ExchangeV I_v` are the *same* subtype of
`Finset V` up to an iff on membership.

**Where the order lives.** `QStar` needs `[LinearOrder α]`, so the two statements naming
`exchangeGraph` carry `[LinearOrder V]`. **`quotient_qstar`, the one the assembly consumes, does
not** — the order is chosen inside its proof. This is the same discipline settled for the yFamily
transport in §8.1′ and recorded in `results/2026-08-18_sec8_encoding_settled.md`: an order may be a
proof device, never a hypothesis of a statement `MainLine` consumes.

**★ Theorem 5.3 needs no external fact, and this is now settled in both directions.** An earlier draft
of its proof moved one unit from a strictly larger residual entry to a strictly smaller one and then
cited Ruch–Gutman — *graphical sequences of a given even sum form a down-set in the majorization
order* — a heavy classical input for a very light step. The single-unit case is **constructive and
elementary**: in any realization, `deg i > deg j` forces some `w` adjacent to `i` and not to `j`,
because otherwise `N(i) ∖ {j} ⊆ N(j) ∖ {i}` would give `deg i ≤ deg j`; and `G − iw + jw` realizes the
transferred function. That is `exists_realization_unit_transfer` below, and it is proved and consumed
by `quotientFamily_isShifted`.

**Corrected 2026-08-24.** This paragraph read *"the manuscript currently claims it does"*, called
Ruch–Gutman *"one of the four external inputs"*, and closed conditionally with *"If it goes through,
Ruch–Gutman leaves the trust surface"*. All three went stale on 2026-08-18: it did go through, the
manuscript's §5.3 already says the proof does not invoke Ruch–Gutman, `RG1979` is cited nowhere, and
the surface has been at three such inputs since. The error direction is the dangerous one — it
**over**-states the trust surface, which invites a reader to re-add a citation that was deliberately
removed.

**Verified before any of this was written** (`compute/unit_transfer_check_2026_08_18.py`), over every
graph on at most 6 vertices: the transfer claim on **364,412** instances with **0** failures, and the
constructive swap vertex `w` existing in every one of them; and Theorem 5.3 in exactly the `v`-maximal
encoding below, **136,128** shift instances, **0** failures.
-/

/-- The family `I_v` of manuscript §5: the neighborhoods of `v` that actually occur in realizations,
as a `Finset (Finset V)`. Same content as `QuotientV d v`, packaged so `QStar` can consume it. -/
noncomputable def realizableNeighborhoods (d : V → ℕ) (v : V) : Finset (Finset V) :=
  letI := Classical.decPred (HasRealizationWithNeighborSet d v)
  Finset.univ.filter (HasRealizationWithNeighborSet d v)

theorem mem_realizableNeighborhoods {d : V → ℕ} {v : V} {S : Finset V} :
    S ∈ realizableNeighborhoods d v ↔ HasRealizationWithNeighborSet d v S := by
  classical
  simp [realizableNeighborhoods]

/-- **The unit-transfer lemma — the elementary fact that replaces Ruch–Gutman in Theorem 5.3.**
Moving one unit of demand from a strictly larger entry to a strictly smaller one preserves
graphicality, by a single edge swap rather than by majorization theory.

Proof, for the wave that formalizes it: `deg i > deg j` gives some `w ∉ {i,j}` with `w ~ i`, `w ≁ j`
— otherwise `N(i) ∖ {j} ⊆ N(j) ∖ {i}`, and since `j ∈ N(i) ↔ i ∈ N(j)` the two sets have cardinality
`deg i − [i ~ j]` and `deg j − [i ~ j]`, forcing `deg i ≤ deg j`. Then delete `iw` and insert `jw`:
legal because `iw` is an edge and `jw` is not, and it changes exactly the degrees of `i` and `j`. -/
theorem exists_realization_unit_transfer {W : Type u} [Fintype W] [DecidableEq W] {f : W → ℕ}
    (G : Realization f) {i j : W} (hij : i ≠ j) (hlt : f j < f i) :
    Graphical (Function.update (Function.update f i (f i - 1)) j (f j + 1)) := by
  letI := G.adjDecidable
  let A : Finset W := (G.graph.neighborFinset i).erase j
  let B : Finset W := (G.graph.neighborFinset j).erase i
  have hAcard : A.card = f i - if G.graph.Adj i j then 1 else 0 := by
    by_cases hadj : G.graph.Adj i j
    · have hj : j ∈ G.graph.neighborFinset i := by
        simpa [SimpleGraph.mem_neighborFinset] using hadj
      simp [A, Finset.card_erase_of_mem hj, G.degree_eq i, hadj]
    · have hj : j ∉ G.graph.neighborFinset i := by
        simpa [SimpleGraph.mem_neighborFinset] using hadj
      simp [A, Finset.erase_eq_of_notMem hj, G.degree_eq i, hadj]
  have hBcard : B.card = f j - if G.graph.Adj i j then 1 else 0 := by
    by_cases hadj : G.graph.Adj i j
    · have hi : i ∈ G.graph.neighborFinset j := by
        simpa [SimpleGraph.mem_neighborFinset] using hadj.symm
      simp [B, Finset.card_erase_of_mem hi, G.degree_eq j, hadj]
    · have hi : i ∉ G.graph.neighborFinset j := by
        simp only [SimpleGraph.mem_neighborFinset]
        exact fun h ↦ hadj h.symm
      simp [B, Finset.erase_eq_of_notMem hi, G.degree_eq j, hadj]
  have hBA : B.card < A.card := by
    by_cases hadj : G.graph.Adj i j
    · rw [hAcard, hBcard, if_pos hadj]
      have hjpos : 0 < f j := by
        rw [← G.degree_eq j, ← SimpleGraph.card_neighborFinset_eq_degree]
        exact Finset.card_pos.mpr ⟨i, by
          simpa [SimpleGraph.mem_neighborFinset] using hadj.symm⟩
      omega
    · rw [hAcard, hBcard, if_neg hadj]
      omega
  have hnot_sub : ¬ A ⊆ B := by
    intro hsub
    exact (not_le_of_gt hBA) (Finset.card_le_card hsub)
  obtain ⟨w, hwA, hwB⟩ := Finset.not_subset.mp hnot_sub
  have hwj : w ≠ j := (Finset.mem_erase.mp hwA).1
  have hiw : G.graph.Adj i w := by
    simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_erase.mp hwA).2
  have hwi : w ≠ i := hiw.ne'
  have hjw : ¬ G.graph.Adj j w := by
    intro hadj
    apply hwB
    exact Finset.mem_erase.mpr ⟨hwi, by
      simpa [SimpleGraph.mem_neighborFinset] using hadj⟩
  let G' : SimpleGraph W := transferGraph G.graph i j w
  let hG'dec : DecidableRel G'.Adj := inferInstance
  refine ⟨G', hG'dec, ?_⟩
  letI := hG'dec
  intro x
  by_cases hxi : x = i
  · subst x
    rw [transferGraph_degree_x (G := G.graph) (y := j) hiw hjw hij, G.degree_eq i]
    simp [Function.update, hij]
  · by_cases hxj : x = j
    · subst x
      rw [transferGraph_degree_y (G := G.graph) (x := i) hjw hij hwj.symm, G.degree_eq j]
      simp [Function.update]
    · by_cases hxw : x = w
      · subst x
        rw [transferGraph_degree_z (G := G.graph) hiw hjw hwj.symm, G.degree_eq w]
        simp [Function.update, hxi, hxj]
      · rw [transferGraph_degree_other (G := G.graph) hxi hxj hxw, G.degree_eq x]
        simp [Function.update, hxi, hxj]

/-- **Manuscript Theorem 5.3.** `I_v` is a shifted family of `d v`-subsets.

Stated against an explicit order rather than a chosen one, so the hypotheses say exactly which orders
work: `v` maximal, and non-increasing degree off `v`. Existence of such an order is
`exists_pivotMaximal_degreeAntitone_order`; separating the two keeps this statement free of a choice
it does not need. -/
theorem quotientFamily_isShifted [LinearOrder V] (d : V → ℕ) (v : V)
    (hvmax : ∀ u : V, u ≤ v)
    (hmono : ∀ i j : V, i ≠ v → j ≠ v → i < j → d j ≤ d i)
    (hne : (realizableNeighborhoods d v).Nonempty) :
    QStar.IsShifted (realizableNeighborhoods d v) (d v) := by
  classical
  refine ⟨hne, ?_, ?_⟩
  · intro X hXF
    obtain ⟨G, hG⟩ := mem_realizableNeighborhoods.mp hXF
    rw [← hG]
    simp [Realization.neighborFinset, SimpleGraph.card_neighborFinset_eq_degree,
      G.degree_eq v]
  · intro X hXF i j hjX hij hiX
    obtain ⟨G, hG⟩ := mem_realizableNeighborhoods.mp hXF
    have hvX : v ∉ X := by
      intro hv
      have hv' : v ∈ G.neighborFinset v := by rwa [hG]
      exact G.graph.irrefl ((G.mem_neighborFinset v v).mp hv')
    have hjv : j ≠ v := by
      intro hjv
      exact hvX (hjv ▸ hjX)
    have hiv : i ≠ v := by
      intro hiv
      subst i
      exact (not_lt_of_ge (hvmax j)) hij
    have hposX : ∀ u ∈ X, 0 < d u := by
      intro u huX
      have huv : G.graph.Adj v u := (G.mem_neighborFinset v u).mp (by rwa [hG])
      rw [← G.degree_eq u, ← SimpleGraph.card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨v, by
        simpa [SimpleGraph.mem_neighborFinset] using huv.symm⟩
    have hjpos : 0 < d j := hposX j hjX
    have hdji : d j ≤ d i := hmono i j hiv hjv hij
    let ii : {u : V // u ≠ v} := ⟨i, hiv⟩
    let jj : {u : V // u ≠ v} := ⟨j, hjv⟩
    let f : {u : V // u ≠ v} → ℕ := residualDegree d v X
    have hji : j ≠ i := ne_of_gt hij
    have hiij : ii ≠ jj := by
      intro h
      exact (ne_of_lt hij) (congrArg Subtype.val h)
    have hltResidual : f jj < f ii := by
      simp [f, ii, jj, residualDegree, hjX, hiX]
      omega
    have hf : Graphical f := by
      exact observation0_delete_direction ⟨G, hG⟩
    let R : Realization f := realizationOfGraphical hf
    have htrans :
        Graphical (Function.update (Function.update f ii (f ii - 1)) jj (f jj + 1)) :=
      exists_realization_unit_transfer R hiij hltResidual
    let Y : Finset V := insert i (X.erase j)
    have hresidual :
        residualDegree d v Y =
          Function.update (Function.update f ii (f ii - 1)) jj (f jj + 1) := by
      funext z
      by_cases hzi : z = ii
      · subst z
        simp [Y, f, ii, jj, residualDegree, hiij, hiX]
      · by_cases hzj : z = jj
        · subst z
          simp [Y, f, ii, jj, residualDegree, hji, hjX]
          omega
        · have hzival : z.val ≠ i := by
            intro h
            apply hzi
            exact Subtype.ext h
          have hzjval : z.val ≠ j := by
            intro h
            apply hzj
            exact Subtype.ext h
          simp [Y, f, ii, jj, residualDegree, hzi, hzj, hzival, hzjval]
    have hYv : v ∉ Y := by
      simp [Y, hiv.symm, hvX]
    have hYcard : Y.card = d v := by
      have hXcard : X.card = d v := by
        rw [← hG]
        simp [Realization.neighborFinset, SimpleGraph.card_neighborFinset_eq_degree,
          G.degree_eq v]
      have hiErase : i ∉ X.erase j := by simp [hiX]
      change (insert i (X.erase j)).card = d v
      rw [Finset.card_insert_of_notMem hiErase, Finset.card_erase_of_mem hjX, hXcard]
      have hdvpos : 0 < d v := by
        rw [← hXcard]
        exact Finset.card_pos.mpr ⟨j, hjX⟩
      omega
    have hYpos : ∀ u, u ∈ Y → 0 < d u := by
      intro u huY
      rcases Finset.mem_insert.mp huY with rfl | hu
      · omega
      · exact hposX u (Finset.mem_of_mem_erase hu)
    apply mem_realizableNeighborhoods.mpr
    apply observation0_add_direction hYv hYcard hYpos
    rw [hresidual]
    exact htrans

/-- Such an order always exists: sort the ground by non-increasing degree and put `v` last. This is
the only choice the bridge makes, and it is made inside proofs. -/
theorem exists_pivotMaximal_degreeAntitone_order (d : V → ℕ) (v : V) :
    ∃ _ : LinearOrder V, (∀ u : V, u ≤ v) ∧
      ∀ i j : V, i ≠ v → j ≠ v → i < j → d j ≤ d i := by
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let key : V → Lex (ℕ × Lex (OrderDual ℕ × Fin (Fintype.card V))) := fun u ↦
    toLex (if u = v then 1 else 0,
      toLex (OrderDual.toDual (d u), e u))
  have hkey : Function.Injective key := by
    intro a b hab
    have hab' := toLex.injective hab
    have hab'' := toLex.injective (congrArg Prod.snd hab')
    exact e.injective (congrArg Prod.snd hab'')
  let inst : LinearOrder V := LinearOrder.lift' key hkey
  refine ⟨inst, ?_, ?_⟩
  · intro u
    change key u ≤ key v
    by_cases huv : u = v
    · subst u
      exact le_rfl
    · simp [key, huv, Prod.Lex.toLex_le_toLex]
  · intro i j hiv hjv hijlt
    change key i < key j at hijlt
    simp only [key, hiv, hjv, if_false, Prod.Lex.toLex_lt_toLex, lt_self_iff_false,
      false_or, true_and, OrderDual.toDual_lt_toDual] at hijlt
    rcases hijlt with hijdeg | hijdeg
    · exact hijdeg.le
    · exact le_of_eq hijdeg.1.symm

/-- **Manuscript Corollary 5.5, the transport half.** The quotient at `v` *is* the Johnson graph
`J(I_v)` of Section 7 — as an isomorphism of graphs, not merely a coincidence of adjacency formulas.

⚠ **This is the trivial half, and the label alone would mislead an auditor** (noted 2026-08-24). Both
sides are `fromRel` on the same relation, so this is `Equiv.subtypeEquivRight` and two lines.
Corollary 5.5's substantive content — that the quotient defined by 2-switches between fibres is the
symmetric-difference graph — is `quotient_adjacency`, which carries the Theorem 5.4 label. The
assembly does consume that half: `ledgerQuotientAdj_of_quotientAdj` calls it to turn each literal
quotient edge into a cross-fibre 2-switch. An auditor asking "is Corollary 5.5 formalized?" should be
sent to both.

Both sides are `SimpleGraph.fromRel` of "symmetric difference has two elements" on a subtype of
`Finset V`, so the content is the membership iff of `mem_realizableNeighborhoods`; the value of
stating it is that it is what lets `qstar` be *applied*. -/
noncomputable def quotientIsoExchange [LinearOrder V] (d : V → ℕ) (v : V) :
    quotientGraph d v ≃g QStar.exchangeGraph (realizableNeighborhoods d v) := by
  let φ : QuotientV d v ≃ QStar.ExchangeV (realizableNeighborhoods d v) :=
    Equiv.subtypeEquivRight fun S ↦ mem_realizableNeighborhoods.symm
  refine ⟨φ, ?_⟩
  intro A B
  have hA : (φ A).val = A.val := rfl
  have hB : (φ B).val = B.val := rfl
  simp [quotientGraph, QStar.exchangeGraph, hA, hB]

/-- **★ `(Q*)` ON THE QUOTIENT — the theorem the assembly consumes, and the point of this section.**

Manuscript Theorem 7.7 transported along Corollary 5.5. **The statement carries no order**: the
`[LinearOrder V]` needed to say "shifted" is chosen inside the proof, via
`exists_pivotMaximal_degreeAntitone_order`, and `quotientGraph`, `HasHamPath` and
`SimpleGraph.IsCliqueSum` are all order-free.

Proving this is what turns `(Q*)` from an isolated result into an input of this paper. Until it
exists, `qstar` is applied nowhere. -/
theorem quotient_qstar (d : V → ℕ) (v : V) (S T : QuotientV d v) (hST : S ≠ T) :
    HasHamPath (quotientGraph d v) S T ↔ ¬ (quotientGraph d v).IsCliqueSum S T := by
  classical
  obtain ⟨inst, hvmax, hmono⟩ := exists_pivotMaximal_degreeAntitone_order d v
  letI : LinearOrder V := inst
  let φ := quotientIsoExchange d v
  have hne : (realizableNeighborhoods d v).Nonempty :=
    ⟨S.val, mem_realizableNeighborhoods.mpr S.property⟩
  have hshifted : QStar.IsShifted (realizableNeighborhoods d v) (d v) :=
    quotientFamily_isShifted d v hvmax hmono hne
  have hpath :
      HasHamPath (quotientGraph d v) S T ↔
        HasHamPath (QStar.exchangeGraph (realizableNeighborhoods d v)) (φ S) (φ T) := by
    constructor
    · intro h
      apply hasHamPath_iso φ.symm
      simpa [φ] using h
    · exact hasHamPath_iso φ
  have hbad :
      ¬ (QStar.exchangeGraph (realizableNeighborhoods d v)).IsCliqueSum (φ S) (φ T) ↔
        ¬ (quotientGraph d v).IsCliqueSum S T :=
    not_congr (QStar.isCliqueSum_iso_iff φ).symm
  rw [hpath, QStar.qstar hshifted (φ S) (φ T) (φ.injective.ne hST)]
  change
    (¬ (QStar.exchangeGraph (realizableNeighborhoods d v)).IsCliqueSum (φ S) (φ T)) ↔
      ¬ (quotientGraph d v).IsCliqueSum S T
  exact hbad

/-! ## 2. Fibres, admissibility, and the difference support -/

/-- The `v`-fibre over a neighborhood `S`. -/
def Fibre (d : V → ℕ) (v : V) (S : Finset V) : Set (Realization d) :=
  {G | G.neighborFinset v = S}

/-- **A pivot has a non-bipartite fibre**, stated the way the route consumes it: some triangle of
the
realization graph lies inside a single `v`-fibre. Equivalent to non-bipartiteness of that fibre by
the held Barrus classification (triangle-free ⟺ bipartite), which is why the prose says
"non-bipartite fibre" and "a triangle avoiding `v`" interchangeably. -/
def HasNonBipartiteFibre (d : V → ℕ) (v : V) : Prop :=
  ∃ A B C : Realization d,
    A.neighborFinset v = B.neighborFinset v ∧ B.neighborFinset v = C.neighborFinset v ∧
    (RealizationGraph d).Adj A B ∧ (RealizationGraph d).Adj B C ∧ (RealizationGraph d).Adj A C

/-- A non-2-colorable realization fibre contains an explicit triangle.  Deleting the pivot
identifies the fibre with the realization graph of the residual degree function
(`fibreDeleteIso`), where Barrus's Theorem 9 turns non-bipartiteness into failure of triangle
freeness. -/
theorem hasNonBipartiteFibre_of_fibreNonbip {d : V → ℕ} {v : V} {S : Finset V}
    (hSreal : HasRealizationWithNeighborSet d v S)
    (hnb : ¬ ∃ col : interfaceFibre d v S → Bool,
      IsProper2Coloring (interfaceFibreGraph d v S) col) :
    HasNonBipartiteFibre d v := by
  classical
  obtain ⟨G₀, hG₀⟩ := hSreal
  have hvS : v ∉ S := by
    intro hv
    have hvN : v ∈ G₀.neighborFinset v := by simpa [hG₀] using hv
    exact G₀.graph.irrefl ((G₀.mem_neighborFinset v v).mp hvN)
  have hcard : S.card = d v := by
    rw [← hG₀]
    simp [Realization.neighborFinset, SimpleGraph.card_neighborFinset_eq_degree,
      G₀.degree_eq v]
  have hpos : ∀ u ∈ S, 0 < d u := by
    intro u hu
    have hvu : G₀.graph.Adj v u := by
      rw [← G₀.mem_neighborFinset, hG₀]
      exact hu
    rw [← G₀.degree_eq u]
    exact hvu.symm.degree_pos_left
  let e := fibreDeleteIso hvS hcard hpos
  have hresNonbip :
      ¬ IsBipartiteRealizationGraph (residualDegree d v S) := by
    rintro ⟨col, hcol⟩
    apply hnb
    refine ⟨fun F => col (e F), ?_⟩
    intro A B hAB
    exact hcol (e A) (e B) (e.map_rel_iff.mpr hAB)
  have hresNotTriangleFree :
      ¬ IsTriangleFreeRealizationGraph (residualDegree d v S) := by
    intro hfree
    exact hresNonbip
      ((barrus_theorem9_bipartite_iff_triangleFree (residualDegree d v S)).mpr hfree)
  obtain ⟨copy⟩ := (SimpleGraph.not_cliqueFree_iff 3).mp hresNotTriangleFree
  let A' : Realization (residualDegree d v S) := copy.toHom 0
  let B' : Realization (residualDegree d v S) := copy.toHom 1
  let C' : Realization (residualDegree d v S) := copy.toHom 2
  have hAB' : (RealizationGraph (residualDegree d v S)).Adj A' B' := by
    exact copy.toHom.map_rel (by simp [A', B'])
  have hBC' : (RealizationGraph (residualDegree d v S)).Adj B' C' := by
    exact copy.toHom.map_rel (by simp [B', C'])
  have hAC' : (RealizationGraph (residualDegree d v S)).Adj A' C' := by
    exact copy.toHom.map_rel (by simp [A', C'])
  let A : interfaceFibre d v S := e.symm A'
  let B : interfaceFibre d v S := e.symm B'
  let C : interfaceFibre d v S := e.symm C'
  refine ⟨A.1, B.1, C.1, A.2.trans B.2.symm, B.2.trans C.2.symm, ?_, ?_, ?_⟩
  · exact e.symm.map_rel_iff.mpr hAB'
  · exact e.symm.map_rel_iff.mpr hBC'
  · exact e.symm.map_rel_iff.mpr hAC'

/-- The difference support `D(X,Y)`: the ground vertices where two realizations disagree. -/
def DifferenceSupport (d : V → ℕ) (X Y : Realization d) : Set V :=
  {v | X.neighborFinset v ≠ Y.neighborFinset v}

/-- **Admissible pivot** for the pair `(X, Y)`: it separates them and carries a non-bipartite fibre.
This is exactly what the separator-buffer theorem delivers. -/
def AdmissiblePivot (d : V → ℕ) (X Y : Realization d) (v : V) : Prop :=
  v ∈ DifferenceSupport d X Y ∧ HasNonBipartiteFibre d v

/-- **Exceptional pivot**: the quotient at `v` is a clique-sum *and* the prescribed pair
`{π_v X, π_v Y}` is its universal pair — the one configuration in which `(Q*)` supplies no path. -/
def ExceptionalPivot (d : V → ℕ) (X Y : Realization d) (v : V) : Prop :=
  ∃ hX : HasRealizationWithNeighborSet d v (X.neighborFinset v),
    ∃ hY : HasRealizationWithNeighborSet d v (Y.neighborFinset v),
      (quotientGraph d v).IsCliqueSum ⟨_, hX⟩ ⟨_, hY⟩

/-! ## 3. The main-line hypotheses -/

/-- Every ground vertex is **active**: it has at least two realizable neighborhoods. -/
def Active (d : V → ℕ) : Prop :=
  ∀ v : V, ∃ S T : Finset V, S ≠ T ∧
    HasRealizationWithNeighborSet d v S ∧ HasRealizationWithNeighborSet d v T

/--
**CITED — Brualdi (Ryser--Haber--Chen).** Richard A. Brualdi,
*Combinatorial Matrix Classes*, Cambridge University Press (2006), Theorem 3.4.1,
rendered p. 63, together with its displayed consequence on rendered p. 65. The equivalences
(i)--(iii) are attributed there to Ryser [59, 62] and Haber [30], and (i) ↔ (iv) to Chen [17].
Verbatim statement of the displayed consequence consumed here:

> if `t_kl = 0` for integers `k` and `l` with `(k,l) ≠ (0,n), (m,0)`, then each matrix `A` in
> `A(R,S)` has a decomposition of the form `A = [[J_{k,l}, X], [Y, O_{m−k,n−l}]]`. At least one of
> the matrices `J_{k,l}` and `O_{m−k,n−l}` is nonvacuous and their positions within `A` are
> invariant positions of `A(R,S)`.

Bibliography key: `brualdiCombinatorialMatrixClasses2006`. ISBN 978-0-521-86565-4,
Encyclopedia of Mathematics and its Applications, vol. 108. The source has no DOI.

Local source pin:
`/mnt/c/Users/jbaggett/Zotero/storage/II8WEZBG/Brualdi - 2006 - Combinatorial matrix classes.pdf`,
SHA-256 `5779aaac8a18b6c45b2d5f72dcca37bce91e7f5d5ef0d875c0bf140ce0fe51db`.

Formal scope: Theorem 3.4.1 (i) ↔ (ii) supplies `t_kl = 0` from an invariant position. The book
states the result for nonincreasing margins; sortedness is absorbed here by relabeling rows and
columns, which bijects the classes and carries invariant positions to invariant positions.
-/
axiom invariantPosition_forces_block {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ)
    (hne : Nonempty (MarginClass r s))
    (i₀ : Fin m) (j₀ : Fin n) (hinv : ¬ CellVaries r s i₀ j₀) :
    ∃ P : Finset (Fin m), ∃ Q : Finset (Fin n),
      ((P.Nonempty ∧ Q.Nonempty) ∨ (Pᶜ.Nonempty ∧ Qᶜ.Nonempty)) ∧
      ∀ M : MarginClass r s,
        (∀ i ∈ P, ∀ j ∈ Q, M.val i j = true) ∧
        (∀ i ∉ P, ∀ j ∉ Q, M.val i j = false)

/-- The concrete interface meant by “the clique--independent incidence matrix of a split degree
function”. Rows and columns relabel the whole ground set, the margin-class flip graph is the
realization graph, and every represented realization has the fixed clique/independent side edges
and its matrix entries as the cross edges. -/
structure SplitIncidenceModel {m n : ℕ} (d : V → ℕ)
    (r : Fin m → ℕ) (s : Fin n → ℕ) where
  vertexEquiv : (Fin m ⊕ Fin n) ≃ V
  realizationIso : flipGraph r s ≃g RealizationGraph d
  left_clique : ∀ (M : MarginClass r s) (i k : Fin m), i ≠ k →
    (realizationIso M).graph.Adj (vertexEquiv (Sum.inl i)) (vertexEquiv (Sum.inl k))
  right_independent : ∀ (M : MarginClass r s) (j l : Fin n),
    ¬ (realizationIso M).graph.Adj (vertexEquiv (Sum.inr j)) (vertexEquiv (Sum.inr l))
  cross_adj_iff : ∀ (M : MarginClass r s) (i : Fin m) (j : Fin n),
    (realizationIso M).graph.Adj (vertexEquiv (Sum.inl i)) (vertexEquiv (Sum.inr j)) ↔
      M.val i j = true

/-- In a split-incidence model, equality of matrix rows is exactly equality of the corresponding
ground-vertex neighborhoods. -/
theorem SplitIncidenceModel.rowPat_eq_iff_neighborFinset_eq {m n : ℕ} {d : V → ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ} (model : SplitIncidenceModel d r s)
    (M N : MarginClass r s) (i : Fin m) :
    rowPat i M = rowPat i N ↔
      (model.realizationIso M).neighborFinset (model.vertexEquiv (Sum.inl i)) =
        (model.realizationIso N).neighborFinset (model.vertexEquiv (Sum.inl i)) := by
  classical
  constructor
  · intro hrow
    ext x
    rw [← model.vertexEquiv.apply_symm_apply x]
    cases h : model.vertexEquiv.symm x with
    | inl k =>
        simp only [Realization.mem_neighborFinset]
        by_cases hik : i = k
        · subst k
          simp
        · constructor
          · intro _
            exact model.left_clique N i k hik
          · intro _
            exact model.left_clique M i k hik
    | inr j =>
        simp only [Realization.mem_neighborFinset, model.cross_adj_iff]
        simpa [rowPat] using congrFun hrow j
  · intro hneighbor
    funext j
    apply Bool.eq_iff_iff.mpr
    change M.val i j = true ↔ N.val i j = true
    rw [← model.cross_adj_iff M i j, ← model.cross_adj_iff N i j]
    rw [← Realization.mem_neighborFinset, ← Realization.mem_neighborFinset, hneighbor]

/-- In a split-incidence model, equality of matrix columns is exactly equality of the corresponding
ground-vertex neighborhoods. -/
theorem SplitIncidenceModel.colPat_eq_iff_neighborFinset_eq {m n : ℕ} {d : V → ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ} (model : SplitIncidenceModel d r s)
    (M N : MarginClass r s) (j : Fin n) :
    colPat j M = colPat j N ↔
      (model.realizationIso M).neighborFinset (model.vertexEquiv (Sum.inr j)) =
        (model.realizationIso N).neighborFinset (model.vertexEquiv (Sum.inr j)) := by
  classical
  constructor
  · intro hcol
    ext x
    rw [← model.vertexEquiv.apply_symm_apply x]
    cases h : model.vertexEquiv.symm x with
    | inl i =>
        simp only [Realization.mem_neighborFinset, SimpleGraph.adj_comm,
          model.cross_adj_iff]
        simpa [colPat] using congrFun hcol i
    | inr l =>
        simp only [Realization.mem_neighborFinset]
        constructor
        · exact fun hAdj => False.elim ((model.right_independent M j l) hAdj)
        · exact fun hAdj => False.elim ((model.right_independent N j l) hAdj)
  · intro hneighbor
    funext i
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hM
      have hAdjM := (model.cross_adj_iff M i j).2 hM
      have hmemM : model.vertexEquiv (Sum.inl i) ∈
          (model.realizationIso M).neighborFinset (model.vertexEquiv (Sum.inr j)) :=
        (Realization.mem_neighborFinset _ _ _).2 hAdjM.symm
      have hmemN : model.vertexEquiv (Sum.inl i) ∈
          (model.realizationIso N).neighborFinset (model.vertexEquiv (Sum.inr j)) := by
        rw [← hneighbor]
        exact hmemM
      exact (model.cross_adj_iff N i j).1
        ((Realization.mem_neighborFinset _ _ _).1 hmemN).symm
    · intro hN
      have hAdjN := (model.cross_adj_iff N i j).2 hN
      have hmemN : model.vertexEquiv (Sum.inl i) ∈
          (model.realizationIso N).neighborFinset (model.vertexEquiv (Sum.inr j)) :=
        (Realization.mem_neighborFinset _ _ _).2 hAdjN.symm
      have hmemM : model.vertexEquiv (Sum.inl i) ∈
          (model.realizationIso M).neighborFinset (model.vertexEquiv (Sum.inr j)) := by
        rw [hneighbor]
        exact hmemN
      exact (model.cross_adj_iff M i j).1
        ((Realization.mem_neighborFinset _ _ _).1 hmemM).symm

/-- The degree multiset of `d`, sorted non-increasingly. -/
noncomputable def degreeList (d : V → ℕ) : List ℕ :=
  (Finset.univ.val.map d).sort (· ≥ ·)

/-- The Erdős–Gallai inequality **holds with equality** at `k`. -/
noncomputable def ErdosGallaiEqualityAt (d : V → ℕ) (k : ℕ) : Prop :=
  ((degreeList d).take k).sum
    = k * (k - 1) + (((degreeList d).drop k).map (fun x => min x k)).sum

/-- **STAND-IN, with a faithfulness obligation attached.** The prose hypothesis is *Tyshkevich
indecomposability*. The computational sweeps in this lane test it by the Erdős–Gallai criterion —
`d` is decomposable exactly when Erdős–Gallai holds with equality at some `k` — and that criterion,
written out honestly, is what appears here.

**This is the criterion, not a definition of Tyshkevich indecomposability.** Their equivalence is
`tyshkevich_iff_no_EG_equality` below and is a real obligation, not a convention. Until it is
discharged, every statement below carrying this hypothesis is about the Erdős–Gallai condition and
not literally about Tyshkevich's.

⚠ An earlier draft of this file gave this definition a deliberately-inert body. That was a mistake
and is recorded rather than quietly fixed: the inert body was **vacuously true**, which would have
made `MainLine` weaker than intended and therefore `sbPlus` and `separator_buffer` *stronger* than
the theorems they name — a statement that looks proved while asserting something possibly false.
A placeholder hypothesis must be *hard to satisfy*, never *easy*. -/
noncomputable def NoErdosGallaiEquality (d : V → ℕ) : Prop :=
  ∀ k : ℕ, 0 < k → k < Fintype.card V → ¬ ErdosGallaiEqualityAt d k

/-- **Tyshkevich decomposability, from the definition.** A graph is a Tyshkevich composition when its
vertices split as `A ⊎ B ⊎ C` with `A ∪ B` and `C` both nonempty, `A` a clique, `B` independent, `A`
complete to `C`, and `B` anticomplete to `C`. Edges inside `C` and between `A` and `B` are
unconstrained: that is the splitted-graph factor `(A, B)` composed with an arbitrary graph on `C`.

`B` is spelled `Cᶜ \ A` rather than carried as a third finset, so the partition is automatic and
cannot be stated inconsistently.

**Why this replaced `NoErdosGallaiEquality`, which is the honest version of this module's history.**
That definition was introduced as a STAND-IN for this one, with the equivalence recorded as an open
obligation, on the reading that `d` is decomposable exactly when Erdős–Gallai holds with equality at
some `k`. **Measured 2026-08-18: that is false in both directions.** `P₄`, the sequence `(2,2,1,1)`,
is indecomposable and has an equality at `k = 2`; `(1,1,1,1,0)` is decomposable and has none. Under
the other three `MainLine` hypotheses the error is one-sided — over the 161 main-line sequences
through ground order 7 there are **0** cases where the stand-in claimed more than the paper and
**26** where it claimed less — so the stand-in was sound but strictly stronger, and every theorem
carrying `MainLine` was a proper special case of the theorem it named.
`results/2026-08-18_tyshkevich_not_equivalent_to_eg.md`.

**⚠ One obligation remains, and it is smaller than the one it replaces.** This says *some*
realization decomposes, so `¬ TyshkevichDecomposable` says *no* realization does. Tyshkevich's
theorem — that the canonical decomposition depends only on the degree sequence — makes that the
paper's condition exactly. Until it is formalized, the `∃` reading is the deliberate choice: it is
the STRONGER form of indecomposability, so it can only make the theorems harder, never let them
claim more. Checked, not assumed: all realizations of a sequence agree, 0 disagreements through
ground order 7 (`compute/qstar_interface_check.py`, `tyshkevich_agreement_check`).

**⚠ That paragraph justifies only the NEGATIVE use, and there is a positive one.** Added 2026-08-24
after an adversary pass on the assembly pointed out that the reasoning above is stated as if
`¬ TyshkevichDecomposable` were the only consumer. `MainLine.indecomposable` is indeed negative, and
there the `∃` form is the stronger hypothesis and therefore safe. But
`isMH_of_tyshkevichDecomposable_of_IH` consumes the predicate **positively**, and there the `∃` form
is the WEAKER hypothesis, so that branch claims more than the paper's `∀`-reading rather than less —
the opposite of what the paragraph above would lead a reader to conclude.

It is nevertheless sound, and this is why: `tyshkevich_forced_in_every_realization` upgrades a single
witness to every realization. The degree-sum identity it turns on depends only on `d`, so one witness
forces the structure throughout the class. **A reader re-deriving "is the `∃` reading safe?" from the
paragraph above alone gets the wrong answer for the branch that actually consumes it**, which is why
this note is here rather than in a results file. -/
def TyshkevichDecomposable (d : V → ℕ) : Prop :=
  ∃ G : Realization d, ∃ A C : Finset V,
    C.Nonempty ∧ (Cᶜ).Nonempty ∧ A ⊆ Cᶜ ∧
    G.graph.IsClique (A : Set V) ∧
    (∀ u ∈ Cᶜ \ A, ∀ w ∈ Cᶜ \ A, ¬ G.graph.Adj u w) ∧
    (∀ a ∈ A, ∀ c ∈ C, G.graph.Adj a c) ∧
    (∀ b ∈ Cᶜ \ A, ∀ c ∈ C, ¬ G.graph.Adj b c)

/-- The invariant-position block has exactly the shape of a nontrivial Tyshkevich composition.
The witnesses are the prescribed ones: `A` is the left-side copy of `P`, while `C` is the union of
the right-side copy of `Q` and the left-side copy of `Pᶜ`. -/
theorem tyshkevichDecomposable_of_block {m n : ℕ} {d : V → ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ} (model : SplitIncidenceModel d r s)
    (M : MarginClass r s) (P : Finset (Fin m)) (Q : Finset (Fin n))
    (hnonempty : (P.Nonempty ∧ Q.Nonempty) ∨ (Pᶜ.Nonempty ∧ Qᶜ.Nonempty))
    (hforced : ∀ N : MarginClass r s,
      (∀ i ∈ P, ∀ j ∈ Q, N.val i j = true) ∧
      (∀ i ∉ P, ∀ j ∉ Q, N.val i j = false)) :
    TyshkevichDecomposable d := by
  classical
  let e : (Fin m ⊕ Fin n) ≃ V := model.vertexEquiv
  let row : Fin m → V := fun i => e (Sum.inl i)
  let col : Fin n → V := fun j => e (Sum.inr j)
  let A : Finset V := Finset.univ.filter fun v =>
    match e.symm v with
    | Sum.inl i => i ∈ P
    | Sum.inr _ => False
  let C : Finset V := Finset.univ.filter fun v =>
    match e.symm v with
    | Sum.inl i => i ∉ P
    | Sum.inr j => j ∈ Q
  have hside (v : V) : (∃ i, v = row i) ∨ (∃ j, v = col j) := by
    cases h : e.symm v with
    | inl i =>
        left
        refine ⟨i, ?_⟩
        change v = e (Sum.inl i)
        rw [← e.apply_symm_apply v, h]
    | inr j =>
        right
        refine ⟨j, ?_⟩
        change v = e (Sum.inr j)
        rw [← e.apply_symm_apply v, h]
  have hrowA (i : Fin m) : row i ∈ A ↔ i ∈ P := by simp [row, A, e]
  have hcolA (j : Fin n) : col j ∈ A ↔ False := by simp [col, A, e]
  have hrowC (i : Fin m) : row i ∈ C ↔ i ∉ P := by simp [row, C, e]
  have hcolC (j : Fin n) : col j ∈ C ↔ j ∈ Q := by simp [col, C, e]
  have hCnonempty : C.Nonempty := by
    rcases hnonempty with ⟨_, hQ⟩ | ⟨hPc, _⟩
    · obtain ⟨j, hj⟩ := hQ
      exact ⟨col j, (hcolC j).2 hj⟩
    · obtain ⟨i, hi⟩ := hPc
      exact ⟨row i, (hrowC i).2 (Finset.mem_compl.mp hi)⟩
  have hCcNonempty : (Cᶜ).Nonempty := by
    rcases hnonempty with ⟨hP, _⟩ | ⟨_, hQc⟩
    · obtain ⟨i, hi⟩ := hP
      exact ⟨row i, Finset.mem_compl.mpr (fun hiC => ((hrowC i).1 hiC) hi)⟩
    · obtain ⟨j, hj⟩ := hQc
      exact ⟨col j, Finset.mem_compl.mpr (fun hjC =>
        (Finset.mem_compl.mp hj) ((hcolC j).1 hjC))⟩
  have hACc : A ⊆ Cᶜ := by
    intro a ha
    rcases hside a with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact Finset.mem_compl.mpr (fun hiC => ((hrowC i).1 hiC) ((hrowA i).1 ha))
    · exact False.elim ((hcolA j).1 ha)
  have hAclique : (model.realizationIso M).graph.IsClique (A : Set V) := by
    intro a ha b hb hab
    rcases hside a with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rcases hside b with ⟨k, rfl⟩ | ⟨l, rfl⟩
      · apply model.left_clique M i k
        intro hik
        subst k
        exact hab rfl
      · exact False.elim ((hcolA l).1 hb)
    · exact False.elim ((hcolA j).1 ha)
  have hBindep : ∀ u ∈ Cᶜ \ A, ∀ w ∈ Cᶜ \ A,
      ¬ (model.realizationIso M).graph.Adj u w := by
    intro u hu w hw
    rcases hside u with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · have hiP : i ∈ P := by
        apply Classical.byContradiction
        intro hi
        exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp hu).1) ((hrowC i).2 hi)
      exact False.elim ((Finset.mem_sdiff.mp hu).2 ((hrowA i).2 hiP))
    · rcases hside w with ⟨k, rfl⟩ | ⟨l, rfl⟩
      · have hkP : k ∈ P := by
          apply Classical.byContradiction
          intro hk
          exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp hw).1) ((hrowC k).2 hk)
        exact False.elim ((Finset.mem_sdiff.mp hw).2 ((hrowA k).2 hkP))
      · exact model.right_independent M j l
  have hAcomplete : ∀ a ∈ A, ∀ c ∈ C,
      (model.realizationIso M).graph.Adj a c := by
    intro a ha c hc
    rcases hside a with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · have hiP : i ∈ P := (hrowA i).1 ha
      rcases hside c with ⟨k, rfl⟩ | ⟨l, rfl⟩
      · apply model.left_clique M i k
        intro hik
        subst k
        exact ((hrowC i).1 hc) hiP
      · exact (model.cross_adj_iff M i l).2
          ((hforced M).1 i hiP l ((hcolC l).1 hc))
    · exact False.elim ((hcolA j).1 ha)
  have hBanti : ∀ b ∈ Cᶜ \ A, ∀ c ∈ C,
      ¬ (model.realizationIso M).graph.Adj b c := by
    intro b hb c hc
    rcases hside b with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · have hiP : i ∈ P := by
        apply Classical.byContradiction
        intro hi
        exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp hb).1) ((hrowC i).2 hi)
      exact False.elim ((Finset.mem_sdiff.mp hb).2 ((hrowA i).2 hiP))
    · have hjQ : j ∉ Q := by
        intro hj
        exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp hb).1) ((hcolC j).2 hj)
      rcases hside c with ⟨k, rfl⟩ | ⟨l, rfl⟩
      · intro hjk
        have hone := (model.cross_adj_iff M k j).1 hjk.symm
        have hzero := (hforced M).2 k ((hrowC k).1 hc) j hjQ
        simp [hzero] at hone
      · exact model.right_independent M j l
  exact ⟨model.realizationIso M, A, C, hCnonempty, hCcNonempty, hACc,
    hAclique, hBindep, hAcomplete, hBanti⟩

/-- Tyshkevich indecomposability removes every invariant cross cell of a split-incidence model.
This is the contrapositive packaging of `invariantPosition_forces_block`. -/
theorem cellVaries_of_tyshkevichIndecomposable {m n : ℕ} {d : V → ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ} (model : SplitIncidenceModel d r s)
    (G : Realization d) (hindec : ¬ TyshkevichDecomposable d) :
    ∀ i j, CellVaries r s i j := by
  intro i j
  by_contra hinv
  have hne : Nonempty (MarginClass r s) := ⟨model.realizationIso.symm G⟩
  obtain ⟨P, Q, hnonempty, hforced⟩ :=
    invariantPosition_forces_block r s hne i j hinv
  exact hindec (tyshkevichDecomposable_of_block model
    (model.realizationIso.symm G) P Q hnonempty hforced)

/-- Transport non-2-colorability of one matrix-pattern fibre through a split-incidence model.
The resulting ground fibre is a realization fibre, so `hasNonBipartiteFibre_of_fibreNonbip`
extracts its triangle through pivot deletion and Barrus's equivalence. -/
theorem hasNonBipartiteFibre_of_patternFibreNonbip {m n : ℕ} {d : V → ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ} (model : SplitIncidenceModel d r s)
    {Q : Type*} [DecidableEq Q] (π : MarginClass r s → Q) (q : Q) (v : V)
    (hneighbor : ∀ M N : MarginClass r s, π M = π N ↔
      (model.realizationIso M).neighborFinset v =
        (model.realizationIso N).neighborFinset v)
    (hnb : ¬ ∃ col : {M : MarginClass r s // π M = q} → Bool,
      IsProper2Coloring (Brualdi.Ledger.fibreGraph (flipGraph r s) π q) col) :
    HasNonBipartiteFibre d v := by
  classical
  have hnonempty : Nonempty {M : MarginClass r s // π M = q} := by
    by_contra hempty
    apply hnb
    refine ⟨fun M => False.elim (hempty ⟨M⟩), ?_⟩
    intro A _B _hAB
    exact False.elim (hempty ⟨A⟩)
  let X : {M : MarginClass r s // π M = q} := Classical.choice hnonempty
  let S : Finset V := (model.realizationIso X.1).neighborFinset v
  let φ : {M : MarginClass r s // π M = q} ≃ interfaceFibre d v S :=
    { toFun := fun M => ⟨model.realizationIso M.1,
        (hneighbor M.1 X.1).1 (M.2.trans X.2.symm)⟩
      invFun := fun G => ⟨model.realizationIso.symm G.1, by
        exact ((hneighbor (model.realizationIso.symm G.1) X.1).2 (by
          simpa [S] using G.2)).trans X.2⟩
      left_inv := by
        intro M
        apply Subtype.ext
        exact model.realizationIso.symm_apply_apply M.1
      right_inv := by
        intro G
        apply Subtype.ext
        exact model.realizationIso.apply_symm_apply G.1 }
  let eFibre : Brualdi.Ledger.fibreGraph (flipGraph r s) π q ≃g
      interfaceFibreGraph d v S :=
    { toEquiv := φ
      map_rel_iff' := by
        intro A B
        exact model.realizationIso.map_rel_iff }
  have hnb' : ¬ ∃ col : interfaceFibre d v S → Bool,
      IsProper2Coloring (interfaceFibreGraph d v S) col := by
    rintro ⟨col, hcol⟩
    apply hnb
    refine ⟨fun M => col (eFibre M), ?_⟩
    intro A B hAB
    exact hcol (eFibre A) (eFibre B) (eFibre.map_rel_iff.mpr hAB)
  apply hasNonBipartiteFibre_of_fibreNonbip
  · exact ⟨model.realizationIso X.1, rfl⟩
  · exact hnb'

/-- A non-bipartite row or column fibre of the split incidence matrix is an explicit triangle in
the corresponding ground-vertex fibre. -/
theorem hasNonBipartiteFibre_of_lineFibreNonbip {m n : ℕ} {d : V → ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ} (model : SplitIncidenceModel d r s)
    (line : Fin m ⊕ Fin n) (hline : lineFibreNonbip (r := r) (s := s) line) :
    HasNonBipartiteFibre d (model.vertexEquiv line) := by
  cases line with
  | inl i =>
      rcases hline with ⟨γ, hγ⟩
      exact hasNonBipartiteFibre_of_patternFibreNonbip model (rowPat i) γ
        (model.vertexEquiv (Sum.inl i)) (fun M N =>
          model.rowPat_eq_iff_neighborFinset_eq M N i) hγ
  | inr j =>
      rcases hline with ⟨γ, hγ⟩
      exact hasNonBipartiteFibre_of_patternFibreNonbip model (colPat j) γ
        (model.vertexEquiv (Sum.inr j)) (fun M N =>
          model.colPat_eq_iff_neighborFinset_eq M N j) hγ

/-- The two bridges composed at the split-incidence boundary: indecomposability supplies the
cell-variation hypothesis of the companion paper's buffer-line theorem, and a non-bipartite matrix
line fibre becomes an explicit triangle in the corresponding ground fibre. The final assembly below
constructs the split-incidence model and identifies the prescribed ground pair with `a,b`. -/
theorem splitIncidence_buffer_of_tyshkevichIndecomposable {m n : ℕ} {d : V → ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ} (model : SplitIncidenceModel d r s)
    (G : Realization d) (hindec : ¬ TyshkevichDecomposable d)
    (hact : IsActive r s) (hm : 3 ≤ m) (hn : 3 ≤ n)
    (hnb : ¬ ∃ col : MarginClass r s → Bool, IsProper2Coloring (flipGraph r s) col)
    (a b : MarginClass r s) (hab : a ≠ b) :
    ∃ line : Fin m ⊕ Fin n,
      lineSeparates a b line ∧ HasNonBipartiteFibre d (model.vertexEquiv line) := by
  obtain ⟨line, hseparates, hline⟩ :=
    Brualdi.Ledger.buffer_line_exists_of_cellVaries r s hact hm hn
      (cellVaries_of_tyshkevichIndecomposable model G hindec) hnb a b hab
  exact ⟨line, hseparates, hasNonBipartiteFibre_of_lineFibreNonbip model line hline⟩

/-- **Anti-vacuity for `TyshkevichDecomposable`**, so that `MainLine`'s indecomposability hypothesis
is known to exclude something rather than being satisfied by everything.

A vertex of degree zero decomposes the sequence: put it alone in `B`, take `A` empty, and let `C` be
everything else. `A` is vacuously a clique and vacuously complete to `C`; `B` is a single vertex,
hence independent; and `B` is anticomplete to `C` because the vertex has no neighbours at all. This
is the shape that made `(1,1,1,1,0)` a counterexample to the old stand-in — it is decomposable while
Erdős–Gallai stays strict at every rank. -/
theorem tyshkevichDecomposable_of_degree_zero {d : V → ℕ} (G : Realization d) {v : V}
    (hv : d v = 0) (hcard : 1 < Fintype.card V) :
    TyshkevichDecomposable d := by
  classical
  -- `v` has no neighbours at all, which is what makes it anticomplete to everything.
  have hnadj : ∀ c : V, ¬ G.graph.Adj v c := by
    intro c hc
    have hmem : c ∈ G.graph.neighborFinset v := by
      simpa [SimpleGraph.mem_neighborFinset] using hc
    have hpos : 0 < (G.graph.neighborFinset v).card := Finset.card_pos.mpr ⟨c, hmem⟩
    rw [G.graph.card_neighborFinset_eq_degree, G.degree_eq v, hv] at hpos
    exact absurd hpos (lt_irrefl 0)
  refine ⟨G, ∅, ({v} : Finset V)ᶜ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `C` is everything but `v`, nonempty because there are at least two vertices
    rw [← Finset.card_pos, Finset.card_compl, Finset.card_singleton]
    omega
  · simpa using (Finset.singleton_nonempty v)
  · exact Finset.empty_subset _
  · simp
  · -- `B = {v}`, independent because `Adj` is irreflexive
    intro u hu w hw
    simp only [compl_compl, Finset.sdiff_empty, Finset.mem_singleton] at hu hw
    subst hu; subst hw
    exact G.graph.irrefl
  · simp
  · -- `B = {v}` is anticomplete to `C`, since `v` has no neighbours
    intro b hb c _
    simp only [compl_compl, Finset.sdiff_empty, Finset.mem_singleton] at hb
    subst hb
    exact hnadj c

/-- `G(d)` is not the `K₃` base graph. -/
def NotK3Base (d : V → ℕ) : Prop :=
  ¬ (∃ A B C : Realization d, A ≠ B ∧ B ≠ C ∧ A ≠ C ∧
      ∀ G : Realization d, G = A ∨ G = B ∨ G = C)

/-- The hypotheses under which the one-pass assembly runs.

**`indecomposable` changed meaning on 2026-08-18**, from the `NoErdosGallaiEquality` stand-in to the
real predicate. That makes this structure strictly HARDER to satisfy the theorems for — the class it
admits grew by 26 of 161 sequences through ground order 7 — and it makes every theorem carrying it
the theorem the manuscript states rather than a special case. The change was made while all four
consumers still carried `sorry`, which is the only time it is free. -/
structure MainLine (d : V → ℕ) : Prop where
  indecomposable : ¬ TyshkevichDecomposable d
  nonbipartite : ¬ (RealizationGraph d).Colorable 2
  notK3 : NotK3Base d
/-- **Relabelling invariance of realizable neighborhoods.** A permutation of the ground that
preserves the degree function and fixes the pivot carries realizable neighborhoods to realizable
neighborhoods.

This is the engine of the manuscript's transposition arguments, and in particular of Lemma 8.3a,
where it appears as *"graphicality depends only on the multiset of residual values"*. Stated on its
own because that phrase is used more than once in §8 and deserves one home rather than an inline
re-derivation each time. -/
theorem hasRealizationWithNeighborSet_image_of_perm {d : V → ℕ} {v : V} {S : Finset V}
    (τ : Equiv.Perm V) (hd : ∀ u, d (τ u) = d u) (hv : τ v = v)
    (h : HasRealizationWithNeighborSet d v S) :
    HasRealizationWithNeighborSet d v (S.image τ) := by
  classical
  obtain ⟨G, hG⟩ := h
  have hd_symm : ∀ u, d (τ.symm u) = d u := by
    intro u
    simpa using (hd (τ.symm u)).symm
  have hv_symm : τ.symm v = v := by
    apply τ.injective
    simpa using hv.symm
  refine ⟨relabelRealizationOfInvariant τ.symm hd_symm G, ?_⟩
  rw [relabelRealizationOfInvariant_neighborFinset, hv_symm, hG,
    Finset.map_eq_image]
  rfl

/-! ## 3b. The four-corner configuration (manuscript §8.2)

STATEMENTS FIRST. The manuscript is emphatic that Lemmas 8.3a–f are statements about **the
configuration itself and not about the pivot we started from**: Lemma 8.3f applies Lemma 8.3e to the
COMPLEMENTARY sequence, which need not be the quotient of a yFamily pivot of `d`. Reading them as
statements about `v` would be a quantifier slip of the kind that has broken an argument in this line
of work before, so they are stated here about the configuration, with `v` present only to name the
corners.

**ENCODING, and why this one.** In the manuscript `c, a, b, x` are `u_{k−1}, u_k, u_{k+1}, u_{k+2}`,
four consecutive RANKS in an order that breaks degree ties by label. Recording only their degrees
would be strictly weaker — Lemmas 8.3e and 8.3f tie a degree to `k = d v`, and it is the rank that
ties them. The ranks are therefore pinned SEMANTICALLY, by `card`, `top_block` and `tail`.

No `[LinearOrder V]` is assumed, and that is a decision rather than an omission. Lemma 8.3b's proof
settles it in one sentence — *"a tie at the boundary can exchange labels but not values, and only the
multiset of values is asserted"* — and the closed form for `F_P(k−1)` depends on `C₀` and the tail
only through the relabelling-invariant sums `L_0` and `T`. Requiring a linear order would have forced
a typeclass change through `MainLine`, which other statements consume. The full reading, including a
hand check that complementation carries all six corners correctly, is in
`topics/flipgraphs/realization/LEAN_SEC8_ENCODING_2026-08-17.md`.

The corners are stated with `HasRealizationWithNeighborSet` rather than as graphicality of six
residual degree functions. The manuscript uses the second form and notes the two are equivalent by
Lemma 5.2; the first needs no bridge, so nothing here waits on that equivalence. -/

/-- **The four-corner hypothesis**, manuscript §8.2. Of the six two-element extensions of `C₀`, the
`c,x` and `a,b` extensions are realizable neighborhoods of `v` and the `a,x` extension is not. The
ordered degree condition forces the `b,x` extension to be non-realizable too, as
`FourCorner.not_corner_bx`.

**Only these three corner conditions are assumed, and that is deliberate** (2026-08-24, finding F1 of
`results/2026-08-24_realization_simplification_study.md`). The structure carried `corner_ca` and
`corner_cb` as well, and neither was consumed by any proof in the 8.3 chain: `corner_cb` appeared
only at its own declaration, its construction and the complement map, where it existed to repopulate
itself, and `corner_ca`'s two uses extracted nothing but *some realization of `d` exists*, which
`corner_cx` supplies identically.

**They are not merely unused, they are derivable.** `quotientFamily_isShifted` makes the realizable
neighbourhoods a shifted family, and `corner_ab` puts `C₀ ∪ {a,b}` in it. **The strictness needed to
shift comes from Lemma 8.3a, not from `ordered`** — `ordered` is non-strict, this structure
deliberately assumes no `LinearOrder V` (see the note above), and the order supplied by
`exists_pivotMaximal_degreeAntitone_order` breaks degree ties arbitrarily, so `d a ≤ d c` alone does
not place `c` first. `lemma_8_3a_strict_outer_gaps` gives `d a < d c`, hence `d b ≤ d a < d c`, and
then shifting `b` or `a` to `c` delivers `C₀ ∪ {c,a}` and `C₀ ∪ {c,b}`. 8.3a consumes only the three
assumed conditions, so there is no circularity. An exhaustive sweep agrees: over ground orders 5
through 9 every configuration satisfying the three satisfies the other two, with no exceptions
-- 2,112 configurations, witness ledger in `compute/data/`
(`compute/f1_three_corner_seal_2026_08_24.py`). So dropping them is free rather than a weakening
that happens to be safe.

**The corner conditions were ALREADY complement-closed, and this did not change that.** The complement
sends a pair to its complement within `{c,a,b,x}` and renames by `(c,a,b,x) ↦ (x,b,a,c)`, so `{c,x}`
and `{a,b}` exchange while `{c,a}`, `{c,b}` and `{a,x}` are each **fixed** — which is exactly why the
deleted lines read `corner_ca := … hfc.corner_ca`, each field repopulated from itself. What the
change buys is that the assumed set is now **minimally** closed: nothing is carried through
`fourCorner_complement` except what a later lemma actually reads. -/
structure FourCorner (d : V → ℕ) (v : V) (C₀ : Finset V) (c a b x : V) : Prop where
  pivot_not_mem : v ∉ C₀
  ne_pivot : c ≠ v ∧ a ≠ v ∧ b ≠ v ∧ x ≠ v
  not_mem : c ∉ C₀ ∧ a ∉ C₀ ∧ b ∉ C₀ ∧ x ∉ C₀
  distinct : c ≠ a ∧ c ≠ b ∧ c ≠ x ∧ a ≠ b ∧ a ≠ x ∧ b ≠ x
  /-- `|C₀| = k − 2`, written without truncated subtraction -/
  card : C₀.card + 2 = d v
  /-- `C₀ ∪ {c}` is a top block by degree -/
  top_block : ∀ u ∈ C₀, d c ≤ d u
  /-- `r ≥ p ≥ q ≥ s` -/
  ordered : d x ≤ d b ∧ d b ≤ d a ∧ d a ≤ d c
  /-- and everything outside the block and the four is at most `s` -/
  tail : ∀ u : V, u ≠ v → u ∉ C₀ → u ≠ c → u ≠ a → u ≠ b → u ≠ x → d u ≤ d x
  corner_cx : HasRealizationWithNeighborSet d v (insert c (insert x C₀))
  corner_ab : HasRealizationWithNeighborSet d v (insert a (insert b C₀))
  not_corner_ax : ¬ HasRealizationWithNeighborSet d v (insert a (insert x C₀))

/-- The second non-corner follows from the first: if `d b < d a`, shiftedness exchanges `b` for
`a`; if `d b = d a`, swapping the two labels preserves the degree function. -/
theorem FourCorner.not_corner_bx {d : V → ℕ} {v : V} {C₀ : Finset V} {c a b x : V}
    (hfc : FourCorner d v C₀ c a b x) :
    ¬ HasRealizationWithNeighborSet d v (insert b (insert x C₀)) := by
  classical
  intro hbx
  apply hfc.not_corner_ax
  rcases lt_or_eq_of_le hfc.ordered.2.1 with hba | hba
  · let X : Finset V := insert b (insert x C₀)
    have hXF : X ∈ realizableNeighborhoods d v :=
      mem_realizableNeighborhoods.mpr hbx
    obtain ⟨inst, hvmax, hmono⟩ := exists_pivotMaximal_degreeAntitone_order d v
    letI : LinearOrder V := inst
    have hab : a < b := by
      rcases lt_trichotomy a b with hab | hab | hba'
      · exact hab
      · exact (hfc.distinct.2.2.2.1 hab).elim
      · have hab_degree : d a ≤ d b :=
          hmono b a hfc.ne_pivot.2.2.1 hfc.ne_pivot.2.1 hba'
        omega
    have htarget := (quotientFamily_isShifted d v hvmax hmono ⟨X, hXF⟩).2.2
      X hXF a b (by simp [X]) hab (by
        simp [X, hfc.distinct.2.2.2.1, hfc.distinct.2.2.2.2.1,
          hfc.not_mem.2.1])
    have hreal := mem_realizableNeighborhoods.mp htarget
    simpa [X, hfc.distinct.2.2.2.2.2, hfc.not_mem.2.2.1] using hreal
  · let τ : Equiv.Perm V := Equiv.swap a b
    have hd : ∀ u, d (τ u) = d u := by
      intro u
      by_cases hua : u = a
      · subst u
        simpa [τ] using hba
      · by_cases hub : u = b
        · subst u
          simpa [τ] using hba.symm
        · rw [Equiv.swap_apply_of_ne_of_ne hua hub]
    have hv : τ v = v := by
      exact Equiv.swap_apply_of_ne_of_ne hfc.ne_pivot.2.1.symm
        hfc.ne_pivot.2.2.1.symm
    have hτb : τ b = a := by simp [τ]
    have hτx : τ x = x := by
      exact Equiv.swap_apply_of_ne_of_ne hfc.distinct.2.2.2.2.1.symm
        hfc.distinct.2.2.2.2.2.symm
    have hτC₀ : C₀.image τ = C₀ := by
      calc
        C₀.image τ = C₀.image id := Finset.image_congr (by
          intro u hu
          exact Equiv.swap_apply_of_ne_of_ne
            (ne_of_mem_of_not_mem hu hfc.not_mem.2.1)
            (ne_of_mem_of_not_mem hu hfc.not_mem.2.2.1))
        _ = C₀ := Finset.image_id
    have himage : (insert b (insert x C₀)).image τ = insert a (insert x C₀) := by
      rw [Finset.image_insert, Finset.image_insert, hτb, hτx, hτC₀]
    rw [← himage]
    exact hasRealizationWithNeighborSet_image_of_perm τ hd hv hbx

/-- **Lemma 8.3a (strict outer gaps).** Manuscript §8.2: `r > p` and `q > s`. Proved there by
transposing `c` with `a` and `b` with `x` — graphicality depends only on the multiset of residual
values, so an equality would carry a graphical corner onto a non-graphical one. -/
theorem lemma_8_3a_strict_outer_gaps {d : V → ℕ} {v : V} {C₀ : Finset V} {c a b x : V}
    (hfc : FourCorner d v C₀ c a b x) :
    d a < d c ∧ d x < d b := by
  classical
  constructor
  · have hne : d a ≠ d c := by
      intro heq
      let τ : Equiv.Perm V := Equiv.swap c a
      have hd : ∀ u, d (τ u) = d u := by
        intro u
        by_cases huc : u = c
        · subst u
          simpa [τ] using heq
        · by_cases hua : u = a
          · subst u
            simpa [τ] using heq.symm
          · rw [Equiv.swap_apply_of_ne_of_ne huc hua]
      have hv : τ v = v := by
        exact Equiv.swap_apply_of_ne_of_ne hfc.ne_pivot.1.symm hfc.ne_pivot.2.1.symm
      have hτc : τ c = a := by
        simp [τ]
      have hτx : τ x = x := by
        exact Equiv.swap_apply_of_ne_of_ne hfc.distinct.2.2.1.symm
          hfc.distinct.2.2.2.2.1.symm
      have hτC₀ : C₀.image τ = C₀ := by
        calc
          C₀.image τ = C₀.image id := Finset.image_congr (by
            intro u hu
            exact Equiv.swap_apply_of_ne_of_ne
              (ne_of_mem_of_not_mem hu hfc.not_mem.1)
              (ne_of_mem_of_not_mem hu hfc.not_mem.2.1))
          _ = C₀ := Finset.image_id
      have himage : (insert c (insert x C₀)).image τ = insert a (insert x C₀) := by
        rw [Finset.image_insert, Finset.image_insert, hτc, hτx, hτC₀]
      apply hfc.not_corner_ax
      rw [← himage]
      exact hasRealizationWithNeighborSet_image_of_perm τ hd hv hfc.corner_cx
    exact lt_of_le_of_ne hfc.ordered.2.2 hne
  · have hne : d x ≠ d b := by
      intro heq
      let τ : Equiv.Perm V := Equiv.swap b x
      have hd : ∀ u, d (τ u) = d u := by
        intro u
        by_cases hub : u = b
        · subst u
          simpa [τ] using heq
        · by_cases hux : u = x
          · subst u
            simpa [τ] using heq.symm
          · rw [Equiv.swap_apply_of_ne_of_ne hub hux]
      have hv : τ v = v := by
        exact Equiv.swap_apply_of_ne_of_ne hfc.ne_pivot.2.2.1.symm
          hfc.ne_pivot.2.2.2.symm
      have hτa : τ a = a := by
        exact Equiv.swap_apply_of_ne_of_ne hfc.distinct.2.2.2.1
          hfc.distinct.2.2.2.2.1
      have hτb : τ b = x := by
        simp [τ]
      have hτC₀ : C₀.image τ = C₀ := by
        calc
          C₀.image τ = C₀.image id := Finset.image_congr (by
            intro u hu
            exact Equiv.swap_apply_of_ne_of_ne
              (ne_of_mem_of_not_mem hu hfc.not_mem.2.2.1)
              (ne_of_mem_of_not_mem hu hfc.not_mem.2.2.2))
          _ = C₀ := Finset.image_id
      have himage : (insert a (insert b C₀)).image τ = insert a (insert x C₀) := by
        rw [Finset.image_insert, Finset.image_insert, hτa, hτb, hτC₀]
      apply hfc.not_corner_ax
      rw [← himage]
      exact hasRealizationWithNeighborSet_image_of_perm τ hd hv hfc.corner_ab
    exact lt_of_le_of_ne hfc.ordered.1 hne

/-- The Erdős–Gallai slack of a degree function at rank `t`: right side minus left side. A function
with even sum and no negative entry is graphical exactly when this is non-negative at every `t`.
Manuscript §8.2. Stated over an arbitrary finite type so it applies both to the residuals on
`{u // u ≠ v}` and to the complement used in Lemma 8.3f. -/
noncomputable def erdosGallaiSlack {W : Type*} [Fintype W] [DecidableEq W]
    (w : W → ℕ) (t : ℕ) : ℤ :=
  ((t : ℤ) * ((t : ℤ) - 1))
    + ((((Finset.univ.val.map w).sort (· ≥ ·)).drop t).map (fun z => (min z t : ℤ))).sum
    - ((((Finset.univ.val.map w).sort (· ≥ ·)).take t).map (fun z => (z : ℤ))).sum

/-- **Erdős–Gallai, the sufficiency direction.** A non-negative sequence of even sum whose
Erdős–Gallai slack is non-negative at every rank is graphical.

**Source.** P. Erdős and T. Gallai, *Gráfok előírt fokú pontokkal*, Matematikai Lapok **11** (1960)
264–274. The page range is settled from the article's own scan — eleven pages, the last printing 274
— which refutes the widespread 264–272; recorded in `REFERENCES_VERIFIED_2026-08-16.md`. Pinned as
`EG1960`.

**Formal scope.** Only the `⟸` half of the characterization: from the numerical conditions to the
existence of a realization. Nothing about which realization, and nothing about the converse.

**THIS IS A TRUST-SURFACE DECISION AND IT WAS JEFF'S**, taken 2026-08-18 after the wave at Lemma
8.3e isolated the missing step into a single named `have` and stopped rather than conceal it. It is
the **seventh** cited axiom on this target.

**Why citing is faithful rather than convenient.** §8.2 of the manuscript already states the full
characterization as a known theorem, in a displayed sentence with this citation attached: *"Thus `W`
is graphical if and only if it is non-negative, has even sum, and `F_W(t) ≥ 0` for every `t`."* The
paper has always used this direction — 8.3e's proof says outright that non-graphicality *"supplies an
Erdős–Gallai violating rank"*. So the axiom records a dependency the paper declares, rather than
introducing one. What the Lean adds is that it cannot cite; it can only prove or axiomatize.

**⚠ Do not confuse this with what the manuscript's §8.2 proves.** Three different things carry the Erdős–Gallai name
here. The *slack* is a definition. *Necessity*, together with its equality case — the clique and the
saturation that Lemma 8.3d Step 3 consumes — is one double count and is **proved** in §8.2.1, with no
citation. Only *sufficiency*, the hard half, is taken on trust, and only here.

**It is the one cited axiom on this surface that is squarely a Mathlib gap**, and discharging it
would retire it: the development already carries necessity in set form, which is the natural first
half of a full treatment. Recorded as a direction in `topics/PROBLEM_BENCH.md`. -/
axiom erdos_gallai_sufficiency {W : Type u} [Fintype W] [DecidableEq W] (w : W → ℕ)
    (heven : Even (∑ u : W, w u))
    (hslack : ∀ t : ℕ, t ≤ Fintype.card W → 0 ≤ erdosGallaiSlack w t) :
    Graphical w

/-- The contrapositive, in the form Lemma 8.3e consumes: a non-graphical sequence of even sum has a
negative slack at some rank. Stated separately so the axiom is invoked at exactly one place and the
dependency stays legible at the call site, as `realizationGraph_preconnected`'s is. -/
theorem exists_neg_slack_of_not_graphical {W : Type u} [Fintype W] [DecidableEq W] (w : W → ℕ)
    (heven : Even (∑ u : W, w u)) (hng : ¬ Graphical w) :
    ∃ t : ℕ, t ≤ Fintype.card W ∧ erdosGallaiSlack w t < 0 := by
  by_contra hcon
  push_neg at hcon
  exact hng (erdos_gallai_sufficiency w heven (fun t ht => by
    have := hcon t ht
    omega))

omit [DecidableEq V] in
/-- Every member of a realizable neighborhood has positive degree. -/
theorem pos_degree_of_mem_realizable {d : V → ℕ} {v : V} {S : Finset V}
    (h : HasRealizationWithNeighborSet d v S) {u : V} (hu : u ∈ S) : 0 < d u := by
  obtain ⟨G, hG⟩ := h
  have huN : u ∈ G.neighborFinset v := by simpa [hG] using hu
  have hvN : v ∈ G.graph.neighborFinset u := by
    simpa [SimpleGraph.mem_neighborFinset] using (G.mem_neighborFinset v u).mp huN |>.symm
  rw [← G.degree_eq_apply u]
  change 0 < G.graph.degree u
  rw [← G.graph.card_neighborFinset_eq_degree]
  exact Finset.card_pos.mpr ⟨v, hvN⟩

/-- The forbidden residual `D`, of the corner `{a, x}`. Manuscript §8.2. -/
noncomputable def fourCornerD (d : V → ℕ) (v : V) (C₀ : Finset V) (a x : V) :
    {u : V // u ≠ v} → ℕ :=
  residualDegree d v (insert a (insert x C₀))

/-- The graphical residual `U`, of the corner `{c, x}`. Manuscript §8.2. -/
noncomputable def fourCornerU (d : V → ℕ) (v : V) (C₀ : Finset V) (c x : V) :
    {u : V // u ≠ v} → ℕ :=
  residualDegree d v (insert c (insert x C₀))

/-- The graphical residual `V`, of the corner `{a, b}`. Manuscript §8.2. -/
noncomputable def fourCornerV (d : V → ℕ) (v : V) (C₀ : Finset V) (a b : V) :
    {u : V // u ≠ v} → ℕ :=
  residualDegree d v (insert a (insert b C₀))

/-- **The sorting kernel of §8.2, in one place.** If every value of `A` dominates every value of
`B`, sorting the sum concatenates the sorted blocks.

Three proofs need it — Lemmas 8.3b and 8.3c, which compare slacks by isolating a common top block,
and `exists_topBlock` in the block below, which is where the vertex order enters the development at all. It
was written out three times before it was written down once: 8.3b and 8.3c each carried a local
`have`, and the copies had drifted only in a binder name. Placed above the first consumer, since Lean
needs it declared before use and 8.3b is the earliest. -/
private lemma sort_add_of_high (A B : Multiset ℕ)
    (hhigh : ∀ z ∈ A, ∀ y ∈ B, z ≥ y) :
    (A + B).sort (· ≥ ·) = A.sort (· ≥ ·) ++ B.sort (· ≥ ·) := by
  apply List.Perm.eq_of_pairwise' (r := (· ≥ ·))
  · exact Multiset.pairwise_sort _ _
  · rw [List.pairwise_append]
    refine ⟨Multiset.pairwise_sort _ _, Multiset.pairwise_sort _ _, ?_⟩
    intro z hz y hy
    exact hhigh z (by simpa using hz) y (by simpa using hy)
  · apply Multiset.coe_eq_coe.mp
    simpa only [Multiset.sort_eq] using
      (Multiset.coe_add (A.sort (· ≥ ·)) (B.sort (· ≥ ·)))

/-- **Lemma 8.3b, in the form its consumers use.** Manuscript §8.2 proves stability of the top `k−1`
sorted entries and then derives, in closed form, the two slack identities at rank `k−1` that the rest
of the section actually consumes. Those identities are stated here directly.

Writing `σ = F_D(k−1)`, `p = d a`, `q = d b`, `s = d x` and `k = d v`:

    F_{c,x}(k−1) = σ + 1 + [p ≤ k−1],      F_{a,b}(k−1) = σ − [q ≤ k−1] + [s ≤ k−1].

**Why this form and not the sorted-entry statement.** The manuscript's Lemma 8.3b says the top `k−1`
entries of all six residuals are the `C₀` values together with `c`'s. That is a statement about sorted
lists, and stating it would drag list-sorting reasoning into the interface for no gain: every later
use is through these two identities. Recording the consumed form keeps the obligation honest and the
statement checkable. The derivation itself — subtract the closed form for the `{a,x}` corner from
those for `{c,x}` and `{a,b}`, then use `m(y) − m(y−1) = [y ≤ k−1]` — is part of this proof. -/
theorem lemma_8_3b_slack_identities {d : V → ℕ} {v : V} {C₀ : Finset V} {c a b x : V}
    (hfc : FourCorner d v C₀ c a b x) :
    erdosGallaiSlack (fourCornerU d v C₀ c x) (d v - 1)
        = erdosGallaiSlack (fourCornerD d v C₀ a x) (d v - 1)
          + 1 + (if d a ≤ d v - 1 then 1 else 0) ∧
      erdosGallaiSlack (fourCornerV d v C₀ a b) (d v - 1)
        = erdosGallaiSlack (fourCornerD d v C₀ a x) (d v - 1)
          - (if d b ≤ d v - 1 then 1 else 0) + (if d x ≤ d v - 1 then 1 else 0) := by
  classical
  let W := {u : V // u ≠ v}
  let t := d v - 1
  have slack_eq_of_top_block (f : W → ℕ) (P : W → Prop) [DecidablePred P]
      (hcard : (Finset.univ.filter P).card = t)
      (hhigh : ∀ z, P z → ∀ y, ¬ P y → f z ≥ f y) :
      erdosGallaiSlack f t =
        ((t : ℤ) * ((t : ℤ) - 1))
          + ∑ z ∈ Finset.univ.filter (fun z ↦ ¬ P z), (min (f z) t : ℤ)
          - ∑ z ∈ Finset.univ.filter P, (f z : ℤ) := by
    let I : Multiset W := Finset.univ.val
    let If : Multiset W := I.filter P
    let Io : Multiset W := I.filter (fun z ↦ ¬ P z)
    let A : Multiset ℕ := If.map f
    let B : Multiset ℕ := Io.map f
    have hI : If + Io = I := Multiset.filter_add_not P I
    have hAcard : A.card = t := by
      simp only [A, Multiset.card_map]
      change (Finset.univ.filter P).card = t
      exact hcard
    have hsort : (Finset.univ.val.map f).sort (· ≥ ·) =
        A.sort (· ≥ ·) ++ B.sort (· ≥ ·) := by
      change (I.map f).sort (· ≥ ·) = _
      rw [← hI, Multiset.map_add]
      apply sort_add_of_high A B
      intro z hz y hy
      obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hz
      obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hy
      exact hhigh u (Multiset.mem_filter.mp hu).2 w (Multiset.mem_filter.mp hw).2
    have hlen : (A.sort (· ≥ ·)).length = t := by simp [hAcard]
    have hdropA : (A.sort (· ≥ ·)).drop t = [] :=
      List.drop_eq_nil_of_le (le_of_eq hlen)
    have htakeA : (A.sort (· ≥ ·)).take t = A.sort (· ≥ ·) :=
      List.take_of_length_le (le_of_eq hlen)
    have hdrop : ((Finset.univ.val.map f).sort (· ≥ ·)).drop t =
        B.sort (· ≥ ·) := by
      rw [hsort, List.drop_append, hlen, hdropA]
      simp
    have htake : ((Finset.univ.val.map f).sort (· ≥ ·)).take t =
        A.sort (· ≥ ·) := by
      rw [hsort, List.take_append, hlen, htakeA]
      simp
    have coe_sum (l : List ℕ) : (show List ℤ from l).sum = (l.sum : ℤ) := by
      induction l with
      | nil => rfl
      | cons z l ih =>
          change (z : ℤ) + (show List ℤ from l).sum = ((z + l.sum : ℕ) : ℤ)
          rw [ih, Nat.cast_add]
    have min_sum (l : List ℕ) :
        (l.map (fun z ↦ (min z t : ℤ))).sum = ((l.map (fun z ↦ min z t)).sum : ℤ) := by
      induction l with
      | nil => rfl
      | cons z l ih =>
          change (min z t : ℤ) + (l.map (fun z ↦ (min z t : ℤ))).sum =
            (((min z t) + (l.map (fun z ↦ min z t)).sum : ℕ) : ℤ)
          rw [ih, Nat.cast_add]
          norm_cast
    have htail :
        ((B.sort (· ≥ ·)).map (fun z ↦ (min z t : ℤ))).sum =
          ∑ z ∈ Finset.univ.filter (fun z : W ↦ ¬ P z), (min (f z) t : ℤ) := by
      rw [min_sum]
      norm_cast
      change ((B.sort (· ≥ ·)).map (fun z ↦ min z t)).sum =
        ((Io.map (fun z ↦ min (f z) t)).sum)
      rw [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.sort_eq]
      simp [B, Multiset.map_map, Function.comp_def]
    have htop :
        ((A.sort (· ≥ ·)).map (fun z ↦ (z : ℤ))).sum =
          ∑ z ∈ Finset.univ.filter P, (f z : ℤ) := by
      simp only [List.map_id_fun', id_eq]
      rw [coe_sum]
      norm_cast
      change (A.sort (· ≥ ·)).sum = (If.map f).sum
      rw [← Multiset.sum_coe, Multiset.sort_eq]
    unfold erdosGallaiSlack
    rw [hdrop, htake, htail, htop]
  let D : W → ℕ := fourCornerD d v C₀ a x
  let U : W → ℕ := fourCornerU d v C₀ c x
  let R : W → ℕ := fourCornerV d v C₀ a b
  let H : Finset V := insert c C₀
  let P : W → Prop := fun z ↦ z.val ∈ H
  let cv : W := ⟨c, hfc.ne_pivot.1⟩
  let av : W := ⟨a, hfc.ne_pivot.2.1⟩
  let bv : W := ⟨b, hfc.ne_pivot.2.2.1⟩
  let xv : W := ⟨x, hfc.ne_pivot.2.2.2⟩
  have hgaps := lemma_8_3a_strict_outer_gaps hfc
  have hp_lt_r : d a < d c := hgaps.1
  have hs_lt_q : d x < d b := hgaps.2
  have hq_le_p : d b ≤ d a := hfc.ordered.2.1
  have hk : C₀.card + 2 = d v := hfc.card
  have hbpos : 0 < d b := by omega
  have hapos : 0 < d a := by omega
  have hcpos : 0 < d c := by omega
  have degree_pos_of_mem_corner (S : Finset V)
      (hS : HasRealizationWithNeighborSet d v S) (z : V) (hzS : z ∈ S) : 0 < d z := by
    obtain ⟨G, hG⟩ := hS
    have hzN : z ∈ G.neighborFinset v := by simpa [hG] using hzS
    have hvN : v ∈ G.graph.neighborFinset z := by
      simpa [SimpleGraph.mem_neighborFinset] using (G.mem_neighborFinset v z).mp hzN |>.symm
    rw [← G.degree_eq_apply z]
    change 0 < G.graph.degree z
    rw [← G.graph.card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨v, hvN⟩
  have hxpos : 0 < d x :=
    degree_pos_of_mem_corner _ hfc.corner_cx x (by simp)
  have block_card (K : Finset V) (hvK : v ∉ K) :
      (Finset.univ.filter (fun z : W ↦ z.val ∈ K)).card = K.card := by
    apply Finset.card_bij (fun z _ ↦ z.val)
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
    · intro z₁ _ z₂ _ heq
      exact Subtype.ext heq
    · intro z hz
      have hzv : z ≠ v := by
        intro heq
        subst z
        exact hvK hz
      refine ⟨⟨z, hzv⟩, ?_, rfl⟩
      simp [hz]
  have hvH : v ∉ H := by
    simp [H, hfc.ne_pivot.1.symm, hfc.pivot_not_mem]
  have hHcard : H.card = t := by
    have hcC : c ∉ C₀ := hfc.not_mem.1
    simp [H, t, hcC]
    omega
  have hPcard : (Finset.univ.filter P).card = t := by
    rw [block_card H hvH, hHcard]
  have hdegree_out (y : W) (hy : ¬ P y) : d y.val ≤ d a := by
    have hyC : y.val ∉ C₀ := by
      intro h
      apply hy
      simp [P, H, h]
    have hyc : y.val ≠ c := by
      intro h
      apply hy
      simp [P, H, h]
    by_cases hya : y.val = a
    · simpa [hya]
    by_cases hyb : y.val = b
    · simpa [hyb] using hfc.ordered.2.1
    by_cases hyx : y.val = x
    · simpa [hyx] using hfc.ordered.1.trans hfc.ordered.2.1
    exact (hfc.tail y.val y.property hyC hyc hya hyb hyx).trans
      (hfc.ordered.1.trans hfc.ordered.2.1)
  have high_of (f : W → ℕ)
      (hc : d a ≤ f cv)
      (hC : ∀ (z : V) (hzv : z ≠ v), z ∈ C₀ → d a ≤ f ⟨z, hzv⟩)
      (hbelow : ∀ y, f y ≤ d y.val) :
      ∀ z, P z → ∀ y, ¬ P y → f z ≥ f y := by
    rintro ⟨z, hzv⟩ hz y hy
    have hfy : f y ≤ d a := (hbelow y).trans (hdegree_out y hy)
    have hfz : d a ≤ f ⟨z, hzv⟩ := by
      simp only [P, H, Finset.mem_insert] at hz
      rcases hz with hzc | hzC
      · subst z
        simpa [cv] using hc
      · exact hC z hzv hzC
    omega
  have hDc : D cv = d c := by
    simp [D, cv, fourCornerD, residualDegree, hfc.distinct.1,
      hfc.distinct.2.2.1, hfc.not_mem.1]
  have hUc : U cv = d c - 1 := by
    simp [U, cv, fourCornerU, residualDegree]
  have hRc : R cv = d c := by
    simp [R, cv, fourCornerV, residualDegree, hfc.distinct.1,
      hfc.distinct.2.1, hfc.not_mem.1]
  have hDC (z : V) (hzv : z ≠ v) (hzC : z ∈ C₀) :
      D ⟨z, hzv⟩ = d z - 1 := by
    simp [D, fourCornerD, residualDegree, hzC]
  have hUC (z : V) (hzv : z ≠ v) (hzC : z ∈ C₀) :
      U ⟨z, hzv⟩ = d z - 1 := by
    simp [U, fourCornerU, residualDegree, hzC]
  have hRC (z : V) (hzv : z ≠ v) (hzC : z ∈ C₀) :
      R ⟨z, hzv⟩ = d z - 1 := by
    simp [R, fourCornerV, residualDegree, hzC]
  have hDhigh : ∀ z, P z → ∀ y, ¬ P y → D z ≥ D y := by
    apply high_of D
    · rw [hDc]
      omega
    · intro z hzv hzC
      rw [hDC z hzv hzC]
      have := hfc.top_block z hzC
      omega
    · intro y
      simp [D, fourCornerD, residualDegree]
  have hUhigh : ∀ z, P z → ∀ y, ¬ P y → U z ≥ U y := by
    apply high_of U
    · rw [hUc]
      omega
    · intro z hzv hzC
      rw [hUC z hzv hzC]
      have := hfc.top_block z hzC
      omega
    · intro y
      simp [U, fourCornerU, residualDegree]
  have hRhigh : ∀ z, P z → ∀ y, ¬ P y → R z ≥ R y := by
    apply high_of R
    · rw [hRc]
      omega
    · intro z hzv hzC
      rw [hRC z hzv hzC]
      have := hfc.top_block z hzC
      omega
    · intro y
      simp [R, fourCornerV, residualDegree]
  have hslackD := slack_eq_of_top_block D P hPcard hDhigh
  have hslackU := slack_eq_of_top_block U P hPcard hUhigh
  have hslackR := slack_eq_of_top_block R P hPcard hRhigh
  have hDa : D av = d a - 1 := by
    simp [D, av, fourCornerD, residualDegree]
  have hUa : U av = d a := by
    simp [U, av, fourCornerU, residualDegree, hfc.distinct.1.symm,
      hfc.distinct.2.2.2.2.1, hfc.not_mem.2.1]
  have hDb : D bv = d b := by
    simp [D, bv, fourCornerD, residualDegree, hfc.distinct.2.2.2.1.symm,
      hfc.distinct.2.2.2.2.2, hfc.not_mem.2.2.1]
  have hRb : R bv = d b - 1 := by
    simp [R, bv, fourCornerV, residualDegree]
  have hDx : D xv = d x - 1 := by
    simp [D, xv, fourCornerD, residualDegree]
  have hRx : R xv = d x := by
    simp [R, xv, fourCornerV, residualDegree, hfc.distinct.2.2.2.2.1.symm,
      hfc.distinct.2.2.2.2.2.symm, hfc.not_mem.2.2.2]
  have htopDU :
      (∑ z ∈ Finset.univ.filter P, (D z : ℤ)) =
        (∑ z ∈ Finset.univ.filter P, (U z : ℤ)) + 1 := by
    let F : Finset W := Finset.univ.filter P
    have hcvF : cv ∈ F := by simp [F, P, H, cv]
    change (∑ z ∈ F, (D z : ℤ)) = (∑ z ∈ F, (U z : ℤ)) + 1
    rw [← Finset.sum_erase_add F (fun z ↦ (D z : ℤ)) hcvF,
      ← Finset.sum_erase_add F (fun z ↦ (U z : ℤ)) hcvF]
    have hrest :
        (∑ z ∈ F.erase cv, (D z : ℤ)) = ∑ z ∈ F.erase cv, (U z : ℤ) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hznec : z.val ≠ c := by
        intro heq
        have : z = cv := Subtype.ext heq
        subst z
        exact (Finset.mem_erase.mp hz).1 rfl
      have hzP : P z := (Finset.mem_filter.mp (Finset.mem_erase.mp hz).2).2
      have hzC : z.val ∈ C₀ := by
        simp only [P, H, Finset.mem_insert] at hzP
        exact hzP.resolve_left hznec
      rw [hDC z.val z.property hzC, hUC z.val z.property hzC]
    rw [hrest, hDc, hUc]
    norm_cast
    omega
  have htopDR :
      (∑ z ∈ Finset.univ.filter P, (D z : ℤ)) =
        ∑ z ∈ Finset.univ.filter P, (R z : ℤ) := by
    apply Finset.sum_congr rfl
    intro z hz
    have hzP : P z := (Finset.mem_filter.mp hz).2
    simp only [P, H, Finset.mem_insert] at hzP
    rcases hzP with hzc | hzC
    · have : z = cv := Subtype.ext hzc
      subst z
      rw [hDc, hRc]
    · rw [hDC z.val z.property hzC, hRC z.val z.property hzC]
  have hminA :
      min (U av : ℤ) (t : ℤ) = min (D av : ℤ) (t : ℤ)
        + (if d a ≤ t then 1 else 0) := by
    rw [hUa, hDa]
    norm_cast
    by_cases ha : d a ≤ t
    · have ha' : d a - 1 ≤ t := by omega
      simp [ha, ha', min_eq_left]
      omega
    · have ht : t ≤ d a := by omega
      have ht' : t ≤ d a - 1 := by omega
      simp [ha, ht, ht', min_eq_right]
  have htailDU :
      (∑ z ∈ Finset.univ.filter (fun z : W ↦ ¬ P z), min (U z : ℤ) (t : ℤ)) =
        (∑ z ∈ Finset.univ.filter (fun z : W ↦ ¬ P z), min (D z : ℤ) (t : ℤ))
          + (if d a ≤ t then 1 else 0) := by
    let F : Finset W := Finset.univ.filter (fun z ↦ ¬ P z)
    have havF : av ∈ F := by
      simp [F, P, H, av, hfc.distinct.1.symm, hfc.not_mem.2.1]
    change (∑ z ∈ F, min (U z : ℤ) (t : ℤ)) =
      (∑ z ∈ F, min (D z : ℤ) (t : ℤ)) + (if d a ≤ t then 1 else 0)
    rw [← Finset.sum_erase_add F (fun z ↦ min (U z : ℤ) (t : ℤ)) havF,
      ← Finset.sum_erase_add F (fun z ↦ min (D z : ℤ) (t : ℤ)) havF]
    have hrest :
        (∑ z ∈ F.erase av, min (U z : ℤ) (t : ℤ)) =
          ∑ z ∈ F.erase av, min (D z : ℤ) (t : ℤ) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hznotP : ¬ P z := (Finset.mem_filter.mp (Finset.mem_erase.mp hz).2).2
      have hznec : z.val ≠ c := by
        intro heq
        apply hznotP
        simp [P, H, heq]
      have hznea : z.val ≠ a := by
        intro heq
        have : z = av := Subtype.ext heq
        subst z
        exact (Finset.mem_erase.mp hz).1 rfl
      congr 1
      simp [D, U, fourCornerD, fourCornerU, residualDegree, hznec, hznea]
    rw [hrest, hminA]
    omega
  have hminB :
      min (D bv : ℤ) (t : ℤ) = min (R bv : ℤ) (t : ℤ)
        + (if d b ≤ t then 1 else 0) := by
    rw [hDb, hRb]
    norm_cast
    by_cases hb : d b ≤ t
    · have hb' : d b - 1 ≤ t := by omega
      simp [hb, hb', min_eq_left]
      omega
    · have ht : t ≤ d b := by omega
      have ht' : t ≤ d b - 1 := by omega
      simp [hb, ht, ht', min_eq_right]
  have hminX :
      min (R xv : ℤ) (t : ℤ) = min (D xv : ℤ) (t : ℤ)
        + (if d x ≤ t then 1 else 0) := by
    rw [hRx, hDx]
    norm_cast
    by_cases hx : d x ≤ t
    · have hx' : d x - 1 ≤ t := by omega
      simp [hx, hx', min_eq_left]
      omega
    · have ht : t ≤ d x := by omega
      have ht' : t ≤ d x - 1 := by omega
      simp [hx, ht, ht', min_eq_right]
  have htailDR :
      (∑ z ∈ Finset.univ.filter (fun z : W ↦ ¬ P z), min (R z : ℤ) (t : ℤ)) =
        (∑ z ∈ Finset.univ.filter (fun z : W ↦ ¬ P z), min (D z : ℤ) (t : ℤ))
          - (if d b ≤ t then 1 else 0) + (if d x ≤ t then 1 else 0) := by
    let F : Finset W := Finset.univ.filter (fun z ↦ ¬ P z)
    have hbF : bv ∈ F := by
      simp [F, P, H, bv, hfc.distinct.2.1.symm, hfc.not_mem.2.2.1]
    have hxF : xv ∈ F := by
      simp [F, P, H, xv, hfc.distinct.2.2.1.symm, hfc.not_mem.2.2.2]
    have hbneX : bv ≠ xv := by
      intro heq
      exact hfc.distinct.2.2.2.2.2 (congr_arg Subtype.val heq)
    have hxE : xv ∈ F.erase bv := Finset.mem_erase.mpr ⟨hbneX.symm, hxF⟩
    change (∑ z ∈ F, min (R z : ℤ) (t : ℤ)) =
      (∑ z ∈ F, min (D z : ℤ) (t : ℤ))
        - (if d b ≤ t then 1 else 0) + (if d x ≤ t then 1 else 0)
    rw [← Finset.sum_erase_add F (fun z ↦ min (R z : ℤ) (t : ℤ)) hbF,
      ← Finset.sum_erase_add F (fun z ↦ min (D z : ℤ) (t : ℤ)) hbF,
      ← Finset.sum_erase_add (F.erase bv) (fun z ↦ min (R z : ℤ) (t : ℤ)) hxE,
      ← Finset.sum_erase_add (F.erase bv) (fun z ↦ min (D z : ℤ) (t : ℤ)) hxE]
    have hrest :
        (∑ z ∈ (F.erase bv).erase xv, min (R z : ℤ) (t : ℤ)) =
          ∑ z ∈ (F.erase bv).erase xv, min (D z : ℤ) (t : ℤ) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hzneb : z.val ≠ b := by
        intro heq
        have : z = bv := Subtype.ext heq
        subst z
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1 rfl
      have hznex : z.val ≠ x := by
        intro heq
        have : z = xv := Subtype.ext heq
        subst z
        exact (Finset.mem_erase.mp hz).1 rfl
      congr 1
      simp [D, R, fourCornerD, fourCornerV, residualDegree, hzneb, hznex]
    rw [hrest]
    omega
  constructor
  · change erdosGallaiSlack U t = erdosGallaiSlack D t
      + 1 + (if d a ≤ t then 1 else 0)
    rw [hslackU, hslackD]
    omega
  · change erdosGallaiSlack R t = erdosGallaiSlack D t
      - (if d b ≤ t then 1 else 0) + (if d x ≤ t then 1 else 0)
    rw [hslackR, hslackD]
    omega

/-- **Lemma 8.3c (agreement above the pivot rank).** Manuscript §8.2: `F_D(j) = F_U(j)` for every
`j ≥ k+1`, and also at `j = k` when `p > q`. Passing from `D` to `U` replaces the pair of values
`(r, p−1)` by `(r−1, p)`, a unit transfer that changes nothing else. -/
theorem lemma_8_3c_agreement_above_pivot {d : V → ℕ} {v : V} {C₀ : Finset V} {c a b x : V}
    (hfc : FourCorner d v C₀ c a b x) :
    (∀ j, d v + 1 ≤ j →
        erdosGallaiSlack (fourCornerD d v C₀ a x) j
          = erdosGallaiSlack (fourCornerU d v C₀ c x) j) ∧
      (d b < d a →
        erdosGallaiSlack (fourCornerD d v C₀ a x) (d v)
          = erdosGallaiSlack (fourCornerU d v C₀ c x) (d v)) := by
  classical
  let W := {u : V // u ≠ v}
  have slack_eq_of_sorted_block (f g : W → ℕ) (P : W → Prop) [DecidablePred P]
      (m j : ℕ) (hcard : (Finset.univ.val.filter P).card = m)
      (hcommon : ∀ z, ¬ P z → f z = g z)
      (hsum : ((Finset.univ.val.filter P).map f).sum =
        ((Finset.univ.val.filter P).map g).sum)
      (hfhigh : ∀ z, P z → ∀ y, ¬ P y → f z ≥ f y)
      (hghigh : ∀ z, P z → ∀ y, ¬ P y → g z ≥ g y)
      (hmj : m ≤ j) : erdosGallaiSlack f j = erdosGallaiSlack g j := by
    let I : Multiset W := Finset.univ.val
    let If : Multiset W := I.filter P
    let Io : Multiset W := I.filter (fun z => ¬ P z)
    let Af : Multiset ℕ := If.map f
    let Ag : Multiset ℕ := If.map g
    let Bf : Multiset ℕ := Io.map f
    let Bg : Multiset ℕ := Io.map g
    have hI : If + Io = I := Multiset.filter_add_not P I
    have hB : Bf = Bg := by
      apply Multiset.map_congr rfl
      intro z hz
      exact hcommon z (Multiset.mem_filter.mp hz).2
    have hAfcard : Af.card = m := by
      simp [Af, If, I, hcard]
    have hAgcard : Ag.card = m := by
      simp [Ag, If, I, hcard]
    have hAfsum : Af.sum = Ag.sum := hsum
    have hsortf : (Finset.univ.val.map f).sort (· ≥ ·) =
        Af.sort (· ≥ ·) ++ Bf.sort (· ≥ ·) := by
      change (I.map f).sort (· ≥ ·) = _
      rw [← hI, Multiset.map_add]
      apply sort_add_of_high Af Bf
      intro z hz y hy
      obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hz
      obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hy
      exact hfhigh u (Multiset.mem_filter.mp hu).2 w (Multiset.mem_filter.mp hw).2
    have hsortg : (Finset.univ.val.map g).sort (· ≥ ·) =
        Ag.sort (· ≥ ·) ++ Bg.sort (· ≥ ·) := by
      change (I.map g).sort (· ≥ ·) = _
      rw [← hI, Multiset.map_add]
      apply sort_add_of_high Ag Bg
      intro z hz y hy
      obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hz
      obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hy
      exact hghigh u (Multiset.mem_filter.mp hu).2 w (Multiset.mem_filter.mp hw).2
    have hlenf : (Af.sort (· ≥ ·)).length = m := by simp [hAfcard]
    have hleng : (Ag.sort (· ≥ ·)).length = m := by simp [hAgcard]
    have hsumsort : (Af.sort (· ≥ ·)).sum = (Ag.sort (· ≥ ·)).sum := by
      rw [← Multiset.sum_coe, Multiset.sort_eq, ← Multiset.sum_coe, Multiset.sort_eq]
      exact hAfsum
    have hlenfj : (Af.sort (· ≥ ·)).length ≤ j := hlenf.trans_le hmj
    have hlengj : (Ag.sort (· ≥ ·)).length ≤ j := hleng.trans_le hmj
    have hdropf : (Af.sort (· ≥ ·)).drop j = [] := List.drop_eq_nil_of_le hlenfj
    have hdropg : (Ag.sort (· ≥ ·)).drop j = [] := List.drop_eq_nil_of_le hlengj
    have htakef : (Af.sort (· ≥ ·)).take j = Af.sort (· ≥ ·) :=
      List.take_of_length_le hlenfj
    have htakeg : (Ag.sort (· ≥ ·)).take j = Ag.sort (· ≥ ·) :=
      List.take_of_length_le hlengj
    have hdrops :
        ((Finset.univ.val.map f).sort (· ≥ ·)).drop j =
          ((Finset.univ.val.map g).sort (· ≥ ·)).drop j := by
      rw [hsortf, hsortg, List.drop_append, List.drop_append, hlenf, hleng,
        hdropf, hdropg, hB]
    have coe_sum (l : List ℕ) : (show List ℤ from l).sum = (l.sum : ℤ) := by
      induction l with
      | nil => rfl
      | cons z l ih =>
          change (z : ℤ) + (show List ℤ from l).sum = ((z + l.sum : ℕ) : ℤ)
          rw [ih, Nat.cast_add]
    have htakesNat :
        (((Finset.univ.val.map f).sort (· ≥ ·)).take j).sum =
          (((Finset.univ.val.map g).sort (· ≥ ·)).take j).sum := by
      rw [hsortf, hsortg, List.take_append, List.take_append, hlenf, hleng,
        htakef, htakeg, List.sum_append, List.sum_append, hB, hsumsort]
    unfold erdosGallaiSlack
    rw [hdrops]
    simp only [List.map_id_fun', id_eq]
    rw [coe_sum, coe_sum, htakesNat]
  let D : W → ℕ := fourCornerD d v C₀ a x
  let U : W → ℕ := fourCornerU d v C₀ c x
  let cv : W := ⟨c, hfc.ne_pivot.1⟩
  let av : W := ⟨a, hfc.ne_pivot.2.1⟩
  have hgaps := lemma_8_3a_strict_outer_gaps hfc
  have hp_lt_r : d a < d c := hgaps.1
  have hs_lt_q : d x < d b := hgaps.2
  have hq_le_p : d b ≤ d a := hfc.ordered.2.1
  have hp_le_r : d a ≤ d c := hfc.ordered.2.2
  have hs_le_q : d x ≤ d b := hfc.ordered.1
  have hkcard : C₀.card + 2 = d v := hfc.card
  have hapos : 0 < d a := by omega
  have hcpos : 0 < d c := by omega
  have hDc : D cv = d c := by
    simp [D, cv, fourCornerD, residualDegree, hfc.distinct.1,
      hfc.distinct.2.2.1, hfc.not_mem.1]
  have hUc : U cv = d c - 1 := by
    simp [U, cv, fourCornerU, residualDegree]
  have hDa : D av = d a - 1 := by
    simp [D, av, fourCornerD, residualDegree]
  have hUa : U av = d a := by
    simp [U, av, fourCornerU, residualDegree, hfc.distinct.1.symm,
      hfc.distinct.2.2.2.2.1, hfc.not_mem.2.1]
  have hDU_of_ne (z : W) (hzc : z.val ≠ c) (hza : z.val ≠ a) : D z = U z := by
    simp [D, U, fourCornerD, fourCornerU, residualDegree, hzc, hza]
  have block_card (H : Finset V) (hvH : v ∉ H) :
      (Finset.univ.val.filter (fun z : W => z.val ∈ H)).card = H.card := by
    change (Finset.univ.filter (fun z : W => z.val ∈ H)).card = H.card
    apply Finset.card_bij (fun z _ => z.val)
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
    · intro z₁ _ z₂ _ heq
      exact Subtype.ext heq
    · intro z hz
      have hzv : z ≠ v := by
        intro h
        subst z
        exact hvH hz
      refine ⟨⟨z, hzv⟩, ?_, rfl⟩
      simp [hz]
  have block_sum (P : W → Prop) [DecidablePred P]
      (hPc : P cv) (hPa : P av) :
      ((Finset.univ.val.filter P).map D).sum =
        ((Finset.univ.val.filter P).map U).sum := by
    let F : Finset W := Finset.univ.filter P
    have hcvF : cv ∈ F := by simp [F, hPc]
    have havF : av ∈ F := by simp [F, hPa]
    have hcva : cv ≠ av := by
      intro h
      exact hfc.distinct.1 (congr_arg Subtype.val h)
    have havE : av ∈ F.erase cv := Finset.mem_erase.mpr ⟨hcva.symm, havF⟩
    change (∑ z ∈ F, D z) = ∑ z ∈ F, U z
    rw [← Finset.sum_erase_add F D hcvF, ← Finset.sum_erase_add F U hcvF,
      ← Finset.sum_erase_add (F.erase cv) D havE,
      ← Finset.sum_erase_add (F.erase cv) U havE]
    have hrest :
        (∑ z ∈ (F.erase cv).erase av, D z) =
          ∑ z ∈ (F.erase cv).erase av, U z := by
      apply Finset.sum_congr rfl
      intro z hz
      have hznec : z.val ≠ c := by
        intro heq
        have : z = cv := Subtype.ext heq
        subst z
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1 rfl
      have hznea : z.val ≠ a := by
        intro heq
        have : z = av := Subtype.ext heq
        subst z
        exact (Finset.mem_erase.mp hz).1 rfl
      exact hDU_of_ne z hznec hznea
    rw [hrest, hDc, hUc, hDa, hUa]
    omega
  have block_common (P : W → Prop) [DecidablePred P]
      (hPc : P cv) (hPa : P av) :
      ∀ z, ¬P z → D z = U z := by
    intro z hz
    apply hDU_of_ne z
    · intro heq
      apply hz
      have : z = cv := Subtype.ext heq
      simpa [this] using hPc
    · intro heq
      apply hz
      have : z = av := Subtype.ext heq
      simpa [this] using hPa
  let Hbig : Finset V := insert b (insert a (insert c C₀))
  let Pbig : W → Prop := fun z => z.val ∈ Hbig
  have hvHbig : v ∉ Hbig := by
    simp [Hbig, hfc.ne_pivot.1.symm, hfc.ne_pivot.2.1.symm,
      hfc.ne_pivot.2.2.1.symm, hfc.pivot_not_mem]
  have hcardHbig : Hbig.card = d v + 1 := by
    have hcC : c ∉ C₀ := hfc.not_mem.1
    have haC : a ∉ insert c C₀ := by
      simp [hfc.not_mem.2.1, hfc.distinct.1.symm]
    have hbC : b ∉ insert a (insert c C₀) := by
      simp [hfc.not_mem.2.2.1, hfc.distinct.2.1.symm,
        hfc.distinct.2.2.2.1.symm]
    simp [Hbig, hcC, haC, hbC]
    omega
  have hPbigc : Pbig cv := by simp [Pbig, Hbig, cv]
  have hPbiga : Pbig av := by simp [Pbig, Hbig, av]
  have hcardbig : (Finset.univ.val.filter Pbig).card = d v + 1 := by
    rw [block_card Hbig hvHbig, hcardHbig]
  have hcommonbig := block_common Pbig hPbigc hPbiga
  have hsumbig := block_sum Pbig hPbigc hPbiga
  have hDhighbig : ∀ z, Pbig z → ∀ y, ¬Pbig y → D z ≥ D y := by
    rintro ⟨z, hzv⟩ hz ⟨y, hyv⟩ hy
    have hDylow : D ⟨y, hyv⟩ ≤ d x := by
      by_cases hyx : y = x
      · subst y
        simp [D, fourCornerD, residualDegree]
      · have hyC : y ∉ C₀ := by
          intro h
          apply hy
          simp [Pbig, Hbig, h]
        have hyc : y ≠ c := by
          intro h
          apply hy
          simp [Pbig, Hbig, h]
        have hya : y ≠ a := by
          intro h
          apply hy
          simp [Pbig, Hbig, h]
        have hyb : y ≠ b := by
          intro h
          apply hy
          simp [Pbig, Hbig, h]
        exact (Nat.sub_le _ _).trans (hfc.tail y hyv hyC hyc hya hyb hyx)
    have hDz : d x ≤ D ⟨z, hzv⟩ := by
      simp only [Pbig, Hbig, Finset.mem_insert] at hz
      rcases hz with rfl | rfl | rfl | hzC
      · simp [D, fourCornerD, residualDegree, hfc.distinct.2.2.2.1.symm,
          hfc.distinct.2.2.2.2.2, hfc.not_mem.2.2.1]
        omega
      · simp [D, fourCornerD, residualDegree]
        omega
      · simp [D, fourCornerD, residualDegree, hfc.distinct.1,
          hfc.distinct.2.2.1, hfc.not_mem.1]
        omega
      · simp [D, fourCornerD, residualDegree, hzC]
        have := hfc.top_block z hzC
        omega
    omega
  have hUhighbig : ∀ z, Pbig z → ∀ y, ¬Pbig y → U z ≥ U y := by
    rintro ⟨z, hzv⟩ hz ⟨y, hyv⟩ hy
    have hUylow : U ⟨y, hyv⟩ ≤ d x := by
      by_cases hyx : y = x
      · subst y
        simp [U, fourCornerU, residualDegree]
      · have hyC : y ∉ C₀ := by
          intro h
          apply hy
          simp [Pbig, Hbig, h]
        have hyc : y ≠ c := by
          intro h
          apply hy
          simp [Pbig, Hbig, h]
        have hya : y ≠ a := by
          intro h
          apply hy
          simp [Pbig, Hbig, h]
        have hyb : y ≠ b := by
          intro h
          apply hy
          simp [Pbig, Hbig, h]
        exact (Nat.sub_le _ _).trans (hfc.tail y hyv hyC hyc hya hyb hyx)
    have hUz : d x ≤ U ⟨z, hzv⟩ := by
      simp only [Pbig, Hbig, Finset.mem_insert] at hz
      rcases hz with rfl | rfl | rfl | hzC
      · simp [U, fourCornerU, residualDegree, hfc.distinct.2.1.symm,
          hfc.distinct.2.2.2.2.2, hfc.not_mem.2.2.1]
        omega
      · simp [U, fourCornerU, residualDegree, hfc.distinct.1.symm,
          hfc.distinct.2.2.2.2.1, hfc.not_mem.2.1]
        omega
      · simp [U, fourCornerU, residualDegree]
        omega
      · simp [U, fourCornerU, residualDegree, hzC]
        have := hfc.top_block z hzC
        omega
    omega
  constructor
  · intro j hj
    exact slack_eq_of_sorted_block D U Pbig (d v + 1) j
      hcardbig hcommonbig hsumbig hDhighbig hUhighbig hj
  · intro hba
    let Hsmall : Finset V := insert a (insert c C₀)
    let Psmall : W → Prop := fun z => z.val ∈ Hsmall
    have hvHsmall : v ∉ Hsmall := by
      simp [Hsmall, hfc.ne_pivot.1.symm, hfc.ne_pivot.2.1.symm,
        hfc.pivot_not_mem]
    have hcardHsmall : Hsmall.card = d v := by
      have hcC : c ∉ C₀ := hfc.not_mem.1
      have haC : a ∉ insert c C₀ := by
        simp [hfc.not_mem.2.1, hfc.distinct.1.symm]
      simp [Hsmall, hcC, haC]
      omega
    have hPsmallc : Psmall cv := by simp [Psmall, Hsmall, cv]
    have hPsmalla : Psmall av := by simp [Psmall, Hsmall, av]
    have hcardsmall : (Finset.univ.val.filter Psmall).card = d v := by
      rw [block_card Hsmall hvHsmall, hcardHsmall]
    have hcommonsmall := block_common Psmall hPsmallc hPsmalla
    have hsumsmall := block_sum Psmall hPsmallc hPsmalla
    have hDhighsmall : ∀ z, Psmall z → ∀ y, ¬Psmall y → D z ≥ D y := by
      rintro ⟨z, hzv⟩ hz ⟨y, hyv⟩ hy
      have hDylow : D ⟨y, hyv⟩ ≤ d b := by
        by_cases hyb : y = b
        · subst y
          simp [D, fourCornerD, residualDegree, hfc.distinct.2.2.2.1.symm,
            hfc.distinct.2.2.2.2.2, hfc.not_mem.2.2.1]
        · by_cases hyx : y = x
          · subst y
            simp [D, fourCornerD, residualDegree]
            omega
          · have hyC : y ∉ C₀ := by
              intro h
              apply hy
              simp [Psmall, Hsmall, h]
            have hyc : y ≠ c := by
              intro h
              apply hy
              simp [Psmall, Hsmall, h]
            have hya : y ≠ a := by
              intro h
              apply hy
              simp [Psmall, Hsmall, h]
            exact (Nat.sub_le _ _).trans
              ((hfc.tail y hyv hyC hyc hya hyb hyx).trans hfc.ordered.1)
      have hDz : d b ≤ D ⟨z, hzv⟩ := by
        simp only [Psmall, Hsmall, Finset.mem_insert] at hz
        rcases hz with rfl | rfl | hzC
        · simp [D, fourCornerD, residualDegree]
          omega
        · simp [D, fourCornerD, residualDegree, hfc.distinct.1,
            hfc.distinct.2.2.1, hfc.not_mem.1]
          omega
        · simp [D, fourCornerD, residualDegree, hzC]
          have := hfc.top_block z hzC
          omega
      omega
    have hUhighsmall : ∀ z, Psmall z → ∀ y, ¬Psmall y → U z ≥ U y := by
      rintro ⟨z, hzv⟩ hz ⟨y, hyv⟩ hy
      have hUylow : U ⟨y, hyv⟩ ≤ d b := by
        by_cases hyb : y = b
        · subst y
          simp [U, fourCornerU, residualDegree, hfc.distinct.2.1.symm,
            hfc.distinct.2.2.2.2.2, hfc.not_mem.2.2.1]
        · by_cases hyx : y = x
          · subst y
            simp [U, fourCornerU, residualDegree]
            omega
          · have hyC : y ∉ C₀ := by
              intro h
              apply hy
              simp [Psmall, Hsmall, h]
            have hyc : y ≠ c := by
              intro h
              apply hy
              simp [Psmall, Hsmall, h]
            have hya : y ≠ a := by
              intro h
              apply hy
              simp [Psmall, Hsmall, h]
            exact (Nat.sub_le _ _).trans
              ((hfc.tail y hyv hyC hyc hya hyb hyx).trans hfc.ordered.1)
      have hUz : d b ≤ U ⟨z, hzv⟩ := by
        simp only [Psmall, Hsmall, Finset.mem_insert] at hz
        rcases hz with rfl | rfl | hzC
        · simp [U, fourCornerU, residualDegree, hfc.distinct.1.symm,
            hfc.distinct.2.2.2.2.1, hfc.not_mem.2.1]
          omega
        · simp [U, fourCornerU, residualDegree]
          omega
        · simp [U, fourCornerU, residualDegree, hzC]
          have := hfc.top_block z hzC
          omega
      omega
    exact slack_eq_of_sorted_block D U Psmall (d v) (d v)
      hcardsmall hcommonsmall hsumsmall hDhighsmall hUhighsmall le_rfl

/-! ## 8.2.1 The Erdős–Gallai equality input, in SET form

Lemma 8.3d's Step 3 needs a structural fact about Erdős–Gallai **equality**:

> *in any realization, equality at rank `t` forces the top `t` vertices to form a clique, and every
> vertex outside the top `t` of degree at least `t` to be adjacent to all of them.*

That is standard in the degree-sequence literature, and it is in neither this development nor
Mathlib (checked 2026-08-18: Mathlib has no Erdős–Gallai at all). Its usual statement also
presupposes an ORDER on the vertices — *"the top `t`"* — while its conclusion is about a realization
rather than about a degree function, and that mismatch is what `LEAN_SEC8_ENCODING_2026-08-17.md`
left undecided.

**The decision, 2026-08-18: state it for an ARBITRARY vertex set, and prove it here rather than cite
it.** The input is not the hard direction of Erdős–Gallai. For *any* `T`,

    ∑_{u ∈ T} deg u = ∑_{u ∈ T} |N(u) ∩ T| + ∑_{u ∉ T} |N(u) ∩ T|
                    ≤ |T|(|T|−1) + ∑_{u ∉ T} min(deg u, |T|),

by one double count of the edges leaving `T`, with both bounds TERMWISE — `|N(u) ∩ T| ≤ |T| − 1` for
`u ∈ T` because `u ∉ N(u)`, and `|N(u) ∩ T| ≤ min(deg u, |T|)` for `u ∉ T`. So equality forces every
term to be tight, which is exactly the clique and the saturation. No sorting appears anywhere, no
order on the vertices is needed, and nothing is cited: **the classical statement is the special case
`T` = a set of `t` vertices of largest degree, and it is that specialization, not the structure, that
needs the order.**

Three consequences of this choice, all of them the point:

* the trust surface does not grow — no seventh cited axiom, where citing the classical theorem would
  have added one;
* `MainLine` is untouched, so no `[LinearOrder V]` propagates (the hazard that option (A) of the
  yFamily-transport question carries);
* the order enters at exactly ONE place, `exists_topBlock` below, which is a statement about
  multisets of values and says nothing about graphs.

**Verified numerically before any of it was written**, per the rule that cost this lane three
statement-level defects in two days: `compute/eg_set_form_check_2026_08_18.py` checks the inequality
and the equality characterization over EVERY graph on at most 6 vertices and every subset — 2,131,018
instances, **0 violations** — plus 3,000 sampled graphs on 7 vertices. The same script checks that
the sorted-slack-to-set-slack bridge holds and is attained at a top-`t` set, and that Step 3's
consequence is **not vacuous**: its hypothesis fires 18,837 times at order 6.
-/

/-- **(EG-set), the inequality.** The Erdős–Gallai bound for an arbitrary vertex set, by one double
count of the edges leaving `T`. Both bounds are termwise, which is what makes the equality case
below immediate. -/
theorem sum_degree_le_of_finset {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (T : Finset W) :
    ∑ u ∈ T, G.degree u ≤ T.card * (T.card - 1) + ∑ u ∈ Tᶜ, min (G.degree u) T.card := by
  have hsplit (u : W) :
      G.degree u = (G.neighborFinset u ∩ T).card +
        (G.neighborFinset u ∩ Tᶜ).card := by
    rw [← G.card_neighborFinset_eq_degree]
    have hT : (G.neighborFinset u).filter (fun z => z ∈ T) =
        G.neighborFinset u ∩ T := Finset.filter_mem_eq_inter
    have hTc : (G.neighborFinset u).filter (fun z => z ∉ T) =
        G.neighborFinset u ∩ Tᶜ := by
      ext z
      simp
    rw [← hT, ← hTc]
    exact (Finset.card_filter_add_card_filter_not (s := G.neighborFinset u)
      (fun z => z ∈ T)).symm
  have hinter (u : W) (S : Finset W) :
      (G.neighborFinset u ∩ S).card =
        ∑ y ∈ S, if G.Adj u y then 1 else 0 := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
    congr 1
    ext y
    simp [SimpleGraph.mem_neighborFinset, and_comm]
  have hcross : (∑ u ∈ T, (G.neighborFinset u ∩ Tᶜ).card) =
      ∑ u ∈ Tᶜ, (G.neighborFinset u ∩ T).card := by
    calc
      (∑ u ∈ T, (G.neighborFinset u ∩ Tᶜ).card) =
          ∑ u ∈ T, ∑ y ∈ Tᶜ, if G.Adj u y then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro u hu
            exact hinter u Tᶜ
      _ = ∑ y ∈ Tᶜ, ∑ u ∈ T, if G.Adj u y then 1 else 0 := Finset.sum_comm
      _ = ∑ y ∈ Tᶜ, ∑ u ∈ T, if G.Adj y u then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        apply Finset.sum_congr rfl
        intro u hu
        simp only [G.adj_comm]
      _ = ∑ y ∈ Tᶜ, (G.neighborFinset y ∩ T).card := by
        apply Finset.sum_congr rfl
        intro y hy
        exact (hinter y T).symm
  have hdecomp : ∑ u ∈ T, G.degree u =
      (∑ u ∈ T, (G.neighborFinset u ∩ T).card) +
        ∑ u ∈ Tᶜ, (G.neighborFinset u ∩ T).card := by
    calc
      (∑ u ∈ T, G.degree u) = ∑ u ∈ T,
          ((G.neighborFinset u ∩ T).card + (G.neighborFinset u ∩ Tᶜ).card) := by
            apply Finset.sum_congr rfl
            intro u hu
            exact hsplit u
      _ = (∑ u ∈ T, (G.neighborFinset u ∩ T).card) +
          ∑ u ∈ T, (G.neighborFinset u ∩ Tᶜ).card := by
            rw [Finset.sum_add_distrib]
      _ = _ := by rw [hcross]
  have hinternal (u : W) (hu : u ∈ T) :
      (G.neighborFinset u ∩ T).card ≤ T.card - 1 := by
    have hsub : G.neighborFinset u ∩ T ⊆ T.erase u := by
      intro y hy
      rw [Finset.mem_erase]
      refine ⟨?_, (Finset.mem_inter.mp hy).2⟩
      intro hyu
      subst y
      exact G.irrefl (by
        simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hy).1)
    simpa [Finset.card_erase_of_mem hu] using Finset.card_le_card hsub
  have hexternal (u : W) (hu : u ∈ Tᶜ) :
      (G.neighborFinset u ∩ T).card ≤ min (G.degree u) T.card := by
    apply le_min
    · rw [← G.card_neighborFinset_eq_degree]
      exact Finset.card_le_card Finset.inter_subset_left
    · exact Finset.card_le_card Finset.inter_subset_right
  rw [hdecomp]
  apply Nat.add_le_add
  · simpa using Finset.sum_le_sum hinternal
  · exact Finset.sum_le_sum hexternal

/- The equality case used below is declared in `EqualityCase.lean`, a prerequisite of
`TightUnion.lean`; keeping its namespace unchanged avoids duplicating this proof. -/

/-- **The degree bound Step 3 actually consumes.** At equality, a vertex `u` of `T` is adjacent to
all of `T ∖ {u}` and to every outside vertex of degree at least `|T|`; if every vertex of `T` has
degree at least `|T|` those are all the vertices of degree at least `|T|` except `u` itself, so

    #{ z : deg z ≥ |T| }  ≤  deg u + 1.

Lemma 8.3d applies this with `|T| = t` and `u` a vertex of `T` of the least degree, `y_t = r − 1`,
to get `N_t(U) ≤ r`.

⚠ The hypothesis `∀ z ∈ T, |T| ≤ deg z` is not decoration. Without it a low-degree member of `T` is
counted on the left and not reached on the right, and the bound is false. In the application it
holds because `y_t = r − 1 ≥ t`, which is (8.1). -/
theorem card_highDegree_le_succ_degree {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] {T : Finset W} {u : W} (hu : u ∈ T)
    (hdeg : ∀ z ∈ T, T.card ≤ G.degree z)
    (heq : ∑ z ∈ T, G.degree z = T.card * (T.card - 1) + ∑ z ∈ Tᶜ, min (G.degree z) T.card) :
    (Finset.univ.filter (fun z => T.card ≤ G.degree z)).card ≤ G.degree u + 1 := by
  let H := Finset.univ.filter (fun z => T.card ≤ G.degree z)
  change H.card ≤ G.degree u + 1
  have hstructure := isClique_of_sum_degree_eq G heq
  have hclique : G.IsClique (T : Set W) := hstructure.1
  have hsaturated : ∀ z ∈ Tᶜ,
      (G.neighborFinset z ∩ T).card = min (G.degree z) T.card := hstructure.2
  have huH : u ∈ H := by simp [H, hdeg u hu]
  have hsub : H.erase u ⊆ G.neighborFinset u := by
    intro z hz
    have hzne : z ≠ u := (Finset.mem_erase.mp hz).1
    have hzH : z ∈ H := (Finset.mem_erase.mp hz).2
    have hzdeg : T.card ≤ G.degree z := (Finset.mem_filter.mp hzH).2
    by_cases hzT : z ∈ T
    · have hadj : G.Adj u z := (G.isClique_iff.mp hclique) hu hzT hzne.symm
      simpa only [SimpleGraph.mem_neighborFinset] using hadj
    · have hzTc : z ∈ Tᶜ := by simpa using hzT
      have hintercard : (G.neighborFinset z ∩ T).card = T.card := by
        rw [hsaturated z hzTc, min_eq_right hzdeg]
      have hintereq : G.neighborFinset z ∩ T = T := by
        apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
        rw [hintercard]
      have huNz : u ∈ G.neighborFinset z := by
        have : u ∈ G.neighborFinset z ∩ T := by rw [hintereq]; exact hu
        exact (Finset.mem_inter.mp this).1
      have hzu : G.Adj z u := by
        simpa only [SimpleGraph.mem_neighborFinset] using huNz
      simpa only [SimpleGraph.mem_neighborFinset] using hzu.symm
  have hle : (H.erase u).card ≤ G.degree u := by
    rw [← G.card_neighborFinset_eq_degree]
    exact Finset.card_le_card hsub
  have hcard : (H.erase u).card = H.card - 1 := Finset.card_erase_of_mem huH
  rw [hcard] at hle
  omega

/-- **The bridge, and the ONLY place an order enters.** A set of `t` vertices carrying the top `t`
values: its value multiset is the first `t` of the sorted list and its complement's is the rest.

This is a statement about multisets of naturals; it mentions no graph. Ties are why it is an
existence statement rather than a definition — several sets carry the top `t` values when the `t`-th
and `(t+1)`-st agree, and the manuscript's Lemma 8.3b makes the same point in prose (*"a tie at the
boundary can exchange labels but not values"*).

**Reuse, do not re-derive:** the kernel is the `sort_add_of_high` argument already inside
`lemma_8_3c_agreement_above_pivot` — if every value of `A` dominates every value of `B` then
`(A + B).sort = A.sort ++ B.sort`. Take `A` to be the block strictly above the threshold value
together with enough of the ties, and `B` the rest. -/
theorem exists_topBlock {W : Type*} [Fintype W] [DecidableEq W] (w : W → ℕ) {t : ℕ}
    (ht : t ≤ Fintype.card W) :
    ∃ T : Finset W, T.card = t ∧ (∀ z ∈ T, ∀ y ∈ Tᶜ, w y ≤ w z) ∧
      (T.val.map w) = ((Finset.univ.val.map w).sort (· ≥ ·)).take t ∧
      (Tᶜ.val.map w) = ((Finset.univ.val.map w).sort (· ≥ ·)).drop t := by
  let F : Finset (Finset W) := Finset.univ.powersetCard t
  have hF : F.Nonempty := by
    obtain ⟨T, hTuniv, hTcard⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset W)) (by simpa using ht)
    exact ⟨T, Finset.mem_powersetCard.mpr ⟨hTuniv, hTcard⟩⟩
  obtain ⟨T, hTF, hmax⟩ :=
    Finset.exists_max_image F (fun S => ∑ z ∈ S, w z) hF
  have hTcard : T.card = t := (Finset.mem_powersetCard.mp hTF).2
  have htop : ∀ z ∈ T, ∀ y ∈ Tᶜ, w y ≤ w z := by
    intro z hz y hy
    by_contra hnot
    have hzy : w z < w y := Nat.lt_of_not_ge hnot
    have hyT : y ∉ T := by simpa using hy
    let T' := insert y (T.erase z)
    have hyErase : y ∉ T.erase z := by simp [hyT]
    have htpos : 0 < t := by
      have : 0 < T.card := Finset.card_pos.mpr ⟨z, hz⟩
      omega
    have hT'card : T'.card = t := by
      simp [T', hyErase, Finset.card_erase_of_mem hz, hTcard]
      omega
    have hT'F : T' ∈ F := by
      apply Finset.mem_powersetCard.mpr
      exact ⟨Finset.subset_univ _, hT'card⟩
    have hmax' := hmax T' hT'F
    have hsumT : (∑ x ∈ T, w x) = (∑ x ∈ T.erase z, w x) + w z :=
      (Finset.sum_erase_add T w hz).symm
    have hsumT' : (∑ x ∈ T', w x) = w y + ∑ x ∈ T.erase z, w x := by
      simp [T', hyErase]
    rw [hsumT, hsumT'] at hmax'
    omega
  let A : Multiset ℕ := T.val.map w
  let B : Multiset ℕ := Tᶜ.val.map w
  have hpartition : T.val + Tᶜ.val = (Finset.univ : Finset W).val := by
    ext x
    rw [Multiset.count_add]
    by_cases hx : x ∈ T
    · rw [Multiset.count_eq_one_of_mem T.nodup hx,
        Multiset.count_eq_zero_of_notMem (by simpa using hx),
        Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ x)]
    · rw [Multiset.count_eq_zero_of_notMem hx,
        Multiset.count_eq_one_of_mem Tᶜ.nodup (by simpa using hx),
        Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ x)]
  have hsort : ((Finset.univ.val.map w).sort (· ≥ ·)) =
      A.sort (· ≥ ·) ++ B.sort (· ≥ ·) := by
    rw [← hpartition, Multiset.map_add]
    change ((A + B).sort (· ≥ ·)) = _
    apply sort_add_of_high A B
    intro z hz y hy
    obtain ⟨z', hz', rfl⟩ := Multiset.mem_map.mp hz
    obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.mp hy
    exact htop z' hz' y' hy'
  have hAlength : (A.sort (· ≥ ·)).length = t := by simp [A, hTcard]
  have htake : ((Finset.univ.val.map w).sort (· ≥ ·)).take t = A.sort (· ≥ ·) := by
    rw [hsort, ← hAlength, List.take_left]
  have hdrop : ((Finset.univ.val.map w).sort (· ≥ ·)).drop t = B.sort (· ≥ ·) := by
    rw [hsort, ← hAlength, List.drop_left]
  refine ⟨T, hTcard, htop, ?_, ?_⟩
  · rw [htake]
    exact (Multiset.sort_eq A (· ≥ ·)).symm
  · rw [hdrop]
    exact (Multiset.sort_eq B (· ≥ ·)).symm

/-- **`erdosGallaiSlack` is the set slack at any top block.** The two forms of the slack agree, which
is what lets a hypothesis stated about the sorted sequence be used as a hypothesis about a concrete
vertex set — the step Lemma 8.3d needs in order to talk about a realization at all. -/
theorem erdosGallaiSlack_eq_of_topBlock {W : Type*} [Fintype W] [DecidableEq W] (w : W → ℕ) {t : ℕ}
    {T : Finset W} (hcard : T.card = t)
    (hT : (T.val.map w) = ((Finset.univ.val.map w).sort (· ≥ ·)).take t)
    (hTc : (Tᶜ.val.map w) = ((Finset.univ.val.map w).sort (· ≥ ·)).drop t) :
    erdosGallaiSlack w t
      = ((t : ℤ) * ((t : ℤ) - 1)) + (∑ z ∈ Tᶜ, (min (w z) t : ℤ)) - (∑ z ∈ T, (w z : ℤ)) := by
  have coe_sum (l : List ℕ) : (show List ℤ from l).sum = (l.sum : ℤ) := by
    induction l with
    | nil => rfl
    | cons z l ih =>
        change (z : ℤ) + (show List ℤ from l).sum = ((z + l.sum : ℕ) : ℤ)
        rw [ih, Nat.cast_add]
  have min_sum (l : List ℕ) :
      (l.map (fun z => (min z t : ℤ))).sum = ((l.map (fun z => min z t)).sum : ℤ) := by
    induction l with
    | nil => rfl
    | cons z l ih =>
        change (min z t : ℤ) + (l.map (fun z => (min z t : ℤ))).sum =
          (((min z t) + (l.map (fun z => min z t)).sum : ℕ) : ℤ)
        rw [ih, Nat.cast_add]
        norm_cast
  have htail :
      ((((Finset.univ.val.map w).sort (· ≥ ·)).drop t).map
          (fun z => (min z t : ℤ))).sum =
        ∑ z ∈ Tᶜ, (min (w z) t : ℤ) := by
    rw [min_sum]
    norm_cast
    change ((((Finset.univ.val.map w).sort (· ≥ ·)).drop t).map
        (fun z => min z t)).sum = (Tᶜ.val.map (fun z => min (w z) t)).sum
    rw [← Multiset.sum_coe, ← Multiset.map_coe, ← hTc]
    simp [Multiset.map_map, Function.comp_def]
  have htop :
      ((((Finset.univ.val.map w).sort (· ≥ ·)).take t).map
          (fun z => (z : ℤ))).sum =
        ∑ z ∈ T, (w z : ℤ) := by
    simp only [List.map_id_fun', id_eq]
    rw [coe_sum]
    norm_cast
    change (((Finset.univ.val.map w).sort (· ≥ ·)).take t).sum = (T.val.map w).sum
    rw [← Multiset.sum_coe, ← hT]
  unfold erdosGallaiSlack
  rw [htail, htop]

/-- The sorted/set slack identity for any chosen top `t`-set. This packages the multiset sorting
bookkeeping in `erdosGallaiSlack_eq_of_topBlock`, so tied top blocks can be used by label. -/
theorem erdosGallaiSlack_eq_of_topFinset {W : Type*} [Fintype W] [DecidableEq W]
    (w : W → ℕ) {t : ℕ} {T : Finset W} (hcard : T.card = t)
    (htop : ∀ z ∈ T, ∀ y ∈ Tᶜ, w z ≥ w y) :
    erdosGallaiSlack w t =
      ((t : ℤ) * ((t : ℤ) - 1)) + (∑ z ∈ Tᶜ, (min (w z) t : ℤ))
        - (∑ z ∈ T, (w z : ℤ)) := by
  let A : Multiset ℕ := T.val.map w
  let B : Multiset ℕ := Tᶜ.val.map w
  have hpartition : T.val + Tᶜ.val = (Finset.univ : Finset W).val := by
    ext x
    rw [Multiset.count_add]
    by_cases hx : x ∈ T
    · rw [Multiset.count_eq_one_of_mem T.nodup hx,
        Multiset.count_eq_zero_of_notMem (by simpa using hx),
        Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ x)]
    · rw [Multiset.count_eq_zero_of_notMem hx,
        Multiset.count_eq_one_of_mem Tᶜ.nodup (by simpa using hx),
        Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ x)]
  have hsort : ((Finset.univ.val.map w).sort (· ≥ ·)) =
      A.sort (· ≥ ·) ++ B.sort (· ≥ ·) := by
    rw [← hpartition, Multiset.map_add]
    change ((A + B).sort (· ≥ ·)) = _
    apply sort_add_of_high A B
    intro z hz y hy
    obtain ⟨z', hz', rfl⟩ := Multiset.mem_map.mp hz
    obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.mp hy
    exact htop z' (by simpa using hz') y' (by simpa using hy')
  have hAlength : (A.sort (· ≥ ·)).length = t := by simp [A, hcard]
  have htake : ((Finset.univ.val.map w).sort (· ≥ ·)).take t = A.sort (· ≥ ·) := by
    rw [hsort, ← hAlength, List.take_left]
  have hdrop : ((Finset.univ.val.map w).sort (· ≥ ·)).drop t = B.sort (· ≥ ·) := by
    rw [hsort, ← hAlength, List.drop_left]
  apply erdosGallaiSlack_eq_of_topBlock w hcard
  · rw [htake]
    exact (Multiset.sort_eq A (· ≥ ·)).symm
  · rw [hdrop]
    exact (Multiset.sort_eq B (· ≥ ·)).symm

/-- **The graph/sequence tightness bridge.** For a realization graph and any chosen top `t`-set,
set-form Erdős–Gallai tightness is equivalent to zero sorted slack. -/
theorem egTight_iff_erdosGallaiSlack_eq_zero_of_topFinset
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] {t : ℕ} {T : Finset W} (htpos : 0 < t)
    (hcard : T.card = t) (htop : ∀ z ∈ T, ∀ y ∈ Tᶜ, G.degree z ≥ G.degree y) :
    TightUnion.EGTight G T ↔ erdosGallaiSlack (fun z ↦ G.degree z) t = 0 := by
  rw [erdosGallaiSlack_eq_of_topFinset (fun z ↦ G.degree z) hcard htop]
  unfold TightUnion.EGTight
  constructor
  · intro heq
    have hcast := congrArg (fun n : ℕ ↦ (n : ℤ)) heq
    push_cast [Nat.cast_sub (by omega : 1 ≤ T.card)] at hcast
    rw [hcard] at hcast
    omega
  · intro hzero
    have hcast : ((∑ z ∈ T, G.degree z : ℕ) : ℤ) =
        ((T.card * (T.card - 1) + ∑ z ∈ Tᶜ, min (G.degree z) T.card : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ T.card)]
      rw [hcard]
      omega
    exact_mod_cast hcast

/-! ## 8.1′ The forced pair, without an order

Manuscript Lemma 8.2 names the universal pair as `{u_k, u_{k+1}}` **in the order
`u_1 ≻ u_2 ≻ ⋯`**, ties broken by label. `QStar.lean` is built over `[LinearOrder α]` and §7's yFamily
classification is stated in those terms, so transporting Lemma 8.2 to `QuotientV d v` looked like it
needed an order on `V` — and `[LinearOrder V]` would propagate through `MainLine`, which `sbPlus`,
`separator_buffer` and both top-level theorems consume.

**It does not. Settled 2026-08-18 (`results/2026-08-18_sec8_encoding_settled.md`).** The forced pair
can be *named* without any order, because Theorem 8.3 identifies it: `u_k` and `u_{k+1}` are exactly
the other two members of `v`'s own degree class. So the two statements §8 actually consumes are

    (8.2′)  an exceptional pivot's two Δ-neighbours are  { u ≠ v : d u = d v };
    (8.3′)  a yFamily pivot's degree class has three members, and d v − 1 vertices lie above it.

Neither mentions an order, and together they give what §8.5 assembles from Lemma 8.2, Theorem 8.3
and Corollary 8.4. Determinacy of the forced pair — the property the manuscript emphasizes, *"a pair
determined by `d` and `v` with no reference to `G_0` or `G_1`"* — is now a triviality rather than a
lemma, since the right-hand side mentions neither realization.

**The order survives only as a proof device.** Proving (8.2′) still reads Theorem 7.6 in a
non-increasing-degree order, and a linear order on a `Fintype` may be introduced inside the proof,
where Lean checks the outcome. This is the rule this module already records one level down: the
index-bearing table is needed to PROVE a lemma and not to STATE it, and inside a proof is the safe
place for it, because Lean rejects a wrong proof and nothing rejects a wrong statement.

**Verified before being written**, `compute/sec8_orderfree_check_2026_08_18.py`: exhaustive over every
graphical degree sequence with at least two realizations through ground order 8, on all **153** yFamily
pivots those sequences carry (84 on the main line, 69 off it) — 0 failures on (8.2′), 0 on both halves
of (8.3′), and 0 on a **faithfulness** check comparing the order-free pair against the manuscript's
ordered `{u_k, u_{k+1}}` computed independently. That last check is the point: an order-free statement
that is true but says less than the lemma it replaces would be a faithfulness gap, which is a defect
this lane has shipped twice. Neither statement needs Theorem 6.1's hypotheses — both hold on the 69
off-main-line pivots too — so the encoding does not quietly inherit one.
-/

/-- **The ⟹ half of Erdős–Gallai**, in the sorted form the slack calculus uses: a graphical degree
function has non-negative slack at every rank up to the ground size.

**Hoisted to top level 2026-08-24**, and the reason is worth recording. It existed only as an
anonymous local `have` inside `lemma_8_3d_lower_witness_propagation`, and again inside
`lemma_8_3e_one_sided_bound`, the two copies byte-identical but for a single underscore. Manuscript
§8.2 states outright that this half *"is proved below by a double count"* — but `#print axioms` cannot
see a local `have`, so `check_axiom_baseline.py` could not certify the claim, an auditor grepping the
tree found only the *set* form `sum_degree_le_of_finset`, and the two copies could drift apart. Found
by the adversary pass in `results/2026-08-24d_adversary_pass_deepest_proofs.md`.

The `j = 0` case is split off because the slack there is a sum of `min z 0` over an empty take, which
the top-block argument does not reach. -/
theorem erdosGallaiSlack_nonneg_of_graphical {W : Type*} [Fintype W] [DecidableEq W]
    (f : W → ℕ) (hf : Graphical f) (j : ℕ) (hj : j ≤ Fintype.card W) :
    0 ≤ erdosGallaiSlack f j := by
  by_cases hjzero : j = 0
  · subst j
    have min_zero_sum (l : List ℕ) :
        ((show List ℤ from l).map (fun z ↦ min z 0)).sum = 0 := by
      induction l with
      | nil => rfl
      | cons z l ih =>
        change min (z : ℤ) 0 + ((show List ℤ from l).map (fun y ↦ min y 0)).sum = 0
        rw [ih]
        simp
    unfold erdosGallaiSlack
    simp only [List.drop_zero, List.take_zero, List.map_nil, List.sum_nil]
    have hzero := min_zero_sum ((Finset.univ.val.map f).sort (· ≥ ·))
    simpa using hzero.ge
  · let G : Realization f := realizationOfGraphical hf
    obtain ⟨T, hTcard, hTtop, hT, hTc⟩ := exists_topBlock f hj
    have hle := sum_degree_le_of_finset G.graph T
    have hle' : ∑ z ∈ T, f z ≤
        T.card * (T.card - 1) + ∑ z ∈ Tᶜ, min (f z) T.card := by
      simpa only [G.degree_eq] using hle
    have hslack := erdosGallaiSlack_eq_of_topBlock f hTcard hT hTc
    rw [hslack]
    have hcardpos : 0 < T.card := by omega
    have hleZ : ((∑ z ∈ T, f z : ℕ) : ℤ) ≤
        ((T.card * (T.card - 1) + ∑ z ∈ Tᶜ, min (f z) T.card : ℕ) : ℤ) := by
      exact_mod_cast hle'
    push_cast [Nat.cast_sub (by omega : 1 ≤ T.card)] at hleZ
    rw [hTcard] at hleZ
    omega

/-- **A Y-family pivot**: the quotient family at `v` is a clique-sum, i.e. its graph is. The manuscript's `H(d)` is the
set of these. Note this asks only that the quotient graph *is* a clique-sum, not that any prescribed pair
is its universal pair — that stronger condition is `ExceptionalPivot`. -/
def YFamilyPivot (d : V → ℕ) (v : V) : Prop :=
  ∃ A B : QuotientV d v, (quotientGraph d v).IsCliqueSum A B

/-- **The bridge from a yFamily pivot to the four-corner hypothesis — manuscript §8.2's setup
paragraph.** Order the ground other than `v` by non-increasing degree, take `C₀ = {u_1 … u_{k−2}}`,
`c = u_{k−1}`, `a = u_k`, `b = u_{k+1}`, `x = u_{k+2}`; then `{c,x}` and `{a,b}` are realizable and
`{a,x}` is not, which is the three-condition hypothesis `FourCorner` now carries. `{c,a}` and `{c,b}`
are realizable too and `{b,x}` is not, but those three are consequences rather than assumptions — see
`FourCorner`'s own docstring and `FourCorner.not_corner_bx`. **Corrected 2026-08-24**: this paragraph
described the five-condition conclusion for some hours after the structure stopped asserting it.

**Why this had to be stated separately, and why its absence was a gap rather than an omission.**
Everything §8.2 proves — Lemmas 8.3a through 8.3f and Theorem 8.3 — is stated about a `FourCorner`
configuration. Everything §8.1′ and §8.4 consume is stated about a `YFamilyPivot`. **Nothing connected
them**, so Theorem 8.3 could not be applied to the object the rest of the paper talks about. The
manuscript's link is a single sentence: *"Because both yFamily arms are nonempty and contiguous (Theorem
7.6), the four sets … are realizable neighborhoods of `v`, while … are not, lying in neither arm."*

That sentence is the content here. It runs through §7's yFamily classification — `lemma3_two_arms` and
`lemma3_arms_are_contiguous` in `QStar.lean` — transported to the quotient by §1b's
`quotientIsoExchange`, which is what makes §7 applicable to a realization graph at all. The two
standing assumptions the manuscript records, `k ≥ 2` and `k + 2 ≤ n − 1`, come from a yFamily having at
least four members.

**Verified before being stated** (`compute/fourcorner_of_yfamilypivot_check_2026_08_18.py`): all **153**
yFamily pivots through ground order 8 yield the four-corner hypothesis at exactly these positions — 918
corner tests, 0 failures — together with the `ordered`, `top_block` and `tail` fields. -/
theorem fourCorner_of_yFamilyPivot {d : V → ℕ} {v : V} (h : YFamilyPivot d v) :
    ∃ (C₀ : Finset V) (c a b x : V), FourCorner d v C₀ c a b x := by
  classical
  obtain ⟨A, B, hbadQ⟩ := h
  obtain ⟨inst, hvmax, hmono⟩ := exists_pivotMaximal_degreeAntitone_order d v
  letI : LinearOrder V := inst
  let F := realizableNeighborhoods d v
  let φ := quotientIsoExchange d v
  have hAF : A.val ∈ F := mem_realizableNeighborhoods.mpr A.prop
  have hFne : F.Nonempty := ⟨A.val, hAF⟩
  have hshift : QStar.IsShifted F (d v) :=
    quotientFamily_isShifted d v hvmax hmono hFne
  have hbad : QStar.IsCliqueSum F (φ A) (φ B) :=
    QStar.isCliqueSum_map_iso φ hbadQ
  obtain ⟨r, s, hrG, hrU, hsC, hfamily⟩ :=
    QStar.lemma3_arms_are_contiguous hshift hbad
  let G := QStar.usedGround F
  change r ∈ G at hrG
  change r ∉ QStar.initialSegment G (d v + 1) at hrU
  change s ∈ QStar.initialSegment G (d v - 1) at hsC
  have hrRank : d v + 1 ≤ QStar.groundRank G r := by
    change r ∉ G.filter (fun z => QStar.groundRank G z < d v + 1) at hrU
    simpa [hrG] using hrU
  have hGcard : d v + 2 ≤ G.card := by
    have := QStar.groundRank_lt_card_of_mem hrG
    omega
  have hk : 2 ≤ d v := by
    change s ∈ G.filter (fun z => QStar.groundRank G z < d v - 1) at hsC
    have := (Finset.mem_filter.mp hsC).2
    omega
  let C₀ := QStar.initialSegment G (d v - 2)
  let c := G.orderEmbOfFin rfl ⟨d v - 2, by omega⟩
  let a := G.orderEmbOfFin rfl ⟨d v - 1, by omega⟩
  let b := G.orderEmbOfFin rfl ⟨d v, by omega⟩
  let x := G.orderEmbOfFin rfl ⟨d v + 1, by omega⟩
  have hcG : c ∈ G := by simp [c]
  have haG : a ∈ G := by simp [a]
  have hbG : b ∈ G := by simp [b]
  have hxG : x ∈ G := by simp [x]
  have hv_sets : ∀ S ∈ F, v ∉ S := by
    intro S hSF hvS
    obtain ⟨R, hR⟩ := mem_realizableNeighborhoods.mp hSF
    have : v ∈ R.neighborFinset v := by simpa [hR] using hvS
    exact R.graph.irrefl ((R.mem_neighborFinset v v).mp this)
  have hvG : v ∉ G := by
    intro hv
    change v ∈ F.biUnion id at hv
    obtain ⟨S, hSF, hvS⟩ := Finset.mem_biUnion.mp hv
    exact hv_sets S hSF hvS
  have hc_ne_v : c ≠ v := ne_of_mem_of_not_mem hcG hvG
  have ha_ne_v : a ≠ v := ne_of_mem_of_not_mem haG hvG
  have hb_ne_v : b ≠ v := ne_of_mem_of_not_mem hbG hvG
  have hx_ne_v : x ≠ v := ne_of_mem_of_not_mem hxG hvG
  have hcC : c ∉ C₀ := by
    simp [C₀, c, QStar.initialSegment_orderEmbOfFin_mem_iff]
  have haC : a ∉ C₀ := by
    simp [C₀, a, QStar.initialSegment_orderEmbOfFin_mem_iff]
    omega
  have hbC : b ∉ C₀ := by
    simp [C₀, b, QStar.initialSegment_orderEmbOfFin_mem_iff]
  have hxC : x ∉ C₀ := by
    simp [C₀, x, QStar.initialSegment_orderEmbOfFin_mem_iff]
    omega
  have hca : c < a := by
    change G.orderEmbOfFin rfl ⟨d v - 2, by omega⟩ <
      G.orderEmbOfFin rfl ⟨d v - 1, by omega⟩
    apply (G.orderEmbOfFin rfl).lt_iff_lt.mpr
    change d v - 2 < d v - 1
    omega
  have hab : a < b := by
    change G.orderEmbOfFin rfl ⟨d v - 1, by omega⟩ <
      G.orderEmbOfFin rfl ⟨d v, by omega⟩
    apply (G.orderEmbOfFin rfl).lt_iff_lt.mpr
    change d v - 1 < d v
    omega
  have hbx : b < x := by
    change G.orderEmbOfFin rfl ⟨d v, by omega⟩ <
      G.orderEmbOfFin rfl ⟨d v + 1, by omega⟩
    apply (G.orderEmbOfFin rfl).lt_iff_lt.mpr
    change d v < d v + 1
    omega
  have init_succ (j : ℕ) (hj : j < G.card) :
      QStar.initialSegment G (j + 1) =
        insert (G.orderEmbOfFin rfl ⟨j, hj⟩) (QStar.initialSegment G j) := by
    ext y
    constructor
    · intro hy
      have hyG := QStar.initialSegment_subset G (j + 1) hy
      let i : Fin G.card := (G.orderIsoOfFin rfl).symm ⟨y, hyG⟩
      have hyi : G.orderEmbOfFin rfl i = y := by
        exact congrArg Subtype.val ((G.orderIsoOfFin rfl).apply_symm_apply ⟨y, hyG⟩)
      have hi : (i : ℕ) < j + 1 :=
        (QStar.initialSegment_orderEmbOfFin_mem_iff G (j + 1) i).mp (hyi ▸ hy)
      by_cases hij : (i : ℕ) < j
      · have himem := (QStar.initialSegment_orderEmbOfFin_mem_iff G j i).mpr hij
        rw [hyi] at himem
        exact Finset.mem_insert.mpr (Or.inr himem)
      · have hieq : (i : ℕ) = j := by omega
        apply Finset.mem_insert.mpr
        left
        rw [← hyi]
        congr 1
        exact Fin.ext hieq
    · intro hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · apply (QStar.initialSegment_orderEmbOfFin_mem_iff G (j + 1) _).mpr
        change j < j + 1
        omega
      · exact QStar.initialSegment_mono G (Nat.le_succ j) hy
  have hC1 : QStar.initialSegment G (d v - 1) = insert c C₀ := by
    have h := init_succ (d v - 2) (by omega)
    simpa [C₀, c, show d v - 2 + 1 = d v - 1 by omega] using h
  have hI : QStar.initialSegment G (d v) = insert a (insert c C₀) := by
    have h := init_succ (d v - 1) (by omega)
    rw [show d v - 1 + 1 = d v by omega, hC1] at h
    simpa [a] using h
  have hU : QStar.initialSegment G (d v + 1) = insert b (insert a (insert c C₀)) := by
    have h := init_succ (d v) (by omega)
    rw [hI] at h
    simpa [b] using h
  have hUx : QStar.initialSegment G (d v + 2) =
      insert x (insert b (insert a (insert c C₀))) := by
    have h := init_succ (d v + 1) (by omega)
    rw [hU] at h
    simpa [x, Nat.add_assoc] using h
  have hM2 : QStar.secondInitialSegment G (d v) = insert b (insert c C₀) := by
    rw [QStar.secondInitialSegment, hC1, hU, hI]
    ext y
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert]
    constructor <;> intro hy
    · rcases hy with hy | ⟨hy, hynot⟩
      · exact Or.inr hy
      · rcases hy with rfl | rfl | rfl | hyC
        · exact Or.inl rfl
        · exact (hynot (Or.inl rfl)).elim
        · exact (hynot (Or.inr (Or.inl rfl))).elim
        · exact (hynot (Or.inr (Or.inr hyC))).elim
    · rcases hy with rfl | rfl | hyC
      · apply Or.inr
        refine ⟨Or.inl rfl, ?_⟩
        rintro (hba | hbc | hbC')
        · exact hab.ne' hba
        · exact (hca.trans hab).ne' hbc
        · exact hbC hbC'
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr hyC)
  have hx_not_U : x ∉ QStar.initialSegment G (d v + 1) := by
    apply (QStar.initialSegment_orderEmbOfFin_mem_iff G (d v + 1) _).not.mpr
    change ¬ d v + 1 < d v + 1
    omega
  have hb_not_C1 : b ∉ QStar.initialSegment G (d v - 1) := by
    apply (QStar.initialSegment_orderEmbOfFin_mem_iff G (d v - 1) _).not.mpr
    change ¬ d v < d v - 1
    omega
  have hcC1 : c ∈ QStar.initialSegment G (d v - 1) := by rw [hC1]; simp
  have hbU : b ∈ QStar.initialSegment G (d v + 1) := by rw [hU]; simp
  have hxTop : x ∈ QStar.initialSegment G (d v + 2) := by rw [hUx]; simp
  have rank_lt {y z : V} (hyG : y ∈ G) (hzG : z ∈ G) (hyz : y < z) :
      QStar.groundRank G y < QStar.groundRank G z := by
    rw [QStar.groundRank, QStar.groundRank]
    apply Finset.card_lt_card
    refine ⟨?_, ?_⟩
    · intro w hw
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2.trans hyz⟩
    · intro hback
      have hyRight : y ∈ G.filter (fun w => w < z) :=
        Finset.mem_filter.mpr ⟨hyG, hyz⟩
      have hyLeft := hback hyRight
      exact (lt_irrefl y) (Finset.mem_filter.mp hyLeft).2
  have hxRank : QStar.groundRank G x = d v + 1 := by
    simpa [x] using QStar.groundRank_orderEmbOfFin G ⟨d v + 1, by omega⟩
  have hcRank : QStar.groundRank G c = d v - 2 := by
    simpa [c] using QStar.groundRank_orderEmbOfFin G ⟨d v - 2, by omega⟩
  have hxr : x ≤ r := by
    by_contra hnot
    have hrx : r < x := lt_of_not_ge hnot
    have := rank_lt hrG hxG hrx
    omega
  have hsG : s ∈ G := QStar.initialSegment_subset G (d v - 1) hsC
  have hsc : s ≤ c := by
    by_contra hnot
    have hcs : c < s := lt_of_not_ge hnot
    have hrank := rank_lt hcG hsG hcs
    change s ∈ G.filter (fun z => QStar.groundRank G z < d v - 1) at hsC
    have hsRank := (Finset.mem_filter.mp hsC).2
    omega
  change F = QStar.yFamily G (d v) r s at hfamily
  have hcaSet : insert c (insert a C₀) = QStar.initialSegment G (d v) := by
    rw [hI]
    exact Finset.insert_comm c a C₀
  have hcbSet : insert c (insert b C₀) = QStar.secondInitialSegment G (d v) := by
    rw [hM2]
    exact Finset.insert_comm c b C₀
  have hcxSet : insert c (insert x C₀) =
      insert x (QStar.initialSegment G (d v - 1)) := by
    rw [hC1]
    exact Finset.insert_comm c x C₀
  have habSet : insert a (insert b C₀) =
      (QStar.initialSegment G (d v + 1)).erase c := by
    rw [hU]
    ext y
    simp only [Finset.mem_insert, Finset.mem_erase]
    constructor
    · intro hy
      rcases hy with rfl | rfl | hyC
      · exact ⟨hca.ne', Or.inr (Or.inl rfl)⟩
      · exact ⟨(hca.trans hab).ne', Or.inl rfl⟩
      · exact ⟨fun h => hcC (h ▸ hyC), Or.inr (Or.inr (Or.inr hyC))⟩
    · rintro ⟨hyc, hy⟩
      rcases hy with rfl | rfl | rfl | hyC
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
      · exact (hyc rfl).elim
      · exact Or.inr (Or.inr hyC)
  have hcxF : insert c (insert x C₀) ∈ F := by
    rw [hfamily, QStar.yFamily]
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    rw [QStar.yOuterArm]
    apply Finset.mem_image.mpr
    exact ⟨x, Finset.mem_filter.mpr ⟨hxG, hx_not_U, hxr⟩, hcxSet.symm⟩
  have habF : insert a (insert b C₀) ∈ F := by
    rw [hfamily, QStar.yFamily]
    apply Finset.mem_union_right
    rw [QStar.yInnerArm]
    apply Finset.mem_image.mpr
    exact ⟨c, Finset.mem_filter.mpr ⟨hcC1, hsc⟩, habSet.symm⟩
  have hc_not_ax : c ∉ insert a (insert x C₀) := by
    simp [hca.ne, (hca.trans (hab.trans hbx)).ne, hcC]
  have hb_not_ax : b ∉ insert a (insert x C₀) := by
    simp [hab.ne', hbx.ne, hbC]
  have hnotax : insert a (insert x C₀) ∉ F := by
    intro hmem
    rw [hfamily, QStar.yFamily] at hmem
    rcases Finset.mem_union.mp hmem with hcenterOrP | hQ
    · rcases Finset.mem_union.mp hcenterOrP with hcenter | hP
      · rcases Finset.mem_insert.mp hcenter with hEq | hEq
        · apply hc_not_ax
          rw [hEq, ← hcaSet]
          simp
        · have hEq' : insert a (insert x C₀) = QStar.secondInitialSegment G (d v) := by
            simpa using hEq
          apply hc_not_ax
          rw [hEq', ← hcbSet]
          simp
      · rw [QStar.yOuterArm] at hP
        obtain ⟨y, hy, hEq⟩ := Finset.mem_image.mp hP
        apply hc_not_ax
        rw [← hEq, hC1]
        simp
    · rw [QStar.yInnerArm] at hQ
      obtain ⟨i, hi, hEq⟩ := Finset.mem_image.mp hQ
      have hiC1 := (Finset.mem_filter.mp hi).1
      have hib : i ≠ b := fun h => hb_not_C1 (h ▸ hiC1)
      apply hb_not_ax
      rw [← hEq]
      exact Finset.mem_erase.mpr ⟨hib.symm, hbU⟩
  have G_lower : ∀ {y : V}, y ∈ G → ∀ {z : V}, z < y → z ∈ G := by
    intro y hyG z hzy
    change y ∈ F.biUnion id at hyG
    obtain ⟨S, hSF, hyS⟩ := Finset.mem_biUnion.mp hyG
    by_cases hzS : z ∈ S
    · change z ∈ F.biUnion id
      exact Finset.mem_biUnion.mpr ⟨S, hSF, hzS⟩
    · have hnew := hshift.2.2 S hSF z y hyS hzy hzS
      change z ∈ F.biUnion id
      exact Finset.mem_biUnion.mpr
        ⟨insert z (S.erase y), hnew, Finset.mem_insert_self z _⟩
  refine ⟨C₀, c, a, b, x, ?_⟩
  refine
    { pivot_not_mem := fun hvC => hvG (QStar.initialSegment_subset G (d v - 2) hvC)
      ne_pivot := ⟨hc_ne_v, ha_ne_v, hb_ne_v, hx_ne_v⟩
      not_mem := ⟨hcC, haC, hbC, hxC⟩
      distinct := ⟨hca.ne, (hca.trans hab).ne, (hca.trans (hab.trans hbx)).ne,
        hab.ne, (hab.trans hbx).ne, hbx.ne⟩
      card := by
        rw [show C₀.card = d v - 2 by
          exact QStar.card_initialSegment_of_le (by omega)]
        omega
      top_block := by
        intro u huC
        have huG := QStar.initialSegment_subset G (d v - 2) huC
        have huc : u < c := by
          rcases lt_trichotomy u c with hlt | heq | hgt
          · exact hlt
          · exact (hcC (heq ▸ huC)).elim
          · exact (hcC (QStar.initialSegment_lowerClosed u huC c hcG hgt)).elim
        exact hmono u c (ne_of_mem_of_not_mem huG hvG) hc_ne_v huc
      ordered := ⟨hmono b x hb_ne_v hx_ne_v hbx,
        hmono a b ha_ne_v hb_ne_v hab, hmono c a hc_ne_v ha_ne_v hca⟩
      tail := by
        intro u huv huC huc hua hub hux
        have hnot_lt : ¬ u < x := by
          intro hlt
          have huG := G_lower hxG hlt
          have huTop := QStar.initialSegment_lowerClosed x hxTop u huG hlt
          rw [hUx] at huTop
          simp [huC, huc, hua, hub, hux] at huTop
        have hxu : x < u := lt_of_le_of_ne (le_of_not_gt hnot_lt) hux.symm
        exact hmono x u hx_ne_v huv hxu
      corner_cx := mem_realizableNeighborhoods.mp hcxF
      corner_ab := mem_realizableNeighborhoods.mp habF
      not_corner_ax := fun hax => hnotax (mem_realizableNeighborhoods.mpr hax) }

/-- **Lemma 8.3d (lower-witness propagation).** Manuscript §8.2: if `F_D(t) < 0` for some `t ≤ k−2`,
then `F_D(k−1) < 0`. The proof takes the union of all tied top-`t` sets in a realization of `U`, uses
`TightUnion.egTight_biUnion` to jump directly to rank `k−1`, and crosses between the set and sorted
forms with `egTight_iff_erdosGallaiSlack_eq_zero_of_topFinset`. -/
theorem lemma_8_3d_lower_witness_propagation {d : V → ℕ} {v : V} {C₀ : Finset V} {c a b x : V}
    (hfc : FourCorner d v C₀ c a b x) {t : ℕ} (ht : t + 2 ≤ d v)
    (hneg : erdosGallaiSlack (fourCornerD d v C₀ a x) t < 0) :
    erdosGallaiSlack (fourCornerD d v C₀ a x) (d v - 1) < 0 := by
  classical
  let W := {u : V // u ≠ v}
  let D : W → ℕ := fourCornerD d v C₀ a x
  let U : W → ℕ := fourCornerU d v C₀ c x
  let R : W → ℕ := fourCornerV d v C₀ a b
  let cv : W := ⟨c, hfc.ne_pivot.1⟩
  let av : W := ⟨a, hfc.ne_pivot.2.1⟩
  let bv : W := ⟨b, hfc.ne_pivot.2.2.1⟩
  let xv : W := ⟨x, hfc.ne_pivot.2.2.2⟩
  change erdosGallaiSlack D t < 0 at hneg
  have hgaps := lemma_8_3a_strict_outer_gaps hfc
  have hp_lt_r : d a < d c := hgaps.1
  have hs_lt_q : d x < d b := hgaps.2
  have hq_le_p : d b ≤ d a := hfc.ordered.2.1
  have hbpos : 0 < d b := by omega
  have hk : C₀.card + 2 = d v := hfc.card
  have ht_le : t ≤ d v - 2 := by omega
  have ht_lt_km1 : t < d v - 1 := by omega
  have hUgraphical : Graphical U := by
    change Graphical (residualDegree d v (insert c (insert x C₀)))
    exact observation0_delete_direction hfc.corner_cx
  have hRgraphical : Graphical R := by
    change Graphical (residualDegree d v (insert a (insert b C₀)))
    exact observation0_delete_direction hfc.corner_ab
  obtain ⟨G₀, hG₀⟩ := hfc.corner_cx
  have hxpos : 0 < d x := by
    have hxN : x ∈ G₀.neighborFinset v := by simpa [hG₀]
    have hvN : v ∈ G₀.graph.neighborFinset x := by
      simpa [SimpleGraph.mem_neighborFinset] using
        ((G₀.mem_neighborFinset v x).mp hxN).symm
    rw [← G₀.degree_eq_apply x]
    change 0 < G₀.graph.degree x
    rw [← G₀.graph.card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨v, hvN⟩
  have hk_lt_cardV : d v < Fintype.card V := by
    rw [← G₀.degree_eq_apply v]
    exact G₀.graph.degree_lt_card_verts v
  have hWcard : Fintype.card W = Fintype.card V - 1 := by
    simp [W]
  have ht_cardW : t ≤ Fintype.card W := by
    rw [hWcard]
    omega
  have hU_nonneg : 0 ≤ erdosGallaiSlack U t :=
    erdosGallaiSlack_nonneg_of_graphical U hUgraphical t ht_cardW
  have hR_nonneg : 0 ≤ erdosGallaiSlack R t :=
    erdosGallaiSlack_nonneg_of_graphical R hRgraphical t ht_cardW
  have hDc : D cv = d c := by
    simp [D, cv, fourCornerD, residualDegree, hfc.distinct.1,
      hfc.distinct.2.2.1, hfc.not_mem.1]
  have hUc : U cv = d c - 1 := by
    simp [U, cv, fourCornerU, residualDegree]
  have hRc : R cv = d c := by
    simp [R, cv, fourCornerV, residualDegree, hfc.distinct.1,
      hfc.distinct.2.1, hfc.not_mem.1]
  have hDa : D av = d a - 1 := by
    simp [D, av, fourCornerD, residualDegree]
  have hUa : U av = d a := by
    simp [U, av, fourCornerU, residualDegree, hfc.distinct.1.symm,
      hfc.distinct.2.2.2.2.1, hfc.not_mem.2.1]
  have hRa : R av = d a - 1 := by
    simp [R, av, fourCornerV, residualDegree]
  have hDb : D bv = d b := by
    simp [D, bv, fourCornerD, residualDegree, hfc.distinct.2.2.2.1.symm,
      hfc.distinct.2.2.2.2.2, hfc.not_mem.2.2.1]
  have hUb : U bv = d b := by
    simp [U, bv, fourCornerU, residualDegree, hfc.distinct.2.1.symm,
      hfc.distinct.2.2.2.2.2, hfc.not_mem.2.2.1]
  have hRb : R bv = d b - 1 := by
    simp [R, bv, fourCornerV, residualDegree]
  have hDx : D xv = d x - 1 := by
    simp [D, xv, fourCornerD, residualDegree]
  have hUx : U xv = d x - 1 := by
    simp [U, xv, fourCornerU, residualDegree]
  have hRx : R xv = d x := by
    simp [R, xv, fourCornerV, residualDegree, hfc.distinct.2.2.2.2.1.symm,
      hfc.distinct.2.2.2.2.2.symm, hfc.not_mem.2.2.2]
  have block_card (K : Finset V) (hvK : v ∉ K) :
      (Finset.univ.val.filter (fun z : W ↦ z.val ∈ K)).card = K.card := by
    change (Finset.univ.filter (fun z : W ↦ z.val ∈ K)).card = K.card
    apply Finset.card_bij (fun z _ ↦ z.val)
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
    · intro z₁ _ z₂ _ heq
      exact Subtype.ext heq
    · intro z hz
      have hzv : z ≠ v := by
        intro heq
        subst z
        exact hvK hz
      refine ⟨⟨z, hzv⟩, ?_, rfl⟩
      simp [hz]
  have take_eq_of_common_high (f g : W → ℕ) (P : W → Prop) [DecidablePred P]
      (m j : ℕ) (hcard : (Finset.univ.val.filter P).card = m) (hjm : j ≤ m)
      (hcommon : ∀ z, P z → f z = g z)
      (hfhigh : ∀ z, P z → ∀ y, ¬ P y → f z ≥ f y)
      (hghigh : ∀ z, P z → ∀ y, ¬ P y → g z ≥ g y) :
      ((Finset.univ.val.map f).sort (· ≥ ·)).take j =
        ((Finset.univ.val.map g).sort (· ≥ ·)).take j := by
    let I : Multiset W := Finset.univ.val
    let If : Multiset W := I.filter P
    let Io : Multiset W := I.filter (fun z ↦ ¬ P z)
    let Af : Multiset ℕ := If.map f
    let Ag : Multiset ℕ := If.map g
    let Bf : Multiset ℕ := Io.map f
    let Bg : Multiset ℕ := Io.map g
    have hI : If + Io = I := Multiset.filter_add_not P I
    have hA : Af = Ag := by
      apply Multiset.map_congr rfl
      intro z hz
      exact hcommon z (Multiset.mem_filter.mp hz).2
    have hsortf : (Finset.univ.val.map f).sort (· ≥ ·) =
        Af.sort (· ≥ ·) ++ Bf.sort (· ≥ ·) := by
      change (I.map f).sort (· ≥ ·) = _
      rw [← hI, Multiset.map_add]
      apply sort_add_of_high Af Bf
      intro z hz y hy
      obtain ⟨z', hz', rfl⟩ := Multiset.mem_map.mp hz
      obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.mp hy
      exact hfhigh z' (Multiset.mem_filter.mp hz').2 y' (Multiset.mem_filter.mp hy').2
    have hsortg : (Finset.univ.val.map g).sort (· ≥ ·) =
        Ag.sort (· ≥ ·) ++ Bg.sort (· ≥ ·) := by
      change (I.map g).sort (· ≥ ·) = _
      rw [← hI, Multiset.map_add]
      apply sort_add_of_high Ag Bg
      intro z hz y hy
      obtain ⟨z', hz', rfl⟩ := Multiset.mem_map.mp hz
      obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.mp hy
      exact hghigh z' (Multiset.mem_filter.mp hz').2 y' (Multiset.mem_filter.mp hy').2
    have hlenf : j ≤ (Af.sort (· ≥ ·)).length := by
      simp [Af, If, I, hcard, hjm]
    have hleng : j ≤ (Ag.sort (· ≥ ·)).length := by
      simp [Ag, If, I, hcard, hjm]
    rw [hsortf, hsortg, List.take_append_of_le_length hlenf,
      List.take_append_of_le_length hleng, hA]
  have coe_sum (l : List ℕ) : (show List ℤ from l).sum = (l.sum : ℤ) := by
    induction l with
    | nil => rfl
    | cons z l ih =>
      change (z : ℤ) + (show List ℤ from l).sum = ((z + l.sum : ℕ) : ℤ)
      rw [ih, Nat.cast_add]
  have min_sum (l : List ℕ) (j : ℕ) :
      (l.map (fun z ↦ (min z j : ℤ))).sum = ((l.map (fun z ↦ min z j)).sum : ℤ) := by
    induction l with
    | nil => rfl
    | cons z l ih =>
      change (min z j : ℤ) + (l.map (fun y ↦ (min y j : ℤ))).sum =
        (((min z j) + (l.map (fun y ↦ min y j)).sum : ℕ) : ℤ)
      rw [ih, Nat.cast_add]
      norm_cast
  have total_min_eq (f : W → ℕ) (j : ℕ) :
      ((((Finset.univ.val.map f).sort (· ≥ ·)).map
          (fun z ↦ (min z j : ℤ))).sum) =
        ∑ z, (min (f z) j : ℤ) := by
    rw [min_sum]
    norm_cast
    change ((((Finset.univ.val.map f).sort (· ≥ ·)).map
      (fun z ↦ min z j)).sum) = (Finset.univ.val.map (fun z ↦ min (f z) j)).sum
    rw [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.sort_eq]
    simp [Multiset.map_map]
  have slack_total_form (f : W → ℕ) (j : ℕ) :
      erdosGallaiSlack f j =
        ((j : ℤ) * ((j : ℤ) - 1))
          + ∑ z, (min (f z) j : ℤ)
          - ((((Finset.univ.val.map f).sort (· ≥ ·)).take j).map
              (fun z ↦ (min z j : ℤ))).sum
          - ((((Finset.univ.val.map f).sort (· ≥ ·)).take j).map
              (fun z ↦ (z : ℤ))).sum := by
    let L := (Finset.univ.val.map f).sort (· ≥ ·)
    have hsplit :
        (L.map (fun z ↦ (min z j : ℤ))).sum =
          ((L.take j).map (fun z ↦ (min z j : ℤ))).sum +
            ((L.drop j).map (fun z ↦ (min z j : ℤ))).sum := by
      rw [min_sum, min_sum, min_sum]
      norm_cast
      rw [← List.sum_append, ← List.map_append, List.take_append_drop]
    unfold erdosGallaiSlack
    rw [← total_min_eq f j]
    change _ + ((L.drop j).map (fun z ↦ (min z j : ℤ))).sum -
      ((L.take j).map (fun z ↦ (z : ℤ))).sum = _
    rw [hsplit]
    ring
  have slack_eq_of_take_eq (f g : W → ℕ) (j : ℕ) (δ : ℤ)
      (htake : ((Finset.univ.val.map f).sort (· ≥ ·)).take j =
        ((Finset.univ.val.map g).sort (· ≥ ·)).take j)
      (htotal : (∑ z, (min (f z) j : ℤ)) = ∑ z, (min (g z) j : ℤ) + δ) :
      erdosGallaiSlack f j = erdosGallaiSlack g j + δ := by
    rw [slack_total_form f j, slack_total_form g j, htake, htotal]
    omega
  have take_sum_eq_of_threshold (f : W → ℕ) (h g j : ℕ)
      (hgtcard : (Finset.univ.val.filter (fun z ↦ h < f z)).card = g)
      (hgj : g ≤ j)
      (hgecard : j ≤ (Finset.univ.val.filter (fun z ↦ h ≤ f z)).card) :
      (((Finset.univ.val.map f).sort (· ≥ ·)).take j).sum =
        ((Finset.univ.val.filter (fun z ↦ h < f z)).map f).sum + (j - g) * h := by
    let I : Multiset W := Finset.univ.val
    let Ih : Multiset W := I.filter (fun z ↦ h < f z)
    let Ir : Multiset W := I.filter (fun z ↦ ¬ h < f z)
    let Ie : Multiset W := Ir.filter (fun z ↦ f z = h)
    let Il : Multiset W := Ir.filter (fun z ↦ f z ≠ h)
    let A : Multiset ℕ := Ih.map f
    let E : Multiset ℕ := Ie.map f
    let L : Multiset ℕ := Il.map f
    have hI : Ih + Ir = I := Multiset.filter_add_not (fun z ↦ h < f z) I
    have hIr : Ie + Il = Ir := Multiset.filter_add_not (fun z ↦ f z = h) Ir
    have hsortA : (I.map f).sort (· ≥ ·) =
        A.sort (· ≥ ·) ++ (Ir.map f).sort (· ≥ ·) := by
      rw [← hI, Multiset.map_add]
      apply sort_add_of_high A (Ir.map f)
      intro z hz y hy
      obtain ⟨z', hz', rfl⟩ := Multiset.mem_map.mp hz
      obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.mp hy
      have hzgt := (Multiset.mem_filter.mp hz').2
      have hyle := Nat.le_of_not_gt (Multiset.mem_filter.mp hy').2
      omega
    have hsortE : (Ir.map f).sort (· ≥ ·) =
        E.sort (· ≥ ·) ++ L.sort (· ≥ ·) := by
      rw [← hIr, Multiset.map_add]
      apply sort_add_of_high E L
      intro z hz y hy
      obtain ⟨z', hz', rfl⟩ := Multiset.mem_map.mp hz
      obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.mp hy
      have hzeq := (Multiset.mem_filter.mp hz').2
      have hyIr := (Multiset.mem_filter.mp (Multiset.mem_filter.mp hy').1).2
      have hyne := (Multiset.mem_filter.mp hy').2
      omega
    have hAlen : (A.sort (· ≥ ·)).length = g := by
      simp [A, Ih, I, hgtcard]
    have hGEcard :
        (Finset.univ.val.filter (fun z ↦ h ≤ f z)).card = Ih.card + Ie.card := by
      let GE : Multiset W := I.filter (fun z ↦ h ≤ f z)
      have hGE : GE = Ih + Ie := by
        ext z
        by_cases hzgt : h < f z
        · have hzge : h ≤ f z := hzgt.le
          simp [GE, Ih, Ie, Ir, hzgt, hzge]
        · have hzle : f z ≤ h := Nat.le_of_not_gt hzgt
          by_cases hzeq : f z = h
          · simp [GE, Ih, Ie, Ir, hzgt, hzeq]
          · have hzlt : f z < h := lt_of_le_of_ne hzle hzeq
            simp [GE, Ih, Ie, Ir, hzgt, hzeq, Nat.not_le_of_lt hzlt]
      change GE.card = Ih.card + Ie.card
      rw [hGE, Multiset.card_add]
    have hIecard : j - g ≤ Ie.card := by
      have hgcard : Ih.card = g := by simpa [Ih, I] using hgtcard
      rw [hGEcard] at hgecard
      omega
    have hElen : j - g ≤ (E.sort (· ≥ ·)).length := by
      simpa [E] using hIecard
    have hEsort : E.sort (· ≥ ·) = List.replicate E.card h := by
      apply List.eq_replicate_iff.mpr
      constructor
      · simp
      · intro y hy
        have hyE : y ∈ E := by simpa using hy
        obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hyE
        exact (Multiset.mem_filter.mp hz).2
    have htake : ((I.map f).sort (· ≥ ·)).take j =
        A.sort (· ≥ ·) ++ (E.sort (· ≥ ·)).take (j - g) := by
      rw [hsortA, hsortE, List.take_append, hAlen,
        List.take_of_length_le (by omega : (A.sort (· ≥ ·)).length ≤ j),
        List.take_append_of_le_length hElen]
    have hsubE : j - g ≤ E.card := by simpa [E] using hIecard
    change (((I.map f).sort (· ≥ ·)).take j).sum = A.sum + (j - g) * h
    rw [htake, List.sum_append, ← Multiset.sum_coe, Multiset.sort_eq, hEsort]
    simp only [List.take_replicate, List.sum_replicate]
    rw [min_eq_left hsubE]
    simp [nsmul_eq_mul]
  have top_min_sum_eq (f : W → ℕ) (j : ℕ)
      (hge : j ≤ (Finset.univ.val.filter (fun z ↦ j ≤ f z)).card) :
      (((((Finset.univ.val.map f).sort (· ≥ ·)).take j).map
          (fun z ↦ (min z j : ℤ))).sum) = (j : ℤ) * (j : ℤ) := by
    let cap : W → ℕ := fun z ↦ min (f z) j
    have hgtzero : (Finset.univ.val.filter (fun z ↦ j < cap z)).card = 0 := by
      apply Multiset.card_eq_zero.mpr
      ext z
      simp [cap]
    have hgecap : j ≤ (Finset.univ.val.filter (fun z ↦ j ≤ cap z)).card := by
      have heq : Finset.univ.val.filter (fun z ↦ j ≤ cap z) =
          Finset.univ.val.filter (fun z ↦ j ≤ f z) := by
        apply Multiset.filter_congr
        intro z hz
        simp [cap]
      rw [heq]
      exact hge
    have hcapsum := take_sum_eq_of_threshold cap j 0 j hgtzero (Nat.zero_le _) hgecap
    have hgtzero' : Finset.univ.val.filter (fun z ↦ j < cap z) = 0 :=
      Multiset.card_eq_zero.mp hgtzero
    simp [hgtzero'] at hcapsum
    have hsortcap : ((Finset.univ.val.map f).sort (· ≥ ·)).map
        (fun z ↦ min z j) = (Finset.univ.val.map cap).sort (· ≥ ·) := by
      apply List.Perm.eq_of_pairwise' (r := (· ≥ ·))
      · rw [List.pairwise_map]
        exact (Multiset.pairwise_sort (Finset.univ.val.map f) (· ≥ ·)).imp
          (fun hab ↦ by omega)
      · exact Multiset.pairwise_sort _ _
      · apply Multiset.coe_eq_coe.mp
        change ((↑((Finset.univ.val.map f).sort (· ≥ ·)) : Multiset ℕ).map
          (fun z ↦ min z j)) = ↑((Finset.univ.val.map cap).sort (· ≥ ·))
        rw [Multiset.sort_eq, Multiset.sort_eq]
        simp [cap, Multiset.map_map]
    rw [min_sum]
    norm_cast
    change (((((Finset.univ.val.map f).sort (· ≥ ·)).take j).map
      (fun z ↦ min z j)).sum) = j * j
    rw [List.map_take, hsortcap]
    simpa using hcapsum
  let H : Finset V := insert c C₀
  let P : W → Prop := fun z ↦ z.val ∈ H
  have hvH : v ∉ H := by
    simp [H, hfc.ne_pivot.1.symm, hfc.pivot_not_mem]
  have hHcard : H.card = d v - 1 := by
    have hcC : c ∉ C₀ := hfc.not_mem.1
    simp [H, hcC]
    omega
  have hPcard : (Finset.univ.val.filter P).card = d v - 1 := by
    rw [block_card H hvH, hHcard]
  have hDRcommonP : ∀ z, P z → D z = R z := by
    rintro ⟨z, hzv⟩ hz
    simp only [P, H, Finset.mem_insert] at hz
    rcases hz with rfl | hzC
    · rw [hDc, hRc]
    · simp [D, R, fourCornerD, fourCornerV, residualDegree, hzC]
  have hdegree_out (y : W) (hy : ¬ P y) : d y.val < d c := by
    have hyC : y.val ∉ C₀ := by
      intro h
      apply hy
      simp [P, H, h]
    have hyc : y.val ≠ c := by
      intro h
      apply hy
      simp [P, H, h]
    by_cases hya : y.val = a
    · simpa [hya] using hp_lt_r
    by_cases hyb : y.val = b
    · simpa [hyb] using hq_le_p.trans_lt hp_lt_r
    by_cases hyx : y.val = x
    · have : d x < d c := by omega
      simpa [hyx] using this
    have htail := hfc.tail y.val y.property hyC hyc hya hyb hyx
    omega
  have hDhighP : ∀ z, P z → ∀ y, ¬ P y → D z ≥ D y := by
    rintro ⟨z, hzv⟩ hz y hy
    have hDy : D y ≤ d y.val := by simp [D, fourCornerD, residualDegree]
    have hDy' : D y ≤ d c - 1 := by
      have := hdegree_out y hy
      omega
    simp only [P, H, Finset.mem_insert] at hz
    rcases hz with rfl | hzC
    · rw [hDc]
      omega
    · rw [show D ⟨z, hzv⟩ = d z - 1 by
        simp [D, fourCornerD, residualDegree, hzC]]
      exact hDy'.trans (Nat.sub_le_sub_right (hfc.top_block z hzC) 1)
  have hRhighP : ∀ z, P z → ∀ y, ¬ P y → R z ≥ R y := by
    rintro ⟨z, hzv⟩ hz y hy
    have hRy : R y ≤ d y.val := by simp [R, fourCornerV, residualDegree]
    have hRy' : R y ≤ d c - 1 := by
      have := hdegree_out y hy
      omega
    simp only [P, H, Finset.mem_insert] at hz
    rcases hz with rfl | hzC
    · rw [hRc]
      omega
    · rw [show R ⟨z, hzv⟩ = d z - 1 by
        simp [R, fourCornerV, residualDegree, hzC]]
      exact hRy'.trans (Nat.sub_le_sub_right (hfc.top_block z hzC) 1)
  have htakeDR : ((Finset.univ.val.map R).sort (· ≥ ·)).take t =
      ((Finset.univ.val.map D).sort (· ≥ ·)).take t := by
    apply take_eq_of_common_high R D P (d v - 1) t hPcard ht_lt_km1.le
    · intro z hz
      exact (hDRcommonP z hz).symm
    · exact hRhighP
    · exact hDhighP
  have hminB :
      min (D bv : ℤ) (t : ℤ) = min (R bv : ℤ) (t : ℤ)
        + (if d b ≤ t then 1 else 0) := by
    rw [hDb, hRb]
    norm_cast
    by_cases hb : d b ≤ t
    · have hb' : d b - 1 ≤ t := by omega
      simp [hb, hb']
      omega
    · have htq : t ≤ d b := by omega
      have htq' : t ≤ d b - 1 := by omega
      simp [hb, htq, htq']
  have hminX :
      min (R xv : ℤ) (t : ℤ) = min (D xv : ℤ) (t : ℤ)
        + (if d x ≤ t then 1 else 0) := by
    rw [hRx, hDx]
    norm_cast
    by_cases hx : d x ≤ t
    · have hx' : d x - 1 ≤ t := by omega
      simp [hx, hx']
      omega
    · have hts : t ≤ d x := by omega
      have hts' : t ≤ d x - 1 := by omega
      simp [hx, hts, hts']
  have htotalDR :
      (∑ z, min (R z : ℤ) (t : ℤ)) =
        (∑ z, min (D z : ℤ) (t : ℤ))
          - (if d b ≤ t then 1 else 0) + (if d x ≤ t then 1 else 0) := by
    let F : Finset W := Finset.univ
    have hbF : bv ∈ F := by simp [F]
    have hxF : xv ∈ F := by simp [F]
    have hbneX : bv ≠ xv := by
      intro heq
      exact hfc.distinct.2.2.2.2.2 (congr_arg Subtype.val heq)
    have hxE : xv ∈ F.erase bv := Finset.mem_erase.mpr ⟨hbneX.symm, hxF⟩
    change (∑ z ∈ F, min (R z : ℤ) (t : ℤ)) =
      (∑ z ∈ F, min (D z : ℤ) (t : ℤ))
        - (if d b ≤ t then 1 else 0) + (if d x ≤ t then 1 else 0)
    rw [← Finset.sum_erase_add F (fun z ↦ min (R z : ℤ) (t : ℤ)) hbF,
      ← Finset.sum_erase_add F (fun z ↦ min (D z : ℤ) (t : ℤ)) hbF,
      ← Finset.sum_erase_add (F.erase bv) (fun z ↦ min (R z : ℤ) (t : ℤ)) hxE,
      ← Finset.sum_erase_add (F.erase bv) (fun z ↦ min (D z : ℤ) (t : ℤ)) hxE]
    have hrest :
        (∑ z ∈ (F.erase bv).erase xv, min (R z : ℤ) (t : ℤ)) =
          ∑ z ∈ (F.erase bv).erase xv, min (D z : ℤ) (t : ℤ) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hzneb : z.val ≠ b := by
        intro heq
        have : z = bv := Subtype.ext heq
        subst z
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1 rfl
      have hznex : z.val ≠ x := by
        intro heq
        have : z = xv := Subtype.ext heq
        subst z
        exact (Finset.mem_erase.mp hz).1 rfl
      congr 1
      simp [D, R, fourCornerD, fourCornerV, residualDegree, hzneb, hznex]
    rw [hrest, hminB, hminX]
    omega
  have hslackRD : erdosGallaiSlack R t = erdosGallaiSlack D t
      - (if d b ≤ t then 1 else 0) + (if d x ≤ t then 1 else 0) := by
    have h := slack_eq_of_take_eq R D t
      (-(if d b ≤ t then 1 else 0) + (if d x ≤ t then 1 else 0)) htakeDR
    have htotal : (∑ z, min (R z : ℤ) (t : ℤ)) =
        (∑ z, min (D z : ℤ) (t : ℤ)) +
          (-(if d b ≤ t then 1 else 0) + (if d x ≤ t then 1 else 0)) := by
      rw [htotalDR]
      omega
    have := h htotal
    omega
  have hs_le_t : d x ≤ t := by
    by_cases hs : d x ≤ t
    · exact hs
    · simp [hs] at hslackRD
      by_cases hq : d b ≤ t
      · simp [hq] at hslackRD
        omega
      · simp [hq] at hslackRD
        omega
  have ht_lt_q : t < d b := by
    by_contra hnot
    have hq : d b ≤ t := Nat.le_of_not_gt hnot
    simp [hs_le_t, hq] at hslackRD
    omega
  have hD_eq_neg_one : erdosGallaiSlack D t = -1 := by
    simp [hs_le_t, Nat.not_le_of_lt ht_lt_q] at hslackRD
    omega
  have hR_eq_zero : erdosGallaiSlack R t = 0 := by
    simp [hs_le_t, Nat.not_le_of_lt ht_lt_q] at hslackRD
    omega
  have hDU_of_ne (z : W) (hzc : z.val ≠ c) (hza : z.val ≠ a) : D z = U z := by
    simp [D, U, fourCornerD, fourCornerU, residualDegree, hzc, hza]
  have htotalDU :
      (∑ z, min (U z : ℤ) (t : ℤ)) = ∑ z, min (D z : ℤ) (t : ℤ) := by
    change (∑ z ∈ (Finset.univ : Finset W), min (U z : ℤ) (t : ℤ)) =
      ∑ z ∈ (Finset.univ : Finset W), min (D z : ℤ) (t : ℤ)
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hzc : z.val = c
    · have : z = cv := Subtype.ext hzc
      subst z
      rw [hUc, hDc]
      norm_cast
      omega
    by_cases hza : z.val = a
    · have : z = av := Subtype.ext hza
      subst z
      rw [hUa, hDa]
      norm_cast
      omega
    rw [hDU_of_ne z hzc hza]
  let Q : W → Prop := fun z ↦ d c - 1 < U z
  let g : ℕ := (Finset.univ.val.filter Q).card
  have hQcard : (Finset.univ.val.filter Q).card = g := rfl
  have hQcommon : ∀ z, Q z → D z = U z := by
    intro z hz
    have hzc : z.val ≠ c := by
      intro heq
      have : z = cv := Subtype.ext heq
      subst z
      simp [Q, hUc] at hz
    have hza : z.val ≠ a := by
      intro heq
      have : z = av := Subtype.ext heq
      subst z
      simp [Q, hUa] at hz
      omega
    exact hDU_of_ne z hzc hza
  have hQhighU : ∀ z, Q z → ∀ y, ¬ Q y → U z ≥ U y := by
    intro z hz y hy
    simp only [Q] at hz hy
    omega
  have hQhighD : ∀ z, Q z → ∀ y, ¬ Q y → D z ≥ D y := by
    intro z hz y hy
    have hzD := hQcommon z hz
    have hzgt : d c - 1 < D z := by rwa [hzD]
    by_cases hyc : y.val = c
    · have : y = cv := Subtype.ext hyc
      subst y
      rw [hDc]
      omega
    by_cases hya : y.val = a
    · have : y = av := Subtype.ext hya
      subst y
      rw [hDa]
      omega
    have hyDU := hDU_of_ne y hyc hya
    simp only [Q] at hy
    rw [hyDU]
    omega
  have hg_lt_t : g < t := by
    by_contra hnot
    have htg : t ≤ g := Nat.le_of_not_gt hnot
    have htakeQU : ((Finset.univ.val.map U).sort (· ≥ ·)).take t =
        ((Finset.univ.val.map D).sort (· ≥ ·)).take t := by
      exact take_eq_of_common_high U D Q g t hQcard htg
        (fun z hz ↦ (hQcommon z hz).symm) hQhighU hQhighD
    have hslack := slack_eq_of_take_eq U D t 0 htakeQU (by
      rw [htotalDU]
      omega)
    omega
  have hP_ge_D : ∀ z, P z → d c - 1 ≤ D z := by
    rintro ⟨z, hzv⟩ hz
    simp only [P, H, Finset.mem_insert] at hz
    rcases hz with rfl | hzC
    · rw [hDc]
      omega
    · simp [D, fourCornerD, residualDegree, hzC]
      have htop := hfc.top_block z hzC
      omega
  have hP_ge_U : ∀ z, P z → d c - 1 ≤ U z := by
    rintro ⟨z, hzv⟩ hz
    simp only [P, H, Finset.mem_insert] at hz
    rcases hz with rfl | hzC
    · rw [hUc]
    · simp [U, fourCornerU, residualDegree, hzC]
      have htop := hfc.top_block z hzC
      omega
  have hgeD : t ≤ (Finset.univ.val.filter (fun z ↦ d c - 1 ≤ D z)).card := by
    have hsub : (Finset.univ.filter P) ⊆
        Finset.univ.filter (fun z ↦ d c - 1 ≤ D z) := by
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact hP_ge_D z hz
    have hcardle := Finset.card_le_card hsub
    change t ≤ (Finset.univ.filter (fun z ↦ d c - 1 ≤ D z)).card
    have hPcard' : (Finset.univ.filter P).card = d v - 1 := hPcard
    omega
  have hgeU : t ≤ (Finset.univ.val.filter (fun z ↦ d c - 1 ≤ U z)).card := by
    have hsub : (Finset.univ.filter P) ⊆
        Finset.univ.filter (fun z ↦ d c - 1 ≤ U z) := by
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact hP_ge_U z hz
    have hcardle := Finset.card_le_card hsub
    change t ≤ (Finset.univ.filter (fun z ↦ d c - 1 ≤ U z)).card
    have hPcard' : (Finset.univ.filter P).card = d v - 1 := hPcard
    omega
  let HU : Finset W := Finset.univ.filter Q
  let HD : Finset W := Finset.univ.filter (fun z ↦ d c - 1 < D z)
  have hcv_not_HU : cv ∉ HU := by
    simp [HU, Q, hUc]
  have hHD_eq : HD = insert cv HU := by
    ext z
    simp only [HD, HU, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    by_cases hzc : z.val = c
    · have hzcv : z = cv := Subtype.ext hzc
      subst z
      simp [hDc]
      omega
    by_cases hza : z.val = a
    · have hzav : z = av := Subtype.ext hza
      subst z
      have havnecv : av ≠ cv := by
        intro heq
        exact hfc.distinct.1.symm (congr_arg Subtype.val heq)
      simp [havnecv, Q, hDa, hUa]
      omega
    have hznecv : z ≠ cv := by
      intro heq
      exact hzc (congr_arg Subtype.val heq)
    simp only [hznecv, false_or]
    rw [hDU_of_ne z hzc hza]
  have hHDcard : HD.card = g + 1 := by
    have hHUcard : HU.card = g := by
      change (Finset.univ.filter Q).card = g
      exact hQcard
    rw [hHD_eq, Finset.card_insert_of_notMem hcv_not_HU, hHUcard]
  have hhighsum : (∑ z ∈ HD, D z) = (∑ z ∈ HU, U z) + d c := by
    rw [hHD_eq, Finset.sum_insert hcv_not_HU, hDc]
    have hsum : (∑ z ∈ HU, D z) = ∑ z ∈ HU, U z := by
      apply Finset.sum_congr rfl
      intro z hz
      apply hQcommon z
      exact (Finset.mem_filter.mp hz).2
    rw [hsum]
    omega
  have htopU := take_sum_eq_of_threshold U (d c - 1) g t hQcard hg_lt_t.le hgeU
  have htopD := take_sum_eq_of_threshold D (d c - 1) (g + 1) t (by
      change HD.card = g + 1
      exact hHDcard) (by omega) hgeD
  have htopDU : (((Finset.univ.val.map D).sort (· ≥ ·)).take t).sum =
      (((Finset.univ.val.map U).sort (· ≥ ·)).take t).sum + 1 := by
    have hsub : t - g = (t - (g + 1)) + 1 := by omega
    rw [hsub, Nat.add_mul, one_mul] at htopU
    change _ = (∑ z ∈ HU, U z) + _ at htopU
    change _ = (∑ z ∈ HD, D z) + _ at htopD
    rw [hhighsum] at htopD
    omega
  have hgeDt : t ≤ (Finset.univ.val.filter (fun z ↦ t ≤ D z)).card := by
    have hsub : (Finset.univ.filter (fun z ↦ d c - 1 ≤ D z)) ⊆
        Finset.univ.filter (fun z ↦ t ≤ D z) := by
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      omega
    have hcardle := Finset.card_le_card hsub
    change t ≤ (Finset.univ.filter (fun z ↦ t ≤ D z)).card
    have hgeD' : t ≤ (Finset.univ.filter (fun z ↦ d c - 1 ≤ D z)).card := hgeD
    exact hgeD'.trans hcardle
  have hgeUt : t ≤ (Finset.univ.val.filter (fun z ↦ t ≤ U z)).card := by
    have hsub : (Finset.univ.filter (fun z ↦ d c - 1 ≤ U z)) ⊆
        Finset.univ.filter (fun z ↦ t ≤ U z) := by
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      omega
    have hcardle := Finset.card_le_card hsub
    change t ≤ (Finset.univ.filter (fun z ↦ t ≤ U z)).card
    have hgeU' : t ≤ (Finset.univ.filter (fun z ↦ d c - 1 ≤ U z)).card := hgeU
    exact hgeU'.trans hcardle
  have htopminD := top_min_sum_eq D t hgeDt
  have htopminU := top_min_sum_eq U t hgeUt
  have htopDUZ :
      (((((Finset.univ.val.map D).sort (· ≥ ·)).take t).map
          (fun z ↦ (z : ℤ))).sum) =
        (((((Finset.univ.val.map U).sort (· ≥ ·)).take t).map
          (fun z ↦ (z : ℤ))).sum) + 1 := by
    simp only [List.map_id_fun', id_eq]
    rw [coe_sum, coe_sum]
    exact_mod_cast htopDU
  have hslackUD : erdosGallaiSlack U t = erdosGallaiSlack D t + 1 := by
    rw [slack_total_form U t, slack_total_form D t, htopminU, htopminD, htotalDU,
      htopDUZ]
    omega
  have hU_eq_zero : erdosGallaiSlack U t = 0 := by omega
  let GU : Realization U := realizationOfGraphical hUgraphical
  let HW : Finset W := Finset.univ.filter P
  have hHWcard : HW.card = d v - 1 := by
    change (Finset.univ.val.filter P).card = d v - 1
    exact hPcard
  have hHUcard : HU.card = g := by
    change (Finset.univ.val.filter Q).card = g
    exact hQcard
  have hHUsub : HU ⊆ HW := by
    intro z hz
    have hzQ : Q z := by simpa [HU] using hz
    have hzP : P z := by
      by_contra hnotP
      have hUz : U z ≤ d z.val := by simp [U, fourCornerU, residualDegree]
      have hzdeg := hdegree_out z hnotP
      simp only [Q] at hzQ
      omega
    simp [HW, hzP]
  let E : Finset W := HW \ HU
  have hEcard : E.card = (d v - 1) - g := by
    simp only [E]
    rw [Finset.card_sdiff_of_subset hHUsub, hHWcard, hHUcard]
  have hchoose_pos : 0 < t - g := by omega
  have hchoose_le : t - g ≤ E.card := by
    rw [hEcard]
    omega
  let 𝒯 : Finset (Finset W) :=
    (E.powersetCard (t - g)).image (fun J ↦ HU ∪ J)
  have h𝒯ne : 𝒯.Nonempty := by
    obtain ⟨J, hJsub, hJcard⟩ := Finset.exists_subset_card_eq hchoose_le
    refine ⟨HU ∪ J, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨J, Finset.mem_powersetCard.mpr ⟨hJsub, hJcard⟩, rfl⟩
  have h𝒯card : ∀ T ∈ 𝒯, T.card = t := by
    intro T hT
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hT
    have hJdata := Finset.mem_powersetCard.mp hJ
    have hdisj : Disjoint HU J := Finset.disjoint_left.mpr (by
      intro z hzHU hzJ
      exact (Finset.mem_sdiff.mp (hJdata.1 hzJ)).2 hzHU)
    rw [Finset.card_union_of_disjoint hdisj, hHUcard, hJdata.2]
    omega
  have h𝒯top : ∀ T ∈ 𝒯, ∀ z ∈ T, ∀ y ∈ Tᶜ, U z ≥ U y := by
    intro T hT
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hT
    have hJsub := (Finset.mem_powersetCard.mp hJ).1
    intro z hz y hy
    have hzge : d c - 1 ≤ U z := by
      rcases Finset.mem_union.mp hz with hzHU | hzJ
      · have hzQ : Q z := by simpa [HU] using hzHU
        simp only [Q] at hzQ
        omega
      · have hzE := hJsub hzJ
        have hzHW := (Finset.mem_sdiff.mp hzE).1
        exact hP_ge_U z ((Finset.mem_filter.mp hzHW).2)
    have hyHU : y ∉ HU := by
      intro hyHU
      exact (Finset.mem_compl.mp hy) (Finset.mem_union_left J hyHU)
    have hyQ : ¬ Q y := by simpa [HU] using hyHU
    simp only [Q] at hyQ
    omega
  have h𝒯tight : ∀ T ∈ 𝒯, TightUnion.EGTight GU.graph T := by
    intro T hT
    have htopGraph : ∀ z ∈ T, ∀ y ∈ Tᶜ, GU.graph.degree z ≥ GU.graph.degree y := by
      simpa only [GU.degree_eq] using h𝒯top T hT
    have hzero : erdosGallaiSlack (fun z ↦ GU.graph.degree z) t = 0 := by
      simpa only [GU.degree_eq] using hU_eq_zero
    exact (egTight_iff_erdosGallaiSlack_eq_zero_of_topFinset GU.graph (by omega)
      (h𝒯card T hT) htopGraph).mpr hzero
  have h𝒯union : 𝒯.biUnion id = HW := by
    apply Finset.Subset.antisymm
    · intro z hz
      obtain ⟨T, hT, hzT⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hT
      rcases Finset.mem_union.mp hzT with hzHU | hzJ
      · exact hHUsub hzHU
      · exact (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp hJ).1 hzJ)).1
    · intro z hzHW
      by_cases hzHU : z ∈ HU
      · obtain ⟨T, hT⟩ := h𝒯ne
        refine Finset.mem_biUnion.mpr ⟨T, hT, ?_⟩
        obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hT
        exact Finset.mem_union_left J hzHU
      · have hzE : z ∈ E := Finset.mem_sdiff.mpr ⟨hzHW, hzHU⟩
        have hzAll : z ∈ (E.powersetCard (t - g)).biUnion id := by
          rw [Finset.powersetCard_biUnion (by omega) hchoose_le]
          exact hzE
        obtain ⟨J, hJ, hzJ⟩ := Finset.mem_biUnion.mp hzAll
        refine Finset.mem_biUnion.mpr ⟨HU ∪ J, ?_, Finset.mem_union_right HU hzJ⟩
        exact Finset.mem_image.mpr ⟨J, hJ, rfl⟩
  have h𝒯deg : ∀ z ∈ 𝒯.biUnion id, t ≤ GU.graph.degree z := by
    intro z hz
    have hzHW : z ∈ HW := by rwa [h𝒯union] at hz
    rw [GU.degree_eq]
    have hzge := hP_ge_U z (Finset.mem_filter.mp hzHW).2
    omega
  have hHWtight : TightUnion.EGTight GU.graph HW := by
    rw [← h𝒯union]
    exact TightUnion.egTight_biUnion GU.graph h𝒯ne h𝒯card h𝒯tight h𝒯deg
  have hHWtop : ∀ z ∈ HW, ∀ y ∈ HWᶜ,
      GU.graph.degree z ≥ GU.graph.degree y := by
    intro z hz y hy
    rw [GU.degree_eq, GU.degree_eq]
    have hzge := hP_ge_U z (Finset.mem_filter.mp hz).2
    have hyP : ¬ P y := by
      intro hyP
      exact (Finset.mem_compl.mp hy) (by simp [HW, hyP])
    have hydeg := hdegree_out y hyP
    have hUy : U y ≤ d y.val := by simp [U, fourCornerU, residualDegree]
    omega
  have hUmzeroRaw : erdosGallaiSlack (fun z ↦ GU.graph.degree z) (d v - 1) = 0 :=
    (egTight_iff_erdosGallaiSlack_eq_zero_of_topFinset GU.graph (by omega)
      hHWcard hHWtop).mp hHWtight
  have hUmzero : erdosGallaiSlack U (d v - 1) = 0 := by
    simpa only [GU.degree_eq] using hUmzeroRaw
  have hslackU := (lemma_8_3b_slack_identities hfc).1
  change erdosGallaiSlack U (d v - 1) = erdosGallaiSlack D (d v - 1)
    + 1 + (if d a ≤ d v - 1 then 1 else 0) at hslackU
  change erdosGallaiSlack D (d v - 1) < 0
  omega

/-- **Lemma 8.3e (one-sided bound).** Manuscript §8.2: `q ≥ k`. -/
theorem lemma_8_3e_one_sided_bound {d : V → ℕ} {v : V} {C₀ : Finset V} {c a b x : V}
    (hfc : FourCorner d v C₀ c a b x) :
    d v ≤ d b := by
  classical
  let W := {u : V // u ≠ v}
  let D : W → ℕ := fourCornerD d v C₀ a x
  let U : W → ℕ := fourCornerU d v C₀ c x
  let R : W → ℕ := fourCornerV d v C₀ a b
  let t := d v - 1
  have hk : 2 ≤ d v := by rw [← hfc.card]; omega
  have hUgraphical : Graphical U := by
    change Graphical (residualDegree d v (insert c (insert x C₀)))
    exact observation0_delete_direction hfc.corner_cx
  have hRgraphical : Graphical R := by
    change Graphical (residualDegree d v (insert a (insert b C₀)))
    exact observation0_delete_direction hfc.corner_ab
  obtain ⟨G₀, hG₀⟩ := hfc.corner_cx
  have hk_lt_cardV : d v < Fintype.card V := by
    rw [← G₀.degree_eq_apply v]
    exact G₀.graph.degree_lt_card_verts v
  have hWcard : Fintype.card W = Fintype.card V - 1 := by
    simp [W]
  have ht_cardW : t ≤ Fintype.card W := by
    rw [hWcard]
    dsimp [t]
    omega
  have hU_nonneg : 0 ≤ erdosGallaiSlack U t :=
    erdosGallaiSlack_nonneg_of_graphical U hUgraphical t ht_cardW
  have hR_nonneg : 0 ≤ erdosGallaiSlack R t :=
    erdosGallaiSlack_nonneg_of_graphical R hRgraphical t ht_cardW
  have hslack0 := lemma_8_3b_slack_identities hfc
  have hslackU := hslack0.1
  have hslackR := hslack0.2
  change erdosGallaiSlack U t = erdosGallaiSlack D t + 1
      + (if d a ≤ t then 1 else 0) at hslackU
  change erdosGallaiSlack R t = erdosGallaiSlack D t
      - (if d b ≤ t then 1 else 0) + (if d x ≤ t then 1 else 0) at hslackR
  by_cases hsigma : erdosGallaiSlack D t < 0
  · have hp : d v ≤ d a := by
      by_contra hnot
      have hpa : d a ≤ t := by
        dsimp [t]
        omega
      have hqb : d b ≤ t := hfc.ordered.2.1.trans hpa
      have hsx : d x ≤ t := hfc.ordered.1.trans hqb
      rw [if_pos hqb, if_pos hsx] at hslackR
      omega
    have hpa : ¬d a ≤ t := by
      dsimp [t]
      omega
    rw [if_neg hpa] at hslackU
    have hsigma_eq : erdosGallaiSlack D t = -1 := by omega
    by_contra hnot
    have hqb : d b ≤ t := by
      dsimp [t]
      omega
    have hsx : d x ≤ t := hfc.ordered.1.trans hqb
    rw [if_pos hqb, if_pos hsx, hsigma_eq] at hslackR
    omega
  · have hsigma_nonneg : 0 ≤ erdosGallaiSlack D t := le_of_not_gt hsigma
    have hk_cardW : d v ≤ Fintype.card W := by
      rw [hWcard]
      omega
    have hneg_exists : ∃ j : ℕ, j ≤ Fintype.card W ∧ erdosGallaiSlack D j < 0 := by
      have hDpos : ∀ u ∈ insert a (insert x C₀), 0 < d u := by
        intro u hu
        rcases Finset.mem_insert.mp hu with hua | hu
        · subst u
          exact pos_degree_of_mem_realizable hfc.corner_ab (by simp)
        rcases Finset.mem_insert.mp hu with hux | huC
        · subst u
          exact pos_degree_of_mem_realizable hfc.corner_cx (by simp)
        · exact pos_degree_of_mem_realizable hfc.corner_ab (by simp [huC])
      have hUpos : ∀ u ∈ insert c (insert x C₀), 0 < d u := by
        intro u hu
        exact pos_degree_of_mem_realizable hfc.corner_cx hu
      have hvD : v ∉ insert a (insert x C₀) := by
        simp [hfc.ne_pivot.2.1.symm, hfc.ne_pivot.2.2.2.symm, hfc.pivot_not_mem]
      have hvU : v ∉ insert c (insert x C₀) := by
        simp [hfc.ne_pivot.1.symm, hfc.ne_pivot.2.2.2.symm, hfc.pivot_not_mem]
      have hDcard : (insert a (insert x C₀)).card = d v := by
        simpa [hfc.not_mem.2.1, hfc.not_mem.2.2.2,
          hfc.distinct.2.2.2.2.1] using hfc.card
      have hUcard : (insert c (insert x C₀)).card = d v := by
        simpa [hfc.not_mem.1, hfc.not_mem.2.2.2,
          hfc.distinct.2.2.1] using hfc.card
      have hDnot : ¬ Graphical D := by
        intro hDgraphical
        apply hfc.not_corner_ax
        apply observation0_add_direction hvD hDcard hDpos
        exact hDgraphical
      have residual_sum_eq (S : Finset V) (hvS : v ∉ S) (hcard : S.card = d v)
          (hpos : ∀ u ∈ S, 0 < d u) :
          (∑ z : W, residualDegree d v S z) = (∑ z : W, d z.val) - d v := by
        have hindicator : (∑ z : W, if z.val ∈ S then 1 else 0) = S.card := by
          rw [Finset.sum_boole]
          apply Finset.card_bij (fun z _ ↦ z.val)
          · intro z hz
            exact (Finset.mem_filter.mp hz).2
          · intro z₁ _ z₂ _ heq
            exact Subtype.ext heq
          · intro z hz
            have hzv : z ≠ v := by
              intro hzv
              subst z
              exact hvS hz
            refine ⟨⟨z, hzv⟩, ?_, rfl⟩
            simp [hz]
        have hpoint (z : W) :
            residualDegree d v S z + (if z.val ∈ S then 1 else 0) = d z.val := by
          by_cases hz : z.val ∈ S
          · simp only [residualDegree, if_pos hz]
            exact Nat.sub_add_cancel (hpos z.val hz)
          · simp [residualDegree, hz]
        apply Nat.eq_sub_of_add_eq
        rw [← hcard, ← hindicator, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun z _ ↦ hpoint z)
      have hDsum : (∑ z : W, D z) = (∑ z : W, d z.val) - d v := by
        change (∑ z : W, residualDegree d v (insert a (insert x C₀)) z) = _
        exact residual_sum_eq (insert a (insert x C₀)) hvD hDcard hDpos
      have hUsum : (∑ z : W, U z) = (∑ z : W, d z.val) - d v := by
        change (∑ z : W, residualDegree d v (insert c (insert x C₀)) z) = _
        exact residual_sum_eq (insert c (insert x C₀)) hvU hUcard hUpos
      have hUeven : Even (∑ z : W, U z) := by
        let G : Realization U := realizationOfGraphical hUgraphical
        rw [even_iff_exists_two_mul]
        refine ⟨G.graph.edgeFinset.card, ?_⟩
        have hsum := G.graph.sum_degrees_eq_twice_card_edges
        simpa only [G.degree_eq] using hsum
      have hDeven : Even (∑ z : W, D z) := by
        rw [hDsum, ← hUsum]
        exact hUeven
      exact exists_neg_slack_of_not_graphical D hDeven hDnot
    obtain ⟨j, hjcard, hjneg⟩ := hneg_exists
    have hj_not_high : ¬d v + 1 ≤ j := by
      intro hj
      have hagree := (lemma_8_3c_agreement_above_pivot hfc).1 j hj
      change erdosGallaiSlack D j = erdosGallaiSlack U j at hagree
      have hUj := erdosGallaiSlack_nonneg_of_graphical U hUgraphical j hjcard
      omega
    have hj_not_low : ¬j + 2 ≤ d v := by
      intro hj
      have hprop := lemma_8_3d_lower_witness_propagation hfc hj
      change erdosGallaiSlack D j < 0 → erdosGallaiSlack D t < 0 at hprop
      exact hsigma (hprop hjneg)
    have hj_not_t : j ≠ t := by
      intro hj
      subst j
      omega
    have hj_eq : j = d v := by
      dsimp [t] at hj_not_t
      omega
    have hDk_neg : erdosGallaiSlack D (d v) < 0 := by
      rw [← hj_eq]
      exact hjneg
    have hpq : d a = d b := by
      by_contra hpq
      have hqp : d b < d a := lt_of_le_of_ne hfc.ordered.2.1 (Ne.symm hpq)
      have hagree := (lemma_8_3c_agreement_above_pivot hfc).2 hqp
      change erdosGallaiSlack D (d v) = erdosGallaiSlack U (d v) at hagree
      have hUk := erdosGallaiSlack_nonneg_of_graphical U hUgraphical (d v) hk_cardW
      omega
    by_contra hnot
    have hp_le_t : d a ≤ t := by
      dsimp [t]
      rw [hpq]
      omega
    let cv : W := ⟨c, hfc.ne_pivot.1⟩
    let av : W := ⟨a, hfc.ne_pivot.2.1⟩
    let bv : W := ⟨b, hfc.ne_pivot.2.2.1⟩
    let xv : W := ⟨x, hfc.ne_pivot.2.2.2⟩
    have hDb : D bv = d b := by
      simp [D, bv, fourCornerD, residualDegree, hfc.distinct.2.2.2.1.symm,
        hfc.distinct.2.2.2.2.2, hfc.not_mem.2.2.1]
    have block_card (K : Finset V) (hvK : v ∉ K) :
        (Finset.univ.filter (fun z : W ↦ z.val ∈ K)).card = K.card := by
      apply Finset.card_bij (fun z _ ↦ z.val)
      · intro z hz
        exact (Finset.mem_filter.mp hz).2
      · intro z₁ _ z₂ _ heq
        exact Subtype.ext heq
      · intro z hz
        have hzv : z ≠ v := by
          intro hzv
          subst z
          exact hvK hz
        refine ⟨⟨z, hzv⟩, ?_, rfl⟩
        simp [hz]
    have topBlock_data (K : Finset W) (m : ℕ) (hKcard : K.card = m)
        (hKhigh : ∀ z ∈ K, ∀ y ∈ Kᶜ, D y ≤ D z) :
        K.val.map D = ((Finset.univ.val.map D).sort (· ≥ ·)).take m ∧
          Kᶜ.val.map D = ((Finset.univ.val.map D).sort (· ≥ ·)).drop m := by
      let A : Multiset ℕ := K.val.map D
      let B : Multiset ℕ := Kᶜ.val.map D
      have hpartition : K.val + Kᶜ.val = (Finset.univ : Finset W).val := by
        ext z
        rw [Multiset.count_add]
        by_cases hz : z ∈ K
        · rw [Multiset.count_eq_one_of_mem K.nodup hz,
            Multiset.count_eq_zero_of_notMem (by simpa using hz),
            Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ z)]
        · rw [Multiset.count_eq_zero_of_notMem hz,
            Multiset.count_eq_one_of_mem Kᶜ.nodup (by simpa using hz),
            Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ z)]
      have hsort : ((Finset.univ.val.map D).sort (· ≥ ·)) =
          A.sort (· ≥ ·) ++ B.sort (· ≥ ·) := by
        rw [← hpartition, Multiset.map_add]
        change ((A + B).sort (· ≥ ·)) = _
        apply sort_add_of_high A B
        intro z hz y hy
        obtain ⟨z', hz', rfl⟩ := Multiset.mem_map.mp hz
        obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.mp hy
        exact hKhigh z' hz' y' hy'
      have hAlength : (A.sort (· ≥ ·)).length = m := by simp [A, hKcard]
      constructor
      · rw [hsort, ← hAlength, List.take_left]
        exact (Multiset.sort_eq A (· ≥ ·)).symm
      · rw [hsort, ← hAlength, List.drop_left]
        exact (Multiset.sort_eq B (· ≥ ·)).symm
    let Tm : Finset W := Finset.univ.filter (fun z : W ↦ z.val ∈ insert c C₀)
    let Tk : Finset W := Finset.univ.filter (fun z : W ↦ z.val ∈ insert b (insert c C₀))
    have hvTm : v ∉ insert c C₀ := by
      simp [hfc.ne_pivot.1.symm, hfc.pivot_not_mem]
    have hvTk : v ∉ insert b (insert c C₀) := by
      simp [hfc.ne_pivot.1.symm, hfc.ne_pivot.2.2.1.symm, hfc.pivot_not_mem]
    have hTmcard : Tm.card = t := by
      rw [show Tm.card = (insert c C₀).card by
        exact block_card (insert c C₀) hvTm]
      simp [hfc.not_mem.1]
      dsimp [t]
      have := hfc.card
      omega
    have hTkcard : Tk.card = d v := by
      rw [show Tk.card = (insert b (insert c C₀)).card by
        exact block_card (insert b (insert c C₀)) hvTk]
      simp [hfc.not_mem.1, hfc.not_mem.2.2.1, hfc.distinct.2.1.symm]
      have := hfc.card
      omega
    have hTk : Tk = insert bv Tm := by
      ext z
      simp only [Tk, Tm, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert]
      constructor
      · rintro (hzb | hzc | hzC)
        · exact Or.inl (Subtype.ext hzb)
        · exact Or.inr (Or.inl hzc)
        · exact Or.inr (Or.inr hzC)
      · rintro (hzb | hzc | hzC)
        · exact Or.inl (congrArg Subtype.val hzb)
        · exact Or.inr (Or.inl hzc)
        · exact Or.inr (Or.inr hzC)
    have hbTm : bv ∉ Tm := by
      simp [Tm, bv, hfc.distinct.2.1.symm, hfc.not_mem.2.2.1]
    have hTmcomp : Tmᶜ = insert bv Tkᶜ := by
      ext z
      rw [hTk]
      by_cases hzb : z = bv
      · subst z
        simp [hbTm]
      · simp [hzb]
    have hD_le_p (z : W) (hz : z ∈ Tkᶜ) : D z ≤ d a - 1 := by
      have hzTk : z.val ∉ insert b (insert c C₀) := by
        simpa [Tk] using hz
      have hzb : z.val ≠ b := by
        intro h
        exact hzTk (by simp [h])
      have hzc : z.val ≠ c := by
        intro h
        exact hzTk (by simp [h])
      have hzC : z.val ∉ C₀ := by
        intro h
        exact hzTk (by simp [h])
      by_cases hza : z.val = a
      · have : z = av := Subtype.ext hza
        subst z
        simp [D, av, fourCornerD, residualDegree]
      · by_cases hzx : z.val = x
        · have : z = xv := Subtype.ext hzx
          subst z
          simp [D, xv, fourCornerD, residualDegree]
          have hsx := (lemma_8_3a_strict_outer_gaps hfc).2
          rw [← hpq] at hsx
          omega
        · have htail := hfc.tail z.val z.property hzC hzc hza hzb hzx
          have hsx := (lemma_8_3a_strict_outer_gaps hfc).2
          rw [← hpq] at hsx
          have hDz : D z = d z.val := by
            simp [D, fourCornerD, residualDegree, hzC, hza, hzx]
          rw [hDz]
          omega
    have hTmhigh : ∀ z ∈ Tm, ∀ y ∈ Tmᶜ, D y ≤ D z := by
      intro z hz y hy
      have hzmem : z.val ∈ insert c C₀ := by simpa [Tm] using hz
      have hycases : y = bv ∨ y ∈ Tkᶜ := by simpa [hTmcomp] using hy
      have hDyle : D y ≤ d a := by
        rcases hycases with rfl | hyTk
        · rw [hDb, ← hpq]
        · exact (hD_le_p y hyTk).trans (Nat.sub_le _ _)
      rcases Finset.mem_insert.mp hzmem with hzc | hzC
      · have : z = cv := Subtype.ext hzc
        subst z
        have hDcv : D cv = d c := by
          simp [D, cv, fourCornerD, residualDegree, hfc.distinct.1,
            hfc.distinct.2.2.1, hfc.not_mem.1]
        rw [hDcv]
        exact hDyle.trans hfc.ordered.2.2
      · have hDz : D z = d z.val - 1 := by
          simp [D, fourCornerD, residualDegree, hzC]
        rw [hDz]
        have htop := hfc.top_block z.val hzC
        have hgaps := (lemma_8_3a_strict_outer_gaps hfc).1
        omega
    have hTkhigh : ∀ z ∈ Tk, ∀ y ∈ Tkᶜ, D y ≤ D z := by
      intro z hz y hy
      rw [hTk] at hz
      rcases Finset.mem_insert.mp hz with rfl | hzTm
      · rw [hDb, ← hpq]
        exact (hD_le_p y hy).trans (Nat.sub_le _ _)
      · exact hTmhigh z hzTm y (by rw [hTmcomp]; exact Finset.mem_insert_of_mem hy)
    obtain ⟨hTmvals, hTmcompvals⟩ := topBlock_data Tm t hTmcard hTmhigh
    obtain ⟨hTkvals, hTkcompvals⟩ := topBlock_data Tk (d v) hTkcard hTkhigh
    have hslackTm := erdosGallaiSlack_eq_of_topBlock D hTmcard hTmvals hTmcompvals
    have hslackTk := erdosGallaiSlack_eq_of_topBlock D hTkcard hTkvals hTkcompvals
    have hbTk : bv ∈ Tk := by rw [hTk]; exact Finset.mem_insert_self _ _
    have hbTkcomp : bv ∉ Tkᶜ := by simpa using hbTk
    have htopSum : (∑ z ∈ Tk, (D z : ℤ)) =
        (d b : ℤ) + ∑ z ∈ Tm, (D z : ℤ) := by
      rw [hTk, Finset.sum_insert hbTm, hDb]
    have htailTm : (∑ z ∈ Tmᶜ, (min (D z) t : ℤ)) =
        (d b : ℤ) + ∑ z ∈ Tkᶜ, (D z : ℤ) := by
      rw [hTmcomp, Finset.sum_insert hbTkcomp]
      have hb_le_t : d b ≤ t := by rw [← hpq]; exact hp_le_t
      have hb_le_t_int : (d b : ℤ) ≤ (t : ℤ) := by exact_mod_cast hb_le_t
      rw [hDb, min_eq_left hb_le_t_int]
      congr 1
      apply Finset.sum_congr rfl
      intro z hz
      rw [min_eq_left]
      have hz_le_t : D z ≤ t := by
        have hzD := hD_le_p z hz
        omega
      exact_mod_cast hz_le_t
    have htailTk : (∑ z ∈ Tkᶜ, (min (D z) (d v) : ℤ)) =
        ∑ z ∈ Tkᶜ, (D z : ℤ) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [min_eq_left]
      have hz_le_k : D z ≤ d v := by
        have hzD := hD_le_p z hz
        omega
      exact_mod_cast hz_le_k
    have hrec : erdosGallaiSlack D (d v) =
        erdosGallaiSlack D t + 2 * ((t : ℤ) - (d a : ℤ)) := by
      rw [hslackTk, hslackTm, htailTk, htailTm, htopSum]
      rw [← hpq]
      have ht_eq : d v = t + 1 := by dsimp [t]; omega
      push_cast [ht_eq]
      ring
    have hrec_nonneg : erdosGallaiSlack D t ≤ erdosGallaiSlack D (d v) := by
      rw [hrec]
      have hdiff_nonneg : 0 ≤ (t : ℤ) - (d a : ℤ) := by
        exact sub_nonneg.mpr (by exact_mod_cast hp_le_t)
      exact le_add_of_nonneg_right (mul_nonneg (by norm_num) hdiff_nonneg)
    exact (not_lt_of_ge (hsigma_nonneg.trans hrec_nonneg)) hDk_neg

/-- Complementing every realization reverses a four-corner configuration. -/
theorem fourCorner_complement {d : V → ℕ} {v : V} {C₀ : Finset V} {c a b x : V}
    (hfc : FourCorner d v C₀ c a b x) :
    FourCorner (fun u => Fintype.card V - 1 - d u) v
      ((insert v (insert c (insert a (insert b (insert x C₀)))))ᶜ) x b a c := by
  classical
  let N := Fintype.card V - 1
  let dc : V → ℕ := fun u => N - d u
  let H : Finset V := insert v (insert c (insert a (insert b (insert x C₀))))
  let B : Finset V := Hᶜ
  change FourCorner dc v B x b a c
  rcases hfc.ne_pivot with ⟨hcv, hav, hbv, hxv⟩
  rcases hfc.not_mem with ⟨hcC, haC, hbC, hxC⟩
  rcases hfc.distinct with ⟨hca_ne, hcb_ne, hcx_ne, hab_ne, hax_ne, hbx_ne⟩
  -- any corner supplies a realization of `d`; nothing here depends on WHICH one
  obtain ⟨G₀, hG₀⟩ := hfc.corner_cx
  have hd_le (u : V) : d u ≤ N := by
    letI := G₀.adjDecidable
    have hdeg : G₀.graph.degree u = d u := G₀.degree_eq u
    have hu := G₀.graph.degree_lt_card_verts u
    dsimp [N]
    rw [← hdeg]
    omega
  have complement_corner {S : Finset V}
      (hS : HasRealizationWithNeighborSet d v S) :
      HasRealizationWithNeighborSet dc v (Sᶜ.erase v) := by
    obtain ⟨G, hG⟩ := hS
    let Gc : Realization dc :=
      { graph := G.graphᶜ
        adjDecidable := by infer_instance
        degree_eq := by
          intro u
          rw [SimpleGraph.degree_compl, G.degree_eq] }
    refine ⟨Gc, ?_⟩
    change G.graphᶜ.neighborFinset v = Sᶜ.erase v
    have hG' : G.graph.neighborFinset v = S := by
      simpa [Realization.neighborFinset] using hG
    rw [SimpleGraph.neighborFinset_compl, hG']
    ext u
    simp [and_comm]
  have uncomplement_corner {S : Finset V} (hvS : v ∉ S)
      (hS : HasRealizationWithNeighborSet dc v (Sᶜ.erase v)) :
      HasRealizationWithNeighborSet d v S := by
    obtain ⟨G, hG⟩ := hS
    let Gc : Realization d :=
      { graph := G.graphᶜ
        adjDecidable := by infer_instance
        degree_eq := by
          intro u
          rw [SimpleGraph.degree_compl, G.degree_eq]
          dsimp [dc, N]
          have := hd_le u
          omega }
    refine ⟨Gc, ?_⟩
    change G.graphᶜ.neighborFinset v = S
    have hG' : G.graph.neighborFinset v = Sᶜ.erase v := by
      simpa [Realization.neighborFinset] using hG
    rw [SimpleGraph.neighborFinset_compl, hG']
    ext u
    by_cases huv : u = v
    · subst u
      simp [hvS]
    · simp [huv]
  have hHcard : H.card = C₀.card + 5 := by
    have hbX : b ∉ insert x C₀ := by
      simp [hbx_ne, hbC]
    have haBX : a ∉ insert b (insert x C₀) := by
      simp [hab_ne, hax_ne, haC]
    have hcABX : c ∉ insert a (insert b (insert x C₀)) := by
      simp [hca_ne, hcb_ne, hcx_ne, hcC]
    have hvCABX : v ∉ insert c (insert a (insert b (insert x C₀))) := by
      simp [hcv.symm, hav.symm, hbv.symm, hxv.symm, hfc.pivot_not_mem]
    simp [H, Finset.card_insert_of_notMem, hvCABX, hcABX, haBX, hbX, hxC]
  have hHle : H.card ≤ Fintype.card V := by
    simpa using Finset.card_le_univ H
  have hBcard : B.card + 2 = dc v := by
    rw [show B.card = Fintype.card V - H.card by
      dsimp [B]; exact Finset.card_compl H]
    rw [hHcard]
    dsimp [dc, N]
    rw [hHcard] at hHle
    rw [← hfc.card]
    omega
  have hBmem (u : V) : u ∈ B ↔
      u ≠ v ∧ u ≠ c ∧ u ≠ a ∧ u ≠ b ∧ u ≠ x ∧ u ∉ C₀ := by
    simp [B, H]
  have hcx : insert x (insert c B) = (insert a (insert b C₀))ᶜ.erase v := by
    ext u
    simp only [Finset.mem_insert, hBmem, Finset.mem_erase, Finset.mem_compl, not_or]
    constructor
    · rintro (rfl | rfl | hu)
      · exact ⟨hxv, hax_ne.symm, hbx_ne.symm, hxC⟩
      · exact ⟨hcv, hca_ne, hcb_ne, hcC⟩
      · exact ⟨hu.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.2⟩
    · rintro ⟨huv, hua, hub, huC⟩
      by_cases hux : u = x
      · exact Or.inl hux
      by_cases huc : u = c
      · exact Or.inr (Or.inl huc)
      exact Or.inr (Or.inr ⟨huv, huc, hua, hub, hux, huC⟩)
  have hab : insert b (insert a B) = (insert c (insert x C₀))ᶜ.erase v := by
    ext u
    simp only [Finset.mem_insert, hBmem, Finset.mem_erase, Finset.mem_compl, not_or]
    constructor
    · rintro (rfl | rfl | hu)
      · exact ⟨hbv, hcb_ne.symm, hbx_ne, hbC⟩
      · exact ⟨hav, hca_ne.symm, hax_ne, haC⟩
      · exact ⟨hu.1, hu.2.1, hu.2.2.2.2.1, hu.2.2.2.2.2⟩
    · rintro ⟨huv, huc, hux, huC⟩
      by_cases hub : u = b
      · exact Or.inl hub
      by_cases hua : u = a
      · exact Or.inr (Or.inl hua)
      exact Or.inr (Or.inr ⟨huv, huc, hua, hub, hux, huC⟩)
  have hax : insert b (insert c B) = (insert a (insert x C₀))ᶜ.erase v := by
    ext u
    simp only [Finset.mem_insert, hBmem, Finset.mem_erase, Finset.mem_compl, not_or]
    constructor
    · rintro (rfl | rfl | hu)
      · exact ⟨hbv, hab_ne.symm, hbx_ne, hbC⟩
      · exact ⟨hcv, hca_ne, hcx_ne, hcC⟩
      · exact ⟨hu.1, hu.2.2.1, hu.2.2.2.2.1, hu.2.2.2.2.2⟩
    · rintro ⟨huv, hua, hux, huC⟩
      by_cases hub : u = b
      · exact Or.inl hub
      by_cases huc : u = c
      · exact Or.inr (Or.inl huc)
      exact Or.inr (Or.inr ⟨huv, huc, hua, hub, hux, huC⟩)
  refine
    { pivot_not_mem := by simp [B, H]
      ne_pivot := ⟨hfc.ne_pivot.2.2.2, hfc.ne_pivot.2.2.1,
        hfc.ne_pivot.2.1, hfc.ne_pivot.1⟩
      not_mem := by simp [B, H]
      distinct := ⟨hbx_ne.symm, hax_ne.symm, hcx_ne.symm,
        hab_ne.symm, hcb_ne.symm, hca_ne.symm⟩
      card := hBcard
      top_block := ?_
      ordered := ?_
      tail := ?_
      corner_cx := by rw [hcx]; exact complement_corner hfc.corner_ab
      corner_ab := by rw [hab]; exact complement_corner hfc.corner_cx
      not_corner_ax := by
        rw [hax]
        intro h
        apply hfc.not_corner_ax
        apply uncomplement_corner
        · simp [hfc.ne_pivot.2.1.symm, hfc.ne_pivot.2.2.2.symm,
            hfc.pivot_not_mem]
        · exact h }
  · intro u hu
    have huv : u ≠ v := by
      intro huv
      subst u
      exact (by simpa [B, H] using hu)
    have huC : u ∉ C₀ := by
      intro huC
      exact (by simpa [B, H, huC] using hu)
    have huc : u ≠ c := by
      intro huc
      subst u
      exact (by simpa [B, H] using hu)
    have hua : u ≠ a := by
      intro hua
      subst u
      exact (by simpa [B, H] using hu)
    have hub : u ≠ b := by
      intro hub
      subst u
      exact (by simpa [B, H] using hu)
    have hux : u ≠ x := by
      intro hux
      subst u
      exact (by simpa [B, H] using hu)
    have hdu := hfc.tail u huv huC huc hua hub hux
    dsimp [dc]
    omega
  · dsimp [dc]
    have hc := hd_le c
    have ha := hd_le a
    have hb := hd_le b
    have hx := hd_le x
    rcases hfc.ordered with ⟨hxb, hba, hac⟩
    constructor
    · omega
    · constructor <;> omega
  · intro u huv huB hux hub hua huc
    have huH : u ∈ H := by
      simpa [B] using huB
    have huC : u ∈ C₀ := by
      simpa [H, huv, huc, hua, hub, hux] using huH
    have hdu := hfc.top_block u huC
    dsimp [dc]
    omega

/-- **Lemma 8.3f (complementation).** Manuscript §8.2: `p ≤ k`, proved by applying Lemma 8.3e to the
complementary sequence — which is exactly why these are stated about the configuration. -/
theorem lemma_8_3f_complementation {d : V → ℕ} {v : V} {C₀ : Finset V} {c a b x : V}
    (hfc : FourCorner d v C₀ c a b x) :
    d a ≤ d v := by
  classical
  have hfc' := fourCorner_complement hfc
  have hbound := lemma_8_3e_one_sided_bound hfc'
  change Fintype.card V - 1 - d v ≤ Fintype.card V - 1 - d a at hbound
  obtain ⟨G, _hG⟩ := hfc.corner_cx
  have hva : d v < Fintype.card V := by
    rw [← G.degree_eq_apply v]
    exact G.graph.degree_lt_card_verts v
  have haa : d a < Fintype.card V := by
    rw [← G.degree_eq_apply a]
    exact G.graph.degree_lt_card_verts a
  omega

/-- **Theorem 8.3**, the point of the section: at a four-corner configuration the two middle degrees
equal the pivot degree. Manuscript §8.2, *"Lemmas 8.3e and 8.3f give `p = q = k`"*. Derived here
rather than assumed, so it charges 8.3e and 8.3f and nothing else. (Until 2026-08-24 this sentence
said its `sorryAx` comes from those two. There is no `sorry` anywhere in this file, and `sbPlus` has
been in the baseline's `sorryAx`-free Part B since 2026-08-19 — a reader auditing the surface from
docstrings would have recorded an open obligation that does not exist.) -/
theorem theorem_8_3_middle_degrees {d : V → ℕ} {v : V} {C₀ : Finset V} {c a b x : V}
    (hfc : FourCorner d v C₀ c a b x) :
    d a = d v ∧ d b = d v := by
  have hq := lemma_8_3e_one_sided_bound hfc
  have hp := lemma_8_3f_complementation hfc
  have hba := hfc.ordered.2.1
  omega

/-- **(8.3′), the degree class.** Manuscript Theorem 8.3: at a yFamily pivot the degree-`d v` class is
exactly `{v, a, b}`, so it has three members. Order-free: it counts a class rather than naming its
elements. -/
theorem yFamilyPivot_degreeClass_card {d : V → ℕ} {v : V} (h : YFamilyPivot d v) :
    (Finset.univ.filter (fun u => d u = d v)).card = 3 := by
  classical
  obtain ⟨C₀, c, a, b, x, hfc⟩ := fourCorner_of_yFamilyPivot h
  have hmid := theorem_8_3_middle_degrees hfc
  have hgaps := lemma_8_3a_strict_outer_gaps hfc
  have hclass : Finset.univ.filter (fun u => d u = d v) = {v, a, b} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hdu
      by_cases huv : u = v
      · exact Or.inl huv
      by_cases hua : u = a
      · exact Or.inr (Or.inl hua)
      by_cases hub : u = b
      · exact Or.inr (Or.inr hub)
      by_cases huC : u ∈ C₀
      · have htop := hfc.top_block u huC
        omega
      by_cases huc : u = c
      · subst u
        omega
      by_cases hux : u = x
      · subst u
        omega
      have htail := hfc.tail u huv huC huc hua hub hux
      omega
    · rintro (rfl | rfl | rfl)
      · rfl
      · exact hmid.1
      · exact hmid.2
  rw [hclass]
  have hva : v ≠ a := hfc.ne_pivot.2.1.symm
  have hvb : v ≠ b := hfc.ne_pivot.2.2.1.symm
  have hab : a ≠ b := hfc.distinct.2.2.2.1
  simp [hva, hvb, hab]

/-- **(8.3′), the count above.** Manuscript §8.2: the vertices above `v`'s degree class are exactly
`u_1, …, u_{k−1}`, so there are `d v − 1` of them. Together with `yFamilyPivot_degreeClass_card` this is
the whole content of Theorem 8.3 that §8.5 uses, with the order removed.

⚠ `d v - 1` is truncated ℕ subtraction, harmless here: no yFamily pivot has `d v = 0`, since a bad
template has at least four vertices while a pivot of degree `0` has a one-element quotient family.
The sweep confirms it — 0 failures over all 153 yFamily pivots, where `d v = 0` would have shown up as
one immediately. -/
theorem yFamilyPivot_card_above {d : V → ℕ} {v : V} (h : YFamilyPivot d v) :
    (Finset.univ.filter (fun u => d v < d u)).card = d v - 1 := by
  classical
  obtain ⟨C₀, c, a, b, x, hfc⟩ := fourCorner_of_yFamilyPivot h
  have hmid := theorem_8_3_middle_degrees hfc
  have hgaps := lemma_8_3a_strict_outer_gaps hfc
  have habove : Finset.univ.filter (fun u => d v < d u) = insert c C₀ := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hdu
      by_cases huc : u = c
      · exact Or.inl huc
      by_cases huC : u ∈ C₀
      · exact Or.inr huC
      by_cases huv : u = v
      · subst u
        omega
      by_cases hua : u = a
      · subst u
        omega
      by_cases hub : u = b
      · subst u
        omega
      by_cases hux : u = x
      · subst u
        omega
      have htail := hfc.tail u huv huC huc hua hub hux
      omega
    · rintro (rfl | huC)
      · omega
      · have htop := hfc.top_block u huC
        omega
  rw [habove, Finset.card_insert_of_notMem hfc.not_mem.1]
  have hcard := hfc.card
  have hk : 2 ≤ d v := by omega
  omega

/-- **Corollary 8.4, the half §8.4 consumes: all yFamily pivots share a degree.** Manuscript §8.2 states
it as `H(d) ⊆ {v, a, b}`, the degree-`k` class; since `yFamilyPivot_degreeClass_card` already pins that
class at three members, what Lemma 8.6 actually needs is that a second yFamily pivot cannot sit at a
different degree.

**The manuscript's counting argument, now available because both inputs are proved.** Suppose `w` is
a yFamily pivot with `d w > d v`. Applying `yFamilyPivot_card_above` and `yFamilyPivot_degreeClass_card` at
`w` gives `d w − 1` vertices strictly above `d w` and three at it, so `d w + 2` vertices of degree at
least `d w`. All of those exceed `d v`, and `yFamilyPivot_card_above` at `v` allows only `d v − 1` such,
giving `d w + 2 ≤ d v − 1` and so `d w < d v` — contradicting `d w > d v`. The case `d w < d v` is
the same count read the other way.

⚠ The manuscript states Corollary 8.4 as an **inclusion** on purpose, and notes that the reverse — that
`a` and `b` are themselves yFamily pivots — is true but not proved there and not used. **Do not
strengthen this to an equality**; an earlier draft asserted it and §8.5 then cited the unproved half.

Verified over all 153 yFamily pivots through ground order 8, together with the rest of Corollary 8.4:
`compute/lemma_8_4_8_6_check_2026_08_18.py`, 0 failures. -/
theorem yFamilyPivot_same_degree {d : V → ℕ} {v w : V}
    (hv : YFamilyPivot d v) (hw : YFamilyPivot d w) : d w = d v := by
  classical
  have card_ge (z : V) (hz : YFamilyPivot d z) :
      (Finset.univ.filter (fun u => d z ≤ d u)).card = (d z - 1) + 3 := by
    let A := Finset.univ.filter (fun u => d z < d u)
    let E := Finset.univ.filter (fun u => d u = d z)
    have hsplit : Finset.univ.filter (fun u => d z ≤ d u) = A ∪ E := by
      ext u
      simp only [A, E, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      omega
    have hdisjoint : Disjoint A E := by
      exact Finset.disjoint_left.mpr (by
        intro u huA huE
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at huA
        simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at huE
        omega)
    rw [hsplit, Finset.card_union_of_disjoint hdisjoint]
    exact congrArg₂ (· + ·) (yFamilyPivot_card_above hz) (yFamilyPivot_degreeClass_card hz)
  apply Nat.le_antisymm
  · by_contra hnot
    have hvw : d v < d w := Nat.lt_of_not_ge hnot
    have hsub :
        Finset.univ.filter (fun u => d w ≤ d u) ⊆
          Finset.univ.filter (fun u => d v < d u) := by
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      omega
    have hle := Finset.card_le_card hsub
    rw [card_ge w hw, yFamilyPivot_card_above hv] at hle
    omega
  · by_contra hnot
    have hwv : d w < d v := Nat.lt_of_not_ge hnot
    have hsub :
        Finset.univ.filter (fun u => d v ≤ d u) ⊆
          Finset.univ.filter (fun u => d w < d u) := by
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      omega
    have hle := Finset.card_le_card hsub
    rw [card_ge v hv, yFamilyPivot_card_above hw] at hle
    omega

/-- **(8.2′), the forced pair.** Manuscript Lemma 8.2, order-free: the two `Δ`-neighbours of an
exceptional pivot are the other two members of its own degree class. In particular `deg_Δ(v) = 2`, so
a vertex with `deg_Δ ≥ 4` is never exceptional, and the pair is determined by `d` and `v` alone —
visibly so, since the right-hand side mentions neither `X` nor `Y`. -/
theorem exceptionalPivot_symmDiff_eq_degreeClass {d : V → ℕ} {X Y : Realization d} {v : V}
    (h : ExceptionalPivot d X Y v) :
    X.neighborFinset v ∆ Y.neighborFinset v
      = Finset.univ.filter (fun u => u ≠ v ∧ d u = d v) := by
  classical
  rcases h with ⟨hX, hY, hbadQ⟩
  let qX : QuotientV d v := ⟨X.neighborFinset v, hX⟩
  let qY : QuotientV d v := ⟨Y.neighborFinset v, hY⟩
  have hpivot : YFamilyPivot d v := ⟨qX, qY, hbadQ⟩
  obtain ⟨inst, hvmax, hmono⟩ := exists_pivotMaximal_degreeAntitone_order d v
  letI : LinearOrder V := inst
  let F := realizableNeighborhoods d v
  let φ := quotientIsoExchange d v
  let G := QStar.usedGround F
  have hFne : F.Nonempty :=
    ⟨X.neighborFinset v, mem_realizableNeighborhoods.mpr hX⟩
  have hshift : QStar.IsShifted F (d v) :=
    quotientFamily_isShifted d v hvmax hmono hFne
  have hbadF : QStar.IsCliqueSum F (φ qX) (φ qY) :=
    QStar.isCliqueSum_map_iso φ hbadQ
  have hφX : (φ qX).val = X.neighborFinset v := rfl
  have hφY : (φ qY).val = Y.neighborFinset v := rfl
  have hcoords := QStar.cliqueSum_universalPair_coordinates hshift hbadF
  change
    ((φ qX).val = QStar.initialSegment G (d v) ∧
        (φ qY).val = QStar.secondInitialSegment G (d v)) ∨
      ((φ qY).val = QStar.initialSegment G (d v) ∧
        (φ qX).val = QStar.secondInitialSegment G (d v)) at hcoords
  rw [hφX, hφY] at hcoords
  have hGcard : d v + 1 ≤ G.card :=
    QStar.cliqueSum_usedGround_card hshift hbadF
  obtain ⟨C₀, c, a, b, x, hfc⟩ := fourCorner_of_yFamilyPivot hpivot
  have hk : 2 ≤ d v := by
    have := hfc.card
    omega
  let E₀ := Finset.univ.filter (fun u => u ≠ v ∧ d u = d v)
  have hclassSplit :
      Finset.univ.filter (fun u => d u = d v) = insert v E₀ := by
    ext u
    simp only [E₀, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hdu
      by_cases huv : u = v
      · exact Or.inl huv
      · exact Or.inr ⟨huv, hdu⟩
    · rintro (rfl | ⟨_, hdu⟩)
      · rfl
      · exact hdu
  have hvE₀ : v ∉ E₀ := by simp [E₀]
  have hE₀card : E₀.card = 2 := by
    have hcard := yFamilyPivot_degreeClass_card hpivot
    rw [hclassSplit, Finset.card_insert_of_notMem hvE₀] at hcard
    omega
  let A := Finset.univ.filter (fun u => d v < d u)
  have hAcard : A.card = d v - 1 := by
    simpa [A] using yFamilyPivot_card_above hpivot
  let B := Finset.univ.filter (fun u => u ≠ v ∧ d v ≤ d u)
  have hBsplit : B = A ∪ E₀ := by
    ext u
    constructor
    · intro huB
      have huB' := Finset.mem_filter.mp huB
      rcases lt_or_eq_of_le huB'.2.2 with hlt | heq
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, huB'.2.1, heq.symm⟩)
    · intro hu
      rcases Finset.mem_union.mp hu with huA | huE
      · have huA' := Finset.mem_filter.mp huA
        have huv : u ≠ v := by
          intro huv
          subst u
          omega
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, huA'.2.le⟩
      · have huE' := Finset.mem_filter.mp huE
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, huE'.2.1, huE'.2.2.ge⟩
  have hAE₀ : Disjoint A E₀ := by
    exact Finset.disjoint_left.mpr (by
      intro u huA huE
      have huA' := (Finset.mem_filter.mp huA).2
      have huE' := (Finset.mem_filter.mp huE).2.2
      omega)
  have hBcard : B.card = d v + 1 := by
    rw [hBsplit, Finset.card_union_of_disjoint hAE₀, hAcard, hE₀card]
    omega
  have hvSets : ∀ S ∈ F, v ∉ S := by
    intro S hSF hvS
    obtain ⟨R, hR⟩ := mem_realizableNeighborhoods.mp hSF
    have : v ∈ R.neighborFinset v := by simpa [hR] using hvS
    exact R.graph.irrefl ((R.mem_neighborFinset v v).mp this)
  have hvG : v ∉ G := by
    intro hv
    change v ∈ F.biUnion id at hv
    obtain ⟨S, hSF, hvS⟩ := Finset.mem_biUnion.mp hv
    exact hvSets S hSF hvS
  have hGlower : ∀ {y : V}, y ∈ G → ∀ {z : V}, z < y → z ∈ G := by
    intro y hyG z hzy
    change y ∈ F.biUnion id at hyG
    obtain ⟨S, hSF, hyS⟩ := Finset.mem_biUnion.mp hyG
    by_cases hzS : z ∈ S
    · change z ∈ F.biUnion id
      exact Finset.mem_biUnion.mpr ⟨S, hSF, hzS⟩
    · have hnew := hshift.2.2 S hSF z y hyS hzy hzS
      change z ∈ F.biUnion id
      exact Finset.mem_biUnion.mpr
        ⟨insert z (S.erase y), hnew, Finset.mem_insert_self z _⟩
  let I := QStar.initialSegment G (d v)
  let M := QStar.secondInitialSegment G (d v)
  let U := QStar.initialSegment G (d v + 1)
  let C := QStar.initialSegment G (d v - 1)
  let D := U \ C
  have hCU : C ⊆ U := by
    exact QStar.initialSegment_mono G (by omega)
  have hUcard : U.card = d v + 1 := by
    exact QStar.card_initialSegment_of_le hGcard
  have hCcard : C.card = d v - 1 := by
    apply QStar.card_initialSegment_of_le
    omega
  have hDcard : D.card = 2 := by
    change (U \ C).card = 2
    rw [Finset.card_sdiff_of_subset hCU, hUcard, hCcard]
    omega
  have hcanonicalDiff : I ∆ M = D := by
    calc
      I ∆ M = (I ∪ M) \ (I ∩ M) := by
        ext u
        by_cases huI : u ∈ I <;> by_cases huM : u ∈ M <;>
          simp [Finset.mem_symmDiff, huI, huM]
      _ = D := by
        change
          (QStar.initialSegment G (d v) ∪ QStar.secondInitialSegment G (d v)) \
              (QStar.initialSegment G (d v) ∩ QStar.secondInitialSegment G (d v)) =
            QStar.initialSegment G (d v + 1) \ QStar.initialSegment G (d v - 1)
        rw [QStar.initialSegment_union_secondInitialSegment,
          QStar.initialSegment_inter_secondInitialSegment]
  have hDsub : D ⊆ E₀ := by
    intro u huD
    have huDC := Finset.mem_sdiff.mp huD
    have huU : u ∈ U := huDC.1
    have huG : u ∈ G := QStar.initialSegment_subset G (d v + 1) huU
    have huv : u ≠ v := ne_of_mem_of_not_mem huG hvG
    have huRankLt : QStar.groundRank G u < d v + 1 := by
      exact (Finset.mem_filter.mp huU).2
    have huRankGe : d v - 1 ≤ QStar.groundRank G u := by
      apply Nat.le_of_not_gt
      intro huRank
      apply huDC.2
      exact Finset.mem_filter.mpr ⟨huG, huRank⟩
    have hduLe : d u ≤ d v := by
      by_contra hnot
      have hvdu : d v < d u := Nat.lt_of_not_ge hnot
      let L := insert u (G.filter (fun z => z < u))
      have hLsub : L ⊆ A := by
        intro z hzL
        rcases Finset.mem_insert.mp hzL with rfl | hzL
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvdu⟩
        · have hzG := (Finset.mem_filter.mp hzL).1
          have hzu := (Finset.mem_filter.mp hzL).2
          have hzv : z ≠ v := ne_of_mem_of_not_mem hzG hvG
          have hmono' := hmono z u hzv huv hzu
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      have hLcard : L.card = QStar.groundRank G u + 1 := by
        simp [L, QStar.groundRank]
      have hle := Finset.card_le_card hLsub
      rw [hLcard, hAcard] at hle
      omega
    have hduGe : d v ≤ d u := by
      by_contra hnot
      have hdult : d u < d v := Nat.lt_of_not_ge hnot
      have hBsub : B ⊆ G.filter (fun z => z < u) := by
        intro z hzB
        have hzB' := (Finset.mem_filter.mp hzB).2
        have hzuNe : z ≠ u := by
          intro hzu
          subst z
          omega
        have hnotUZ : ¬ u < z := by
          intro huz
          have hmono' := hmono u z huv hzB'.1 huz
          omega
        have hzu : z < u := lt_of_le_of_ne (le_of_not_gt hnotUZ) hzuNe
        exact Finset.mem_filter.mpr ⟨hGlower huG hzu, hzu⟩
      have hle := Finset.card_le_card hBsub
      change B.card ≤ QStar.groundRank G u at hle
      rw [hBcard] at hle
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, Nat.le_antisymm hduLe hduGe⟩
  have hDE₀ : D = E₀ := by
    apply Finset.eq_of_subset_of_card_le hDsub
    rw [hE₀card, hDcard]
  have hforced : I ∆ M = E₀ := hcanonicalDiff.trans hDE₀
  change X.neighborFinset v ∆ Y.neighborFinset v = E₀
  rcases hcoords with ⟨hXI, hYM⟩ | ⟨hYI, hXM⟩
  · rw [hXI, hYM]
    exact hforced
  · rw [hXM, hYI, symmDiff_comm]
    exact hforced

/-! ## 4. `(SB+)` -/

/-- **The engine of `(SB+)`, worth stating separately because it is reusable.** Admissibility is
constant on a degree class: an equal-degree transposition is an automorphism of the realization
graph, so it carries a triangle inside a `v`-fibre to a triangle inside a `w`-fibre. -/
theorem hasNonBipartiteFibre_of_degree_eq {d : V → ℕ} {v w : V} (hdeg : d v = d w)
    (h : HasNonBipartiteFibre d v) : HasNonBipartiteFibre d w := by
  classical
  let τ : Equiv.Perm V := Equiv.swap v w
  have hτd : ∀ x, d (τ x) = d x := by
    intro x
    by_cases hxv : x = v
    · subst x
      simpa [τ] using hdeg.symm
    · by_cases hxw : x = w
      · subst x
        simpa [τ] using hdeg
      · simp [τ, Equiv.swap_apply_def, hxv, hxw]
  rcases h with ⟨A, B, C, hABN, hBCN, hAB, hBC, hAC⟩
  refine ⟨relabelRealizationOfInvariant τ hτd A,
    relabelRealizationOfInvariant τ hτd B,
    relabelRealizationOfInvariant τ hτd C, ?_, ?_, ?_, ?_, ?_⟩
  · rw [relabelRealizationOfInvariant_neighborFinset,
      relabelRealizationOfInvariant_neighborFinset]
    simpa [τ] using congrArg (fun S => S.map τ.symm.toEmbedding) hABN
  · rw [relabelRealizationOfInvariant_neighborFinset,
      relabelRealizationOfInvariant_neighborFinset]
    simpa [τ] using congrArg (fun S => S.map τ.symm.toEmbedding) hBCN
  · exact (relabelRealizationOfInvariant_adj_iff τ hτd A B).2 hAB
  · exact (relabelRealizationOfInvariant_adj_iff τ hτd B C).2 hBC
  · exact (relabelRealizationOfInvariant_adj_iff τ hτd A C).2 hAC

/-- **The other engine: at most two pivots can be exceptional.** The yFamily pivots of a degree
sequence all lie in ONE degree class, which has three members, and a third exceptional pivot would
force an odd alternating cycle in `E(X) ∆ E(Y)`.

**Corrected 2026-08-24.** This said the yFamily pivots "form exactly one degree class of size three",
which is the equality form — and 283 lines above, `yFamilyPivot_same_degree`'s own docstring says
*"⚠ Do not strengthen this to an equality; an earlier draft asserted it and §8.5 then cited the
unproved half."* The proof below uses only the inclusion. The recorded error had reappeared in the
docstring of the engine `sbPlus` calls. -/
theorem atMostTwoExceptional {d : V → ℕ} (X Y : Realization d)
    (u v w : V) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w) :
    ¬ (ExceptionalPivot d X Y u ∧ ExceptionalPivot d X Y v ∧ ExceptionalPivot d X Y w) := by
  classical
  rintro ⟨hu, hv, hw⟩
  have huYFamily : YFamilyPivot d u := by
    rcases hu with ⟨hXu, hYu, hbad⟩
    exact ⟨⟨X.neighborFinset u, hXu⟩, ⟨Y.neighborFinset u, hYu⟩, hbad⟩
  have hvYFamily : YFamilyPivot d v := by
    rcases hv with ⟨hXv, hYv, hbad⟩
    exact ⟨⟨X.neighborFinset v, hXv⟩, ⟨Y.neighborFinset v, hYv⟩, hbad⟩
  have hwYFamily : YFamilyPivot d w := by
    rcases hw with ⟨hXw, hYw, hbad⟩
    exact ⟨⟨X.neighborFinset w, hXw⟩, ⟨Y.neighborFinset w, hYw⟩, hbad⟩
  have hdv : d v = d u := yFamilyPivot_same_degree huYFamily hvYFamily
  have hdw : d w = d u := yFamilyPivot_same_degree huYFamily hwYFamily
  let C := Finset.univ.filter (fun z ↦ d z = d u)
  have htripleSub : {u, v, w} ⊆ C := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · simp [C]
    · simp [C, hdv]
    · simp [C, hdw]
  have hCcard : C.card = 3 := by
    simpa [C] using yFamilyPivot_degreeClass_card huYFamily
  have htripleCard : ({u, v, w} : Finset V).card = 3 := by
    simp [huv, hvw, huw]
  have hclass : C = {u, v, w} := by
    symm
    apply Finset.eq_of_subset_of_card_le htripleSub
    rw [hCcard, htripleCard]
  have huDiff : X.neighborFinset u ∆ Y.neighborFinset u = {v, w} := by
    rw [exceptionalPivot_symmDiff_eq_degreeClass hu]
    calc
      Finset.univ.filter (fun z ↦ z ≠ u ∧ d z = d u) = C.erase u := by
        ext z
        simp [C, and_comm]
      _ = {v, w} := by
        rw [hclass]
        simp [huv, huw]
  have hvDiff : X.neighborFinset v ∆ Y.neighborFinset v = {u, w} := by
    rw [exceptionalPivot_symmDiff_eq_degreeClass hv]
    calc
      Finset.univ.filter (fun z ↦ z ≠ v ∧ d z = d v) = C.erase v := by
        ext z
        simp [C, hdv, and_comm]
      _ = {u, w} := by
        rw [hclass]
        ext z
        simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hzv, rfl | rfl | rfl⟩
          · exact Or.inl rfl
          · exact (hzv rfl).elim
          · exact Or.inr rfl
        · rintro (rfl | rfl)
          · exact ⟨huv, Or.inl rfl⟩
          · exact ⟨hvw.symm, Or.inr (Or.inr rfl)⟩
  have hwDiff : X.neighborFinset w ∆ Y.neighborFinset w = {u, v} := by
    rw [exceptionalPivot_symmDiff_eq_degreeClass hw]
    calc
      Finset.univ.filter (fun z ↦ z ≠ w ∧ d z = d w) = C.erase w := by
        ext z
        simp [C, hdw, and_comm]
      _ = {u, v} := by
        rw [hclass]
        ext z
        simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hzw, rfl | rfl | rfl⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
          · exact (hzw rfl).elim
        · rintro (rfl | rfl)
          · exact ⟨huw, Or.inl rfl⟩
          · exact ⟨hvw, Or.inr (Or.inl rfl)⟩
  have hneighborCard (z : V) :
      (X.neighborFinset z).card = (Y.neighborFinset z).card := by
    simp [Realization.neighborFinset, SimpleGraph.card_neighborFinset_eq_degree,
      X.degree_eq z, Y.degree_eq z]
  have oppositeAt (a b c : V) (hbc : b ≠ c)
      (hdiff : X.neighborFinset a ∆ Y.neighborFinset a = {b, c}) :
      (b ∈ X.neighborFinset a ↔ c ∉ X.neighborFinset a) := by
    have hdiffCard :
        (X.neighborFinset a ∆ Y.neighborFinset a).card = 2 := by
      rw [hdiff]
      simp [hbc]
    rw [Finset.symmDiff_def,
      Finset.card_union_of_disjoint
        (Finset.sdiff_disjoint.mono_right Finset.sdiff_subset)] at hdiffCard
    have hbalanced :
        (X.neighborFinset a \ Y.neighborFinset a).card =
          (Y.neighborFinset a \ X.neighborFinset a).card :=
      Finset.card_sdiff_comm (hneighborCard a)
    have hXonlyCard : (X.neighborFinset a \ Y.neighborFinset a).card = 1 := by
      omega
    have hXonlySub : X.neighborFinset a \ Y.neighborFinset a ⊆ {b, c} := by
      intro z hz
      have hzDiff : z ∈ X.neighborFinset a ∆ Y.neighborFinset a := by
        simp only [Finset.mem_symmDiff]
        exact Or.inl ⟨(Finset.mem_sdiff.mp hz).1, (Finset.mem_sdiff.mp hz).2⟩
      simpa [hdiff] using hzDiff
    constructor
    · intro hbX hcX
      have hbDiff : b ∈ X.neighborFinset a ∆ Y.neighborFinset a := by
        rw [hdiff]
        simp
      have hcDiff : c ∈ X.neighborFinset a ∆ Y.neighborFinset a := by
        rw [hdiff]
        simp
      have hbY : b ∉ Y.neighborFinset a := by
        intro hbY
        simp [Finset.mem_symmDiff, hbX, hbY] at hbDiff
      have hcY : c ∉ Y.neighborFinset a := by
        intro hcY
        simp [Finset.mem_symmDiff, hcX, hcY] at hcDiff
      have hpairsSub : {b, c} ⊆ X.neighborFinset a \ Y.neighborFinset a := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_sdiff.mpr ⟨hbX, hbY⟩
        · exact Finset.mem_sdiff.mpr ⟨hcX, hcY⟩
      have hle := Finset.card_le_card hpairsSub
      have hpairsCard : ({b, c} : Finset V).card = 2 := by simp [hbc]
      omega
    · intro hcX
      by_contra hbX
      have hempty : X.neighborFinset a \ Y.neighborFinset a = ∅ := by
        ext z
        constructor
        · intro hz
          have hzPair := hXonlySub hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hzPair
          rcases hzPair with rfl | rfl
          · exact (hbX (Finset.mem_sdiff.mp hz).1).elim
          · exact (hcX (Finset.mem_sdiff.mp hz).1).elim
        · simp
      rw [hempty] at hXonlyCard
      simp at hXonlyCard
  have huOpp := oppositeAt u v w hvw huDiff
  have hvOpp := oppositeAt v u w huw hvDiff
  have hwOpp := oppositeAt w u v huv hwDiff
  have huAdj : X.graph.Adj u v ↔ ¬ X.graph.Adj u w := by
    simpa only [Realization.mem_neighborFinset] using huOpp
  have hvOppAdj : X.graph.Adj v u ↔ ¬ X.graph.Adj v w := by
    simpa only [Realization.mem_neighborFinset] using hvOpp
  have hwOppAdj : X.graph.Adj w u ↔ ¬ X.graph.Adj w v := by
    simpa only [Realization.mem_neighborFinset] using hwOpp
  have hvAdj : X.graph.Adj u v ↔ ¬ X.graph.Adj v w := by
    constructor
    · intro h
      exact hvOppAdj.mp h.symm
    · intro h
      exact (hvOppAdj.mpr h).symm
  have hwAdj : X.graph.Adj u w ↔ ¬ X.graph.Adj v w := by
    constructor
    · intro h
      intro h'
      exact (hwOppAdj.mp h.symm) h'.symm
    · intro h
      apply (hwOppAdj.mpr ?_).symm
      intro h'
      exact h h'.symm
  by_cases hUV : X.graph.Adj u v
  · have hUW : ¬ X.graph.Adj u w := huAdj.mp hUV
    have hVW : ¬ X.graph.Adj v w := hvAdj.mp hUV
    exact hUW (hwAdj.mpr hVW)
  · have hUW : X.graph.Adj u w := by
      by_contra h
      exact hUV (huAdj.mpr h)
    have hVW : X.graph.Adj v w := by
      by_contra h
      exact hUV (hvAdj.mpr h)
    exact (hwAdj.mp hUW) hVW

/-! ## 4b. §6's triangle trichotomy and the reduction to a common core

The separator-buffer theorem (§6, `separator_buffer`) is not one argument but four: the reduction of
§6.1, the triangle classification of §6.2, the rich four-core lemma of §6.3, and the split branch of
§6.4. Stating its pieces separately made it provable in stages and keeps the dependency structure
visible in the completed assembly.

**Verified before being stated**, `compute/sec6_steps_check_2026_08_18.py` through ground order 7:
**179,442 triangles and 2,411,461 realization pairs, 0 failures** on every claim below. The type
counts are 13,495 / 152,452 / 13,495 — Types I and III equal, which is the complementation duality
§6.3 uses, arrived at by counting rather than by the argument, at two separate orders.
-/

/-- The **ground support** of a set of edges: the vertices it touches. §6 works with the support of
`E(X) ∆ E(Y)` for a pair and of the union of a triangle's two switches. -/
noncomputable def edgeSupport (E : Finset (Sym2 V)) : Finset V :=
  Finset.univ.filter (fun v => ∃ e ∈ E, v ∈ e)

private theorem edgeSupport_union_eq (E F : Finset (Sym2 V)) :
    edgeSupport (E ∪ F) = edgeSupport E ∪ edgeSupport F := by
  classical
  ext v
  simp only [edgeSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union]
  constructor
  · rintro ⟨e, he, hve⟩
    rcases he with he | he
    · exact Or.inl ⟨e, he, hve⟩
    · exact Or.inr ⟨e, he, hve⟩
  · rintro (⟨e, he, hve⟩ | ⟨e, he, hve⟩)
    · exact ⟨e, Or.inl he, hve⟩
    · exact ⟨e, Or.inr he, hve⟩

private theorem edgeSupport_mono {E F : Finset (Sym2 V)} (hEF : E ⊆ F) :
    edgeSupport E ⊆ edgeSupport F := by
  classical
  intro v hv
  simp only [edgeSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  obtain ⟨e, he, hve⟩ := hv
  exact ⟨e, hEF he, hve⟩

private theorem edgeSupport_symmDiff_eq_support {d : V → ℕ} (G H : Realization d) :
    edgeSupport (G.edgeFinset ∆ H.edgeFinset) =
      (edgeDifferenceGraph G H).support.toFinset := by
  classical
  ext v
  simp only [edgeSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Set.mem_toFinset, SimpleGraph.mem_support]
  constructor
  · rintro ⟨e, he, hve⟩
    rw [Sym2.mem_iff_exists] at hve
    obtain ⟨w, rfl⟩ := hve
    refine ⟨w, ?_⟩
    have hedge : s(v, w) ∈ (edgeDifferenceGraph G H).edgeFinset := by
      rw [edgeDifferenceGraph_edgeFinset]
      exact he
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hedge
  · rintro ⟨w, hvw⟩
    refine ⟨s(v, w), ?_, Sym2.mem_mk_left v w⟩
    rw [← edgeDifferenceGraph_edgeFinset]
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hvw

private theorem three_le_edgeSupport_of_card_eq_two {E : Finset (Sym2 V)}
    (hcard : E.card = 2) (hnondiag : ∀ e ∈ E, ¬ e.IsDiag) :
    3 ≤ (edgeSupport E).card := by
  classical
  obtain ⟨e, f, hef, hE⟩ := Finset.card_eq_two.mp hcard
  have he_nondiag : ¬ e.IsDiag := hnondiag e (by simp [hE])
  have hf_nondiag : ¬ f.IsDiag := hnondiag f (by simp [hE])
  have hecard : e.toFinset.card = 2 := Sym2.card_toFinset_of_not_isDiag e he_nondiag
  have hfcard : f.toFinset.card = 2 := Sym2.card_toFinset_of_not_isDiag f hf_nondiag
  have hsupp : edgeSupport E = e.toFinset ∪ f.toFinset := by
    rw [hE]
    ext v
    simp [edgeSupport, Sym2.mem_toFinset]
  rw [hsupp]
  by_contra hlt
  have hunion_le : (e.toFinset ∪ f.toFinset).card ≤ 2 := by omega
  have heSub : e.toFinset ⊆ e.toFinset ∪ f.toFinset := Finset.subset_union_left
  have hfSub : f.toFinset ⊆ e.toFinset ∪ f.toFinset := Finset.subset_union_right
  have heEq : e.toFinset = e.toFinset ∪ f.toFinset :=
    Finset.eq_of_subset_of_card_le heSub (by omega)
  have hfEq : f.toFinset = e.toFinset ∪ f.toFinset :=
    Finset.eq_of_subset_of_card_le hfSub (by omega)
  apply hef
  apply Sym2.ext
  intro v
  simpa only [Sym2.mem_toFinset] using
    Finset.ext_iff.mp (heEq.trans hfEq.symm) v

/-- **§6.2, the arithmetic of a triangle.** For a triangle `G, G₁, G₂` of the realization graph, put
`Δᵢ = E(G) ∆ E(Gᵢ)`. All three pairs are 2-switch adjacent, so `|Δ₁| = |Δ₂| = |Δ₁ ∆ Δ₂| = 4`, and
that forces the two switches to share exactly two edges. Everything in §6.2's classification rests on
this count. -/
theorem triangle_switches_share_two {d : V → ℕ} {G G₁ G₂ : Realization d}
    (h1 : (RealizationGraph d).Adj G G₁) (h2 : (RealizationGraph d).Adj G G₂)
    (h12 : (RealizationGraph d).Adj G₁ G₂) :
    ((G.edgeFinset ∆ G₁.edgeFinset) ∩ (G.edgeFinset ∆ G₂.edgeFinset)).card = 2 := by
  classical
  let A := G.edgeFinset ∆ G₁.edgeFinset
  let B := G.edgeFinset ∆ G₂.edgeFinset
  have hA : A.card = 4 := h1
  have hB : B.card = 4 := h2
  have hchain : A ∆ B = G₁.edgeFinset ∆ G₂.edgeFinset := by
    calc
      A ∆ B = (G.edgeFinset ∆ G₁.edgeFinset) ∆
          (G.edgeFinset ∆ G₂.edgeFinset) := rfl
      _ = (G.edgeFinset ∆ G.edgeFinset) ∆
          (G₁.edgeFinset ∆ G₂.edgeFinset) :=
        symmDiff_symmDiff_symmDiff_comm G.edgeFinset G₁.edgeFinset
          G.edgeFinset G₂.edgeFinset
      _ = G₁.edgeFinset ∆ G₂.edgeFinset := by simp
  have hAB : (A ∆ B).card = 4 := by
    rw [hchain]
    exact h12
  have hsplitA : (A \ B).card + (A ∩ B).card = A.card :=
    Finset.card_sdiff_add_card_inter A B
  have hsplitB : (B \ A).card + (B ∩ A).card = B.card :=
    Finset.card_sdiff_add_card_inter B A
  have hsymm : (A ∆ B).card = (A \ B).card + (B \ A).card := by
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint]
    exact Finset.sdiff_disjoint.mono_right Finset.sdiff_subset
  have hinter : (A ∩ B).card = (B ∩ A).card := by rw [Finset.inter_comm]
  rw [hA] at hsplitA
  rw [hB] at hsplitB
  rw [hAB] at hsymm
  change (A ∩ B).card = 2
  omega

/-- **§6.2, the classification.** Every triangle of the realization graph has ground support of size
four or five: four when the two shared edges are both present in `G` or both absent — the **rich**
Types I and III — and five when one is present and one absent, Type II.

Only the size claim is stated, because only it is used: §6.1 needs that a triangle support is never
larger than five, and §6.3 needs that a rich one has exactly four vertices. -/
theorem triangle_support_card_four_or_five {d : V → ℕ} {G G₁ G₂ : Realization d}
    (h1 : (RealizationGraph d).Adj G G₁) (h2 : (RealizationGraph d).Adj G G₂)
    (h12 : (RealizationGraph d).Adj G₁ G₂) :
    (edgeSupport ((G.edgeFinset ∆ G₁.edgeFinset) ∪ (G.edgeFinset ∆ G₂.edgeFinset))).card = 4 ∨
      (edgeSupport ((G.edgeFinset ∆ G₁.edgeFinset) ∪ (G.edgeFinset ∆ G₂.edgeFinset))).card = 5 := by
  classical
  let A := G.edgeFinset ∆ G₁.edgeFinset
  let B := G.edgeFinset ∆ G₂.edgeFinset
  have hshared : (A ∩ B).card = 2 := by
    exact triangle_switches_share_two h1 h2 h12
  have hASupport : (edgeSupport A).card = 4 := by
    rw [show A = G.edgeFinset ∆ G₁.edgeFinset from rfl,
      edgeSupport_symmDiff_eq_support]
    exact (twoSwitchAdjacent_is_alternating_cycle h1).1
  have hBSupport : (edgeSupport B).card = 4 := by
    rw [show B = G.edgeFinset ∆ G₂.edgeFinset from rfl,
      edgeSupport_symmDiff_eq_support]
    exact (twoSwitchAdjacent_is_alternating_cycle h2).1
  have hshared_nondiag : ∀ e ∈ A ∩ B, ¬ e.IsDiag := by
    intro e he
    have heA : e ∈ G.edgeFinset ∆ G₁.edgeFinset :=
      (Finset.mem_inter.mp he).1
    rcases Finset.mem_symmDiff.mp heA with heG | heG₁
    · exact G.graph.not_isDiag_of_mem_edgeFinset heG.1
    · exact G₁.graph.not_isDiag_of_mem_edgeFinset heG₁.1
  have hsharedSupport : 3 ≤ (edgeSupport (A ∩ B)).card :=
    three_le_edgeSupport_of_card_eq_two hshared hshared_nondiag
  have hsupportSub : edgeSupport (A ∩ B) ⊆ edgeSupport A ∩ edgeSupport B := by
    intro v hv
    exact Finset.mem_inter.mpr
      ⟨edgeSupport_mono Finset.inter_subset_left hv,
        edgeSupport_mono Finset.inter_subset_right hv⟩
  have hinterLower : 3 ≤ (edgeSupport A ∩ edgeSupport B).card := by
    exact hsharedSupport.trans (Finset.card_le_card hsupportSub)
  have hinterUpper : (edgeSupport A ∩ edgeSupport B).card ≤ 4 := by
    have hle := Finset.card_le_card (Finset.inter_subset_left :
      edgeSupport A ∩ edgeSupport B ⊆ edgeSupport A)
    omega
  have hunionCard := Finset.card_union_add_card_inter (edgeSupport A) (edgeSupport B)
  rw [hASupport, hBSupport] at hunionCard
  change (edgeSupport (A ∪ B)).card = 4 ∨ (edgeSupport (A ∪ B)).card = 5
  rw [edgeSupport_union_eq]
  omega

private theorem realization_eq_of_edgeFinset_eq {d : V → ℕ} {G H : Realization d}
    (h : G.edgeFinset = H.edgeFinset) : G = H := by
  have hgraph : G.graph = H.graph := by
    ext x y
    have hmem : s(x, y) ∈ G.edgeFinset ↔ s(x, y) ∈ H.edgeFinset := by rw [h]
    simpa [Realization.edgeFinset, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet] using hmem
  cases G with
  | mk graphG decG degreeG =>
      cases H with
      | mk graphH decH degreeH =>
          dsimp at hgraph
          subst graphH
          congr
          exact Subsingleton.elim _ _

private theorem realization_neighbor_card_eq {d : V → ℕ}
    (G H : Realization d) (v : V) :
    (G.neighborFinset v).card = (H.neighborFinset v).card := by
  classical
  simp [Realization.neighborFinset, SimpleGraph.card_neighborFinset_eq_degree,
    G.degree_eq v, H.degree_eq v]

private theorem edgeDifference_degree_eq_twice_local {d : V → ℕ}
    (G H : Realization d) (v : V) :
    (edgeDifferenceGraph G H).degree v =
      2 * (G.neighborFinset v \ H.neighborFinset v).card := by
  classical
  rw [SimpleGraph.degree, edgeDifferenceGraph_neighborFinset]
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint]
  · have hcards := Finset.card_sdiff_comm (realization_neighbor_card_eq G H v)
    omega
  · exact Finset.sdiff_disjoint.mono_right Finset.sdiff_subset

private theorem realization_edgeFinset_card_eq {d : V → ℕ} (G H : Realization d) :
    G.edgeFinset.card = H.edgeFinset.card := by
  classical
  have hGsum := G.graph.sum_degrees_eq_twice_card_edges
  have hHsum := H.graph.sum_degrees_eq_twice_card_edges
  have hsums : (∑ v, G.graph.degree v) = ∑ v, H.graph.degree v := by
    apply Finset.sum_congr rfl
    intro v _hv
    rw [G.degree_eq v, H.degree_eq v]
  change G.graph.edgeFinset.card = H.graph.edgeFinset.card
  omega

/-- **§6.1, the lower bound.** The difference support of two distinct realizations has at least four
vertices. `E(X) ∆ E(Y)` is balanced at every ground vertex, so it decomposes into alternating closed
trails, and the shortest of those already meets four vertices. -/
theorem differenceSupport_card_ge_four {d : V → ℕ} {X Y : Realization d} (hXY : X ≠ Y) :
    4 ≤ (edgeSupport (X.edgeFinset ∆ Y.edgeFinset)).card := by
  classical
  let D : SimpleGraph V := edgeDifferenceGraph X Y
  have hedgeNe : X.edgeFinset ≠ Y.edgeFinset := by
    intro h
    exact hXY (realization_eq_of_edgeFinset_eq h)
  have hDedge : D.edgeFinset = X.edgeFinset ∆ Y.edgeFinset := by
    exact edgeDifferenceGraph_edgeFinset X Y
  have hDnonempty : D.edgeFinset.Nonempty := by
    rw [hDedge]
    exact Finset.symmDiff_nonempty.mpr hedgeNe
  have hDcardPos : 0 < D.edgeFinset.card := Finset.card_pos.mpr hDnonempty
  have hsuppPos : 0 < D.support.toFinset.card := by
    obtain ⟨e, he⟩ := hDnonempty
    induction e using Sym2.inductionOn with
    | _ v w =>
        have hvw : D.Adj v w := by
          simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
        exact Finset.card_pos.mpr ⟨v, Set.mem_toFinset.mpr ⟨w, hvw⟩⟩
  have hdegree (v : V) :
      D.degree v = 2 * (X.neighborFinset v \ Y.neighborFinset v).card := by
    exact edgeDifference_degree_eq_twice_local X Y v
  have hdegLower : ∀ v ∈ D.support, 2 ≤ D.degree v := by
    intro v hv
    have hpos : 0 < D.degree v := (D.degree_pos_iff_mem_support v).2 hv
    rw [hdegree] at hpos ⊢
    omega
  have hsum : ∑ v ∈ D.support.toFinset, D.degree v = 2 * D.edgeFinset.card :=
    D.sum_degrees_support_eq_twice_card_edges
  have hlower : 2 * D.support.toFinset.card ≤
      ∑ v ∈ D.support.toFinset, D.degree v := by
    calc
      2 * D.support.toFinset.card = ∑ _v ∈ D.support.toFinset, 2 := by
        simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ D.support.toFinset, D.degree v := by
        exact Finset.sum_le_sum fun v hv ↦ hdegLower v (Set.mem_toFinset.mp hv)
  have hedgeBound : D.edgeFinset.card ≤ (Fintype.card D.support).choose 2 := by
    have h := (D.induce D.support).card_edgeFinset_le_card_choose_two
    rw [D.card_edgeFinset_induce_support] at h
    exact h
  have hcardType : Fintype.card D.support = D.support.toFinset.card := by simp
  rw [hcardType] at hedgeBound
  have hbalanced := Finset.card_sdiff_comm (realization_edgeFinset_card_eq X Y)
  have hDtwice : D.edgeFinset.card =
      2 * (X.edgeFinset \ Y.edgeFinset).card := by
    rw [hDedge, Finset.symmDiff_def, Finset.card_union_of_disjoint]
    · omega
    · exact Finset.sdiff_disjoint.mono_right Finset.sdiff_subset
  have hedgeLower : D.support.toFinset.card ≤ D.edgeFinset.card := by omega
  have hDcardNeThree : D.edgeFinset.card ≠ 3 := by
    intro hthree
    rw [hthree] at hDtwice
    omega
  have hsuppGe : 4 ≤ D.support.toFinset.card := by
    by_contra h
    have hsuppLe : D.support.toFinset.card ≤ 3 := by omega
    have hcases : D.support.toFinset.card = 0 ∨ D.support.toFinset.card = 1 ∨
        D.support.toFinset.card = 2 ∨ D.support.toFinset.card = 3 := by
      omega
    rcases hcases with hzero | hone | htwo | hthree
    · exact (Nat.ne_of_gt hsuppPos) hzero
    · rw [hone] at hedgeBound
      have hcap : D.edgeFinset.card ≤ 0 := by simpa using hedgeBound
      exact (Nat.not_lt_of_ge hcap) hDcardPos
    · rw [htwo] at hedgeBound
      have hcap : D.edgeFinset.card ≤ 1 := by simpa using hedgeBound
      have hlow : 2 ≤ D.edgeFinset.card := by simpa [htwo] using hedgeLower
      have : 2 ≤ 1 := hlow.trans hcap
      omega
    · rw [hthree] at hedgeBound
      have hcap : D.edgeFinset.card ≤ 3 := by simpa using hedgeBound
      have hlow : 3 ≤ D.edgeFinset.card := by simpa [hthree] using hedgeLower
      have hcardThree : D.edgeFinset.card = 3 := Nat.le_antisymm hcap hlow
      exact hDcardNeThree hcardThree
  rw [edgeSupport_symmDiff_eq_support]
  exact hsuppGe

/-- **A rich triangle**: a triangle of the realization graph whose ground support has four vertices.
By the classification of §6.2 those are exactly the manuscript's Types I and III — both shared edges
removed, or both added — and Type II is the five-vertex case. Defining richness by the support size
rather than by the type avoids naming the types, which nothing below needs. -/
def IsRichTriangle (d : V → ℕ) (G G₁ G₂ : Realization d) : Prop :=
  (RealizationGraph d).Adj G G₁ ∧ (RealizationGraph d).Adj G G₂ ∧ (RealizationGraph d).Adj G₁ G₂ ∧
    (edgeSupport ((G.edgeFinset ∆ G₁.edgeFinset) ∪ (G.edgeFinset ∆ G₂.edgeFinset))).card = 4

/-! ### Local switch certificates used by the rich four-core argument -/

private def FourDistinct (a b c e : V) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ e ∧ b ≠ c ∧ b ≠ e ∧ c ≠ e

private def FiveDistinct (x y z t u : V) : Prop :=
  x ≠ y ∧ x ≠ z ∧ x ≠ t ∧ x ≠ u ∧ y ≠ z ∧ y ≠ t ∧ y ≠ u ∧
    z ≠ t ∧ z ≠ u ∧ t ≠ u

private def InducesMatching (G : SimpleGraph V) (a b c e : V) : Prop :=
  G.Adj a b ∧ G.Adj c e ∧ ¬ G.Adj a c ∧ ¬ G.Adj a e ∧
    ¬ G.Adj b c ∧ ¬ G.Adj b e

private def InducesFourCycle (G : SimpleGraph V) (a b c e : V) : Prop :=
  ¬ G.Adj a b ∧ ¬ G.Adj c e ∧ G.Adj a c ∧ G.Adj a e ∧
    G.Adj b c ∧ G.Adj b e

private structure FourCode where
  b₀ : Bool
  b₁ : Bool
  b₂ : Bool
  b₃ : Bool
  b₄ : Bool
  b₅ : Bool
  deriving DecidableEq, Fintype

private def FourCode.ofFun (f : Fin 6 → Bool) : FourCode :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5⟩

private def FourCode.get (A : FourCode) : Fin 6 → Bool
  | 0 => A.b₀
  | 1 => A.b₁
  | 2 => A.b₂
  | 3 => A.b₃
  | 4 => A.b₄
  | 5 => A.b₅

private instance : CoeFun FourCode (fun _ => Fin 6 → Bool) := ⟨FourCode.get⟩

private def fourCodeDegree (A : FourCode) : Fin 4 → Nat
  | 0 => (A 0).toNat + (A 1).toNat + (A 2).toNat
  | 1 => (A 0).toNat + (A 3).toNat + (A 4).toNat
  | 2 => (A 1).toNat + (A 3).toNat + (A 5).toNat
  | 3 => (A 2).toNat + (A 4).toNat + (A 5).toNat

private def matchingCode₀ : FourCode := FourCode.ofFun fun i => i = 0 || i = 5
private def matchingCode₁ : FourCode := FourCode.ofFun fun i => i = 1 || i = 4
private def matchingCode₂ : FourCode := FourCode.ofFun fun i => i = 2 || i = 3

private def codeComplement (A : FourCode) : FourCode := FourCode.ofFun fun i => !(A i)

private def IsMatchingCodeTriple (A B C : FourCode) : Prop :=
  ({A, B, C} : Finset FourCode) = {matchingCode₀, matchingCode₁, matchingCode₂}

private def IsCycleCodeTriple (A B C : FourCode) : Prop :=
  ({A, B, C} : Finset FourCode) =
    {codeComplement matchingCode₀, codeComplement matchingCode₁,
      codeComplement matchingCode₂}

private instance (A B C : FourCode) : Decidable (IsMatchingCodeTriple A B C) := by
  unfold IsMatchingCodeTriple
  infer_instance

private instance (A B C : FourCode) : Decidable (IsCycleCodeTriple A B C) := by
  unfold IsCycleCodeTriple
  infer_instance

private instance finiteForallDecidable {α : Type*} [Fintype α]
    {p : α → Prop} [DecidablePred p] : Decidable (∀ x, p x) :=
  Fintype.decidableForallFintype

private def finiteDecidableForall {α : Type*} [Fintype α] {p : α → Prop}
    (h : ∀ x, Decidable (p x)) : Decidable (∀ x, p x) :=
  @Fintype.decidableForallFintype α p h _

private def orientedSwitch₀₁ (A B : FourCode) : Bool :=
  A 0 && A 5 && !(A 1) && !(A 4) &&
  !(B 0) && !(B 5) && B 1 && B 4 &&
  (A 2 == B 2) && (A 3 == B 3)

private def orientedSwitch₀₂ (A B : FourCode) : Bool :=
  A 0 && A 5 && !(A 2) && !(A 3) &&
  !(B 0) && !(B 5) && B 2 && B 3 &&
  (A 1 == B 1) && (A 4 == B 4)

private def orientedSwitch₁₂ (A B : FourCode) : Bool :=
  A 1 && A 4 && !(A 2) && !(A 3) &&
  !(B 1) && !(B 4) && B 2 && B 3 &&
  (A 0 == B 0) && (A 5 == B 5)

private def fourCodeSwitch (A B : FourCode) : Bool :=
  orientedSwitch₀₁ A B || orientedSwitch₀₁ B A ||
  orientedSwitch₀₂ A B || orientedSwitch₀₂ B A ||
  orientedSwitch₁₂ A B || orientedSwitch₁₂ B A

private def PairCodeClassifierProp : Prop :=
  ∀ A B : FourCode,
    fourCodeDegree A = fourCodeDegree B →
    (Finset.univ.filter fun i => A i != B i).card = 4 →
    fourCodeSwitch A B = true

private instance : Decidable PairCodeClassifierProp :=
  finiteDecidableForall fun _ => finiteDecidableForall fun _ => inferInstance

set_option maxRecDepth 100000 in
private theorem pair_code_classifier : PairCodeClassifierProp := by
  decide

private def SwitchTriangleClassifierProp : Prop :=
  ∀ A B C : FourCode,
    fourCodeSwitch A B = true →
    fourCodeSwitch A C = true →
    fourCodeSwitch B C = true →
    IsMatchingCodeTriple A B C ∨ IsCycleCodeTriple A B C

private instance : Decidable SwitchTriangleClassifierProp :=
  finiteDecidableForall fun _ => finiteDecidableForall fun _ =>
    finiteDecidableForall fun _ => inferInstance

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
private theorem switch_triangle_classifier : SwitchTriangleClassifierProp := by
  decide

private def FourCodeClassifierProp : Prop :=
    ∀ A B C : FourCode,
      fourCodeDegree A = fourCodeDegree B →
      fourCodeDegree A = fourCodeDegree C →
      ((Finset.univ.filter fun i => A i != B i).card = 4) →
      ((Finset.univ.filter fun i => A i != C i).card = 4) →
      ((Finset.univ.filter fun i => B i != C i).card = 4) →
      IsMatchingCodeTriple A B C ∨ IsCycleCodeTriple A B C

private instance : Decidable FourCodeClassifierProp :=
  finiteDecidableForall fun _ => finiteDecidableForall fun _ =>
    finiteDecidableForall fun _ => inferInstance

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 100000 in
private theorem four_code_classifier : FourCodeClassifierProp := by
  intro A B C hdegAB hdegAC hcardAB hcardAC hcardBC
  exact switch_triangle_classifier A B C
    (pair_code_classifier A B hdegAB hcardAB)
    (pair_code_classifier A C hdegAC hcardAC)
    (pair_code_classifier B C (hdegAB.symm.trans hdegAC) hcardBC)

private theorem finset_three_ordered {α : Type*} [DecidableEq α]
    (x y z A B C : α) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hset : ({A, B, C} : Finset α) = {x, y, z}) :
    (A = x ∧ ((B = y ∧ C = z) ∨ (B = z ∧ C = y))) ∨
    (A = y ∧ ((B = x ∧ C = z) ∨ (B = z ∧ C = x))) ∨
    (A = z ∧ ((B = x ∧ C = y) ∨ (B = y ∧ C = x))) := by
  have hA : A = x ∨ A = y ∨ A = z := by
    have hm : A ∈ ({x, y, z} : Finset α) := by
      rw [← hset]
      simp
    simpa using hm
  rcases hA with hA | hA | hA
  · subst A
    have hy : B = y ∨ C = y := by
      have hm : y ∈ ({x, B, C} : Finset α) := by rw [hset]; simp
      simpa [hxy, eq_comm] using hm
    have hz : B = z ∨ C = z := by
      have hm : z ∈ ({x, B, C} : Finset α) := by rw [hset]; simp
      simpa [hxz, eq_comm] using hm
    rcases hy with hy | hy <;> rcases hz with hz | hz <;> simp_all
  · subst A
    have hx : B = x ∨ C = x := by
      have hm : x ∈ ({y, B, C} : Finset α) := by rw [hset]; simp
      simpa [hxy, eq_comm] using hm
    have hz : B = z ∨ C = z := by
      have hm : z ∈ ({y, B, C} : Finset α) := by rw [hset]; simp
      simpa [hyz, eq_comm] using hm
    rcases hx with hx | hx <;> rcases hz with hz | hz <;> simp_all
  · subst A
    have hx : B = x ∨ C = x := by
      have hm : x ∈ ({z, B, C} : Finset α) := by rw [hset]; simp
      simpa [hxz, eq_comm] using hm
    have hy : B = y ∨ C = y := by
      have hm : y ∈ ({z, B, C} : Finset α) := by rw [hset]; simp
      simpa [hyz, eq_comm] using hm
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp_all

private def MatchingCodeOrderedProp : Prop :=
    ∀ A B C : FourCode, IsMatchingCodeTriple A B C →
      (A = matchingCode₀ ∧
          ((B = matchingCode₁ ∧ C = matchingCode₂) ∨
            (B = matchingCode₂ ∧ C = matchingCode₁))) ∨
      (A = matchingCode₁ ∧
          ((B = matchingCode₀ ∧ C = matchingCode₂) ∨
            (B = matchingCode₂ ∧ C = matchingCode₀))) ∨
      (A = matchingCode₂ ∧
          ((B = matchingCode₀ ∧ C = matchingCode₁) ∨
            (B = matchingCode₁ ∧ C = matchingCode₀)))

private instance : Decidable MatchingCodeOrderedProp :=
  finiteDecidableForall fun _ => finiteDecidableForall fun _ =>
    finiteDecidableForall fun _ => inferInstance

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 100000 in
private theorem matching_code_ordered : MatchingCodeOrderedProp := by
  intro A B C h
  exact finset_three_ordered matchingCode₀ matchingCode₁ matchingCode₂ A B C
    (by decide) (by decide) (by decide) h

private def CycleCodeOrderedProp : Prop :=
    ∀ A B C : FourCode, IsCycleCodeTriple A B C →
      (A = codeComplement matchingCode₀ ∧
          ((B = codeComplement matchingCode₁ ∧
              C = codeComplement matchingCode₂) ∨
            (B = codeComplement matchingCode₂ ∧
              C = codeComplement matchingCode₁))) ∨
      (A = codeComplement matchingCode₁ ∧
          ((B = codeComplement matchingCode₀ ∧
              C = codeComplement matchingCode₂) ∨
            (B = codeComplement matchingCode₂ ∧
              C = codeComplement matchingCode₀))) ∨
      (A = codeComplement matchingCode₂ ∧
          ((B = codeComplement matchingCode₀ ∧
              C = codeComplement matchingCode₁) ∨
            (B = codeComplement matchingCode₁ ∧
              C = codeComplement matchingCode₀)))

private instance : Decidable CycleCodeOrderedProp :=
  finiteDecidableForall fun _ => finiteDecidableForall fun _ =>
    finiteDecidableForall fun _ => inferInstance

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 100000 in
private theorem cycle_code_ordered : CycleCodeOrderedProp := by
  intro A B C h
  exact finset_three_ordered (codeComplement matchingCode₀)
    (codeComplement matchingCode₁) (codeComplement matchingCode₂) A B C
    (by decide) (by decide) (by decide) h

/- The three closed propositions above deliberately carry their decision procedures as named
instances, so `decide` can check them in the kernel even though this file imports a module which
locally disables Mathlib's generic finite-forall instance. -/

private def coreVertex (a b c e : V) : Fin 4 → V
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => e

private def coreEdge (a b c e : V) : Fin 6 → Sym2 V
  | 0 => s(a, b)
  | 1 => s(a, c)
  | 2 => s(a, e)
  | 3 => s(b, c)
  | 4 => s(b, e)
  | 5 => s(c, e)

private noncomputable def fourCodeOf {d : V → ℕ} (G : Realization d)
    (a b c e : V) : FourCode :=
  FourCode.ofFun fun i => decide (coreEdge a b c e i ∈ G.edgeFinset)

private theorem decide_bne_eq_true_iff {p q : Prop} [Decidable p] [Decidable q] :
    (decide p != decide q) = true ↔ (p ∧ ¬ q) ∨ (q ∧ ¬ p) := by
  by_cases hp : p <;> by_cases hq : q <;> simp_all

private theorem fourCode_ext {A B : FourCode} (h : ∀ i, A i = B i) : A = B := by
  cases A with
  | mk a₀ a₁ a₂ a₃ a₄ a₅ =>
      cases B with
      | mk b₀ b₁ b₂ b₃ b₄ b₅ =>
          have h₀ := h (0 : Fin 6)
          have h₁ := h (1 : Fin 6)
          have h₂ := h (2 : Fin 6)
          have h₃ := h (3 : Fin 6)
          have h₄ := h (4 : Fin 6)
          have h₅ := h (5 : Fin 6)
          simp only [FourCode.get] at h₀ h₁ h₂ h₃ h₄ h₅
          subst b₀; subst b₁; subst b₂; subst b₃; subst b₄; subst b₅
          rfl

private theorem coreEdge_injective {a b c e : V} (hdist : FourDistinct a b c e) :
    Function.Injective (coreEdge a b c e) := by
  rcases hdist with ⟨hab, hac, hae, hbc, hbe, hce⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [coreEdge, Sym2.eq_iff] <;> aesop

private theorem edge_mem_six_of_support_subset {E : Finset (Sym2 V)} {f : Sym2 V}
    {a b c e : V} (hf : f ∈ E) (hnondiag : ¬ f.IsDiag)
    (hsub : edgeSupport E ⊆ {a, b, c, e}) :
    f ∈ ({s(a, b), s(a, c), s(a, e), s(b, c), s(b, e), s(c, e)} :
      Finset (Sym2 V)) := by
  induction f using Sym2.inductionOn with
  | _ x y =>
      have hxS : x ∈ ({a, b, c, e} : Finset V) := hsub (by
        simp only [edgeSupport, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨s(x, y), hf, Sym2.mem_mk_left x y⟩)
      have hyS : y ∈ ({a, b, c, e} : Finset V) := hsub (by
        simp only [edgeSupport, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨s(x, y), hf, Sym2.mem_mk_right x y⟩)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxS hyS ⊢
      rcases hxS with rfl | rfl | rfl | rfl <;>
        rcases hyS with rfl | rfl | rfl | rfl <;>
        simp_all [Sym2.eq_iff]

private theorem fourCode_distance_eq {d : V → ℕ} (A B : Realization d)
    {a b c e : V} (hdist : FourDistinct a b c e)
    (hsub : edgeSupport (A.edgeFinset ∆ B.edgeFinset) ⊆ {a, b, c, e}) :
    (Finset.univ.filter fun i =>
      fourCodeOf A a b c e i != fourCodeOf B a b c e i).card =
      (A.edgeFinset ∆ B.edgeFinset).card := by
  classical
  have hmap (i : Fin 6) :
      i ∈ Finset.univ.filter (fun i =>
        fourCodeOf A a b c e i != fourCodeOf B a b c e i) ↔
      coreEdge a b c e i ∈ A.edgeFinset ∆ B.edgeFinset := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases i <;>
      simp [fourCodeOf, FourCode.ofFun, FourCode.get, coreEdge,
        decide_bne_eq_true_iff, Finset.mem_symmDiff]
    all_goals tauto
  apply Finset.card_bij (fun i _ => coreEdge a b c e i)
  · intro i hi
    exact (hmap i).mp hi
  · intro i hi j hj hij
    exact coreEdge_injective hdist hij
  · intro f hf
    have hnondiag : ¬ f.IsDiag := by
      rcases Finset.mem_symmDiff.mp hf with hfA | hfB
      · exact A.graph.not_isDiag_of_mem_edgeFinset hfA.1
      · exact B.graph.not_isDiag_of_mem_edgeFinset hfB.1
    have hsix := edge_mem_six_of_support_subset hf hnondiag hsub
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsix
    rcases hsix with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨0, (hmap 0).mpr ?_, rfl⟩
      simpa [coreEdge] using hf
    · refine ⟨1, (hmap 1).mpr ?_, rfl⟩
      simpa [coreEdge] using hf
    · refine ⟨2, (hmap 2).mpr ?_, rfl⟩
      simpa [coreEdge] using hf
    · refine ⟨3, (hmap 3).mpr ?_, rfl⟩
      simpa [coreEdge] using hf
    · refine ⟨4, (hmap 4).mpr ?_, rfl⟩
      simpa [coreEdge] using hf
    · refine ⟨5, (hmap 5).mpr ?_, rfl⟩
      simpa [coreEdge] using hf

set_option maxHeartbeats 800000 in
private theorem fourCodeDegree_eq_internal_degree {d : V → ℕ} (G : Realization d)
    {a b c e : V} (hdist : FourDistinct a b c e) :
    fourCodeDegree (fourCodeOf G a b c e) = fun i =>
      (G.neighborFinset (coreVertex a b c e i) ∩ {a, b, c, e}).card := by
  classical
  rcases hdist with ⟨hab, hac, hae, hbc, hbe, hce⟩
  have hinter (v : V) : G.neighborFinset v ∩ ({a, b, c, e} : Finset V) =
      ({a, b, c, e} : Finset V).filter (fun x => G.graph.Adj v x) := by
    ext x
    simp [Realization.mem_neighborFinset]
    tauto
  funext i
  rw [hinter]
  fin_cases i
  · by_cases hAB : G.graph.Adj a b <;> by_cases hAC : G.graph.Adj a c <;>
      by_cases hAE : G.graph.Adj a e <;>
      simp_all [fourCodeDegree, fourCodeOf, FourCode.ofFun, FourCode.get, coreEdge,
        coreVertex, Realization.edgeFinset, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, Finset.filter_insert, Finset.filter_singleton]
  · by_cases hAB : G.graph.Adj a b <;> by_cases hBC : G.graph.Adj b c <;>
      by_cases hBE : G.graph.Adj b e <;>
      simp_all [fourCodeDegree, fourCodeOf, FourCode.ofFun, FourCode.get, coreEdge,
        coreVertex, Realization.edgeFinset, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, SimpleGraph.adj_comm, Finset.filter_insert,
        Finset.filter_singleton]
  · by_cases hAC : G.graph.Adj a c <;> by_cases hBC : G.graph.Adj b c <;>
      by_cases hCE : G.graph.Adj c e <;>
      simp_all [fourCodeDegree, fourCodeOf, FourCode.ofFun, FourCode.get, coreEdge,
        coreVertex, Realization.edgeFinset, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, SimpleGraph.adj_comm, Finset.filter_insert,
        Finset.filter_singleton]
  · by_cases hAE : G.graph.Adj a e <;> by_cases hBE : G.graph.Adj b e <;>
      by_cases hCE : G.graph.Adj c e <;>
      simp_all [fourCodeDegree, fourCodeOf, FourCode.ofFun, FourCode.get, coreEdge,
        coreVertex, Realization.edgeFinset, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, SimpleGraph.adj_comm, Finset.filter_insert,
        Finset.filter_singleton]

private theorem neighbor_sdiff_eq_of_support_subset {d : V → ℕ}
    (A B : Realization d) (S : Finset V)
    (hsub : edgeSupport (A.edgeFinset ∆ B.edgeFinset) ⊆ S) (v : V) :
    A.neighborFinset v \ S = B.neighborFinset v \ S := by
  classical
  ext w
  simp only [Finset.mem_sdiff, Realization.mem_neighborFinset]
  constructor
  · rintro ⟨hvw, hwS⟩
    refine ⟨?_, hwS⟩
    by_contra hB
    apply hwS
    apply hsub
    simp only [edgeSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨s(v, w), ?_, Sym2.mem_mk_right v w⟩
    simp only [Finset.mem_symmDiff, Realization.edgeFinset,
      SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.adj_comm]
    exact Or.inl ⟨hvw, hB⟩
  · rintro ⟨hvw, hwS⟩
    refine ⟨?_, hwS⟩
    by_contra hA
    apply hwS
    apply hsub
    simp only [edgeSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨s(v, w), ?_, Sym2.mem_mk_right v w⟩
    simp only [Finset.mem_symmDiff, Realization.edgeFinset,
      SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.adj_comm]
    exact Or.inr ⟨hvw, hA⟩

private theorem internal_neighbor_card_eq_of_support_subset {d : V → ℕ}
    (A B : Realization d) (S : Finset V)
    (hsub : edgeSupport (A.edgeFinset ∆ B.edgeFinset) ⊆ S) (v : V) :
    (A.neighborFinset v ∩ S).card = (B.neighborFinset v ∩ S).card := by
  classical
  have hout := congrArg Finset.card
    (neighbor_sdiff_eq_of_support_subset A B S hsub v)
  have hA := Finset.card_inter_add_card_sdiff (A.neighborFinset v) S
  have hB := Finset.card_inter_add_card_sdiff (B.neighborFinset v) S
  have htotal := realization_neighbor_card_eq A B v
  omega

private theorem fourCodeDegree_eq_of_support_subset {d : V → ℕ}
    (A B : Realization d) {a b c e : V} (hdist : FourDistinct a b c e)
    (hsub : edgeSupport (A.edgeFinset ∆ B.edgeFinset) ⊆ {a, b, c, e}) :
    fourCodeDegree (fourCodeOf A a b c e) =
      fourCodeDegree (fourCodeOf B a b c e) := by
  rw [fourCodeDegree_eq_internal_degree A hdist,
    fourCodeDegree_eq_internal_degree B hdist]
  funext i
  exact internal_neighbor_card_eq_of_support_subset A B {a, b, c, e} hsub _

private theorem fourCode_matching₀_iff {d : V → ℕ} (G : Realization d)
    (a b c e : V) :
    fourCodeOf G a b c e = matchingCode₀ ↔ InducesMatching G.graph a b c e := by
  constructor
  · intro h
    have h0 := congrArg (fun A : FourCode => A (0 : Fin 6)) h
    have h1 := congrArg (fun A : FourCode => A (1 : Fin 6)) h
    have h2 := congrArg (fun A : FourCode => A (2 : Fin 6)) h
    have h3 := congrArg (fun A : FourCode => A (3 : Fin 6)) h
    have h4 := congrArg (fun A : FourCode => A (4 : Fin 6)) h
    have h5 := congrArg (fun A : FourCode => A (5 : Fin 6)) h
    simp [fourCodeOf, FourCode.ofFun, FourCode.get, coreEdge, matchingCode₀, Realization.edgeFinset,
      SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.adj_comm] at h0 h1 h2 h3 h4 h5
    exact ⟨h0, h5, h1, h2, h3, h4⟩
  · rintro ⟨h0, h5, h1, h2, h3, h4⟩
    apply fourCode_ext
    intro i
    fin_cases i <;>
      simp_all [fourCodeOf, FourCode.ofFun, FourCode.get, coreEdge, matchingCode₀, Realization.edgeFinset,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.adj_comm]

private theorem fourCode_matching₁_iff {d : V → ℕ} (G : Realization d)
    (a b c e : V) :
    fourCodeOf G a b c e = matchingCode₁ ↔ InducesMatching G.graph a c b e := by
  constructor
  · intro h
    have h0 := congrArg (fun A : FourCode => A (0 : Fin 6)) h
    have h1 := congrArg (fun A : FourCode => A (1 : Fin 6)) h
    have h2 := congrArg (fun A : FourCode => A (2 : Fin 6)) h
    have h3 := congrArg (fun A : FourCode => A (3 : Fin 6)) h
    have h4 := congrArg (fun A : FourCode => A (4 : Fin 6)) h
    have h5 := congrArg (fun A : FourCode => A (5 : Fin 6)) h
    simp [fourCodeOf, FourCode.ofFun, FourCode.get, coreEdge, matchingCode₁, Realization.edgeFinset,
      SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.adj_comm] at h0 h1 h2 h3 h4 h5
    exact ⟨h1, h4, h0, h2, fun h => h3 h.symm, h5⟩
  · rintro ⟨h1, h4, h0, h2, h3, h5⟩
    have h3' : ¬ G.graph.Adj b c := fun h => h3 h.symm
    apply fourCode_ext
    intro i
    fin_cases i <;>
      simp_all [fourCodeOf, FourCode.ofFun, FourCode.get, coreEdge, matchingCode₁, Realization.edgeFinset,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.adj_comm]

private theorem fourCode_matching₂_iff {d : V → ℕ} (G : Realization d)
    (a b c e : V) :
    fourCodeOf G a b c e = matchingCode₂ ↔ InducesMatching G.graph a e b c := by
  constructor
  · intro h
    have h0 := congrArg (fun A : FourCode => A (0 : Fin 6)) h
    have h1 := congrArg (fun A : FourCode => A (1 : Fin 6)) h
    have h2 := congrArg (fun A : FourCode => A (2 : Fin 6)) h
    have h3 := congrArg (fun A : FourCode => A (3 : Fin 6)) h
    have h4 := congrArg (fun A : FourCode => A (4 : Fin 6)) h
    have h5 := congrArg (fun A : FourCode => A (5 : Fin 6)) h
    simp [fourCodeOf, FourCode.ofFun, FourCode.get, coreEdge, matchingCode₂, Realization.edgeFinset,
      SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.adj_comm] at h0 h1 h2 h3 h4 h5
    exact ⟨h2, h3, h0, h1, fun h => h4 h.symm, fun h => h5 h.symm⟩
  · rintro ⟨h2, h3, h0, h1, h4, h5⟩
    have h4' : ¬ G.graph.Adj b e := fun h => h4 h.symm
    have h5' : ¬ G.graph.Adj c e := fun h => h5 h.symm
    apply fourCode_ext
    intro i
    fin_cases i <;>
      simp_all [fourCodeOf, FourCode.ofFun, FourCode.get, coreEdge, matchingCode₂, Realization.edgeFinset,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.adj_comm]

private theorem fourCode_cycle₀_iff {d : V → ℕ} (G : Realization d)
    (a b c e : V) :
    fourCodeOf G a b c e = codeComplement matchingCode₀ ↔
      InducesFourCycle G.graph a b c e := by
  constructor
  · intro h
    have h0 := congrArg (fun A : FourCode => A (0 : Fin 6)) h
    have h1 := congrArg (fun A : FourCode => A (1 : Fin 6)) h
    have h2 := congrArg (fun A : FourCode => A (2 : Fin 6)) h
    have h3 := congrArg (fun A : FourCode => A (3 : Fin 6)) h
    have h4 := congrArg (fun A : FourCode => A (4 : Fin 6)) h
    have h5 := congrArg (fun A : FourCode => A (5 : Fin 6)) h
    simp [fourCodeOf, FourCode.ofFun, FourCode.get, coreEdge, codeComplement, matchingCode₀,
      Realization.edgeFinset, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet, SimpleGraph.adj_comm] at h0 h1 h2 h3 h4 h5
    exact ⟨h0, h5, h1, h2, h3, h4⟩
  · rintro ⟨h0, h5, h1, h2, h3, h4⟩
    apply fourCode_ext
    intro i
    fin_cases i <;>
      simp_all [fourCodeOf, FourCode.ofFun, FourCode.get, coreEdge, codeComplement, matchingCode₀,
        Realization.edgeFinset, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, SimpleGraph.adj_comm]

private theorem fourCode_cycle₁_iff {d : V → ℕ} (G : Realization d)
    (a b c e : V) :
    fourCodeOf G a b c e = codeComplement matchingCode₁ ↔
      InducesFourCycle G.graph a c b e := by
  constructor
  · intro h
    have h0 := congrArg (fun A : FourCode => A (0 : Fin 6)) h
    have h1 := congrArg (fun A : FourCode => A (1 : Fin 6)) h
    have h2 := congrArg (fun A : FourCode => A (2 : Fin 6)) h
    have h3 := congrArg (fun A : FourCode => A (3 : Fin 6)) h
    have h4 := congrArg (fun A : FourCode => A (4 : Fin 6)) h
    have h5 := congrArg (fun A : FourCode => A (5 : Fin 6)) h
    simp [fourCodeOf, FourCode.ofFun, FourCode.get, coreEdge, codeComplement, matchingCode₁,
      Realization.edgeFinset, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet, SimpleGraph.adj_comm] at h0 h1 h2 h3 h4 h5
    exact ⟨h1, h4, h0, h2, h3.symm, h5⟩
  · rintro ⟨h1, h4, h0, h2, h3, h5⟩
    have h3' : G.graph.Adj b c := h3.symm
    apply fourCode_ext
    intro i
    fin_cases i <;>
      simp_all [fourCodeOf, FourCode.ofFun, FourCode.get, coreEdge, codeComplement, matchingCode₁,
        Realization.edgeFinset, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, SimpleGraph.adj_comm]

private theorem fourCode_cycle₂_iff {d : V → ℕ} (G : Realization d)
    (a b c e : V) :
    fourCodeOf G a b c e = codeComplement matchingCode₂ ↔
      InducesFourCycle G.graph a e b c := by
  constructor
  · intro h
    have h0 := congrArg (fun A : FourCode => A (0 : Fin 6)) h
    have h1 := congrArg (fun A : FourCode => A (1 : Fin 6)) h
    have h2 := congrArg (fun A : FourCode => A (2 : Fin 6)) h
    have h3 := congrArg (fun A : FourCode => A (3 : Fin 6)) h
    have h4 := congrArg (fun A : FourCode => A (4 : Fin 6)) h
    have h5 := congrArg (fun A : FourCode => A (5 : Fin 6)) h
    simp [fourCodeOf, FourCode.ofFun, FourCode.get, coreEdge, codeComplement, matchingCode₂,
      Realization.edgeFinset, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet, SimpleGraph.adj_comm] at h0 h1 h2 h3 h4 h5
    exact ⟨h2, h3, h0, h1, h4.symm, h5.symm⟩
  · rintro ⟨h2, h3, h0, h1, h4, h5⟩
    have h4' : G.graph.Adj b e := h4.symm
    have h5' : G.graph.Adj c e := h5.symm
    apply fourCode_ext
    intro i
    fin_cases i <;>
      simp_all [fourCodeOf, FourCode.ofFun, FourCode.get, coreEdge, codeComplement, matchingCode₂,
        Realization.edgeFinset, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, SimpleGraph.adj_comm]

private theorem inducesMatching_reverse_second (G : SimpleGraph V) (a b c e : V)
    (h : InducesMatching G a b c e) : InducesMatching G a b e c := by
  rcases h with ⟨hab, hce, hac, hae, hbc, hbe⟩
  exact ⟨hab, hce.symm, hae, hac, hbe, hbc⟩

private theorem inducesFourCycle_reverse_second (G : SimpleGraph V) (a b c e : V)
    (h : InducesFourCycle G a b c e) : InducesFourCycle G a b e c := by
  rcases h with ⟨hab, hce, hac, hae, hbc, hbe⟩
  exact ⟨hab, fun h => hce h.symm, hae, hac, hbe, hbc⟩

private theorem finset_four_swap_middle {α : Type*} [DecidableEq α] (a b c e : α) :
    ({a, b, c, e} : Finset α) = {a, c, b, e} := by
  ext v
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem finset_four_move_second_last {α : Type*} [DecidableEq α] (a b c e : α) :
    ({a, b, c, e} : Finset α) = {a, e, b, c} := by
  ext v
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem finset_four_swap_pairs {α : Type*} [DecidableEq α] (a b c e : α) :
    ({a, b, c, e} : Finset α) = {c, e, a, b} := by
  ext v
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

set_option maxHeartbeats 2000000 in
private theorem rich_triangle_normal_form {d : V → ℕ} {G G₁ G₂ : Realization d}
    (hrich : IsRichTriangle d G G₁ G₂) :
    ∃ a b c e : V, FourDistinct a b c e ∧
      edgeSupport ((G.edgeFinset ∆ G₁.edgeFinset) ∪
        (G.edgeFinset ∆ G₂.edgeFinset)) = {a, b, c, e} ∧
      ((InducesMatching G.graph a b c e ∧
          ((InducesMatching G₁.graph a c b e ∧
              InducesMatching G₂.graph a e b c) ∨
            (InducesMatching G₂.graph a c b e ∧
              InducesMatching G₁.graph a e b c))) ∨
        (InducesFourCycle G.graph a b c e ∧
          ((InducesFourCycle G₁.graph a c b e ∧
              InducesFourCycle G₂.graph a e b c) ∨
            (InducesFourCycle G₂.graph a c b e ∧
              InducesFourCycle G₁.graph a e b c)))) := by
  classical
  rcases hrich with ⟨h01, h02, h12, hcard⟩
  obtain ⟨a, b, c, e, hab, hac, hae, hbc, hbe, hce, hS⟩ :=
    Finset.card_eq_four.mp hcard
  have hdist : FourDistinct a b c e := ⟨hab, hac, hae, hbc, hbe, hce⟩
  let S : Finset V := {a, b, c, e}
  have hsub01 : edgeSupport (G.edgeFinset ∆ G₁.edgeFinset) ⊆ S := by
    change edgeSupport (G.edgeFinset ∆ G₁.edgeFinset) ⊆ {a, b, c, e}
    rw [← hS]
    exact edgeSupport_mono Finset.subset_union_left
  have hsub02 : edgeSupport (G.edgeFinset ∆ G₂.edgeFinset) ⊆ S := by
    change edgeSupport (G.edgeFinset ∆ G₂.edgeFinset) ⊆ {a, b, c, e}
    rw [← hS]
    exact edgeSupport_mono Finset.subset_union_right
  have hdiff12 : G₁.edgeFinset ∆ G₂.edgeFinset ⊆
      (G.edgeFinset ∆ G₁.edgeFinset) ∪ (G.edgeFinset ∆ G₂.edgeFinset) := by
    intro f hf
    simp only [Finset.mem_symmDiff, Finset.mem_union] at hf ⊢
    tauto
  have hsub12 : edgeSupport (G₁.edgeFinset ∆ G₂.edgeFinset) ⊆ S := by
    change edgeSupport (G₁.edgeFinset ∆ G₂.edgeFinset) ⊆ {a, b, c, e}
    rw [← hS]
    exact edgeSupport_mono hdiff12
  let A := fourCodeOf G a b c e
  let B := fourCodeOf G₁ a b c e
  let C := fourCodeOf G₂ a b c e
  have hdegAB : fourCodeDegree A = fourCodeDegree B :=
    fourCodeDegree_eq_of_support_subset G G₁ hdist hsub01
  have hdegAC : fourCodeDegree A = fourCodeDegree C :=
    fourCodeDegree_eq_of_support_subset G G₂ hdist hsub02
  have hcardAB : (Finset.univ.filter fun i => A i != B i).card = 4 := by
    rw [fourCode_distance_eq G G₁ hdist hsub01]
    exact h01
  have hcardAC : (Finset.univ.filter fun i => A i != C i).card = 4 := by
    rw [fourCode_distance_eq G G₂ hdist hsub02]
    exact h02
  have hcardBC : (Finset.univ.filter fun i => B i != C i).card = 4 := by
    rw [fourCode_distance_eq G₁ G₂ hdist hsub12]
    exact h12
  rcases four_code_classifier A B C hdegAB hdegAC hcardAB hcardAC hcardBC with hm | hc
  · rcases matching_code_ordered A B C hm with
      ⟨hA, (⟨hB, hC⟩ | ⟨hB, hC⟩)⟩ |
      ⟨hA, (⟨hB, hC⟩ | ⟨hB, hC⟩)⟩ |
      ⟨hA, (⟨hB, hC⟩ | ⟨hB, hC⟩)⟩
    · exact ⟨a, b, c, e, hdist, hS,
        Or.inl ⟨(fourCode_matching₀_iff G a b c e).mp hA,
          Or.inl ⟨(fourCode_matching₁_iff G₁ a b c e).mp hB,
            (fourCode_matching₂_iff G₂ a b c e).mp hC⟩⟩⟩
    · exact ⟨a, b, c, e, hdist, hS,
        Or.inl ⟨(fourCode_matching₀_iff G a b c e).mp hA,
          Or.inr ⟨(fourCode_matching₁_iff G₂ a b c e).mp hC,
            (fourCode_matching₂_iff G₁ a b c e).mp hB⟩⟩⟩
    · refine ⟨a, c, b, e, ⟨hac, hab, hae, hbc.symm, hce, hbe⟩, ?_, Or.inl ⟨?_, ?_⟩⟩
      · exact hS.trans (finset_four_swap_middle a b c e)
      · exact (fourCode_matching₁_iff G a b c e).mp hA
      · exact Or.inl ⟨(fourCode_matching₀_iff G₁ a b c e).mp hB,
          inducesMatching_reverse_second G₂.graph a e b c
            ((fourCode_matching₂_iff G₂ a b c e).mp hC)⟩
    · refine ⟨a, c, b, e, ⟨hac, hab, hae, hbc.symm, hce, hbe⟩, ?_, Or.inl ⟨?_, ?_⟩⟩
      · exact hS.trans (finset_four_swap_middle a b c e)
      · exact (fourCode_matching₁_iff G a b c e).mp hA
      · exact Or.inr ⟨(fourCode_matching₀_iff G₂ a b c e).mp hC,
          inducesMatching_reverse_second G₁.graph a e b c
            ((fourCode_matching₂_iff G₁ a b c e).mp hB)⟩
    · refine ⟨a, e, b, c, ⟨hae, hab, hac, hbe.symm, hce.symm, hbc⟩, ?_, Or.inl ⟨?_, ?_⟩⟩
      · exact hS.trans (finset_four_move_second_last a b c e)
      · exact (fourCode_matching₂_iff G a b c e).mp hA
      · exact Or.inl ⟨inducesMatching_reverse_second G₁.graph a b c e
            ((fourCode_matching₀_iff G₁ a b c e).mp hB),
          inducesMatching_reverse_second G₂.graph a c b e
            ((fourCode_matching₁_iff G₂ a b c e).mp hC)⟩
    · refine ⟨a, e, b, c, ⟨hae, hab, hac, hbe.symm, hce.symm, hbc⟩, ?_, Or.inl ⟨?_, ?_⟩⟩
      · exact hS.trans (finset_four_move_second_last a b c e)
      · exact (fourCode_matching₂_iff G a b c e).mp hA
      · exact Or.inr ⟨inducesMatching_reverse_second G₂.graph a b c e
            ((fourCode_matching₀_iff G₂ a b c e).mp hC),
          inducesMatching_reverse_second G₁.graph a c b e
            ((fourCode_matching₁_iff G₁ a b c e).mp hB)⟩
  · rcases cycle_code_ordered A B C hc with
      ⟨hA, (⟨hB, hC⟩ | ⟨hB, hC⟩)⟩ |
      ⟨hA, (⟨hB, hC⟩ | ⟨hB, hC⟩)⟩ |
      ⟨hA, (⟨hB, hC⟩ | ⟨hB, hC⟩)⟩
    · exact ⟨a, b, c, e, hdist, hS,
        Or.inr ⟨(fourCode_cycle₀_iff G a b c e).mp hA,
          Or.inl ⟨(fourCode_cycle₁_iff G₁ a b c e).mp hB,
            (fourCode_cycle₂_iff G₂ a b c e).mp hC⟩⟩⟩
    · exact ⟨a, b, c, e, hdist, hS,
        Or.inr ⟨(fourCode_cycle₀_iff G a b c e).mp hA,
          Or.inr ⟨(fourCode_cycle₁_iff G₂ a b c e).mp hC,
            (fourCode_cycle₂_iff G₁ a b c e).mp hB⟩⟩⟩
    · refine ⟨a, c, b, e, ⟨hac, hab, hae, hbc.symm, hce, hbe⟩, ?_, Or.inr ⟨?_, ?_⟩⟩
      · exact hS.trans (finset_four_swap_middle a b c e)
      · exact (fourCode_cycle₁_iff G a b c e).mp hA
      · exact Or.inl ⟨(fourCode_cycle₀_iff G₁ a b c e).mp hB,
          inducesFourCycle_reverse_second G₂.graph a e b c
            ((fourCode_cycle₂_iff G₂ a b c e).mp hC)⟩
    · refine ⟨a, c, b, e, ⟨hac, hab, hae, hbc.symm, hce, hbe⟩, ?_, Or.inr ⟨?_, ?_⟩⟩
      · exact hS.trans (finset_four_swap_middle a b c e)
      · exact (fourCode_cycle₁_iff G a b c e).mp hA
      · exact Or.inr ⟨(fourCode_cycle₀_iff G₂ a b c e).mp hC,
          inducesFourCycle_reverse_second G₁.graph a e b c
            ((fourCode_cycle₂_iff G₁ a b c e).mp hB)⟩
    · refine ⟨a, e, b, c, ⟨hae, hab, hac, hbe.symm, hce.symm, hbc⟩, ?_, Or.inr ⟨?_, ?_⟩⟩
      · exact hS.trans (finset_four_move_second_last a b c e)
      · exact (fourCode_cycle₂_iff G a b c e).mp hA
      · exact Or.inl ⟨inducesFourCycle_reverse_second G₁.graph a b c e
            ((fourCode_cycle₀_iff G₁ a b c e).mp hB),
          inducesFourCycle_reverse_second G₂.graph a c b e
            ((fourCode_cycle₁_iff G₂ a b c e).mp hC)⟩
    · refine ⟨a, e, b, c, ⟨hae, hab, hac, hbe.symm, hce.symm, hbc⟩, ?_, Or.inr ⟨?_, ?_⟩⟩
      · exact hS.trans (finset_four_move_second_last a b c e)
      · exact (fourCode_cycle₂_iff G a b c e).mp hA
      · exact Or.inr ⟨inducesFourCycle_reverse_second G₂.graph a b c e
            ((fourCode_cycle₀_iff G₂ a b c e).mp hC),
          inducesFourCycle_reverse_second G₁.graph a c b e
            ((fourCode_cycle₁_iff G₁ a b c e).mp hB)⟩

private theorem neighborFinset_eq_of_not_mem_edgeSupport_symmDiff {d : V → ℕ}
    (A B : Realization d) {v : V}
    (hv : v ∉ edgeSupport (A.edgeFinset ∆ B.edgeFinset)) :
    A.neighborFinset v = B.neighborFinset v := by
  classical
  ext w
  simp only [Realization.mem_neighborFinset]
  by_contra hne
  have hedge : s(v, w) ∈ A.edgeFinset ∆ B.edgeFinset := by
    simp only [Finset.mem_symmDiff, Realization.edgeFinset,
      SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.adj_comm]
    tauto
  apply hv
  simp only [edgeSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨s(v, w), hedge, Sym2.mem_mk_left v w⟩

private theorem triangle_hasNonBipartiteFibre_of_not_mem_support {d : V → ℕ}
    {A B C : Realization d}
    (hAB : (RealizationGraph d).Adj A B)
    (hAC : (RealizationGraph d).Adj A C)
    (hBC : (RealizationGraph d).Adj B C) {v : V}
    (hv : v ∉ edgeSupport ((A.edgeFinset ∆ B.edgeFinset) ∪
      (A.edgeFinset ∆ C.edgeFinset))) :
    HasNonBipartiteFibre d v := by
  have hvAB : v ∉ edgeSupport (A.edgeFinset ∆ B.edgeFinset) := by
    intro h
    exact hv (edgeSupport_mono Finset.subset_union_left h)
  have hvAC : v ∉ edgeSupport (A.edgeFinset ∆ C.edgeFinset) := by
    intro h
    exact hv (edgeSupport_mono Finset.subset_union_right h)
  have hAeqB := neighborFinset_eq_of_not_mem_edgeSupport_symmDiff A B hvAB
  have hAeqC := neighborFinset_eq_of_not_mem_edgeSupport_symmDiff A C hvAC
  exact ⟨A, B, C, hAeqB, hAeqB.symm.trans hAeqC, hAB, hBC, hAC⟩

private theorem failing_pair_forbids_triangle_missing_difference {d : V → ℕ}
    {X Y : Realization d}
    (hfail : ∀ v : V, v ∈ edgeSupport (X.edgeFinset ∆ Y.edgeFinset) →
      ¬ HasNonBipartiteFibre d v)
    {A B C : Realization d}
    (hAB : (RealizationGraph d).Adj A B)
    (hAC : (RealizationGraph d).Adj A C)
    (hBC : (RealizationGraph d).Adj B C) :
    edgeSupport (X.edgeFinset ∆ Y.edgeFinset) ⊆
      edgeSupport ((A.edgeFinset ∆ B.edgeFinset) ∪
        (A.edgeFinset ∆ C.edgeFinset)) := by
  intro v hvD
  by_contra hvS
  exact hfail v hvD
    (triangle_hasNonBipartiteFibre_of_not_mem_support hAB hAC hBC hvS)

private theorem symmDiff_chain_from_base {d : V → ℕ}
    (A B C : Realization d) :
    B.edgeFinset ∆ C.edgeFinset =
      (A.edgeFinset ∆ B.edgeFinset) ∆ (A.edgeFinset ∆ C.edgeFinset) := by
  classical
  ext f
  simp only [Finset.mem_symmDiff]
  tauto

private theorem edgeSupport_singleton_pair (a b : V) :
    edgeSupport ({s(a, b)} : Finset (Sym2 V)) = {a, b} := by
  classical
  ext v
  simp [edgeSupport, Sym2.mem_iff]

private theorem edgeSupport_insert_pair (a b : V) (E : Finset (Sym2 V)) :
    edgeSupport (insert s(a, b) E) = {a, b} ∪ edgeSupport E := by
  rw [show insert s(a, b) E = {s(a, b)} ∪ E by simp,
    edgeSupport_union_eq, edgeSupport_singleton_pair]

private theorem four_switch_edges_card_local {a b c e : V}
    (h : FourDistinct a b c e) :
    ({s(a, b), s(c, e), s(a, c), s(b, e)} : Finset (Sym2 V)).card = 4 := by
  classical
  rcases h with ⟨hab, hac, hae, hbc, hbe, hce⟩
  rw [Finset.card_eq_four]
  refine ⟨s(a, b), s(c, e), s(a, c), s(b, e), ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
    simp [Sym2.eq_iff, hab, hab.symm, hac, hac.symm, hae, hae.symm,
      hbc, hbc.symm, hbe, hbe.symm, hce, hce.symm]

private theorem triangle_certificate_of_symmDiff {d : V → ℕ}
    (A B C : Realization d) (E F : Finset (Sym2 V)) (S : Finset V)
    (hAB : A.edgeFinset ∆ B.edgeFinset = E)
    (hAC : A.edgeFinset ∆ C.edgeFinset = F)
    (hE : E.card = 4) (hF : F.card = 4) (hEF : (E ∆ F).card = 4)
    (hS : edgeSupport (E ∪ F) = S) :
    (RealizationGraph d).Adj A B ∧ (RealizationGraph d).Adj A C ∧
      (RealizationGraph d).Adj B C ∧
      edgeSupport ((A.edgeFinset ∆ B.edgeFinset) ∪
        (A.edgeFinset ∆ C.edgeFinset)) = S := by
  have hBC : B.edgeFinset ∆ C.edgeFinset = E ∆ F := by
    rw [symmDiff_chain_from_base A B C, hAB, hAC]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (A.edgeFinset ∆ B.edgeFinset).card = 4
    rw [hAB]
    exact hE
  · change (A.edgeFinset ∆ C.edgeFinset).card = 4
    rw [hAC]
    exact hF
  · change (B.edgeFinset ∆ C.edgeFinset).card = 4
    rw [hBC]
    exact hEF
  · rw [hAB, hAC]
    exact hS

set_option maxHeartbeats 800000 in
private theorem typeI_triangle_certificate {d : V → ℕ} (A : Realization d)
    {a b c e : V} (hdist : FourDistinct a b c e)
    (hmatch : InducesMatching A.graph a b c e) :
    ∃ B C : Realization d,
      (RealizationGraph d).Adj A B ∧ (RealizationGraph d).Adj A C ∧
      (RealizationGraph d).Adj B C ∧
      edgeSupport ((A.edgeFinset ∆ B.edgeFinset) ∪
        (A.edgeFinset ∆ C.edgeFinset)) = {a, b, c, e} := by
  classical
  rcases hdist with ⟨hab, hac, hae, hbc, hbe, hce⟩
  rcases hmatch with ⟨hAB, hCE, hAC, hAE, hBC, hBE⟩
  let B := quotientSwitchRealization A hAB hAC hCE.symm (fun h => hBE h.symm)
    hac.symm hab.symm hbc hae.symm hbe.symm
  let C := quotientSwitchRealization A hAB hAE hCE (fun h => hBC h.symm)
    hae.symm hab.symm hbe hac.symm hbc.symm
  let D₁ : Finset (Sym2 V) := {s(a, b), s(c, e), s(a, c), s(b, e)}
  let D₂ : Finset (Sym2 V) := {s(a, b), s(c, e), s(a, e), s(b, c)}
  have hD₁ : A.edgeFinset ∆ B.edgeFinset = D₁ := by
    have h := quotientSwitchRealization_symmDiff A hAB hAC hCE.symm
      (fun h => hBE h.symm) hac.symm hab.symm hbc hae.symm hbe.symm
    rw [show s(b, a) = s(a, b) from Sym2.eq_swap,
      show s(c, a) = s(a, c) from Sym2.eq_swap] at h
    simpa [B, D₁] using h
  have hD₂ : A.edgeFinset ∆ C.edgeFinset = D₂ := by
    have h := quotientSwitchRealization_symmDiff A hAB hAE hCE
      (fun h => hBC h.symm) hae.symm hab.symm hbe hac.symm hbc.symm
    rw [show s(b, a) = s(a, b) from Sym2.eq_swap,
      show s(e, c) = s(c, e) from Sym2.eq_swap,
      show s(e, a) = s(a, e) from Sym2.eq_swap] at h
    simpa [C, D₂] using h
  have hxor : D₁ ∆ D₂ = {s(a, c), s(b, e), s(a, e), s(b, c)} := by
    ext f
    simp only [D₁, D₂, Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor <;> intro hf
    · rcases hf with ⟨hf, hn⟩ | ⟨hf, hn⟩
      · rcases hf with hf | hf | hf | hf
        · exact False.elim (hn (Or.inl hf))
        · exact False.elim (hn (Or.inr (Or.inl hf)))
        · exact Or.inl hf
        · exact Or.inr (Or.inl hf)
      · rcases hf with hf | hf | hf | hf
        · exact False.elim (hn (Or.inl hf))
        · exact False.elim (hn (Or.inr (Or.inl hf)))
        · exact Or.inr (Or.inr (Or.inl hf))
        · exact Or.inr (Or.inr (Or.inr hf))
    · rcases hf with hf | hf | hf | hf
      · exact Or.inl ⟨Or.inr (Or.inr (Or.inl hf)), by
          simp [hf, hab, hab.symm, hac, hac.symm, hae, hae.symm,
            hbc, hbc.symm, hbe, hbe.symm, hce, hce.symm]⟩
      · exact Or.inl ⟨Or.inr (Or.inr (Or.inr hf)), by
          simp [hf, hab, hab.symm, hac, hac.symm, hae, hae.symm,
            hbc, hbc.symm, hbe, hbe.symm, hce, hce.symm]⟩
      · exact Or.inr ⟨Or.inr (Or.inr (Or.inl hf)), by
          simp [hf, hab, hab.symm, hac, hac.symm, hae, hae.symm,
            hbc, hbc.symm, hbe, hbe.symm, hce, hce.symm]⟩
      · exact Or.inr ⟨Or.inr (Or.inr (Or.inr hf)), by
          simp [hf, hab, hab.symm, hac, hac.symm, hae, hae.symm,
            hbc, hbc.symm, hbe, hbe.symm, hce, hce.symm]⟩
  have hBCdiff : B.edgeFinset ∆ C.edgeFinset =
      {s(a, c), s(b, e), s(a, e), s(b, c)} := by
    rw [symmDiff_chain_from_base A B C, hD₁, hD₂, hxor]
  refine ⟨B, C, ?_, ?_, ?_, ?_⟩
  · change (A.edgeFinset ∆ B.edgeFinset).card = 4
    rw [hD₁]
    exact four_switch_edges_card_local ⟨hab, hac, hae, hbc, hbe, hce⟩
  · change (A.edgeFinset ∆ C.edgeFinset).card = 4
    rw [hD₂]
    have hcard := four_switch_edges_card_local
      (a := a) (b := b) (c := e) (e := c)
      ⟨hab, hae, hac, hbe, hbc, hce.symm⟩
    rw [show s(e, c) = s(c, e) from Sym2.eq_swap] at hcard
    exact hcard
  · change (B.edgeFinset ∆ C.edgeFinset).card = 4
    rw [hBCdiff]
    have hcard := four_switch_edges_card_local
      ⟨hac, hae, hab, hce, hbc.symm, hbe.symm⟩
    rw [show s(e, b) = s(b, e) from Sym2.eq_swap,
      show s(c, b) = s(b, c) from Sym2.eq_swap] at hcard
    exact hcard
  · rw [hD₁, hD₂]
    simp only [D₁, D₂, edgeSupport_union_eq, edgeSupport_insert_pair,
      edgeSupport_singleton_pair]
    ext v
    simp
    tauto

set_option maxHeartbeats 800000 in
private theorem typeIII_triangle_certificate {d : V → ℕ} (A : Realization d)
    {a b c e : V} (hdist : FourDistinct a b c e)
    (hcycle : InducesFourCycle A.graph a b c e) :
    ∃ B C : Realization d,
      (RealizationGraph d).Adj A B ∧ (RealizationGraph d).Adj A C ∧
      (RealizationGraph d).Adj B C ∧
      edgeSupport ((A.edgeFinset ∆ B.edgeFinset) ∪
        (A.edgeFinset ∆ C.edgeFinset)) = {a, b, c, e} := by
  classical
  rcases hdist with ⟨hab, hac, hae, hbc, hbe, hce⟩
  rcases hcycle with ⟨hAB, hCE, hAC, hAE, hBC, hBE⟩
  let B := quotientSwitchRealization A hAC hAB hBE.symm (fun h => hCE h.symm)
    hab.symm hac.symm hbc.symm hae.symm hce.symm
  let C := quotientSwitchRealization A hAE hAB hBC.symm (fun h => hCE h)
    hab.symm hae.symm hbe.symm hac.symm hce
  let E : Finset (Sym2 V) := {s(a, b), s(c, e), s(a, c), s(b, e)}
  let F : Finset (Sym2 V) := {s(a, b), s(c, e), s(a, e), s(b, c)}
  have hE : A.edgeFinset ∆ B.edgeFinset = E := by
    have h := quotientSwitchRealization_symmDiff A hAC hAB hBE.symm
      (fun h => hCE h.symm) hab.symm hac.symm hbc.symm hae.symm hce.symm
    rw [show s(c, a) = s(a, c) from Sym2.eq_swap,
      show s(b, a) = s(a, b) from Sym2.eq_swap] at h
    change A.edgeFinset ∆ B.edgeFinset = {s(a, b), s(c, e), s(a, c), s(b, e)}
    simpa only [B] using h.trans
      (finset_four_swap_pairs (s(a, c)) (s(b, e)) (s(a, b)) (s(c, e)))
  have hF : A.edgeFinset ∆ C.edgeFinset = F := by
    have h := quotientSwitchRealization_symmDiff A hAE hAB hBC.symm
      (fun h => hCE h) hab.symm hae.symm hbe.symm hac.symm hce
    rw [show s(e, a) = s(a, e) from Sym2.eq_swap,
      show s(b, a) = s(a, b) from Sym2.eq_swap,
      show s(e, c) = s(c, e) from Sym2.eq_swap] at h
    change A.edgeFinset ∆ C.edgeFinset = {s(a, b), s(c, e), s(a, e), s(b, c)}
    simpa only [C] using h.trans
      (finset_four_swap_pairs (s(a, e)) (s(b, c)) (s(a, b)) (s(c, e)))
  have hEcard : E.card = 4 := by
    simpa [E] using four_switch_edges_card_local
      (a := a) (b := b) (c := c) (e := e) ⟨hab, hac, hae, hbc, hbe, hce⟩
  have hFcard : F.card = 4 := by
    have hcard := four_switch_edges_card_local
      (a := a) (b := b) (c := e) (e := c)
      ⟨hab, hae, hac, hbe, hbc, hce.symm⟩
    rw [show s(e, c) = s(c, e) from Sym2.eq_swap] at hcard
    simpa [F] using hcard
  have hEFset : E ∆ F = {s(a, c), s(b, e), s(a, e), s(b, c)} := by
    ext f
    simp only [E, F, Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor <;> intro hf
    · rcases hf with ⟨hf, hn⟩ | ⟨hf, hn⟩
      · rcases hf with hf | hf | hf | hf
        · exact False.elim (hn (Or.inl hf))
        · exact False.elim (hn (Or.inr (Or.inl hf)))
        · exact Or.inl hf
        · exact Or.inr (Or.inl hf)
      · rcases hf with hf | hf | hf | hf
        · exact False.elim (hn (Or.inl hf))
        · exact False.elim (hn (Or.inr (Or.inl hf)))
        · exact Or.inr (Or.inr (Or.inl hf))
        · exact Or.inr (Or.inr (Or.inr hf))
    · rcases hf with hf | hf | hf | hf
      · exact Or.inl ⟨Or.inr (Or.inr (Or.inl hf)), by
          simp [hf, hab, hab.symm, hac, hac.symm, hae, hae.symm,
            hbc, hbc.symm, hbe, hbe.symm, hce, hce.symm]⟩
      · exact Or.inl ⟨Or.inr (Or.inr (Or.inr hf)), by
          simp [hf, hab, hab.symm, hac, hac.symm, hae, hae.symm,
            hbc, hbc.symm, hbe, hbe.symm, hce, hce.symm]⟩
      · exact Or.inr ⟨Or.inr (Or.inr (Or.inl hf)), by
          simp [hf, hab, hab.symm, hac, hac.symm, hae, hae.symm,
            hbc, hbc.symm, hbe, hbe.symm, hce, hce.symm]⟩
      · exact Or.inr ⟨Or.inr (Or.inr (Or.inr hf)), by
          simp [hf, hab, hab.symm, hac, hac.symm, hae, hae.symm,
            hbc, hbc.symm, hbe, hbe.symm, hce, hce.symm]⟩
  have hEFcard : (E ∆ F).card = 4 := by
    rw [hEFset]
    have hcard := four_switch_edges_card_local
      (a := a) (b := c) (c := e) (e := b)
      ⟨hac, hae, hab, hce, hbc.symm, hbe.symm⟩
    rw [show s(e, b) = s(b, e) from Sym2.eq_swap,
      show s(c, b) = s(b, c) from Sym2.eq_swap] at hcard
    exact hcard
  have hsupport : edgeSupport (E ∪ F) = {a, b, c, e} := by
    simp only [E, F, edgeSupport_union_eq, edgeSupport_insert_pair,
      edgeSupport_singleton_pair]
    ext v
    simp
    tauto
  exact ⟨B, C, triangle_certificate_of_symmDiff A B C E F {a, b, c, e}
    hE hF hEcard hFcard hEFcard hsupport⟩

set_option maxHeartbeats 800000 in
private theorem typeII_triangle_certificate {d : V → ℕ} (A : Realization d)
    {x y z t u : V} (hdist : FiveDistinct x y z t u)
    (hxy : A.graph.Adj x y) (hzt : A.graph.Adj z t)
    (hzu : A.graph.Adj z u) (hxz : ¬ A.graph.Adj x z)
    (hyt : ¬ A.graph.Adj y t) (hyu : ¬ A.graph.Adj y u) :
    ∃ B C : Realization d,
      (RealizationGraph d).Adj A B ∧ (RealizationGraph d).Adj A C ∧
      (RealizationGraph d).Adj B C ∧
      edgeSupport ((A.edgeFinset ∆ B.edgeFinset) ∪
        (A.edgeFinset ∆ C.edgeFinset)) = {x, y, z, t, u} := by
  classical
  rcases hdist with ⟨hxy', hxz', hxt, hxu, hyz, hyt', hyu', hzt', hzu', htu⟩
  let B := quotientSwitchRealization A hxy hxz hzt.symm (fun h => hyt h.symm)
    hxz'.symm hxy'.symm hyz hxt.symm hyt'.symm
  let C := quotientSwitchRealization A hxy hxz hzu.symm (fun h => hyu h.symm)
    hxz'.symm hxy'.symm hyz hxu.symm hyu'.symm
  let E : Finset (Sym2 V) := {s(x, y), s(z, t), s(x, z), s(y, t)}
  let F : Finset (Sym2 V) := {s(x, y), s(z, u), s(x, z), s(y, u)}
  have hE : A.edgeFinset ∆ B.edgeFinset = E := by
    have h := quotientSwitchRealization_symmDiff A hxy hxz hzt.symm
      (fun h => hyt h.symm) hxz'.symm hxy'.symm hyz hxt.symm hyt'.symm
    rw [show s(y, x) = s(x, y) from Sym2.eq_swap,
      show s(z, x) = s(x, z) from Sym2.eq_swap] at h
    simpa [B, E] using h
  have hF : A.edgeFinset ∆ C.edgeFinset = F := by
    have h := quotientSwitchRealization_symmDiff A hxy hxz hzu.symm
      (fun h => hyu h.symm) hxz'.symm hxy'.symm hyz hxu.symm hyu'.symm
    rw [show s(y, x) = s(x, y) from Sym2.eq_swap,
      show s(z, x) = s(x, z) from Sym2.eq_swap] at h
    simpa [C, F] using h
  have hEcard : E.card = 4 := by
    simpa [E] using four_switch_edges_card_local
      (a := x) (b := y) (c := z) (e := t)
      ⟨hxy', hxz', hxt, hyz, hyt', hzt'⟩
  have hFcard : F.card = 4 := by
    simpa [F] using four_switch_edges_card_local
      (a := x) (b := y) (c := z) (e := u)
      ⟨hxy', hxz', hxu, hyz, hyu', hzu'⟩
  have hEFset : E ∆ F = {s(z, t), s(y, t), s(z, u), s(y, u)} := by
    ext f
    simp only [E, F, Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor <;> intro hf
    · rcases hf with ⟨hf, hn⟩ | ⟨hf, hn⟩
      · rcases hf with hf | hf | hf | hf
        · exact False.elim (hn (Or.inl hf))
        · exact Or.inl hf
        · exact False.elim (hn (Or.inr (Or.inr (Or.inl hf))))
        · exact Or.inr (Or.inl hf)
      · rcases hf with hf | hf | hf | hf
        · exact False.elim (hn (Or.inl hf))
        · exact Or.inr (Or.inr (Or.inl hf))
        · exact False.elim (hn (Or.inr (Or.inr (Or.inl hf))))
        · exact Or.inr (Or.inr (Or.inr hf))
    · rcases hf with hf | hf | hf | hf
      · exact Or.inl ⟨Or.inr (Or.inl hf), by
          simp [hf, hxy', hxy'.symm, hxz', hxz'.symm, hxt, hxt.symm,
            hxu, hxu.symm, hyz, hyz.symm, hyt', hyt'.symm, hyu', hyu'.symm,
            hzt', hzt'.symm, hzu', hzu'.symm, htu, htu.symm]⟩
      · exact Or.inl ⟨Or.inr (Or.inr (Or.inr hf)), by
          simp [hf, hxy', hxy'.symm, hxz', hxz'.symm, hxt, hxt.symm,
            hxu, hxu.symm, hyz, hyz.symm, hyt', hyt'.symm, hyu', hyu'.symm,
            hzt', hzt'.symm, hzu', hzu'.symm, htu, htu.symm]⟩
      · exact Or.inr ⟨Or.inr (Or.inl hf), by
          simp [hf, hxy', hxy'.symm, hxz', hxz'.symm, hxt, hxt.symm,
            hxu, hxu.symm, hyz, hyz.symm, hyt', hyt'.symm, hyu', hyu'.symm,
            hzt', hzt'.symm, hzu', hzu'.symm, htu, htu.symm]⟩
      · exact Or.inr ⟨Or.inr (Or.inr (Or.inr hf)), by
          simp [hf, hxy', hxy'.symm, hxz', hxz'.symm, hxt, hxt.symm,
            hxu, hxu.symm, hyz, hyz.symm, hyt', hyt'.symm, hyu', hyu'.symm,
            hzt', hzt'.symm, hzu', hzu'.symm, htu, htu.symm]⟩
  have hEFcard : (E ∆ F).card = 4 := by
    rw [hEFset, Finset.card_eq_four]
    refine ⟨s(z, t), s(y, t), s(z, u), s(y, u), ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
      simp [Sym2.eq_iff, hxy', hxy'.symm, hxz', hxz'.symm, hxt, hxt.symm,
        hxu, hxu.symm, hyz, hyz.symm, hyt', hyt'.symm, hyu', hyu'.symm,
        hzt', hzt'.symm, hzu', hzu'.symm, htu, htu.symm]
  have hsupport : edgeSupport (E ∪ F) = {x, y, z, t, u} := by
    simp only [E, F, edgeSupport_union_eq, edgeSupport_insert_pair,
      edgeSupport_singleton_pair]
    ext v
    simp
    tauto
  exact ⟨B, C, triangle_certificate_of_symmDiff A B C E F {x, y, z, t, u}
    hE hF hEcard hFcard hEFcard hsupport⟩

private def CoreTriangleForbidden {d : V → ℕ} (S : Finset V) : Prop :=
  ∀ A B C : Realization d,
    (RealizationGraph d).Adj A B → (RealizationGraph d).Adj A C →
    (RealizationGraph d).Adj B C →
    S ⊆ edgeSupport ((A.edgeFinset ∆ B.edgeFinset) ∪
      (A.edgeFinset ∆ C.edgeFinset))

private theorem matching_violates_core_forbidden {d : V → ℕ}
    (S : Finset V) (hforbid : CoreTriangleForbidden (d := d) S)
    (A : Realization d) {p q r t j : V} (hdist : FourDistinct p q r t)
    (hmatch : InducesMatching A.graph p q r t) (hjS : j ∈ S)
    (hjmiss : j ∉ ({p, q, r, t} : Finset V)) : False := by
  obtain ⟨B, C, hAB, hAC, hBC, hsupp⟩ := typeI_triangle_certificate A hdist hmatch
  have hj := hforbid A B C hAB hAC hBC hjS
  rw [hsupp] at hj
  exact hjmiss hj

private theorem cycle_violates_core_forbidden {d : V → ℕ}
    (S : Finset V) (hforbid : CoreTriangleForbidden (d := d) S)
    (A : Realization d) {p q r t j : V} (hdist : FourDistinct p q r t)
    (hcycle : InducesFourCycle A.graph p q r t) (hjS : j ∈ S)
    (hjmiss : j ∉ ({p, q, r, t} : Finset V)) : False := by
  obtain ⟨B, C, hAB, hAC, hBC, hsupp⟩ := typeIII_triangle_certificate A hdist hcycle
  have hj := hforbid A B C hAB hAC hBC hjS
  rw [hsupp] at hj
  exact hjmiss hj

private theorem typeII_violates_core_forbidden {d : V → ℕ}
    (S : Finset V) (hforbid : CoreTriangleForbidden (d := d) S)
    (A : Realization d) {x y z t u j : V} (hdist : FiveDistinct x y z t u)
    (hxy : A.graph.Adj x y) (hzt : A.graph.Adj z t) (hzu : A.graph.Adj z u)
    (hxz : ¬ A.graph.Adj x z) (hyt : ¬ A.graph.Adj y t)
    (hyu : ¬ A.graph.Adj y u) (hjS : j ∈ S)
    (hjmiss : j ∉ ({x, y, z, t, u} : Finset V)) : False := by
  obtain ⟨B, C, hAB, hAC, hBC, hsupp⟩ :=
    typeII_triangle_certificate A hdist hxy hzt hzu hxz hyt hyu
  have hj := hforbid A B C hAB hAC hBC hjS
  rw [hsupp] at hj
  exact hjmiss hj

private def TypeIIForbiddenData (G : SimpleGraph V) (S : Finset V)
    (x y z t u j : V) : Prop :=
  FiveDistinct x y z t u ∧ G.Adj x y ∧ G.Adj z t ∧ G.Adj z u ∧
    ¬ G.Adj x z ∧ ¬ G.Adj y t ∧ ¬ G.Adj y u ∧
    j ∈ S ∧ j ∉ ({x, y, z, t, u} : Finset V)

private theorem typeII_data_violates_core_forbidden {d : V → ℕ}
    (S : Finset V) (hforbid : CoreTriangleForbidden (d := d) S)
    (G : Realization d) {x y z t u j : V}
    (h : TypeIIForbiddenData G.graph S x y z t u j) : False := by
  rcases h with ⟨hdist, hxy, hzt, hzu, hxz, hyt, hyu, hjS, hjmiss⟩
  exact typeII_violates_core_forbidden S hforbid G hdist hxy hzt hzu hxz hyt hyu
    hjS hjmiss

private def OutsidePatternI (G : SimpleGraph V) (a b c e w : V) : Prop :=
  (¬ G.Adj w a ∧ ¬ G.Adj w b ∧ ¬ G.Adj w c ∧ ¬ G.Adj w e) ∨
  (G.Adj w a ∧ G.Adj w b ∧ G.Adj w c ∧ G.Adj w e) ∨
  (¬ G.Adj w a ∧ G.Adj w b ∧ G.Adj w c ∧ G.Adj w e) ∨
  (G.Adj w a ∧ ¬ G.Adj w b ∧ G.Adj w c ∧ G.Adj w e) ∨
  (G.Adj w a ∧ G.Adj w b ∧ ¬ G.Adj w c ∧ G.Adj w e) ∨
  (G.Adj w a ∧ G.Adj w b ∧ G.Adj w c ∧ ¬ G.Adj w e)

private def OutsidePatternIII (G : SimpleGraph V) (a b c e w : V) : Prop :=
  (¬ G.Adj w a ∧ ¬ G.Adj w b ∧ ¬ G.Adj w c ∧ ¬ G.Adj w e) ∨
  (G.Adj w a ∧ G.Adj w b ∧ G.Adj w c ∧ G.Adj w e) ∨
  (G.Adj w a ∧ ¬ G.Adj w b ∧ ¬ G.Adj w c ∧ ¬ G.Adj w e) ∨
  (¬ G.Adj w a ∧ G.Adj w b ∧ ¬ G.Adj w c ∧ ¬ G.Adj w e) ∨
  (¬ G.Adj w a ∧ ¬ G.Adj w b ∧ G.Adj w c ∧ ¬ G.Adj w e) ∨
  (¬ G.Adj w a ∧ ¬ G.Adj w b ∧ ¬ G.Adj w c ∧ G.Adj w e)

private def OutsideA (G : SimpleGraph V) (a b c e w : V) : Prop :=
  ¬ G.Adj w a ∧ ¬ G.Adj w b ∧ ¬ G.Adj w c ∧ ¬ G.Adj w e

private def OutsideB (G : SimpleGraph V) (a b c e w : V) : Prop :=
  G.Adj w a ∧ G.Adj w b ∧ G.Adj w c ∧ G.Adj w e

private def OutsideZI (G : SimpleGraph V) (a b c e w : V) : Prop :=
  (¬ G.Adj w a ∧ G.Adj w b ∧ G.Adj w c ∧ G.Adj w e) ∨
  (G.Adj w a ∧ ¬ G.Adj w b ∧ G.Adj w c ∧ G.Adj w e) ∨
  (G.Adj w a ∧ G.Adj w b ∧ ¬ G.Adj w c ∧ G.Adj w e) ∨
  (G.Adj w a ∧ G.Adj w b ∧ G.Adj w c ∧ ¬ G.Adj w e)

private def OutsideZIII (G : SimpleGraph V) (a b c e w : V) : Prop :=
  (G.Adj w a ∧ ¬ G.Adj w b ∧ ¬ G.Adj w c ∧ ¬ G.Adj w e) ∨
  (¬ G.Adj w a ∧ G.Adj w b ∧ ¬ G.Adj w c ∧ ¬ G.Adj w e) ∨
  (¬ G.Adj w a ∧ ¬ G.Adj w b ∧ G.Adj w c ∧ ¬ G.Adj w e) ∨
  (¬ G.Adj w a ∧ ¬ G.Adj w b ∧ ¬ G.Adj w c ∧ G.Adj w e)

attribute [local simp] ne_comm SimpleGraph.adj_comm

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 5000 in
private theorem outside_pattern_I {d : V → ℕ} (S : Finset V)
    (hforbid : CoreTriangleForbidden (d := d) S)
    (G G₁ G₂ : Realization d) {a b c e w : V}
    (hdist : FourDistinct a b c e) (hS : S = {a, b, c, e})
    (hwS : w ∉ S)
    (hG : InducesMatching G.graph a b c e)
    (hG₁ : InducesMatching G₁.graph a c b e)
    (hG₂ : InducesMatching G₂.graph a e b c)
    (heq₁ : ∀ x ∈ S, G.graph.Adj w x ↔ G₁.graph.Adj w x)
    (heq₂ : ∀ x ∈ S, G.graph.Adj w x ↔ G₂.graph.Adj w x) :
    OutsidePatternI G.graph a b c e w := by
  have hwaS : w ≠ a := by
    intro h
    subst w
    exact hwS (by simp [hS])
  have hwbS : w ≠ b := by
    intro h
    subst w
    exact hwS (by simp [hS])
  have hwcS : w ≠ c := by
    intro h
    subst w
    exact hwS (by simp [hS])
  have hweS : w ≠ e := by
    intro h
    subst w
    exact hwS (by simp [hS])
  have h₁a := heq₁ a (by simp [hS])
  have h₁b := heq₁ b (by simp [hS])
  have h₁c := heq₁ c (by simp [hS])
  have h₁e := heq₁ e (by simp [hS])
  have h₂a := heq₂ a (by simp [hS])
  have h₂b := heq₂ b (by simp [hS])
  have h₂c := heq₂ c (by simp [hS])
  have h₂e := heq₂ e (by simp [hS])
  rcases hdist with ⟨hab, hac, hae, hbc, hbe, hce⟩
  by_cases hwa : G.graph.Adj w a <;>
    by_cases hwb : G.graph.Adj w b <;>
    by_cases hwc : G.graph.Adj w c <;>
    by_cases hwe : G.graph.Adj w e <;>
    simp only [OutsidePatternI, hwa, hwb, hwc, hwe, not_true_eq_false,
      not_false_eq_true, and_self, and_true, true_and, false_and, and_false,
      or_false, false_or, true_or, or_true]
  all_goals
    solve
    | (apply matching_violates_core_forbidden S hforbid G (p := w) (q := a) (r := c) (t := e) (j := b) <;> simp_all [FourDistinct, InducesMatching, hS])
    | (apply matching_violates_core_forbidden S hforbid G (p := w) (q := b) (r := c) (t := e) (j := a) <;> simp_all [FourDistinct, InducesMatching, hS])
    | (apply matching_violates_core_forbidden S hforbid G (p := w) (q := c) (r := a) (t := b) (j := e) <;> simp_all [FourDistinct, InducesMatching, hS])
    | (apply matching_violates_core_forbidden S hforbid G₁ (p := w) (q := c) (r := b) (t := e) (j := a) <;> simp_all [FourDistinct, InducesMatching, hS])
    | (apply matching_violates_core_forbidden S hforbid G₂ (p := w) (q := c) (r := a) (t := e) (j := b) <;> simp_all [FourDistinct, InducesMatching, hS])
    | (apply matching_violates_core_forbidden S hforbid G (p := w) (q := e) (r := a) (t := b) (j := c) <;> simp_all [FourDistinct, InducesMatching, hS])
    | (apply matching_violates_core_forbidden S hforbid G₂ (p := w) (q := e) (r := b) (t := c) (j := a) <;> simp_all [FourDistinct, InducesMatching, hS])
    | (apply matching_violates_core_forbidden S hforbid G₁ (p := w) (q := e) (r := a) (t := c) (j := b) <;> simp_all [FourDistinct, InducesMatching, hS])

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 5000 in
private theorem outside_pattern_III {d : V → ℕ} (S : Finset V)
    (hforbid : CoreTriangleForbidden (d := d) S)
    (G G₁ G₂ : Realization d) {a b c e w : V}
    (hdist : FourDistinct a b c e) (hS : S = {a, b, c, e})
    (hwS : w ∉ S)
    (hG : InducesFourCycle G.graph a b c e)
    (hG₁ : InducesFourCycle G₁.graph a c b e)
    (hG₂ : InducesFourCycle G₂.graph a e b c)
    (heq₁ : ∀ x ∈ S, G.graph.Adj w x ↔ G₁.graph.Adj w x)
    (heq₂ : ∀ x ∈ S, G.graph.Adj w x ↔ G₂.graph.Adj w x) :
    OutsidePatternIII G.graph a b c e w := by
  have hwaS : w ≠ a := by
    intro h
    subst w
    exact hwS (by simp [hS])
  have hwbS : w ≠ b := by
    intro h
    subst w
    exact hwS (by simp [hS])
  have hwcS : w ≠ c := by
    intro h
    subst w
    exact hwS (by simp [hS])
  have hweS : w ≠ e := by
    intro h
    subst w
    exact hwS (by simp [hS])
  have h₁a := heq₁ a (by simp [hS])
  have h₁b := heq₁ b (by simp [hS])
  have h₁c := heq₁ c (by simp [hS])
  have h₁e := heq₁ e (by simp [hS])
  have h₂a := heq₂ a (by simp [hS])
  have h₂b := heq₂ b (by simp [hS])
  have h₂c := heq₂ c (by simp [hS])
  have h₂e := heq₂ e (by simp [hS])
  rcases hdist with ⟨hab, hac, hae, hbc, hbe, hce⟩
  by_cases hwa : G.graph.Adj w a <;>
    by_cases hwb : G.graph.Adj w b <;>
    by_cases hwc : G.graph.Adj w c <;>
    by_cases hwe : G.graph.Adj w e <;>
    simp only [OutsidePatternIII, hwa, hwb, hwc, hwe, not_true_eq_false,
      not_false_eq_true, and_self, and_true, true_and, false_and, and_false,
      or_false, false_or, true_or, or_true]
  all_goals
    solve
    | (apply cycle_violates_core_forbidden S hforbid G (p := w) (q := e) (r := a) (t := b) (j := c) <;> simp_all [FourDistinct, InducesFourCycle, hS])
    | (apply cycle_violates_core_forbidden S hforbid G₁ (p := w) (q := e) (r := a) (t := c) (j := b) <;> simp_all [FourDistinct, InducesFourCycle, hS])
    | (apply cycle_violates_core_forbidden S hforbid G₂ (p := w) (q := e) (r := b) (t := c) (j := a) <;> simp_all [FourDistinct, InducesFourCycle, hS])
    | (apply cycle_violates_core_forbidden S hforbid G₂ (p := w) (q := c) (r := a) (t := e) (j := b) <;> simp_all [FourDistinct, InducesFourCycle, hS])
    | (apply cycle_violates_core_forbidden S hforbid G₁ (p := w) (q := c) (r := b) (t := e) (j := a) <;> simp_all [FourDistinct, InducesFourCycle, hS])
    | (apply cycle_violates_core_forbidden S hforbid G (p := w) (q := c) (r := a) (t := b) (j := e) <;> simp_all [FourDistinct, InducesFourCycle, hS])
    | (apply cycle_violates_core_forbidden S hforbid G (p := w) (q := b) (r := c) (t := e) (j := a) <;> simp_all [FourDistinct, InducesFourCycle, hS])
    | (apply cycle_violates_core_forbidden S hforbid G (p := w) (q := a) (r := c) (t := e) (j := b) <;> simp_all [FourDistinct, InducesFourCycle, hS])

private theorem outside_status_I {d : V → ℕ} (S : Finset V)
    (hforbid : CoreTriangleForbidden (d := d) S) (G : Realization d)
    {a b c e : V} (hdist : FourDistinct a b c e) (hS : S = {a, b, c, e})
    (hG : InducesMatching G.graph a b c e) :
    (∀ u v, u ∉ S → v ∉ S → u ≠ v →
      OutsideA G.graph a b c e u → OutsideA G.graph a b c e v →
      ¬ G.graph.Adj u v) ∧
    (∀ u v, u ∉ S → v ∉ S → u ≠ v →
      OutsideB G.graph a b c e u → OutsideB G.graph a b c e v →
      G.graph.Adj u v) ∧
    (∀ u v, u ∉ S → v ∉ S → u ≠ v →
      OutsideA G.graph a b c e u → OutsideZI G.graph a b c e v →
      ¬ G.graph.Adj u v) ∧
    (∀ u v, u ∉ S → v ∉ S → u ≠ v →
      OutsideB G.graph a b c e u → OutsideZI G.graph a b c e v →
      G.graph.Adj u v) := by
  rcases hdist with ⟨hab, hac, hae, hbc, hbe, hce⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u v huS hvS huv huA hvA huvEdge
    exact matching_violates_core_forbidden S hforbid G
      (p := a) (q := b) (r := u) (t := v) (j := c)
      (by simp_all [FourDistinct, OutsideA]) (by simp_all [InducesMatching, OutsideA])
      (by simp [hS]) (by simp_all)
  · intro u v huS hvS huv huB hvB
    by_contra huvEdge
    exact typeII_violates_core_forbidden S hforbid G
      (x := u) (y := b) (z := v) (t := c) (u := e) (j := a)
      (by simp_all [FiveDistinct, OutsideB])
      (by simp_all [OutsideB]) (by simp_all [OutsideB]) (by simp_all [OutsideB])
      huvEdge (by simp_all [InducesMatching, OutsideB])
      (by simp_all [InducesMatching, OutsideB]) (by simp [hS]) (by simp_all)
  · intro u v huS hvS huv huA hvZ huvEdge
    rcases hvZ with hvZ | hvZ | hvZ | hvZ
    · exact typeII_violates_core_forbidden S hforbid G
        (x := a) (y := b) (z := v) (t := c) (u := u) (j := e)
        (by simp_all [FiveDistinct, OutsideA])
        (by simp_all [InducesMatching]) (by simp_all)
        (by simpa only [SimpleGraph.adj_comm] using huvEdge)
        (by simp_all [OutsideA]) (by simp_all [InducesMatching])
        (by simp_all [OutsideA]) (by simp [hS]) (by simp_all)
    · exact typeII_violates_core_forbidden S hforbid G
        (x := b) (y := a) (z := v) (t := c) (u := u) (j := e)
        (by simp_all [FiveDistinct, OutsideA])
        (by simp_all [InducesMatching]) (by simp_all)
        (by simpa only [SimpleGraph.adj_comm] using huvEdge)
        (by simp_all [OutsideA]) (by simp_all [InducesMatching])
        (by simp_all [OutsideA]) (by simp [hS]) (by simp_all)
    · exact typeII_violates_core_forbidden S hforbid G
        (x := c) (y := e) (z := v) (t := a) (u := u) (j := b)
        (by simp_all [FiveDistinct, OutsideA])
        (by simp_all [InducesMatching]) (by simp_all)
        (by simpa only [SimpleGraph.adj_comm] using huvEdge)
        (by simp_all [OutsideA]) (by simp_all [InducesMatching])
        (by simp_all [OutsideA]) (by simp [hS]) (by simp_all)
    · exact typeII_violates_core_forbidden S hforbid G
        (x := e) (y := c) (z := v) (t := a) (u := u) (j := b)
        (by simp_all [FiveDistinct, OutsideA])
        (by simp_all [InducesMatching]) (by simp_all)
        (by simpa only [SimpleGraph.adj_comm] using huvEdge)
        (by simp_all [OutsideA]) (by simp_all [InducesMatching])
        (by simp_all [OutsideA]) (by simp [hS]) (by simp_all)
  · intro u v huS hvS huv huB hvZ
    by_contra huvEdge
    rcases hvZ with hvZ | hvZ | hvZ | hvZ
    · exact typeII_violates_core_forbidden S hforbid G
        (x := u) (y := b) (z := v) (t := c) (u := e) (j := a)
        (by simp_all [FiveDistinct, OutsideB])
        (by simp_all [OutsideB]) (by simp_all) (by simp_all)
        huvEdge (by simp_all [InducesMatching]) (by simp_all [InducesMatching])
        (by simp [hS]) (by simp_all)
    · exact typeII_violates_core_forbidden S hforbid G
        (x := u) (y := b) (z := v) (t := c) (u := e) (j := a)
        (by simp_all [FiveDistinct, OutsideB])
        (by simp_all [OutsideB]) (by simp_all) (by simp_all)
        huvEdge (by simp_all [InducesMatching]) (by simp_all [InducesMatching])
        (by simp [hS]) (by simp_all)
    · exact typeII_violates_core_forbidden S hforbid G
        (x := b) (y := v) (z := e) (t := c) (u := u) (j := a)
        (by simp_all [FiveDistinct, OutsideB])
        (by simp_all) (by simp_all [InducesMatching]) (by simp_all [OutsideB])
        (by simp_all [InducesMatching]) (by simp_all)
        (by simpa only [SimpleGraph.adj_comm] using huvEdge)
        (by simp [hS]) (by simp_all)
    · exact typeII_violates_core_forbidden S hforbid G
        (x := a) (y := v) (z := c) (t := e) (u := u) (j := b)
        (by simp_all [FiveDistinct, OutsideB])
        (by simp_all) (by simp_all [InducesMatching]) (by simp_all [OutsideB])
        (by simp_all [InducesMatching]) (by simp_all)
        (by simpa only [SimpleGraph.adj_comm] using huvEdge)
        (by simp [hS]) (by simp_all)

private theorem outside_status_III {d : V → ℕ} (S : Finset V)
    (hforbid : CoreTriangleForbidden (d := d) S) (G : Realization d)
    {a b c e : V} (hdist : FourDistinct a b c e) (hS : S = {a, b, c, e})
    (hG : InducesFourCycle G.graph a b c e) :
    (∀ u v, u ∉ S → v ∉ S → u ≠ v →
      OutsideA G.graph a b c e u → OutsideA G.graph a b c e v →
      ¬ G.graph.Adj u v) ∧
    (∀ u v, u ∉ S → v ∉ S → u ≠ v →
      OutsideB G.graph a b c e u → OutsideB G.graph a b c e v →
      G.graph.Adj u v) ∧
    (∀ u v, u ∉ S → v ∉ S → u ≠ v →
      OutsideA G.graph a b c e u → OutsideZIII G.graph a b c e v →
      ¬ G.graph.Adj u v) ∧
    (∀ u v, u ∉ S → v ∉ S → u ≠ v →
      OutsideB G.graph a b c e u → OutsideZIII G.graph a b c e v →
      G.graph.Adj u v) := by
  rcases hdist with ⟨hab, hac, hae, hbc, hbe, hce⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u v huS hvS huv huA hvA huvEdge
    exact matching_violates_core_forbidden S hforbid G
      (p := b) (q := c) (r := u) (t := v) (j := a)
      (by simp_all [FourDistinct, OutsideA])
      (by simp_all [InducesFourCycle, InducesMatching, OutsideA])
      (by simp [hS]) (by simp_all)
  · intro u v huS hvS huv huB hvB
    by_contra huvEdge
    exact cycle_violates_core_forbidden S hforbid G
      (p := u) (q := v) (r := a) (t := b) (j := c)
      (by simp_all [FourDistinct, OutsideB])
      (by simp_all [InducesFourCycle, OutsideB])
      (by simp [hS]) (by simp_all)
  · intro u v huS hvS huv huA hvZ huvEdge
    rcases hvZ with hvZ | hvZ | hvZ | hvZ
    · exact matching_violates_core_forbidden S hforbid G
        (p := b) (q := c) (r := u) (t := v) (j := a)
        (by simp_all [FourDistinct, OutsideA])
        (by simp_all [InducesFourCycle, InducesMatching, OutsideA])
        (by simp [hS]) (by simp_all)
    · exact matching_violates_core_forbidden S hforbid G
        (p := a) (q := c) (r := u) (t := v) (j := b)
        (by simp_all [FourDistinct, OutsideA])
        (by simp_all [InducesFourCycle, InducesMatching, OutsideA])
        (by simp [hS]) (by simp_all)
    · exact matching_violates_core_forbidden S hforbid G
        (p := a) (q := e) (r := u) (t := v) (j := b)
        (by simp_all [FourDistinct, OutsideA])
        (by simp_all [InducesFourCycle, InducesMatching, OutsideA])
        (by simp [hS]) (by simp_all)
    · exact matching_violates_core_forbidden S hforbid G
        (p := a) (q := c) (r := u) (t := v) (j := b)
        (by simp_all [FourDistinct, OutsideA])
        (by simp_all [InducesFourCycle, InducesMatching, OutsideA])
        (by simp [hS]) (by simp_all)
  · intro u v huS hvS huv huB hvZ
    by_contra huvEdge
    rcases hvZ with hvZ | hvZ | hvZ | hvZ
    · exact typeII_violates_core_forbidden S hforbid G
        (x := a) (y := v) (z := b) (t := c) (u := u) (j := e)
        (by simp_all [FiveDistinct, OutsideB])
        (by simp_all) (by simp_all [InducesFourCycle]) (by simp_all [OutsideB])
        (by simp_all [InducesFourCycle]) (by simp_all)
        (by simpa only [SimpleGraph.adj_comm] using huvEdge)
        (by simp [hS]) (by simp_all)
    · exact typeII_violates_core_forbidden S hforbid G
        (x := b) (y := v) (z := a) (t := c) (u := u) (j := e)
        (by simp_all [FiveDistinct, OutsideB])
        (by simp_all) (by simp_all [InducesFourCycle]) (by simp_all [OutsideB])
        (by simp_all [InducesFourCycle]) (by simp_all)
        (by simpa only [SimpleGraph.adj_comm] using huvEdge)
        (by simp [hS]) (by simp_all)
    · exact typeII_violates_core_forbidden S hforbid G
        (x := c) (y := v) (z := e) (t := a) (u := u) (j := b)
        (by simp_all [FiveDistinct, OutsideB])
        (by simp_all) (by simp_all [InducesFourCycle]) (by simp_all [OutsideB])
        (by simp_all [InducesFourCycle]) (by simp_all)
        (by simpa only [SimpleGraph.adj_comm] using huvEdge)
        (by simp [hS]) (by simp_all)
    · exact typeII_violates_core_forbidden S hforbid G
        (x := e) (y := v) (z := c) (t := a) (u := u) (j := b)
        (by simp_all [FiveDistinct, OutsideB])
        (by simp_all) (by simp_all [InducesFourCycle]) (by simp_all [OutsideB])
        (by simp_all [InducesFourCycle]) (by simp_all)
        (by simpa only [SimpleGraph.adj_comm] using huvEdge)
        (by simp [hS]) (by simp_all)

set_option maxHeartbeats 2000000 in
private theorem outside_ZI_unique {d : V → ℕ} (S : Finset V)
    (hforbid : CoreTriangleForbidden (d := d) S) (G : Realization d)
    {a b c e : V} (hdist : FourDistinct a b c e) (hS : S = {a, b, c, e})
    (hG : InducesMatching G.graph a b c e) :
    ∀ u v, u ∉ S → v ∉ S → OutsideZI G.graph a b c e u →
      OutsideZI G.graph a b c e v → u = v := by
  intro u v huS hvS huZ hvZ
  by_contra huv
  rcases hdist with ⟨hab, hac, hae, hbc, hbe, hce⟩
  rcases huZ with huZ | huZ | huZ | huZ <;>
    rcases hvZ with hvZ | hvZ | hvZ | hvZ <;>
    by_cases huvEdge : G.graph.Adj u v
  all_goals
    solve
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := b) (y := a) (z := c) (t := u) (u := v) (j := e); simp_all [TypeIIForbiddenData, FiveDistinct, InducesMatching, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := u) (y := b) (z := v) (t := c) (u := e) (j := a); simp_all [TypeIIForbiddenData, FiveDistinct, InducesMatching, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := a) (y := b) (z := u) (t := c) (u := v) (j := e); simp_all [TypeIIForbiddenData, FiveDistinct, InducesMatching, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := a) (y := v) (z := e) (t := c) (u := u) (j := b); simp_all [TypeIIForbiddenData, FiveDistinct, InducesMatching, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := u) (y := c) (z := a) (t := b) (u := v) (j := e); simp_all [TypeIIForbiddenData, FiveDistinct, InducesMatching, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := a) (y := v) (z := c) (t := e) (u := u) (j := b); simp_all [TypeIIForbiddenData, FiveDistinct, InducesMatching, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := u) (y := e) (z := a) (t := b) (u := v) (j := c); simp_all [TypeIIForbiddenData, FiveDistinct, InducesMatching, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := u) (y := a) (z := v) (t := c) (u := e) (j := b); simp_all [TypeIIForbiddenData, FiveDistinct, InducesMatching, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := a) (y := b) (z := v) (t := c) (u := u) (j := e); simp_all [TypeIIForbiddenData, FiveDistinct, InducesMatching, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := a) (y := b) (z := c) (t := u) (u := v) (j := e); simp_all [TypeIIForbiddenData, FiveDistinct, InducesMatching, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := u) (y := c) (z := b) (t := a) (u := v) (j := e); simp_all [TypeIIForbiddenData, FiveDistinct, InducesMatching, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := u) (y := e) (z := b) (t := a) (u := v) (j := c); simp_all [TypeIIForbiddenData, FiveDistinct, InducesMatching, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := a) (y := u) (z := e) (t := c) (u := v) (j := b); simp_all [TypeIIForbiddenData, FiveDistinct, InducesMatching, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := u) (y := a) (z := c) (t := e) (u := v) (j := b); simp_all [TypeIIForbiddenData, FiveDistinct, InducesMatching, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := u) (y := b) (z := c) (t := e) (u := v) (j := a); simp_all [TypeIIForbiddenData, FiveDistinct, InducesMatching, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := e) (y := c) (z := a) (t := u) (u := v) (j := b); simp_all [TypeIIForbiddenData, FiveDistinct, InducesMatching, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := u) (y := e) (z := v) (t := a) (u := b) (j := c); simp_all [TypeIIForbiddenData, FiveDistinct, InducesMatching, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := c) (y := e) (z := u) (t := a) (u := v) (j := b); simp_all [TypeIIForbiddenData, FiveDistinct, InducesMatching, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := a) (y := u) (z := c) (t := e) (u := v) (j := b); simp_all [TypeIIForbiddenData, FiveDistinct, InducesMatching, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := u) (y := a) (z := e) (t := c) (u := v) (j := b); simp_all [TypeIIForbiddenData, FiveDistinct, InducesMatching, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := u) (y := b) (z := e) (t := c) (u := v) (j := a); simp_all [TypeIIForbiddenData, FiveDistinct, InducesMatching, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := u) (y := c) (z := v) (t := a) (u := b) (j := e); simp_all [TypeIIForbiddenData, FiveDistinct, InducesMatching, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := c) (y := e) (z := v) (t := a) (u := u) (j := b); simp_all [TypeIIForbiddenData, FiveDistinct, InducesMatching, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := c) (y := e) (z := a) (t := u) (u := v) (j := b); simp_all [TypeIIForbiddenData, FiveDistinct, InducesMatching, hS])

set_option maxHeartbeats 2000000 in
private theorem outside_ZIII_unique {d : V → ℕ} (S : Finset V)
    (hforbid : CoreTriangleForbidden (d := d) S) (G : Realization d)
    {a b c e : V} (hdist : FourDistinct a b c e) (hS : S = {a, b, c, e})
    (hG : InducesFourCycle G.graph a b c e) :
    ∀ u v, u ∉ S → v ∉ S → OutsideZIII G.graph a b c e u →
      OutsideZIII G.graph a b c e v → u = v := by
  intro u v huS hvS huZ hvZ
  by_contra huv
  rcases hdist with ⟨hab, hac, hae, hbc, hbe, hce⟩
  rcases huZ with huZ | huZ | huZ | huZ <;>
    rcases hvZ with hvZ | hvZ | hvZ | hvZ <;>
    by_cases huvEdge : G.graph.Adj u v
  all_goals
    solve
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := b) (y := c) (z := a) (t := u) (u := v) (j := e); simp_all [TypeIIForbiddenData, FiveDistinct, InducesFourCycle, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := a) (y := u) (z := b) (t := c) (u := v) (j := e); simp_all [TypeIIForbiddenData, FiveDistinct, InducesFourCycle, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := u) (y := v) (z := b) (t := c) (u := e) (j := a); simp_all [TypeIIForbiddenData, FiveDistinct, InducesFourCycle, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := u) (y := a) (z := c) (t := b) (u := v) (j := e); simp_all [TypeIIForbiddenData, FiveDistinct, InducesFourCycle, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := a) (y := e) (z := v) (t := c) (u := u) (j := b); simp_all [TypeIIForbiddenData, FiveDistinct, InducesFourCycle, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := u) (y := a) (z := e) (t := b) (u := v) (j := c); simp_all [TypeIIForbiddenData, FiveDistinct, InducesFourCycle, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := a) (y := c) (z := v) (t := e) (u := u) (j := b); simp_all [TypeIIForbiddenData, FiveDistinct, InducesFourCycle, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := a) (y := v) (z := b) (t := c) (u := u) (j := e); simp_all [TypeIIForbiddenData, FiveDistinct, InducesFourCycle, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := u) (y := v) (z := a) (t := c) (u := e) (j := b); simp_all [TypeIIForbiddenData, FiveDistinct, InducesFourCycle, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := a) (y := c) (z := b) (t := u) (u := v) (j := e); simp_all [TypeIIForbiddenData, FiveDistinct, InducesFourCycle, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := u) (y := b) (z := c) (t := a) (u := v) (j := e); simp_all [TypeIIForbiddenData, FiveDistinct, InducesFourCycle, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := u) (y := b) (z := e) (t := a) (u := v) (j := c); simp_all [TypeIIForbiddenData, FiveDistinct, InducesFourCycle, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := u) (y := c) (z := a) (t := e) (u := v) (j := b); simp_all [TypeIIForbiddenData, FiveDistinct, InducesFourCycle, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := a) (y := e) (z := u) (t := c) (u := v) (j := b); simp_all [TypeIIForbiddenData, FiveDistinct, InducesFourCycle, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := u) (y := c) (z := b) (t := e) (u := v) (j := a); simp_all [TypeIIForbiddenData, FiveDistinct, InducesFourCycle, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := e) (y := a) (z := c) (t := u) (u := v) (j := b); simp_all [TypeIIForbiddenData, FiveDistinct, InducesFourCycle, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := c) (y := u) (z := e) (t := a) (u := v) (j := b); simp_all [TypeIIForbiddenData, FiveDistinct, InducesFourCycle, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := u) (y := v) (z := e) (t := a) (u := b) (j := c); simp_all [TypeIIForbiddenData, FiveDistinct, InducesFourCycle, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := u) (y := e) (z := a) (t := c) (u := v) (j := b); simp_all [TypeIIForbiddenData, FiveDistinct, InducesFourCycle, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := a) (y := c) (z := u) (t := e) (u := v) (j := b); simp_all [TypeIIForbiddenData, FiveDistinct, InducesFourCycle, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := u) (y := e) (z := b) (t := c) (u := v) (j := a); simp_all [TypeIIForbiddenData, FiveDistinct, InducesFourCycle, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := c) (y := v) (z := e) (t := a) (u := u) (j := b); simp_all [TypeIIForbiddenData, FiveDistinct, InducesFourCycle, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := u) (y := v) (z := c) (t := a) (u := b) (j := e); simp_all [TypeIIForbiddenData, FiveDistinct, InducesFourCycle, hS])
    | (apply typeII_data_violates_core_forbidden S hforbid G (x := c) (y := a) (z := e) (t := u) (u := v) (j := b); simp_all [TypeIIForbiddenData, FiveDistinct, InducesFourCycle, hS])

attribute [-simp] ne_comm SimpleGraph.adj_comm

private theorem outside_partition_decomposes_or_all_Z {d : V → ℕ}
    (G : Realization d) (S : Finset V) (P Q Z : V → Prop)
    (hSnonempty : S.Nonempty)
    (hpartition : ∀ w, w ∉ S → P w ∨ Q w ∨ Z w)
    (hPcore : ∀ w, w ∉ S → P w → ∀ x ∈ S, ¬ G.graph.Adj w x)
    (hQcore : ∀ w, w ∉ S → Q w → ∀ x ∈ S, G.graph.Adj w x)
    (hPP : ∀ u v, u ∉ S → v ∉ S → u ≠ v → P u → P v →
      ¬ G.graph.Adj u v)
    (hQQ : ∀ u v, u ∉ S → v ∉ S → u ≠ v → Q u → Q v →
      G.graph.Adj u v)
    (hPZ : ∀ u v, u ∉ S → v ∉ S → u ≠ v → P u → Z v →
      ¬ G.graph.Adj u v)
    (hQZ : ∀ u v, u ∉ S → v ∉ S → u ≠ v → Q u → Z v →
      G.graph.Adj u v) :
    TyshkevichDecomposable d ∨ ∀ w, w ∉ S → Z w := by
  classical
  let PF : Finset V := Finset.univ.filter fun w => w ∉ S ∧ P w
  let QF : Finset V := Finset.univ.filter fun w => w ∉ S ∧ Q w
  by_cases hPQ : (PF ∪ QF).Nonempty
  · left
    let C : Finset V := (PF ∪ QF)ᶜ
    refine ⟨G, QF, C, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨x, hxS⟩ := hSnonempty
      refine ⟨x, ?_⟩
      simp only [C, Finset.mem_compl, Finset.mem_union, PF, QF,
        Finset.mem_filter, Finset.mem_univ, true_and, not_or]
      exact ⟨fun h => h.1 hxS, fun h => h.1 hxS⟩
    · simpa [C] using hPQ
    · intro q hq
      simp only [C, compl_compl, Finset.mem_union]
      exact Or.inr hq
    · intro u hu v hv huv
      simp [QF] at hu hv
      exact hQQ u v hu.1 hv.1 huv hu.2 hv.2
    · intro u hu v hv
      simp [C, QF] at hu hv
      have huP : u ∈ PF := by
        rcases hu.1 with huP | huQ
        · exact huP
        · exact False.elim ((hu.2 huQ.1) huQ.2)
      have hvP : v ∈ PF := by
        rcases hv.1 with hvP | hvQ
        · exact hvP
        · exact False.elim ((hv.2 hvQ.1) hvQ.2)
      simp [PF] at huP hvP
      by_cases huv : u = v
      · subst v
        exact G.graph.irrefl
      · exact hPP u v huP.1 hvP.1 huv huP.2 hvP.2
    · intro q hq x hx
      simp [QF] at hq
      have hxnot : x ∉ PF ∪ QF := by simpa [C] using hx
      by_cases hxS : x ∈ S
      · exact hQcore q hq.1 hq.2 x hxS
      · rcases hpartition x hxS with hxP | hxQ | hxZ
        · exact False.elim (hxnot (Finset.mem_union_left _ (by simp [PF, hxS, hxP])))
        · exact False.elim (hxnot (Finset.mem_union_right _ (by simp [QF, hxS, hxQ])))
        · exact hQZ q x hq.1 hxS (fun h => hxnot
              (Finset.mem_union_right _ (by simpa [QF, h] using hq))) hq.2 hxZ
    · intro p hp x hx
      simp [C, QF] at hp
      have hpP : p ∈ PF := by
        rcases hp.1 with hpP | hpQ
        · exact hpP
        · exact False.elim ((hp.2 hpQ.1) hpQ.2)
      simp [PF] at hpP
      have hxnot : x ∉ PF ∪ QF := by simpa [C] using hx
      by_cases hxS : x ∈ S
      · exact hPcore p hpP.1 hpP.2 x hxS
      · rcases hpartition x hxS with hxP | hxQ | hxZ
        · exact False.elim (hxnot (Finset.mem_union_left _ (by simp [PF, hxS, hxP])))
        · exact False.elim (hxnot (Finset.mem_union_right _ (by simp [QF, hxS, hxQ])))
        · exact hPZ p x hpP.1 hxS (fun h => hxnot
              (Finset.mem_union_left _ (by simpa [PF, h] using hpP))) hpP.2 hxZ
  · right
    intro w hwS
    rcases hpartition w hwS with hwP | hwQ | hwZ
    · exact False.elim (hPQ ⟨w, Finset.mem_union_left _ (by simp [PF, hwS, hwP])⟩)
    · exact False.elim (hPQ ⟨w, Finset.mem_union_right _ (by simp [QF, hwS, hwQ])⟩)
    · exact hwZ

private theorem lone_ZI_violates_core_forbidden {d : V → ℕ}
    (S : Finset V) (hforbid : CoreTriangleForbidden (d := d) S)
    (G : Realization d) {a b c e z : V} (hdist : FourDistinct a b c e)
    (hS : S = {a, b, c, e}) (hzS : z ∉ S)
    (hG : InducesMatching G.graph a b c e) (hz : OutsideZI G.graph a b c e z) : False := by
  rcases hdist with ⟨hab, hac, hae, hbc, hbe, hce⟩
  rcases hG with ⟨hAB, hCE, hAC, hAE, hBC, hBE⟩
  have hza : z ≠ a := by intro h; subst z; exact hzS (by simp [hS])
  have hzb : z ≠ b := by intro h; subst z; exact hzS (by simp [hS])
  have hzc : z ≠ c := by intro h; subst z; exact hzS (by simp [hS])
  have hze : z ≠ e := by intro h; subst z; exact hzS (by simp [hS])
  have haz : a ≠ z := hza.symm
  have hbz : b ≠ z := hzb.symm
  have hcz : c ≠ z := hzc.symm
  have hez : e ≠ z := hze.symm
  rcases hz with hz | hz | hz | hz
  · have hzb' : G.graph.Adj b z := hz.2.1.symm
    have hzc' : G.graph.Adj c z := hz.2.2.1.symm
    have hze' : G.graph.Adj e z := hz.2.2.2.symm
    let H := quotientSwitchRealization G hAB (fun h => hz.1 h.symm) hz.2.2.2.symm
        (fun h => hBE h.symm) hza hab.symm hzb.symm hae.symm hbe.symm
    have hcycle : InducesFourCycle H.graph b c e z := by
      change InducesFourCycle (quotientSwitchGraph G.graph a b z e) b c e z
      simp_all [InducesFourCycle, quotientSwitchGraph, transferGraph,
        ne_comm, SimpleGraph.adj_comm]
    exact cycle_violates_core_forbidden S hforbid H
      (p := b) (q := c) (r := e) (t := z) (j := a)
      ⟨hbc, hbe, hzb.symm, hce, hzc.symm, hze.symm⟩ hcycle
      (by simp [hS]) (by simp_all [ne_comm])
  · have hza' : G.graph.Adj a z := hz.1.symm
    have hzc' : G.graph.Adj c z := hz.2.2.1.symm
    have hze' : G.graph.Adj e z := hz.2.2.2.symm
    let H := quotientSwitchRealization G hAB.symm (fun h => hz.2.1 h.symm)
        hz.2.2.2.symm (fun h => hAE h.symm) hzb hab hza.symm hbe.symm hae.symm
    have hcycle : InducesFourCycle H.graph a c e z := by
      change InducesFourCycle (quotientSwitchGraph G.graph b a z e) a c e z
      simp_all [InducesFourCycle, quotientSwitchGraph, transferGraph,
        ne_comm, SimpleGraph.adj_comm]
    exact cycle_violates_core_forbidden S hforbid H
      (p := a) (q := c) (r := e) (t := z) (j := b)
      ⟨hac, hae, hza.symm, hce, hzc.symm, hze.symm⟩ hcycle
      (by simp [hS]) (by simp_all [ne_comm])
  · have hza' : G.graph.Adj a z := hz.1.symm
    have hzb' : G.graph.Adj b z := hz.2.1.symm
    have hze' : G.graph.Adj e z := hz.2.2.2.symm
    let H := quotientSwitchRealization G hCE (fun h => hz.2.2.1 h.symm)
        hz.1.symm (fun h => hAE h) hzc hce.symm hze.symm hac hae
    have hcycle : InducesFourCycle H.graph a z b e := by
      change InducesFourCycle (quotientSwitchGraph G.graph c e z a) a z b e
      simp_all [InducesFourCycle, quotientSwitchGraph, transferGraph,
        ne_comm, SimpleGraph.adj_comm]
    exact cycle_violates_core_forbidden S hforbid H
      (p := a) (q := z) (r := b) (t := e) (j := c)
      ⟨hza.symm, hab, hae, hzb, hze, hbe⟩ hcycle
      (by simp [hS]) (by simp_all [ne_comm])
  · have hza' : G.graph.Adj a z := hz.1.symm
    have hzb' : G.graph.Adj b z := hz.2.1.symm
    have hzc' : G.graph.Adj c z := hz.2.2.1.symm
    let H := quotientSwitchRealization G hCE.symm (fun h => hz.2.2.2 h.symm)
        hz.1.symm (fun h => hAC h) hze hce hzc.symm hae hac
    have hcycle : InducesFourCycle H.graph a z b c := by
      change InducesFourCycle (quotientSwitchGraph G.graph e c z a) a z b c
      simp_all [InducesFourCycle, quotientSwitchGraph, transferGraph,
        ne_comm, SimpleGraph.adj_comm]
    exact cycle_violates_core_forbidden S hforbid H
      (p := a) (q := z) (r := b) (t := c) (j := e)
      ⟨hza.symm, hab, hac, hzb, hzc, hbc⟩ hcycle
      (by simp [hS]) (by simp_all [ne_comm])

private theorem lone_ZIII_violates_core_forbidden {d : V → ℕ}
    (S : Finset V) (hforbid : CoreTriangleForbidden (d := d) S)
    (G : Realization d) {a b c e z : V} (hdist : FourDistinct a b c e)
    (hS : S = {a, b, c, e}) (hzS : z ∉ S)
    (hG : InducesFourCycle G.graph a b c e)
    (hz : OutsideZIII G.graph a b c e z) : False := by
  rcases hdist with ⟨hab, hac, hae, hbc, hbe, hce⟩
  rcases hG with ⟨hAB, hCE, hAC, hAE, hBC, hBE⟩
  have hza : z ≠ a := by intro h; subst z; exact hzS (by simp [hS])
  have hzb : z ≠ b := by intro h; subst z; exact hzS (by simp [hS])
  have hzc : z ≠ c := by intro h; subst z; exact hzS (by simp [hS])
  have hze : z ≠ e := by intro h; subst z; exact hzS (by simp [hS])
  have haz : a ≠ z := hza.symm
  have hbz : b ≠ z := hzb.symm
  have hcz : c ≠ z := hzc.symm
  have hez : e ≠ z := hze.symm
  rcases hz with hz | hz | hz | hz
  · have hza' : G.graph.Adj a z := hz.1.symm
    have hzb' : ¬ G.graph.Adj b z := fun h => hz.2.1 h.symm
    have hzc' : ¬ G.graph.Adj c z := fun h => hz.2.2.1 h.symm
    have hze' : ¬ G.graph.Adj e z := fun h => hz.2.2.2 h.symm
    let H := quotientSwitchRealization G hz.1.symm hAB hBE.symm
        (fun h => hz.2.2.2 h.symm) hab.symm hza hzb hae.symm hze.symm
    have hmatch : InducesMatching H.graph b c e z := by
      change InducesMatching (quotientSwitchGraph G.graph a z b e) b c e z
      simp_all [InducesMatching, quotientSwitchGraph, transferGraph,
        ne_comm, SimpleGraph.adj_comm]
    exact matching_violates_core_forbidden S hforbid H
      (p := b) (q := c) (r := e) (t := z) (j := a)
      ⟨hbc, hbe, hzb.symm, hce, hzc.symm, hze.symm⟩ hmatch
      (by simp [hS]) (by simp_all [ne_comm])
  · have hza' : ¬ G.graph.Adj a z := fun h => hz.1 h.symm
    have hzb' : G.graph.Adj b z := hz.2.1.symm
    have hzc' : ¬ G.graph.Adj c z := fun h => hz.2.2.1 h.symm
    have hze' : ¬ G.graph.Adj e z := fun h => hz.2.2.2 h.symm
    let H := quotientSwitchRealization G hz.2.1.symm (fun h => hAB h.symm)
        hAE.symm (fun h => hz.2.2.2 h.symm) hab hzb hza hbe.symm hze.symm
    have hmatch : InducesMatching H.graph a c e z := by
      change InducesMatching (quotientSwitchGraph G.graph b z a e) a c e z
      simp_all [InducesMatching, quotientSwitchGraph, transferGraph,
        ne_comm, SimpleGraph.adj_comm]
    exact matching_violates_core_forbidden S hforbid H
      (p := a) (q := c) (r := e) (t := z) (j := b)
      ⟨hac, hae, hza.symm, hce, hzc.symm, hze.symm⟩ hmatch
      (by simp [hS]) (by simp_all [ne_comm])
  · have hza' : ¬ G.graph.Adj a z := fun h => hz.1 h.symm
    have hzb' : ¬ G.graph.Adj b z := fun h => hz.2.1 h.symm
    have hzc' : G.graph.Adj c z := hz.2.2.1.symm
    have hze' : ¬ G.graph.Adj e z := fun h => hz.2.2.2 h.symm
    let H := quotientSwitchRealization G hz.2.2.1.symm hCE hAE
        (fun h => hz.1 h.symm) hce.symm hzc hze hac hza.symm
    have hmatch : InducesMatching H.graph a z b e := by
      change InducesMatching (quotientSwitchGraph G.graph c z e a) a z b e
      simp_all [InducesMatching, quotientSwitchGraph, transferGraph,
        ne_comm, SimpleGraph.adj_comm]
    exact matching_violates_core_forbidden S hforbid H
      (p := a) (q := z) (r := b) (t := e) (j := c)
      ⟨hza.symm, hab, hae, hzb, hze, hbe⟩ hmatch
      (by simp [hS]) (by simp_all [ne_comm])
  · have hza' : ¬ G.graph.Adj a z := fun h => hz.1 h.symm
    have hzb' : ¬ G.graph.Adj b z := fun h => hz.2.1 h.symm
    have hzc' : ¬ G.graph.Adj c z := fun h => hz.2.2.1 h.symm
    have hze' : G.graph.Adj e z := hz.2.2.2.symm
    let H := quotientSwitchRealization G hz.2.2.2.symm (fun h => hCE h.symm)
        hAC (fun h => hz.1 h.symm) hce hze hzc hae hza.symm
    have hmatch : InducesMatching H.graph a z b c := by
      change InducesMatching (quotientSwitchGraph G.graph e z c a) a z b c
      simp_all [InducesMatching, quotientSwitchGraph, transferGraph,
        ne_comm, SimpleGraph.adj_comm]
    exact matching_violates_core_forbidden S hforbid H
      (p := a) (q := z) (r := b) (t := c) (j := e)
      ⟨hza.symm, hab, hac, hzb, hzc, hbc⟩ hmatch
      (by simp [hS]) (by simp_all [ne_comm])

private theorem fourCode_degree_one_classifier :
    ∀ A : FourCode, fourCodeDegree A = fourCodeDegree matchingCode₀ →
      A = matchingCode₀ ∨ A = matchingCode₁ ∨ A = matchingCode₂ := by
  decide

private theorem fourCode_degree_two_classifier :
    ∀ A : FourCode,
      fourCodeDegree A = fourCodeDegree (codeComplement matchingCode₀) →
      A = codeComplement matchingCode₀ ∨
        A = codeComplement matchingCode₁ ∨
        A = codeComplement matchingCode₂ := by
  decide

private theorem realization_eq_of_fourCode_eq {d : V → ℕ}
    (A B : Realization d) {a b c e : V} (hdist : FourDistinct a b c e)
    (hall : ∀ v : V, v ∈ ({a, b, c, e} : Finset V))
    (hcode : fourCodeOf A a b c e = fourCodeOf B a b c e) : A = B := by
  have hsub : edgeSupport (A.edgeFinset ∆ B.edgeFinset) ⊆ {a, b, c, e} := by
    intro v _
    exact hall v
  have hdistance := fourCode_distance_eq A B hdist hsub
  have hzero : (Finset.univ.filter fun i =>
      fourCodeOf A a b c e i != fourCodeOf B a b c e i).card = 0 := by
    simp [hcode]
  have hdiffzero : (A.edgeFinset ∆ B.edgeFinset).card = 0 := by omega
  apply realization_eq_of_edgeFinset_eq
  exact Finset.symmDiff_eq_empty.mp (Finset.card_eq_zero.mp hdiffzero)

private theorem no_outside_matching_violates_notK3 {d : V → ℕ}
    (hnotK3 : NotK3Base d) (G G₁ G₂ : Realization d)
    {a b c e : V} (hdist : FourDistinct a b c e)
    (hall : ∀ v : V, v ∈ ({a, b, c, e} : Finset V))
    (h01 : (RealizationGraph d).Adj G G₁)
    (h02 : (RealizationGraph d).Adj G G₂)
    (h12 : (RealizationGraph d).Adj G₁ G₂)
    (hG : InducesMatching G.graph a b c e)
    (hG₁ : InducesMatching G₁.graph a c b e)
    (hG₂ : InducesMatching G₂.graph a e b c) : False := by
  apply hnotK3
  refine ⟨G, G₁, G₂, ?_, ?_, ?_, ?_⟩
  · intro h
    subst G₁
    simpa using h01
  · intro h
    subst G₂
    simpa using h12
  · intro h
    subst G₂
    simpa using h02
  · intro H
    have hsub : edgeSupport (H.edgeFinset ∆ G.edgeFinset) ⊆ {a, b, c, e} := by
      intro v _
      exact hall v
    have hdeg := fourCodeDegree_eq_of_support_subset H G hdist hsub
    have hGcode := (fourCode_matching₀_iff G a b c e).mpr hG
    have hHdeg : fourCodeDegree (fourCodeOf H a b c e) =
        fourCodeDegree matchingCode₀ := hdeg.trans (congrArg fourCodeDegree hGcode)
    rcases fourCode_degree_one_classifier _ hHdeg with hH | hH | hH
    · exact Or.inl (realization_eq_of_fourCode_eq H G hdist hall (hH.trans hGcode.symm))
    · have hG₁code := (fourCode_matching₁_iff G₁ a b c e).mpr hG₁
      exact Or.inr (Or.inl
        (realization_eq_of_fourCode_eq H G₁ hdist hall (hH.trans hG₁code.symm)))
    · have hG₂code := (fourCode_matching₂_iff G₂ a b c e).mpr hG₂
      exact Or.inr (Or.inr
        (realization_eq_of_fourCode_eq H G₂ hdist hall (hH.trans hG₂code.symm)))

private theorem no_outside_cycle_violates_notK3 {d : V → ℕ}
    (hnotK3 : NotK3Base d) (G G₁ G₂ : Realization d)
    {a b c e : V} (hdist : FourDistinct a b c e)
    (hall : ∀ v : V, v ∈ ({a, b, c, e} : Finset V))
    (h01 : (RealizationGraph d).Adj G G₁)
    (h02 : (RealizationGraph d).Adj G G₂)
    (h12 : (RealizationGraph d).Adj G₁ G₂)
    (hG : InducesFourCycle G.graph a b c e)
    (hG₁ : InducesFourCycle G₁.graph a c b e)
    (hG₂ : InducesFourCycle G₂.graph a e b c) : False := by
  apply hnotK3
  refine ⟨G, G₁, G₂, ?_, ?_, ?_, ?_⟩
  · intro h
    subst G₁
    simpa using h01
  · intro h
    subst G₂
    simpa using h12
  · intro h
    subst G₂
    simpa using h02
  · intro H
    have hsub : edgeSupport (H.edgeFinset ∆ G.edgeFinset) ⊆ {a, b, c, e} := by
      intro v _
      exact hall v
    have hdeg := fourCodeDegree_eq_of_support_subset H G hdist hsub
    have hGcode := (fourCode_cycle₀_iff G a b c e).mpr hG
    have hHdeg : fourCodeDegree (fourCodeOf H a b c e) =
        fourCodeDegree (codeComplement matchingCode₀) :=
      hdeg.trans (congrArg fourCodeDegree hGcode)
    rcases fourCode_degree_two_classifier _ hHdeg with hH | hH | hH
    · exact Or.inl (realization_eq_of_fourCode_eq H G hdist hall (hH.trans hGcode.symm))
    · have hG₁code := (fourCode_cycle₁_iff G₁ a b c e).mpr hG₁
      exact Or.inr (Or.inl
        (realization_eq_of_fourCode_eq H G₁ hdist hall (hH.trans hG₁code.symm)))
    · have hG₂code := (fourCode_cycle₂_iff G₂ a b c e).mpr hG₂
      exact Or.inr (Or.inr
        (realization_eq_of_fourCode_eq H G₂ hdist hall (hH.trans hG₂code.symm)))
/-- **§6.3, the rich four-core lemma, in the form §6 consumes it.** On the main line a pair that
fails the separator-buffer conclusion has no rich triangle whose support contains its difference
support.

The manuscript's route: `D` is then exactly that four-vertex support, and every outside vertex `w`
has `N_D(w)` empty, all of `D`, or `D` minus one element — the types `A`, `B`, `Z_j`, the other sizes
each creating a forbidden `2K₂` or `C₄` in one of the three matchings. The permitted-status table
then makes the `A`s independent, the `B`s a clique, each anticomplete or complete to `D` and to the
at most one `Z`, so a nonempty `A ∪ B` exhibits a nontrivial Tyshkevich composition — contradicting
`MainLine.indecomposable`. A lone `Z` is removed by an explicit switch. With no outside vertex the
sequence is `(1,1,1,1)` or `(2,2,2,2)` and `G(d) = K₃`, which `MainLine.notK3` excludes.

**Verified before being stated**, `compute/sec63_table_check_2026_08_18.py`: through ground order 7,
612 outside vertices at rich failures, every one of type `A`, `B` or `Z_j`, and `D` equal to the rich
support in every case, 0 failures. And under the real hypotheses — active and Tyshkevich-
indecomposable — over 169 such sequences there are **exactly six** rich failures, all at order four,
all the `K₃` base case, with nothing new at orders 5, 6 or 7.

⚠ A first version of that check imposed neither hypothesis and reported 84 rich failures carrying an
outside vertex, which reads as a refutation of this lemma. It is not: the lemma is about main-line
sequences. **A check that omits the hypotheses of the theorem it tests produces a number that looks
like a counterexample**, and this is the second time today that shape appeared. -/
theorem no_rich_failure_of_mainLine {d : V → ℕ} (hd : MainLine d) {X Y : Realization d}
    (hXY : X ≠ Y)
    (hfail : ∀ v : V, v ∈ edgeSupport (X.edgeFinset ∆ Y.edgeFinset) →
      ¬ HasNonBipartiteFibre d v)
    {G G₁ G₂ : Realization d} (hrich : IsRichTriangle d G G₁ G₂)
    (hsub : edgeSupport (X.edgeFinset ∆ Y.edgeFinset) ⊆
      edgeSupport ((G.edgeFinset ∆ G₁.edgeFinset) ∪ (G.edgeFinset ∆ G₂.edgeFinset))) :
    False := by
  classical
  have h01 := hrich.1
  have h02 := hrich.2.1
  have h12 := hrich.2.2.1
  obtain ⟨a, b, c, e, hdist, hsupport, hform⟩ := rich_triangle_normal_form hrich
  let S : Finset V := {a, b, c, e}
  have hScore : S.card = 4 := by
    rcases hdist with ⟨hab, hac, hae, hbc, hbe, hce⟩
    rw [Finset.card_eq_four]
    exact ⟨a, b, c, e, hab, hac, hae, hbc, hbe, hce, rfl⟩
  have hDsub : edgeSupport (X.edgeFinset ∆ Y.edgeFinset) ⊆ S := by
    simpa [S, hsupport] using hsub
  have hDlower := differenceSupport_card_ge_four hXY
  have hDeq : edgeSupport (X.edgeFinset ∆ Y.edgeFinset) = S :=
    Finset.eq_of_subset_of_card_le hDsub (by omega)
  have hforbid : CoreTriangleForbidden (d := d) S := by
    intro A B C hAB hAC hBC
    rw [← hDeq]
    exact failing_pair_forbids_triangle_missing_difference hfail hAB hAC hBC
  have hsub01 : edgeSupport (G.edgeFinset ∆ G₁.edgeFinset) ⊆ S := by
    change edgeSupport (G.edgeFinset ∆ G₁.edgeFinset) ⊆ {a, b, c, e}
    rw [← hsupport]
    exact edgeSupport_mono Finset.subset_union_left
  have hsub02 : edgeSupport (G.edgeFinset ∆ G₂.edgeFinset) ⊆ S := by
    change edgeSupport (G.edgeFinset ∆ G₂.edgeFinset) ⊆ {a, b, c, e}
    rw [← hsupport]
    exact edgeSupport_mono Finset.subset_union_right
  have heq₁ : ∀ w, w ∉ S → ∀ x ∈ S,
      G.graph.Adj w x ↔ G₁.graph.Adj w x := by
    intro w hwS
    have hw : w ∉ edgeSupport (G.edgeFinset ∆ G₁.edgeFinset) :=
      fun h => hwS (hsub01 h)
    have hn := neighborFinset_eq_of_not_mem_edgeSupport_symmDiff G G₁ hw
    intro x _
    have hx := Finset.ext_iff.mp hn x
    simpa [Realization.mem_neighborFinset] using hx
  have heq₂ : ∀ w, w ∉ S → ∀ x ∈ S,
      G.graph.Adj w x ↔ G₂.graph.Adj w x := by
    intro w hwS
    have hw : w ∉ edgeSupport (G.edgeFinset ∆ G₂.edgeFinset) :=
      fun h => hwS (hsub02 h)
    have hn := neighborFinset_eq_of_not_mem_edgeSupport_symmDiff G G₂ hw
    intro x _
    have hx := Finset.ext_iff.mp hn x
    simpa [Realization.mem_neighborFinset] using hx
  rcases hform with ⟨hG, hothers⟩ | ⟨hG, hothers⟩
  · let P : V → Prop := OutsideA G.graph a b c e
    let Q : V → Prop := OutsideB G.graph a b c e
    let Z : V → Prop := OutsideZI G.graph a b c e
    have hpartition : ∀ w, w ∉ S → P w ∨ Q w ∨ Z w := by
      intro w hwS
      rcases hothers with ⟨hG₁, hG₂⟩ | ⟨hG₂, hG₁⟩
      · simpa [P, Q, Z, OutsidePatternI, OutsideA, OutsideB, OutsideZI] using
          outside_pattern_I S hforbid G G₁ G₂ hdist rfl hwS hG hG₁ hG₂
            (heq₁ w hwS) (heq₂ w hwS)
      · simpa [P, Q, Z, OutsidePatternI, OutsideA, OutsideB, OutsideZI] using
          outside_pattern_I S hforbid G G₂ G₁ hdist rfl hwS hG hG₂ hG₁
            (heq₂ w hwS) (heq₁ w hwS)
    have hstatus := outside_status_I S hforbid G hdist rfl hG
    have hPcore : ∀ w, w ∉ S → P w → ∀ x ∈ S, ¬ G.graph.Adj w x := by
      intro w _ hwP x hx
      rcases hwP with ⟨hwa, hwb, hwc, hwe⟩
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have hQcore : ∀ w, w ∉ S → Q w → ∀ x ∈ S, G.graph.Adj w x := by
      intro w _ hwQ x hx
      rcases hwQ with ⟨hwa, hwb, hwc, hwe⟩
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    rcases outside_partition_decomposes_or_all_Z G S P Q Z (by simp [S]) hpartition
        hPcore hQcore hstatus.1 hstatus.2.1 hstatus.2.2.1 hstatus.2.2.2 with hdec | hallZ
    · exact hd.indecomposable hdec
    · by_cases hout : ∃ z : V, z ∉ S
      · obtain ⟨z, hzS⟩ := hout
        exact lone_ZI_violates_core_forbidden S hforbid G hdist rfl hzS hG (hallZ z hzS)
      · have hall : ∀ v : V, v ∈ S := by
          intro v
          by_contra hv
          exact hout ⟨v, hv⟩
        rcases hothers with ⟨hG₁, hG₂⟩ | ⟨hG₂, hG₁⟩
        · exact no_outside_matching_violates_notK3 hd.notK3 G G₁ G₂ hdist hall
            h01 h02 h12 hG hG₁ hG₂
        · exact no_outside_matching_violates_notK3 hd.notK3 G G₂ G₁ hdist hall
            h02 h01 h12.symm hG hG₂ hG₁
  · let P : V → Prop := OutsideA G.graph a b c e
    let Q : V → Prop := OutsideB G.graph a b c e
    let Z : V → Prop := OutsideZIII G.graph a b c e
    have hpartition : ∀ w, w ∉ S → P w ∨ Q w ∨ Z w := by
      intro w hwS
      rcases hothers with ⟨hG₁, hG₂⟩ | ⟨hG₂, hG₁⟩
      · simpa [P, Q, Z, OutsidePatternIII, OutsideA, OutsideB, OutsideZIII] using
          outside_pattern_III S hforbid G G₁ G₂ hdist rfl hwS hG hG₁ hG₂
            (heq₁ w hwS) (heq₂ w hwS)
      · simpa [P, Q, Z, OutsidePatternIII, OutsideA, OutsideB, OutsideZIII] using
          outside_pattern_III S hforbid G G₂ G₁ hdist rfl hwS hG hG₂ hG₁
            (heq₂ w hwS) (heq₁ w hwS)
    have hstatus := outside_status_III S hforbid G hdist rfl hG
    have hPcore : ∀ w, w ∉ S → P w → ∀ x ∈ S, ¬ G.graph.Adj w x := by
      intro w _ hwP x hx
      rcases hwP with ⟨hwa, hwb, hwc, hwe⟩
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have hQcore : ∀ w, w ∉ S → Q w → ∀ x ∈ S, G.graph.Adj w x := by
      intro w _ hwQ x hx
      rcases hwQ with ⟨hwa, hwb, hwc, hwe⟩
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    rcases outside_partition_decomposes_or_all_Z G S P Q Z (by simp [S]) hpartition
        hPcore hQcore hstatus.1 hstatus.2.1 hstatus.2.2.1 hstatus.2.2.2 with hdec | hallZ
    · exact hd.indecomposable hdec
    · by_cases hout : ∃ z : V, z ∉ S
      · obtain ⟨z, hzS⟩ := hout
        exact lone_ZIII_violates_core_forbidden S hforbid G hdist rfl hzS hG (hallZ z hzS)
      · have hall : ∀ v : V, v ∈ S := by
          intro v
          by_contra hv
          exact hout ⟨v, hv⟩
        rcases hothers with ⟨hG₁, hG₂⟩ | ⟨hG₂, hG₁⟩
        · exact no_outside_cycle_violates_notK3 hd.notK3 G G₁ G₂ hdist hall
            h01 h02 h12 hG hG₁ hG₂
        · exact no_outside_cycle_violates_notK3 hd.notK3 G G₂ G₁ hdist hall
            h02 h01 h12.symm hG hG₂ hG₁

/-! ### §6.4. The pseudo-split and split branch -/

private theorem no_rich_triangle_of_failure {d : V → ℕ} (hd : MainLine d)
    {X Y : Realization d} (hXY : X ≠ Y)
    (hfail : ∀ v : V, v ∈ edgeSupport (X.edgeFinset ∆ Y.edgeFinset) →
      ¬ HasNonBipartiteFibre d v) :
    ∀ G G₁ G₂ : Realization d, ¬ IsRichTriangle d G G₁ G₂ := by
  intro G G₁ G₂ hrich
  exact no_rich_failure_of_mainLine hd hXY hfail hrich
    (failing_pair_forbids_triangle_missing_difference hfail
      hrich.1 hrich.2.1 hrich.2.2.1)

private theorem no_induced_matching_of_no_rich {d : V → ℕ}
    (hno : ∀ G G₁ G₂ : Realization d, ¬ IsRichTriangle d G G₁ G₂)
    (G : Realization d) {a b c e : V} (hdist : FourDistinct a b c e) :
    ¬ InducesMatching G.graph a b c e := by
  intro hmatch
  obtain ⟨G₁, G₂, h01, h02, h12, hsupp⟩ :=
    typeI_triangle_certificate G hdist hmatch
  apply hno G G₁ G₂
  refine ⟨h01, h02, h12, ?_⟩
  rw [hsupp]
  rcases hdist with ⟨hab, hac, hae, hbc, hbe, hce⟩
  rw [Finset.card_eq_four]
  exact ⟨a, b, c, e, hab, hac, hae, hbc, hbe, hce, rfl⟩

private theorem no_induced_fourCycle_of_no_rich {d : V → ℕ}
    (hno : ∀ G G₁ G₂ : Realization d, ¬ IsRichTriangle d G G₁ G₂)
    (G : Realization d) {a b c e : V} (hdist : FourDistinct a b c e) :
    ¬ InducesFourCycle G.graph a b c e := by
  intro hcycle
  obtain ⟨G₁, G₂, h01, h02, h12, hsupp⟩ :=
    typeIII_triangle_certificate G hdist hcycle
  apply hno G G₁ G₂
  refine ⟨h01, h02, h12, ?_⟩
  rw [hsupp]
  rcases hdist with ⟨hab, hac, hae, hbc, hbe, hce⟩
  rw [Finset.card_eq_four]
  exact ⟨a, b, c, e, hab, hac, hae, hbc, hbe, hce, rfl⟩

/-! ### Complementation and the chair/kite obstructions -/

/-- Complement a realization. Its degree function is complemented inside the complete graph on
the same labelled ground set. -/
noncomputable def complementRealization {d : V → ℕ} (G : Realization d) :
    Realization (fun u => Fintype.card V - 1 - d u) where
  graph := G.graphᶜ
  adjDecidable := by infer_instance
  degree_eq := by
    intro u
    rw [SimpleGraph.degree_compl, G.degree_eq]

private theorem degree_le_card_sub_one_of_graphical {d : V → ℕ} (hd : Graphical d) (u : V) :
    d u ≤ Fintype.card V - 1 := by
  obtain ⟨G, hG, hdegree⟩ := hd
  letI := hG
  have hlt := G.degree_lt_card_verts u
  rw [hdegree u] at hlt
  omega

private noncomputable def uncomplementRealization {d : V → ℕ} (hd : Graphical d)
    (G : Realization (fun u => Fintype.card V - 1 - d u)) : Realization d where
  graph := G.graphᶜ
  adjDecidable := by infer_instance
  degree_eq := by
    intro u
    rw [SimpleGraph.degree_compl, G.degree_eq]
    have hdu := degree_le_card_sub_one_of_graphical hd u
    omega

private theorem complement_edgeFinset_symmDiff {G H : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel H.Adj] :
    Gᶜ.edgeFinset ∆ Hᶜ.edgeFinset = G.edgeFinset ∆ H.edgeFinset := by
  classical
  ext e
  induction e using Sym2.ind with
  | _ u v =>
      rw [Finset.mem_symmDiff, Finset.mem_symmDiff]
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      rw [SimpleGraph.compl_adj, SimpleGraph.compl_adj]
      by_cases huv : u = v
      · subst v
        have hG := G.loopless.irrefl u
        have hH := H.loopless.irrefl u
        tauto
      · tauto

omit [DecidableEq V] in
private theorem complement_realization_eq_of_graph_eq {d : V → ℕ} {G H : Realization d}
    (h : G.graph = H.graph) : G = H := by
  cases G with
  | mk graphG decG degreeG =>
      cases H with
      | mk graphH decH degreeH =>
          dsimp at h
          subst graphH
          congr
          exact Subsingleton.elim _ _

private theorem uncomplement_complement {d : V → ℕ} (hd : Graphical d)
    (G : Realization d) : uncomplementRealization hd (complementRealization G) = G := by
  apply complement_realization_eq_of_graph_eq
  exact compl_compl G.graph

private theorem complement_uncomplement {d : V → ℕ} (hd : Graphical d)
    (G : Realization (fun u => Fintype.card V - 1 - d u)) :
    complementRealization (uncomplementRealization hd G) = G := by
  apply complement_realization_eq_of_graph_eq
  exact compl_compl G.graph

/-- Complementation is an isomorphism between the realization graphs of a graphical labelled
degree function and its complementary degree function. The graphicality hypothesis is necessary
because subtraction in `ℕ` is truncated for invalid degree functions. -/
noncomputable def realizationGraph_complementIso {d : V → ℕ} (hd : Graphical d) :
    RealizationGraph d ≃g
      RealizationGraph (fun u => Fintype.card V - 1 - d u) :=
  RelIso.mk
    (Equiv.mk complementRealization (uncomplementRealization hd)
      (uncomplement_complement hd) (complement_uncomplement hd))
    (by
      intro G H
      change ((G.graphᶜ.edgeFinset ∆ H.graphᶜ.edgeFinset).card = 4) ↔
        ((G.graph.edgeFinset ∆ H.graph.edgeFinset).card = 4)
      rw [complement_edgeFinset_symmDiff])

/-- The labelled graph induced by `a-b-c-e`, together with the pendant edge `b-f`, is a chair.
The first ten clauses say that the five displayed vertices are pairwise distinct; the last ten
specify all pairs in the induced subgraph. -/
def InducesChair (G : SimpleGraph V) (a b c e f : V) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ e ∧ a ≠ f ∧ b ≠ c ∧ b ≠ e ∧ b ≠ f ∧
    c ≠ e ∧ c ≠ f ∧ e ≠ f ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c e ∧ G.Adj b f ∧
    ¬ G.Adj a c ∧ ¬ G.Adj a e ∧ ¬ G.Adj a f ∧
    ¬ G.Adj b e ∧ ¬ G.Adj c f ∧ ¬ G.Adj e f

/-- A kite is the complement of a chair on the same five labelled vertices. Thus its six induced
edges are `ac, ae, af, be, cf, ef`. -/
def InducesKite (G : SimpleGraph V) (a b c e f : V) : Prop :=
  InducesChair Gᶜ a b c e f

/-- An induced chair in a realization gives two explicit 2-switch neighbors which, together with
the original realization, form a triangle in the realization graph. -/
theorem triangle_of_induced_chair {d : V → ℕ} (G : Realization d) {a b c e f : V}
    (hchair : InducesChair G.graph a b c e f) :
    ∃ G₁ G₂ : Realization d,
      (RealizationGraph d).Adj G G₁ ∧ (RealizationGraph d).Adj G G₂ ∧
        (RealizationGraph d).Adj G₁ G₂ := by
  rcases hchair with
    ⟨hab, hac, hae, haf, hbc, hbe, hbf, hce, hcf, hef,
      hAB, hBC, hCE, hBF, hAC, _hAE, _hAF, hBE, hCF, _hEF⟩
  have hdist : FiveDistinct e c b a f :=
    ⟨hce.symm, hbe.symm, hae.symm, hef, hbc.symm, hac.symm, hcf,
      hab.symm, hbf, haf⟩
  obtain ⟨G₁, G₂, h01, h02, h12, _⟩ :=
    typeII_triangle_certificate G hdist hCE.symm hAB.symm hBF
      (fun h => hBE h.symm) (fun h => hAC h.symm) hCF
  exact ⟨G₁, G₂, h01, h02, h12⟩

/-- An induced kite gives a triangle by complementing to a chair, applying
`triangle_of_induced_chair`, and transporting the resulting triangle back along
`realizationGraph_complementIso`. -/
theorem triangle_of_induced_kite {d : V → ℕ} (G : Realization d) {a b c e f : V}
    (hkite : InducesKite G.graph a b c e f) :
    ∃ G₁ G₂ : Realization d,
      (RealizationGraph d).Adj G G₁ ∧ (RealizationGraph d).Adj G G₂ ∧
        (RealizationGraph d).Adj G₁ G₂ := by
  let dc : V → ℕ := fun u => Fintype.card V - 1 - d u
  let Gc : Realization dc := complementRealization G
  have hchair : InducesChair Gc.graph a b c e f := by
    simpa [Gc, InducesKite, complementRealization] using hkite
  obtain ⟨H₁, H₂, h01, h02, h12⟩ := triangle_of_induced_chair Gc hchair
  let iso : RealizationGraph d ≃g RealizationGraph dc :=
    realizationGraph_complementIso G.toGraphical
  have hG : iso.symm Gc = G := by
    change iso.symm (iso G) = G
    exact iso.symm_apply_apply G
  refine ⟨iso.symm H₁, iso.symm H₂, ?_, ?_, ?_⟩
  · rw [← hG]
    exact iso.symm.map_rel_iff'.2 h01
  · rw [← hG]
    exact iso.symm.map_rel_iff'.2 h02
  · exact iso.symm.map_rel_iff'.2 h12

private def IsSplitAt (G : SimpleGraph V) (C : Finset V) : Prop :=
  G.IsClique (C : Set V) ∧
    ∀ a, a ∉ C → ∀ b, b ∉ C → ¬ G.Adj a b

private def InducesFiveCycle (G : SimpleGraph V) (a b c e f : V) : Prop :=
  FiveDistinct a b c e f ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c e ∧ G.Adj e f ∧ G.Adj f a ∧
    ¬ G.Adj a c ∧ ¬ G.Adj a e ∧ ¬ G.Adj b e ∧ ¬ G.Adj b f ∧ ¬ G.Adj c f

/-- Ordered adjacent pairs wholly outside `C`. Doubling every undirected edge makes the strict
comparison in the optimal-clique proof elementary. -/
private noncomputable def outsideDarts (G : SimpleGraph V) (C : Finset V) : Finset (V × V) := by
  classical
  exact Finset.univ.filter fun p => G.Adj p.1 p.2 ∧ p.1 ∉ C ∧ p.2 ∉ C

private theorem exists_optimal_clique (G : SimpleGraph V) :
    ∃ C : Finset V, G.IsClique (C : Set V) ∧
      (∀ D : Finset V, G.IsClique (D : Set V) → D.card ≤ C.card) ∧
      (∀ D : Finset V, G.IsClique (D : Set V) → D.card = C.card →
        (outsideDarts G C).card ≤ (outsideDarts G D).card) := by
  classical
  let cliques : Finset (Finset V) :=
    Finset.univ.powerset.filter fun C => G.IsClique (C : Set V)
  have hcliques : cliques.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [cliques]
  obtain ⟨C₀, hC₀, hmax⟩ := Finset.exists_max_image cliques Finset.card hcliques
  let maximumCliques : Finset (Finset V) :=
    cliques.filter fun C => C.card = C₀.card
  have hmaximum : maximumCliques.Nonempty := by
    exact ⟨C₀, Finset.mem_filter.mpr ⟨hC₀, rfl⟩⟩
  obtain ⟨C, hC, hmin⟩ :=
    Finset.exists_min_image maximumCliques (fun D => (outsideDarts G D).card) hmaximum
  have hCmem : C ∈ cliques := (Finset.mem_filter.mp hC).1
  have hCcard : C.card = C₀.card := (Finset.mem_filter.mp hC).2
  have hCclique : G.IsClique (C : Set V) := by
    simpa [cliques] using hCmem
  refine ⟨C, hCclique, ?_, ?_⟩
  · intro D hD
    have hDmem : D ∈ cliques := by simp [cliques, hD]
    rw [hCcard]
    exact hmax D hDmem
  · intro D hD hDcard
    apply hmin D
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · simp [cliques, hD]
    · exact hDcard.trans hCcard

private theorem split_or_induced_fiveCycle (G : SimpleGraph V)
    (hmatch : ∀ a b c e, FourDistinct a b c e → ¬ InducesMatching G a b c e)
    (hfour : ∀ a b c e, FourDistinct a b c e → ¬ InducesFourCycle G a b c e) :
    (∃ C : Finset V, IsSplitAt G C) ∨
      ∃ a b c e f : V, InducesFiveCycle G a b c e f := by
  classical
  obtain ⟨C, hCclique, hCmax, hCmin⟩ := exists_optimal_clique G
  have hnonadj (x : V) (hxC : x ∉ C) : ∃ y ∈ C, ¬ G.Adj x y := by
    by_contra h
    push_neg at h
    have hbig : G.IsClique ((insert x C : Finset V) : Set V) := by
      simpa only [Finset.coe_insert] using
        hCclique.insert (by
          intro y hy _
          exact h y hy)
    have := hCmax (insert x C) hbig
    rw [Finset.card_insert_of_notMem hxC] at this
    omega
  have hcomparable (p q : V) (hpC : p ∉ C) (hqC : q ∉ C) (hpq : G.Adj p q) :
      (∀ x ∈ C, G.Adj p x → G.Adj q x) ∨
        (∀ x ∈ C, G.Adj q x → G.Adj p x) := by
    by_cases hpqsub : ∀ x ∈ C, G.Adj p x → G.Adj q x
    · exact Or.inl hpqsub
    by_cases hqpsub : ∀ x ∈ C, G.Adj q x → G.Adj p x
    · exact Or.inr hqpsub
    push_neg at hpqsub hqpsub
    obtain ⟨x, hxC, hpx, hqx⟩ := hpqsub
    obtain ⟨y, hyC, hqy, hpy⟩ := hqpsub
    have hxy : G.Adj x y := by
      apply hCclique hxC hyC
      intro hxy
      subst y
      exact hpy hpx
    have hdist : FourDistinct p y q x := by
      refine ⟨?_, hpq.ne, ?_, ?_, ?_, ?_⟩
      · exact fun h => hpC (h ▸ hyC)
      · exact fun h => hpC (h ▸ hxC)
      · exact fun h => hqC (h.symm ▸ hyC)
      · exact fun h => hpy (h ▸ hpx)
      · exact fun h => hqC (h ▸ hxC)
    exact False.elim (hfour p y q x hdist
      ⟨hpy, hqx, hpq, hpx, hqy.symm, hxy.symm⟩)
  by_cases hstable : ∀ a, a ∉ C → ∀ b, b ∉ C → ¬ G.Adj a b
  · exact Or.inl ⟨C, hCclique, hstable⟩
  push_neg at hstable
  obtain ⟨a, haC, b, hbC, hab⟩ := hstable
  have oriented (a b : V) (haC : a ∉ C) (hbC : b ∉ C) (hab : G.Adj a b)
      (hsub : ∀ x ∈ C, G.Adj a x → G.Adj b x) :
      (∃ D : Finset V, IsSplitAt G D) ∨
        ∃ p q r s t : V, InducesFiveCycle G p q r s t := by
    obtain ⟨z, hzC, hzb⟩ := hnonadj b hbC
    have hza : ¬ G.Adj a z := by
      intro haz
      exact hzb (hsub z hzC haz)
    have hb_all : ∀ y ∈ C, y ≠ z → G.Adj b y := by
      intro y hyC hyz
      by_contra hby
      have hay : ¬ G.Adj a y := by
        intro hay
        exact hby (hsub y hyC hay)
      have hyzAdj : G.Adj y z := hCclique hyC hzC hyz
      have hdist : FourDistinct a b y z := by
        refine ⟨hab.ne, ?_, ?_, ?_, ?_, hyz⟩
        · exact fun h => haC (h ▸ hyC)
        · exact fun h => haC (h ▸ hzC)
        · exact fun h => hbC (h ▸ hyC)
        · exact fun h => hbC (h ▸ hzC)
      exact hmatch a b y z hdist
        ⟨hab, hyzAdj, hay, hza, hby, hzb⟩
    by_cases hout : ∃ x : V, x ∉ C ∧ G.Adj z x
    · obtain ⟨x, hxC, hzx⟩ := hout
      have hxb : ¬ G.Adj x b := by
        intro hxb
        have hbx : G.Adj b x := hxb.symm
        have hbxSub : ∀ y ∈ C, G.Adj b y → G.Adj x y := by
          rcases hcomparable b x hbC hxC hbx with h | h
          · exact h
          · exact False.elim (hzb (h z hzC hzx.symm))
        have hxAll : ∀ y ∈ C, G.Adj x y := by
          intro y hyC
          by_cases hyz : y = z
          · subst y
            exact hzx.symm
          · exact hbxSub y hyC (hb_all y hyC hyz)
        have hbig : G.IsClique ((insert x C : Finset V) : Set V) := by
          simpa only [Finset.coe_insert] using
            hCclique.insert (by
              intro y hy _
              exact hxAll y hy)
        have := hCmax (insert x C) hbig
        rw [Finset.card_insert_of_notMem hxC] at this
        omega
      have hxa : G.Adj a x := by
        by_contra hax
        have hdist : FourDistinct a b z x := by
          refine ⟨hab.ne, ?_, ?_, ?_, ?_, hzx.ne⟩
          · exact fun h => haC (h ▸ hzC)
          · intro h
            subst x
            exact hza hzx.symm
          · exact fun h => hbC (h ▸ hzC)
          · intro h
            subst x
            exact hzb hzx.symm
        exact hmatch a b z x hdist
          ⟨hab, hzx, hza, hax, hzb, fun h => hxb h.symm⟩
      obtain ⟨y, hyC, hxy⟩ := hnonadj x hxC
      have hyz : y ≠ z := by
        intro h
        subst y
        exact hxy hzx.symm
      have hyb : G.Adj y b := (hb_all y hyC hyz).symm
      have hzy : G.Adj z y := hCclique hzC hyC hyz.symm
      by_cases hay : G.Adj a y
      · have hdist : FourDistinct x y z a := by
          refine ⟨?_, ?_, hxa.ne.symm, hyz, ?_, ?_⟩
          · exact fun h => hxC (h ▸ hyC)
          · exact hzx.ne.symm
          · exact fun h => haC (h.symm ▸ hyC)
          · exact fun h => haC (h.symm ▸ hzC)
        exact False.elim (hfour x y z a hdist
          ⟨hxy, (fun h => hza h.symm), hzx.symm, hxa.symm, hzy.symm, hay.symm⟩)
      · right
        refine ⟨x, z, y, b, a, ?_⟩
        have hxb_ne : x ≠ b := by
          intro h
          subst x
          exact hzb hzx.symm
        have hdist : FiveDistinct x z y b a := by
          refine ⟨hzx.ne.symm, ?_, hxb_ne, hxa.ne.symm, hyz.symm, ?_, ?_, ?_, ?_, hab.ne.symm⟩
          · exact fun h => hxC (h ▸ hyC)
          · exact fun h => hbC (h.symm ▸ hzC)
          · exact fun h => haC (h.symm ▸ hzC)
          · exact fun h => hbC (h.symm ▸ hyC)
          · exact fun h => haC (h.symm ▸ hyC)
        exact ⟨hdist, hzx.symm, hzy, hyb, hab.symm, hxa,
          hxy, hxb, (fun h => hzb h.symm), (fun h => hza h.symm), (fun h => hay h.symm)⟩
    · push_neg at hout
      let C' : Finset V := insert b (C.erase z)
      have hbCerase : b ∉ C.erase z := fun h => hbC (Finset.mem_of_mem_erase h)
      have hC'erase : G.IsClique ((C.erase z : Finset V) : Set V) :=
        hCclique.subset (by simp)
      have hC'clique : G.IsClique (C' : Set V) := by
        simpa only [C', Finset.coe_insert] using
          hC'erase.insert (by
            intro y hy _
            exact hb_all y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy))
      have hC'card : C'.card = C.card := by
        rw [show C' = insert b (C.erase z) from rfl,
          Finset.card_insert_of_notMem hbCerase, Finset.card_erase_of_mem hzC]
        have hCpos : 0 < C.card := Finset.card_pos.mpr ⟨z, hzC⟩
        omega
      have hDsubset : outsideDarts G C' ⊆ outsideDarts G C := by
        intro p hp
        rcases p with ⟨u, v⟩
        simp only [outsideDarts, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        rcases hp with ⟨huv, huC', hvC'⟩
        have huC : u ∉ C := by
          intro huC
          have huz : u = z := by
            by_contra huz
            exact huC' (by simp [C', huC, huz])
          have hvC : v ∉ C := by
            intro hvC
            have hvz : v = z := by
              by_contra hvz
              exact hvC' (by simp [C', hvC, hvz])
            subst u
            subst v
            exact G.irrefl huv
          subst u
          exact hout v hvC huv
        have hvC : v ∉ C := by
          intro hvC
          have hvz : v = z := by
            by_contra hvz
            exact hvC' (by simp [C', hvC, hvz])
          subst v
          exact hout u huC huv.symm
        exact ⟨huv, huC, hvC⟩
      have habOld : (a, b) ∈ outsideDarts G C := by
        simp [outsideDarts, hab, haC, hbC]
      have habNew : (a, b) ∉ outsideDarts G C' := by
        simp [outsideDarts, C']
      have hproper : outsideDarts G C' ⊂ outsideDarts G C := by
        exact Finset.ssubset_iff_subset_ne.mpr
          ⟨hDsubset, fun h => habNew (h ▸ habOld)⟩
      have hlt := Finset.card_lt_card hproper
      have hmin := hCmin C' hC'clique hC'card
      omega
  rcases hcomparable a b haC hbC hab with hsub | hsub
  · exact oriented a b haC hbC hab hsub
  · exact oriented b a hbC haC hab.symm hsub

private theorem fiveDistinct_rotate {a b c e f : V} (hd : FiveDistinct a b c e f) :
    FiveDistinct b c e f a := by
  rcases hd with ⟨habne, hacne, haene, hafne, hbcne, hbene, hbfne, hcene, hcfne, hefne⟩
  exact ⟨hbcne, hbene, hbfne, habne.symm, hcene, hcfne, hacne.symm,
    hefne, haene.symm, hafne.symm⟩

private theorem inducesFiveCycle_rotate {G : SimpleGraph V} {a b c e f : V}
    (h : InducesFiveCycle G a b c e f) : InducesFiveCycle G b c e f a := by
  rcases h with ⟨hd, hab, hbc, hce, hef, hfa, hac, hae, hbe, hbf, hcf⟩
  exact ⟨fiveDistinct_rotate hd,
    hbc, hce, hef, hfa, hab, hbe, hbf, hcf,
      (fun h => hac h.symm), (fun h => hae h.symm)⟩

private theorem fiveCycle_boundary_forbidden (G : SimpleGraph V)
    (hmatch : ∀ a b c e, FourDistinct a b c e → ¬ InducesMatching G a b c e)
    (hfour : ∀ a b c e, FourDistinct a b c e → ¬ InducesFourCycle G a b c e)
    {a b c e f w : V} (hcycle : InducesFiveCycle G a b c e f)
    (hw : w ≠ a ∧ w ≠ b ∧ w ≠ c ∧ w ≠ e ∧ w ≠ f)
    (hwa : G.Adj w a) (hwb : ¬ G.Adj w b) : False := by
  rcases hcycle with ⟨hd, hab, hbc, hce, hef, hfa, hac, hae, hbe, hbf, hcf⟩
  rcases hd with ⟨habne, hacne, haene, hafne, hbcne, hbene, hbfne, hcene, hcfne, hefne⟩
  rcases hw with ⟨hwa_ne, hwb_ne, hwc_ne, hwe_ne, hwf_ne⟩
  by_cases hwc : G.Adj w c
  · exact hfour a c b w
      ⟨hacne, habne, hwa.ne.symm, hbcne.symm, hwc.ne.symm, hwb_ne.symm⟩
      ⟨hac, fun h => hwb h.symm, hab, hwa.symm, hbc.symm, hwc.symm⟩
  by_cases hwe : G.Adj w e
  · by_cases hwf : G.Adj w f
    · exact hmatch w f b c
        ⟨hwf.ne, hwb_ne, hwc_ne, hbfne.symm, hcfne.symm, hbcne⟩
        ⟨hwf, hbc, hwb, hwc, (fun h => hbf h.symm), (fun h => hcf h.symm)⟩
    · exact hfour e a f w
        ⟨haene.symm, hef.ne, hwe.ne.symm, hafne, hwa.ne.symm, hwf_ne.symm⟩
        ⟨(fun h => hae h.symm), (fun h => hwf h.symm),
          hef, hwe.symm, hfa.symm, hwa.symm⟩
  · by_cases hwf : G.Adj w f
    · exact hmatch w a c e
        ⟨hwa.ne, hwc_ne, hwe_ne, hacne, haene, hcene⟩
        ⟨hwa, hce, hwc, hwe, hac, hae⟩
    · exact hmatch w a c e
        ⟨hwa.ne, hwc_ne, hwe_ne, hacne, haene, hcene⟩
        ⟨hwa, hce, hwc, hwe, hac, hae⟩

private theorem outside_fiveCycle_uniform (G : SimpleGraph V)
    (hmatch : ∀ a b c e, FourDistinct a b c e → ¬ InducesMatching G a b c e)
    (hfour : ∀ a b c e, FourDistinct a b c e → ¬ InducesFourCycle G a b c e)
    {a b c e f w : V} (hcycle : InducesFiveCycle G a b c e f)
    (hw : w ∉ ({a, b, c, e, f} : Finset V)) :
    (G.Adj w a ∧ G.Adj w b ∧ G.Adj w c ∧ G.Adj w e ∧ G.Adj w f) ∨
      (¬ G.Adj w a ∧ ¬ G.Adj w b ∧ ¬ G.Adj w c ∧ ¬ G.Adj w e ∧ ¬ G.Adj w f) := by
  have hwdist : w ≠ a ∧ w ≠ b ∧ w ≠ c ∧ w ≠ e ∧ w ≠ f := by
    simpa using hw
  have h₀ := hcycle
  have h₁ := inducesFiveCycle_rotate h₀
  have h₂ := inducesFiveCycle_rotate h₁
  have h₃ := inducesFiveCycle_rotate h₂
  have h₄ := inducesFiveCycle_rotate h₃
  by_cases hwa : G.Adj w a <;> by_cases hwb : G.Adj w b <;>
    by_cases hwc : G.Adj w c <;> by_cases hwe : G.Adj w e <;>
    by_cases hwf : G.Adj w f
  all_goals first
    | exact Or.inl ⟨hwa, hwb, hwc, hwe, hwf⟩
    | exact Or.inr ⟨hwa, hwb, hwc, hwe, hwf⟩
    | exact False.elim (fiveCycle_boundary_forbidden G hmatch hfour h₀ hwdist hwa hwb)
    | exact False.elim (fiveCycle_boundary_forbidden G hmatch hfour h₁
        ⟨hwdist.2.1, hwdist.2.2.1, hwdist.2.2.2.1, hwdist.2.2.2.2, hwdist.1⟩ hwb hwc)
    | exact False.elim (fiveCycle_boundary_forbidden G hmatch hfour h₂
        ⟨hwdist.2.2.1, hwdist.2.2.2.1, hwdist.2.2.2.2, hwdist.1, hwdist.2.1⟩ hwc hwe)
    | exact False.elim (fiveCycle_boundary_forbidden G hmatch hfour h₃
        ⟨hwdist.2.2.2.1, hwdist.2.2.2.2, hwdist.1, hwdist.2.1, hwdist.2.2.1⟩ hwe hwf)
    | exact False.elim (fiveCycle_boundary_forbidden G hmatch hfour h₄
        ⟨hwdist.2.2.2.2, hwdist.1, hwdist.2.1, hwdist.2.2.1, hwdist.2.2.2.1⟩ hwf hwa)

private theorem fiveCycle_decomposable_or_univ {d : V → ℕ} (G : Realization d)
    (hmatch : ∀ a b c e, FourDistinct a b c e → ¬ InducesMatching G.graph a b c e)
    (hfour : ∀ a b c e, FourDistinct a b c e → ¬ InducesFourCycle G.graph a b c e)
    {a b c e f : V} (hcycle : InducesFiveCycle G.graph a b c e f) :
    TyshkevichDecomposable d ∨ (Finset.univ : Finset V) = {a, b, c, e, f} := by
  classical
  let S : Finset V := {a, b, c, e, f}
  let A : Finset V := Sᶜ.filter fun w => G.graph.Adj w a
  have huniform (w : V) (hwS : w ∉ S) :
      (G.graph.Adj w a ∧ G.graph.Adj w b ∧ G.graph.Adj w c ∧
          G.graph.Adj w e ∧ G.graph.Adj w f) ∨
        (¬ G.graph.Adj w a ∧ ¬ G.graph.Adj w b ∧ ¬ G.graph.Adj w c ∧
          ¬ G.graph.Adj w e ∧ ¬ G.graph.Adj w f) := by
    exact outside_fiveCycle_uniform G.graph hmatch hfour hcycle hwS
  have hAcomplete (w : V) (hwA : w ∈ A) :
      G.graph.Adj w a ∧ G.graph.Adj w b ∧ G.graph.Adj w c ∧
        G.graph.Adj w e ∧ G.graph.Adj w f := by
    have hwS : w ∉ S := by simpa [A] using (Finset.mem_filter.mp hwA).1
    have hwa : G.graph.Adj w a := (Finset.mem_filter.mp hwA).2
    rcases huniform w hwS with h | h
    · exact h
    · exact False.elim (h.1 hwa)
  have hBanti (w : V) (hwB : w ∈ Sᶜ \ A) :
      ¬ G.graph.Adj w a ∧ ¬ G.graph.Adj w b ∧ ¬ G.graph.Adj w c ∧
        ¬ G.graph.Adj w e ∧ ¬ G.graph.Adj w f := by
    have hwS : w ∉ S := by
      simpa using (Finset.mem_compl.mp (Finset.mem_sdiff.mp hwB).1)
    have hwa : ¬ G.graph.Adj w a := by
      intro hwa
      exact (Finset.mem_sdiff.mp hwB).2 (Finset.mem_filter.mpr ⟨by simpa using hwS, hwa⟩)
    rcases huniform w hwS with h | h
    · exact False.elim (hwa h.1)
    · exact h
  have hAclique : G.graph.IsClique (A : Set V) := by
    intro u hu v hv huv
    have hu' : u ∈ A := hu
    have hv' : v ∈ A := hv
    by_contra huvAdj
    rcases hcycle with ⟨hd, _, _, _, _, _, hac, _, _, _, _⟩
    have hdist : FourDistinct u v a c := by
      rcases hd with ⟨_, hacne, _, _, _, _, _, _, _, _⟩
      have huS : u ∉ S := by simpa [A] using (Finset.mem_filter.mp hu').1
      have hvS : v ∉ S := by simpa [A] using (Finset.mem_filter.mp hv').1
      have huSD : u ≠ a ∧ u ≠ b ∧ u ≠ c ∧ u ≠ e ∧ u ≠ f := by simpa [S] using huS
      have hvSD : v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ e ∧ v ≠ f := by simpa [S] using hvS
      exact ⟨huv, huSD.1, huSD.2.2.1, hvSD.1, hvSD.2.2.1, hacne⟩
    have huall := hAcomplete u hu'
    have hvall := hAcomplete v hv'
    exact hfour u v a c hdist
      ⟨huvAdj, hac, huall.1, huall.2.2.1, hvall.1, hvall.2.2.1⟩
  have hBindep : ∀ u ∈ Sᶜ \ A, ∀ w ∈ Sᶜ \ A, ¬ G.graph.Adj u w := by
    intro u hu v hv huv
    rcases hcycle with ⟨hd, hab, _, _, _, _, _, _, _, _, _⟩
    rcases hd with ⟨habne, _, _, _, _, _, _, _, _, _⟩
    have huS : u ∉ S := by
      simpa using (Finset.mem_compl.mp (Finset.mem_sdiff.mp hu).1)
    have hvS : v ∉ S := by
      simpa using (Finset.mem_compl.mp (Finset.mem_sdiff.mp hv).1)
    have hdist : FourDistinct u v a b := by
      have huSD : u ≠ a ∧ u ≠ b ∧ u ≠ c ∧ u ≠ e ∧ u ≠ f := by simpa [S] using huS
      have hvSD : v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ e ∧ v ≠ f := by simpa [S] using hvS
      exact ⟨huv.ne, huSD.1, huSD.2.1, hvSD.1, hvSD.2.1, habne⟩
    have huanti := hBanti u hu
    have hvanti := hBanti v hv
    exact hmatch u v a b hdist
      ⟨huv, hab, huanti.1, huanti.2.1, hvanti.1, hvanti.2.1⟩
  have hAC : ∀ x ∈ A, ∀ y ∈ S, G.graph.Adj x y := by
    intro x hx y hy
    have hxall := hAcomplete x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact hxall.1
    · exact hxall.2.1
    · exact hxall.2.2.1
    · exact hxall.2.2.2.1
    · exact hxall.2.2.2.2
  have hBC : ∀ x ∈ Sᶜ \ A, ∀ y ∈ S, ¬ G.graph.Adj x y := by
    intro x hx y hy
    have hxall := hBanti x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact hxall.1
    · exact hxall.2.1
    · exact hxall.2.2.1
    · exact hxall.2.2.2.1
    · exact hxall.2.2.2.2
  by_cases hout : Sᶜ.Nonempty
  · left
    refine ⟨G, A, S, ?_, hout, ?_, hAclique, hBindep, hAC, hBC⟩
    · simp [S]
    · exact fun x hx => (Finset.mem_filter.mp hx).1
  · right
    have hempty : Sᶜ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hout
    ext x
    have hxS : x ∈ S := by
      by_contra hx
      have : x ∈ Sᶜ := Finset.mem_compl.mpr hx
      rw [hempty] at this
      simpa using this
    simpa [S] using hxS

private def fiveBit (b : Bool) : Nat := if b then 1 else 0

private def fiveCodeTwoRegular (x : Fin 10 → Bool) : Bool :=
  decide (fiveBit (x 0) + fiveBit (x 1) + fiveBit (x 2) + fiveBit (x 3) = 2) &&
  decide (fiveBit (x 0) + fiveBit (x 4) + fiveBit (x 5) + fiveBit (x 6) = 2) &&
  decide (fiveBit (x 1) + fiveBit (x 4) + fiveBit (x 7) + fiveBit (x 8) = 2) &&
  decide (fiveBit (x 2) + fiveBit (x 5) + fiveBit (x 7) + fiveBit (x 9) = 2) &&
  decide (fiveBit (x 3) + fiveBit (x 6) + fiveBit (x 8) + fiveBit (x 9) = 2)

private def fiveCodeDistance (x y : Fin 10 → Bool) : Nat :=
  fiveBit (x 0 != y 0) + fiveBit (x 1 != y 1) + fiveBit (x 2 != y 2) +
  fiveBit (x 3 != y 3) + fiveBit (x 4 != y 4) + fiveBit (x 5 != y 5) +
  fiveBit (x 6 != y 6) + fiveBit (x 7 != y 7) + fiveBit (x 8 != y 8) +
  fiveBit (x 9 != y 9)

/-- One side of the crown bipartition, written on the ten possible edges of five vertices. -/
private def fiveCodeColor (x : Fin 10 → Bool) : Bool := decide (
  x = ![true, true, false, false, false, true, false, false, true, true] ∨
  x = ![true, false, true, false, false, false, true, true, true, false] ∨
  x = ![true, false, false, true, true, false, false, true, false, true] ∨
  x = ![false, true, true, false, true, false, true, false, false, true] ∨
  x = ![false, true, false, true, false, true, true, true, false, false] ∨
  x = ![false, false, true, true, true, true, false, false, true, false])

/-- The twelve two-regular graphs on five labelled vertices, written in edge-code order. -/
private def fiveCodeTwoRegularList : List (Fin 10 → Bool) :=
  [![false, false, true, true, true, false, true, true, false, false],
   ![false, false, true, true, true, true, false, false, true, false],
   ![false, true, false, true, false, true, true, true, false, false],
   ![false, true, false, true, true, true, false, false, false, true],
   ![false, true, true, false, false, true, true, false, true, false],
   ![false, true, true, false, true, false, true, false, false, true],
   ![true, false, false, true, false, true, false, true, true, false],
   ![true, false, false, true, true, false, false, true, false, true],
   ![true, false, true, false, false, false, true, true, true, false],
   ![true, false, true, false, true, false, false, false, true, true],
   ![true, true, false, false, false, false, true, true, false, true],
   ![true, true, false, false, false, true, false, false, true, true]]

private def fiveFiniteDecidableForall {α : Type*} [Fintype α] {p : α → Prop}
    (h : ∀ x, Decidable (p x)) : Decidable (∀ x, p x) :=
  @Fintype.decidableForallFintype α p h _

set_option maxRecDepth 5000 in
private theorem fiveCodeTwoRegular_mem :
    ∀ x : Fin 10 → Bool,
      fiveCodeTwoRegular x = true → x ∈ fiveCodeTwoRegularList := by
  letI : Decidable (∀ x : Fin 10 → Bool,
      fiveCodeTwoRegular x = true → x ∈ fiveCodeTwoRegularList) :=
    fiveFiniteDecidableForall fun _ => inferInstance
  decide

private def fiveCodeProperOnList : Bool :=
  fiveCodeTwoRegularList.all fun x =>
    fiveCodeTwoRegularList.all fun y =>
      decide (fiveCodeDistance x y = 4 → fiveCodeColor x ≠ fiveCodeColor y)

private theorem fiveCodeProperOnList_ok : fiveCodeProperOnList = true := by decide

private theorem fiveCodeColor_proper (x y : Fin 10 → Bool)
    (hx : fiveCodeTwoRegular x = true) (hy : fiveCodeTwoRegular y = true)
    (hxy : fiveCodeDistance x y = 4) : fiveCodeColor x ≠ fiveCodeColor y := by
  have hxmem := fiveCodeTwoRegular_mem x hx
  have hymem := fiveCodeTwoRegular_mem y hy
  have hxall := List.all_eq_true.mp fiveCodeProperOnList_ok x hxmem
  have hyall := List.all_eq_true.mp hxall y hymem
  exact of_decide_eq_true hyall hxy

private def fiveGraphCode (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b c e f : V) : Fin 10 → Bool :=
  ![decide (G.Adj a b), decide (G.Adj a c), decide (G.Adj a e), decide (G.Adj a f),
    decide (G.Adj b c), decide (G.Adj b e), decide (G.Adj b f),
    decide (G.Adj c e), decide (G.Adj c f), decide (G.Adj e f)]

private theorem five_degree_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b c e f : V} (huniv : (Finset.univ : Finset V) = {a, b, c, e, f})
    (hd : FiveDistinct a b c e f) :
    G.degree a = (if G.Adj a b then 1 else 0) + (if G.Adj a c then 1 else 0) +
      (if G.Adj a e then 1 else 0) + (if G.Adj a f then 1 else 0) := by
  rcases hd with ⟨hab, hac, hae, haf, hbc, hbe, hbf, hce, hcf, hef⟩
  rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter, huniv]
  by_cases habA : G.Adj a b <;> by_cases hacA : G.Adj a c <;>
    by_cases haeA : G.Adj a e <;> by_cases hafA : G.Adj a f <;>
    simp [Finset.filter_insert, Finset.filter_singleton, habA, hacA, haeA, hafA,
      hab, hac, hae, haf, hbc, hbe, hbf, hce, hcf, hef]

private theorem fiveGraphCode_twoRegular {d : V → ℕ} (G₀ H : Realization d)
    {a b c e f : V} (huniv : (Finset.univ : Finset V) = {a, b, c, e, f})
    (hcycle : InducesFiveCycle G₀.graph a b c e f) :
    fiveCodeTwoRegular (fiveGraphCode H.graph a b c e f) = true := by
  rcases hcycle with ⟨hd₀, hab, hbc, hce, hef, hfa, hac, hae, hbe, hbf, hcf⟩
  have h₁ := inducesFiveCycle_rotate
    (show InducesFiveCycle G₀.graph a b c e f from
      ⟨hd₀, hab, hbc, hce, hef, hfa, hac, hae, hbe, hbf, hcf⟩)
  have h₂ := inducesFiveCycle_rotate h₁
  have h₃ := inducesFiveCycle_rotate h₂
  have h₄ := inducesFiveCycle_rotate h₃
  have huniv₁ : (Finset.univ : Finset V) = {b, c, e, f, a} := by
    rw [huniv]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have huniv₂ : (Finset.univ : Finset V) = {c, e, f, a, b} := by
    rw [huniv]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have huniv₃ : (Finset.univ : Finset V) = {e, f, a, b, c} := by
    rw [huniv]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have huniv₄ : (Finset.univ : Finset V) = {f, a, b, c, e} := by
    rw [huniv]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hda : d a = 2 := by
    rw [← G₀.degree_eq a, five_degree_eq_sum G₀.graph huniv hd₀]
    have hafAdj : G₀.graph.Adj a f := hfa.symm
    simp [hab, hac, hae, hafAdj]
  have hdb : d b = 2 := by
    rw [← G₀.degree_eq b, five_degree_eq_sum G₀.graph huniv₁ h₁.1]
    simp [hab, hbc, hbe, hbf, SimpleGraph.adj_comm]
  have hdc : d c = 2 := by
    rw [← G₀.degree_eq c, five_degree_eq_sum G₀.graph huniv₂ h₂.1]
    simp [hbc, hce, hac, hcf, SimpleGraph.adj_comm]
  have hde : d e = 2 := by
    rw [← G₀.degree_eq e, five_degree_eq_sum G₀.graph huniv₃ h₃.1]
    simp [hce, hef, hae, hbe, SimpleGraph.adj_comm]
  have hdf : d f = 2 := by
    rw [← G₀.degree_eq f, five_degree_eq_sum G₀.graph huniv₄ h₄.1]
    have hafAdj : G₀.graph.Adj a f := hfa.symm
    simp [hef, hafAdj, hbf, hcf, SimpleGraph.adj_comm]
  have ha := five_degree_eq_sum H.graph huniv hd₀
  have hb := five_degree_eq_sum H.graph huniv₁ h₁.1
  have hc := five_degree_eq_sum H.graph huniv₂ h₂.1
  have he := five_degree_eq_sum H.graph huniv₃ h₃.1
  have hf := five_degree_eq_sum H.graph huniv₄ h₄.1
  rw [H.degree_eq a, hda] at ha
  rw [H.degree_eq b, hdb] at hb
  rw [H.degree_eq c, hdc] at hc
  rw [H.degree_eq e, hde] at he
  rw [H.degree_eq f, hdf] at hf
  simp [fiveCodeTwoRegular, fiveGraphCode, fiveBit, Bool.and_eq_true]
  all_goals simp only [SimpleGraph.adj_comm] at hb hc he hf
  all_goals omega

private theorem fiveGraphCode_distance_of_adj {d : V → ℕ} (H K : Realization d)
    {a b c e f : V} (huniv : (Finset.univ : Finset V) = {a, b, c, e, f})
    (hd : FiveDistinct a b c e f) (hHK : (RealizationGraph d).Adj H K) :
    fiveCodeDistance (fiveGraphCode H.graph a b c e f)
      (fiveGraphCode K.graph a b c e f) = 4 := by
  let D : SimpleGraph V :=
    { Adj := fun x y => decide (H.graph.Adj x y) ≠ decide (K.graph.Adj x y)
      symm := by
        constructor
        intro x y h
        simpa only [SimpleGraph.adj_comm] using h
      loopless := by
        constructor
        intro x
        simp }
  letI : DecidableRel D.Adj := Classical.decRel _
  have hDedge : D.edgeFinset = H.edgeFinset ∆ K.edgeFinset := by
    ext s
    induction s using Sym2.inductionOn with
    | _ x y =>
        by_cases hH : H.graph.Adj x y <;> by_cases hK : K.graph.Adj x y <;>
          simp [D, Realization.edgeFinset, SimpleGraph.mem_edgeFinset,
            SimpleGraph.mem_edgeSet, Finset.mem_symmDiff, hH, hK]
  have hDcard : D.edgeFinset.card = 4 := by
    rw [hDedge]
    exact hHK
  have hsum := D.sum_degrees_eq_twice_card_edges
  rw [hDcard, huniv] at hsum
  have h₁ : FiveDistinct b c e f a := fiveDistinct_rotate hd
  have h₂ : FiveDistinct c e f a b := fiveDistinct_rotate h₁
  have h₃ : FiveDistinct e f a b c := fiveDistinct_rotate h₂
  have h₄ : FiveDistinct f a b c e := fiveDistinct_rotate h₃
  have huniv₁ : (Finset.univ : Finset V) = {b, c, e, f, a} := by
    rw [huniv]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have huniv₂ : (Finset.univ : Finset V) = {c, e, f, a, b} := by
    rw [huniv]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have huniv₃ : (Finset.univ : Finset V) = {e, f, a, b, c} := by
    rw [huniv]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have huniv₄ : (Finset.univ : Finset V) = {f, a, b, c, e} := by
    rw [huniv]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have ha := five_degree_eq_sum D huniv hd
  have hb := five_degree_eq_sum D huniv₁ h₁
  have hc := five_degree_eq_sum D huniv₂ h₂
  have he := five_degree_eq_sum D huniv₃ h₃
  have hf := five_degree_eq_sum D huniv₄ h₄
  rcases hd with ⟨hab, hac, hae, haf, hbc, hbe, hbf, hce, hcf, hef⟩
  simp [hab, hac, hae, haf, hbc, hbe, hbf, hce, hcf, hef] at hsum
  have hbit (x y : V) :
      fiveBit (decide (H.graph.Adj x y) != decide (K.graph.Adj x y)) =
        (if D.Adj x y then 1 else 0) := by
    by_cases hHxy : H.graph.Adj x y <;> by_cases hKxy : K.graph.Adj x y <;>
      simp [fiveBit, D, hHxy, hKxy]
  change
    fiveBit (decide (H.graph.Adj a b) != decide (K.graph.Adj a b)) +
      fiveBit (decide (H.graph.Adj a c) != decide (K.graph.Adj a c)) +
      fiveBit (decide (H.graph.Adj a e) != decide (K.graph.Adj a e)) +
      fiveBit (decide (H.graph.Adj a f) != decide (K.graph.Adj a f)) +
      fiveBit (decide (H.graph.Adj b c) != decide (K.graph.Adj b c)) +
      fiveBit (decide (H.graph.Adj b e) != decide (K.graph.Adj b e)) +
      fiveBit (decide (H.graph.Adj b f) != decide (K.graph.Adj b f)) +
      fiveBit (decide (H.graph.Adj c e) != decide (K.graph.Adj c e)) +
      fiveBit (decide (H.graph.Adj c f) != decide (K.graph.Adj c f)) +
      fiveBit (decide (H.graph.Adj e f) != decide (K.graph.Adj e f)) = 4
  rw [hbit a b, hbit a c, hbit a e, hbit a f, hbit b c,
    hbit b e, hbit b f, hbit c e, hbit c f, hbit e f]
  simp only [SimpleGraph.adj_comm] at ha hb hc he hf
  omega

private theorem fiveCycle_realizationGraph_colorable {d : V → ℕ} (G₀ : Realization d)
    {a b c e f : V} (huniv : (Finset.univ : Finset V) = {a, b, c, e, f})
    (hcycle : InducesFiveCycle G₀.graph a b c e f) :
    (RealizationGraph d).Colorable 2 := by
  classical
  let col : Realization d → Fin 2 := fun G =>
    ⟨if fiveCodeColor (fiveGraphCode G.graph a b c e f) then 1 else 0, by split <;> omega⟩
  refine ⟨⟨col, ?_⟩⟩
  intro H K hHK
  have hH := fiveGraphCode_twoRegular G₀ H huniv hcycle
  have hK := fiveGraphCode_twoRegular G₀ K huniv hcycle
  have hdist := fiveGraphCode_distance_of_adj H K huniv hcycle.1 hHK
  have hcol := fiveCodeColor_proper _ _ hH hK hdist
  simp only [col]
  by_cases hHc : fiveCodeColor (fiveGraphCode H.graph a b c e f) <;>
    by_cases hKc : fiveCodeColor (fiveGraphCode K.graph a b c e f) <;>
    simp_all

private theorem realization_split_of_failure {d : V → ℕ} (hd : MainLine d)
    {X Y : Realization d} (hXY : X ≠ Y) (hfail : ∀ v, ¬ AdmissiblePivot d X Y v)
    (G : Realization d) : ∃ C : Finset V, IsSplitAt G.graph C := by
  have hfail' : ∀ v : V, v ∈ edgeSupport (X.edgeFinset ∆ Y.edgeFinset) →
      ¬ HasNonBipartiteFibre d v := by
    intro v hv hnb
    apply hfail v
    refine ⟨?_, hnb⟩
    intro heq
    rw [edgeSupport_symmDiff_eq_support] at hv
    have hvSupp : v ∈ (edgeDifferenceGraph X Y).support := Set.mem_toFinset.mp hv
    rcases hvSupp with ⟨w, hvw⟩
    change (edgeDifferenceGraph X Y).Adj v w at hvw
    have hmem : w ∈ X.neighborFinset v ∆ Y.neighborFinset v := by
      rw [← edgeDifferenceGraph_neighborFinset]
      simpa only [SimpleGraph.mem_neighborFinset] using hvw
    rw [heq] at hmem
    simpa using hmem
  have hnrich := no_rich_triangle_of_failure hd hXY hfail'
  have hmatch : ∀ a b c e, FourDistinct a b c e → ¬ InducesMatching G.graph a b c e :=
    fun _ _ _ _ hdist => no_induced_matching_of_no_rich hnrich G hdist
  have hfour : ∀ a b c e, FourDistinct a b c e → ¬ InducesFourCycle G.graph a b c e :=
    fun _ _ _ _ hdist => no_induced_fourCycle_of_no_rich hnrich G hdist
  rcases split_or_induced_fiveCycle G.graph hmatch hfour with hsplit | hfive
  · exact hsplit
  · obtain ⟨a, b, c, e, f, hcycle⟩ := hfive
    rcases fiveCycle_decomposable_or_univ G hmatch hfour hcycle with hdec | huniv
    · exact False.elim (hd.indecomposable hdec)
    · exact False.elim (hd.nonbipartite
        (fiveCycle_realizationGraph_colorable G huniv hcycle))

private theorem splitAt_degree_equality {d : V → ℕ} (G : Realization d) (C : Finset V)
    (hsplit : IsSplitAt G.graph C) :
    ∑ u ∈ C, d u = C.card * (C.card - 1) + ∑ u ∈ Cᶜ, min (d u) C.card := by
  classical
  have hparts (u : V) :
      G.graph.degree u = (G.neighborFinset u ∩ C).card +
        (G.neighborFinset u ∩ Cᶜ).card := by
    rw [← G.graph.card_neighborFinset_eq_degree]
    have hC : (G.neighborFinset u).filter (fun x => x ∈ C) =
        G.neighborFinset u ∩ C := Finset.filter_mem_eq_inter
    have hCc : (G.neighborFinset u).filter (fun x => x ∉ C) =
        G.neighborFinset u ∩ Cᶜ := by
      ext x
      simp
    rw [← hC, ← hCc]
    exact (Finset.card_filter_add_card_filter_not (s := G.neighborFinset u)
      (fun x => x ∈ C)).symm
  have hinter (u : V) (hu : u ∈ C) :
      (G.neighborFinset u ∩ C).card = C.card - 1 := by
    have heq : G.neighborFinset u ∩ C = C.erase u := by
      ext x
      simp only [Finset.mem_inter, Realization.mem_neighborFinset, Finset.mem_erase]
      constructor
      · intro hx
        exact ⟨hx.1.ne.symm, hx.2⟩
      · intro hx
        exact ⟨hsplit.1 hu hx.2 hx.1.symm, hx.2⟩
    rw [heq, Finset.card_erase_of_mem hu]
  have houtside (u : V) (hu : u ∈ Cᶜ) :
      (G.neighborFinset u ∩ C).card = G.graph.degree u := by
    have heq : G.neighborFinset u ∩ C = G.neighborFinset u := by
      apply Finset.Subset.antisymm Finset.inter_subset_left
      intro x hx
      refine Finset.mem_inter.mpr ⟨hx, ?_⟩
      by_contra hxC
      exact hsplit.2 u (Finset.mem_compl.mp hu) x hxC ((G.mem_neighborFinset u x).mp hx)
    rw [heq]
    simp [Realization.neighborFinset, SimpleGraph.card_neighborFinset_eq_degree]
  have hout_le (u : V) (hu : u ∈ Cᶜ) : d u ≤ C.card := by
    rw [← G.degree_eq u, ← houtside u hu]
    exact Finset.card_le_card Finset.inter_subset_right
  have hcross : (∑ u ∈ C, (G.neighborFinset u ∩ Cᶜ).card) =
      ∑ u ∈ Cᶜ, (G.neighborFinset u ∩ C).card := by
    calc
      (∑ u ∈ C, (G.neighborFinset u ∩ Cᶜ).card) =
          ∑ u ∈ C, ∑ v ∈ Cᶜ, if G.graph.Adj u v then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
            congr 1
            ext v
            simp [Realization.mem_neighborFinset, and_comm]
      _ = ∑ v ∈ Cᶜ, ∑ u ∈ C, if G.graph.Adj u v then 1 else 0 := Finset.sum_comm
      _ = ∑ v ∈ Cᶜ, ∑ u ∈ C, if G.graph.Adj v u then 1 else 0 := by
            simp only [SimpleGraph.adj_comm]
      _ = ∑ v ∈ Cᶜ, (G.neighborFinset v ∩ C).card := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
            congr 1
            ext u
            simp [Realization.mem_neighborFinset, and_comm]
  calc
    ∑ u ∈ C, d u = ∑ u ∈ C,
        ((G.neighborFinset u ∩ C).card + (G.neighborFinset u ∩ Cᶜ).card) := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [← G.degree_eq u, hparts u]
    _ = (∑ u ∈ C, (G.neighborFinset u ∩ C).card) +
        ∑ u ∈ C, (G.neighborFinset u ∩ Cᶜ).card := by
          rw [Finset.sum_add_distrib]
    _ = C.card * (C.card - 1) + ∑ u ∈ Cᶜ, G.graph.degree u := by
          rw [hcross]
          congr 1
          · calc
              ∑ u ∈ C, (G.neighborFinset u ∩ C).card =
                  ∑ _u ∈ C, (C.card - 1) := Finset.sum_congr rfl hinter
              _ = C.card * (C.card - 1) := by simp
          · exact Finset.sum_congr rfl houtside
    _ = C.card * (C.card - 1) + ∑ u ∈ Cᶜ, min (d u) C.card := by
          congr 1
          apply Finset.sum_congr rfl
          intro u hu
          rw [G.degree_eq u, min_eq_left (hout_le u hu)]

private theorem splitAt_all_realizations {d : V → ℕ} (G : Realization d) (C : Finset V)
    (hsplit : IsSplitAt G.graph C) (H : Realization d) : IsSplitAt H.graph C := by
  classical
  have heq := splitAt_degree_equality G C hsplit
  have heqH :
      ∑ u ∈ C, H.graph.degree u = C.card * (C.card - 1) +
        ∑ u ∈ Cᶜ, min (H.graph.degree u) C.card := by
    simpa only [H.degree_eq] using heq
  obtain ⟨hclique, hsat⟩ := isClique_of_sum_degree_eq H.graph heqH
  refine ⟨hclique, ?_⟩
  intro u hu v hv huv
  have hdu : d u ≤ C.card := by
    have hsub : G.neighborFinset u ⊆ C := by
      intro x hx
      by_contra hxC
      exact hsplit.2 u hu x hxC ((G.mem_neighborFinset u x).mp hx)
    rw [← G.degree_eq u, ← G.graph.card_neighborFinset_eq_degree]
    exact (Finset.card_le_card hsub)
  have hcard : (H.neighborFinset u ∩ C).card = (H.neighborFinset u).card := by
    change (H.graph.neighborFinset u ∩ C).card = (H.graph.neighborFinset u).card
    rw [hsat u (Finset.mem_compl.mpr hu), min_eq_left]
    · rw [H.graph.card_neighborFinset_eq_degree]
    · simpa only [H.degree_eq] using hdu
  have hinter : H.neighborFinset u ∩ C = H.neighborFinset u := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
    rw [hcard]
  have hvN : v ∈ H.neighborFinset u := (H.mem_neighborFinset u v).mpr huv
  have : v ∈ C := (Finset.mem_inter.mp (hinter.symm ▸ hvN)).2
  exact hv this

/-! ## 4b. The clique--independent incidence model of a split realization -/

/-- The graph encoded by a clique--independent incidence matrix, before the two sides are
relabelled onto the ground type. -/
private def splitIncidenceGraph {m n : ℕ} (M : ZeroOneMat m n) :
    SimpleGraph (Fin m ⊕ Fin n) where
  Adj x y := match x, y with
    | Sum.inl i, Sum.inl k => i ≠ k
    | Sum.inl i, Sum.inr j => M i j = true
    | Sum.inr j, Sum.inl i => M i j = true
    | Sum.inr _, Sum.inr _ => False
  symm := by
    constructor
    intro x y
    cases x <;> cases y <;> simp [ne_comm]
  loopless := by
    constructor
    intro x
    cases x <;> simp

private instance splitIncidenceGraphAdjDecidable {m n : ℕ} (M : ZeroOneMat m n) :
    DecidableRel (splitIncidenceGraph M).Adj := by
  intro x y
  cases x <;> cases y <;> simp [splitIncidenceGraph] <;> infer_instance

private theorem card_filter_bool_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Bool) :
    (Finset.univ.filter fun x => f x = true).card = ∑ x, if f x then 1 else 0 := by
  rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]

private theorem splitIncidenceGraph_degree_left {m n : ℕ} (M : ZeroOneMat m n)
    (i : Fin m) :
    (splitIncidenceGraph M).degree (Sum.inl i) = (m - 1) + rowSum M i := by
  rw [← (splitIncidenceGraph M).card_neighborFinset_eq_degree]
  have hn : (splitIncidenceGraph M).neighborFinset (Sum.inl i) =
      ((Finset.univ.erase i).map Function.Embedding.inl) ∪
        ((Finset.univ.filter fun j => M i j = true).map Function.Embedding.inr) := by
    ext x
    cases x with
    | inl k => simp [splitIncidenceGraph, ne_comm]
    | inr j => simp [splitIncidenceGraph]
  rw [hn, Finset.card_union_of_disjoint]
  · rw [Finset.card_map, Finset.card_map,
      Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [card_filter_bool_eq_sum]
    rfl
  · exact Finset.disjoint_left.mpr (by simp)

private theorem splitIncidenceGraph_degree_right {m n : ℕ} (M : ZeroOneMat m n)
    (j : Fin n) :
    (splitIncidenceGraph M).degree (Sum.inr j) = colSum M j := by
  rw [← (splitIncidenceGraph M).card_neighborFinset_eq_degree]
  have hn : (splitIncidenceGraph M).neighborFinset (Sum.inr j) =
      (Finset.univ.filter fun i => M i j = true).map Function.Embedding.inl := by
    ext x
    cases x with
    | inl i => simp [splitIncidenceGraph]
    | inr l => simp [splitIncidenceGraph]
  rw [hn, Finset.card_map, card_filter_bool_eq_sum]
  rfl

/-- The cells on which two Boolean matrices differ. -/
private def splitDiffCells {m n : ℕ} (M N : ZeroOneMat m n) :
    Finset (Fin m × Fin n) :=
  Finset.univ.filter fun p => M p.1 p.2 ≠ N p.1 p.2

/-- If one Boolean function has an extra `1` at a named coordinate but the two functions have
equal sums, it has a compensating `0`--`1` discrepancy somewhere else. -/
private theorem exists_bool_compensation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → Bool)
    (hsum : (∑ x, if f x = true then 1 else 0) =
      ∑ x, if g x = true then 1 else 0)
    (x : ι) (hfx : f x = true) (hgx : g x = false) :
    ∃ y, f y = false ∧ g y = true := by
  by_contra h
  push Not at h
  have hle (y : ι) :
      (if g y = true then 1 else 0) ≤ (if f y = true then 1 else 0) := by
    cases hf : f y <;> cases hg : g y <;> simp
    exact h y hf hg
  have hrest :
      (∑ y ∈ Finset.univ.erase x, if g y = true then 1 else 0) ≤
        ∑ y ∈ Finset.univ.erase x, if f y = true then 1 else 0 :=
    Finset.sum_le_sum fun y _ => hle y
  have hfdecomp := Finset.sum_erase_add (s := Finset.univ)
    (f := fun y => if f y = true then 1 else 0) (Finset.mem_univ x)
  have hgdecomp := Finset.sum_erase_add (s := Finset.univ)
    (f := fun y => if g y = true then 1 else 0) (Finset.mem_univ x)
  have hfdecomp' :
      (∑ y ∈ Finset.univ.erase x, if f y = true then 1 else 0) + 1 =
        ∑ y, if f y = true then 1 else 0 := by
    simpa only [hfx, eq_self, if_true] using hfdecomp
  have hgdecomp' :
      (∑ y ∈ Finset.univ.erase x, if g y = true then 1 else 0) + 0 =
        ∑ y, if g y = true then 1 else 0 := by
    simpa only [hgx, Bool.false_eq_true, if_false] using hgdecomp
  omega

/-- Four differing cells between equal-margin Boolean matrices are necessarily the four cells of
one interchange.  This is the matrix form of the alternating-four-cycle argument. -/
private theorem interchange_of_splitDiffCells_card_four {m n : ℕ}
    {M N : ZeroOneMat m n}
    (hrow : ∀ i, rowSum M i = rowSum N i)
    (hcol : ∀ j, colSum M j = colSum N j)
    (hcard : (splitDiffCells M N).card = 4) :
    Interchange M N := by
  classical
  have hDnonempty : (splitDiffCells M N).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p, hpD⟩ := hDnonempty
  have hpne : M p.1 p.2 ≠ N p.1 p.2 := by
    simpa [splitDiffCells] using hpD
  obtain ⟨i, j, hMij, hNij⟩ :
      ∃ i j, M i j = true ∧ N i j = false := by
    cases hM : M p.1 p.2 <;> cases hN : N p.1 p.2
    · exact False.elim (hpne (by simp [hM, hN]))
    · obtain ⟨j', hNj', hMj'⟩ := exists_bool_compensation (N p.1) (M p.1)
          (by simpa [rowSum] using (hrow p.1).symm) p.2 hN hM
      exact ⟨p.1, j', hMj', hNj'⟩
    · exact ⟨p.1, p.2, hM, hN⟩
    · exact False.elim (hpne (by simp [hM, hN]))
  obtain ⟨j', hMij', hNij'⟩ := exists_bool_compensation (M i) (N i)
    (by simpa [rowSum] using hrow i) j hMij hNij
  obtain ⟨i', hMi'j, hNi'j⟩ :=
    exists_bool_compensation (fun a => M a j) (fun a => N a j)
      (by simpa [colSum] using hcol j) i hMij hNij
  obtain ⟨k, hNkj', hMkj'⟩ :=
    exists_bool_compensation (fun a => N a j') (fun a => M a j')
      (by simpa [colSum] using (hcol j').symm) i hNij' hMij'
  obtain ⟨l, hNi'l, hMi'l⟩ := exists_bool_compensation (N i') (M i')
    (by simpa [rowSum] using (hrow i').symm) j hNi'j hMi'j
  have hjj' : j ≠ j' := by
    rintro rfl
    simp_all
  have hii' : i ≠ i' := by
    rintro rfl
    simp_all
  have hik : i ≠ k := by
    rintro rfl
    simp_all
  have hjl : j ≠ l := by
    rintro rfl
    simp_all
  let P : Fin m × Fin n := (i, j)
  let Q : Fin m × Fin n := (i, j')
  let R : Fin m × Fin n := (i', j)
  let T : Fin m × Fin n := (k, j')
  let U : Fin m × Fin n := (i', l)
  let B : Finset (Fin m × Fin n) := {P, Q, R}
  have hPD : P ∈ splitDiffCells M N := by
    simp [P, splitDiffCells, hMij, hNij]
  have hQD : Q ∈ splitDiffCells M N := by
    simp [Q, splitDiffCells, hMij', hNij']
  have hRD : R ∈ splitDiffCells M N := by
    simp [R, splitDiffCells, hMi'j, hNi'j]
  have hTD : T ∈ splitDiffCells M N := by
    simp [T, splitDiffCells, hMkj', hNkj']
  have hUD : U ∈ splitDiffCells M N := by
    simp [U, splitDiffCells, hMi'l, hNi'l]
  have hBcard : B.card = 3 := by
    simp [B, P, Q, R, hii', hjj']
  have hBsub : B ⊆ splitDiffCells M N := by
    intro x hx
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hPD
    · exact hQD
    · exact hRD
  have hTnotB : T ∉ B := by
    intro ht
    simp only [T, B, P, Q, R, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at ht
    rcases ht with ht | ht | ht
    · exact hik ht.1.symm
    · exact hik ht.1.symm
    · exact hjj' ht.2.symm
  have hUnotB : U ∉ B := by
    intro hu
    simp only [U, B, P, Q, R, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at hu
    rcases hu with hu | hu | hu
    · exact hii' hu.1.symm
    · exact hii' hu.1.symm
    · exact hjl hu.2.symm
  have hrestCard : ((splitDiffCells M N) \ B).card = 1 := by
    rw [Finset.card_sdiff_of_subset hBsub, hcard, hBcard]
  have hTU : T = U := by
    have hTmem : T ∈ splitDiffCells M N \ B :=
      Finset.mem_sdiff.mpr ⟨hTD, hTnotB⟩
    have hUmem : U ∈ splitDiffCells M N \ B :=
      Finset.mem_sdiff.mpr ⟨hUD, hUnotB⟩
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hrestCard
    have hTz : T = z := by simpa [hz] using hTmem
    have hUz : U = z := by simpa [hz] using hUmem
    exact hTz.trans hUz.symm
  have hki' : k = i' := congrArg Prod.fst hTU
  have hj'l : j' = l := congrArg Prod.snd hTU
  subst k
  subst l
  let W : Finset (Fin m × Fin n) := {P, Q, R, T}
  have hWsub : W ⊆ splitDiffCells M N := by
    intro x hx
    simp only [W, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hPD
    · exact hQD
    · exact hRD
    · exact hTD
  have hWcard : W.card = 4 := by
    simp [W, P, Q, R, T, hii', hjj']
  have hWD : W = splitDiffCells M N :=
    Finset.eq_of_subset_of_card_le hWsub (by rw [hcard, hWcard])
  refine ⟨i, i', j, j', hii', hjj', hMij, ?_, hMij', hMi'j,
    hNij, ?_, hNij', hNi'j, ?_⟩
  · exact hMkj'
  · exact hNkj'
  · intro a b hab
    have hout : (a, b) ∉ W := by
      simp only [W, P, Q, R, T, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq]
      push Not
      tauto
    have hsame : M a b = N a b := by
      have : (a, b) ∉ splitDiffCells M N := by rwa [← hWD]
      simpa [splitDiffCells] using this
    exact hsame.symm

/-- Relabelling cells as cross edges preserves the number of discrepancies.  The clique and
independent edges occur in both encoded graphs and hence cancel from the symmetric difference. -/
private theorem splitIncidenceGraph_edgeDiff_card {m n : ℕ}
    (e : (Fin m ⊕ Fin n) ≃ V) (M N : ZeroOneMat m n) :
    (((splitIncidenceGraph M).comap e.symm).edgeFinset ∆
      ((splitIncidenceGraph N).comap e.symm).edgeFinset).card =
        (splitDiffCells M N).card := by
  classical
  symm
  apply Finset.card_bij
    (fun p _ => s(e (Sum.inl p.1), e (Sum.inr p.2)))
  · intro p hp
    have hne : M p.1 p.2 ≠ N p.1 p.2 := by
      simpa [splitDiffCells] using hp
    simp only [Finset.mem_symmDiff, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet, SimpleGraph.comap_adj]
    simp only [e.symm_apply_apply, splitIncidenceGraph]
    cases hM : M p.1 p.2 <;> cases hN : N p.1 p.2 <;> simp_all
  · intro p _ q _ hpq
    have hs := Sym2.eq_iff.mp hpq
    rcases hs with hs | hs
    · exact Prod.ext
        (Sum.inl_injective (e.injective hs.1))
        (Sum.inr_injective (e.injective hs.2))
    · have bad : Sum.inl p.1 = Sum.inr q.2 := e.injective hs.1
      contradiction
  · intro z hz
    induction z using Sym2.inductionOn with
    | _ x y =>
      rw [← e.apply_symm_apply x, ← e.apply_symm_apply y] at hz ⊢
      cases hx : e.symm x with
      | inl i =>
        cases hy : e.symm y with
        | inl k =>
          simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
            Finset.mem_symmDiff, SimpleGraph.comap_adj, e.symm_apply_apply,
            hx, hy, splitIncidenceGraph] at hz
          tauto
        | inr j =>
          have hne : M i j ≠ N i j := by
            simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
              Finset.mem_symmDiff, SimpleGraph.comap_adj, e.symm_apply_apply,
              hx, hy, splitIncidenceGraph] at hz
            cases hM : M i j <;> cases hN : N i j <;> simp_all
          let p : Fin m × Fin n := (i, j)
          have hp : p ∈ splitDiffCells M N := by
            simpa [p, splitDiffCells]
          refine ⟨p, hp, ?_⟩
          simp [p]
      | inr j =>
        cases hy : e.symm y with
        | inl i =>
          have hne : M i j ≠ N i j := by
            simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
              Finset.mem_symmDiff, SimpleGraph.comap_adj, e.symm_apply_apply,
              hx, hy, splitIncidenceGraph] at hz
            cases hM : M i j <;> cases hN : N i j <;> simp_all
          let p : Fin m × Fin n := (i, j)
          have hp : p ∈ splitDiffCells M N := by
            simpa [p, splitDiffCells]
          refine ⟨p, hp, ?_⟩
          simp [p, Sym2.eq_swap]
        | inr l =>
          simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
            Finset.mem_symmDiff, SimpleGraph.comap_adj, e.symm_apply_apply,
            hx, hy, splitIncidenceGraph] at hz
          tauto

/-- A canonical indexing of a finite split partition by a sum of finite ordinals. -/
private noncomputable def splitPartitionEquiv (C : Finset V) :
    (Fin C.card ⊕ Fin Cᶜ.card) ≃ V := by
  let ec : {x // x ∈ Cᶜ} ≃ {x // x ∉ C} :=
    Equiv.subtypeEquivRight (by intro x; simp)
  exact (Equiv.sumCongr C.equivFin.symm ((Cᶜ).equivFin.symm.trans ec)).trans
    (Equiv.sumCompl fun x => x ∈ C)

private theorem splitPartitionEquiv_left_mem (C : Finset V) (i : Fin C.card) :
    splitPartitionEquiv C (Sum.inl i) ∈ C := by
  simp [splitPartitionEquiv]

private theorem splitPartitionEquiv_right_notMem (C : Finset V) (j : Fin Cᶜ.card) :
    splitPartitionEquiv C (Sum.inr j) ∉ C := by
  have hj := ((Cᶜ).equivFin.symm j).property
  change ((Cᶜ).equivFin.symm j).val ∉ C
  exact Finset.mem_compl.mp hj

/-- The incidence matrix extracted from a realization using fixed row and column labels. -/
private noncomputable def splitIncidenceMatrix {m n : ℕ}
    (e : (Fin m ⊕ Fin n) ≃ V) {d : V → ℕ} (H : Realization d) :
    ZeroOneMat m n :=
  fun i j => decide (H.graph.Adj (e (Sum.inl i)) (e (Sum.inr j)))

private theorem splitIncidenceGraph_matrix_eq {m n : ℕ}
    (e : (Fin m ⊕ Fin n) ≃ V) {d : V → ℕ} (H : Realization d)
    (hleft : ∀ i k : Fin m, i ≠ k →
      H.graph.Adj (e (Sum.inl i)) (e (Sum.inl k)))
    (hright : ∀ j l : Fin n,
      ¬ H.graph.Adj (e (Sum.inr j)) (e (Sum.inr l))) :
    (splitIncidenceGraph (splitIncidenceMatrix e H)).comap e.symm = H.graph := by
  ext x y
  rw [← e.apply_symm_apply x, ← e.apply_symm_apply y]
  cases hx : e.symm x with
  | inl i =>
      cases hy : e.symm y with
      | inl k =>
          by_cases hik : i = k
          · subst k
            simp [splitIncidenceGraph]
          · simp only [SimpleGraph.comap_adj, e.symm_apply_apply,
              splitIncidenceGraph]
            exact ⟨fun _ => hleft i k hik, fun _ => hik⟩
      | inr j => simp [splitIncidenceGraph, splitIncidenceMatrix]
  | inr j =>
      cases hy : e.symm y with
      | inl i =>
          simp [splitIncidenceGraph, splitIncidenceMatrix, SimpleGraph.adj_comm]
      | inr l =>
          simp only [SimpleGraph.comap_adj, e.symm_apply_apply,
            splitIncidenceGraph, false_iff]
          exact hright j l

private theorem splitIncidence_left_degree_lower {d : V → ℕ} (G : Realization d)
    (C : Finset V) (hsplit : IsSplitAt G.graph C)
    (i : Fin C.card) :
    C.card - 1 ≤ d (splitPartitionEquiv C (Sum.inl i)) := by
  classical
  let u := splitPartitionEquiv C (Sum.inl i)
  have hu : u ∈ C := splitPartitionEquiv_left_mem C i
  have hsub : C.erase u ⊆ G.neighborFinset u := by
    intro v hv
    obtain ⟨hvu, hvC⟩ := Finset.mem_erase.mp hv
    exact (G.mem_neighborFinset u v).mpr (hsplit.1 hu hvC hvu.symm)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hu] at hcard
  simpa [u, Realization.neighborFinset, SimpleGraph.card_neighborFinset_eq_degree,
    G.degree_eq u] using hcard

private noncomputable def splitIncidenceRealization {m n : ℕ} {d : V → ℕ}
    (e : (Fin m ⊕ Fin n) ≃ V)
    (hle : ∀ i : Fin m, m - 1 ≤ d (e (Sum.inl i)))
    (M : MarginClass (fun i => d (e (Sum.inl i)) - (m - 1))
      (fun j => d (e (Sum.inr j)))) :
    Realization d where
  graph := (splitIncidenceGraph M.val).comap e.symm
  adjDecidable := by infer_instance
  degree_eq := by
    intro v
    rw [comap_equiv_degree]
    cases h : e.symm v with
    | inl i =>
        have hev : e (Sum.inl i) = v := by
          rw [← h]
          simp
        rw [splitIncidenceGraph_degree_left, M.property.1]
        dsimp only
        rw [hev]
        have := hle i
        rw [hev] at this
        omega
    | inr j =>
        have hev : e (Sum.inr j) = v := by
          rw [← h]
          simp
        rw [splitIncidenceGraph_degree_right, M.property.2]
        exact congrArg d hev

private theorem splitIncidenceMatrix_hasMargins {m n : ℕ} {d : V → ℕ}
    (e : (Fin m ⊕ Fin n) ≃ V)
    (H : Realization d)
    (hleft : ∀ i k : Fin m, i ≠ k →
      H.graph.Adj (e (Sum.inl i)) (e (Sum.inl k)))
    (hright : ∀ j l : Fin n,
      ¬ H.graph.Adj (e (Sum.inr j)) (e (Sum.inr l))) :
    HasMargins (fun i => d (e (Sum.inl i)) - (m - 1))
      (fun j => d (e (Sum.inr j))) (splitIncidenceMatrix e H) := by
  classical
  have hgraph := splitIncidenceGraph_matrix_eq e H hleft hright
  let graphIso :
      (splitIncidenceGraph (splitIncidenceMatrix e H)).comap e.symm ≃g H.graph :=
    { toEquiv := Equiv.refl V
      map_rel_iff' := by
        intro x y
        simpa only [Equiv.refl_apply, hgraph] }
  have graphIso_apply (x : V) : graphIso x = x := by rfl
  constructor
  · intro i
    change rowSum (splitIncidenceMatrix e H) i =
      d (e (Sum.inl i)) - (m - 1)
    have hdeg :
        (splitIncidenceGraph (splitIncidenceMatrix e H)).degree (Sum.inl i) =
          H.graph.degree (e (Sum.inl i)) := by
      have hi := (graphIso.degree_eq (e (Sum.inl i))).symm
      rw [graphIso_apply] at hi
      rw [comap_equiv_degree] at hi
      have he : e.symm (e (Sum.inl i)) = Sum.inl i := e.symm_apply_apply _
      rw [he] at hi
      exact hi
    rw [splitIncidenceGraph_degree_left, H.degree_eq] at hdeg
    exact Nat.eq_sub_of_add_eq' hdeg
  · intro j
    have hdeg :
        (splitIncidenceGraph (splitIncidenceMatrix e H)).degree (Sum.inr j) =
          H.graph.degree (e (Sum.inr j)) := by
      have hj := (graphIso.degree_eq (e (Sum.inr j))).symm
      rw [graphIso_apply] at hj
      rw [comap_equiv_degree] at hj
      have he : e.symm (e (Sum.inr j)) = Sum.inr j := e.symm_apply_apply _
      rw [he] at hj
      exact hj
    rw [splitIncidenceGraph_degree_right, H.degree_eq] at hdeg
    exact hdeg

private theorem realization_eq_of_graph_eq {d : V → ℕ} {G H : Realization d}
    (h : G.graph = H.graph) : G = H := by
  cases G with
  | mk graphG decG degreeG =>
      cases H with
      | mk graphH decH degreeH =>
          dsimp at h
          subst graphH
          congr
          exact Subsingleton.elim _ _

private noncomputable def splitIncidenceEquiv {d : V → ℕ} (G : Realization d)
    (C : Finset V) (hsplit : IsSplitAt G.graph C) :
    MarginClass
        (fun i => d (splitPartitionEquiv C (Sum.inl i)) - (C.card - 1))
        (fun j => d (splitPartitionEquiv C (Sum.inr j))) ≃
      Realization d where
  toFun := splitIncidenceRealization (splitPartitionEquiv C)
    (splitIncidence_left_degree_lower G C hsplit)
  invFun H :=
    ⟨splitIncidenceMatrix (splitPartitionEquiv C) H, by
      apply splitIncidenceMatrix_hasMargins
        (splitPartitionEquiv C) H
      · intro i k hik
        have hHsplit := splitAt_all_realizations G C hsplit H
        exact hHsplit.1 (splitPartitionEquiv_left_mem C i)
          (splitPartitionEquiv_left_mem C k)
          (fun h => hik (Sum.inl_injective ((splitPartitionEquiv C).injective h)))
      · intro j l
        exact (splitAt_all_realizations G C hsplit H).2 _
          (splitPartitionEquiv_right_notMem C j) _
          (splitPartitionEquiv_right_notMem C l)⟩
  left_inv M := by
    apply Subtype.ext
    funext i j
    simp [splitIncidenceMatrix, splitIncidenceRealization, splitIncidenceGraph]
  right_inv H := by
    apply realization_eq_of_graph_eq
    dsimp only [splitIncidenceRealization]
    apply splitIncidenceGraph_matrix_eq
    · intro i k hik
      have hHsplit := splitAt_all_realizations G C hsplit H
      exact hHsplit.1 (splitPartitionEquiv_left_mem C i)
        (splitPartitionEquiv_left_mem C k)
        (fun h => hik (Sum.inl_injective ((splitPartitionEquiv C).injective h)))
    · intro j l
      exact (splitAt_all_realizations G C hsplit H).2 _
        (splitPartitionEquiv_right_notMem C j) _
        (splitPartitionEquiv_right_notMem C l)

private theorem splitDiffCells_card_four_of_interchange {m n : ℕ}
    {M N : ZeroOneMat m n} (hint : Interchange M N) :
    (splitDiffCells M N).card = 4 := by
  classical
  rcases hint with
    ⟨i, i', j, j', hii, hjj, hMij, hMi'j', hMij', hMi'j,
      hNij, hNi'j', hNij', hNi'j, hout⟩
  have hD : splitDiffCells M N =
      ({i, i'} : Finset (Fin m)) ×ˢ ({j, j'} : Finset (Fin n)) := by
    ext p
    constructor
    · intro hp
      have hne : M p.1 p.2 ≠ N p.1 p.2 := by
        simpa [splitDiffCells] using hp
      have hblock : (p.1 = i ∨ p.1 = i') ∧ (p.2 = j ∨ p.2 = j') := by
        by_contra hnot
        exact hne (hout p.1 p.2 hnot).symm
      simpa using hblock
    · intro hp
      rcases (by simpa using hp :
          (p.1 = i ∨ p.1 = i') ∧ (p.2 = j ∨ p.2 = j')) with ⟨hr, hc⟩
      rcases hr with rfl | rfl <;> rcases hc with rfl | rfl
      · simp [splitDiffCells, hMij, hNij]
      · simp [splitDiffCells, hMij', hNij']
      · simp [splitDiffCells, hMi'j, hNi'j]
      · simp [splitDiffCells, hMi'j', hNi'j']
  rw [hD, Finset.card_product, Finset.card_pair hii, Finset.card_pair hjj]

private noncomputable def splitIncidenceIso {d : V → ℕ} (G : Realization d)
    (C : Finset V) (hsplit : IsSplitAt G.graph C) :
    flipGraph
        (fun i => d (splitPartitionEquiv C (Sum.inl i)) - (C.card - 1))
        (fun j => d (splitPartitionEquiv C (Sum.inr j))) ≃g
      RealizationGraph d where
  toEquiv := splitIncidenceEquiv G C hsplit
  map_rel_iff' := by
    intro M N
    rw [flipGraph, SimpleGraph.fromRel_adj]
    change twoSwitchAdjacent
        (splitIncidenceRealization (splitPartitionEquiv C)
          (splitIncidence_left_degree_lower G C hsplit) M)
        (splitIncidenceRealization (splitPartitionEquiv C)
          (splitIncidence_left_degree_lower G C hsplit) N) ↔
      (M ≠ N ∧ (Interchange M.val N.val ∨ Interchange N.val M.val))
    change
      (((splitIncidenceGraph M.val).comap (splitPartitionEquiv C).symm).edgeFinset ∆
        ((splitIncidenceGraph N.val).comap (splitPartitionEquiv C).symm).edgeFinset).card = 4 ↔
      (M ≠ N ∧ (Interchange M.val N.val ∨ Interchange N.val M.val))
    rw [show
      (((splitIncidenceGraph M.val).comap (splitPartitionEquiv C).symm).edgeFinset ∆
        ((splitIncidenceGraph N.val).comap (splitPartitionEquiv C).symm).edgeFinset).card =
          (splitDiffCells M.val N.val).card from
        splitIncidenceGraph_edgeDiff_card (splitPartitionEquiv C) M.val N.val]
    constructor
    · intro hfour
      have hneVal : M.val ≠ N.val := by
        intro h
        rw [h] at hfour
        simp [splitDiffCells] at hfour
      have hrow : ∀ i, rowSum M.val i = rowSum N.val i := fun i =>
        (M.property.1 i).trans (N.property.1 i).symm
      have hcol : ∀ j, colSum M.val j = colSum N.val j := fun j =>
        (M.property.2 j).trans (N.property.2 j).symm
      exact ⟨fun h => hneVal (congrArg Subtype.val h),
        Or.inl (interchange_of_splitDiffCells_card_four hrow hcol hfour)⟩
    · rintro ⟨_, hint | hint⟩
      · exact splitDiffCells_card_four_of_interchange hint
      · simpa [splitDiffCells, ne_comm] using
          (splitDiffCells_card_four_of_interchange hint)

private theorem splitIncidenceIso_graph {d : V → ℕ} (G : Realization d)
    (C : Finset V) (hsplit : IsSplitAt G.graph C)
    (M : MarginClass
      (fun i => d (splitPartitionEquiv C (Sum.inl i)) - (C.card - 1))
      (fun j => d (splitPartitionEquiv C (Sum.inr j)))) :
    (splitIncidenceIso G C hsplit M).graph =
      (splitIncidenceGraph M.val).comap (splitPartitionEquiv C).symm := rfl

private theorem splitIncidenceIso_adj_iff {d : V → ℕ} (G : Realization d)
    (C : Finset V) (hsplit : IsSplitAt G.graph C)
    (M : MarginClass
      (fun i => d (splitPartitionEquiv C (Sum.inl i)) - (C.card - 1))
      (fun j => d (splitPartitionEquiv C (Sum.inr j))))
    (x y : Fin C.card ⊕ Fin Cᶜ.card) :
    (splitIncidenceIso G C hsplit M).graph.Adj
        (splitPartitionEquiv C x) (splitPartitionEquiv C y) ↔
      (splitIncidenceGraph M.val).Adj x y := by
  rw [splitIncidenceIso_graph]
  simp

/-- A split partition of one realization supplies the concrete clique--independent incidence
model.  The margins are the cross-degrees on the clique side and the full degrees on the
independent side. -/
noncomputable def splitIncidenceModelOfSplitPartition {d : V → ℕ}
    (G : Realization d) (C : Finset V)
    (hclique : G.graph.IsClique (C : Set V))
    (hindependent : ∀ a, a ∉ C → ∀ b, b ∉ C → ¬ G.graph.Adj a b) :
    Σ r : Fin C.card → ℕ, Σ s : Fin Cᶜ.card → ℕ,
      SplitIncidenceModel d r s := by
  classical
  let hsplit : IsSplitAt G.graph C := ⟨hclique, hindependent⟩
  exact ⟨
    (fun i => d (splitPartitionEquiv C (Sum.inl i)) - (C.card - 1)),
    (fun j => d (splitPartitionEquiv C (Sum.inr j))), {
    vertexEquiv := splitPartitionEquiv C
    realizationIso := splitIncidenceIso G C hsplit
    left_clique := by
      intro M i k hik
      exact (splitIncidenceIso_adj_iff G C hsplit M _ _).2 hik
    right_independent := by
      intro M j l
      rw [splitIncidenceIso_adj_iff]
      simp [splitIncidenceGraph]
    cross_adj_iff := by
      intro M i j
      rw [splitIncidenceIso_adj_iff]
      rfl }⟩

theorem splitIncidenceModel_exists_of_splitPartition {d : V → ℕ}
    (G : Realization d) (C : Finset V)
    (hclique : G.graph.IsClique (C : Set V))
    (hindependent : ∀ a, a ∉ C → ∀ b, b ∉ C → ¬ G.graph.Adj a b) :
    ∃ r : Fin C.card → ℕ, ∃ s : Fin Cᶜ.card → ℕ,
      Nonempty (SplitIncidenceModel d r s) := by
  let packed := splitIncidenceModelOfSplitPartition G C hclique hindependent
  exact ⟨packed.1, packed.2.1, ⟨packed.2.2⟩⟩

/-- Under the failed-pivot hypotheses used by Section 6.4, the split partition theorem and the
incidence construction together produce actual margins and a `SplitIncidenceModel`. -/
theorem splitIncidenceModel_exists_of_failure {d : V → ℕ} (hd : MainLine d)
    {X Y : Realization d} (hXY : X ≠ Y) (hfail : ∀ v, ¬ AdmissiblePivot d X Y v)
    (G : Realization d) :
    ∃ m n, ∃ r : Fin m → ℕ, ∃ s : Fin n → ℕ,
      Nonempty (SplitIncidenceModel d r s) := by
  obtain ⟨C, hsplit⟩ := realization_split_of_failure hd hXY hfail G
  obtain ⟨r, s, model⟩ :=
    splitIncidenceModel_exists_of_splitPartition G C hsplit.1 hsplit.2
  exact ⟨C.card, Cᶜ.card, r, s, model⟩

/-! ## 4c. Assembly of the separator buffer -/

private theorem separator_rowSum_le_cols {m n : ℕ} (M : ZeroOneMat m n) (i : Fin m) :
    rowSum M i ≤ n := by
  calc
    rowSum M i = ∑ j : Fin n, (if M i j then 1 else 0 : ℕ) := rfl
    _ ≤ ∑ _j : Fin n, (1 : ℕ) := by
      exact Finset.sum_le_sum (fun j _ => by split <;> omega)
    _ = n := by simp

private theorem separator_colSum_le_rows {m n : ℕ} (M : ZeroOneMat m n) (j : Fin n) :
    colSum M j ≤ m := by
  calc
    colSum M j = ∑ i : Fin m, (if M i j then 1 else 0 : ℕ) := rfl
    _ ≤ ∑ _i : Fin m, (1 : ℕ) := by
      exact Finset.sum_le_sum (fun i _ => by split <;> omega)
    _ = m := by simp

private theorem separator_row_eq_of_sum_zero {m n : ℕ} (M N : ZeroOneMat m n) (i : Fin m)
    (hM : rowSum M i = 0) (hN : rowSum N i = 0) :
    (fun j => M i j) = fun j => N i j := by
  funext j
  have hMj := (Finset.sum_eq_zero_iff.mp hM) j (Finset.mem_univ j)
  have hNj := (Finset.sum_eq_zero_iff.mp hN) j (Finset.mem_univ j)
  simp only [ite_eq_right_iff] at hMj hNj
  cases hMij : M i j <;> cases hNij : N i j <;> simp_all

private theorem separator_row_eq_of_sum_full {m n : ℕ} (M N : ZeroOneMat m n) (i : Fin m)
    (hM : rowSum M i = n) (hN : rowSum N i = n) :
    (fun j => M i j) = fun j => N i j := by
  funext j
  by_contra hne
  have hMle := separator_rowSum_le_cols M i
  have hNle := separator_rowSum_le_cols N i
  have hMij : M i j = false ∨ N i j = false := by
    cases hMi : M i j <;> cases hNi : N i j <;> simp_all
  rcases hMij with hfalse | hfalse
  · have hlt : rowSum M i < n := by
      calc
        rowSum M i = ∑ x : Fin n, (if M i x then 1 else 0 : ℕ) := rfl
        _ < ∑ _x : Fin n, (1 : ℕ) := by
          apply Finset.sum_lt_sum
          · exact fun x _ => by split <;> omega
          · exact ⟨j, Finset.mem_univ j, by simp [hfalse]⟩
        _ = n := by simp
    omega
  · have hlt : rowSum N i < n := by
      calc
        rowSum N i = ∑ x : Fin n, (if N i x then 1 else 0 : ℕ) := rfl
        _ < ∑ _x : Fin n, (1 : ℕ) := by
          apply Finset.sum_lt_sum
          · exact fun x _ => by split <;> omega
          · exact ⟨j, Finset.mem_univ j, by simp [hfalse]⟩
        _ = n := by simp
    omega

private theorem separator_col_eq_of_sum_zero {m n : ℕ} (M N : ZeroOneMat m n) (j : Fin n)
    (hM : colSum M j = 0) (hN : colSum N j = 0) :
    (fun i => M i j) = fun i => N i j := by
  funext i
  have hMi := (Finset.sum_eq_zero_iff.mp hM) i (Finset.mem_univ i)
  have hNi := (Finset.sum_eq_zero_iff.mp hN) i (Finset.mem_univ i)
  simp only [ite_eq_right_iff] at hMi hNi
  cases hMij : M i j <;> cases hNij : N i j <;> simp_all

private theorem separator_col_eq_of_sum_full {m n : ℕ} (M N : ZeroOneMat m n) (j : Fin n)
    (hM : colSum M j = m) (hN : colSum N j = m) :
    (fun i => M i j) = fun i => N i j := by
  funext i
  by_contra hne
  have hMij : M i j = false ∨ N i j = false := by
    cases hMi : M i j <;> cases hNi : N i j <;> simp_all
  rcases hMij with hfalse | hfalse
  · have hlt : colSum M j < m := by
      calc
        colSum M j = ∑ x : Fin m, (if M x j then 1 else 0 : ℕ) := rfl
        _ < ∑ _x : Fin m, (1 : ℕ) := by
          apply Finset.sum_lt_sum
          · exact fun x _ => by split <;> omega
          · exact ⟨i, Finset.mem_univ i, by simp [hfalse]⟩
        _ = m := by simp
    omega
  · have hlt : colSum N j < m := by
      calc
        colSum N j = ∑ x : Fin m, (if N x j then 1 else 0 : ℕ) := rfl
        _ < ∑ _x : Fin m, (1 : ℕ) := by
          apply Finset.sum_lt_sum
          · exact fun x _ => by split <;> omega
          · exact ⟨i, Finset.mem_univ i, by simp [hfalse]⟩
        _ = m := by simp
    omega

private theorem separator_isActive_of_model {m n : ℕ} {d : V → ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ} (hindec : ¬ TyshkevichDecomposable d)
    (hnb : ¬ (RealizationGraph d).Colorable 2)
    (model : SplitIncidenceModel d r s) : IsActive r s := by
  classical
  have hrealDiff : ∃ G H : Realization d, G ≠ H := by
    by_contra hall
    push_neg at hall
    apply hnb
    let color : Realization d → Fin 2 := fun _ => 0
    refine ⟨⟨color, ?_⟩⟩
    intro G H hGH
    exact (hGH.ne (hall G H)).elim
  obtain ⟨G, H, hGH⟩ := hrealDiff
  let M₀ := model.realizationIso.symm G
  let N₀ := model.realizationIso.symm H
  have hM₀N₀ : M₀ ≠ N₀ := by
    intro h
    apply hGH
    simpa [M₀, N₀] using congrArg model.realizationIso h
  have hcell : ∃ i : Fin m, ∃ j : Fin n, M₀.val i j ≠ N₀.val i j := by
    by_contra h
    push_neg at h
    apply hM₀N₀
    apply Subtype.ext
    funext i j
    exact h i j
  obtain ⟨i₀, j₀, _⟩ := hcell
  have hrowDiff (i : Fin m) : ∃ M N : MarginClass r s, rowPat i M ≠ rowPat i N := by
    obtain ⟨M, N, hMN⟩ :=
      cellVaries_of_tyshkevichIndecomposable model G hindec i j₀
    refine ⟨M, N, ?_⟩
    intro hpat
    exact hMN (congrFun hpat j₀)
  have hcolDiff (j : Fin n) : ∃ M N : MarginClass r s, colPat j M ≠ colPat j N := by
    obtain ⟨M, N, hMN⟩ :=
      cellVaries_of_tyshkevichIndecomposable model G hindec i₀ j
    refine ⟨M, N, ?_⟩
    intro hpat
    exact hMN (congrFun hpat i₀)
  constructor
  · intro i
    obtain ⟨M, N, hMN⟩ := hrowDiff i
    have hle : r i ≤ n := by
      rw [← M.property.1 i]
      exact separator_rowSum_le_cols M.val i
    have hne0 : r i ≠ 0 := by
      intro hr
      apply hMN
      apply separator_row_eq_of_sum_zero M.val N.val i
      · rw [M.property.1 i, hr]
      · rw [N.property.1 i, hr]
    have hnen : r i ≠ n := by
      intro hr
      apply hMN
      apply separator_row_eq_of_sum_full M.val N.val i
      · rw [M.property.1 i, hr]
      · rw [N.property.1 i, hr]
    exact ⟨Nat.pos_of_ne_zero hne0, Nat.lt_of_le_of_ne hle hnen⟩
  · intro j
    obtain ⟨M, N, hMN⟩ := hcolDiff j
    have hle : s j ≤ m := by
      rw [← M.property.2 j]
      exact separator_colSum_le_rows M.val j
    have hne0 : s j ≠ 0 := by
      intro hs
      apply hMN
      apply separator_col_eq_of_sum_zero M.val N.val j
      · rw [M.property.2 j, hs]
      · rw [N.property.2 j, hs]
    have hnem : s j ≠ m := by
      intro hs
      apply hMN
      apply separator_col_eq_of_sum_full M.val N.val j
      · rw [M.property.2 j, hs]
      · rw [N.property.2 j, hs]
    exact ⟨Nat.pos_of_ne_zero hne0, Nat.lt_of_le_of_ne hle hnem⟩

private def separator_twoRowMat {n : ℕ} (q : Fin 2) (T : Finset (Fin n)) : ZeroOneMat 2 n :=
  fun i j => if i = q then decide (j ∈ T) else decide (j ∉ T)

private theorem separator_twoRowMat_hasMargins {n : ℕ} {r : Fin 2 → ℕ} {s : Fin n → ℕ}
    (q : Fin 2) (T : Finset (Fin n)) (hT : T.card = r q)
    (hs : ∀ j, s j = 1) (hrsum : r 0 + r 1 = n) :
    HasMargins r s (separator_twoRowMat q T) := by
  constructor
  · intro i
    fin_cases q <;> fin_cases i
    · simpa [rowSum, separator_twoRowMat] using hT
    · simp only [rowSum, separator_twoRowMat, Fin.isValue, OfNat.ofNat, Fin.zero_eta,
        Fin.mk.injEq, one_ne_zero, ↓reduceIte]
      have hT0 : T.card = r 0 := by simpa using hT
      calc
        (∑ j : Fin n, if decide (j ∉ T) then 1 else 0) =
            (Finset.univ.filter fun j : Fin n => j ∉ T).card := by
          simpa using (Finset.sum_boole (R := ℕ) (fun j : Fin n => j ∉ T) Finset.univ)
        _ = n - T.card := by
          rw [show (Finset.univ.filter fun j : Fin n => j ∉ T) = Finset.univ \ T by
            ext j; simp]
          simp [Finset.card_sdiff_of_subset (Finset.subset_univ T)]
        _ = r 1 := by omega
    · simp only [rowSum, separator_twoRowMat, Fin.isValue, OfNat.ofNat, Fin.zero_eta,
        Fin.mk.injEq, zero_ne_one, ↓reduceIte]
      have hT1 : T.card = r 1 := by simpa using hT
      calc
        (∑ j : Fin n, if decide (j ∉ T) then 1 else 0) =
            (Finset.univ.filter fun j : Fin n => j ∉ T).card := by
          simpa using (Finset.sum_boole (R := ℕ) (fun j : Fin n => j ∉ T) Finset.univ)
        _ = n - T.card := by
          rw [show (Finset.univ.filter fun j : Fin n => j ∉ T) = Finset.univ \ T by
            ext j; simp]
          simp [Finset.card_sdiff_of_subset (Finset.subset_univ T)]
        _ = r 0 := by omega
    · simpa [rowSum, separator_twoRowMat] using hT
  · intro j
    rw [colSum, Fin.sum_univ_two, hs j]
    fin_cases q <;> by_cases hjT : j ∈ T <;> simp [separator_twoRowMat, hjT]

private theorem separator_twoRowMat_interchange {n : ℕ} (q : Fin 2)
    (B : Finset (Fin n)) (x y : Fin n) (hxy : x ≠ y) (hxB : x ∉ B) (hyB : y ∉ B) :
    Interchange (separator_twoRowMat q (insert x B)) (separator_twoRowMat q (insert y B)) := by
  fin_cases q
  · refine ⟨0, 1, x, y, by decide, hxy, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [separator_twoRowMat]
    · simp [separator_twoRowMat, hxy.symm, hyB]
    · simp [separator_twoRowMat, hxy.symm, hyB]
    · simp [separator_twoRowMat, hxB]
    · simp [separator_twoRowMat, hxy, hxB]
    · simp [separator_twoRowMat, hxy, hxB]
    · simp [separator_twoRowMat]
    · simp [separator_twoRowMat, hxy, hxB, hyB]
    · intro i j houtside
      have hjx : j ≠ x := by
        intro h
        apply houtside
        exact ⟨by fin_cases i <;> simp, Or.inl h⟩
      have hjy : j ≠ y := by
        intro h
        apply houtside
        exact ⟨by fin_cases i <;> simp, Or.inr h⟩
      simp [separator_twoRowMat, hjx, hjy]
  · refine ⟨1, 0, x, y, by decide, hxy, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [separator_twoRowMat]
    · simp [separator_twoRowMat, hxy.symm, hyB]
    · simp [separator_twoRowMat, hxy.symm, hyB]
    · simp [separator_twoRowMat, hxB]
    · simp [separator_twoRowMat, hxy, hxB]
    · simp [separator_twoRowMat, hxy, hxB]
    · simp [separator_twoRowMat]
    · simp [separator_twoRowMat, hxy, hxB, hyB]
    · intro i j houtside
      have hjx : j ≠ x := by
        intro h
        apply houtside
        exact ⟨by fin_cases i <;> simp, Or.inl h⟩
      have hjy : j ≠ y := by
        intro h
        apply houtside
        exact ⟨by fin_cases i <;> simp, Or.inr h⟩
      simp [separator_twoRowMat, hjx, hjy]

private theorem separator_margin_sum_eq {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    (M : MarginClass r s) : (∑ i : Fin m, r i) = ∑ j : Fin n, s j := by
  calc
    (∑ i : Fin m, r i) = ∑ i : Fin m, rowSum M.val i := by
      exact Finset.sum_congr rfl (fun i _ => (M.property.1 i).symm)
    _ = ∑ j : Fin n, colSum M.val j := by
      exact Finset.sum_comm
    _ = ∑ j : Fin n, s j := by
      exact Finset.sum_congr rfl (fun j _ => M.property.2 j)

private theorem separator_twoRow_other_eq_not {n : ℕ} {r : Fin 2 → ℕ} {s : Fin n → ℕ}
    (M : MarginClass r s) (hs : ∀ j, s j = 1) (q i : Fin 2) (hi : i ≠ q) (j : Fin n) :
    M.val i j = !M.val q j := by
  have hcol := M.property.2 j
  rw [colSum, Fin.sum_univ_two, hs j] at hcol
  fin_cases q <;> fin_cases i <;>
    simp_all only [Fin.isValue, ne_eq, not_true_eq_false, Bool.not_eq_eq_eq_not,
      Bool.not_eq_true, Bool.not_eq_false]
  all_goals
    cases h0 : M.val 0 j <;> cases h1 : M.val 1 j <;> simp_all

private theorem separator_twoRow_separating_column_triangle {n : ℕ}
    {r : Fin 2 → ℕ} {s : Fin n → ℕ} (hact : IsActive r s)
    (a b : MarginClass r s) (hab : a ≠ b) (hn : 4 ≤ n) :
    ∃ p : Fin n, colPat p a ≠ colPat p b ∧
      ∃ M0 M1 M2 : MarginClass r s,
        (flipGraph r s).Adj M0 M1 ∧ (flipGraph r s).Adj M1 M2 ∧
        (flipGraph r s).Adj M0 M2 ∧
        colPat p M0 = colPat p M1 ∧ colPat p M1 = colPat p M2 := by
  classical
  have hs : ∀ j, s j = 1 := by
    intro j
    have hj := hact.2 j
    omega
  have hrsum : r 0 + r 1 = n := by
    have hsum := separator_margin_sum_eq a
    rw [Fin.sum_univ_two] at hsum
    have hsSum : (∑ j : Fin n, s j) = n := by simp [hs]
    omega
  let q : Fin 2 := if r 0 ≤ r 1 then 0 else 1
  have hqpos : 0 < r q := (hact.1 q).1
  have hqsmall : 2 * r q ≤ n := by
    simp only [q]
    split_ifs with h
    · omega
    · omega
  let A : Finset (Fin n) := Finset.univ.filter fun j => a.val q j = true
  let B : Finset (Fin n) := Finset.univ.filter fun j => b.val q j = true
  have hAcard : A.card = r q := by
    simpa [A, rowSum] using a.property.1 q
  have hBcard : B.card = r q := by
    simpa [B, rowSum] using b.property.1 q
  have hAB : A ≠ B := by
    intro hsets
    apply hab
    apply Subtype.ext
    funext i j
    have htop : a.val q j = b.val q j := by
      apply Bool.eq_iff_iff.mpr
      simpa [A, B] using Finset.ext_iff.mp hsets j
    by_cases hi : i = q
    · simpa [hi] using htop
    · rw [separator_twoRow_other_eq_not a hs q i hi j,
        separator_twoRow_other_eq_not b hs q i hi j, htop]
  have hnotAB : ¬ A ⊆ B := by
    intro hsub
    apply hAB
    exact Finset.eq_of_subset_of_card_le hsub (by omega)
  have hnotBA : ¬ B ⊆ A := by
    intro hsub
    apply hAB
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  by_cases hqone : r q = 1
  · have hBA : (B \ A).Nonempty := Finset.sdiff_nonempty.mpr hnotBA
    obtain ⟨p, hp⟩ := hBA
    have hpB := (Finset.mem_sdiff.mp hp).1
    have hpA := (Finset.mem_sdiff.mp hp).2
    have hsep : colPat p a ≠ colPat p b := by
      intro heq
      have hp := congrFun heq q
      have hap : a.val q p = false := by
        cases h : a.val q p
        · rfl
        · exact False.elim (hpA (by simp [A, h]))
      have hbp : b.val q p = true := by
        simpa [B] using hpB
      simp [colPat, hap, hbp] at hp
    have hrestCard : (Finset.univ.erase p : Finset (Fin n)).card = n - 1 := by simp
    have hthree : 3 ≤ (Finset.univ.erase p : Finset (Fin n)).card := by omega
    obtain ⟨Z, hZsub, hZcard⟩ := Finset.exists_subset_card_eq hthree
    obtain ⟨x, y, z, hxy, hxz, hyz, hZ⟩ := Finset.card_eq_three.mp hZcard
    have hxp : x ≠ p := by
      intro h
      subst x
      exact (Finset.mem_erase.mp (hZsub (by simp [hZ]))).1 rfl
    have hyp : y ≠ p := by
      intro h
      subst y
      exact (Finset.mem_erase.mp (hZsub (by simp [hZ]))).1 rfl
    have hzp : z ≠ p := by
      intro h
      subst z
      exact (Finset.mem_erase.mp (hZsub (by simp [hZ]))).1 rfl
    let M0 : MarginClass r s := ⟨separator_twoRowMat q {x},
      separator_twoRowMat_hasMargins q {x} (by simp [hqone]) hs hrsum⟩
    let M1 : MarginClass r s := ⟨separator_twoRowMat q {y},
      separator_twoRowMat_hasMargins q {y} (by simp [hqone]) hs hrsum⟩
    let M2 : MarginClass r s := ⟨separator_twoRowMat q {z},
      separator_twoRowMat_hasMargins q {z} (by simp [hqone]) hs hrsum⟩
    have h01 : (flipGraph r s).Adj M0 M1 := by
      rw [flipGraph, SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl (separator_twoRowMat_interchange q ∅ x y hxy (by simp) (by simp))⟩
      intro heq
      have hv := congrArg (fun M : MarginClass r s => M.val q x) heq
      simp [M0, M1, separator_twoRowMat, hxy] at hv
    have h12 : (flipGraph r s).Adj M1 M2 := by
      rw [flipGraph, SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl (separator_twoRowMat_interchange q ∅ y z hyz (by simp) (by simp))⟩
      intro heq
      have hv := congrArg (fun M : MarginClass r s => M.val q y) heq
      simp [M1, M2, separator_twoRowMat, hyz] at hv
    have h02 : (flipGraph r s).Adj M0 M2 := by
      rw [flipGraph, SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl (separator_twoRowMat_interchange q ∅ x z hxz (by simp) (by simp))⟩
      intro heq
      have hv := congrArg (fun M : MarginClass r s => M.val q x) heq
      simp [M0, M2, separator_twoRowMat, hxz] at hv
    refine ⟨p, hsep, M0, M1, M2, h01, h12, h02, ?_, ?_⟩
    · funext i
      simp [colPat, M0, M1, separator_twoRowMat, hxp.symm, hyp.symm]
    · funext i
      simp [colPat, M1, M2, separator_twoRowMat, hyp.symm, hzp.symm]
  · have hABdiff : (A \ B).Nonempty := Finset.sdiff_nonempty.mpr hnotAB
    obtain ⟨p, hp⟩ := hABdiff
    have hpA := (Finset.mem_sdiff.mp hp).1
    have hpB := (Finset.mem_sdiff.mp hp).2
    have hsep : colPat p a ≠ colPat p b := by
      intro heq
      have hp := congrFun heq q
      have hap : a.val q p = true := by simpa [A] using hpA
      have hbp : b.val q p = false := by
        cases h : b.val q p
        · rfl
        · exact False.elim (hpB (by simp [B, h]))
      simp [colPat, hap, hbp] at hp
    have hKbound : r q - 2 ≤ (Finset.univ.erase p : Finset (Fin n)).card := by simp; omega
    obtain ⟨K, hKsub, hKcard⟩ := Finset.exists_subset_card_eq hKbound
    have hpK : p ∉ K := by
      intro hp
      exact (Finset.mem_erase.mp (hKsub hp)).1 rfl
    let Base : Finset (Fin n) := insert p K
    have hBaseCard : Base.card = r q - 1 := by simp [Base, hpK, hKcard]; omega
    have hCandCard : ((Finset.univ.erase p) \ Base).card = n - r q + 1 := by
      have hBsub : K ⊆ Finset.univ.erase p := hKsub
      rw [show (Finset.univ.erase p) \ Base = (Finset.univ.erase p) \ K by
        ext j
        simp [Base]]
      rw [Finset.card_sdiff_of_subset hBsub]
      simp [hKcard]
      omega
    have hthree : 3 ≤ ((Finset.univ.erase p) \ Base).card := by omega
    obtain ⟨Z, hZsub, hZcard⟩ := Finset.exists_subset_card_eq hthree
    obtain ⟨x, y, z, hxy, hxz, hyz, hZ⟩ := Finset.card_eq_three.mp hZcard
    have hx : x ∈ (Finset.univ.erase p) \ Base := hZsub (by simp [hZ])
    have hy : y ∈ (Finset.univ.erase p) \ Base := hZsub (by simp [hZ])
    have hz : z ∈ (Finset.univ.erase p) \ Base := hZsub (by simp [hZ])
    have hxp : x ≠ p := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hx).1).1
    have hyp : y ≠ p := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hy).1).1
    have hzp : z ≠ p := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hz).1).1
    have hxBase : x ∉ Base := (Finset.mem_sdiff.mp hx).2
    have hyBase : y ∉ Base := (Finset.mem_sdiff.mp hy).2
    have hzBase : z ∉ Base := (Finset.mem_sdiff.mp hz).2
    have hT0 : (insert x Base).card = r q := by simp [hxBase, hBaseCard]; omega
    have hT1 : (insert y Base).card = r q := by simp [hyBase, hBaseCard]; omega
    have hT2 : (insert z Base).card = r q := by simp [hzBase, hBaseCard]; omega
    let M0 : MarginClass r s := ⟨separator_twoRowMat q (insert x Base),
      separator_twoRowMat_hasMargins q (insert x Base) hT0 hs hrsum⟩
    let M1 : MarginClass r s := ⟨separator_twoRowMat q (insert y Base),
      separator_twoRowMat_hasMargins q (insert y Base) hT1 hs hrsum⟩
    let M2 : MarginClass r s := ⟨separator_twoRowMat q (insert z Base),
      separator_twoRowMat_hasMargins q (insert z Base) hT2 hs hrsum⟩
    have h01 : (flipGraph r s).Adj M0 M1 := by
      rw [flipGraph, SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl (separator_twoRowMat_interchange q Base x y hxy hxBase hyBase)⟩
      intro heq
      have hv := congrArg (fun M : MarginClass r s => M.val q x) heq
      simp [M0, M1, separator_twoRowMat, hxy, hxBase] at hv
    have h12 : (flipGraph r s).Adj M1 M2 := by
      rw [flipGraph, SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl (separator_twoRowMat_interchange q Base y z hyz hyBase hzBase)⟩
      intro heq
      have hv := congrArg (fun M : MarginClass r s => M.val q y) heq
      simp [M1, M2, separator_twoRowMat, hyz, hyBase] at hv
    have h02 : (flipGraph r s).Adj M0 M2 := by
      rw [flipGraph, SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl (separator_twoRowMat_interchange q Base x z hxz hxBase hzBase)⟩
      intro heq
      have hv := congrArg (fun M : MarginClass r s => M.val q x) heq
      simp [M0, M2, separator_twoRowMat, hxz, hxBase] at hv
    refine ⟨p, hsep, M0, M1, M2, h01, h12, h02, ?_, ?_⟩
    · funext i
      have hpBase : p ∈ Base := by simp [Base]
      simp [colPat, M0, M1, separator_twoRowMat, hpBase, hxp, hyp]
    · funext i
      have hpBase : p ∈ Base := by simp [Base]
      simp [colPat, M1, M2, separator_twoRowMat, hpBase, hyp, hzp]

private def separator_transposeMat {m n : ℕ} (M : ZeroOneMat m n) : ZeroOneMat n m :=
  fun j i => M i j

private theorem separator_transpose_hasMargins {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    (M : MarginClass r s) : HasMargins s r (separator_transposeMat M.val) := by
  exact ⟨M.property.2, M.property.1⟩

private def separator_transposeEquiv {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ) :
    MarginClass r s ≃ MarginClass s r where
  toFun M := ⟨separator_transposeMat M.val, separator_transpose_hasMargins M⟩
  invFun M := ⟨separator_transposeMat M.val, separator_transpose_hasMargins M⟩
  left_inv M := by rfl
  right_inv M := by rfl

private theorem separator_interchange_transpose_iff {m n : ℕ} {M N : ZeroOneMat m n} :
    Interchange (separator_transposeMat M) (separator_transposeMat N) ↔ Interchange M N := by
  constructor
  · rintro ⟨c₁, c₂, r₁, r₂, hcne, hrne, hM₁₁, hM₂₂, hM₁₂, hM₂₁,
        hN₁₁, hN₂₂, hN₁₂, hN₂₁, hout⟩
    refine ⟨r₁, r₂, c₁, c₂, hrne, hcne, hM₁₁, hM₂₂, hM₂₁, hM₁₂,
      hN₁₁, hN₂₂, hN₂₁, hN₁₂, ?_⟩
    intro i j hnot
    exact hout j i (fun hblock => hnot ⟨hblock.2, hblock.1⟩)
  · rintro ⟨r₁, r₂, c₁, c₂, hrne, hcne, hM₁₁, hM₂₂, hM₁₂, hM₂₁,
        hN₁₁, hN₂₂, hN₁₂, hN₂₁, hout⟩
    refine ⟨c₁, c₂, r₁, r₂, hcne, hrne, hM₁₁, hM₂₂, hM₂₁, hM₁₂,
      hN₁₁, hN₂₂, hN₂₁, hN₁₂, ?_⟩
    intro j i hnot
    exact hout i j (fun hblock => hnot ⟨hblock.2, hblock.1⟩)

private theorem separator_transposeEquiv_interchange_iff {m n : ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ} (M N : MarginClass r s) :
    Interchange ((separator_transposeEquiv r s M).val) ((separator_transposeEquiv r s N).val) ↔
      Interchange M.val N.val := by
  exact separator_interchange_transpose_iff

private def separator_transposeIso {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ) :
    flipGraph r s ≃g flipGraph s r where
  toEquiv := separator_transposeEquiv r s
  map_rel_iff' := by
    intro M N
    let e := separator_transposeEquiv r s
    rw [flipGraph, flipGraph, SimpleGraph.fromRel_adj, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨hne, hrel | hrel⟩
      · refine ⟨?_, Or.inl ?_⟩
        · intro hMN
          exact hne (congrArg e hMN)
        · simpa only [e] using (separator_transposeEquiv_interchange_iff M N).mp hrel
      · refine ⟨?_, Or.inr ?_⟩
        · intro hMN
          exact hne (congrArg e hMN)
        · simpa only [e] using (separator_transposeEquiv_interchange_iff N M).mp hrel
    · rintro ⟨hne, hrel | hrel⟩
      · refine ⟨?_, Or.inl ?_⟩
        · intro heq
          exact hne (e.injective heq)
        · simpa only [e] using (separator_transposeEquiv_interchange_iff M N).mpr hrel
      · refine ⟨?_, Or.inr ?_⟩
        · intro heq
          exact hne (e.injective heq)
        · simpa only [e] using (separator_transposeEquiv_interchange_iff N M).mpr hrel

private theorem separator_twoCol_separating_row_triangle {m : ℕ}
    {r : Fin m → ℕ} {s : Fin 2 → ℕ} (hact : IsActive r s)
    (a b : MarginClass r s) (hab : a ≠ b) (hm : 4 ≤ m) :
    ∃ p : Fin m, rowPat p a ≠ rowPat p b ∧
      ∃ M0 M1 M2 : MarginClass r s,
        (flipGraph r s).Adj M0 M1 ∧ (flipGraph r s).Adj M1 M2 ∧
        (flipGraph r s).Adj M0 M2 ∧
        rowPat p M0 = rowPat p M1 ∧ rowPat p M1 = rowPat p M2 := by
  let e := separator_transposeIso r s
  have habT : e a ≠ e b := e.injective.ne hab
  obtain ⟨p, hsep, T0, T1, T2, h01, h12, h02, hp01, hp12⟩ :=
    separator_twoRow_separating_column_triangle ⟨hact.2, hact.1⟩ (e a) (e b) habT hm
  let M0 : MarginClass r s := e.symm T0
  let M1 : MarginClass r s := e.symm T1
  let M2 : MarginClass r s := e.symm T2
  refine ⟨p, ?_, M0, M1, M2, ?_, ?_, ?_, ?_, ?_⟩
  · intro hrow
    apply hsep
    funext i
    simpa [e, separator_transposeIso, separator_transposeEquiv, separator_transposeMat, rowPat, colPat]
      using congrFun hrow i
  · exact e.symm.map_rel_iff.mpr h01
  · exact e.symm.map_rel_iff.mpr h12
  · exact e.symm.map_rel_iff.mpr h02
  · change colPat p T0 = colPat p T1
    exact hp01
  · change colPat p T1 = colPat p T2
    exact hp12

private theorem separator_twoCol_other_eq_not {m : ℕ} {r : Fin m → ℕ} {s : Fin 2 → ℕ}
    (M : MarginClass r s) (hr : ∀ i, r i = 1) (p j : Fin 2) (hj : j ≠ p) (i : Fin m) :
    M.val i j = !M.val i p := by
  have hrow := M.property.1 i
  rw [rowSum, Fin.sum_univ_two, hr i] at hrow
  fin_cases p <;> fin_cases j <;> simp_all only [Fin.isValue, ne_eq, not_true_eq_false]
  all_goals
    cases h0 : M.val i 0 <;> cases h1 : M.val i 1 <;> simp_all

private theorem separator_two_by_two_colorable {r s : Fin 2 → ℕ} (hact : IsActive r s) :
    ∃ col : MarginClass r s → Bool, IsProper2Coloring (flipGraph r s) col := by
  have hr : ∀ i, r i = 1 := by intro i; have := hact.1 i; omega
  have hs : ∀ j, s j = 1 := by intro j; have := hact.2 j; omega
  have hentry_injective : Function.Injective (fun M : MarginClass r s => M.val 0 0) := by
    intro M N h00
    have htop (j : Fin 2) : M.val 0 j = N.val 0 j := by
      by_cases hj : j = 0
      · simpa [hj] using h00
      · have hj1 : j = 1 := by
          apply Fin.ext
          omega
        subst j
        rw [separator_twoCol_other_eq_not M hr 0 1 (by decide) 0,
          separator_twoCol_other_eq_not N hr 0 1 (by decide) 0]
        exact congrArg (fun x : Bool => !x) h00
    apply Subtype.ext
    funext i j
    by_cases hi : i = 0
    · simpa [hi] using htop j
    · rw [separator_twoRow_other_eq_not M hs 0 i hi j,
        separator_twoRow_other_eq_not N hs 0 i hi j, htop j]
  refine ⟨fun M => M.val 0 0, ?_⟩
  intro M N hMN heq
  exact hMN.ne (hentry_injective heq)

private theorem separator_twoRow_threeCol_violates_notK3 {d : V → ℕ}
    {r : Fin 2 → ℕ} {s : Fin 3 → ℕ} (hd : MainLine d)
    (model : SplitIncidenceModel d r s) (hact : IsActive r s)
    (hnb : ¬ ∃ col : MarginClass r s → Bool, IsProper2Coloring (flipGraph r s) col)
    (G : Realization d) : False := by
  classical
  have hs : ∀ j, s j = 1 := by intro j; have := hact.2 j; omega
  let top : MarginClass r s → {T : Finset (Fin 3) // T.card = r 0} := fun M =>
    ⟨Finset.univ.filter (fun j => M.val 0 j = true), by
      simpa [rowSum] using M.property.1 0⟩
  have htop_injective : Function.Injective top := by
    intro M N htop
    apply Subtype.ext
    funext i j
    have htopEntry : M.val 0 j = N.val 0 j := by
      apply Bool.eq_iff_iff.mpr
      have hsets := congrArg Subtype.val htop
      simpa [top] using Finset.ext_iff.mp hsets j
    by_cases hi : i = 0
    · simpa [hi] using htopEntry
    · rw [separator_twoRow_other_eq_not M hs 0 i hi j,
        separator_twoRow_other_eq_not N hs 0 i hi j, htopEntry]
  have hrCases : r 0 = 1 ∨ r 0 = 2 := by
    have := hact.1 (0 : Fin 2)
    omega
  have hcardLe : Fintype.card (MarginClass r s) ≤ 3 := by
    calc
      Fintype.card (MarginClass r s) ≤
          Fintype.card {T : Finset (Fin 3) // T.card = r 0} :=
        Fintype.card_le_of_injective top htop_injective
      _ = Nat.choose 3 (r 0) := Fintype.card_finset_len (r 0)
      _ = 3 := by rcases hrCases with h | h <;> simp [h]
  have hvar : ∀ i j, CellVaries r s i j :=
    cellVaries_of_tyshkevichIndecomposable model G hd.indecomposable
  obtain ⟨M0, M1, M2, h01, h12, h02⟩ :=
    nonbip_has_triangle_of_cellVaries r s hact hvar hnb
  have hM01 : M0 ≠ M1 := h01.ne
  have hM12 : M1 ≠ M2 := h12.ne
  have hM02 : M0 ≠ M2 := h02.ne
  have htripleCard : ({M0, M1, M2} : Finset (MarginClass r s)).card = 3 := by
    simp [hM01, hM02, hM12]
  have hcardGe : 3 ≤ Fintype.card (MarginClass r s) := by
    calc
      3 = ({M0, M1, M2} : Finset (MarginClass r s)).card := htripleCard.symm
      _ ≤ (Finset.univ : Finset (MarginClass r s)).card := Finset.card_le_univ _
      _ = Fintype.card (MarginClass r s) := rfl
  have hcard : Fintype.card (MarginClass r s) = 3 := by omega
  have htriple : ({M0, M1, M2} : Finset (MarginClass r s)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa [htripleCard, hcard]
  apply hd.notK3
  refine ⟨model.realizationIso M0, model.realizationIso M1, model.realizationIso M2,
    model.realizationIso.injective.ne hM01, model.realizationIso.injective.ne hM12,
    model.realizationIso.injective.ne hM02, ?_⟩
  intro H
  let M := model.realizationIso.symm H
  have hmem : M ∈ ({M0, M1, M2} : Finset (MarginClass r s)) := by
    rw [htriple]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h
  · left
    simpa [M] using congrArg model.realizationIso h
  · right; left
    simpa [M] using congrArg model.realizationIso h
  · right; right
    simpa [M] using congrArg model.realizationIso h

private theorem separator_threeRow_twoCol_violates_notK3 {d : V → ℕ}
    {r : Fin 3 → ℕ} {s : Fin 2 → ℕ} (hd : MainLine d)
    (model : SplitIncidenceModel d r s) (hact : IsActive r s)
    (hnb : ¬ ∃ col : MarginClass r s → Bool, IsProper2Coloring (flipGraph r s) col)
    (G : Realization d) : False := by
  classical
  have hr : ∀ i, r i = 1 := by intro i; have := hact.1 i; omega
  let left : MarginClass r s → {T : Finset (Fin 3) // T.card = s 0} := fun M =>
    ⟨Finset.univ.filter (fun i => M.val i 0 = true), by
      simpa [colSum] using M.property.2 0⟩
  have hleft_injective : Function.Injective left := by
    intro M N hleft
    apply Subtype.ext
    funext i j
    have hleftEntry : M.val i 0 = N.val i 0 := by
      apply Bool.eq_iff_iff.mpr
      have hsets := congrArg Subtype.val hleft
      simpa [left] using Finset.ext_iff.mp hsets i
    by_cases hj : j = 0
    · simpa [hj] using hleftEntry
    · rw [separator_twoCol_other_eq_not M hr 0 j hj i,
        separator_twoCol_other_eq_not N hr 0 j hj i, hleftEntry]
  have hsCases : s 0 = 1 ∨ s 0 = 2 := by
    have := hact.2 (0 : Fin 2)
    omega
  have hcardLe : Fintype.card (MarginClass r s) ≤ 3 := by
    calc
      Fintype.card (MarginClass r s) ≤
          Fintype.card {T : Finset (Fin 3) // T.card = s 0} :=
        Fintype.card_le_of_injective left hleft_injective
      _ = Nat.choose 3 (s 0) := Fintype.card_finset_len (s 0)
      _ = 3 := by rcases hsCases with h | h <;> simp [h]
  have hvar : ∀ i j, CellVaries r s i j :=
    cellVaries_of_tyshkevichIndecomposable model G hd.indecomposable
  obtain ⟨M0, M1, M2, h01, h12, h02⟩ :=
    nonbip_has_triangle_of_cellVaries r s hact hvar hnb
  have hM01 : M0 ≠ M1 := h01.ne
  have hM12 : M1 ≠ M2 := h12.ne
  have hM02 : M0 ≠ M2 := h02.ne
  have htripleCard : ({M0, M1, M2} : Finset (MarginClass r s)).card = 3 := by
    simp [hM01, hM02, hM12]
  have hcardGe : 3 ≤ Fintype.card (MarginClass r s) := by
    calc
      3 = ({M0, M1, M2} : Finset (MarginClass r s)).card := htripleCard.symm
      _ ≤ (Finset.univ : Finset (MarginClass r s)).card := Finset.card_le_univ _
      _ = Fintype.card (MarginClass r s) := rfl
  have hcard : Fintype.card (MarginClass r s) = 3 := by omega
  have htriple : ({M0, M1, M2} : Finset (MarginClass r s)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa [htripleCard, hcard]
  apply hd.notK3
  refine ⟨model.realizationIso M0, model.realizationIso M1, model.realizationIso M2,
    model.realizationIso.injective.ne hM01, model.realizationIso.injective.ne hM12,
    model.realizationIso.injective.ne hM02, ?_⟩
  intro H
  let M := model.realizationIso.symm H
  have hmem : M ∈ ({M0, M1, M2} : Finset (MarginClass r s)) := by
    rw [htriple]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h
  · left
    simpa [M] using congrArg model.realizationIso h
  · right; left
    simpa [M] using congrArg model.realizationIso h
  · right; right
    simpa [M] using congrArg model.realizationIso h

private theorem separator_buffer_completed {d : V → ℕ} (hd : MainLine d)
    (X Y : Realization d) (hXY : X ≠ Y) :
    ∃ v : V, AdmissiblePivot d X Y v := by
  classical
  by_contra hnone
  push_neg at hnone
  have hfail : ∀ v, ¬ AdmissiblePivot d X Y v := hnone
  obtain ⟨m, n, r, s, ⟨model⟩⟩ :=
    splitIncidenceModel_exists_of_failure hd hXY hfail X
  let a : MarginClass r s := model.realizationIso.symm X
  let b : MarginClass r s := model.realizationIso.symm Y
  have hab : a ≠ b := by
    intro heq
    apply hXY
    simpa [a, b] using congrArg model.realizationIso heq
  have hact : IsActive r s :=
    separator_isActive_of_model hd.indecomposable hd.nonbipartite model
  have hnb : ¬ ∃ col : MarginClass r s → Bool,
      IsProper2Coloring (flipGraph r s) col := by
    rintro ⟨col, hcol⟩
    apply hd.nonbipartite
    let color : Realization d → Fin 2 := fun G =>
      ⟨if col (model.realizationIso.symm G) then 1 else 0, by split <;> omega⟩
    refine ⟨⟨color, ?_⟩⟩
    intro G H hGH
    have hmat : (flipGraph r s).Adj
        (model.realizationIso.symm G) (model.realizationIso.symm H) :=
      model.realizationIso.symm.map_rel_iff.mpr hGH
    have hne := hcol _ _ hmat
    simp only [color]
    cases hG : col (model.realizationIso.symm G) <;>
      cases hH : col (model.realizationIso.symm H) <;> simp_all
  have hcell : ∃ i : Fin m, ∃ j : Fin n, a.val i j ≠ b.val i j := by
    by_contra h
    push_neg at h
    apply hab
    apply Subtype.ext
    funext i j
    exact h i j
  obtain ⟨i, j, hij⟩ := hcell
  have hm2 : 2 ≤ m := by
    have hjact := hact.2 j
    omega
  have hn2 : 2 ≤ n := by
    have hiact := hact.1 i
    omega
  by_cases hm3 : 3 ≤ m
  · by_cases hn3 : 3 ≤ n
    · obtain ⟨line, hsep, hfibre⟩ :=
        splitIncidence_buffer_of_tyshkevichIndecomposable model X hd.indecomposable
          hact hm3 hn3 hnb a b hab
      refine hfail (model.vertexEquiv line) ⟨?_, hfibre⟩
      change X.neighborFinset (model.vertexEquiv line) ≠
        Y.neighborFinset (model.vertexEquiv line)
      cases line with
      | inl i =>
          intro hneighbor
          apply hsep
          apply (model.rowPat_eq_iff_neighborFinset_eq a b i).2
          simpa [a, b] using hneighbor
      | inr j =>
          intro hneighbor
          apply hsep
          apply (model.colPat_eq_iff_neighborFinset_eq a b j).2
          simpa [a, b] using hneighbor
    · have hnEq : n = 2 := by omega
      subst n
      by_cases hm4 : 4 ≤ m
      · obtain ⟨p, hsep, M0, M1, M2, h01, h12, h02, hp01, hp12⟩ :=
          separator_twoCol_separating_row_triangle hact a b hab hm4
        have hgroundSep : X.neighborFinset (model.vertexEquiv (Sum.inl p)) ≠
            Y.neighborFinset (model.vertexEquiv (Sum.inl p)) := by
          intro hneighbor
          apply hsep
          apply (model.rowPat_eq_iff_neighborFinset_eq a b p).2
          simpa [a, b] using hneighbor
        have hfibre : HasNonBipartiteFibre d (model.vertexEquiv (Sum.inl p)) := by
          refine ⟨model.realizationIso M0, model.realizationIso M1,
            model.realizationIso M2, ?_, ?_, ?_, ?_, ?_⟩
          · exact (model.rowPat_eq_iff_neighborFinset_eq M0 M1 p).1 hp01
          · exact (model.rowPat_eq_iff_neighborFinset_eq M1 M2 p).1 hp12
          · exact model.realizationIso.map_rel_iff.mpr h01
          · exact model.realizationIso.map_rel_iff.mpr h12
          · exact model.realizationIso.map_rel_iff.mpr h02
        exact hfail _ ⟨hgroundSep, hfibre⟩
      · have hmCases : m = 2 ∨ m = 3 := by omega
        rcases hmCases with hmEq | hmEq
        · subst m
          exact hnb (separator_two_by_two_colorable hact)
        · subst m
          exact separator_threeRow_twoCol_violates_notK3 hd model hact hnb X
  · have hmEq : m = 2 := by omega
    subst m
    by_cases hn4 : 4 ≤ n
    · obtain ⟨p, hsep, M0, M1, M2, h01, h12, h02, hp01, hp12⟩ :=
        separator_twoRow_separating_column_triangle hact a b hab hn4
      have hgroundSep : X.neighborFinset (model.vertexEquiv (Sum.inr p)) ≠
          Y.neighborFinset (model.vertexEquiv (Sum.inr p)) := by
        intro hneighbor
        apply hsep
        apply (model.colPat_eq_iff_neighborFinset_eq a b p).2
        simpa [a, b] using hneighbor
      have hfibre : HasNonBipartiteFibre d (model.vertexEquiv (Sum.inr p)) := by
        refine ⟨model.realizationIso M0, model.realizationIso M1,
          model.realizationIso M2, ?_, ?_, ?_, ?_, ?_⟩
        · exact (model.colPat_eq_iff_neighborFinset_eq M0 M1 p).1 hp01
        · exact (model.colPat_eq_iff_neighborFinset_eq M1 M2 p).1 hp12
        · exact model.realizationIso.map_rel_iff.mpr h01
        · exact model.realizationIso.map_rel_iff.mpr h12
        · exact model.realizationIso.map_rel_iff.mpr h02
      exact hfail _ ⟨hgroundSep, hfibre⟩
    · have hnCases : n = 2 ∨ n = 3 := by omega
      rcases hnCases with hnEq | hnEq
      · subst n
        exact hnb (separator_two_by_two_colorable hact)
      · subst n
        exact separator_twoRow_threeCol_violates_notK3 hd model hact hnb X


/-- **The separator-buffer theorem**, `SEPARATOR_BUFFER_2026-08-14.md`: on the main line, every pair
of distinct realizations has an admissible pivot. -/
theorem separator_buffer {d : V → ℕ} (hd : MainLine d) (X Y : Realization d) (hXY : X ≠ Y) :
    ∃ v : V, AdmissiblePivot d X Y v :=
  separator_buffer_completed hd X Y hXY
/-- **`(SB+)`**, the strengthening the one-pass route actually needs: the admissible pivot can be
chosen so that the prescribed endpoint pair is **not** the `(Q*)` exception.

Strictly stronger than `separator_buffer`, and not implied by it: the exception genuinely occurs at
separator-buffer-admissible pivots on main-line sequences (30 such pivots at ground order 8;
smallest witnesses `d = (4,4,3,3,3,1)` and `d = (4,2,2,2,1,1)`).

Proved 2026-08-15 at lead + decoupled-adversary + computation level; sealed 0 violations through
ground order 8 in two independent implementations and through orders 9 and 10 in two more. -/
theorem sbPlus {d : V → ℕ} (hd : MainLine d) (X Y : Realization d) (hXY : X ≠ Y) :
    ∃ v : V, AdmissiblePivot d X Y v ∧ ¬ ExceptionalPivot d X Y v := by
  classical
  obtain ⟨v, hvAdm⟩ := separator_buffer hd X Y hXY
  by_cases hvExc : ExceptionalPivot d X Y v
  · have hvYFamily : YFamilyPivot d v := by
      rcases hvExc with ⟨hX, hY, hbad⟩
      exact ⟨⟨X.neighborFinset v, hX⟩, ⟨Y.neighborFinset v, hY⟩, hbad⟩
    obtain ⟨C₀, c, a, b, x, hfc⟩ := fourCorner_of_yFamilyPivot hvYFamily
    have hmid := theorem_8_3_middle_degrees hfc
    have hclassCard := yFamilyPivot_degreeClass_card hvYFamily
    let C := Finset.univ.filter (fun u => d u = d v)
    have htripleSub : {v, a, b} ⊆ C := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · simp [C]
      · simp [C, hmid.1]
      · simp [C, hmid.2]
    have hva : v ≠ a := hfc.ne_pivot.2.1.symm
    have hvb : v ≠ b := hfc.ne_pivot.2.2.1.symm
    have hab : a ≠ b := hfc.distinct.2.2.2.1
    have htripleCard : ({v, a, b} : Finset V).card = 3 := by
      simp [hva, hvb, hab]
    have hclass : C = {v, a, b} := by
      symm
      apply Finset.eq_of_subset_of_card_le htripleSub
      rw [htripleCard]
      simpa [C] using hclassCard.le
    have hdiff : X.neighborFinset v ∆ Y.neighborFinset v = {a, b} := by
      rw [exceptionalPivot_symmDiff_eq_degreeClass hvExc]
      calc
        Finset.univ.filter (fun u => u ≠ v ∧ d u = d v) = C.erase v := by
          ext u
          simp [C, and_comm]
        _ = {a, b} := by
          rw [hclass]
          simp [hva, hvb]
    have separates_of_mem_symmDiff {z : V}
        (hz : z ∈ X.neighborFinset v ∆ Y.neighborFinset v) :
        z ∈ DifferenceSupport d X Y := by
      change X.neighborFinset z ≠ Y.neighborFinset z
      intro heq
      have hvEq : v ∈ X.neighborFinset z ↔ v ∈ Y.neighborFinset z := by
        rw [heq]
      simp only [Finset.mem_symmDiff] at hz
      rcases hz with ⟨hzX, hzY⟩ | ⟨hzY, hzX⟩
      · have hzX' : X.graph.Adj v z := by
          simpa only [Realization.mem_neighborFinset] using hzX
        have hzY' : ¬ Y.graph.Adj v z := by
          simpa only [Realization.mem_neighborFinset] using hzY
        have hvX : v ∈ X.neighborFinset z := by
          simpa only [Realization.mem_neighborFinset] using hzX'.symm
        have hvY : v ∉ Y.neighborFinset z := by
          simpa only [Realization.mem_neighborFinset] using fun h => hzY' h.symm
        exact hvY (hvEq.mp hvX)
      · have hzY' : Y.graph.Adj v z := by
          simpa only [Realization.mem_neighborFinset] using hzY
        have hzX' : ¬ X.graph.Adj v z := by
          simpa only [Realization.mem_neighborFinset] using hzX
        have hvY : v ∈ Y.neighborFinset z := by
          simpa only [Realization.mem_neighborFinset] using hzY'.symm
        have hvX : v ∉ X.neighborFinset z := by
          simpa only [Realization.mem_neighborFinset] using fun h => hzX' h.symm
        exact hvX (hvEq.mpr hvY)
    have haSep : a ∈ DifferenceSupport d X Y := by
      apply separates_of_mem_symmDiff
      rw [hdiff]
      simp
    have hbSep : b ∈ DifferenceSupport d X Y := by
      apply separates_of_mem_symmDiff
      rw [hdiff]
      simp
    have haFibre : HasNonBipartiteFibre d a :=
      hasNonBipartiteFibre_of_degree_eq hmid.1.symm hvAdm.2
    have hbFibre : HasNonBipartiteFibre d b :=
      hasNonBipartiteFibre_of_degree_eq hmid.2.symm hvAdm.2
    have haAdm : AdmissiblePivot d X Y a := ⟨haSep, haFibre⟩
    have hbAdm : AdmissiblePivot d X Y b := ⟨hbSep, hbFibre⟩
    have hnotAll := atMostTwoExceptional X Y v a b
      hfc.ne_pivot.2.1.symm hfc.distinct.2.2.2.1 hfc.ne_pivot.2.2.1.symm
    by_cases haExc : ExceptionalPivot d X Y a
    · refine ⟨b, hbAdm, ?_⟩
      intro hbExc
      exact hnotAll ⟨hvExc, haExc, hbExc⟩
    · exact ⟨a, haAdm, haExc⟩
  · exact ⟨v, hvAdm, hvExc⟩

/-! ## 5. `(ORD)` -/

/-- A **connector**: a literal 2-switch of the realization graph joining the `S`-fibre to the
`T`-fibre. The route's ordinary propagation step needs one out of the fibre it is currently in. -/
def IsConnectorSource (d : V → ℕ) (v : V) (T : Finset V) (y : Realization d) : Prop :=
  ∃ z : Realization d, z.neighborFinset v = T ∧ (RealizationGraph d).Adj y z

/-- The `S`-fibre at `v`, as an induced subgraph of the realization graph. This is the object the
prose calls `Φ_S` and asks to be maximally Hamiltonian. -/
noncomputable def fibreGraph (d : V → ℕ) (v : V) (S : Finset V) :
    SimpleGraph (Fibre d v S) :=
  (RealizationGraph d).induce (Fibre d v S)

/-- The set-based fibre graph used by `(ORD)`/`(OBI)` and the subtype-based interface fibre graph
used by `fibreDeleteIso` are the same induced graph, up to their two spellings of membership. -/
noncomputable def fibreGraphInterfaceFibreGraphIso (d : V → ℕ) (v : V) (S : Finset V) :
    fibreGraph d v S ≃g interfaceFibreGraph d v S :=
  { toEquiv := Equiv.refl _
    map_rel_iff' := Iff.rfl }

/-- Equality of realizations inside a fibre is decidable classically. Needed only so that
`HasHamPath` and `IsMH`, which are stated for a `DecidableEq` vertex type, apply to `fibreGraph`. -/
noncomputable instance fibreDecidableEq (d : V → ℕ) (v : V) (S : Finset V) :
    DecidableEq (Fibre d v S) := Classical.decEq _

/-- **The connector-source half of `(ORD)`**, which needs no maximal-Hamiltonicity hypothesis.

This is the `δ` dichotomy of `SEC_INTERFACE.md` §9.2 in the form the route consumes: some member of
the `S`-fibre carries a connector into the `T`-fibre, and it can be taken distinct from a prescribed
`x` unless the fibre is a singleton. Orient the hop as `T = S − b + a` and put `δ = f_S(a) − f_S(b)`;
if `δ ≥ 1` every member of the source fibre is a connector source, and if `δ ≤ 0` a single target
realization already has two distinct connector sources.

⚠ `δ ≥ 0` is **not** a general fact about ordinary hops — it fails at 8,876 of 88,518 hops through
ground order 7, as it must, since reversing the orientation sends `δ ↦ 2 − δ`. The dichotomy is
stated so that no branch needs it. -/
theorem ord_connector_source {d : V → ℕ} (v : V) (S T : Finset V)
    (hST : (S ∆ T).card = 2)
    (hS : HasRealizationWithNeighborSet d v S) (hT : HasRealizationWithNeighborSet d v T)
    (x : Realization d) (hx : x.neighborFinset v = S) :
    ∃ y : Realization d, y.neighborFinset v = S ∧ IsConnectorSource d v T y ∧
      (y ≠ x ∨ ∀ z : Realization d, z.neighborFinset v = S → z = x) := by
  classical
  obtain ⟨G, hG⟩ := hS
  obtain ⟨H, hH⟩ := hT
  have hScard : S.card = d v := by
    rw [← hG]
    simp [Realization.neighborFinset, SimpleGraph.card_neighborFinset_eq_degree,
      G.degree_eq v]
  have hTcard : T.card = d v := by
    rw [← hH]
    simp [Realization.neighborFinset, SimpleGraph.card_neighborFinset_eq_degree,
      H.degree_eq v]
  have hcard : S.card = T.card := hScard.trans hTcard.symm
  have hbalanced : (T \ S).card = (S \ T).card := Finset.card_sdiff_comm hcard.symm
  have hsdiff_card : (S \ T).card = 1 := by
    rw [Finset.symmDiff_def,
      Finset.card_union_of_disjoint
        (Finset.sdiff_disjoint.mono_right Finset.sdiff_subset)] at hST
    omega
  have hsdiff_card' : (T \ S).card = 1 := by
    omega
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hsdiff_card
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hsdiff_card'
  have hbST : b ∈ S \ T := hb.symm.subset (Finset.mem_singleton_self b)
  have haTS : a ∈ T \ S := ha.symm.subset (Finset.mem_singleton_self a)
  have hbS : b ∈ S := (Finset.mem_sdiff.mp hbST).1
  have hbT : b ∉ T := (Finset.mem_sdiff.mp hbST).2
  have haT : a ∈ T := (Finset.mem_sdiff.mp haTS).1
  have haS : a ∉ S := (Finset.mem_sdiff.mp haTS).2
  have hTform : T = insert a (S.erase b) := by
    ext z
    constructor
    · intro hzT
      by_cases hzS : z ∈ S
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨by
          rintro rfl
          exact hbT hzT, hzS⟩))
      · have hz : z ∈ T \ S := Finset.mem_sdiff.mpr ⟨hzT, hzS⟩
        have : z = a := by simpa [ha] using hz
        exact Finset.mem_insert.mpr (Or.inl this)
    · intro hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact haT
      · obtain ⟨hzb, hzS⟩ := Finset.mem_erase.mp hz
        by_contra hzT
        have hz' : z ∈ S \ T := Finset.mem_sdiff.mpr ⟨hzS, hzT⟩
        have : z = b := by simpa [hb] using hz'
        exact hzb this
  have hav : a ≠ v := by
    intro hav
    subst a
    have : v ∈ H.neighborFinset v := by simpa [hH] using haT
    exact (SimpleGraph.notMem_neighborFinset_self H.graph v) this
  have hbv : b ≠ v := by
    intro hbv
    subst b
    have : v ∈ G.neighborFinset v := by simpa [hG] using hbS
    exact (SimpleGraph.notMem_neighborFinset_self G.graph v) this
  let av : {u : V // u ≠ v} := ⟨a, hav⟩
  let bv : {u : V // u ≠ v} := ⟨b, hbv⟩
  by_cases hdelta : residualDegree d v S bv < residualDegree d v S av
  · have source_connector (Y : Realization d) (hY : Y.neighborFinset v = S) :
        IsConnectorSource d v T Y := by
      have hlower :
          residualDegree d v S av - residualDegree d v S bv ≤
            (sSideConnectorTargets Y hY hbS haS hav hbv).card := by
        simpa [av, bv] using sSide_connector_degree_lower_bound Y hY hbS haS hav hbv
      have hpositive : 0 < (sSideConnectorTargets Y hY hbS haS hav hbv).card := by
        have : 0 < residualDegree d v S av - residualDegree d v S bv :=
          Nat.sub_pos_of_lt hdelta
        omega
      obtain ⟨Z, hZ⟩ := Finset.card_pos.mp hpositive
      obtain ⟨hZN, hYZ⟩ := mem_sSideConnectorTargets_spec Y hY hbS haS hav hbv hZ
      refine ⟨Z, ?_, ?_⟩
      · simpa [hTform] using hZN
      · exact hYZ
    by_cases hne : ∃ Y : Realization d, Y.neighborFinset v = S ∧ Y ≠ x
    · obtain ⟨Y, hY, hYx⟩ := hne
      exact ⟨Y, hY, source_connector Y hY, Or.inl hYx⟩
    · refine ⟨x, hx, source_connector x hx, Or.inr ?_⟩
      intro Z hZ
      by_contra hZx
      exact hne ⟨Z, hZ, hZx⟩
  · have hle : residualDegree d v S av ≤ residualDegree d v S bv :=
      Nat.le_of_not_lt hdelta
    have hlower :
        residualDegree d v S bv + 2 - residualDegree d v S av ≤
          (sPrimeSideConnectorTargets H (hTform ▸ hH) hbS haS hav hbv).card := by
      simpa [av, bv] using sPrimeSide_connector_degree_lower_bound
        (⟨G, hG⟩ : HasRealizationWithNeighborSet d v S) H (hTform ▸ hH)
          hbS haS hav hbv
    have htwo : 1 < (sPrimeSideConnectorTargets H (hTform ▸ hH) hbS haS hav hbv).card := by
      have : 2 ≤ residualDegree d v S bv + 2 - residualDegree d v S av := by omega
      omega
    obtain ⟨Y, hYmem, hYx⟩ := Finset.exists_mem_ne htwo x
    obtain ⟨hYN, hYH⟩ := mem_sPrimeSideConnectorTargets_spec
      H (hTform ▸ hH) hbS haS hav hbv hYmem
    exact ⟨Y, hYN, ⟨H, hH, hYH⟩, Or.inl hYx⟩

/-- **`(ORD)`, ordinary propagation** — manuscript Theorem 9.1 (`paper/SEC_INTERFACE.md` §9.2),
with **no Hladík–Fink input**. It replaces the citation of Hladík–Fink Lemma 1.3, which
`HF_DEFECT_2026-08-14.md` §323 marked unsafe because their printed proof passes through the Theorem
3.3 this lane refuted. Sealed at 50,957,138 ordinary hops through ground order 8, 0 failures.

CORRECTED 2026-08-17, and the previous version is recorded as a defect rather than quietly replaced.
This theorem previously stated only that a connector source EXISTS, with an endpoint dodge, and
carried **no** `hMH` hypothesis — while its own docstring described a spanning run and referred to
"the hypothesis `hMH`", which was not in the signature. So the Lean stated a different theorem from
the one it named: it dropped the maximal-Hamiltonicity hypothesis that manuscript Theorem 9.1 makes,
and dropped the spanning-run conclusion that theorem draws. That is the same defect class as
`crossingLemma`'s endpoint-only dodge, found and repaired earlier in this development, and it is why the
docstring is now checked against the statement rather than trusted alongside it.

The connector-source half is genuinely true without `hMH` — it is the `δ` dichotomy — and is kept
above as `ord_connector_source`, which is what a consumer needing only a connector should cite. -/
theorem ord {d : V → ℕ} (v : V) (S T : Finset V)
    (hST : (S ∆ T).card = 2)
    (hS : HasRealizationWithNeighborSet d v S) (hT : HasRealizationWithNeighborSet d v T)
    (hMH : IsMH (fibreGraph d v S))
    (x : Realization d) (hx : x.neighborFinset v = S) (hxS : x ∈ Fibre d v S) :
    ∃ y : Realization d, ∃ hyS : y ∈ Fibre d v S,
      IsConnectorSource d v T y ∧
      HasHamPath (fibreGraph d v S) ⟨x, hxS⟩ ⟨y, hyS⟩ := by
  classical
  by_cases hsingle : ∀ z : Realization d, z.neighborFinset v = S → z = x
  · have hneST : S ≠ T := by
      intro h
      subst T
      simp at hST
    let qS : QuotientV d v := ⟨S, hS⟩
    let qT : QuotientV d v := ⟨T, hT⟩
    have hqne : qS ≠ qT := by
      intro h
      exact hneST (congrArg Subtype.val h)
    have hqadj : (quotientGraph d v).Adj qS qT := by
      rw [quotientGraph, SimpleGraph.fromRel_adj]
      exact ⟨hqne, Or.inl hST⟩
    obtain ⟨G, H, hG, hH, hGH⟩ :=
      (quotient_adjacency d v qS qT hqne).mp hqadj
    have hGx : G = x := hsingle G (by simpa [qS] using hG)
    subst G
    letI : Subsingleton (Fibre d v S) :=
      ⟨fun A B => Subtype.ext ((hsingle A.1 A.2).trans (hsingle B.1 B.2).symm)⟩
    refine ⟨x, hxS, ⟨H, ?_, hGH⟩, ?_⟩
    · simpa [qT] using hH
    · exact ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsHamiltonian.of_subsingleton⟩
  · rcases hMH with hconnected | ⟨col, hproper, hsurj, hlace⟩
    · obtain ⟨y, hy, hyconn, hyne | hall⟩ :=
        ord_connector_source v S T hST hS hT x hx
      · have hyS : y ∈ Fibre d v S := hy
        refine ⟨y, hyS, hyconn, hconnected ⟨x, hxS⟩ ⟨y, hyS⟩ ?_⟩
        intro hxy
        exact hyne (congrArg Subtype.val hxy).symm
      · exact (hsingle hall).elim
    · obtain ⟨G, hG⟩ := hS
      obtain ⟨H, hH⟩ := hT
      have hScard : S.card = d v := by
        rw [← hG]
        simp [Realization.neighborFinset, SimpleGraph.card_neighborFinset_eq_degree,
          G.degree_eq v]
      have hTcard : T.card = d v := by
        rw [← hH]
        simp [Realization.neighborFinset, SimpleGraph.card_neighborFinset_eq_degree,
          H.degree_eq v]
      have hcard : S.card = T.card := hScard.trans hTcard.symm
      have hbalanced : (T \ S).card = (S \ T).card := Finset.card_sdiff_comm hcard.symm
      have hsdiff_card : (S \ T).card = 1 := by
        rw [Finset.symmDiff_def,
          Finset.card_union_of_disjoint
            (Finset.sdiff_disjoint.mono_right Finset.sdiff_subset)] at hST
        omega
      have hsdiff_card' : (T \ S).card = 1 := by omega
      obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hsdiff_card
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hsdiff_card'
      have hbST : b ∈ S \ T := hb.symm.subset (Finset.mem_singleton_self b)
      have haTS : a ∈ T \ S := ha.symm.subset (Finset.mem_singleton_self a)
      have hbS : b ∈ S := (Finset.mem_sdiff.mp hbST).1
      have hbT : b ∉ T := (Finset.mem_sdiff.mp hbST).2
      have haT : a ∈ T := (Finset.mem_sdiff.mp haTS).1
      have haS : a ∉ S := (Finset.mem_sdiff.mp haTS).2
      have hTform : T = insert a (S.erase b) := by
        ext z
        constructor
        · intro hzT
          by_cases hzS : z ∈ S
          · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨by
              rintro rfl
              exact hbT hzT, hzS⟩))
          · have hz : z ∈ T \ S := Finset.mem_sdiff.mpr ⟨hzT, hzS⟩
            have : z = a := by simpa [ha] using hz
            exact Finset.mem_insert.mpr (Or.inl this)
        · intro hz
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact haT
          · obtain ⟨hzb, hzS⟩ := Finset.mem_erase.mp hz
            by_contra hzT
            have hz' : z ∈ S \ T := Finset.mem_sdiff.mpr ⟨hzS, hzT⟩
            have : z = b := by simpa [hb] using hz'
            exact hzb this
      have hav : a ≠ v := by
        intro hav
        subst a
        have : v ∈ H.neighborFinset v := by simpa [hH] using haT
        exact (SimpleGraph.notMem_neighborFinset_self H.graph v) this
      have hbv : b ≠ v := by
        intro hbv
        subst b
        have : v ∈ G.neighborFinset v := by simpa [hG] using hbS
        exact (SimpleGraph.notMem_neighborFinset_self G.graph v) this
      have hproper' : ∀ A B : interfaceFibre d v S,
          (interfaceFibreGraph d v S).Adj A B → col A ≠ col B := by
        intro A B hAB
        apply hproper A B
        exact hAB
      obtain ⟨y, hycol⟩ := hsurj (!(col ⟨x, hxS⟩))
      have hyopp : col ⟨x, hxS⟩ ≠ col y := by
        rw [hycol]
        exact Bool.self_ne_not _
      let yi : interfaceFibre d v S := ⟨y.1, y.2⟩
      have hyiopp : col ⟨x, hxS⟩ ≠ col yi := by
        simpa [yi] using hyopp
      let A : Finset (interfaceFibre d v S) := {yi}
      have hAcol : ∀ z ∈ A, col z = col yi := by
        intro z hz
        have hzy : z = yi := by
          apply Finset.mem_singleton.mp
          exact hz
        subst z
        rfl
      have hTreal : HasRealizationWithNeighborSet d v (insert a (S.erase b)) := by
        rw [← hTform]
        exact ⟨H, hH⟩
      have hexpand := theorem_5_8_exact_color_expansion hbS haS
        (⟨G, hG⟩ : HasRealizationWithNeighborSet d v S)
        hTreal hav hbv col hproper' (col yi) A hAcol
      have hNpos : 0 < (connectorNeighborhood hbS haS hav hbv A).card := by
        rw [hexpand]
        apply Nat.mul_pos
        · omega
        · change 0 < ({yi} : Finset (interfaceFibre d v S)).card
          rw [Finset.card_singleton]
          exact Nat.zero_lt_one
      obtain ⟨Z, hZ⟩ := Finset.card_pos.mp hNpos
      have hZ' : Z ∈ sSideConnectorTargets yi.1 yi.2 hbS haS hav hbv := by
        rw [connectorNeighborhood, Finset.mem_biUnion] at hZ
        obtain ⟨y', hy'A, hZ'⟩ := hZ
        have hy'y : y' = yi := by
          apply Finset.mem_singleton.mp
          exact hy'A
        subst y'
        exact hZ'
      obtain ⟨hZN, hyZ⟩ :=
        mem_sSideConnectorTargets_spec yi.1 yi.2 hbS haS hav hbv hZ'
      refine ⟨yi.1, yi.2, ⟨Z, ?_, hyZ⟩, hlace ⟨x, hxS⟩ yi hyiopp⟩
      simpa [hTform] using hZN

/-! ### 5a. Avoiding one prescribed target -/

set_option maxHeartbeats 10000000

/-- `interfaceFibre` is deliberately a `def`, so typeclass search does not unfold it to the
already-finite subtype `Fibre`.  Keep the two spellings on the same finite enumeration locally. -/
noncomputable local instance fibreFintypeForObi
    (d : V → ℕ) (v : V) (S : Finset V) : Fintype (Fibre d v S) :=
  Fintype.ofInjective (fun G : Fibre d v S => G.1) (by
    intro G H h
    exact Subtype.ext h)

noncomputable local instance interfaceFibreFintypeForObi
    (d : V → ℕ) (v : V) (S : Finset V) : Fintype (interfaceFibre d v S) :=
  Fintype.ofInjective (fun G : interfaceFibre d v S => G.1) (by
    intro G H h
    exact Subtype.ext h)

/-- The two fibre spellings have the same finite cardinality. -/
private theorem card_interfaceFibre_eq_fibre (d : V → ℕ) (v : V) (S : Finset V) :
    Fintype.card (interfaceFibre d v S) = Fintype.card (Fibre d v S) := by
  apply Fintype.card_congr
  exact
    { toFun := fun G => ⟨G.1, G.2⟩
      invFun := fun G => ⟨G.1, G.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- A connector constructed from the `S` side is literally reversible by the constructor on the
`T` side.  This is the set-level bridge needed below: the same interface edge is counted at both
endpoints, with no appeal to a second notion of connector. -/
private theorem connectorTarget_mem_reverse {d : V → ℕ} {S : Finset V} {v a b : V}
    (G : Realization d) (hS : G.neighborFinset v = S) (hbS : b ∈ S) (haS : a ∉ S)
    (hav : a ≠ v) (hbv : b ≠ v) {H : Realization d}
    (hHT : H.neighborFinset v = insert a (S.erase b))
    (hH : H ∈ sSideConnectorTargets G hS hbS haS hav hbv) :
    G ∈ sPrimeSideConnectorTargets H hHT hbS haS hav hbv := by
  classical
  rw [sSideConnectorTargets, Finset.mem_image] at hH
  obtain ⟨c, hc, rfl⟩ := hH
  have hdata := residualConnectorCandidate_spec G c.2
  have hab : a ≠ b := fun h => haS (h ▸ hbS)
  simp only [sPrimeSideConnectorTargets]
  rw [sSideConnectorTargets, Finset.mem_image]
  have hc' : c.1 ∈ residualConnectorCandidates
      (sSideConnectorSwitch G hS hbS haS hav hbv c.1 c.2) v b a hbv hav := by
    let K := sSideConnectorSwitch G hS hbS haS hav hbv c.1 c.2
    have hca : c.1.val ≠ a := hdata.2.1.ne
    have hKcb : K.graph.Adj c.1.val b := by
      change (quotientSwitchGraph G.graph v b a c.1.val).Adj c.1.val b
      simp [quotientSwitchGraph, transferGraph, hdata.1]
    have hKca : ¬ K.graph.Adj c.1.val a := by
      change ¬ (quotientSwitchGraph G.graph v b a c.1.val).Adj c.1.val a
      simp [quotientSwitchGraph, transferGraph, hdata.2.1, hdata.1,
        hca, c.1.property, hav, hab]
    simp only [residualConnectorCandidates, Finset.mem_sdiff, Finset.mem_erase,
      SimpleGraph.mem_neighborFinset, deleteVertexGraph]
    constructor
    · constructor
      · exact fun h => hca (congrArg Subtype.val h)
      · simpa using hKcb.symm
    · rintro ⟨_, h⟩
      exact hKca (by simpa using h.symm)
  refine ⟨⟨c.1, hc'⟩, by simp, ?_⟩
  let K := sSideConnectorSwitch G hS hbS haS hav hbv c.1 c.2
  have hbK : a ∈ insert a (S.erase b) := Finset.mem_insert_self _ _
  have haK : b ∉ insert a (S.erase b) := by simp [hab.symm]
  change sSideConnectorSwitch K hHT hbK haK hbv hav c.1 hc' = G
  apply realization_eq_of_edgeFinset_eq
  have hforward := sSideConnectorSwitch_symmDiff G hS hbS haS hav hbv c.1 c.2
  have hreverse := sSideConnectorSwitch_symmDiff K hHT hbK haK hbv hav c.1 hc'
  have hcancel (A B : Finset (Sym2 V)) : A = B ∆ (B ∆ A) := by
    calc
      A = A ∆ (B ∆ B) := by rw [symmDiff_self, symmDiff_bot]
      _ = B ∆ (B ∆ A) := by ac_rfl
  calc
    (sSideConnectorSwitch K hHT hbK haK hbv hav c.1 hc').edgeFinset =
        K.edgeFinset ∆ {s(a, v), s(b, c.1.val), s(b, v), s(a, c.1.val)} := by
          rw [← hreverse]
          exact hcancel _ _
    _ = K.edgeFinset ∆ {s(b, v), s(a, c.1.val), s(a, v), s(b, c.1.val)} := by
          congr 1
          ext e
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
    _ = G.edgeFinset := by
          rw [← hforward]
          calc
            K.edgeFinset ∆ (G.edgeFinset ∆ K.edgeFinset) =
                K.edgeFinset ∆ (K.edgeFinset ∆ G.edgeFinset) := by ac_rfl
            _ = G.edgeFinset := (hcancel _ _).symm

/-- The reverse-side constructor returns the original source target as well. -/
private theorem connectorSource_mem_reverse {d : V → ℕ} {S : Finset V} {v a b : V}
    (H : Realization d) (hH : H.neighborFinset v = insert a (S.erase b))
    (hbS : b ∈ S) (haS : a ∉ S) (hav : a ≠ v) (hbv : b ≠ v)
    {G : Realization d}
    (hG : G ∈ sPrimeSideConnectorTargets H hH hbS haS hav hbv) :
    H ∈ sSideConnectorTargets G
      (mem_sPrimeSideConnectorTargets_spec H hH hbS haS hav hbv hG).1
      hbS haS hav hbv := by
  classical
  have hab : a ≠ b := fun h => haS (h ▸ hbS)
  have hbK : a ∈ insert a (S.erase b) := Finset.mem_insert_self _ _
  have haK : b ∉ insert a (S.erase b) := by simp [hab.symm]
  have hrev : G ∈ sSideConnectorTargets H hH hbK haK hbv hav := by
    simpa [sPrimeSideConnectorTargets, hab, hbK, haK] using hG
  have hback := connectorTarget_mem_reverse H hH hbK haK hbv hav
    (mem_sSideConnectorTargets_spec H hH hbK haK hbv hav hrev).1 hrev
  simpa [sPrimeSideConnectorTargets, hab, hbS, haS] using hback

/-- The exact signed degree difference across a constructed connector edge.  It is Theorem 5.6's
edge identity after deleting the pivot, translated back to the existing finite target sets. -/
private theorem connectorTarget_degree_difference {d : V → ℕ} {S : Finset V} {v a b : V}
    (G : Realization d) (hS : G.neighborFinset v = S) (hbS : b ∈ S) (haS : a ∉ S)
    (hav : a ≠ v) (hbv : b ≠ v) {H : Realization d}
    (hH : H ∈ sSideConnectorTargets G hS hbS haS hav hbv) :
    ((sSideConnectorTargets G hS hbS haS hav hbv).card : ℤ) -
        (sPrimeSideConnectorTargets H
          (mem_sSideConnectorTargets_spec G hS hbS haS hav hbv hH).1
          hbS haS hav hbv).card =
      (residualDegree d v S ⟨a, hav⟩ : ℤ) - residualDegree d v S ⟨b, hbv⟩ - 1 := by
  classical
  rw [sSideConnectorTargets, Finset.mem_image] at hH
  obtain ⟨c, hc, rfl⟩ := hH
  let K := sSideConnectorSwitch G hS hbS haS hav hbv c.1 c.2
  have hK : K.neighborFinset v = insert a (S.erase b) :=
    (sSideConnectorSwitch_spec G hS hbS haS hav hbv c.1 c.2).1
  have hab : a ≠ b := fun h => haS (h ▸ hbS)
  have hbK : a ∈ insert a (S.erase b) := Finset.mem_insert_self _ _
  have haK : b ∉ insert a (S.erase b) := by simp [hab.symm]
  have hdata := residualConnectorCandidate_spec G c.2
  let F := deleteVertexGraph_realizes_residual G v S hS
  let av : {x : V // x ≠ v} := ⟨a, hav⟩
  let bv : {x : V // x ≠ v} := ⟨b, hbv⟩
  have hcav : F.graph.Adj c.1 av := by
    change G.graph.Adj c.1.val a
    exact hdata.2.1
  have hcbv : ¬ F.graph.Adj c.1 bv := by
    change ¬ G.graph.Adj c.1.val b
    exact hdata.2.2
  have habv : av ≠ bv := by
    intro h
    exact hab (congrArg Subtype.val h)
  have hbvc : bv ≠ c.1 := by
    intro h
    exact hdata.1 (congrArg Subtype.val h).symm
  have hgraph : deleteVertexGraph K.graph v = transferGraph F.graph av bv c.1 := by
    ext x y
    simp only [K, F, deleteVertexGraph, sSideConnectorSwitch, quotientSwitchRealization,
      quotientSwitchGraph, transferGraph]
    have hvb : G.graph.Adj v b := by
      rw [← Realization.mem_neighborFinset, hS]
      exact hbS
    have hva : ¬ G.graph.Adj v a := by
      intro h
      exact haS (by rw [← hS, Realization.mem_neighborFinset]; exact h)
    aesop
  rw [card_sSideConnectorTargets_eq_interfaceWitnessCount]
  simp only [sPrimeSideConnectorTargets]
  rw [card_sSideConnectorTargets_eq_interfaceWitnessCount]
  change (interfaceWitnessCount F.graph av bv : ℤ) -
      interfaceWitnessCount (deleteVertexGraph K.graph v) bv av = _
  simpa only [hgraph] using interface_edge_degree_difference F hcav hcbv habv hbvc

set_option maxHeartbeats 200000

/-- If both sides have at least three vertices, an endpoint distinct from `x` and a connector target
distinct from `bad` can be chosen simultaneously.  The middle signed-degree case is where the
quantifier order matters: two candidate endpoints are inspected only after `bad` is fixed. -/
private theorem exists_avoiding_connector_of_source_card_three
    {d : V → ℕ} {S : Finset V} {v a b : V}
    (hSreal : HasRealizationWithNeighborSet d v S)
    (x : Realization d) (hx : x.neighborFinset v = S)
    (bad : Realization d) (hbad : bad.neighborFinset v = insert a (S.erase b))
    (hbS : b ∈ S) (haS : a ∉ S) (hav : a ≠ v) (hbv : b ≠ v)
    (hScard : 3 ≤ Fintype.card (interfaceFibre d v S))
    (hTcard : 3 ≤ Fintype.card (interfaceFibre d v (insert a (S.erase b)))) :
    ∃ y z : Realization d,
      y.neighborFinset v = S ∧ y ≠ x ∧
      z.neighborFinset v = insert a (S.erase b) ∧ z ≠ bad ∧
      (RealizationGraph d).Adj y z := by
  classical
  let xi : interfaceFibre d v S := ⟨x, hx⟩
  have htwoSource : 1 < ((Finset.univ : Finset (interfaceFibre d v S)).erase xi).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ xi), Finset.card_univ]
    omega
  obtain ⟨y₁, hy₁, y₂, hy₂, hy₁y₂⟩ := Finset.one_lt_card.mp htwoSource
  have hy₁x : y₁.1 ≠ x := by
    intro h
    exact (Finset.mem_erase.mp hy₁).1 (Subtype.ext h)
  have hy₂x : y₂.1 ≠ x := by
    intro h
    exact (Finset.mem_erase.mp hy₂).1 (Subtype.ext h)
  let badi : interfaceFibre d v (insert a (S.erase b)) := ⟨bad, hbad⟩
  have htargetOutside : 0 <
      ((Finset.univ : Finset (interfaceFibre d v (insert a (S.erase b)))).erase badi).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ badi), Finset.card_univ]
    omega
  obtain ⟨z₀, hz₀⟩ := Finset.card_pos.mp htargetOutside
  have hz₀bad : z₀.1 ≠ bad := by
    intro h
    exact (Finset.mem_erase.mp hz₀).1 (Subtype.ext h)
  let da := residualDegree d v S ⟨a, hav⟩
  let db := residualDegree d v S ⟨b, hbv⟩
  by_cases hhigh : db + 2 ≤ da
  · have hlower := sSide_connector_degree_lower_bound y₁.1 y₁.2 hbS haS hav hbv
    have htwo : 1 < (sSideConnectorTargets y₁.1 y₁.2 hbS haS hav hbv).card := by
      dsimp [da, db] at hhigh
      omega
    obtain ⟨z, hz, hzbad⟩ := Finset.exists_mem_ne htwo bad
    obtain ⟨hzN, hyz⟩ :=
      mem_sSideConnectorTargets_spec y₁.1 y₁.2 hbS haS hav hbv hz
    exact ⟨y₁.1, z, y₁.2, hy₁x, hzN, hzbad, hyz⟩
  · by_cases hlow : da ≤ db
    · have hlower := sPrimeSide_connector_degree_lower_bound hSreal z₀.1 z₀.2
        hbS haS hav hbv
      have htwo : 1 <
          (sPrimeSideConnectorTargets z₀.1 z₀.2 hbS haS hav hbv).card := by
        dsimp [da, db] at hlow
        omega
      obtain ⟨y, hy, hyx⟩ := Finset.exists_mem_ne htwo x
      obtain ⟨hyN, hyz⟩ :=
        mem_sPrimeSideConnectorTargets_spec z₀.1 z₀.2 hbS haS hav hbv hy
      exact ⟨y, z₀.1, hyN, hyx, z₀.2, hz₀bad, hyz⟩
    · have hmiddle : da = db + 1 := by omega
      have hlower₁ := sSide_connector_degree_lower_bound y₁.1 y₁.2 hbS haS hav hbv
      have hpos₁ : 0 < (sSideConnectorTargets y₁.1 y₁.2 hbS haS hav hbv).card := by
        dsimp [da, db] at hmiddle
        omega
      obtain ⟨z₁, hz₁⟩ := Finset.card_pos.mp hpos₁
      by_cases hz₁bad : z₁ ≠ bad
      · obtain ⟨hz₁N, hy₁z₁⟩ :=
          mem_sSideConnectorTargets_spec y₁.1 y₁.2 hbS haS hav hbv hz₁
        exact ⟨y₁.1, z₁, y₁.2, hy₁x, hz₁N, hz₁bad, hy₁z₁⟩
      · have hz₁eq : z₁ = bad := not_ne_iff.mp hz₁bad
        have hbad₁ : bad ∈ sSideConnectorTargets y₁.1 y₁.2 hbS haS hav hbv := by
          simpa [hz₁eq] using hz₁
        have hlower₂ := sSide_connector_degree_lower_bound y₂.1 y₂.2 hbS haS hav hbv
        have hpos₂ : 0 < (sSideConnectorTargets y₂.1 y₂.2 hbS haS hav hbv).card := by
          dsimp [da, db] at hmiddle
          omega
        obtain ⟨z₂, hz₂⟩ := Finset.card_pos.mp hpos₂
        by_cases hz₂bad : z₂ ≠ bad
        · obtain ⟨hz₂N, hy₂z₂⟩ :=
            mem_sSideConnectorTargets_spec y₂.1 y₂.2 hbS haS hav hbv hz₂
          exact ⟨y₂.1, z₂, y₂.2, hy₂x, hz₂N, hz₂bad, hy₂z₂⟩
        · have hz₂eq : z₂ = bad := not_ne_iff.mp hz₂bad
          have hbad₂ : bad ∈ sSideConnectorTargets y₂.1 y₂.2 hbS haS hav hbv := by
            simpa [hz₂eq] using hz₂
          have hy₁rev : y₁.1 ∈ sPrimeSideConnectorTargets bad hbad hbS haS hav hbv := by
            simpa using connectorTarget_mem_reverse y₁.1 y₁.2 hbS haS hav hbv hbad hbad₁
          have hy₂rev : y₂.1 ∈ sPrimeSideConnectorTargets bad hbad hbS haS hav hbv := by
            simpa using connectorTarget_mem_reverse y₂.1 y₂.2 hbS haS hav hbv hbad hbad₂
          have hy₁val_ne_y₂val : y₁.1 ≠ y₂.1 := by
            intro h
            exact hy₁y₂ (Subtype.ext h)
          have hrevTwo : 1 <
              (sPrimeSideConnectorTargets bad hbad hbS haS hav hbv).card :=
            Finset.one_lt_card.mpr
              ⟨y₁.1, hy₁rev, y₂.1, hy₂rev, hy₁val_ne_y₂val⟩
          have hdiff := connectorTarget_degree_difference
            y₁.1 y₁.2 hbS haS hav hbv hbad₁
          have hsourceTwo : 1 <
              (sSideConnectorTargets y₁.1 y₁.2 hbS haS hav hbv).card := by
            have hdiff' :
                ((sSideConnectorTargets y₁.1 y₁.2 hbS haS hav hbv).card : ℤ) -
                    (sPrimeSideConnectorTargets bad hbad hbS haS hav hbv).card = 0 := by
              simpa [da, db, hmiddle] using hdiff
            omega
          obtain ⟨z, hz, hzbad⟩ := Finset.exists_mem_ne hsourceTwo bad
          obtain ⟨hzN, hyz⟩ :=
            mem_sSideConnectorTargets_spec y₁.1 y₁.2 hbS haS hav hbv hz
          exact ⟨y₁.1, z, y₁.2, hy₁x, hzN, hzbad, hyz⟩

/-- A source fibre of order at most two has at least two connector targets at every vertex whenever
the target is non-bipartite (hence has order at least three). -/
private theorem two_le_cross_degree_of_small_source
    {d : V → ℕ} {S : Finset V} {v a b : V}
    (hSreal : HasRealizationWithNeighborSet d v S)
    (hTreal : HasRealizationWithNeighborSet d v (insert a (S.erase b)))
    (hbS : b ∈ S) (haS : a ∉ S) (hav : a ≠ v) (hbv : b ≠ v)
    (hScard : Fintype.card (interfaceFibre d v S) ≤ 2)
    (hTcard : 3 ≤ Fintype.card (interfaceFibre d v (insert a (S.erase b)))) :
    2 ≤ max 1
      (residualDegree d v S ⟨a, hav⟩ - residualDegree d v S ⟨b, hbv⟩) := by
  classical
  have htriangle : (interfaceFibreGraph d v S).CliqueFree 3 :=
    SimpleGraph.cliqueFree_of_card_lt (by omega)
  have hcross := theorem_5_7_cross_degree hbS haS hSreal hTreal hav hbv htriangle
  let k := max 1
    (residualDegree d v S ⟨a, hav⟩ - residualDegree d v S ⟨b, hbv⟩)
  by_contra hk
  have hkone : k = 1 := by
    dsimp [k]
    omega
  have hdeltaLow : residualDegree d v S ⟨a, hav⟩ ≤
      residualDegree d v S ⟨b, hbv⟩ + 1 := by
    have hnonneg := hcross.1
    dsimp [k] at hkone
    omega
  have reverse_nonempty
      (Z : interfaceFibre d v (insert a (S.erase b))) :
      (sPrimeSideConnectorTargets Z.1 Z.2 hbS haS hav hbv).Nonempty := by
    have hlower := sPrimeSide_connector_degree_lower_bound hSreal Z.1 Z.2
      hbS haS hav hbv
    apply Finset.card_pos.mp
    omega
  let sourceOf
      (Z : interfaceFibre d v (insert a (S.erase b))) : interfaceFibre d v S :=
    ⟨Classical.choose (reverse_nonempty Z),
      (mem_sPrimeSideConnectorTargets_spec Z.1 Z.2 hbS haS hav hbv
        (Classical.choose_spec (reverse_nonempty Z))).1⟩
  have hsourceOf_mem
      (Z : interfaceFibre d v (insert a (S.erase b))) :
      (sourceOf Z).1 ∈ sPrimeSideConnectorTargets Z.1 Z.2 hbS haS hav hbv := by
    exact Classical.choose_spec (reverse_nonempty Z)
  have hsourceOf_forward
      (Z : interfaceFibre d v (insert a (S.erase b))) :
      Z.1 ∈ sSideConnectorTargets (sourceOf Z).1 (sourceOf Z).2 hbS haS hav hbv := by
    simpa using connectorSource_mem_reverse Z.1 Z.2 hbS haS hav hbv (hsourceOf_mem Z)
  have hsourceOf_injective : Function.Injective sourceOf := by
    intro Z W hZW
    have hZmem : Z.1 ∈
        sSideConnectorTargets (sourceOf Z).1 (sourceOf Z).2 hbS haS hav hbv :=
      hsourceOf_forward Z
    have hWmem : W.1 ∈
        sSideConnectorTargets (sourceOf Z).1 (sourceOf Z).2 hbS haS hav hbv := by
      have hW := hsourceOf_forward W
      simpa [hZW] using hW
    have hdegree := hcross.2 (sourceOf Z)
    have hcardLe :
        (sSideConnectorTargets (sourceOf Z).1 (sourceOf Z).2 hbS haS hav hbv).card ≤ 1 := by
      simpa [k, hkone] using hdegree.le
    apply Subtype.ext
    exact Finset.card_le_one.mp hcardLe Z.1 hZmem W.1 hWmem
  have hcardLe := Fintype.card_le_of_injective sourceOf hsourceOf_injective
  omega

/-- **Manuscript Theorem 9.2 (`(OBI)`), avoiding one target.**

If the target fibre is non-bipartite and the source fibre is maximally Hamiltonian, then after a
source entry `x` and a forbidden target `bad` are fixed, one may choose jointly a source endpoint,
a spanning run to it, and a literal connector whose target is not `bad`.

The quantifier order is deliberate and load-bearing: `bad` is an argument before the existential
tuple `y, z`.  In particular this does **not** choose `y` before seeing `bad`. -/
theorem obi {d : V → ℕ} (v : V) (S T : Finset V)
    (hST : (S ∆ T).card = 2)
    (hS : HasRealizationWithNeighborSet d v S) (hT : HasRealizationWithNeighborSet d v T)
    (hTnb : ¬ ∃ col : Fibre d v T → Bool,
      IsProper2Coloring (fibreGraph d v T) col)
    (hMH : IsMH (fibreGraph d v S))
    (x : Realization d) (hx : x.neighborFinset v = S) (hxS : x ∈ Fibre d v S)
    (bad : Realization d) (hbadT : bad ∈ Fibre d v T) :
    ∃ y : Realization d, ∃ hyS : y ∈ Fibre d v S,
      IsConnectorSource d v T y ∧
      HasHamPath (fibreGraph d v S) ⟨x, hxS⟩ ⟨y, hyS⟩ ∧
      ∃ z : Realization d,
        z.neighborFinset v = T ∧ (RealizationGraph d).Adj y z ∧ z ≠ bad := by
  classical
  obtain ⟨G, hG⟩ := hS
  obtain ⟨K, hK⟩ := hT
  have hScard : S.card = d v := by
    rw [← hG]
    simp [Realization.neighborFinset, SimpleGraph.card_neighborFinset_eq_degree,
      G.degree_eq v]
  have hTcard : T.card = d v := by
    rw [← hK]
    simp [Realization.neighborFinset, SimpleGraph.card_neighborFinset_eq_degree,
      K.degree_eq v]
  have hcard : S.card = T.card := hScard.trans hTcard.symm
  have hbalanced : (T \ S).card = (S \ T).card := Finset.card_sdiff_comm hcard.symm
  have hsdiff_card : (S \ T).card = 1 := by
    rw [Finset.symmDiff_def,
      Finset.card_union_of_disjoint
        (Finset.sdiff_disjoint.mono_right Finset.sdiff_subset)] at hST
    omega
  have hsdiff_card' : (T \ S).card = 1 := by omega
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hsdiff_card
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hsdiff_card'
  have hbST : b ∈ S \ T := hb.symm.subset (Finset.mem_singleton_self b)
  have haTS : a ∈ T \ S := ha.symm.subset (Finset.mem_singleton_self a)
  have hbS : b ∈ S := (Finset.mem_sdiff.mp hbST).1
  have hbT : b ∉ T := (Finset.mem_sdiff.mp hbST).2
  have haT : a ∈ T := (Finset.mem_sdiff.mp haTS).1
  have haS : a ∉ S := (Finset.mem_sdiff.mp haTS).2
  have hTform : T = insert a (S.erase b) := by
    ext z
    constructor
    · intro hzT
      by_cases hzS : z ∈ S
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨by
          rintro rfl
          exact hbT hzT, hzS⟩))
      · have hz : z ∈ T \ S := Finset.mem_sdiff.mpr ⟨hzT, hzS⟩
        have : z = a := by simpa [ha] using hz
        exact Finset.mem_insert.mpr (Or.inl this)
    · intro hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact haT
      · obtain ⟨hzb, hzS⟩ := Finset.mem_erase.mp hz
        by_contra hzT
        have hz' : z ∈ S \ T := Finset.mem_sdiff.mpr ⟨hzS, hzT⟩
        have : z = b := by simpa [hb] using hz'
        exact hzb this
  have hav : a ≠ v := by
    intro hav
    subst a
    have : v ∈ K.neighborFinset v := by simpa [hK] using haT
    exact (SimpleGraph.notMem_neighborFinset_self K.graph v) this
  have hbv : b ≠ v := by
    intro hbv
    subst b
    have : v ∈ G.neighborFinset v := by simpa [hG] using hbS
    exact (SimpleGraph.notMem_neighborFinset_self G.graph v) this
  have hTreal : HasRealizationWithNeighborSet d v (insert a (S.erase b)) := by
    rw [← hTform]
    exact ⟨K, hK⟩
  have hbad : bad.neighborFinset v = insert a (S.erase b) := by
    have hbadT' : bad.neighborFinset v = T := hbadT
    exact hbadT'.trans hTform
  have hTcardThreeF : 3 ≤ Fintype.card (Fibre d v T) :=
    card_ge_three_of_not_bip (A := fibreGraph d v T) hTnb
  have hTcardThree :
      3 ≤ Fintype.card (interfaceFibre d v (insert a (S.erase b))) := by
    rw [card_interfaceFibre_eq_fibre]
    simpa only [hTform] using hTcardThreeF
  by_cases hsmall : Fintype.card (interfaceFibre d v S) ≤ 2
  · have hkTwo := two_le_cross_degree_of_small_source
      (⟨G, hG⟩ : HasRealizationWithNeighborSet d v S) hTreal
      hbS haS hav hbv hsmall hTcardThree
    have htriangle : (interfaceFibreGraph d v S).CliqueFree 3 :=
      SimpleGraph.cliqueFree_of_card_lt (by omega)
    have hdegree := (theorem_5_7_cross_degree hbS haS
      (⟨G, hG⟩ : HasRealizationWithNeighborSet d v S) hTreal
      hav hbv htriangle).2
    obtain ⟨y, hyS, hyconn, hypath⟩ := ord v S T hST
      (⟨G, hG⟩ : HasRealizationWithNeighborSet d v S)
      (⟨K, hK⟩ : HasRealizationWithNeighborSet d v T) hMH x hx hxS
    have hycard := hdegree (⟨y, hyS⟩ : interfaceFibre d v S)
    have htwo : 1 < (sSideConnectorTargets y hyS hbS haS hav hbv).card := by
      rw [hycard]
      exact hkTwo
    obtain ⟨z, hz, hzbad⟩ := Finset.exists_mem_ne htwo bad
    obtain ⟨hzN, hyz⟩ := mem_sSideConnectorTargets_spec y hyS hbS haS hav hbv hz
    have hzT : z.neighborFinset v = T := by simpa [hTform] using hzN
    exact ⟨y, hyS, hyconn, hypath, z, hzT, hyz, hzbad⟩
  · have hsourceThree : 3 ≤ Fintype.card (interfaceFibre d v S) := by omega
    rcases hMH with hham | ⟨col, hproper, hsurj, hlace⟩
    · obtain ⟨y, z, hyS, hyx, hzN, hzbad, hyz⟩ :=
        exists_avoiding_connector_of_source_card_three
          (⟨G, hG⟩ : HasRealizationWithNeighborSet d v S)
          x hx bad hbad hbS haS hav hbv hsourceThree hTcardThree
      have hypath : HasHamPath (fibreGraph d v S) ⟨x, hxS⟩ ⟨y, hyS⟩ := by
        apply hham
        intro hxy
        exact hyx (congrArg Subtype.val hxy).symm
      have hzT : z.neighborFinset v = T := by simpa [hTform] using hzN
      exact ⟨y, hyS, ⟨z, hzT, hyz⟩, hypath, z, hzT, hyz, hzbad⟩
    · have hproper' : ∀ A B : interfaceFibre d v S,
          (interfaceFibreGraph d v S).Adj A B → col A ≠ col B := by
        intro A B hAB
        apply hproper A B
        exact hAB
      let xi : Fibre d v S := ⟨x, hxS⟩
      let C : Finset (interfaceFibre d v S) :=
        Finset.univ.filter fun y => col y = !(col xi)
      let D : Finset (Fibre d v S) :=
        Finset.univ.filter fun y => col y = !(col xi)
      have hCcol : ∀ y ∈ C, col y = !(col xi) := by
        intro y hy
        exact (Finset.mem_filter.mp hy).2
      have heven : Even (Fintype.card (Fibre d v S)) :=
        even_card_of_bip_laceable_surj (A := fibreGraph d v S) hproper hsurj hlace
      obtain ⟨opp, hopp⟩ := hsurj (!(col xi))
      have hxiopp : col xi ≠ col opp := by
        rw [hopp]
        exact Bool.self_ne_not _
      obtain ⟨p, hp⟩ := hlace xi opp hxiopp
      have hequitable : IsEquitableBipartite (fibreGraph d v S) col :=
        ⟨hproper, hamiltonian_even_equitable hp hproper heven⟩
      have hhalf := dpc_class_card hequitable (!(col xi))
      have hCcard : 2 ≤ C.card := by
        have hCD : C.card = D.card := by
          apply Finset.card_bij (fun y _ => (⟨y.1, y.2⟩ : Fibre d v S))
          · intro y hy
            simpa [C, D] using hy
          · intro y₁ _ y₂ _ heq
            exact Subtype.ext (congrArg Subtype.val heq)
          · intro y hy
            refine ⟨(⟨y.1, y.2⟩ : interfaceFibre d v S), ?_, ?_⟩
            · simpa [C, D] using hy
            · rfl
        have hhalf' : 2 * C.card = Fintype.card (Fibre d v S) := by
          calc
            2 * C.card = 2 * D.card := congrArg (2 * ·) hCD
            _ = Fintype.card (Fibre d v S) := by simpa [D] using hhalf
        have hsourceThreeF : 3 ≤ Fintype.card (Fibre d v S) := by
          rw [card_interfaceFibre_eq_fibre] at hsourceThree
          exact hsourceThree
        omega
      have hexpand := theorem_5_8_exact_color_expansion hbS haS
        (⟨G, hG⟩ : HasRealizationWithNeighborSet d v S)
        hTreal hav hbv col hproper' (!(col xi)) C hCcol
      have hNtwo : 1 < (connectorNeighborhood hbS haS hav hbv C).card := by
        rw [hexpand]
        have hkpos : 0 < max 1
            (residualDegree d v S ⟨a, hav⟩ - residualDegree d v S ⟨b, hbv⟩) := by
          omega
        exact lt_of_lt_of_le (by simpa using Nat.lt_of_succ_le hCcard)
          (Nat.mul_le_mul_right C.card hkpos)
      obtain ⟨z, hz, hzbad⟩ := Finset.exists_mem_ne hNtwo bad
      rw [connectorNeighborhood, Finset.mem_biUnion] at hz
      obtain ⟨yi, hyiC, hz⟩ := hz
      obtain ⟨hzN, hyz⟩ :=
        mem_sSideConnectorTargets_spec yi.1 yi.2 hbS haS hav hbv hz
      have hyiopp : col xi ≠ col yi := by
        rw [hCcol yi hyiC]
        exact Bool.self_ne_not _
      have hypath : HasHamPath (fibreGraph d v S) xi ⟨yi.1, yi.2⟩ :=
        hlace xi yi hyiopp
      have hzT : z.neighborFinset v = T := by simpa [hTform] using hzN
      exact ⟨yi.1, yi.2, ⟨z, hzT, hyz⟩, hypath, z, hzT, hyz, hzbad⟩

/-- The converse direction of the set-form Erdős–Gallai equality characterization used below. -/
private theorem sum_degree_eq_of_clique_saturated
    (G : SimpleGraph V) [DecidableRel G.Adj] {T : Finset V}
    (hclique : G.IsClique (T : Set V))
    (hsat : ∀ u ∈ Tᶜ,
      (G.neighborFinset u ∩ T).card = min (G.degree u) T.card) :
    ∑ u ∈ T, G.degree u =
      T.card * (T.card - 1) + ∑ u ∈ Tᶜ, min (G.degree u) T.card := by
  have hsplit (u : V) :
      G.degree u = (G.neighborFinset u ∩ T).card +
        (G.neighborFinset u ∩ Tᶜ).card := by
    rw [← G.card_neighborFinset_eq_degree]
    have hT : (G.neighborFinset u).filter (fun z => z ∈ T) =
        G.neighborFinset u ∩ T := Finset.filter_mem_eq_inter
    have hTc : (G.neighborFinset u).filter (fun z => z ∉ T) =
        G.neighborFinset u ∩ Tᶜ := by
      ext z
      simp
    rw [← hT, ← hTc]
    exact (Finset.card_filter_add_card_filter_not (s := G.neighborFinset u)
      (fun z => z ∈ T)).symm
  have hinter (u : V) (S : Finset V) :
      (G.neighborFinset u ∩ S).card =
        ∑ y ∈ S, if G.Adj u y then 1 else 0 := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
    congr 1
    ext y
    simp [SimpleGraph.mem_neighborFinset, and_comm]
  have hcross : (∑ u ∈ T, (G.neighborFinset u ∩ Tᶜ).card) =
      ∑ u ∈ Tᶜ, (G.neighborFinset u ∩ T).card := by
    calc
      (∑ u ∈ T, (G.neighborFinset u ∩ Tᶜ).card) =
          ∑ u ∈ T, ∑ y ∈ Tᶜ, if G.Adj u y then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro u hu
            exact hinter u Tᶜ
      _ = ∑ y ∈ Tᶜ, ∑ u ∈ T, if G.Adj u y then 1 else 0 := Finset.sum_comm
      _ = ∑ y ∈ Tᶜ, ∑ u ∈ T, if G.Adj y u then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        apply Finset.sum_congr rfl
        intro u hu
        simp only [G.adj_comm]
      _ = ∑ y ∈ Tᶜ, (G.neighborFinset y ∩ T).card := by
        apply Finset.sum_congr rfl
        intro y hy
        exact (hinter y T).symm
  have hinternal (u : V) (hu : u ∈ T) :
      (G.neighborFinset u ∩ T).card = T.card - 1 := by
    have heq : G.neighborFinset u ∩ T = T.erase u := by
      ext y
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_erase]
      constructor
      · rintro ⟨huy, hyT⟩
        exact ⟨fun h => G.irrefl (h ▸ huy), hyT⟩
      · rintro ⟨hyu, hyT⟩
        exact ⟨hclique hu hyT hyu.symm, hyT⟩
    rw [heq, Finset.card_erase_of_mem hu]
  have hconst : (∑ _u ∈ T, (T.card - 1)) = T.card * (T.card - 1) := by
    simp
  calc
    (∑ u ∈ T, G.degree u) = ∑ u ∈ T,
        ((G.neighborFinset u ∩ T).card +
          (G.neighborFinset u ∩ Tᶜ).card) := by
            apply Finset.sum_congr rfl
            intro u hu
            exact hsplit u
    _ = (∑ u ∈ T, (G.neighborFinset u ∩ T).card) +
        ∑ u ∈ T, (G.neighborFinset u ∩ Tᶜ).card := by
          rw [Finset.sum_add_distrib]
    _ = (∑ _u ∈ T, (T.card - 1)) +
        ∑ u ∈ Tᶜ, (G.neighborFinset u ∩ T).card := by
          congr 1
          · apply Finset.sum_congr rfl
            intro u hu
            exact hinternal u hu
    _ = T.card * (T.card - 1) + ∑ u ∈ Tᶜ,
        min (G.degree u) T.card := by
          rw [hconst]
          congr 1
          apply Finset.sum_congr rfl
          intro u hu
          exact hsat u hu

theorem tyshkevich_forced_in_every_realization {d : V → ℕ}
    (G₀ : Realization d) (A C : Finset V)
    (hAC : A ⊆ Cᶜ)
    (hAclique : G₀.graph.IsClique (A : Set V))
    (hBindep : ∀ u ∈ Cᶜ \ A, ∀ w ∈ Cᶜ \ A, ¬ G₀.graph.Adj u w)
    (hAcomplete : ∀ a ∈ A, ∀ c ∈ C, G₀.graph.Adj a c)
    (hBanticomplete : ∀ b ∈ Cᶜ \ A, ∀ c ∈ C, ¬ G₀.graph.Adj b c)
    (H : Realization d) :
    H.graph.IsClique (A : Set V) ∧
      (∀ u ∈ Cᶜ \ A, ∀ w ∈ Cᶜ \ A, ¬ H.graph.Adj u w) ∧
      (∀ a ∈ A, ∀ c ∈ C, H.graph.Adj a c) ∧
      (∀ b ∈ Cᶜ \ A, ∀ c ∈ C, ¬ H.graph.Adj b c) := by
  classical
  have hG₀sat : ∀ u ∈ Aᶜ,
      (G₀.graph.neighborFinset u ∩ A).card =
        min (G₀.graph.degree u) A.card := by
    intro u huA
    by_cases huC : u ∈ C
    · have hinter : G₀.graph.neighborFinset u ∩ A = A := by
        apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
        apply Finset.card_le_card
        intro a ha
        rw [Finset.mem_inter]
        exact ⟨by
          simpa only [SimpleGraph.mem_neighborFinset] using (hAcomplete a ha u huC).symm, ha⟩
      have hdeg : A.card ≤ G₀.graph.degree u := by
        rw [← G₀.graph.card_neighborFinset_eq_degree, ← hinter]
        exact Finset.card_le_card Finset.inter_subset_left
      rw [hinter, min_eq_right hdeg]
    · have huB : u ∈ Cᶜ \ A := by
        simp [huC, Finset.mem_compl.mp huA]
      have hsub : G₀.graph.neighborFinset u ⊆ A := by
        intro y hy
        have huy : G₀.graph.Adj u y := by
          simpa only [SimpleGraph.mem_neighborFinset] using hy
        by_contra hyA
        by_cases hyC : y ∈ C
        · exact hBanticomplete u huB y hyC huy
        · exact hBindep u huB y (by simp [hyC, hyA]) huy
      have hinter : G₀.graph.neighborFinset u ∩ A = G₀.graph.neighborFinset u :=
        Finset.inter_eq_left.mpr hsub
      have hdeg : G₀.graph.degree u ≤ A.card := by
        rw [← G₀.graph.card_neighborFinset_eq_degree]
        exact Finset.card_le_card hsub
      rw [hinter, G₀.graph.card_neighborFinset_eq_degree, min_eq_left hdeg]
  have hG₀eq := sum_degree_eq_of_clique_saturated G₀.graph hAclique hG₀sat
  have hHeq : ∑ u ∈ A, H.graph.degree u =
      A.card * (A.card - 1) + ∑ u ∈ Aᶜ, min (H.graph.degree u) A.card := by
    simpa only [G₀.degree_eq, H.degree_eq] using hG₀eq
  obtain ⟨hHclique, hHsat⟩ := isClique_of_sum_degree_eq H.graph hHeq
  have hCdeg (c : V) (hc : c ∈ C) : A.card ≤ d c := by
    rw [← G₀.degree_eq c, ← G₀.graph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro a ha
    simpa only [SimpleGraph.mem_neighborFinset] using (hAcomplete a ha c hc).symm
  have hBdeg (b : V) (hb : b ∈ Cᶜ \ A) : d b ≤ A.card := by
    rw [← G₀.degree_eq b, ← G₀.graph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro y hy
    have hby : G₀.graph.Adj b y := by
      simpa only [SimpleGraph.mem_neighborFinset] using hy
    by_contra hyA
    by_cases hyC : y ∈ C
    · exact hBanticomplete b hb y hyC hby
    · exact hBindep b hb y (by simp [hyC, hyA]) hby
  have hHcomplete : ∀ a ∈ A, ∀ c ∈ C, H.graph.Adj a c := by
    intro a ha c hc
    have hcAc : c ∈ Aᶜ := Finset.mem_compl.mpr fun hcA =>
      (Finset.mem_compl.mp (hAC hcA)) hc
    have hcard : (H.graph.neighborFinset c ∩ A).card = A.card := by
      rw [hHsat c (by simpa using hcAc), H.degree_eq c, min_eq_right (hCdeg c hc)]
    have hinter : H.graph.neighborFinset c ∩ A = A := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
      rw [hcard]
    have : a ∈ H.graph.neighborFinset c := by
      have : a ∈ H.graph.neighborFinset c ∩ A := by rw [hinter]; exact ha
      exact (Finset.mem_inter.mp this).1
    have hca : H.graph.Adj c a := by
      simpa only [SimpleGraph.mem_neighborFinset] using this
    exact hca.symm
  have hHneighborB : ∀ b ∈ Cᶜ \ A, H.graph.neighborFinset b ⊆ A := by
    intro b hb
    have hbAc : b ∈ Aᶜ := by
      exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hb).2
    have hcard : (H.graph.neighborFinset b ∩ A).card =
        (H.graph.neighborFinset b).card := by
      rw [hHsat b (by simpa using hbAc), H.degree_eq b,
        min_eq_left (hBdeg b hb), H.graph.card_neighborFinset_eq_degree, H.degree_eq b]
    have heq : H.graph.neighborFinset b ∩ A = H.graph.neighborFinset b := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      rw [hcard]
    exact Finset.inter_eq_left.mp heq
  refine ⟨hHclique, ?_, hHcomplete, ?_⟩
  · intro u hu w hw huw
    have hwA := hHneighborB u hu (by
      simpa only [SimpleGraph.mem_neighborFinset] using huw)
    exact (Finset.mem_sdiff.mp hw).2 hwA
  · intro b hb c hc hbc
    have hcA := hHneighborB b hb (by
      simpa only [SimpleGraph.mem_neighborFinset] using hbc)
    exact (Finset.mem_compl.mp (hAC hcA)) hc

/-! ## 4c. A concrete main-line witness -/

/-- The six labelled realizations of the degree sequence `(3,3,3,3,2)` on `Fin 5`.
Only explicit witnesses are used below; there is no enumeration of the type `Realization d`. -/
private def mainLineWitnessEdges : Fin 6 → Finset (Fin 5 × Fin 5)
  | 0 => {(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)}
  | 1 => {(0, 1), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3), (2, 4)}
  | 2 => {(0, 1), (0, 2), (0, 3), (1, 3), (1, 4), (2, 3), (2, 4)}
  | 3 => {(0, 1), (0, 2), (0, 4), (1, 2), (1, 3), (2, 3), (3, 4)}
  | 4 => {(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 3), (3, 4)}
  | 5 => {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 4), (3, 4)}

private def mainLineWitnessGraph (i : Fin 6) : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel fun u v => (u, v) ∈ mainLineWitnessEdges i

private def mainLineWitnessRealization (i : Fin 6) :
    Realization (![3, 3, 3, 3, 2] : Fin 5 → ℕ) where
  graph := mainLineWitnessGraph i
  adjDecidable := by
    unfold mainLineWitnessGraph
    infer_instance
  degree_eq := by
    fin_cases i <;> decide

private theorem mainLineWitness_edgeDiff_01 :
    (mainLineWitnessRealization 0).edgeFinset ∆
        (mainLineWitnessRealization 1).edgeFinset =
      {s(0, 2), s(1, 4), s(0, 1), s(2, 4)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      fin_cases u <;> fin_cases v <;>
        simp [Finset.mem_symmDiff, Realization.edgeFinset, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet, mainLineWitnessRealization, mainLineWitnessGraph,
          mainLineWitnessEdges]

private theorem mainLineWitness_edgeDiff_02 :
    (mainLineWitnessRealization 0).edgeFinset ∆
        (mainLineWitnessRealization 2).edgeFinset =
      {s(0, 4), s(1, 2), s(0, 1), s(2, 4)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      fin_cases u <;> fin_cases v <;>
        simp [Finset.mem_symmDiff, Realization.edgeFinset, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet, mainLineWitnessRealization, mainLineWitnessGraph,
          mainLineWitnessEdges]

private theorem mainLineWitness_edgeDiff_12 :
    (mainLineWitnessRealization 1).edgeFinset ∆
        (mainLineWitnessRealization 2).edgeFinset =
      {s(0, 4), s(1, 2), s(0, 2), s(1, 4)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      fin_cases u <;> fin_cases v <;>
        simp [Finset.mem_symmDiff, Realization.edgeFinset, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet, mainLineWitnessRealization, mainLineWitnessGraph,
          mainLineWitnessEdges]

/-- Every cell varies among the six explicit realizations. This is the structural certificate used
both for activity and to rule out a Tyshkevich split. -/
private theorem mainLineWitness_cell_varies (u v : Fin 5) (huv : u ≠ v) :
    ∃ i j : Fin 6, (mainLineWitnessRealization i).graph.Adj u v ∧
      ¬ (mainLineWitnessRealization j).graph.Adj u v := by
  fin_cases u <;> fin_cases v <;> simp_all <;> decide

private theorem mainLineWitness_active : Active (![3, 3, 3, 3, 2] : Fin 5 → ℕ) := by
  intro u
  let v : Fin 5 := if u = 0 then 1 else 0
  have huv : u ≠ v := by
    fin_cases u <;> decide
  obtain ⟨i, j, hi, hj⟩ := mainLineWitness_cell_varies u v huv
  have hne : (mainLineWitnessRealization i).neighborFinset u ≠
      (mainLineWitnessRealization j).neighborFinset u := by
    intro hsame
    have hv_i : v ∈ (mainLineWitnessRealization i).neighborFinset u :=
      (mainLineWitnessRealization i).mem_neighborFinset u v |>.mpr hi
    have hv_j : v ∈ (mainLineWitnessRealization j).neighborFinset u := by
      rw [← hsame]
      exact hv_i
    exact hj ((mainLineWitnessRealization j).mem_neighborFinset u v |>.mp hv_j)
  exact ⟨(mainLineWitnessRealization i).neighborFinset u,
    (mainLineWitnessRealization j).neighborFinset u, hne,
    ⟨mainLineWitnessRealization i, rfl⟩, ⟨mainLineWitnessRealization j, rfl⟩⟩

private theorem mainLineWitness_nonbipartite :
    ¬ (RealizationGraph (![3, 3, 3, 3, 2] : Fin 5 → ℕ)).Colorable 2 := by
  have h01 : (RealizationGraph (![3, 3, 3, 3, 2] : Fin 5 → ℕ)).Adj
      (mainLineWitnessRealization 0) (mainLineWitnessRealization 1) := by
    change ((mainLineWitnessRealization 0).edgeFinset ∆
      (mainLineWitnessRealization 1).edgeFinset).card = 4
    rw [mainLineWitness_edgeDiff_01]
    decide
  have h02 : (RealizationGraph (![3, 3, 3, 3, 2] : Fin 5 → ℕ)).Adj
      (mainLineWitnessRealization 0) (mainLineWitnessRealization 2) := by
    change ((mainLineWitnessRealization 0).edgeFinset ∆
      (mainLineWitnessRealization 2).edgeFinset).card = 4
    rw [mainLineWitness_edgeDiff_02]
    decide
  have h12 : (RealizationGraph (![3, 3, 3, 3, 2] : Fin 5 → ℕ)).Adj
      (mainLineWitnessRealization 1) (mainLineWitnessRealization 2) := by
    change ((mainLineWitnessRealization 1).edgeFinset ∆
      (mainLineWitnessRealization 2).edgeFinset).card = 4
    rw [mainLineWitness_edgeDiff_12]
    decide
  intro hcolor
  have hpair : Pairwise fun i j : Fin 3 =>
      (RealizationGraph (![3, 3, 3, 3, 2] : Fin 5 → ℕ)).Adj
        (![mainLineWitnessRealization 0, mainLineWitnessRealization 1,
          mainLineWitnessRealization 2] i)
        (![mainLineWitnessRealization 0, mainLineWitnessRealization 1,
          mainLineWitnessRealization 2] j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [SimpleGraph.adj_comm]
  have hle : Nat.card (Fin 3) ≤ 2 := hcolor.card_le_of_pairwise_adj
    (fun i : Fin 3 =>
      ![mainLineWitnessRealization 0, mainLineWitnessRealization 1,
        mainLineWitnessRealization 2] i) hpair
  norm_num at hle

private theorem mainLineWitness_realization_ne_of_adj_not_adj {i j : Fin 6} {u v : Fin 5}
    (hi : (mainLineWitnessRealization i).graph.Adj u v)
    (hj : ¬ (mainLineWitnessRealization j).graph.Adj u v) :
    mainLineWitnessRealization i ≠ mainLineWitnessRealization j := by
  intro h
  have hgraph : (mainLineWitnessRealization i).graph =
      (mainLineWitnessRealization j).graph := congrArg Realization.graph h
  apply hj
  rw [← hgraph]
  exact hi

private theorem mainLineWitness_notK3 :
    NotK3Base (![3, 3, 3, 3, 2] : Fin 5 → ℕ) := by
  rintro ⟨A, B, C, hAB, hBC, hAC, hcover⟩
  have h01 : mainLineWitnessRealization 0 ≠ mainLineWitnessRealization 1 :=
    mainLineWitness_realization_ne_of_adj_not_adj
      (u := 0) (v := 2) (by decide) (by decide)
  have h02 : mainLineWitnessRealization 0 ≠ mainLineWitnessRealization 2 :=
    mainLineWitness_realization_ne_of_adj_not_adj
      (u := 0) (v := 4) (by decide) (by decide)
  have h03 : mainLineWitnessRealization 0 ≠ mainLineWitnessRealization 3 :=
    mainLineWitness_realization_ne_of_adj_not_adj
      (u := 0) (v := 3) (by decide) (by decide)
  have h12 : mainLineWitnessRealization 1 ≠ mainLineWitnessRealization 2 :=
    mainLineWitness_realization_ne_of_adj_not_adj
      (u := 0) (v := 4) (by decide) (by decide)
  have h13 : mainLineWitnessRealization 1 ≠ mainLineWitnessRealization 3 :=
    mainLineWitness_realization_ne_of_adj_not_adj
      (u := 0) (v := 3) (by decide) (by decide)
  have h23 : mainLineWitnessRealization 2 ≠ mainLineWitnessRealization 3 :=
    mainLineWitness_realization_ne_of_adj_not_adj
      (u := 0) (v := 3) (by decide) (by decide)
  let four : Finset (Realization (![3, 3, 3, 3, 2] : Fin 5 → ℕ)) :=
    {mainLineWitnessRealization 0, mainLineWitnessRealization 1,
      mainLineWitnessRealization 2, mainLineWitnessRealization 3}
  let three : Finset (Realization (![3, 3, 3, 3, 2] : Fin 5 → ℕ)) := {A, B, C}
  have hfour : four.card = 4 := by
    simp [four, h01, h02, h03, h12, h13, h23]
  have hthree : three.card = 3 := by
    simp [three, hAB, hBC, hAC]
  have hsub : four ⊆ three := by
    intro G hG
    simp only [four, Finset.mem_insert, Finset.mem_singleton] at hG
    simp only [three, Finset.mem_insert, Finset.mem_singleton]
    rcases hG with rfl | rfl | rfl | rfl
    · exact hcover (mainLineWitnessRealization 0)
    · exact hcover (mainLineWitnessRealization 1)
    · exact hcover (mainLineWitnessRealization 2)
    · exact hcover (mainLineWitnessRealization 3)
  have := Finset.card_le_card hsub
  rw [hfour, hthree] at this
  omega

private theorem mainLineWitness_indecomposable :
    ¬ TyshkevichDecomposable (![3, 3, 3, 3, 2] : Fin 5 → ℕ) := by
  rintro ⟨G, A, C, hC, hCc, hAC, hAclique, hBindep, hAcomplete, hBanticomplete⟩
  obtain ⟨c, hc⟩ := hC
  obtain ⟨x, hx⟩ := hCc
  have hxc : x ≠ c := by
    intro h
    subst x
    exact (Finset.mem_compl.mp hx) hc
  obtain ⟨i, j, hi, hj⟩ := mainLineWitness_cell_varies x c hxc
  have hforced_i := tyshkevich_forced_in_every_realization G A C hAC hAclique hBindep
    hAcomplete hBanticomplete (mainLineWitnessRealization i)
  have hforced_j := tyshkevich_forced_in_every_realization G A C hAC hAclique hBindep
    hAcomplete hBanticomplete (mainLineWitnessRealization j)
  by_cases hxA : x ∈ A
  · exact hj (hforced_j.2.2.1 x hxA c hc)
  · have hxB : x ∈ Cᶜ \ A := Finset.mem_sdiff.mpr ⟨hx, hxA⟩
    exact (hforced_i.2.2.2 x hxB c hc) hi

/-- The one-pass main-line hypotheses are jointly satisfiable. -/
theorem mainLine_witness : MainLine (![3, 3, 3, 3, 2] : Fin 5 → ℕ) where
  indecomposable := mainLineWitness_indecomposable
  nonbipartite := mainLineWitness_nonbipartite
  notK3 := mainLineWitness_notK3

/-! ## Anti-vacuity for the exceptional branch of `sbPlus`

`mainLine_witness` shows `MainLine` is inhabited, and that is NOT enough for `sbPlus`: an adversary
pass on 2026-08-24 observed that `![3,3,3,3,2]` **provably cannot** exercise `sbPlus`'s exceptional
branch, since `yFamilyPivot_degreeClass_card` forces the pivot's degree class to have exactly three
members and that sequence's classes have four and one. If `MainLine d ∧ YFamilyPivot d v` were
unsatisfiable, `sbPlus` would be `separator_buffer` with dead code, its docstring's "strictly stronger
than `separator_buffer`" would be false, and no gate here would notice.

This block closes that. `d = ![3,2,2,2,1]` has six realizations; the pivot `1` has exactly four
realizable neighbourhoods, `{0,2}` and `{0,3}` adjacent to everything and `{0,4}`, `{2,3}` at
symmetric difference four, so the quotient is `K₂ ∨ (K₁ ⊔ K₁)` — a clique-sum.

The characterization is where the work is, and it cannot be `decide`d: `realizableNeighborhoods` is
NONCOMPUTABLE, built through `Classical.decPred`. Cardinality and non-self-membership cut the
candidates to six; `yfw_no_four` kills the two survivors by an elementary argument — vertex `0` has
degree three and is not a neighbour of the pivot, so it takes all of `{2,3,4}`, which would give
vertex `4` two neighbours where it has one. Once the candidate set is pinned the rest IS decidable.

Recorded in `results/2026-08-24c_adversary_pass_sections_5_9.md`. -/

def yfwD : Fin 5 → ℕ := ![3, 2, 2, 2, 1]

/-- Four realizations of `yfwD`, one per realizable neighbourhood of the pivot `1`. -/
def yfwEdges : Fin 6 → Finset (Fin 5 × Fin 5)
  | 0 => {(0, 2), (0, 3), (0, 4), (1, 2), (1, 3)}
  | 1 => {(0, 1), (0, 3), (0, 4), (1, 2), (2, 3)}
  | 2 => {(0, 1), (0, 2), (0, 4), (1, 3), (2, 3)}
  | 3 => {(0, 1), (0, 2), (0, 3), (1, 4), (2, 3)}
  | 4 => {(0, 1), (0, 2), (0, 3), (1, 3), (2, 4)}
  | 5 => {(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)}

def yfwGraph (i : Fin 6) : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel fun u v => (u, v) ∈ yfwEdges i

def yfwRealization (i : Fin 6) : Realization yfwD where
  graph := yfwGraph i
  adjDecidable := by unfold yfwGraph; infer_instance
  degree_eq := by fin_cases i <;> decide

/-- The four neighbourhoods, in the order the realizations produce them. -/
def yfwN : Fin 4 → Finset (Fin 5)
  | 0 => {0, 2}
  | 1 => {0, 3}
  | 2 => {0, 4}
  | 3 => {2, 3}

/-- Which realization exhibits which neighbourhood: `{0,2}`, `{0,3}`, `{0,4}`, `{2,3}` come from
realizations 1, 2, 3, 0 respectively. -/
def yfwSrc : Fin 4 → Fin 6
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 0

theorem yfw_neighborFinset (i : Fin 4) :
    (yfwRealization (yfwSrc i)).neighborFinset 1 = yfwN i := by
  fin_cases i <;> decide

/-- The pivot's neighbourhood cannot contain `4`: vertex `0` has degree three and, not being a
neighbour of the pivot, must take all of `{2,3,4}`, which would give `4` two neighbours where it
has one. -/
theorem yfw_no_four {G : Realization yfwD} (h4 : G.graph.Adj 1 4) (h0 : ¬ G.graph.Adj 1 0) :
    False := by
  classical
  letI := G.adjDecidable
  have hd0 : G.graph.degree 0 = 3 := by simpa [yfwD] using G.degree_eq 0
  have hsub : G.neighborFinset 0 ⊆ ({2, 3, 4} : Finset (Fin 5)) := by
    intro x hx
    rw [Realization.mem_neighborFinset] at hx
    have hx0 : x ≠ 0 := hx.ne'
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact h0 hx.symm
    fin_cases x <;> simp_all
  have hcard : (G.neighborFinset 0).card = 3 := by
    simpa [Realization.neighborFinset, SimpleGraph.card_neighborFinset_eq_degree] using hd0
  have heq : G.neighborFinset 0 = ({2, 3, 4} : Finset (Fin 5)) :=
    Finset.eq_of_subset_of_card_le hsub (by simp [hcard])
  have h04 : G.graph.Adj 0 4 := by
    have hmem : (4 : Fin 5) ∈ G.neighborFinset 0 := by rw [heq]; decide
    rwa [Realization.mem_neighborFinset] at hmem
  have hd4 : G.graph.degree 4 = 1 := by simpa [yfwD] using G.degree_eq 4
  have hm0 : (0 : Fin 5) ∈ G.neighborFinset 4 := by
    rw [Realization.mem_neighborFinset]; exact h04.symm
  have hm1 : (1 : Fin 5) ∈ G.neighborFinset 4 := by
    rw [Realization.mem_neighborFinset]; exact h4.symm
  have hsub2 : ({0, 1} : Finset (Fin 5)) ⊆ G.neighborFinset 4 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hm0
    · exact hm1
  have hle : (2 : ℕ) ≤ (G.neighborFinset 4).card := by
    have hc := Finset.card_le_card hsub2
    simpa using hc
  rw [show (G.neighborFinset 4).card = G.graph.degree 4 by
    simp [Realization.neighborFinset, SimpleGraph.card_neighborFinset_eq_degree], hd4] at hle
  omega

/-- **The realizable neighbourhoods of the pivot are exactly the four.** The forward direction is
where the work is: cardinality and non-self-membership cut the candidates to six, and `yfw_no_four`
kills the two that remain. -/
theorem yfw_realizable_iff {S : Finset (Fin 5)} :
    HasRealizationWithNeighborSet yfwD 1 S ↔
      S = yfwN 0 ∨ S = yfwN 1 ∨ S = yfwN 2 ∨ S = yfwN 3 := by
  classical
  constructor
  · rintro ⟨G, hG⟩
    letI := G.adjDecidable
    have hd1 : G.graph.degree 1 = 2 := by simpa [yfwD] using G.degree_eq 1
    have hcard : S.card = 2 := by
      rw [← hG]
      simpa [Realization.neighborFinset, SimpleGraph.card_neighborFinset_eq_degree] using hd1
    have h1 : (1 : Fin 5) ∉ S := by
      rw [← hG, Realization.mem_neighborFinset]
      exact fun h => (SimpleGraph.irrefl G.graph) h
    have h40 : (4 : Fin 5) ∈ S → (0 : Fin 5) ∈ S := by
      intro h4
      by_contra h0
      rw [← hG, Realization.mem_neighborFinset] at h4
      rw [← hG, Realization.mem_neighborFinset] at h0
      exact yfw_no_four h4 h0
    clear hG hd1
    revert hcard h1 h40
    revert S
    decide
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨_, yfw_neighborFinset 0⟩, ⟨_, yfw_neighborFinset 1⟩,
            ⟨_, yfw_neighborFinset 2⟩, ⟨_, yfw_neighborFinset 3⟩]

/-- Every quotient vertex is one of the four. -/
theorem yfw_quotient_cases (X : QuotientV yfwD 1) :
    X.val = yfwN 0 ∨ X.val = yfwN 1 ∨ X.val = yfwN 2 ∨ X.val = yfwN 3 :=
  yfw_realizable_iff.mp X.property

def yfwQ (i : Fin 4) : QuotientV yfwD 1 :=
  ⟨yfwN i, yfw_realizable_iff.mpr (by fin_cases i <;> simp)⟩

/-- **The exceptional branch of `sbPlus` is inhabited.** The quotient at the pivot is a clique-sum:
`{0,2}` and `{0,3}` are adjacent to everything, and the two remaining neighbourhoods `{0,4}` and
`{2,3}` sit at symmetric difference four, hence non-adjacent. So the quotient is `K₂ ∨ (K₁ ⊔ K₁)`. -/
theorem yfwPivot_witness : YFamilyPivot yfwD 1 := by
  classical
  refine ⟨yfwQ 0, yfwQ 1, ?_, ?_, ?_, fun X => decide (X.val = yfwN 2), ?_, ?_, ?_⟩
  · intro h; exact absurd (congrArg Subtype.val h) (by decide)
  · intro X hX
    have hne : X.val ≠ yfwN 0 := fun h => hX (Subtype.ext h)
    refine (SimpleGraph.fromRel_adj _ _ _).mpr
      ⟨fun hc => hX (Subtype.ext (congrArg Subtype.val hc).symm), ?_⟩
    rcases yfw_quotient_cases X with h | h | h | h
    · exact absurd h hne
    all_goals (left; rw [h]; decide)
  · intro X hX
    have hne : X.val ≠ yfwN 1 := fun h => hX (Subtype.ext h)
    refine (SimpleGraph.fromRel_adj _ _ _).mpr
      ⟨fun hc => hX (Subtype.ext (congrArg Subtype.val hc).symm), ?_⟩
    rcases yfw_quotient_cases X with h | h | h | h
    · left; rw [h]; decide
    · exact absurd h hne
    all_goals (left; rw [h]; decide)
  · exact ⟨yfwQ 2, fun h => absurd (congrArg Subtype.val h) (by decide),
           fun h => absurd (congrArg Subtype.val h) (by decide), by decide⟩
  · exact ⟨yfwQ 3, fun h => absurd (congrArg Subtype.val h) (by decide),
           fun h => absurd (congrArg Subtype.val h) (by decide), by decide⟩
  · intro a b ha0 ha1 hb0 hb1 hab
    have hav : a.val = yfwN 2 ∨ a.val = yfwN 3 := by
      rcases yfw_quotient_cases a with h | h | h | h
      · exact absurd (Subtype.ext h) ha0
      · exact absurd (Subtype.ext h) ha1
      · exact Or.inl h
      · exact Or.inr h
    have hbv : b.val = yfwN 2 ∨ b.val = yfwN 3 := by
      rcases yfw_quotient_cases b with h | h | h | h
      · exact absurd (Subtype.ext h) hb0
      · exact absurd (Subtype.ext h) hb1
      · exact Or.inl h
      · exact Or.inr h
    have hne : a.val ≠ b.val := fun h => hab (Subtype.ext h)
    constructor
    · intro hAdj
      exfalso
      rw [quotientGraph, SimpleGraph.fromRel_adj] at hAdj
      rcases hav with ha | ha <;> rcases hbv with hb | hb <;>
        first
          | exact hne (ha.trans hb.symm)
          | (rw [ha, hb] at hAdj; exact absurd hAdj.2 (by decide))
    · intro hside
      exfalso
      rcases hav with ha | ha <;> rcases hbv with hb | hb <;>
        first
          | exact hne (ha.trans hb.symm)
          | (simp only [ha, hb] at hside; exact absurd hside (by decide))

/-! ### The other half: `MainLine` at the same degree function -/

theorem yfw_cell_varies (u v : Fin 5) (huv : u ≠ v) :
    ∃ i j : Fin 6, (yfwRealization i).graph.Adj u v ∧ ¬ (yfwRealization j).graph.Adj u v := by
  fin_cases u <;> fin_cases v <;> simp_all <;> decide

theorem yfw_active : Active yfwD := by
  intro u
  let v : Fin 5 := if u = 0 then 1 else 0
  have huv : u ≠ v := by fin_cases u <;> decide
  obtain ⟨i, j, hi, hj⟩ := yfw_cell_varies u v huv
  have hne : (yfwRealization i).neighborFinset u ≠ (yfwRealization j).neighborFinset u := by
    intro hsame
    have hv_i : v ∈ (yfwRealization i).neighborFinset u :=
      (yfwRealization i).mem_neighborFinset u v |>.mpr hi
    have hv_j : v ∈ (yfwRealization j).neighborFinset u := by rw [← hsame]; exact hv_i
    exact hj ((yfwRealization j).mem_neighborFinset u v |>.mp hv_j)
  exact ⟨(yfwRealization i).neighborFinset u, (yfwRealization j).neighborFinset u, hne,
    ⟨yfwRealization i, rfl⟩, ⟨yfwRealization j, rfl⟩⟩

theorem yfw_edgeDiff_01 :
    (yfwRealization 0).edgeFinset ∆ (yfwRealization 1).edgeFinset =
      {s(0, 2), s(1, 3), s(0, 1), s(2, 3)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      fin_cases u <;> fin_cases v <;>
        simp [Finset.mem_symmDiff, Realization.edgeFinset, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet, yfwRealization, yfwGraph, yfwEdges]

theorem yfw_edgeDiff_02 :
    (yfwRealization 0).edgeFinset ∆ (yfwRealization 2).edgeFinset =
      {s(0, 3), s(1, 2), s(0, 1), s(2, 3)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      fin_cases u <;> fin_cases v <;>
        simp [Finset.mem_symmDiff, Realization.edgeFinset, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet, yfwRealization, yfwGraph, yfwEdges]

theorem yfw_edgeDiff_12 :
    (yfwRealization 1).edgeFinset ∆ (yfwRealization 2).edgeFinset =
      {s(0, 3), s(1, 2), s(0, 2), s(1, 3)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      fin_cases u <;> fin_cases v <;>
        simp [Finset.mem_symmDiff, Realization.edgeFinset, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet, yfwRealization, yfwGraph, yfwEdges]

theorem yfw_nonbipartite : ¬ (RealizationGraph yfwD).Colorable 2 := by
  have h01 : (RealizationGraph yfwD).Adj (yfwRealization 0) (yfwRealization 1) := by
    change ((yfwRealization 0).edgeFinset ∆ (yfwRealization 1).edgeFinset).card = 4
    rw [yfw_edgeDiff_01]; decide
  have h02 : (RealizationGraph yfwD).Adj (yfwRealization 0) (yfwRealization 2) := by
    change ((yfwRealization 0).edgeFinset ∆ (yfwRealization 2).edgeFinset).card = 4
    rw [yfw_edgeDiff_02]; decide
  have h12 : (RealizationGraph yfwD).Adj (yfwRealization 1) (yfwRealization 2) := by
    change ((yfwRealization 1).edgeFinset ∆ (yfwRealization 2).edgeFinset).card = 4
    rw [yfw_edgeDiff_12]; decide
  intro hcolor
  have hpair : Pairwise fun i j : Fin 3 =>
      (RealizationGraph yfwD).Adj
        (![yfwRealization 0, yfwRealization 1, yfwRealization 2] i)
        (![yfwRealization 0, yfwRealization 1, yfwRealization 2] j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [SimpleGraph.adj_comm]
  have hle : Nat.card (Fin 3) ≤ 2 := hcolor.card_le_of_pairwise_adj
    (fun i : Fin 3 => ![yfwRealization 0, yfwRealization 1, yfwRealization 2] i) hpair
  norm_num at hle

theorem yfw_ne_of_adj_not_adj {i j : Fin 6} {u v : Fin 5}
    (hi : (yfwRealization i).graph.Adj u v) (hj : ¬ (yfwRealization j).graph.Adj u v) :
    yfwRealization i ≠ yfwRealization j := by
  intro h
  exact hj ((congrArg Realization.graph h) ▸ hi)

theorem yfw_notK3 : NotK3Base yfwD := by
  rintro ⟨A, B, C, hAB, hBC, hAC, hcover⟩
  have h01 : yfwRealization 0 ≠ yfwRealization 1 :=
    yfw_ne_of_adj_not_adj (u := 0) (v := 2) (by decide) (by decide)
  have h02 : yfwRealization 0 ≠ yfwRealization 2 :=
    yfw_ne_of_adj_not_adj (u := 0) (v := 3) (by decide) (by decide)
  have h03 : yfwRealization 0 ≠ yfwRealization 3 :=
    yfw_ne_of_adj_not_adj (u := 0) (v := 4) (by decide) (by decide)
  have h12 : yfwRealization 1 ≠ yfwRealization 2 :=
    yfw_ne_of_adj_not_adj (u := 0) (v := 3) (by decide) (by decide)
  have h13 : yfwRealization 1 ≠ yfwRealization 3 :=
    yfw_ne_of_adj_not_adj (u := 0) (v := 4) (by decide) (by decide)
  have h23 : yfwRealization 2 ≠ yfwRealization 3 :=
    yfw_ne_of_adj_not_adj (u := 0) (v := 4) (by decide) (by decide)
  let four : Finset (Realization yfwD) :=
    {yfwRealization 0, yfwRealization 1, yfwRealization 2, yfwRealization 3}
  let three : Finset (Realization yfwD) := {A, B, C}
  have hfour : four.card = 4 := by simp [four, h01, h02, h03, h12, h13, h23]
  have hthree : three.card = 3 := by simp [three, hAB, hBC, hAC]
  have hsub : four ⊆ three := by
    intro G hG
    simp only [four, Finset.mem_insert, Finset.mem_singleton] at hG
    simp only [three, Finset.mem_insert, Finset.mem_singleton]
    rcases hG with rfl | rfl | rfl | rfl
    exacts [hcover _, hcover _, hcover _, hcover _]
  have hcard := Finset.card_le_card hsub
  rw [hfour, hthree] at hcard
  omega

theorem yfw_indecomposable : ¬ TyshkevichDecomposable yfwD := by
  rintro ⟨G, A, C, hC, hCc, hAC, hAclique, hBindep, hAcomplete, hBanticomplete⟩
  obtain ⟨c, hc⟩ := hC
  obtain ⟨x, hx⟩ := hCc
  have hxc : x ≠ c := by
    intro h; subst x; exact (Finset.mem_compl.mp hx) hc
  obtain ⟨i, j, hi, hj⟩ := yfw_cell_varies x c hxc
  have hforced_i := tyshkevich_forced_in_every_realization G A C hAC hAclique hBindep
    hAcomplete hBanticomplete (yfwRealization i)
  have hforced_j := tyshkevich_forced_in_every_realization G A C hAC hAclique hBindep
    hAcomplete hBanticomplete (yfwRealization j)
  by_cases hxA : x ∈ A
  · exact hj (hforced_j.2.2.1 x hxA c hc)
  · have hxB : x ∈ Cᶜ \ A := Finset.mem_sdiff.mpr ⟨hx, hxA⟩
    exact (hforced_i.2.2.2 x hxB c hc) hi

/-- **The exceptional branch is inhabited on the main line.** -/
theorem yfw_mainLine : MainLine yfwD where
  indecomposable := yfw_indecomposable
  nonbipartite := yfw_nonbipartite
  notK3 := yfw_notK3

/-- The residual degree function on the split factor of a Tyshkevich composition. -/
def tyshkevichLeftDegree (d : V → ℕ) (A C : Finset V) :
    {x : V // x ∉ C} → ℕ :=
  fun v => d v.1 - if v.1 ∈ A then C.card else 0

/-- The degree function on the ordinary factor of a Tyshkevich composition. -/
def tyshkevichRightDegree (d : V → ℕ) (A C : Finset V) :
    {x : V // x ∈ C} → ℕ :=
  fun c => d c.1 - A.card

noncomputable def tyshkevichLeftRestriction {d : V → ℕ}
    (A C : Finset V) (H : Realization d)
    (hcomplete : ∀ a ∈ A, ∀ c ∈ C, H.graph.Adj a c)
    (hanticomplete : ∀ b ∈ Cᶜ \ A, ∀ c ∈ C, ¬ H.graph.Adj b c) :
    Realization (tyshkevichLeftDegree d A C) := by
  classical
  let K : SimpleGraph {x : V // x ∉ C} := H.graph.comap Subtype.val
  let hdec : DecidableRel K.Adj := inferInstance
  letI := hdec
  have hdegree (v : {x : V // x ∉ C}) :
      K.degree v = tyshkevichLeftDegree d A C v := by
    have hinduce : K.degree v = (H.graph.neighborFinset v.1 ∩ Cᶜ).card := by
      let e : {x : V // x ∉ C} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
      calc
        K.degree v = (K.neighborFinset v).card := (K.card_neighborFinset_eq_degree v).symm
        _ = ((K.neighborFinset v).map e).card := (Finset.card_map e).symm
        _ = (H.graph.neighborFinset v.1 ∩ Cᶜ).card := by
          congr 1
          ext x
          simp [e, K, SimpleGraph.mem_neighborFinset]
    have hsplit : H.graph.degree v.1 =
        (H.graph.neighborFinset v.1 ∩ Cᶜ).card +
          (H.graph.neighborFinset v.1 ∩ C).card := by
      rw [← H.graph.card_neighborFinset_eq_degree]
      have hC : (H.graph.neighborFinset v.1).filter (fun z => z ∈ C) =
          H.graph.neighborFinset v.1 ∩ C := Finset.filter_mem_eq_inter
      have hCc : (H.graph.neighborFinset v.1).filter (fun z => z ∉ C) =
          H.graph.neighborFinset v.1 ∩ Cᶜ := by ext z; simp
      rw [← hC, ← hCc, Nat.add_comm]
      exact (Finset.card_filter_add_card_filter_not
        (s := H.graph.neighborFinset v.1) (fun z => z ∈ C)).symm
    by_cases hvA : v.1 ∈ A
    · have hinter : H.graph.neighborFinset v.1 ∩ C = C := by
        apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
        apply Finset.card_le_card
        intro c hc
        rw [Finset.mem_inter]
        exact ⟨by
          simpa only [SimpleGraph.mem_neighborFinset] using hcomplete v.1 hvA c hc, hc⟩
      simp only [tyshkevichLeftDegree, hvA, if_true]
      rw [hinter, H.degree_eq v.1] at hsplit
      rw [hinduce]
      omega
    · have hvB : v.1 ∈ Cᶜ \ A := by simp [v.2, hvA]
      have hinter : H.graph.neighborFinset v.1 ∩ C = ∅ := by
        apply Finset.Subset.antisymm
        · intro c hc
          have hvc : H.graph.Adj v.1 c := by
            simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hc).1
          exact (hanticomplete v.1 hvB c (Finset.mem_inter.mp hc).2 hvc).elim
        · exact Finset.empty_subset _
      simp only [tyshkevichLeftDegree, hvA, if_false, Nat.sub_zero]
      rw [hinter, Finset.card_empty, Nat.add_zero, H.degree_eq v.1] at hsplit
      rw [hinduce]
      exact hsplit.symm
  exact
    { graph := K
      adjDecidable := hdec
      degree_eq := hdegree }

noncomputable def tyshkevichRightRestriction {d : V → ℕ}
    (A C : Finset V) (H : Realization d)
    (hAC : A ⊆ Cᶜ)
    (hcomplete : ∀ a ∈ A, ∀ c ∈ C, H.graph.Adj a c)
    (hanticomplete : ∀ b ∈ Cᶜ \ A, ∀ c ∈ C, ¬ H.graph.Adj b c) :
    Realization (tyshkevichRightDegree d A C) := by
  classical
  let K : SimpleGraph {x : V // x ∈ C} := H.graph.comap Subtype.val
  let hdec : DecidableRel K.Adj := inferInstance
  letI := hdec
  have hdegree (c : {x : V // x ∈ C}) :
      K.degree c = tyshkevichRightDegree d A C c := by
    have hinduce : K.degree c = (H.graph.neighborFinset c.1 ∩ C).card := by
      let e : {x : V // x ∈ C} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
      calc
        K.degree c = (K.neighborFinset c).card := (K.card_neighborFinset_eq_degree c).symm
        _ = ((K.neighborFinset c).map e).card := (Finset.card_map e).symm
        _ = (H.graph.neighborFinset c.1 ∩ C).card := by
          congr 1
          ext x
          simp [e, K, SimpleGraph.mem_neighborFinset]
    have hsplit : H.graph.degree c.1 =
        (H.graph.neighborFinset c.1 ∩ C).card +
          (H.graph.neighborFinset c.1 ∩ Cᶜ).card := by
      rw [← H.graph.card_neighborFinset_eq_degree]
      have hC : (H.graph.neighborFinset c.1).filter (fun z => z ∈ C) =
          H.graph.neighborFinset c.1 ∩ C := Finset.filter_mem_eq_inter
      have hCc : (H.graph.neighborFinset c.1).filter (fun z => z ∉ C) =
          H.graph.neighborFinset c.1 ∩ Cᶜ := by ext z; simp
      rw [← hC, ← hCc]
      exact (Finset.card_filter_add_card_filter_not
        (s := H.graph.neighborFinset c.1) (fun z => z ∈ C)).symm
    have hinter : H.graph.neighborFinset c.1 ∩ Cᶜ = A := by
      apply Finset.Subset.antisymm
      · intro x hx
        have hxc : x ∈ Cᶜ := (Finset.mem_inter.mp hx).2
        by_contra hxA
        have hxB : x ∈ Cᶜ \ A := Finset.mem_sdiff.mpr ⟨hxc, hxA⟩
        have hcx : H.graph.Adj c.1 x := by
          simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hx).1
        exact hanticomplete x hxB c.1 c.2 hcx.symm
      · intro a ha
        rw [Finset.mem_inter]
        exact ⟨by
          simpa only [SimpleGraph.mem_neighborFinset] using (hcomplete a ha c.1 c.2).symm,
          hAC ha⟩
    simp only [tyshkevichRightDegree]
    rw [hinter, H.degree_eq c.1] at hsplit
    rw [hinduce]
    omega
  exact
    { graph := K
      adjDecidable := hdec
      degree_eq := hdegree }

def tyshkevichMergeGraph (A C : Finset V) (hAC : A ⊆ Cᶜ)
    (L : SimpleGraph {x : V // x ∉ C}) (R : SimpleGraph {x : V // x ∈ C}) :
    SimpleGraph V where
  Adj x y :=
    (∃ hx : x ∉ C, ∃ hy : y ∉ C, L.Adj ⟨x, hx⟩ ⟨y, hy⟩) ∨
    (∃ hx : x ∈ C, ∃ hy : y ∈ C, R.Adj ⟨x, hx⟩ ⟨y, hy⟩) ∨
    (x ∈ A ∧ y ∈ C) ∨ (y ∈ A ∧ x ∈ C)
  symm := by
    constructor
    intro x y hxy
    rcases hxy with hL | hR | hACross | hCAcross
    · left
      obtain ⟨hx, hy, hxy⟩ := hL
      exact ⟨hy, hx, hxy.symm⟩
    · right; left
      obtain ⟨hx, hy, hxy⟩ := hR
      exact ⟨hy, hx, hxy.symm⟩
    · exact Or.inr (Or.inr (Or.inr hACross))
    · exact Or.inr (Or.inr (Or.inl hCAcross))
  loopless := by
    constructor
    intro x hxx
    rcases hxx with hL | hR | hcross | hcross
    · obtain ⟨hx, hx', hxx⟩ := hL
      have heq : (⟨x, hx⟩ : {z : V // z ∉ C}) = ⟨x, hx'⟩ := Subtype.ext rfl
      exact L.irrefl (heq ▸ hxx)
    · obtain ⟨hx, hx', hxx⟩ := hR
      have heq : (⟨x, hx⟩ : {z : V // z ∈ C}) = ⟨x, hx'⟩ := Subtype.ext rfl
      exact R.irrefl (heq ▸ hxx)
    · exact (Finset.mem_compl.mp (hAC hcross.1)) hcross.2
    · exact (Finset.mem_compl.mp (hAC hcross.1)) hcross.2

noncomputable def tyshkevichMergeRealization {d : V → ℕ}
    (A C : Finset V) (hAC : A ⊆ Cᶜ)
    (hAdegree : ∀ a ∈ A, C.card ≤ d a)
    (hCdegree : ∀ c ∈ C, A.card ≤ d c)
    (L : Realization (tyshkevichLeftDegree d A C))
    (R : Realization (tyshkevichRightDegree d A C)) : Realization d := by
  classical
  let K := tyshkevichMergeGraph A C hAC L.graph R.graph
  let hdec : DecidableRel K.Adj := Classical.decRel _
  letI := hdec
  let eL : {x : V // x ∉ C} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let eR : {x : V // x ∈ C} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hdegree (x : V) : K.degree x = d x := by
    by_cases hxC : x ∈ C
    · let xc : {z : V // z ∈ C} := ⟨x, hxC⟩
      have hN : K.neighborFinset x = (R.graph.neighborFinset xc).map eR ∪ A := by
        ext y
        simp only [Finset.mem_union, Finset.mem_map, SimpleGraph.mem_neighborFinset]
        constructor
        · intro hxy
          change (tyshkevichMergeGraph A C hAC L.graph R.graph).Adj x y at hxy
          rcases hxy with hL | hR | hcross | hcross
          · obtain ⟨hx, -, -⟩ := hL
            exact (hx hxC).elim
          · obtain ⟨hx, hy, hxy⟩ := hR
            left
            exact ⟨⟨y, hy⟩, hxy, rfl⟩
          · exact ((Finset.mem_compl.mp (hAC hcross.1)) hxC).elim
          · exact Or.inr hcross.1
        · rintro (⟨y', hy', rfl⟩ | hyA)
          · change (tyshkevichMergeGraph A C hAC L.graph R.graph).Adj x y'.1
            exact Or.inr (Or.inl ⟨hxC, y'.2, hy'⟩)
          · change (tyshkevichMergeGraph A C hAC L.graph R.graph).Adj x y
            exact Or.inr (Or.inr (Or.inr ⟨hyA, hxC⟩))
      have hdisj : Disjoint ((R.graph.neighborFinset xc).map eR) A := by
        rw [Finset.disjoint_left]
        intro y hyR hyA
        obtain ⟨y', -, rfl⟩ := Finset.mem_map.mp hyR
        exact (Finset.mem_compl.mp (hAC hyA)) y'.2
      rw [← K.card_neighborFinset_eq_degree, hN, Finset.card_union_of_disjoint hdisj,
        Finset.card_map, R.graph.card_neighborFinset_eq_degree, R.degree_eq]
      simp only [tyshkevichRightDegree, xc]
      have hxdeg := hCdegree x hxC
      omega
    · let xl : {z : V // z ∉ C} := ⟨x, hxC⟩
      by_cases hxA : x ∈ A
      · have hN : K.neighborFinset x = (L.graph.neighborFinset xl).map eL ∪ C := by
          ext y
          simp only [Finset.mem_union, Finset.mem_map, SimpleGraph.mem_neighborFinset]
          constructor
          · intro hxy
            change (tyshkevichMergeGraph A C hAC L.graph R.graph).Adj x y at hxy
            rcases hxy with hL | hR | hcross | hcross
            · obtain ⟨hx, hy, hxy⟩ := hL
              left
              exact ⟨⟨y, hy⟩, hxy, rfl⟩
            · obtain ⟨hx, -, -⟩ := hR
              exact (hxC hx).elim
            · exact Or.inr hcross.2
            · exact (hxC hcross.2).elim
          · rintro (⟨y', hy', rfl⟩ | hyC)
            · change (tyshkevichMergeGraph A C hAC L.graph R.graph).Adj x y'.1
              exact Or.inl ⟨hxC, y'.2, hy'⟩
            · change (tyshkevichMergeGraph A C hAC L.graph R.graph).Adj x y
              exact Or.inr (Or.inr (Or.inl ⟨hxA, hyC⟩))
        have hdisj : Disjoint ((L.graph.neighborFinset xl).map eL) C := by
          rw [Finset.disjoint_left]
          intro y hyL hyC
          obtain ⟨y', -, rfl⟩ := Finset.mem_map.mp hyL
          exact y'.2 hyC
        rw [← K.card_neighborFinset_eq_degree, hN, Finset.card_union_of_disjoint hdisj,
          Finset.card_map, L.graph.card_neighborFinset_eq_degree, L.degree_eq]
        simp only [tyshkevichLeftDegree, xl, hxA, if_true]
        have hxdeg := hAdegree x hxA
        omega
      · have hN : K.neighborFinset x = (L.graph.neighborFinset xl).map eL := by
          ext y
          simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset]
          constructor
          · intro hxy
            change (tyshkevichMergeGraph A C hAC L.graph R.graph).Adj x y at hxy
            rcases hxy with hL | hR | hcross | hcross
            · obtain ⟨hx, hy, hxy⟩ := hL
              exact ⟨⟨y, hy⟩, hxy, rfl⟩
            · obtain ⟨hx, -, -⟩ := hR
              exact (hxC hx).elim
            · exact (hxA hcross.1).elim
            · exact (hxC hcross.2).elim
          · rintro ⟨y', hy', rfl⟩
            change (tyshkevichMergeGraph A C hAC L.graph R.graph).Adj x y'.1
            exact Or.inl ⟨hxC, y'.2, hy'⟩
        rw [← K.card_neighborFinset_eq_degree, hN, Finset.card_map,
          L.graph.card_neighborFinset_eq_degree, L.degree_eq]
        simp [tyshkevichLeftDegree, xl, hxA]
  exact
    { graph := K
      adjDecidable := hdec
      degree_eq := hdegree }

theorem tyshkevichMergeGraph_comap_left (A C : Finset V) (hAC : A ⊆ Cᶜ)
    (L : SimpleGraph {x : V // x ∉ C}) (R : SimpleGraph {x : V // x ∈ C}) :
    (tyshkevichMergeGraph A C hAC L R).comap
      (fun x : {z : V // z ∉ C} => x.1) = L := by
  ext x y
  simp only [SimpleGraph.comap_adj]
  change (tyshkevichMergeGraph A C hAC L R).Adj x.1 y.1 ↔ L.Adj x y
  constructor
  · intro hxy
    rcases hxy with hL | hR | hcross | hcross
    · obtain ⟨hx, hy, hxy⟩ := hL
      convert hxy using 1 <;> apply Subtype.ext <;> rfl
    · obtain ⟨hx, -, -⟩ := hR
      exact (x.2 hx).elim
    · exact (y.2 hcross.2).elim
    · exact (x.2 hcross.2).elim
  · intro hxy
    exact Or.inl ⟨x.2, y.2, hxy⟩

theorem tyshkevichMergeGraph_comap_right (A C : Finset V) (hAC : A ⊆ Cᶜ)
    (L : SimpleGraph {x : V // x ∉ C}) (R : SimpleGraph {x : V // x ∈ C}) :
    (tyshkevichMergeGraph A C hAC L R).comap
      (fun x : {z : V // z ∈ C} => x.1) = R := by
  ext x y
  simp only [SimpleGraph.comap_adj]
  change (tyshkevichMergeGraph A C hAC L R).Adj x.1 y.1 ↔ R.Adj x y
  constructor
  · intro hxy
    rcases hxy with hL | hR | hcross | hcross
    · obtain ⟨hx, -, -⟩ := hL
      exact (hx x.2).elim
    · obtain ⟨hx, hy, hxy⟩ := hR
      convert hxy using 1 <;> apply Subtype.ext <;> rfl
    · exact ((Finset.mem_compl.mp (hAC hcross.1)) x.2).elim
    · exact ((Finset.mem_compl.mp (hAC hcross.1)) y.2).elim
  · intro hxy
    exact Or.inr (Or.inl ⟨x.2, y.2, hxy⟩)

theorem tyshkevichMergeGraph_restrict (A C : Finset V) (hAC : A ⊆ Cᶜ)
    (H : SimpleGraph V)
    (hcomplete : ∀ a ∈ A, ∀ c ∈ C, H.Adj a c)
    (hanticomplete : ∀ b ∈ Cᶜ \ A, ∀ c ∈ C, ¬ H.Adj b c) :
    tyshkevichMergeGraph A C hAC
      (H.comap (fun x : {z : V // z ∉ C} => x.1))
      (H.comap (fun x : {z : V // z ∈ C} => x.1)) = H := by
  ext x y
  by_cases hxC : x ∈ C
  · by_cases hyC : y ∈ C
    · constructor
      · intro hxy
        rcases hxy with hL | hR | hcross | hcross
        · obtain ⟨hx, -, -⟩ := hL
          exact (hx hxC).elim
        · obtain ⟨hx, hy, hxy⟩ := hR
          exact hxy
        · exact ((Finset.mem_compl.mp (hAC hcross.1)) hxC).elim
        · exact ((Finset.mem_compl.mp (hAC hcross.1)) hyC).elim
      · intro hxy
        exact Or.inr (Or.inl ⟨hxC, hyC, hxy⟩)
    · constructor
      · intro hxy
        rcases hxy with hL | hR | hcross | hcross
        · obtain ⟨hx, -, -⟩ := hL
          exact (hx hxC).elim
        · obtain ⟨-, hy, -⟩ := hR
          exact (hyC hy).elim
        · exact ((Finset.mem_compl.mp (hAC hcross.1)) hxC).elim
        · exact (hcomplete y hcross.1 x hxC).symm
      · intro hxy
        by_cases hyA : y ∈ A
        · exact Or.inr (Or.inr (Or.inr ⟨hyA, hxC⟩))
        · have hyB : y ∈ Cᶜ \ A := by simp [hyC, hyA]
          exact (hanticomplete y hyB x hxC hxy.symm).elim
  · by_cases hyC : y ∈ C
    · constructor
      · intro hxy
        rcases hxy with hL | hR | hcross | hcross
        · obtain ⟨-, hy, -⟩ := hL
          exact (hy hyC).elim
        · obtain ⟨hx, -, -⟩ := hR
          exact (hxC hx).elim
        · exact hcomplete x hcross.1 y hyC
        · exact ((Finset.mem_compl.mp (hAC hcross.1)) hyC).elim
      · intro hxy
        by_cases hxA : x ∈ A
        · exact Or.inr (Or.inr (Or.inl ⟨hxA, hyC⟩))
        · have hxB : x ∈ Cᶜ \ A := by simp [hxC, hxA]
          exact (hanticomplete x hxB y hyC hxy).elim
    · constructor
      · intro hxy
        rcases hxy with hL | hR | hcross | hcross
        · obtain ⟨hx, hy, hxy⟩ := hL
          exact hxy
        · obtain ⟨hx, -, -⟩ := hR
          exact (hxC hx).elim
        · exact (hyC hcross.2).elim
        · exact (hxC hcross.2).elim
      · intro hxy
        exact Or.inl ⟨hxC, hyC, hxy⟩

private theorem map_edgeFinset_comap_pred (p : V → Prop) [DecidablePred p]
    (S : Finset V) (hp : ∀ x, p x ↔ x ∈ S) (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ((G.comap (fun x : {z : V // p z} => x.1)).edgeFinset).map
        (⟨Subtype.val, Subtype.val_injective⟩ : {z : V // p z} ↪ V).sym2Map =
      G.edgeFinset ∩ S.sym2 := by
  classical
  ext z
  induction z using Sym2.inductionOn with
  | _ x y =>
      simp only [Finset.mem_map, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.comap_adj, Finset.mem_inter, Finset.mk_mem_sym2_iff]
      constructor
      · rintro ⟨w, hw, hmap⟩
        induction w using Sym2.inductionOn with
        | _ a b =>
            change s((a : V), (b : V)) = s(x, y) at hmap
            rw [Sym2.eq_iff] at hmap
            rcases hmap with ⟨hax, hby⟩ | ⟨hay, hbx⟩
            · subst x; subst y
              exact ⟨hw, (hp a).mp a.2, (hp b).mp b.2⟩
            · subst y; subst x
              exact ⟨hw.symm, (hp b).mp b.2, (hp a).mp a.2⟩
      · rintro ⟨hxy, hxS, hyS⟩
        refine ⟨s(⟨x, (hp x).mpr hxS⟩, ⟨y, (hp y).mpr hyS⟩), ?_, ?_⟩
        · exact hxy
        · simp [Function.Embedding.sym2Map_apply]

private theorem comap_symmDiff_card_pred (p : V → Prop) [DecidablePred p]
    (S : Finset V) (hp : ∀ x, p x ↔ x ∈ S) (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] :
    (((G.comap (fun x : {z : V // p z} => x.1)).edgeFinset) ∆
        ((H.comap (fun x : {z : V // p z} => x.1)).edgeFinset)).card =
      ((G.edgeFinset ∆ H.edgeFinset) ∩ S.sym2).card := by
  classical
  let e : {z : V // p z} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  calc
    _ = (((((G.comap (fun x : {z : V // p z} => x.1)).edgeFinset) ∆
        ((H.comap (fun x : {z : V // p z} => x.1)).edgeFinset)).map e.sym2Map).card) :=
      (Finset.card_map e.sym2Map).symm
    _ = _ := by
      rw [Finset.map_eq_image, Finset.image_symmDiff _ _ e.sym2Map.injective,
        ← Finset.map_eq_image, ← Finset.map_eq_image]
      change ((G.comap (fun x : {z : V // p z} => x.1)).edgeFinset.map
          (⟨Subtype.val, Subtype.val_injective⟩ : {z : V // p z} ↪ V).sym2Map ∆
        (H.comap (fun x : {z : V // p z} => x.1)).edgeFinset.map
          (⟨Subtype.val, Subtype.val_injective⟩ : {z : V // p z} ↪ V).sym2Map).card = _
      rw [map_edgeFinset_comap_pred p S hp G, map_edgeFinset_comap_pred p S hp H]
      congr 1
      ext z
      simp only [Finset.mem_symmDiff, Finset.mem_inter]
      tauto

private theorem map_edgeFinset_comap_right (C : Finset V) (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ((G.comap (fun x : {z : V // z ∈ C} => x.1)).edgeFinset).map
        (⟨Subtype.val, Subtype.val_injective⟩ : {z : V // z ∈ C} ↪ V).sym2Map =
      G.edgeFinset ∩ C.sym2 := by
  classical
  ext z
  induction z using Sym2.inductionOn with
  | _ x y =>
      simp only [Finset.mem_map, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        Finset.mem_inter, Finset.mk_mem_sym2_iff]
      constructor
      · rintro ⟨w, hw, hmap⟩
        induction w using Sym2.inductionOn with
        | _ a b =>
            change s((a : V), (b : V)) = s(x, y) at hmap
            rw [Sym2.eq_iff] at hmap
            rcases hmap with ⟨hax, hby⟩ | ⟨hay, hbx⟩
            · subst x; subst y
              exact ⟨hw, a.2, b.2⟩
            · subst y; subst x
              exact ⟨hw.symm, b.2, a.2⟩
      · rintro ⟨hxy, hxC, hyC⟩
        refine ⟨s(⟨x, hxC⟩, ⟨y, hyC⟩), hxy, ?_⟩
        simp [Function.Embedding.sym2Map_apply]

private theorem comap_symmDiff_card_right (C : Finset V) (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] :
    (((G.comap (fun x : {z : V // z ∈ C} => x.1)).edgeFinset) ∆
        ((H.comap (fun x : {z : V // z ∈ C} => x.1)).edgeFinset)).card =
      ((G.edgeFinset ∆ H.edgeFinset) ∩ C.sym2).card := by
  classical
  let e : {z : V // z ∈ C} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  calc
    _ = (((((G.comap (fun x : {z : V // z ∈ C} => x.1)).edgeFinset) ∆
        ((H.comap (fun x : {z : V // z ∈ C} => x.1)).edgeFinset)).map e.sym2Map).card) :=
      (Finset.card_map e.sym2Map).symm
    _ = _ := by
      rw [Finset.map_eq_image, Finset.image_symmDiff _ _ e.sym2Map.injective,
        ← Finset.map_eq_image, ← Finset.map_eq_image]
      change ((G.comap (fun x : {z : V // z ∈ C} => x.1)).edgeFinset.map
          (⟨Subtype.val, Subtype.val_injective⟩ : {z : V // z ∈ C} ↪ V).sym2Map ∆
        (H.comap (fun x : {z : V // z ∈ C} => x.1)).edgeFinset.map
          (⟨Subtype.val, Subtype.val_injective⟩ : {z : V // z ∈ C} ↪ V).sym2Map).card = _
      rw [map_edgeFinset_comap_right C G, map_edgeFinset_comap_right C H]
      congr 1
      ext z
      simp only [Finset.mem_symmDiff, Finset.mem_inter]
      tauto

theorem realization_symmDiff_card_split {d : V → ℕ} (C : Finset V)
    (G H : Realization d)
    (hcross : ∀ x y : V, x ∈ C → y ∉ C →
      (G.graph.Adj x y ↔ H.graph.Adj x y)) :
    (G.edgeFinset ∆ H.edgeFinset).card =
      (((G.graph.comap (fun x : {z : V // z ∉ C} => x.1)).edgeFinset) ∆
          ((H.graph.comap (fun x : {z : V // z ∉ C} => x.1)).edgeFinset)).card +
        (((G.graph.comap (fun x : {z : V // z ∈ C} => x.1)).edgeFinset) ∆
          ((H.graph.comap (fun x : {z : V // z ∈ C} => x.1)).edgeFinset)).card := by
  classical
  let D := G.edgeFinset ∆ H.edgeFinset
  let DL := D ∩ Cᶜ.sym2
  let DR := D ∩ C.sym2
  have hcover : D = DL ∪ DR := by
    apply Finset.Subset.antisymm
    · intro z hz
      induction z using Sym2.inductionOn with
      | _ x y =>
          by_cases hxC : x ∈ C
          · by_cases hyC : y ∈ C
            · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr
                ⟨hz, Finset.mk_mem_sym2_iff.mpr ⟨hxC, hyC⟩⟩))
            · have hsame := hcross x y hxC hyC
              have hdiff :
                  (G.graph.Adj x y ∧ ¬ H.graph.Adj x y) ∨
                    (H.graph.Adj x y ∧ ¬ G.graph.Adj x y) := by
                change s(x, y) ∈ G.graph.edgeFinset ∆ H.graph.edgeFinset at hz
                simpa only [Finset.mem_symmDiff, SimpleGraph.mem_edgeFinset,
                  SimpleGraph.mem_edgeSet] using hz
              exact (hdiff.elim (fun h => h.2 (hsame.mp h.1))
                (fun h => h.2 (hsame.mpr h.1))).elim
          · by_cases hyC : y ∈ C
            · have hsame := hcross y x hyC hxC
              have hdiff :
                  (G.graph.Adj x y ∧ ¬ H.graph.Adj x y) ∨
                    (H.graph.Adj x y ∧ ¬ G.graph.Adj x y) := by
                change s(x, y) ∈ G.graph.edgeFinset ∆ H.graph.edgeFinset at hz
                simpa only [Finset.mem_symmDiff, SimpleGraph.mem_edgeFinset,
                  SimpleGraph.mem_edgeSet] using hz
              exact (hdiff.elim
                (fun h => h.2 ((hsame.mp h.1.symm).symm))
                (fun h => h.2 ((hsame.mpr h.1.symm).symm))).elim
            · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr
                ⟨hz, Finset.mk_mem_sym2_iff.mpr ⟨by simp [hxC], by simp [hyC]⟩⟩))
    · apply Finset.union_subset
      · intro z hz
        exact (Finset.mem_inter.mp hz).1
      · intro z hz
        exact (Finset.mem_inter.mp hz).1
  have hdisj : Disjoint DL DR := by
    rw [Finset.disjoint_left]
    intro z hzL hzR
    induction z using Sym2.inductionOn with
    | _ x y =>
        have hxnot : x ∉ C := Finset.mem_compl.mp
          (Finset.mk_mem_sym2_iff.mp (Finset.mem_inter.mp hzL).2).1
        exact hxnot (Finset.mk_mem_sym2_iff.mp (Finset.mem_inter.mp hzR).2).1
  change D.card = _
  rw [hcover, Finset.card_union_of_disjoint hdisj]
  rw [comap_symmDiff_card_pred (fun z : V => z ∉ C) Cᶜ (by simp) G.graph H.graph,
    comap_symmDiff_card_right C G.graph H.graph]
  simp [D, DL, DR, Realization.edgeFinset]


/-- Distinct realizations differ on at least four edges.  This is the edge-count companion to
`differenceSupport_card_ge_four`; balance at every vertex makes the support no larger than the
edge set. -/
theorem realization_edgeSymmDiff_card_ge_four {d : V → ℕ} {X Y : Realization d}
    (hXY : X ≠ Y) : 4 ≤ (X.edgeFinset ∆ Y.edgeFinset).card := by
  classical
  let D : SimpleGraph V := edgeDifferenceGraph X Y
  have hDedge : D.edgeFinset = X.edgeFinset ∆ Y.edgeFinset :=
    edgeDifferenceGraph_edgeFinset X Y
  have hdegLower : ∀ v ∈ D.support, 2 ≤ D.degree v := by
    intro v hv
    have hpos : 0 < D.degree v := (D.degree_pos_iff_mem_support v).2 hv
    rw [edgeDifference_degree_eq_twice_local X Y v] at hpos ⊢
    omega
  have hsum : ∑ v ∈ D.support.toFinset, D.degree v = 2 * D.edgeFinset.card :=
    D.sum_degrees_support_eq_twice_card_edges
  have hlower : 2 * D.support.toFinset.card ≤
      ∑ v ∈ D.support.toFinset, D.degree v := by
    calc
      2 * D.support.toFinset.card = ∑ _v ∈ D.support.toFinset, 2 := by
        simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ D.support.toFinset, D.degree v :=
        Finset.sum_le_sum fun v hv ↦ hdegLower v (Set.mem_toFinset.mp hv)
  have hsupport : 4 ≤ D.support.toFinset.card := by
    rw [← edgeSupport_symmDiff_eq_support X Y]
    exact differenceSupport_card_ge_four hXY
  rw [hsum, hDedge] at hlower
  omega


private theorem realization_eq_of_graph_eq' {d : V → ℕ} {G H : Realization d}
    (h : G.graph = H.graph) : G = H := by
  cases G with
  | mk graphG decG degreeG =>
      cases H with
      | mk graphH decH degreeH =>
          dsimp at h
          subst graphH
          congr
          exact Subsingleton.elim _ _

/-- Manuscript Theorem 4.2 for a specified (arbitrary) Tyshkevich witness. -/
noncomputable def realizationGraph_iso_boxProd_of_tyshkevichWitness {d : V → ℕ}
    (G₀ : Realization d) (A C : Finset V)
    (hAC : A ⊆ Cᶜ)
    (hAclique : G₀.graph.IsClique (A : Set V))
    (hBindep : ∀ u ∈ Cᶜ \ A, ∀ w ∈ Cᶜ \ A, ¬ G₀.graph.Adj u w)
    (hAcomplete : ∀ a ∈ A, ∀ c ∈ C, G₀.graph.Adj a c)
    (hBanticomplete : ∀ b ∈ Cᶜ \ A, ∀ c ∈ C, ¬ G₀.graph.Adj b c) :
    RealizationGraph d ≃g
      RealizationGraph (tyshkevichLeftDegree d A C) □
        RealizationGraph (tyshkevichRightDegree d A C) := by
  classical
  let forced (H : Realization d) := tyshkevich_forced_in_every_realization
    G₀ A C hAC hAclique hBindep hAcomplete hBanticomplete H
  have hAdegree : ∀ a ∈ A, C.card ≤ d a := by
    intro a ha
    rw [← G₀.degree_eq a, ← G₀.graph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro c hc
    simpa only [SimpleGraph.mem_neighborFinset] using hAcomplete a ha c hc
  have hCdegree : ∀ c ∈ C, A.card ≤ d c := by
    intro c hc
    rw [← G₀.degree_eq c, ← G₀.graph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro a ha
    simpa only [SimpleGraph.mem_neighborFinset] using (hAcomplete a ha c hc).symm
  let left (H : Realization d) : Realization (tyshkevichLeftDegree d A C) :=
    tyshkevichLeftRestriction A C H (forced H).2.2.1 (forced H).2.2.2
  let right (H : Realization d) : Realization (tyshkevichRightDegree d A C) :=
    tyshkevichRightRestriction A C H hAC (forced H).2.2.1 (forced H).2.2.2
  let merge (P : Realization (tyshkevichLeftDegree d A C) ×
      Realization (tyshkevichRightDegree d A C)) : Realization d :=
    tyshkevichMergeRealization A C hAC hAdegree hCdegree P.1 P.2
  have hleftInv (H : Realization d) : merge (left H, right H) = H := by
    apply realization_eq_of_graph_eq'
    change tyshkevichMergeGraph A C hAC
      (H.graph.comap (fun x : {z : V // z ∉ C} => x.1))
      (H.graph.comap (fun x : {z : V // z ∈ C} => x.1)) = H.graph
    exact tyshkevichMergeGraph_restrict A C hAC H.graph
      (forced H).2.2.1 (forced H).2.2.2
  have hrightInv (P : Realization (tyshkevichLeftDegree d A C) ×
      Realization (tyshkevichRightDegree d A C)) :
      (left (merge P), right (merge P)) = P := by
    apply Prod.ext
    · apply realization_eq_of_graph_eq'
      change (tyshkevichMergeGraph A C hAC P.1.graph P.2.graph).comap
        (fun x : {z : V // z ∉ C} => x.1) = P.1.graph
      exact tyshkevichMergeGraph_comap_left A C hAC P.1.graph P.2.graph
    · apply realization_eq_of_graph_eq'
      change (tyshkevichMergeGraph A C hAC P.1.graph P.2.graph).comap
        (fun x : {z : V // z ∈ C} => x.1) = P.2.graph
      exact tyshkevichMergeGraph_comap_right A C hAC P.1.graph P.2.graph
  let e : Realization d ≃
      Realization (tyshkevichLeftDegree d A C) ×
        Realization (tyshkevichRightDegree d A C) :=
    { toFun := fun H => (left H, right H)
      invFun := merge
      left_inv := hleftInv
      right_inv := hrightInv }
  refine
    { toEquiv := e
      map_rel_iff' := ?_ }
  intro X Y
  have hcross : ∀ x y : V, x ∈ C → y ∉ C →
      (X.graph.Adj x y ↔ Y.graph.Adj x y) := by
    intro x y hxC hyC
    have hiff (H : Realization d) : H.graph.Adj x y ↔ y ∈ A := by
      constructor
      · intro hxy
        by_contra hyA
        have hyB : y ∈ Cᶜ \ A := by simp [hyC, hyA]
        exact (forced H).2.2.2 y hyB x hxC hxy.symm
      · intro hyA
        exact ((forced H).2.2.1 y hyA x hxC).symm
    exact (hiff X).trans (hiff Y).symm
  have hsum := realization_symmDiff_card_split C X Y hcross
  change (X.edgeFinset ∆ Y.edgeFinset).card =
      ((left X).edgeFinset ∆ (left Y).edgeFinset).card +
        ((right X).edgeFinset ∆ (right Y).edgeFinset).card at hsum
  apply Iff.symm
  change (X.edgeFinset ∆ Y.edgeFinset).card = 4 ↔ _
  rw [SimpleGraph.boxProd_adj]
  constructor
  · intro hamb
    by_cases hL : left X = left Y
    · right
      refine ⟨?_, hL⟩
      change ((right X).edgeFinset ∆ (right Y).edgeFinset).card = 4
      simp [hL] at hsum
      omega
    · by_cases hR : right X = right Y
      · left
        refine ⟨?_, hR⟩
        change ((left X).edgeFinset ∆ (left Y).edgeFinset).card = 4
        simp [hR] at hsum
        omega
      · have hLge := realization_edgeSymmDiff_card_ge_four hL
        have hRge := realization_edgeSymmDiff_card_ge_four hR
        omega
  · rintro (⟨hLadj, hR⟩ | ⟨hRadj, hL⟩)
    · change ((left X).edgeFinset ∆ (left Y).edgeFinset).card = 4 at hLadj
      change right X = right Y at hR
      have hRzero : ((right X).edgeFinset ∆ (right Y).edgeFinset).card = 0 := by
        rw [hR]
        simp
      omega
    · change ((right X).edgeFinset ∆ (right Y).edgeFinset).card = 4 at hRadj
      change left X = left Y at hL
      have hLzero : ((left X).edgeFinset ∆ (left Y).edgeFinset).card = 0 := by
        rw [hL]
        simp
      omega

/-- Manuscript Theorem 4.2, extracting the two factor grounds from decomposability. -/
theorem realizationGraph_iso_boxProd_of_tyshkevichDecomposable {d : V → ℕ}
    (hdec : TyshkevichDecomposable d) :
    ∃ A C : Finset V, C.Nonempty ∧ Cᶜ.Nonempty ∧
      Nonempty (RealizationGraph d ≃g
        RealizationGraph (tyshkevichLeftDegree d A C) □
          RealizationGraph (tyshkevichRightDegree d A C)) := by
  rcases hdec with ⟨G₀, A, C, hC, hCc, hAC, hclique, hBindep, hcomplete, hanti⟩
  exact ⟨A, C, hC, hCc,
    ⟨realizationGraph_iso_boxProd_of_tyshkevichWitness
      G₀ A C hAC hclique hBindep hcomplete hanti⟩⟩


private def boxProdSubsingletonIso_local
    {W Z : Type*} [Subsingleton Z] [Inhabited Z]
    (P : SimpleGraph W) (Q : SimpleGraph Z) : P □ Q ≃g P where
  toEquiv :=
    { toFun := Prod.fst
      invFun := fun w => (w, default)
      left_inv := fun z => Prod.ext rfl (Subsingleton.elim _ _)
      right_inv := fun _ => rfl }
  map_rel_iff' := by
    intro x y
    change P.Adj x.1 y.1 ↔
      (P.Adj x.1 y.1 ∧ x.2 = y.2) ∨ (Q.Adj x.2 y.2 ∧ x.1 = y.1)
    constructor
    · intro h
      exact Or.inl ⟨h, Subsingleton.elim _ _⟩
    · rintro (h | h)
      · exact h.1
      · exact (h.1.ne (Subsingleton.elim _ _)).elim

/-- **Manuscript Theorem 4.1, the inactive-vertex reduction.** If every realization gives `v` the same
neighborhood `S`, then no 2-switch can touch `v` — a switch through `v` would change `N(v)` — so
deleting `v` is a bijection onto the realizations of the residual, carrying switches to switches in
both directions.

The **reflection** direction is not decoration: an isomorphism claim that only preserves adjacency is
a standard error, and the §4 adversary asked for it explicitly.

⚠ **`hgraphical` is REQUIRED, and this statement was FALSE without it.** Written first with only
`hS`, it was refuted by the wave sent to prove it, with a machine-checked counterexample the lead
then reproduced independently: on `V = Fin 1` with `d 0 = 1` and `S = ∅`, **no graph realizes `d`**,
so `hS` holds **vacuously** — while the residual lives on an empty carrier, where the empty graph
realizes it. One side has no vertices and the other has one, so no isomorphism exists.

That is the **vacuous-hypothesis** bug class this module's header already warns about, committed by
the lead while writing the statement, and caught only because every wave brief carries *"if a
statement is false as written, STOP and report."* A hypothesis that is satisfiable only because
nothing satisfies its subject proves nothing. -/
theorem realizationGraph_iso_of_inactive {d : V → ℕ} {v : V} {S : Finset V}
    (hgraphical : Nonempty (Realization d))
    (hS : ∀ G : Realization d, G.neighborFinset v = S) :
    Nonempty (RealizationGraph d ≃g RealizationGraph (residualDegree d v S)) := by
  classical
  obtain ⟨G₀⟩ := hgraphical
  have hG₀S : G₀.neighborFinset v = S := hS G₀
  have hvS : v ∉ S := by
    intro hv
    have hvN : v ∈ G₀.neighborFinset v := by
      rw [hG₀S]
      exact hv
    exact G₀.graph.irrefl ((G₀.mem_neighborFinset v v).mp hvN)
  have hcard : S.card = d v := by
    rw [← hG₀S]
    simp [Realization.neighborFinset, SimpleGraph.card_neighborFinset_eq_degree,
      G₀.degree_eq v]
  have hpos : ∀ u ∈ S, 0 < d u := by
    intro u hu
    exact pos_degree_of_mem_realizable ⟨G₀, hG₀S⟩ hu
  let eFibre : Realization d ≃ interfaceFibre d v S :=
    { toFun := fun G => ⟨G, hS G⟩
      invFun := fun G => G.1
      left_inv := fun _ => rfl
      right_inv := fun _ => Subtype.ext rfl }
  let eFull : RealizationGraph d ≃g interfaceFibreGraph d v S :=
    { toEquiv := eFibre
      map_rel_iff' := by
        intro G H
        rfl }
  exact ⟨eFull.trans (fibreDeleteIso hvS hcard hpos)⟩

/-- **Manuscript Corollary 4.3, component closure**, in the form §10.1 consumes: if a degree function
decomposes and both sides have maximally Hamiltonian realization graphs, so does it.

Theorem 4.2 is the vehicle — in a Tyshkevich composition the cross adjacencies are forced in every
realization, so no 2-switch crosses, every switch lifts, and the realization graph is the Cartesian
product of the two sides'. The `FactorReady` hypotheses are what §3 supplies for a bipartite factor:
`boxProd_hamConnected_paper` needs the bipartite side to carry the paired two-disjoint-path property,
which is exactly Theorem 3.1's content and the reason §3 proves more than Hamilton-laceability. -/
theorem isMH_boxProd_of_factorReady {WA WB : Type u} [Fintype WA] [Fintype WB]
    [DecidableEq WA] [DecidableEq WB] {A : SimpleGraph WA} {B : SimpleGraph WB}
    (hA : FactorReady A) (hB : FactorReady B) :
    IsMH (A □ B) := by
  classical
  by_cases hnb : ¬ ∃ col, IsProper2Coloring (A □ B) col
  · exact Or.inl (boxProd_hamConnected_paper hA hB hnb)
  · push_neg at hnb
    obtain ⟨col, hcol⟩ := hnb
    have hWA : Nonempty WA := by
      rcases hA with ⟨hAnb, _⟩ | ⟨colA, _, hAsurj, _, _⟩
      · by_contra hne
        apply hAnb
        refine ⟨fun _ => false, ?_⟩
        intro a _ _
        exact (hne ⟨a⟩).elim
      · obtain ⟨a, _⟩ := hAsurj false
        exact ⟨a⟩
    have hWB : Nonempty WB := by
      rcases hB with ⟨hBnb, _⟩ | ⟨colB, _, hBsurj, _, _⟩
      · by_contra hne
        apply hBnb
        refine ⟨fun _ => false, ?_⟩
        intro b _ _
        exact (hne ⟨b⟩).elim
      · obtain ⟨b, _⟩ := hBsurj false
        exact ⟨b⟩
    let a₀ : WA := Classical.choice hWA
    let b₀ : WB := Classical.choice hWB
    have hAbipFromProd : IsProper2Coloring A (fun a => col (a, b₀)) := by
      intro a a' haa
      exact hcol (a, b₀) (a', b₀) (by
        rw [SimpleGraph.boxProd_adj]
        exact Or.inl ⟨haa, rfl⟩)
    have hBbipFromProd : IsProper2Coloring B (fun b => col (a₀, b)) := by
      intro b b' hbb
      exact hcol (a₀, b) (a₀, b') (by
        rw [SimpleGraph.boxProd_adj]
        exact Or.inr ⟨hbb, rfl⟩)
    rcases hA with ⟨hAnb, _⟩ | ⟨colA, hAbip, hAsurj, hAlace, hAspan⟩
    · exact (hAnb ⟨_, hAbipFromProd⟩).elim
    rcases hB with ⟨hBnb, _⟩ | ⟨colB, hBbip, hBsurj, hBlace, hBspan⟩
    · exact (hBnb ⟨_, hBbipFromProd⟩).elim
    refine Or.inr ⟨fun p => Bool.xor (colA p.1) (colB p.2),
      boxProd_proper_color hAbip hBbip, ?_, ?_⟩
    · intro c
      obtain ⟨a, ha⟩ := hAsurj c
      obtain ⟨b, hb⟩ := hBsurj false
      exact ⟨(a, b), by simp [ha, hb]⟩
    · rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ hxor
      have hcolors :
          (colA a₁ = colA a₂ ∧ colB b₁ ≠ colB b₂) ∨
            (colA a₁ ≠ colA a₂ ∧ colB b₁ = colB b₂) := by
        have xor_ne_cases : ∀ x x' y y' : Bool,
            Bool.xor x y ≠ Bool.xor x' y' →
              (x = x' ∧ y ≠ y') ∨ (x ≠ x' ∧ y = y') := by
          decide
        exact xor_ne_cases _ _ _ _ hxor
      rcases hcolors with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · obtain ⟨pB, hpB⟩ := hBlace b₁ b₂ hb
        have hBeven : Even (Fintype.card WB) :=
          even_card_of_bip_laceable_surj (A := B) hBbip hBsurj hBlace
        have hlen : pB.support.length = Fintype.card WB := by
          rw [SimpleGraph.Walk.length_support, hpB.length_eq]
          have hpos : 0 < Fintype.card WB := Fintype.card_pos_iff.mpr hWB
          omega
        refine walk_pass_hamPath (A := A) (B := B) hAsurj hAlace a₁ a₂ pB hpB ?_
        rw [hlen]
        simp [walkColor, Nat.even_iff.mp hBeven, ha]
      · obtain ⟨pA, hpA⟩ := hAlace a₁ a₂ ha
        have hAeven : Even (Fintype.card WA) :=
          even_card_of_bip_laceable_surj (A := A) hAbip hAsurj hAlace
        have hlen : pA.support.length = Fintype.card WA := by
          rw [SimpleGraph.Walk.length_support, hpA.length_eq]
          have hpos : 0 < Fintype.card WA := Fintype.card_pos_iff.mpr hWA
          omega
        refine hasHamPath_iso (SimpleGraph.boxProdComm A B)
          (walk_pass_hamPath (A := B) (B := A) hBsurj hBlace b₁ b₂ pA hpA ?_)
        rw [hlen]
        simp [walkColor, Nat.even_iff.mp hAeven, hb]

/-- The decomposable branch of §10.1, including the one-realization factor cases. -/
theorem isMH_of_tyshkevichDecomposable_of_IH {d : V → ℕ}
    (hdec : TyshkevichDecomposable d)
    (IH : ∀ (W : Type u) [Fintype W] [DecidableEq W] (e : W → ℕ),
      Fintype.card W < Fintype.card V → IsMaximallyHamiltonianRealizationGraph e) :
    IsMaximallyHamiltonianRealizationGraph d := by
  classical
  rcases hdec with
    ⟨G₀, A, C, hC, hCc, hAC, hclique, hBindep, hcomplete, hanti⟩
  let dL := tyshkevichLeftDegree d A C
  let dR := tyshkevichRightDegree d A C
  let e : RealizationGraph d ≃g RealizationGraph dL □ RealizationGraph dR :=
    realizationGraph_iso_boxProd_of_tyshkevichWitness
      G₀ A C hAC hclique hBindep hcomplete hanti
  have hLlt : Fintype.card {x : V // x ∉ C} < Fintype.card V := by
    rw [Fintype.card_subtype_compl (fun x : V => x ∈ C)]
    have hCpos : 0 < Fintype.card {x : V // x ∈ C} := by
      rw [Fintype.card_pos_iff]
      exact ⟨⟨hC.choose, hC.choose_spec⟩⟩
    have hCle := Fintype.card_subtype_le (fun x : V => x ∈ C)
    omega
  have hRlt : Fintype.card {x : V // x ∈ C} < Fintype.card V := by
    have hLpos : 0 < Fintype.card {x : V // x ∉ C} := by
      rw [Fintype.card_pos_iff]
      exact ⟨⟨hCc.choose, Finset.mem_compl.mp hCc.choose_spec⟩⟩
    have hsum := Fintype.card_subtype_compl (fun x : V => x ∈ C)
    have hRle := Fintype.card_subtype_le (fun x : V => x ∈ C)
    omega
  have hLMH : IsMH (RealizationGraph dL) := IH _ dL hLlt
  have hRMH : IsMH (RealizationGraph dR) := IH _ dR hRlt
  have hLnon : Nonempty (Realization dL) := ⟨(e G₀).1⟩
  have hRnon : Nonempty (Realization dR) := ⟨(e G₀).2⟩
  have hprod : IsMH (RealizationGraph dL □ RealizationGraph dR) := by
    by_cases hLcard : 2 ≤ Fintype.card (Realization dL)
    · by_cases hRcard : 2 ≤ Fintype.card (Realization dR)
      · exact isMH_boxProd_of_factorReady
          (factorReady_of_realizationGraph dL hLMH hLcard)
          (factorReady_of_realizationGraph dR hRMH hRcard)
      · have hRle : Fintype.card (Realization dR) ≤ 1 := by omega
        letI : Subsingleton (Realization dR) :=
          Fintype.card_le_one_iff_subsingleton.mp hRle
        letI : Inhabited (Realization dR) := ⟨Classical.choice hRnon⟩
        exact isMH_iso (boxProdSubsingletonIso_local
          (RealizationGraph dL) (RealizationGraph dR)) hLMH
    · have hLle : Fintype.card (Realization dL) ≤ 1 := by omega
      letI : Subsingleton (Realization dL) :=
        Fintype.card_le_one_iff_subsingleton.mp hLle
      letI : Inhabited (Realization dL) := ⟨Classical.choice hLnon⟩
      exact isMH_iso
        ((SimpleGraph.boxProdComm (RealizationGraph dL) (RealizationGraph dR)).trans
          (boxProdSubsingletonIso_local (RealizationGraph dR) (RealizationGraph dL))) hRMH
  exact isMH_iso e hprod


/-! ## 5c. One-pass assembly plumbing -/

/-- Every realized pivot fibre is maximally Hamiltonian by the induction hypothesis on the
one-vertex-smaller residual ground. -/
theorem fibreGraph_isMH_of_IH {d : V → ℕ}
    (IH : ∀ (W : Type u) [Fintype W] [DecidableEq W] (e : W → ℕ),
      Fintype.card W < Fintype.card V → IsMaximallyHamiltonianRealizationGraph e)
    (v : V) (S : Finset V) (hS : HasRealizationWithNeighborSet d v S) :
    IsMH (fibreGraph d v S) := by
  classical
  obtain ⟨G, hG⟩ := hS
  have hvS : v ∉ S := by
    intro hv
    have hvN : v ∈ G.neighborFinset v := by simpa [hG] using hv
    exact G.graph.irrefl ((G.mem_neighborFinset v v).mp hvN)
  have hcard : S.card = d v := by
    rw [← hG]
    simp [Realization.neighborFinset, SimpleGraph.card_neighborFinset_eq_degree,
      G.degree_eq v]
  have hpos : ∀ w ∈ S, 0 < d w := by
    intro w hw
    exact pos_degree_of_mem_realizable ⟨G, hG⟩ hw
  have hlt : Fintype.card {w : V // w ≠ v} < Fintype.card V :=
    Fintype.card_subtype_lt (p := fun w : V => w ≠ v) (x := v) (by simp)
  let e := (fibreGraphInterfaceFibreGraphIso d v S).trans
    (fibreDeleteIso hvS hcard hpos)
  exact isMH_iso e (IH {w : V // w ≠ v} (residualDegree d v S) hlt)

/-- The canonical projection of a realization to its realized neighbourhood at the pivot. -/
noncomputable def realizationQuotientProjection (d : V → ℕ) (v : V) :
    Realization d → QuotientV d v :=
  fun G => ⟨G.neighborFinset v, G, rfl⟩

private theorem walkSupport_head_eq {W : Type*} {G : SimpleGraph W} {x y : W}
    (p : G.Walk x y) : p.support.head? = some x := by
  rw [List.head?_eq_some_head p.support_ne_nil]
  exact congrArg some (SimpleGraph.Walk.head_support p)

private theorem walkSupport_last_eq {W : Type*} {G : SimpleGraph W} {x y : W}
    (p : G.Walk x y) : p.support.getLast? = some y := by
  rw [List.getLast?_eq_getLast_of_ne_nil p.support_ne_nil]
  exact congrArg some (SimpleGraph.Walk.getLast_support p)

/-- Flatten a spanning path in the set-based realization fibre to the ambient realization graph,
with its quotient index retained for `thread_fibres`. -/
noncomputable def realizationFibreRunOfHamPath {d : V → ℕ} (v : V)
    (q : QuotientV d v) (x y : Fibre d v q.val)
    (hpath : HasHamPath (fibreGraph d v q.val) x y) :
    FibreRun (RealizationGraph d) (realizationQuotientProjection d v) q x.val y.val := by
  classical
  let p := Classical.choose hpath
  have hp : p.IsHamiltonian := Classical.choose_spec hpath
  refine
    { run := p.support.map Subtype.val
      hsub := ?_
      hnodup := ?_
      hcover := ?_
      hne := ?_
      hchain := ?_
      hhead := ?_
      hlast := ?_ }
  · intro z hz
    rw [List.mem_map] at hz
    obtain ⟨w, _hw, rfl⟩ := hz
    simp only [Brualdi.Ledger.fibre, Finset.mem_filter, Finset.mem_univ, true_and]
    apply Subtype.ext
    exact w.property
  · exact List.Nodup.map Subtype.val_injective hp.isPath.support_nodup
  · intro z hz
    simp only [Brualdi.Ledger.fibre, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have hz' : z.neighborFinset v = q.val := congrArg Subtype.val hz
    rw [List.mem_map]
    exact ⟨⟨z, hz'⟩, hp.mem_support ⟨z, hz'⟩, rfl⟩
  · intro hnil
    cases hs : p.support with
    | nil => exact p.support_ne_nil hs
    | cons z zs => simp [hs] at hnil
  · exact List.isChain_map_of_isChain Subtype.val (by
      intro A B hAB
      exact SimpleGraph.induce_adj.mp hAB) p.isChain_adj_support
  · rw [List.head?_map, walkSupport_head_eq p]
    rfl
  · rw [List.getLast?_map, walkSupport_last_eq p]
    rfl

/-- Package a spanning path in a realization fibre as a quotient-indexed fibre pack. -/
noncomputable def realizationFibrePackOfHamPath {d : V → ℕ} (v : V)
    (q : QuotientV d v) (x y : Fibre d v q.val)
    (hpath : HasHamPath (fibreGraph d v q.val) x y) :
    FibrePack (RealizationGraph d) (realizationQuotientProjection d v) q := by
  let x' : {G : Realization d // realizationQuotientProjection d v G = q} :=
    ⟨x.val, Subtype.ext x.property⟩
  let y' : {G : Realization d // realizationQuotientProjection d v G = q} :=
    ⟨y.val, Subtype.ext y.property⟩
  exact ⟨x', y', realizationFibreRunOfHamPath v q x y hpath⟩

/-- Reversal of a quotient-indexed fibre run. -/
noncomputable def realizationFibreRunReverse {d : V → ℕ} {v : V}
    {q : QuotientV d v} {x y : Realization d}
    (P : FibreRun (RealizationGraph d) (realizationQuotientProjection d v) q x y) :
    FibreRun (RealizationGraph d) (realizationQuotientProjection d v) q y x := by
  classical
  refine
    { run := P.run.reverse
      hsub := ?_
      hnodup := ?_
      hcover := ?_
      hne := ?_
      hchain := ?_
      hhead := ?_
      hlast := ?_ }
  · intro z hz
    exact P.hsub z (by simpa using hz)
  · rw [List.nodup_reverse]
    exact P.hnodup
  · intro z hz
    simpa using P.hcover z hz
  · simpa using P.hne
  · rw [List.isChain_reverse]
    exact P.hchain.imp fun _ _ h => h.symm
  · simpa [List.head?_reverse] using P.hlast
  · simpa [List.getLast?_reverse] using P.hhead

/-- Reverse the endpoints and run of a fibre pack. -/
noncomputable def realizationFibrePackReverse {d : V → ℕ} {v : V}
    {q : QuotientV d v}
    (P : FibrePack (RealizationGraph d) (realizationQuotientProjection d v) q) :
    FibrePack (RealizationGraph d) (realizationQuotientProjection d v) q :=
  ⟨P.exit, P.entry, realizationFibreRunReverse P.run⟩

/-- A harmless total default pack; the final thread overwrites it on every quotient vertex visited
by the quotient Hamilton path. -/
private theorem defaultRealizationFibrePack_nonempty {d : V → ℕ}
    (IH : ∀ (W : Type u) [Fintype W] [DecidableEq W] (e : W → ℕ),
      Fintype.card W < Fintype.card V → IsMaximallyHamiltonianRealizationGraph e)
    (v : V) (q : QuotientV d v) :
    Nonempty (FibrePack (RealizationGraph d) (realizationQuotientProjection d v) q) := by
  classical
  let x : Fibre d v q.val := ⟨Classical.choose q.property, Classical.choose_spec q.property⟩
  have hMH : IsMH (fibreGraph d v q.val) := fibreGraph_isMH_of_IH IH v q.val q.property
  by_cases hsingle : ∀ y : Fibre d v q.val, y = x
  · letI : Subsingleton (Fibre d v q.val) := ⟨fun a b => (hsingle a).trans (hsingle b).symm⟩
    exact ⟨realizationFibrePackOfHamPath v q x x
      ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsHamiltonian.of_subsingleton⟩⟩
  · push Not at hsingle
    obtain ⟨y, hy⟩ := hsingle
    rcases hMH with hconn | ⟨col, _hproper, hsurj, hlace⟩
    · exact ⟨realizationFibrePackOfHamPath v q x y (hconn x y hy.symm)⟩
    · obtain ⟨y, hycol⟩ := hsurj (!(col x))
      have hxycol : col x ≠ col y := by
        rw [hycol]
        exact Bool.self_ne_not _
      exact ⟨realizationFibrePackOfHamPath v q x y (hlace x y hxycol)⟩

noncomputable def defaultRealizationFibrePack {d : V → ℕ}
    (IH : ∀ (W : Type u) [Fintype W] [DecidableEq W] (e : W → ℕ),
      Fintype.card W < Fintype.card V → IsMaximallyHamiltonianRealizationGraph e)
    (v : V) (q : QuotientV d v) :
    FibrePack (RealizationGraph d) (realizationQuotientProjection d v) q :=
  Classical.choice (defaultRealizationFibrePack_nonempty IH v q)

private theorem quotientAdj_symmDiff_card {d : V → ℕ} {v : V}
    {S T : QuotientV d v} (hST : (quotientGraph d v).Adj S T) :
    (S.val ∆ T.val).card = 2 := by
  rw [quotientGraph, SimpleGraph.fromRel_adj] at hST
  rcases hST.2 with h | h
  · exact h
  · simpa [symmDiff_comm] using h

private structure RealizationOrdStep {d : V → ℕ} (v : V)
    {q q' : QuotientV d v} (x : Fibre d v q.val) where
  exit : Fibre d v q.val
  delivered : Fibre d v q'.val
  path : HasHamPath (fibreGraph d v q.val) x exit
  adj : (RealizationGraph d).Adj exit.val delivered.val

private noncomputable def realizationOrdStep {d : V → ℕ}
    (IH : ∀ (W : Type u) [Fintype W] [DecidableEq W] (e : W → ℕ),
      Fintype.card W < Fintype.card V → IsMaximallyHamiltonianRealizationGraph e)
    (v : V) {q q' : QuotientV d v} (hqq' : (quotientGraph d v).Adj q q')
    (x : Fibre d v q.val) : RealizationOrdStep (q' := q') v x :=
  Classical.choice (by
    obtain ⟨y, hy, hconn, hpath⟩ := ord v q.val q'.val
      (quotientAdj_symmDiff_card hqq') q.property q'.property
      (fibreGraph_isMH_of_IH IH v q.val q.property) x.val x.property x.property
    obtain ⟨z, hz, hyz⟩ := hconn
    exact ⟨{ exit := ⟨y, hy⟩, delivered := ⟨z, hz⟩, path := hpath, adj := hyz }⟩)

private structure RealizationAvoidStep {d : V → ℕ} (v : V)
    {q buffer : QuotientV d v} (x : Fibre d v q.val)
    (bad : Fibre d v buffer.val) where
  exit : Fibre d v q.val
  delivered : Fibre d v buffer.val
  path : HasHamPath (fibreGraph d v q.val) x exit
  adj : (RealizationGraph d).Adj exit.val delivered.val
  avoids : delivered ≠ bad

private noncomputable def realizationAvoidStep {d : V → ℕ}
    (IH : ∀ (W : Type u) [Fintype W] [DecidableEq W] (e : W → ℕ),
      Fintype.card W < Fintype.card V → IsMaximallyHamiltonianRealizationGraph e)
    (v : V) {q buffer : QuotientV d v}
    (hbufferNonbip : ¬ ∃ col : Fibre d v buffer.val → Bool,
      IsProper2Coloring (fibreGraph d v buffer.val) col)
    (hqq' : (quotientGraph d v).Adj q buffer)
    (x : Fibre d v q.val) (bad : Fibre d v buffer.val) :
    RealizationAvoidStep (buffer := buffer) v x bad :=
  Classical.choice (by
    obtain ⟨y, hy, _hconn, hpath, z, hz, hyz, hzbad⟩ :=
      obi v q.val buffer.val (quotientAdj_symmDiff_card hqq')
        q.property buffer.property hbufferNonbip
        (fibreGraph_isMH_of_IH IH v q.val q.property)
        x.val x.property x.property bad.val bad.property
    have havoid : (⟨z, hz⟩ : Fibre d v buffer.val) ≠ bad := by
      intro h
      exact hzbad (congrArg Subtype.val h)
    exact ⟨RealizationAvoidStep.mk ⟨y, hy⟩ ⟨z, hz⟩ hpath hyz havoid⟩)

private theorem listIsChain_monoOn {Q : Type*} {R S : Q → Q → Prop}
    {l : List Q} (hchain : l.IsChain R)
    (himp : ∀ {x y : Q}, x ∈ l → y ∈ l → R x y → S x y) :
    l.IsChain S := by
  induction l with
  | nil => simpa using hchain
  | cons x xs ih =>
      rw [List.isChain_cons] at hchain ⊢
      constructor
      · intro y hy
        exact himp (by simp) (by simp [List.mem_of_mem_head? hy]) (hchain.1 y hy)
      · exact ih hchain.2 fun {y z} hy hz hyz =>
          himp (by simp [hy]) (by simp [hz]) hyz

/-- Convert the support list of a quotient Hamilton walk back to the recursive quotient-walk
certificate used by the propagation builders. -/
private def qwalkOfChain {Q : Type u} {R : Q → Q → Prop} :
    ∀ {qs : List Q} {q q' : Q}, qs.IsChain R → qs.head? = some q →
      qs.getLast? = some q' → QWalk R q q'
  | [], q, _q', _hchain, hhead, _hlast => by simp at hhead
  | [x], q, q', _hchain, hhead, hlast => by
      simp at hhead hlast
      subst x
      subst q'
      exact QWalk.nil q
  | x :: y :: xs, q, q', hchain, hhead, hlast => by
      simp at hhead
      subst x
      rw [List.isChain_cons] at hchain
      have htailLast : (y :: xs).getLast? = some q' := by
        simpa [List.getLast?_cons_of_ne_nil (by simp : y :: xs ≠ [])] using hlast
      exact QWalk.cons (hchain.1 y (by simp))
        (qwalkOfChain hchain.2 (by simp) htailLast)

private theorem qwalkOfChain_support {Q : Type u} {R : Q → Q → Prop} :
    ∀ {qs : List Q} {q q' : Q} (hchain : qs.IsChain R)
      (hhead : qs.head? = some q) (hlast : qs.getLast? = some q'),
      QWalk.support (qwalkOfChain hchain hhead hlast) = qs
  | [], q, _q', _hchain, hhead, _hlast => by simp at hhead
  | [x], q, q', _hchain, hhead, hlast => by
      simp at hhead hlast
      subst x
      subst q'
      rfl
  | x :: y :: xs, q, q', hchain, hhead, hlast => by
      simp at hhead
      subst x
      rw [List.isChain_cons] at hchain
      have htailLast : (y :: xs).getLast? = some q' := by
        simpa [List.getLast?_cons_of_ne_nil (by simp : y :: xs ≠ [])] using hlast
      have htailSupport :
          QWalk.support (qwalkOfChain hchain.2
            (by simp : (y :: xs).head? = some y) htailLast) = y :: xs :=
        qwalkOfChain_support hchain.2 (by simp) htailLast
      simp [qwalkOfChain, QWalk.support, htailSupport]

private theorem qwalk_support_singleton_of_endpoint_eq {Q : Type u} {R : Q → Q → Prop}
    {q q' : Q} (w : QWalk R q q') (hnd : (QWalk.support w).Nodup)
    (hqq' : q = q') : QWalk.support w = [q'] := by
  induction w with
  | nil q => simp [QWalk.support]
  | cons hstep tail =>
      exfalso
      subst hqq'
      exact (List.nodup_cons.mp (by simpa [QWalk.support] using hnd)).1
        (QWalk.end_mem_support tail)

/-- Result of ordinary left-to-buffer propagation along a quotient walk. -/
private structure ForwardThreadResult {d : V → ℕ} (v : V) (buffer : QuotientV d v)
    {q0 : QuotientV d v}
    (w : QWalk (quotientGraph d v).Adj q0 buffer) (x0 : Fibre d v q0.val) where
  packs : ∀ q, FibrePack (RealizationGraph d) (realizationQuotientProjection d v) q
  bufferEntry : Fibre d v buffer.val
  visited : List (QuotientV d v)
  visited_sub : ∀ q ∈ visited, q ∈ QWalk.support w
  support_eq : visited ++ [buffer] = QWalk.support w
  chain : visited.IsChain fun q q' =>
    (RealizationGraph d).Adj (packs q).exit.val (packs q').entry.val
  start : q0 ≠ buffer →
    q0 ∈ visited ∧ (packs q0).entry.val = x0.val ∧ visited.head? = some q0
  empty : q0 = buffer → visited = []
  empty_entry : visited = [] → bufferEntry.val = x0.val
  last_adj : ∀ q, visited.getLast? = some q →
    (RealizationGraph d).Adj (packs q).exit.val bufferEntry.val

/-- Repeated `(ORD)` from a prescribed endpoint up to the buffer. -/
private theorem forwardThreadBuild_nonempty {V : Type u}
    [instFV : Fintype V] [instDV : DecidableEq V] {d : V → ℕ}
    (IH : ∀ (W : Type u) [Fintype W] [DecidableEq W] (e : W → ℕ),
      Fintype.card W < Fintype.card V → IsMaximallyHamiltonianRealizationGraph e)
    (v : V) :
    ∀ {q0 buffer : QuotientV d v}
      (w : QWalk (quotientGraph d v).Adj q0 buffer),
      (QWalk.support w).Nodup → ∀ x0 : Fibre d v q0.val,
      Nonempty (ForwardThreadResult v buffer w x0) := by
  classical
  intro q0 buffer w
  induction w with
  | nil q =>
      intro _hnd x0
      refine ⟨
        { packs := defaultRealizationFibrePack IH v
          bufferEntry := x0
          visited := []
          visited_sub := ?_
          support_eq := ?_
          chain := ?_
          start := ?_
          empty := ?_
          empty_entry := ?_
          last_adj := ?_ }⟩
      · intro q hq; simp at hq
      · rfl
      · simp
      · intro hne; exact False.elim (hne rfl)
      · intro _; rfl
      · intro _; rfl
      · intro q hq; simp at hq
  | @cons qStart qNext qEnd hstep tail =>
      intro hnd x0
      have tailIH :
          (QWalk.support tail).Nodup → ∀ x : Fibre d v qNext.val,
            Nonempty (ForwardThreadResult v qEnd tail x) := by
        assumption
      have hndTail : (QWalk.support tail).Nodup :=
        (List.nodup_cons.mp (by simpa [QWalk.support] using hnd)).2
      have hq0NotTail : qStart ∉ QWalk.support tail :=
        (List.nodup_cons.mp (by simpa [QWalk.support] using hnd)).1
      have hq0q' : qStart ≠ qNext := by
        intro h
        exact hq0NotTail (h ▸ QWalk.head_mem_support tail)
      have hq0Buffer : qStart ≠ qEnd := by
        intro h
        exact hq0NotTail (h ▸ QWalk.end_mem_support tail)
      let step := realizationOrdStep IH v hstep x0
      let q0pack := realizationFibrePackOfHamPath v qStart x0 step.exit step.path
      obtain ⟨tailResult⟩ := tailIH hndTail step.delivered
      refine ⟨
        { packs := Function.update tailResult.packs qStart q0pack
          bufferEntry := tailResult.bufferEntry
          visited := qStart :: tailResult.visited
          visited_sub := ?_
          support_eq := ?_
          chain := ?_
          start := ?_
          empty := ?_
          empty_entry := ?_
          last_adj := ?_ }⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · simp [QWalk.support]
        · exact List.mem_cons_of_mem _ (tailResult.visited_sub q hq)
      · simp [QWalk.support, tailResult.support_eq]
      · rw [List.isChain_cons]
        constructor
        · intro next hnext
          have hnextMem : next ∈ tailResult.visited := List.mem_of_mem_head? hnext
          have hrecNe : tailResult.visited ≠ [] := by
            intro h
            rw [h] at hnextMem
            simp at hnextMem
          have hq'Buffer : qNext ≠ qEnd := by
            intro h
            exact hrecNe (tailResult.empty h)
          have hstart := tailResult.start hq'Buffer
          have hq'next : qNext = next := by simpa [hstart.2.2] using hnext
          subst next
          rw [Function.update_self, Function.update_of_ne (Ne.symm hq0q')]
          change (RealizationGraph d).Adj q0pack.exit.val (tailResult.packs qNext).entry.val
          rw [hstart.2.1]
          exact step.adj
        · exact listIsChain_monoOn tailResult.chain fun {a b} ha hb hab => by
            rw [Function.update_of_ne (by
              rintro rfl
              exact hq0NotTail (tailResult.visited_sub a ha)),
              Function.update_of_ne (by
                rintro rfl
                exact hq0NotTail (tailResult.visited_sub b hb))]
            exact hab
      · intro _
        refine ⟨by simp, ?_, rfl⟩
        rw [Function.update_self]
        rfl
      · intro h; exact False.elim (hq0Buffer h)
      · intro h; simp at h
      · intro last hlast
        by_cases hempty : tailResult.visited = []
        · rw [hempty] at hlast
          simp only [List.getLast?_singleton, Option.some.injEq] at hlast
          subst last
          rw [Function.update_self]
          change (RealizationGraph d).Adj q0pack.exit.val tailResult.bufferEntry.val
          rw [tailResult.empty_entry hempty]
          exact step.adj
        · have hlast' : tailResult.visited.getLast? = some last := by
            simpa [List.getLast?_cons_of_ne_nil hempty] using hlast
          have hlastMem : last ∈ tailResult.visited := List.mem_of_mem_getLast? hlast'
          rw [Function.update_of_ne (by
            rintro rfl
            exact hq0NotTail (tailResult.visited_sub last hlastMem))]
          exact tailResult.last_adj last hlast'

private noncomputable def forwardThreadBuild {d : V → ℕ}
    (IH : ∀ (W : Type u) [Fintype W] [DecidableEq W] (e : W → ℕ),
      Fintype.card W < Fintype.card V → IsMaximallyHamiltonianRealizationGraph e)
    (v : V) {q0 buffer : QuotientV d v}
    (w : QWalk (quotientGraph d v).Adj q0 buffer)
    (hnd : (QWalk.support w).Nodup) (x0 : Fibre d v q0.val) :
    ForwardThreadResult v buffer w x0 :=
  Classical.choice (forwardThreadBuild_nonempty IH v w hnd x0)

/-- Result of propagation whose final hop uses `(OBI)` to avoid one prescribed buffer vertex. -/
private structure ForwardAvoidThreadResult {d : V → ℕ} (v : V)
    (buffer : QuotientV d v) {q0 : QuotientV d v}
    (w : QWalk (quotientGraph d v).Adj q0 buffer) (x0 : Fibre d v q0.val)
    (bad : Fibre d v buffer.val) where
  packs : ∀ q, FibrePack (RealizationGraph d) (realizationQuotientProjection d v) q
  bufferEntry : Fibre d v buffer.val
  visited : List (QuotientV d v)
  visited_sub : ∀ q ∈ visited, q ∈ QWalk.support w
  support_eq : visited ++ [buffer] = QWalk.support w
  chain : visited.IsChain fun q q' =>
    (RealizationGraph d).Adj (packs q).exit.val (packs q').entry.val
  start : q0 ∈ visited ∧
    (packs q0).entry.val = x0.val ∧ visited.head? = some q0
  last_adj : ∀ q, visited.getLast? = some q →
    (RealizationGraph d).Adj (packs q).exit.val bufferEntry.val
  avoids : bufferEntry ≠ bad

/-- Repeated `(ORD)` followed by `(OBI)` on the final hop into the buffer. -/
private theorem forwardAvoidThreadBuild_nonempty {V : Type u}
    [instFV : Fintype V] [instDV : DecidableEq V] {d : V → ℕ}
    (IH : ∀ (W : Type u) [Fintype W] [DecidableEq W] (e : W → ℕ),
      Fintype.card W < Fintype.card V → IsMaximallyHamiltonianRealizationGraph e)
    (v : V) :
    ∀ {q0 buffer : QuotientV d v}
      (w : QWalk (quotientGraph d v).Adj q0 buffer),
      (hbufferNonbip : ¬ ∃ col : Fibre d v buffer.val → Bool,
        IsProper2Coloring (fibreGraph d v buffer.val) col) →
      (QWalk.support w).Nodup → q0 ≠ buffer →
      ∀ (x0 : Fibre d v q0.val) (bad : Fibre d v buffer.val),
      Nonempty (ForwardAvoidThreadResult v buffer w x0 bad) := by
  classical
  intro q0 buffer w
  induction w with
  | nil q =>
      intro _hbufferNonbip _hnd hne _x0 _bad
      exact False.elim (hne rfl)
  | @cons qStart qNext qEnd hstep tail =>
      intro hbufferNonbip hnd hq0Buffer x0 bad
      have tailIH :
          (¬ ∃ col : Fibre d v qEnd.val → Bool,
            IsProper2Coloring (fibreGraph d v qEnd.val) col) →
          (QWalk.support tail).Nodup → qNext ≠ qEnd →
          ∀ (x : Fibre d v qNext.val) (bad : Fibre d v qEnd.val),
            Nonempty (ForwardAvoidThreadResult v qEnd tail x bad) := by
        assumption
      have hndTail : (QWalk.support tail).Nodup :=
        (List.nodup_cons.mp (by simpa [QWalk.support] using hnd)).2
      have hq0NotTail : qStart ∉ QWalk.support tail :=
        (List.nodup_cons.mp (by simpa [QWalk.support] using hnd)).1
      have hq0q' : qStart ≠ qNext := by
        intro h
        exact hq0NotTail (h ▸ QWalk.head_mem_support tail)
      by_cases hq'Buffer : qNext = qEnd
      · subst qNext
        let step := realizationAvoidStep IH v hbufferNonbip hstep x0 bad
        let q0pack := realizationFibrePackOfHamPath v qStart x0 step.exit step.path
        refine ⟨
          { packs := Function.update (defaultRealizationFibrePack IH v) qStart q0pack
            bufferEntry := step.delivered
            visited := [qStart]
            visited_sub := ?_
            support_eq := ?_
            chain := ?_
            start := ?_
            last_adj := ?_
            avoids := ?_ }⟩
        · intro q hq
          simp only [List.mem_singleton] at hq
          subst q
          simp [QWalk.support]
        · have htail : QWalk.support tail = [qEnd] :=
            qwalk_support_singleton_of_endpoint_eq tail hndTail rfl
          simp [QWalk.support, htail]
        · simp
        · refine ⟨by simp, ?_, by simp⟩
          rw [Function.update_self]
          rfl
        · intro last hlast
          simp only [List.getLast?_singleton, Option.some.injEq] at hlast
          subst last
          rw [Function.update_self]
          exact step.adj
        · exact step.avoids
      · let step := realizationOrdStep IH v hstep x0
        let q0pack := realizationFibrePackOfHamPath v qStart x0 step.exit step.path
        obtain ⟨tailResult⟩ := tailIH hbufferNonbip hndTail hq'Buffer step.delivered bad
        refine ⟨
          { packs := Function.update tailResult.packs qStart q0pack
            bufferEntry := tailResult.bufferEntry
            visited := qStart :: tailResult.visited
            visited_sub := ?_
            support_eq := ?_
            chain := ?_
            start := ?_
            last_adj := ?_
            avoids := tailResult.avoids }⟩
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · simp [QWalk.support]
          · exact List.mem_cons_of_mem _ (tailResult.visited_sub q hq)
        · simp [QWalk.support, tailResult.support_eq]
        · rw [List.isChain_cons]
          constructor
          · intro next hnext
            have hstart := tailResult.start
            have hq'next : qNext = next := by simpa [hstart.2.2] using hnext
            subst next
            rw [Function.update_self, Function.update_of_ne (Ne.symm hq0q')]
            change (RealizationGraph d).Adj q0pack.exit.val (tailResult.packs qNext).entry.val
            rw [hstart.2.1]
            exact step.adj
          · exact listIsChain_monoOn tailResult.chain fun {a b} ha hb hab => by
              rw [Function.update_of_ne (by
                rintro rfl
                exact hq0NotTail (tailResult.visited_sub a ha)),
                Function.update_of_ne (by
                  rintro rfl
                  exact hq0NotTail (tailResult.visited_sub b hb))]
              exact hab
        · refine ⟨by simp, ?_, rfl⟩
          rw [Function.update_self]
          rfl
        · intro last hlast
          by_cases hempty : tailResult.visited = []
          · exact False.elim (by simpa [hempty] using tailResult.start.1)
          · have hlast' : tailResult.visited.getLast? = some last := by
              simpa [List.getLast?_cons_of_ne_nil hempty] using hlast
            have hlastMem : last ∈ tailResult.visited := List.mem_of_mem_getLast? hlast'
            rw [Function.update_of_ne (by
              rintro rfl
              exact hq0NotTail (tailResult.visited_sub last hlastMem))]
            exact tailResult.last_adj last hlast'

private noncomputable def forwardAvoidThreadBuild {d : V → ℕ}
    (IH : ∀ (W : Type u) [Fintype W] [DecidableEq W] (e : W → ℕ),
      Fintype.card W < Fintype.card V → IsMaximallyHamiltonianRealizationGraph e)
    (v : V) {q0 buffer : QuotientV d v}
    (w : QWalk (quotientGraph d v).Adj q0 buffer)
    (hbufferNonbip : ¬ ∃ col : Fibre d v buffer.val → Bool,
      IsProper2Coloring (fibreGraph d v buffer.val) col)
    (hnd : (QWalk.support w).Nodup) (hq0buffer : q0 ≠ buffer)
    (x0 : Fibre d v q0.val) (bad : Fibre d v buffer.val) :
    ForwardAvoidThreadResult v buffer w x0 bad :=
  Classical.choice
    (forwardAvoidThreadBuild_nonempty IH v w hbufferNonbip hnd hq0buffer x0 bad)

private theorem ledgerQuotientAdj_of_quotientAdj {d : V → ℕ} {v : V}
    {S T : QuotientV d v} (hST : (quotientGraph d v).Adj S T) :
    quotientAdj (RealizationGraph d) (realizationQuotientProjection d v) S T := by
  classical
  have hne : S ≠ T := by
    intro h
    subst T
    exact (quotientGraph d v).loopless.irrefl S hST
  obtain ⟨G, H, hG, hH, hGH⟩ := (quotient_adjacency d v S T hne).mp hST
  refine ⟨hne, G, ?_, H, ?_, hGH⟩
  · simp only [fibre, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Subtype.ext hG
  · simp only [fibre, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Subtype.ext hH

private theorem threadedListHeadOfHead {W : Type u} {Q : Type u}
    (qs : List Q) (runs : Q → List W) {q0 : Q} {a : W}
    (hqs : qs.head? = some q0) (hrun : (runs q0).head? = some a) :
    (threadedList qs runs).head? = some a := by
  cases qs with
  | nil => simp at hqs
  | cons q qs =>
      simp at hqs
      subst q
      rw [threadedList, List.join]
      change ((runs q0) ++ (qs.map runs).flatten).head? = some a
      rw [List.head?_append, hrun]
      rfl

private theorem threadedListLastOfLast {W : Type u} {Q : Type u}
    (qs : List Q) (runs : Q → List W) {q1 : Q} {b : W}
    (hqs : qs.getLast? = some q1) (hrun : (runs q1).getLast? = some b)
    (hrun_ne : ∀ q : Q, q ∈ qs → runs q ≠ []) :
    (threadedList qs runs).getLast? = some b := by
  induction qs with
  | nil => simp at hqs
  | cons q qs ih =>
      cases qs with
      | nil =>
          simp at hqs
          subst q
          simpa [threadedList, List.join] using hrun
      | cons q' qs =>
          have htailLast : (q' :: qs).getLast? = some q1 := by
            simpa [List.getLast?_cons_of_ne_nil (by simp : q' :: qs ≠ [])] using hqs
          have htailNe : ∀ q2 : Q, q2 ∈ q' :: qs → runs q2 ≠ [] := by
            intro q2 hq2
            exact hrun_ne q2 (by simp [hq2])
          have htailThread :
              (threadedList (q' :: qs) runs).getLast? = some b :=
            ih htailLast htailNe
          have htailThreadNe : threadedList (q' :: qs) runs ≠ [] := by
            intro hnil
            rw [hnil] at htailThread
            simp at htailThread
          rw [threadedList, List.join]
          change ((runs q) ++ threadedList (q' :: qs) runs).getLast? = some b
          rw [List.getLast?_append_of_ne_nil _ htailThreadNe]
          exact htailThread

/-- Package quotient-indexed fibre runs once the explicit cross-fibre adjacency check is done. -/
private noncomputable def realizationThreadDataOfPacks {d : V → ℕ} (v : V)
    {a b : Realization d} {q0 q1 : QuotientV d v}
    (qs : List (QuotientV d v))
    (packOf : ∀ q, FibrePack (RealizationGraph d)
      (realizationQuotientProjection d v) q)
    (hchain : qs.IsChain (quotientGraph d v).Adj)
    (hnd : qs.Nodup) (hcover : ∀ q, q ∈ qs)
    (hboundary : qs.IsChain fun q q' =>
      (RealizationGraph d).Adj (packOf q).exit.val (packOf q').entry.val)
    (hhead : qs.head? = some q0) (hfirst : (packOf q0).entry.val = a)
    (hlast : qs.getLast? = some q1) (hfinal : (packOf q1).exit.val = b) :
    PivotThreadData (RealizationGraph d) a b := by
  classical
  let T : ThreadTerminals (RealizationGraph d) (realizationQuotientProjection d v) qs a b :=
    { entry := fun q => (packOf q).entry.val
      exit := fun q => (packOf q).exit.val
      hentry_fibre := fun q => by
        simp [fibre, (packOf q).entry.property]
      hexit_fibre := fun q => by
        simp [fibre, (packOf q).exit.property]
      hrun := fun q => (packOf q).run
      hfirst := by
        have hrunHead : ((packOf q0).run.run).head? = some a := by
          simpa [hfirst] using (packOf q0).run.hhead
        exact threadedListHeadOfHead qs (fun q => (packOf q).run.run) hhead hrunHead
      hlast := by
        have hrunLast : ((packOf q1).run.run).getLast? = some b := by
          simpa [hfinal] using (packOf q1).run.hlast
        exact threadedListLastOfLast qs (fun q => (packOf q).run.run) hlast hrunLast
          (fun q _ => (packOf q).run.hne)
      hcross := hboundary.imp fun {q q'} hqq' => by
        simpa [runBoundaryAdj] using FibrePack.boundary_of_adj (packOf q) (packOf q') hqq' }
  exact thread_from_terminals
    (hchain.imp fun {q q'} hqq' => ledgerQuotientAdj_of_quotientAdj hqq')
    hnd hcover T

/-- The §10.2 one-pass residual assembly, with the smaller-ground induction hypothesis explicit. -/
theorem mainLine_MH_of_IH {V : Type u} [Fintype V] [DecidableEq V] {d : V → ℕ}
    (hd : MainLine d)
    (IH : ∀ (W : Type u) [Fintype W] [DecidableEq W] (e : W → ℕ),
      Fintype.card W < Fintype.card V → IsMaximallyHamiltonianRealizationGraph e) :
    IsMaximallyHamiltonianRealizationGraph d := by
  classical
  refine Or.inl ?_
  intro G0 G1 hG01
  obtain ⟨v, hvAdm, hvNotExceptional⟩ := sbPlus hd G0 G1 hG01
  let q0 : QuotientV d v := realizationQuotientProjection d v G0
  let q1 : QuotientV d v := realizationQuotientProjection d v G1
  have hq01 : q0 ≠ q1 := by
    intro h
    exact hvAdm.1 (congrArg Subtype.val h)
  have hnotBad : ¬ (quotientGraph d v).IsCliqueSum q0 q1 := by
    intro hbad
    apply hvNotExceptional
    let h0 : HasRealizationWithNeighborSet d v (G0.neighborFinset v) := ⟨G0, rfl⟩
    let h1 : HasRealizationWithNeighborSet d v (G1.neighborFinset v) := ⟨G1, rfl⟩
    refine ⟨h0, h1, ?_⟩
    have e0 : (⟨G0.neighborFinset v, h0⟩ : QuotientV d v) = q0 := Subtype.ext rfl
    have e1 : (⟨G1.neighborFinset v, h1⟩ : QuotientV d v) = q1 := Subtype.ext rfl
    rw [e0, e1]
    exact hbad
  obtain ⟨qwalk, hqHam⟩ := (quotient_qstar d v q0 q1 hq01).mpr hnotBad
  let qs : List (QuotientV d v) := qwalk.support
  have hqsChain : qs.IsChain (quotientGraph d v).Adj := qwalk.isChain_adj_support
  have hqsNodup : qs.Nodup := hqHam.isPath.support_nodup
  have hqsCover : ∀ q : QuotientV d v, q ∈ qs := hqHam.mem_support
  have hqsHead : qs.head? = some q0 := walkSupport_head_eq qwalk
  have hqsLast : qs.getLast? = some q1 := walkSupport_last_eq qwalk

  obtain ⟨A, B, C, hABN, hBCN, hAB, hBC, hAC⟩ := hvAdm.2
  let buffer : QuotientV d v := realizationQuotientProjection d v A
  let AF : Fibre d v buffer.val := ⟨A, rfl⟩
  let BF : Fibre d v buffer.val := ⟨B, by
    change B.neighborFinset v = A.neighborFinset v
    exact hABN.symm⟩
  let CF : Fibre d v buffer.val := ⟨C, by
    change C.neighborFinset v = A.neighborFinset v
    exact (hABN.trans hBCN).symm⟩
  have hbufferNonbip : ¬ ∃ col : Fibre d v buffer.val → Bool,
      IsProper2Coloring (fibreGraph d v buffer.val) col := by
    rintro ⟨col, hcol⟩
    have hab : col AF ≠ col BF := hcol AF BF hAB
    have hbc : col BF ≠ col CF := hcol BF CF hBC
    have hac : col AF ≠ col CF := hcol AF CF hAC
    have hbool : ∀ a b c : Bool, ¬ (a ≠ b ∧ b ≠ c ∧ a ≠ c) := by decide
    exact hbool (col AF) (col BF) (col CF) ⟨hab, hbc, hac⟩
  have hbufferConnected : IsHamConnected (fibreGraph d v buffer.val) :=
    isMH_hamConnected_of_nonbip
      (fibreGraph_isMH_of_IH IH v buffer.val buffer.property) hbufferNonbip

  have hbufferMem : buffer ∈ qs := hqsCover buffer
  let left : List (QuotientV d v) := Classical.choose (List.append_of_mem hbufferMem)
  let right : List (QuotientV d v) :=
    Classical.choose (Classical.choose_spec (List.append_of_mem hbufferMem))
  have hsplit : qs = left ++ buffer :: right :=
    Classical.choose_spec (Classical.choose_spec (List.append_of_mem hbufferMem))
  clear_value left right
  have hchainSplit : (left ++ buffer :: right).IsChain (quotientGraph d v).Adj := by
    simpa [hsplit] using hqsChain
  have hndSplit : (left ++ buffer :: right).Nodup := by
    simpa [hsplit] using hqsNodup
  have hchainL : (left ++ [buffer]).IsChain (quotientGraph d v).Adj := by
    have h : ((left ++ [buffer]) ++ right).IsChain (quotientGraph d v).Adj := by
      simpa [List.append_assoc] using hchainSplit
    exact (List.isChain_append.mp h).1
  have hchainR : (buffer :: right).IsChain (quotientGraph d v).Adj :=
    (List.isChain_append.mp hchainSplit).2.1
  have hheadL : (left ++ [buffer]).head? = some q0 := by
    have h : (left ++ buffer :: right).head? = some q0 := by
      simpa [hsplit] using hqsHead
    cases left with
    | nil => simpa using h
    | cons x xs => simpa using h
  have hlastL : (left ++ [buffer]).getLast? = some buffer := by simp
  have hlastR : (buffer :: right).getLast? = some q1 := by
    have h : (left ++ buffer :: right).getLast? = some q1 := by
      simpa [hsplit] using hqsLast
    simpa [List.getLast?_append_of_ne_nil left (by simp : buffer :: right ≠ [])] using h
  let wL : QWalk (quotientGraph d v).Adj q0 buffer :=
    qwalkOfChain hchainL hheadL hlastL
  have hwLSupport : QWalk.support wL = left ++ [buffer] := by
    simpa [wL] using qwalkOfChain_support hchainL hheadL hlastL
  have ndL : (QWalk.support wL).Nodup := by
    have h : ((left ++ [buffer]) ++ right).Nodup := by
      simpa [List.append_assoc] using hndSplit
    simpa [hwLSupport] using List.Nodup.of_append_left h
  have hbufferNotLeft : buffer ∉ left := by
    intro hb
    have hcross := (List.nodup_append.mp hndSplit).2.2 buffer hb buffer (by simp)
    exact hcross rfl
  have hnotLeftOfRight : ∀ {q : QuotientV d v}, q ∈ right → q ∉ left := by
    intro q hq hleft
    have hcross := (List.nodup_append.mp hndSplit).2.2 q hleft q (by simp [hq])
    exact hcross rfl
  have hnotBufferOfRight : ∀ {q : QuotientV d v}, q ∈ right → q ≠ buffer := by
    intro q hq h
    have htailNodup : (buffer :: right).Nodup :=
      (List.nodup_append.mp hndSplit).2.1
    exact htailNodup.notMem (h ▸ hq)
  let G0F : Fibre d v q0.val := ⟨G0, rfl⟩
  let G1F : Fibre d v q1.val := ⟨G1, rfl⟩

  by_cases hright : right = []
  · subst right
    have hq1Buffer : q1 = buffer := by simpa using hlastR.symm
    have hq0Buffer : q0 ≠ buffer := by
      intro h
      exact hq01 (h.trans hq1Buffer.symm)
    let bad : Fibre d v buffer.val := ⟨G1, congrArg Subtype.val hq1Buffer⟩
    let forward := forwardAvoidThreadBuild IH v wL hbufferNonbip ndL hq0Buffer G0F bad
    have hvisited : forward.visited = left := by
      have h := forward.support_eq
      rw [hwLSupport] at h
      exact List.append_cancel_right h
    let bufferPack : FibrePack (RealizationGraph d)
        (realizationQuotientProjection d v) buffer :=
      realizationFibrePackOfHamPath v buffer forward.bufferEntry bad
        (hbufferConnected forward.bufferEntry bad forward.avoids)
    let packOf : ∀ q : QuotientV d v,
        FibrePack (RealizationGraph d) (realizationQuotientProjection d v) q :=
      fun q => if q ∈ left then forward.packs q
        else if h : q = buffer then h.symm ▸ bufferPack else forward.packs q
    have hpackLeft : ∀ {q : QuotientV d v}, q ∈ left → packOf q = forward.packs q := by
      intro q hq
      simp [packOf, hq]
    have hpackBuffer : packOf buffer = bufferPack := by
      simp [packOf, hbufferNotLeft]
    have hq0Left : q0 ∈ left := by simpa [hvisited] using forward.start.1
    have hfirst : (packOf q0).entry.val = G0 := by
      rw [hpackLeft hq0Left]
      exact forward.start.2.1
    have hfinal : (packOf q1).exit.val = G1 := by
      rw [hq1Buffer, hpackBuffer]
      change bad.val = G1
      simp [bad, G1F]
    have hleftChain : left.IsChain fun q q' =>
        (RealizationGraph d).Adj (packOf q).exit.val (packOf q').entry.val := by
      have h := forward.chain
      rw [hvisited] at h
      exact listIsChain_monoOn h fun {q q'} hq hq' hAdj => by
        rw [hpackLeft hq, hpackLeft hq']
        exact hAdj
    have hboundary : qs.IsChain fun q q' =>
        (RealizationGraph d).Adj (packOf q).exit.val (packOf q').entry.val := by
      have hedge : (left ++ [buffer]).IsChain fun q q' =>
          (RealizationGraph d).Adj (packOf q).exit.val (packOf q').entry.val := by
        rw [List.isChain_append]
        refine ⟨hleftChain, by simp, ?_⟩
        intro q hq q' hq'
        simp only [List.head?_singleton, Option.mem_def, Option.some.injEq] at hq'
        subst q'
        have hqmem : q ∈ left := List.mem_of_mem_getLast? hq
        rw [hpackLeft hqmem, hpackBuffer]
        exact forward.last_adj q (by simpa [hvisited] using hq)
      simpa [hsplit] using hedge
    exact hasHamPath_of_pivotThreadData
      (realizationThreadDataOfPacks v qs packOf hqsChain hqsNodup hqsCover
        hboundary hqsHead hfirst hqsLast hfinal)
  · have hrevChain : ((buffer :: right).reverse).IsChain (quotientGraph d v).Adj := by
      rw [List.isChain_reverse]
      exact hchainR.imp fun {q q'} hqq' => hqq'.symm
    have hheadRev : ((buffer :: right).reverse).head? = some q1 := by
      rw [List.head?_reverse]
      exact hlastR
    have hlastRev : ((buffer :: right).reverse).getLast? = some buffer := by
      simp [List.getLast?_reverse]
    let wR : QWalk (quotientGraph d v).Adj q1 buffer :=
      qwalkOfChain hrevChain hheadRev hlastRev
    have hwRSupport : QWalk.support wR = (buffer :: right).reverse := by
      simpa [wR] using qwalkOfChain_support hrevChain hheadRev hlastRev
    have htailNodup : (buffer :: right).Nodup :=
      (List.nodup_append.mp hndSplit).2.1
    have ndR : (QWalk.support wR).Nodup := by
      rw [hwRSupport, List.nodup_reverse]
      exact htailNodup
    have hq1Right : q1 ∈ right := by
      have hlastRight : right.getLast? = some q1 := by
        cases right with
        | nil => exact absurd rfl hright
        | cons q qs => simpa using hlastR
      exact List.mem_of_mem_getLast? hlastRight
    have hq1Buffer : q1 ≠ buffer := hnotBufferOfRight hq1Right
    let forward := forwardThreadBuild IH v wL ndL G0F
    have hvisitedF : forward.visited = left := by
      have h := forward.support_eq
      rw [hwLSupport] at h
      exact List.append_cancel_right h
    let backward := forwardAvoidThreadBuild IH v wR hbufferNonbip ndR hq1Buffer
      G1F forward.bufferEntry
    have hvisitedB : backward.visited = right.reverse := by
      have h := backward.support_eq
      rw [hwRSupport] at h
      have h' : backward.visited ++ [buffer] = right.reverse ++ [buffer] := by
        simpa using h
      exact List.append_cancel_right h'
    have hbufferDistinct : forward.bufferEntry ≠ backward.bufferEntry :=
      fun h => backward.avoids h.symm
    let bufferPack : FibrePack (RealizationGraph d)
        (realizationQuotientProjection d v) buffer :=
      realizationFibrePackOfHamPath v buffer forward.bufferEntry backward.bufferEntry
        (hbufferConnected forward.bufferEntry backward.bufferEntry hbufferDistinct)
    let backwardPack : ∀ q : QuotientV d v,
        FibrePack (RealizationGraph d) (realizationQuotientProjection d v) q :=
      fun q => realizationFibrePackReverse (backward.packs q)
    let packOf : ∀ q : QuotientV d v,
        FibrePack (RealizationGraph d) (realizationQuotientProjection d v) q :=
      fun q => if q ∈ left then forward.packs q
        else if h : q = buffer then h.symm ▸ bufferPack else backwardPack q
    have hpackLeft : ∀ {q : QuotientV d v}, q ∈ left → packOf q = forward.packs q := by
      intro q hq
      simp [packOf, hq]
    have hpackBuffer : packOf buffer = bufferPack := by
      simp [packOf, hbufferNotLeft]
    have hpackRight : ∀ {q : QuotientV d v}, q ∈ right → packOf q = backwardPack q := by
      intro q hq
      simp [packOf, hnotLeftOfRight hq, hnotBufferOfRight hq]
    have hfirst : (packOf q0).entry.val = G0 := by
      by_cases hleftEmpty : left = []
      · have hq0Buffer : q0 = buffer := by
          have h : buffer = q0 := by simpa [hleftEmpty] using hheadL
          exact h.symm
        have hvisitedEmpty : forward.visited = [] := by simpa [hvisitedF, hleftEmpty]
        rw [hq0Buffer, hpackBuffer]
        exact forward.empty_entry hvisitedEmpty
      · have hq0Buffer : q0 ≠ buffer := by
          intro h
          have hq0Left : q0 ∈ left := by
            cases left with
            | nil => contradiction
            | cons q qs =>
                simp at hheadL
                simpa [hheadL]
          exact hbufferNotLeft (h ▸ hq0Left)
        have hstart := forward.start hq0Buffer
        have hq0Left : q0 ∈ left := by simpa [hvisitedF] using hstart.1
        rw [hpackLeft hq0Left]
        exact hstart.2.1
    have hfinal : (packOf q1).exit.val = G1 := by
      rw [hpackRight hq1Right]
      exact backward.start.2.1
    have hleftChain : left.IsChain fun q q' =>
        (RealizationGraph d).Adj (packOf q).exit.val (packOf q').entry.val := by
      have h := forward.chain
      rw [hvisitedF] at h
      exact listIsChain_monoOn h fun {q q'} hq hq' hAdj => by
        rw [hpackLeft hq, hpackLeft hq']
        exact hAdj
    have hrightChain : right.IsChain fun q q' =>
        (RealizationGraph d).Adj (packOf q).exit.val (packOf q').entry.val := by
      have hrev : right.reverse.IsChain fun q q' =>
          (RealizationGraph d).Adj (backward.packs q).exit.val
            (backward.packs q').entry.val := by
        simpa [hvisitedB] using backward.chain
      have h : right.IsChain fun q q' =>
          (RealizationGraph d).Adj (backwardPack q).exit.val
            (backwardPack q').entry.val := by
        rw [← List.reverse_reverse right, List.isChain_reverse]
        exact hrev.imp fun {q q'} hqq' => by
          simpa [backwardPack, realizationFibrePackReverse] using hqq'.symm
      exact listIsChain_monoOn h fun {q q'} hq hq' hAdj => by
        rw [hpackRight hq, hpackRight hq']
        exact hAdj
    have hleftBufferChain : (left ++ [buffer]).IsChain fun q q' =>
        (RealizationGraph d).Adj (packOf q).exit.val (packOf q').entry.val := by
      rw [List.isChain_append]
      refine ⟨hleftChain, by simp, ?_⟩
      intro q hq q' hq'
      simp only [List.head?_singleton, Option.mem_def, Option.some.injEq] at hq'
      subst q'
      have hqmem : q ∈ left := List.mem_of_mem_getLast? hq
      rw [hpackLeft hqmem, hpackBuffer]
      exact forward.last_adj q (by simpa [hvisitedF] using hq)
    have hboundary : qs.IsChain fun q q' =>
        (RealizationGraph d).Adj (packOf q).exit.val (packOf q').entry.val := by
      have hedge : ((left ++ [buffer]) ++ right).IsChain fun q q' =>
          (RealizationGraph d).Adj (packOf q).exit.val (packOf q').entry.val := by
        rw [List.isChain_append]
        refine ⟨hleftBufferChain, hrightChain, ?_⟩
        intro q hq q' hq'
        have hqBuffer : q = buffer := by
          have h : buffer = q := by simpa using hq
          exact h.symm
        subst q
        have hq'mem : q' ∈ right := List.mem_of_mem_head? hq'
        rw [hpackBuffer, hpackRight hq'mem]
        have hlastVisited : backward.visited.getLast? = some q' := by
          simpa [hvisitedB, List.getLast?_reverse] using hq'
        change (RealizationGraph d).Adj backward.bufferEntry.val
          (backward.packs q').exit.val
        exact (backward.last_adj q' hlastVisited).symm
      simpa [hsplit, List.append_assoc] using hedge
    exact hasHamPath_of_pivotThreadData
      (realizationThreadDataOfPacks v qs packOf hqsChain hqsNodup hqsCover
        hboundary hqsHead hfirst hqsLast hfinal)

/-! ## 6. The main theorem

Added 2026-08-16. Until today **the general theorem had no Lean statement at all**: `TheoremOne`
proves `IsMaximallyHamiltonianRealizationGraph` only under `IsTriangleFreeRealizationGraph`, and this
module stated the one-pass route's *ingredients* and stopped. That is a statements-first violation —
the discipline is a formal statement at the graph boundary from the start — and it also meant no
single declaration's axiom trace could answer "is the main theorem machine-checked?"; one had to
reason about seven separate obligations and an assembly nobody had written down.

These two statements give the development a top. Their proofs use one strong induction on the
ground order; the `MainLine` corollary is then immediate.
-/

/-- A non-bipartite graph with exactly three vertices is complete, hence Hamilton-connected.

The hypotheses are phrased in the realization-graph vocabulary used by the ordered case split
below.  The three named realizations exhaust the vertex set.  If a pair were nonadjacent, colouring
that pair alike and the remaining realization oppositely would be a proper two-colouring.  Thus all
distinct pairs are adjacent, and the path through the third realization is Hamiltonian. -/
private theorem k3Base_maximally_hamiltonian {V : Type u} [Fintype V] [DecidableEq V]
    {d : V → ℕ} (hnb : ¬ IsBipartiteRealizationGraph d) (hk3 : ¬ NotK3Base d) :
    IsMaximallyHamiltonianRealizationGraph d := by
  classical
  simp only [NotK3Base, not_not] at hk3
  obtain ⟨A, B, C, hAB, hBC, hAC, hcover⟩ := hk3
  have hadj : ∀ X Y : Realization d, X ≠ Y → (RealizationGraph d).Adj X Y := by
    intro X Y hXY
    by_contra hnotAdj
    have hthird : ∃ Z : Realization d, X ≠ Z ∧ Y ≠ Z ∧
        ∀ Q : Realization d, Q = X ∨ Q = Y ∨ Q = Z := by
      rcases hcover X with hXA | hXB | hXC <;>
        rcases hcover Y with hYA | hYB | hYC
      · exact (hXY (hXA.trans hYA.symm)).elim
      · refine ⟨C, by simpa [hXA] using hAC, by simpa [hYB] using hBC, ?_⟩
        intro Q
        rcases hcover Q with h | h | h <;> simp_all
      · refine ⟨B, by simpa [hXA] using hAB, by simpa [hYC] using hBC.symm, ?_⟩
        intro Q
        rcases hcover Q with h | h | h <;> simp_all
      · refine ⟨C, by simpa [hXB] using hBC, by simpa [hYA] using hAC, ?_⟩
        intro Q
        rcases hcover Q with h | h | h <;> simp_all
      · exact (hXY (hXB.trans hYB.symm)).elim
      · refine ⟨A, by simpa [hXB] using hAB.symm, by simpa [hYC] using hAC.symm, ?_⟩
        intro Q
        rcases hcover Q with h | h | h <;> simp_all
      · refine ⟨B, by simpa [hXC] using hBC.symm, by simpa [hYA] using hAB, ?_⟩
        intro Q
        rcases hcover Q with h | h | h <;> simp_all
      · refine ⟨A, by simpa [hXC] using hAC.symm, by simpa [hYB] using hAB.symm, ?_⟩
        intro Q
        rcases hcover Q with h | h | h <;> simp_all
      · exact (hXY (hXC.trans hYC.symm)).elim
    obtain ⟨Z, hXZ, hYZ, hall⟩ := hthird
    apply hnb
    refine ⟨fun Q => decide (Q = Z), ?_⟩
    intro P Q hPQ
    rcases hall P with rfl | rfl | rfl <;>
      rcases hall Q with rfl | rfl | rfl
    · exact (hPQ.ne rfl).elim
    · exact (hnotAdj hPQ).elim
    · simp [hXZ]
    · exact (hnotAdj hPQ.symm).elim
    · exact (hPQ.ne rfl).elim
    · simp [hYZ]
    · simp [hXZ]
    · simp [hYZ]
    · exact (hPQ.ne rfl).elim
  have nodup_isChain : ∀ {l : List (Realization d)}, l.Nodup →
      l.IsChain (RealizationGraph d).Adj := by
    intro l hl
    induction l with
    | nil => exact .nil
    | cons X xs ih =>
        cases xs with
        | nil => exact .singleton X
        | cons Y ys =>
            exact .cons_cons
              (hadj X Y (fun hXY => (List.nodup_cons.mp hl).1 (by simp [hXY])))
              (ih (List.nodup_cons.mp hl).2)
  refine Or.inl ?_
  intro X Y hXY
  let route : List (Realization d) :=
    X :: (((Finset.univ.erase X).erase Y).toList ++ [Y])
  have hrouteNe : route ≠ [] := by simp [route]
  have hrouteNodup : route.Nodup := by
    rw [show route = X :: (((Finset.univ.erase X).erase Y).toList ++ [Y]) from rfl,
      List.nodup_cons]
    refine ⟨by simp [hXY], ?_⟩
    rw [List.nodup_append]
    refine ⟨Finset.nodup_toList _, by simp, ?_⟩
    intro P hP Q hQ hPQ
    simp only [List.mem_singleton] at hQ
    subst Q
    subst P
    simpa using hP
  have hrouteChain : route.IsChain (RealizationGraph d).Adj :=
    nodup_isChain hrouteNodup
  have hhead : route.head hrouteNe = X := by simp [route]
  have hlast : route.getLast hrouteNe = Y := by simp [route]
  let p : (RealizationGraph d).Walk X Y :=
    (SimpleGraph.Walk.ofSupport route hrouteNe hrouteChain).copy hhead hlast
  refine ⟨p, ?_⟩
  have hpPath : p.IsPath := SimpleGraph.Walk.IsPath.mk' (by
    simpa [p, SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_ofSupport] using hrouteNodup)
  apply hpPath.isHamiltonian_of_mem
  intro Z
  have hZ : Z ∈ route := by
    by_cases hZX : Z = X
    · simp [route, hZX]
    by_cases hZY : Z = Y
    · simp [route, hZY]
    · simp [route, hZX, hZY]
  simpa [p, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_ofSupport] using hZ

/-- **Theorem 10.1, the main theorem** (`paper/SEC_ASSEMBLY.md` §10):
*every realization graph is Hamilton-laceable when bipartite and Hamilton-connected otherwise.*

`IsMaximallyHamiltonianRealizationGraph d` unfolds to `IsMH (RealizationGraph d)`, and `IsMH` is
exactly that disjunction — `IsHamConnected`, or a surjective proper 2-colouring together with
`IsHamLaceable` for it — so this statement is the prose theorem and not a paraphrase of it.

**Status.** Machine-checked as of 2026-08-19, relative to the cited axioms below. It has NOT yet had
decoupled adversaries on the assembly itself, so it is not at the standard the gauntlet asks for and
is certainly not referee-final. Milestone calls are Jeff's. An order-eight computational seal of the
same construction exists independently (`SEAL_ORDER8_2026-08-14.md`) and is honest about what it
skipped.

**What it rests on**, read off this declaration's own axiom trace rather than from memory:
`flipGraph_connected` and `invariantFree_nonbip_has_triangle` (the companion paper),
`barrus_theorem9_bipartite_iff_triangleFree` and `barrus_theorem9_bipartite_classification`
(Barrus 2016 Theorem 9, two directions), `realizationGraph_preconnected` (Fulkerson–Hoffman–McAndrew),
`erdos_gallai_sufficiency`, `invariantPosition_forces_block` (Brualdi, *Combinatorial Matrix Classes*
Theorem 3.4.1). The finite five-vertex colouring check is carried by kernel reduction.

**This docstring previously named Schvöllner–Pastine**, which stopped being a dependency when §4 was
proved directly rather than cited, and claimed an adversary-and-computation status the declaration
could not have had while it was still a `sorry`. Both were corrected on 2026-08-19. The lesson is the
cheap one: a docstring that lists dependencies from memory goes stale silently, while a trace cannot.

**Tyshkevich is NOT among the cited axioms.** §4 cites the decomposition theorem for canonicity, and
this induction never needs it: it asks only whether `d` admits some nontrivial composition and applies
Theorem 4.2 to whichever witness it is handed. -/
theorem realizationGraph_maximally_hamiltonian {V : Type u} [Fintype V] [DecidableEq V]
    (d : V → ℕ) :
    IsMaximallyHamiltonianRealizationGraph d := by
  classical
  refine Nat.strong_induction_on (p := fun n =>
    ∀ (W : Type u) [Fintype W] [DecidableEq W] (e : W → ℕ),
      Fintype.card W = n → IsMaximallyHamiltonianRealizationGraph e)
    (Fintype.card V) ?_ V d rfl
  intro n IH W _ _ e hWcard
  have smallerIH : ∀ (Z : Type u) [Fintype Z] [DecidableEq Z] (f : Z → ℕ),
      Fintype.card Z < Fintype.card W → IsMaximallyHamiltonianRealizationGraph f := by
    intro Z _ _ f hlt
    exact IH (Fintype.card Z) (by simpa [hWcard] using hlt) Z f rfl
  by_cases hgraphical : Nonempty (Realization e)
  · by_cases hbip : IsBipartiteRealizationGraph e
    · exact theorem_one e ((barrus_theorem9_bipartite_iff_triangleFree e).mp hbip)
    by_cases hdec : TyshkevichDecomposable e
    · exact isMH_of_tyshkevichDecomposable_of_IH hdec smallerIH
    by_cases hnotK3 : NotK3Base e
    · apply mainLine_MH_of_IH
      · refine ⟨hdec, ?_, hnotK3⟩
        intro hcolorable
        obtain ⟨coloring⟩ := hcolorable
        apply hbip
        refine ⟨fun G => finTwoEquiv (coloring G), ?_⟩
        intro G H hGH hsame
        exact coloring.valid hGH (finTwoEquiv.injective hsame)
      · exact smallerIH
    · exact k3Base_maximally_hamiltonian hbip hnotK3
  · refine Or.inl ?_
    intro G _ _
    exact (hgraphical ⟨G⟩).elim

/-- **Corollary 10.2 (homogeneous traceability).**  Every realization graph has a Hamilton path
beginning at any prescribed realization.

This is the weaker statement that Hladik and Fink's Theorem 1.1 asserts, obtained here from the
main theorem in four lines.  It is stated because Section 11.1 claims every numbered result of
Sections 3 to 10 is machine-checked, and until 2026-08-27 this corollary was the one exception --
true and correctly proved on the page, but with no declaration behind it.

The two branches are the printed ones.  Where `RealizationGraph d` is Hamilton-connected any other
realization serves as an endpoint; where it is laceable, **surjectivity of the proper colouring is
what supplies one in the opposite class**, which is why `IsMH` carries that guard.  The one-vertex
case is `Walk.nil`, Hamiltonian by `IsHamiltonian.of_subsingleton`. -/
theorem realizationGraph_homogeneously_traceable {V : Type u} [Fintype V] [DecidableEq V]
    (d : V → ℕ) (G : Realization d) :
    letI := Classical.decEq (Realization d)
    ∃ H : Realization d, HasHamPath (RealizationGraph d) G H := by
  classical
  by_cases hsub : Subsingleton (Realization d)
  · haveI := hsub
    exact ⟨G, SimpleGraph.Walk.nil, SimpleGraph.Walk.IsHamiltonian.of_subsingleton⟩
  · have hne : ∃ H : Realization d, H ≠ G := by
      by_contra hall
      push_neg at hall
      exact hsub ⟨fun a b => (hall a).trans (hall b).symm⟩
    obtain ⟨H₀, hH₀⟩ := hne
    have hmh := realizationGraph_maximally_hamiltonian d
    rcases hmh with hconn | ⟨col, _hproper, hsurj, hlace⟩
    · exact ⟨H₀, hconn G H₀ (Ne.symm hH₀)⟩
    · obtain ⟨H, hH⟩ := hsurj (!col G)
      refine ⟨H, hlace G H ?_⟩
      rw [hH]
      exact (Bool.not_ne_self (col G)).symm

/-- **The residual case that the one-pass assembly actually proves** (`SEC_ASSEMBLY.md` §10.2–10.3).

§10.1 splits into four branches: bipartite (Theorem 3.1, by classification),
Tyshkevich-decomposable (Corollary 4.3, propagating from factors with fewer ground vertices), the
`K₃` base graph (directly), and this one — `d` indecomposable, non-bipartite, and not `K₃`, which
is exactly `MainLine d`.

Separating this from `realizationGraph_maximally_hamiltonian` is deliberate: the other three branches
are handled by classification, decomposition, or the base case, while THIS is where
`separator_buffer`, `sbPlus`, `qstar` and `ord` are consumed.

**Its axiom trace is NOT sharper than the main theorem's, and cannot be.** The docstring claimed
otherwise until 2026-08-19, when an adversary measured the two and found them byte-identical. The
reason is structural rather than accidental: this statement carries no induction hypothesis, so any
proof of it must obtain one, and the only source is the general theorem — which charges everything.
Rerouting the body through `mainLine_MH_of_IH` was tried and changed nothing.

**The declaration that does answer "is the one-pass route machine-checked?" is `mainLine_MH_of_IH`**,
which takes the induction hypothesis as a parameter and whose trace omits
`barrus_theorem9_bipartite_classification`. Ask that one. -/
theorem mainLine_maximally_hamiltonian {V : Type u} [Fintype V] [DecidableEq V]
    {d : V → ℕ} (hd : MainLine d) :
    IsMaximallyHamiltonianRealizationGraph d := by
  -- `hd` is deliberately unused: the general theorem is unconditional, so it already covers the
  -- main line.  Routing through `mainLine_MH_of_IH` instead was tried on 2026-08-19 to make `hd`
  -- load-bearing, and it changes NOTHING in the trace -- the induction hypothesis it then needs is
  -- the general theorem, which charges every axiom anyway.  See the docstring: no statement of this
  -- shape can have a sharper trace, and the simpler proof is the honest one.
  exact realizationGraph_maximally_hamiltonian d

end Brualdi.RealizationGraph.SBPlusOrd
