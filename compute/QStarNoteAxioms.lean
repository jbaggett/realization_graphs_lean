/-
Q* NOTE — axiom generator for the claim the note makes to its recipients.

Run:  cd lean && (ulimit -v 67108864; LEAN_NUM_THREADS=6 \
        lake env lean ../topics/flipgraphs/realization/compute/QStarNoteAxioms.lean)

WHY THIS FILE EXISTS.  The standalone note tells Hladik and Fink: "Every numbered result below has a
Lean 4 declaration whose axiom trace is the ambient foundations and nothing further."  That is the
one claim in the note a recipient can test, and it is addressed to people who might.  On 2026-08-20
only TWO of the note's declarations -- `qstar` and `crossingLemma` -- were in the lane's axiom baseline.

## THE SURFACE, AND A CORRECTION MADE THE SAME NIGHT

A first version of this file audited THIRTEEN declarations, taken from
`LEAN_PAPER_CORRESPONDENCE_2026-08-20.md`, which lists one representative declaration per manuscript
result.  A decoupled adversary on the note found that this is NARROWER THAN THE CLAIM: a
representative is not the whole of a multi-part result.  `card_singleDecrements_insert_erase_Iic`
carries only the COUNT in Lemma 7.1(a), not (b), (c) or (d); the coordinate lemmas carry only parts
(i) and (ii) of Lemma 7.2; and `cliqueSum_exists_incomparable_galeMaximal` carries only the
incomparability clause of Corollary 7.9 -- not the Hamilton-connectivity clause, which is the very
statement that generalizes the recipients' Theorem 2.1.

`results/2026-08-17_qstar_note_axiom_audit.md` had already established the correct surface, at 29
declarations, and this file should have started from it.  It now covers that surface, the coordinate
lemmas and faithfulness bridges the audit did not list, and the seven carriers added on 2026-08-23 --
one or more rows per numbered result, not one row per result.  A gate narrower than the sentence it
certifies is worse than no gate, because it reads as coverage.

`ulimit -v` takes KIBIBYTES.  64 GiB is 67108864; 68719476736 is 64 TiB and disables the guard.

NO `open`, PINNED PATH, per the root `CLAUDE.md`: `#print axioms` prints a name qualified or
unqualified depending on the `open` context, and Lean prefixes each line with `file:line:col`, so the
checker strips that prefix and asserts the declaration count.

LEMMA 7.4 AND COROLLARY 7.9, added 2026-08-23 after a prose-against-Lean adversary.  Two gaps, both
in the direction of the gate being narrower than the sentence it certifies.  (1) The obstruction half
of Lemma 7.4 was `private`, so `#print axioms` could not name it from outside the module; it was
covered only transitively through `qstar`.  It is public now and traced directly.  (2) Corollary 7.9
is PRINTED with a Gale-greatest member, while every declaration here hypothesized the principal
equation `X in F <-> (X.card = k and GaleLE X M)` instead.  CORRECTED LATER THE SAME DAY: the first
version of this note called the equation "a strictly stronger hypothesis", which is backwards.  Under
shiftedness the printed hypotheses IMPLY the equation -- that is exactly what the new proof does --
while the equation does not imply them, since it never forces `M.card = k` and so never forces
`M` into `F`.  The printed hypothesis is the stronger one.  What was missing was therefore not
generality but the BRIDGE: no declaration combined that derivation with the printed conclusion, so a
reader checking "is Corollary 7.9 as printed machine-checked?" had nothing to point at.
`qstar_hamConnected_of_galeGreatest` closes that and is traced too.

An earlier version of this paragraph asserted that the note "discloses" the Lemma 7.4 gap.  It did
not; the note says nothing of the kind.  A comment that reports what another document says is a claim
like any other, and that one was false.
-/
import Realization.QStar

#print axioms Brualdi.RealizationGraph.QStar.galeLE_iff_pointwise
-- FAITHFULNESS BRIDGES, added 2026-08-22.  A cold reader pointed out that Theorem 7.6 asserts a
-- coordinate yFamily is a SHIFTED family and the surface did not carry that theorem, and that Sections
-- 7.5-7.6 print the classification in ambient coordinates on [n] while the Lean states it over
-- `usedGround F`.  The certificate the recipients are invited to test now covers all three.
#print axioms Brualdi.RealizationGraph.QStar.yFamily_isShifted
#print axioms Brualdi.RealizationGraph.QStar.usedGround_downwardClosed
#print axioms Brualdi.RealizationGraph.QStar.initialSegment_downwardClosed
#print axioms Brualdi.RealizationGraph.QStar.card_singleDecrements_insert_erase_Iic
#print axioms Brualdi.RealizationGraph.QStar.singleDecrements_insert_erase_Iic
#print axioms Brualdi.RealizationGraph.QStar.lemma7_1b_one_decrement
#print axioms Brualdi.RealizationGraph.QStar.lemma7_1c_two_decrements
#print axioms Brualdi.RealizationGraph.QStar.four_le_card_singleDecrements_of_two_outside
#print axioms Brualdi.RealizationGraph.QStar.four_distinct_decrements_of_two_outside
-- CLAUSE-LEVEL CARRIERS, added 2026-08-23.  The adversary that read every printed clause against
-- its Lean statement found five more places where the gate held a GENERIC ingredient while the note
-- prints an EXACT statement: Lemma 7.2(iii)'s adjacency (`lemma1_bottom` gives only `F = {m1,m2}`,
-- and its own comment says "and they are adjacent"), Lemma 7.1(d) over `[n]` rather than the generic
-- bound, and the three opening clauses of Lemma 7.10 -- involution, cardinality, rank bijection.
#print axioms Brualdi.RealizationGraph.QStar.exists_adjacent_gale_bottom_pair
#print axioms Brualdi.RealizationGraph.QStar.lemma7_1d_four_decrements
#print axioms Brualdi.RealizationGraph.QStar.dualSet_dualSet
#print axioms Brualdi.RealizationGraph.QStar.card_dualSet
#print axioms Brualdi.RealizationGraph.QStar.dualSetRankEquiv
#print axioms Brualdi.RealizationGraph.QStar.lemma1_bottom
#print axioms Brualdi.RealizationGraph.QStar.galeLeast_eq_initialSegment
#print axioms Brualdi.RealizationGraph.QStar.galeSecondLeast_eq_secondInitialSegment
#print axioms Brualdi.RealizationGraph.QStar.exchangeGraph_not_bipartite_of_three_le
#print axioms Brualdi.RealizationGraph.QStar.hamPath_of_cliqueSum_of_other_pair
#print axioms Brualdi.RealizationGraph.QStar.no_hamPath_of_cliqueSum
#print axioms Brualdi.RealizationGraph.QStar.qstar_hamConnected_of_galeGreatest
#print axioms Brualdi.RealizationGraph.QStar.lemma2_universalPair_is_galeLeast
#print axioms Brualdi.RealizationGraph.QStar.cliqueSum_universalPair_coordinates
#print axioms Brualdi.RealizationGraph.QStar.lemma3_two_arms
#print axioms Brualdi.RealizationGraph.QStar.lemma3_arms_are_contiguous
#print axioms Brualdi.RealizationGraph.QStar.yFamily_isCliqueSum
#print axioms Brualdi.RealizationGraph.QStar.qstar
#print axioms Brualdi.RealizationGraph.QStar.not_yFamily_isHamConnected
#print axioms Brualdi.RealizationGraph.QStar.cliqueSum_exists_incomparable_galeMaximal
#print axioms Brualdi.RealizationGraph.QStar.qstar_no_exception_of_principal
#print axioms Brualdi.RealizationGraph.QStar.qstar_principal_isHamConnected
#print axioms Brualdi.RealizationGraph.QStar.galeLE_dualSet_iff
#print axioms Brualdi.RealizationGraph.QStar.card_dualSet_symmDiff
#print axioms Brualdi.RealizationGraph.QStar.mem_iff_dualElem_notMem_dualSet
#print axioms Brualdi.RealizationGraph.QStar.subset_iff_dualSet_subset
#print axioms Brualdi.RealizationGraph.QStar.isShifted_dualFamily
#print axioms Brualdi.RealizationGraph.QStar.exchangeGraph_dualIso
#print axioms Brualdi.RealizationGraph.QStar.image_layerAbove_dualSet
#print axioms Brualdi.RealizationGraph.QStar.image_layerBelow_dualSet
#print axioms Brualdi.RealizationGraph.QStar.isCliqueSum_dual_iff
#print axioms Brualdi.RealizationGraph.QStar.innerArm_dual_iff_outerArm
#print axioms Brualdi.RealizationGraph.QStar.outerArm_dual_iff_innerArm
#print axioms Brualdi.RealizationGraph.QStar.image_dualSet_yInnerArm
#print axioms Brualdi.RealizationGraph.QStar.image_dualSet_yOuterArm
#print axioms Brualdi.RealizationGraph.QStar.crossingLemma
