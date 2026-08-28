#!/usr/bin/env python3
"""check_qstar_note_axioms.py — GATE the one claim the Q* note makes to its recipients.

The standalone note tells Hladik and Fink:

    "Every numbered result below has a Lean 4 declaration whose axiom trace is the ambient
     foundations and nothing further: no `sorry`, no cited axioms, and no `native_decide`."

That is the sentence a recipient can test, so it should not rest on anyone's memory.  Until
2026-08-20 only `qstar` and `crossingLemma` were in the lane's axiom baseline. A first version of this
gate audited thirteen declarations, one representative per result, which a decoupled adversary showed
is narrower than the sentence it certifies -- a representative is not the whole of a multi-part
result. It now covers the 29-declaration surface of results/2026-08-17_qstar_note_axiom_audit.md, the
coordinate lemmas and faithfulness bridges, and -- from 2026-08-23 -- direct carriers for Lemma 7.4
and for Corollary 7.9 in its printed greatest-member form.  This runs `QStarNoteAxioms.lean` and
checks every one.

METHOD, per the root CLAUDE.md.  Never grep for `native_decide` or `Lean.ofReduceBool`: in this
toolchain the certificate axiom is named `<decl>._native.native_decide.ax_1_1` and the literal
string `Lean.ofReduceBool` never appears, so a source grep errs in BOTH directions.  Parse each
`'name' depends on axioms: [...]` list and subtract {propext, Classical.choice, Quot.sound};
whatever remains is a cited axiom or a certificate, and either one fails this gate.  Strip Lean's
`file:line:col` prefix and assert the declaration COUNT, because the output is not canonical.
"""
import re, subprocess, sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[4]
GEN  = REPO / "topics/flipgraphs/realization/compute/QStarNoteAxioms.lean"
LEAN = REPO / "lean"
FOUNDATIONS = {"propext", "Classical.choice", "Quot.sound"}

# one or more rows per numbered result of the note; the count is asserted, not inferred
EXPECT = {
    'galeLE_iff_pointwise'                          : 'Section 7.1, the Gale order itself',
    'yFamily_isShifted'                          : 'Section 7.5, that a yFamily IS a shifted family',
    'usedGround_downwardClosed'                     : 'Sections 7.5-7.6, the ambient-coordinate reading',
    'initialSegment_downwardClosed'                 : 'Sections 7.5-7.6, the ambient-coordinate reading',
    'card_singleDecrements_insert_erase_Iic'        : 'Lemma 7.1 (a) count',
    'singleDecrements_insert_erase_Iic'             : 'Lemma 7.1 (a) list',
    'lemma7_1b_one_decrement'                       : 'Lemma 7.1 (b)',
    'lemma7_1c_two_decrements'                      : 'Lemma 7.1 (c)',
    'four_le_card_singleDecrements_of_two_outside'  : 'Lemma 7.1 (d) bound',
    # RELABELLED 2026-08-24 by a two-reader blind pass, which ranked this the worst label in the
    # gate and ranked it FIRST independently.  `singleDecrements` does not occur in the statement.
    # What is proved is: four pairwise-distinct members of `F`, each different from `W` -- which is
    # `5 ≤ F.card` and nothing about `W`.  The `D₁₁ … D₂₂` naming suggests a 2x2 structure that the
    # statement does not express.  The old label is what a reader HOLDING THE PAPER reads it as.
    'four_distinct_decrements_of_two_outside'       : 'Lemma 7.1 (d), four distinct members of F other than W -- NOT stated as decrements of W',
    'lemma1_bottom'                                 : 'Lemma 7.2 (i)-(iv) less the adjacency',
    'exists_adjacent_gale_bottom_pair'              : 'Lemma 7.2 (iii) adjacency',
    'lemma7_1d_four_decrements'                     : 'Lemma 7.1 (d) over [n]',
    'dualSet_dualSet'                               : 'Lemma 7.10 involution',
    'card_dualSet'                                  : 'Lemma 7.10 cardinality',
    'dualSetRankEquiv'                              : 'Lemma 7.10 rank bijection',
    'galeLeast_eq_initialSegment'                   : 'Lemma 7.2 (i) coordinates',
    'galeSecondLeast_eq_secondInitialSegment'       : 'Lemma 7.2 (ii) coordinates',
    'exchangeGraph_not_bipartite_of_three_le'       : 'Corollary 7.3',
    'hamPath_of_cliqueSum_of_other_pair'          : 'the other pairs of a clique-sum, from Theorem 7.7',
    'no_hamPath_of_cliqueSum'                       : 'Lemma 7.4 (the obstruction)',
    'qstar_hamConnected_of_galeGreatest'            : 'Corollary 7.9 as printed',
    'lemma2_universalPair_is_galeLeast'             : 'Lemma 7.5',
    'cliqueSum_universalPair_coordinates'         : 'Lemma 7.5 coordinates',
    # RELABELLED 2026-08-24, both blind readers.  The conclusion is `(u ∩ v ⊆ X) ≠ (X ⊆ u ∪ v)`,
    # an exclusive or between two containment conditions by propext.  No arm object occurs, and
    # NEITHER SIDE IS ASSERTED NONEMPTY -- the statement holds when every X lands on one side, i.e.
    # when an "arm" is empty.  Nonemptiness of both arms is `yFamily_isCliqueSum`, not this.
    'lemma3_two_arms'                               : 'Theorem 7.6, the two containment conditions are exclusive (no arm, no nonemptiness)',
    # RELABELLED 2026-08-24, both blind readers.  The conclusion is `F = yFamily (usedGround F) k r s`
    # -- a classification of F.  No arm occurs and nothing expressing contiguity occurs; contiguity is
    # inside the yFamily DEFINITION, which is exactly what a blind reader cannot see.
    'lemma3_arms_are_contiguous'                    : 'Theorem 7.6, F is exactly a yFamily (contiguity lives in that definition)',
    'yFamily_isCliqueSum'                      : 'Theorem 7.6 converse',
    'qstar'                                         : 'Theorem 7.7  -- (Q*)',
    'not_yFamily_isHamConnected'                       : 'Corollary 7.8',
    'cliqueSum_exists_incomparable_galeMaximal'   : 'Corollary 7.9 incomparability',
    'qstar_no_exception_of_principal'               : 'Corollary 7.9 no exception',
    'qstar_principal_isHamConnected'                : 'Corollary 7.9 Hamilton-connected',
    'galeLE_dualSet_iff'                            : 'Lemma 7.10 (i) Gale transport',
    'card_dualSet_symmDiff'                         : 'Lemma 7.10 (ii)',
    'mem_iff_dualElem_notMem_dualSet'               : 'Lemma 7.10 (iii)',
    'subset_iff_dualSet_subset'                     : 'Lemma 7.10 (iv)',
    'isShifted_dualFamily'                          : 'Lemma 7.10 shiftedness',
    'exchangeGraph_dualIso'                         : 'Lemma 7.10 the isomorphism',
    'image_layerAbove_dualSet'                      : 'Lemma 7.10 layers above',
    'image_layerBelow_dualSet'                      : 'Lemma 7.10 layers below',
    'isCliqueSum_dual_iff'                        : 'Lemma 7.10 Y-families',
    # RELABELLED 2026-08-24 after a blind back-translation.  These two say
    #     X ⊆ u ∪ v  ↔  dualSet u ∩ dualSet v ⊆ dualSet X
    # and its converse.  They mention no arm.  They are the containment identity that section 7.10's
    # arm-exchange clause is proved FROM -- inner-arm membership is "X ⊆ u ∪ v" and outer-arm
    # membership is "X* ⊇ u* ∩ v*" -- but nothing in the tree states the arm exchange with the arm
    # objects themselves.  The old labels claimed the clause; these claim what is proved.
    'innerArm_dual_iff_outerArm'                  : 'Lemma 7.10, the containment identity behind the arm exchange',
    'outerArm_dual_iff_innerArm'                  : 'Lemma 7.10, the same identity, converse direction',
    # ADDED 2026-08-24, the same day the gap was found.  These two state the arm-exchange clause
    # itself, with `yInnerArm` and `yOuterArm` in it, which is what the two rows above do NOT do.
    # The hypothesis `k + 2 ≤ n` is `yFamily_isShifted`'s own `hGcard`; without it the statement is
    # false, because truncated subtraction collapses the dual rank while the inner arm survives.
    # SCOPE, flagged by both blind readers on the day these were added, and they are right: these are
    # proved for the FULL ground `Finset.univ`, not for a general downward-closed `G` nor for
    # `usedGround F`, which is the ground the rest of Section 7 works over.  `dualSet` complements in
    # `Fin n`, so the full ground is where the duality lives -- but the label has to say so instead of
    # letting a reader assume generality.  The `2 ≤ k` in the second and not the first is real: the
    # second is derived from the first at the dual rank, which needs `(n - k) + 2 ≤ n`.
    'image_dualSet_yInnerArm'                     : 'Lemma 7.10 arm exchange, inner onto outer, ON THE FULL GROUND',
    'image_dualSet_yOuterArm'                     : 'Lemma 7.10 arm exchange, outer onto inner, ON THE FULL GROUND',
    'crossingLemma'                                      : 'Theorem 7.11 (crossing lemma)',
}

def main():
    if not GEN.exists():
        print(f"FAIL: generator missing at {GEN}"); return 1
    cmd = (f"cd {LEAN} && (ulimit -v 67108864; LEAN_NUM_THREADS=6 "
           f"lake env lean {GEN})")                      # KiB = 64 GiB.  never `lake -j`.
    r = subprocess.run(["bash", "-lc", cmd], capture_output=True, text=True, timeout=3600)
    out = r.stdout + r.stderr
    if r.returncode != 0:
        print("FAIL: the generator did not run cleanly\n" + out[-2000:]); return 1

    # Lean wraps long axiom lists over several lines; rejoin before parsing.
    flat = re.sub(r"\s+", " ", re.sub(r"^\S+?:\d+:\d+:\s*", "", out, flags=re.M))
    traces = dict(re.findall(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]", flat))

    problems, seen = [], set()
    for short, label in EXPECT.items():
        full = [k for k in traces if k.split(".")[-1] == short]
        if not full:
            problems.append(f"{label:34} {short}: NO TRACE PRINTED"); continue
        name = full[0]; seen.add(name)
        axioms = {a.strip() for a in traces[name].split(",") if a.strip()}
        extra = axioms - FOUNDATIONS
        if extra:
            kind = ("native_decide certificate" if any("native_decide" in e for e in extra)
                    else "sorryAx" if any("sorry" in e for e in extra) else "cited axiom")
            problems.append(f"{label:34} {short}: {kind} -> {sorted(extra)}")
        else:
            print(f"  ok   {label:34} {short}")
    stray = set(traces) - seen
    if stray:
        problems.append(f"generator printed declarations the gate does not expect: {sorted(stray)}")
    if len(traces) != len(EXPECT):
        problems.append(f"declaration count {len(traces)}, expected {len(EXPECT)}")

    print()
    if problems:
        print("RESULT: FAIL")
        for p in problems: print("  " + p)
        return 1
    print(f"RESULT: PASS — all {len(EXPECT)} of the note's declarations trace to "
          f"{{propext, Classical.choice, Quot.sound}} and nothing else.")
    print("        No cited axiom, no sorryAx, no native_decide certificate on the note's surface.")
    return 0

if __name__ == "__main__":
    sys.exit(main())
