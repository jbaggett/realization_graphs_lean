/-
Realization / P59 lane — axiom baseline generator.

Run:  cd lean && ulimit -v 67108864 && LEAN_NUM_THREADS=6 \
        lake env lean ../topics/flipgraphs/realization/compute/AxiomBaseline.lean

`ulimit -v` takes KIBIBYTES.  64 GiB is 67108864.  The figure 68719476736 that circulated on
2026-07-30 is 64 GiB in BYTES, i.e. 64 TiB — larger than the box, so the shell accepts it and the
guard does nothing.  See `_coord/BULLETIN_2026-07-30e_ULIMIT_UNITS.md`.  Verify the effect, not the
exit code: `ulimit -v 67108864; ulimit -v`.

This generator deliberately carries NO `open` and lives at a PINNED path, per the root `CLAUDE.md`:
`#print axioms` prints names qualified or unqualified depending on the `open` context, and Lean
prefixes each line with `file:line:col`, so a byte-compare gate must strip that prefix and assert the
declaration counts below rather than diffing raw output.

Prints the axiom trace of every load-bearing declaration.  The lane's cited-axiom and certificate
inventory is whatever survives subtracting {propext, Classical.choice, Quot.sound} from each printed
list.  Per `_coord/BULLETIN_2026-07-30_NEW_LANES.md` §1.3 this is read off declarations, never off
module sources, in either direction.

## COUNTS TO ASSERT — 115 declarations in three strata, which are NEVER summed

    PART A  proved, §1-§4 and the engines                25   0 sorryAx
    PART B  proved, §1b / §4 / §5 / §6 / §7 / §8 / §9    90   0 sorryAx
    PART C  OPEN                                          0   every one carries sorryAx

The figures above were STALE from 2026-08-18 to 2026-08-20, reading 28/81/0 against an enforced
28/84/0.  Nothing failed, because the enforced numbers live in `check_axiom_baseline.py` and this
comment is prose -- which is exactly the drift this file exists to prevent, one level up.

The strata are separate because `SEC_COMPUTATION.md` §11.4 reports them separately and says
explicitly that they are never added together.  A single number over all 90 would be the exact claim
this lane has spent two days refusing to make.

These counts are ENFORCED, not documented: `compute/check_axiom_baseline.py` runs this generator,
parses the traces, and fails on a wrong stratum size, a `sorryAx` in Part A or B, a Part C
declaration that has stopped carrying one, a named declaration that was not traced at all, or a
cited axiom outside the expected six.  The counts above were wrong when first written and that
checker is what caught them.

## ⚠ WHY PART B EXISTS — the failure it was written to end (2026-08-18)

Until today this generator traced ONLY the 28 declarations named in `paper/DEPENDENCY_GRAPH.md`.
Re-run on 2026-08-18 it reported 28 declarations and **five** cited axioms, and every figure was
correct.  It was also **wrong in the way that matters**: on 2026-08-17 Jeff took a SIXTH cited axiom
onto the trust surface — `realizationGraph_preconnected`, Fulkerson-Hoffman-McAndrew 1965 — and
`theorem_5_7_cross_degree` depends on it.  Neither appeared here, because no §5 declaration was in
the list.  **A submission-time audit against the old baseline would have been green and would have
omitted a cited axiom that a top-level theorem rests on.**  That is the dangerous direction: stale in
SCOPE rather than in count, so nothing looks wrong.

The rule this earns: **when a declaration joins the trust surface, it joins THIS FILE in the same
edit.**  A baseline that names a subset of the surface is not a weaker gate, it is a misleading one.

## ⚠ PART C IS TRACED ON PURPOSE

Open declarations of `SBPlusOrd.lean`, when present, are traced here to make the open surface
COUNTABLE from the same run that audits the proved one, instead of from a separate audit nobody
remembers to run.  Every Part C line
must print `sorryAx`; a Part C declaration that stops printing it has been PROVED and belongs in
Part B, and one that never printed it was never open.  Note the converse trap recorded in
`SBPlusOrd.lean`'s own header: `theorem <name> : True := by trivial` carries no `sorryAx` and traces
as *"does not depend on any axioms"*, cleaner than a real theorem.  There are none in this tree; if
one is ever reintroduced, this file will report it as PROVED and be wrong.
-/
import Realization.TheoremOne
import Realization.SequelWave1
import Realization.SeparatorTheorem
import Realization.LayeredBase
import Realization.InterfaceSaturation
import Realization.TriangleProjection
import Realization.LayerCapacity
import Realization.PathWalks3
import Realization.QStar
import Realization.SBPlusOrd

-- Theorem 1.1 / 3.1, the bipartite case, and its product inputs
#print axioms Brualdi.RealizationGraph.theorem_one
#print axioms Brualdi.RealizationGraph.barrus_products_maximally_hamiltonian
#print axioms Brualdi.RealizationGraph.ctProduct_maximally_hamiltonian
#print axioms Brualdi.RealizationGraph.ctCrownProduct_maximally_hamiltonian

-- Lemma 3.2, the crown
#print axioms Brualdi.Ledger.crown_spanning2_laceable

-- Lemma 4.1, quotient adjacency
#print axioms Brualdi.RealizationGraph.quotient_adjacent

-- PARKED 2026-08-20.  `regularCore_base_isMH` (the regular/Johnson base) and
-- `nearRegular_admissible_laminar_baseFamily` / `intervalLaminar_baseExchange_hamConnected` (the
-- near-regular/laminar base) left this target with `BaseStructureJohnson`.  They were the ONLY
-- consumers of `johnson_isMH` and `naddef_pulleyblank_baseExchange`, the two cited axioms the main
-- theorem never charged.  See `ParkedBaseStructure` in `lakefile.toml`.  The interval lemma itself
-- STAYS: `LayerCapacity`, a root, still imports `IntervalLemma`.
#print axioms Brualdi.RealizationGraph.intervalLemma_suffix
#print axioms Brualdi.RealizationGraph.intervalLemma_suffix_zero

-- Lemma 5.1, two-block splice
#print axioms Brualdi.Ledger.twoBlock_splice
#print axioms Brualdi.Ledger.twoBlock_splice_same

-- Lemma 5.2 / B3, path-walk engine, and TL-4
#print axioms Brualdi.RealizationGraph.PathWalks.B3_separable
#print axioms Brualdi.RealizationGraph.PathWalks.B3_reduction_from_two_walks
#print axioms Brualdi.RealizationGraph.PathWalks.hamCycle_of_hamConnected

-- E2-odd
#print axioms Brualdi.RealizationGraph.triangle_projects_to_neighbor_triangle

-- E3-sat
#print axioms Brualdi.RealizationGraph.BipartiteInterface.biregular_matching

-- TL-8-RS, the universal separator theorem
#print axioms
  Brualdi.RealizationGraph.SeparatorTheorem.residual_capacitySeparator_part3_no_internal_separator
#print axioms Brualdi.RealizationGraph.SeparatorTheorem.capacitySeparator_part3_no_internal_separator

-- Sub-claim L1, layer capacity (the two cited axioms live in this module)
#print axioms Brualdi.RealizationGraph.L1

-- Layered base: the proved k = 2 case and the recorded TS step
#print axioms Brualdi.Ledger.layeredBase_two_blocks
#print axioms Brualdi.Ledger.layeredBase_TS_step

-- Sequel wave 1 port saturation
#print axioms Brualdi.RealizationGraph.SequelWave1.minimum_port_saturation
#print axioms Brualdi.RealizationGraph.SequelWave1.maximum_port_saturation

-- Bounded-composition path criterion and the dodge core
#print axioms Brualdi.RealizationGraph.BoundedComposition.isPathGraph_of_effectiveDimension_le_two
#print axioms Brualdi.RealizationGraph.DodgeCore.hamilton_path_separator_bound
#print axioms Brualdi.RealizationGraph.DodgeCore.first_death_localization

/- ======================================================================
   PART B — proved surface added 2026-08-18: §5, §7, §8.  14 declarations.
   ====================================================================== -/

-- ★ §1b, THE BRIDGE — PROVED 2026-08-18, and it is what makes §7 usable.  Before it, `qstar` was
-- applied NOWHERE: 252 machine-checked declarations attached to nothing, because no declaration
-- identified `quotientGraph d v` with the exchange graph of a shifted family.  `quotient_qstar` is
-- what the assembly consumes and it is ORDER-FREE; the `[LinearOrder V]` that `QStar` requires is
-- chosen inside the proofs.  `exists_realization_unit_transfer` is the elementary edge swap that
-- lets manuscript Theorem 5.3 avoid citing Ruch-Gutman for the majorization down-set.
#print axioms Brualdi.RealizationGraph.SBPlusOrd.mem_realizableNeighborhoods
#print axioms Brualdi.RealizationGraph.SBPlusOrd.exists_realization_unit_transfer
#print axioms Brualdi.RealizationGraph.SBPlusOrd.exists_pivotMaximal_degreeAntitone_order
#print axioms Brualdi.RealizationGraph.SBPlusOrd.quotientFamily_isShifted
#print axioms Brualdi.RealizationGraph.SBPlusOrd.quotientIsoExchange
#print axioms Brualdi.RealizationGraph.SBPlusOrd.quotient_qstar

-- §5.4, the twin/constancy chain proved overnight 2026-08-17/18.
-- `corollary_5_7c_twins_constant` keeps preconnectedness as an explicit HYPOTHESIS, so it traces to
-- foundations alone; the axiom is charged exactly once, below, and stays legible at every call site.
#print axioms Brualdi.RealizationGraph.twins_iff_interfaceWitnessCount_eq_zero
#print axioms Brualdi.RealizationGraph.lemma_5_7c_twin_invariant_along_edge
#print axioms Brualdi.RealizationGraph.corollary_5_7c_twins_constant
#print axioms Brualdi.RealizationGraph.card_sSideConnectorTargets_eq_interfaceWitnessCount

-- Manuscript Lemma 5.1.  Two false versions of this preceded the true one, both because
-- `residualDegree` uses TRUNCATED natural subtraction; see the handoff's §F.
#print axioms Brualdi.RealizationGraph.fibreDeleteIso

-- Theorem 5.7, which is where the sixth cited axiom `realizationGraph_preconnected`
-- (Fulkerson-Hoffman-McAndrew 1965, Jeff's call 2026-08-17) is INVOKED -- once, at
-- `InterfaceSaturation.lean:1407`, and nowhere else in the tree.
--
-- ⚠ CORRECTED 2026-08-18, hours after this line was first written the wrong way.  It said Theorem
-- 5.7 was "the only declaration that charges" the axiom and that a second printing it would mean the
-- axiom was being invoked somewhere it was not charged.  **That would have been a false alarm.**
-- `#print axioms` reports the TRANSITIVE trace, so every consequence of Theorem 5.7 prints the axiom
-- too -- `theorem_5_8_exact_color_expansion` already does, correctly, because it consumes 5.7.
-- "Charged once" is a claim about INVOCATION SITES, which is checked by grepping the axiom's name in
-- the sources; it is not a claim about traces, and the two must not be conflated.  The property Jeff
-- asked to preserve is the invocation one: `corollary_5_7c_twins_constant` keeps preconnectedness as
-- an explicit hypothesis, so the dependency stays legible at every call site.
#print axioms Brualdi.RealizationGraph.theorem_5_7_cross_degree

-- The rest of §5's proved surface, added 2026-08-18 when a manuscript-to-Lean sweep found it was
-- missing: Lemma 5.7a, the three names carrying the vicinal trichotomy (manuscript Lemma 5.7b), and
-- Theorem 5.8.  This is the SAME stale-in-scope failure recorded in the header, one section further
-- in: Part B was built from the overnight §5.4 chain rather than from §5, so proved declarations
-- sat outside the audit.
#print axioms Brualdi.RealizationGraph.lemma_5_7a
#print axioms Brualdi.RealizationGraph.interfaceWitnessCount_eq_degree_sub_of_gt
#print axioms Brualdi.RealizationGraph.interfaceWitnessCount_le_one_of_degree_eq
#print axioms Brualdi.RealizationGraph.interfaceWitnessCount_eq_zero_of_lt
#print axioms Brualdi.RealizationGraph.theorem_5_8_exact_color_expansion

-- Theorem 5.4, and the relabelling transport §8 consumes.
#print axioms Brualdi.RealizationGraph.SBPlusOrd.quotient_adjacency
#print axioms Brualdi.RealizationGraph.SBPlusOrd.hasRealizationWithNeighborSet_image_of_perm

-- §7, the (Q*) quotient theorem: the induction, the Step+ lemma, and both principal corollaries.
-- Foundations alone -- no cited axiom and no `native_decide` -- which is the claim
-- `results/2026-08-16_qstar_fully_machine_checked.md` makes and this is where it is checkable.
-- FAITHFULNESS, added 2026-08-21.  `GaleLE` is the THRESHOLD form; the manuscript's Section 7.1
-- defines the Gale order by sorted pointwise comparison and uses the two interchangeably.  Until
-- this landed, the kernel certified theorems about one order and the paper printed the other, with
-- a sentence of prose as the only bridge -- the one class of defect a kernel cannot see, since it
-- would be proving true statements about a neighbouring object.  Its own key lemma is `private`,
-- so it cannot be named here; it is consumed by this theorem, whose trace is clean.
#print axioms Brualdi.RealizationGraph.QStar.galeLE_iff_pointwise
-- FAITHFULNESS, added 2026-08-22.  The manuscript prints its yFamily classification in ambient
-- coordinates on `[n]`; Lean states it over `usedGround F` and `initialSegment (usedGround F) j`.
-- Those agree only because a shifted family's used ground is downward closed, which nothing proved
-- until now.  Same class as `galeLE_iff_pointwise`.  The third is Section 7.5's assertion that a
-- coordinate yFamily is a shifted family, which the development had never carried.
#print axioms Brualdi.RealizationGraph.QStar.usedGround_downwardClosed
#print axioms Brualdi.RealizationGraph.QStar.initialSegment_downwardClosed
#print axioms Brualdi.RealizationGraph.QStar.yFamily_isShifted
#print axioms Brualdi.RealizationGraph.QStar.qstar
#print axioms Brualdi.RealizationGraph.QStar.crossingLemma
#print axioms Brualdi.RealizationGraph.QStar.qstar_no_exception_of_principal
#print axioms Brualdi.RealizationGraph.QStar.qstar_principal_isHamConnected

-- ★ FOUND BY THIS FILE, 2026-08-18, on its first run.  `ord_connector_source` was written into Part
-- C on the assumption that it consumes `ord` and is therefore open.  It traces to foundations ALONE:
-- it is the connector-source half of (ORD), it needs no maximal-Hamiltonicity hypothesis, and it is
-- proved outright.  The (ORD) obligation is smaller than the handoff's open list implied -- one of
-- its two halves is already machine-checked.
#print axioms Brualdi.RealizationGraph.SBPlusOrd.ord_connector_source

-- The Erdős–Gallai necessity input (§8.2's double count), proved here rather than cited
-- (2026-08-18).  The classical statement is about "the top `t` vertices" and would have been a
-- SEVENTH cited axiom; the set form is one double count and adds nothing to the trust surface.
-- `exists_topBlock` is the single declaration in the whole §8 development where a vertex order
-- enters.
--
-- ⚠ This comment said "§8.2.1" until 2026-08-24, and so does `erdos_gallai_sufficiency`'s docstring.
-- There is no §8.2.1 in the manuscript.  Corrected here; the docstring is a separate fix.
--
-- `erdosGallaiSlack_nonneg_of_graphical` was ADDED 2026-08-24.  It is the sorted form of the same
-- necessity half, and until that day it existed only as an anonymous local `have`, duplicated
-- byte-for-byte in 8.3d and 8.3e.  §8.2 of the manuscript claims this half "is proved below by a
-- double count" -- and a local `have` has no axiom trace, so nothing here could certify that claim.
-- Now it can.
#print axioms Brualdi.RealizationGraph.SBPlusOrd.sum_degree_le_of_finset
#print axioms Brualdi.RealizationGraph.SBPlusOrd.isClique_of_sum_degree_eq
#print axioms Brualdi.RealizationGraph.SBPlusOrd.card_highDegree_le_succ_degree
#print axioms Brualdi.RealizationGraph.SBPlusOrd.exists_topBlock
#print axioms Brualdi.RealizationGraph.SBPlusOrd.erdosGallaiSlack_eq_of_topBlock
#print axioms Brualdi.RealizationGraph.SBPlusOrd.erdosGallaiSlack_nonneg_of_graphical

-- Phase 1 of the formalization plan, 2026-08-18: `MainLine.indecomposable` now carries the REAL
-- Tyshkevich predicate rather than the `NoErdosGallaiEquality` stand-in, which was measured to be
-- strictly stronger -- sound, but covering 26 fewer of the 161 main-line sequences through order 7.
-- This is the anti-vacuity theorem for the new predicate: a degree-zero vertex decomposes, so the
-- hypothesis excludes something rather than holding of everything.
#print axioms Brualdi.RealizationGraph.SBPlusOrd.tyshkevichDecomposable_of_degree_zero

-- The complementation transport of §8.2, proved 2026-08-18 as part of Lemma 8.3f: complementing
-- every realization sends `d` to `n−1−d` and reverses the roles `(c,a,b,x) ↦ (x,b,a,c)`, carrying a
-- four-corner configuration to a four-corner configuration — forbidden corners included, which is
-- the half a careless transport would drop.
#print axioms Brualdi.RealizationGraph.SBPlusOrd.fourCorner_complement

-- §9's Theorem 9.1 = `ord`, PROVED 2026-08-19.  Its three cases rest entirely on proved machinery:
-- quotient_adjacency for the singleton fibre, theorem_5_8_exact_color_expansion for the bipartite
-- case -- which needs the connector source in the class OPPOSITE the endpoint, since a laceable
-- graph has Hamilton paths only between opposite colours -- and ord_connector_source for the rest.
-- Charges `realizationGraph_preconnected` transitively through Theorem 5.7 and nothing else.
#print axioms Brualdi.RealizationGraph.SBPlusOrd.ord

-- §4's reductions, PROVED 2026-08-18.  Manuscript Theorem 4.1 and the engine of Corollary 4.3, the
-- two branches §10.1 dispatches through that had no Lean at all until today.  Both on foundations
-- alone -- in particular the product route picks up NONE of Paper-interchange's cited axioms through
-- `Sec4Walk`, which the brief asked to be checked because it would have changed this paper's list.
#print axioms Brualdi.RealizationGraph.SBPlusOrd.realizationGraph_iso_of_inactive
#print axioms Brualdi.RealizationGraph.SBPlusOrd.isMH_boxProd_of_factorReady

-- §6.3's rich four-core lemma, PROVED 2026-08-18 -- the hardest single proof in the paper, and the
-- third of `separator_buffer`'s four arguments.
#print axioms Brualdi.RealizationGraph.SBPlusOrd.no_rich_failure_of_mainLine

-- §6's foundations, PROVED 2026-08-18: the triangle trichotomy's arithmetic and support bound, and
-- the |D| >= 4 lower bound.  Two of `separator_buffer`'s four arguments; §6.3's case table and
-- §6.4's split branch remain.
#print axioms Brualdi.RealizationGraph.SBPlusOrd.triangle_switches_share_two
#print axioms Brualdi.RealizationGraph.SBPlusOrd.triangle_support_card_four_or_five
#print axioms Brualdi.RealizationGraph.SBPlusOrd.differenceSupport_card_ge_four

-- Lemma 8.6, PROVED 2026-08-18: no three pivots are exceptional for the same pair.  ⚠ Its
-- `MainLine` hypothesis is UNUSED -- the manuscript's Lemma 8.6 has none either, so the Lean
-- statement is WEAKER than the paper's.  Safe, but a correspondence gap, recorded rather than
-- silently tightened: changing a statement is not a wave's call.
#print axioms Brualdi.RealizationGraph.SBPlusOrd.atMostTwoExceptional

-- §8.1′ and Corollary 8.4, PROVED 2026-08-18: the order-free form of Lemma 8.2, and the half of
-- Corollary 8.4 that Lemma 8.6 consumes.  Between them they are `atMostTwoExceptional`'s inputs.
#print axioms Brualdi.RealizationGraph.SBPlusOrd.yFamilyPivot_same_degree
#print axioms Brualdi.RealizationGraph.SBPlusOrd.exceptionalPivot_symmDiff_eq_degreeClass

-- The bridge from a yFamily pivot to the four-corner hypothesis, and the two degree-class statements it
-- unblocks.  Manuscript §8.2's setup paragraph and the second half of Theorem 8.3.  Until this
-- existed, everything §8.2 proved was about a `FourCorner` and everything the rest of §8 consumed was
-- about a `YFamilyPivot`, with nothing joining them.
#print axioms Brualdi.RealizationGraph.SBPlusOrd.fourCorner_of_yFamilyPivot
#print axioms Brualdi.RealizationGraph.SBPlusOrd.yFamilyPivot_degreeClass_card
#print axioms Brualdi.RealizationGraph.SBPlusOrd.yFamilyPivot_card_above

-- §8.2's chain, CLOSED 2026-08-18 on the seventh cited axiom.  8.3e's `σ ≥ 0` branch needed the
-- SUFFICIENCY direction of Erdős–Gallai -- the hard half, absent from Mathlib and from this
-- development -- and Jeff's call was to cite it.  8.3f and Theorem 8.3 followed at once.  These
-- three are the only declarations that charge `erdos_gallai_sufficiency`, and they charge it
-- transitively through the single invocation site inside `exists_neg_slack_of_not_graphical`.
#print axioms Brualdi.RealizationGraph.SBPlusOrd.lemma_8_3e_one_sided_bound
#print axioms Brualdi.RealizationGraph.SBPlusOrd.lemma_8_3f_complementation
#print axioms Brualdi.RealizationGraph.SBPlusOrd.theorem_8_3_middle_degrees
#print axioms Brualdi.RealizationGraph.SBPlusOrd.exists_neg_slack_of_not_graphical
#print axioms Brualdi.RealizationGraph.SBPlusOrd.pos_degree_of_mem_realizable

-- §8.2's proved numerical layer.  8.3d joined it 2026-08-18: four steps, its Step 3 input supplied
-- by §8.2.1's `card_highDegree_le_succ_degree`, and every step verified numerically over 1,227
-- four-corner configurations through order 10 before the wave was dispatched.
#print axioms Brualdi.RealizationGraph.SBPlusOrd.lemma_8_3d_lower_witness_propagation
#print axioms Brualdi.RealizationGraph.SBPlusOrd.lemma_8_3a_strict_outer_gaps
#print axioms Brualdi.RealizationGraph.SBPlusOrd.lemma_8_3b_slack_identities
#print axioms Brualdi.RealizationGraph.SBPlusOrd.lemma_8_3c_agreement_above_pivot
#print axioms Brualdi.RealizationGraph.SBPlusOrd.hasNonBipartiteFibre_of_degree_eq

-- §8.1′ / §8.4, closed 2026-08-18: the order-free forced-pair statement and the fact that all yFamily
-- pivots have the same degree.  Both are the last inputs used by `atMostTwoExceptional`.

/-
   PART B — the §6.4 bridge, added 2026-08-19.  9 declarations.

   The clause "indecomposability removes the invariant-position product factors" is three
   transports, not one.  Two of them are here.  The third — that `G(d)` IS the interchange graph of
   the clique-independent incidence matrix — is `SplitIncidenceModel`, and it is still a
   HYPOTHESIS: nothing constructs one, so `splitIncidence_buffer_of_tyshkevichIndecomposable` is
   CONDITIONAL and §6.4 is restated rather than closed.  Traced here so that stays visible instead
   of being read off a theorem name that looks finished.
-/
#print axioms Brualdi.RealizationGraph.SBPlusOrd.SplitIncidenceModel.rowPat_eq_iff_neighborFinset_eq
#print axioms Brualdi.RealizationGraph.SBPlusOrd.SplitIncidenceModel.colPat_eq_iff_neighborFinset_eq
#print axioms Brualdi.RealizationGraph.SBPlusOrd.tyshkevichDecomposable_of_block
-- `tyshkevichDecomposable_of_degree_zero` was ALSO listed here until 2026-08-20.  Listing it twice
-- made the declared strata sum to one more than the distinct declarations traced, so the gate's own
-- two headline numbers did not reconcile.  It keeps its entry above, with the comment that explains
-- what it is for.
#print axioms Brualdi.RealizationGraph.SBPlusOrd.cellVaries_of_tyshkevichIndecomposable
#print axioms Brualdi.RealizationGraph.SBPlusOrd.hasNonBipartiteFibre_of_fibreNonbip
#print axioms Brualdi.RealizationGraph.SBPlusOrd.hasNonBipartiteFibre_of_patternFibreNonbip
#print axioms Brualdi.RealizationGraph.SBPlusOrd.hasNonBipartiteFibre_of_lineFibreNonbip
#print axioms Brualdi.RealizationGraph.SBPlusOrd.splitIncidence_buffer_of_tyshkevichIndecomposable

/-
   PART B — the split-incidence model, added 2026-08-19.  3 declarations.

   This is the transport §6.4 asserts in half a clause: *"For a split degree sequence, G(d) is the
   interchange graph of the clique-independent incidence matrix."*  Until now it was a HYPOTHESIS
   (`SplitIncidenceModel`) that nothing supplied.  `splitIncidenceModelOfSplitPartition` constructs
   one, on foundations alone, and `..._exists_of_failure` delivers it in the context §6.4 needs.

   `..._exists_of_failure` inherits a `native_decide` certificate from `realization_split_of_failure`
   — NOT introduced here.  It is traced so the certificate is named rather than discovered later; see
   the CLAUDE.md rule that a grep for `Lean.ofReduceBool` returns zero on a surface carrying them.
-/
#print axioms Brualdi.RealizationGraph.SBPlusOrd.splitIncidenceModelOfSplitPartition
#print axioms Brualdi.RealizationGraph.SBPlusOrd.splitIncidenceModel_exists_of_splitPartition
#print axioms Brualdi.RealizationGraph.SBPlusOrd.splitIncidenceModel_exists_of_failure

/-
   PART B — §6 CLOSES, 2026-08-19.  2 declarations.

   `separator_buffer` (manuscript Theorem 6.1) is proved: the rich-triangle branch through
   `no_rich_failure_of_mainLine`, the split branch through the split-incidence model, both size-2
   Johnson branches, and size 3 excluded by `MainLine.notK3`.  `sbPlus` follows, its argument having
   been complete since 08-18 and waiting only on this input.
-/
#print axioms Brualdi.RealizationGraph.SBPlusOrd.separator_buffer
#print axioms Brualdi.RealizationGraph.SBPlusOrd.sbPlus

/-
   PART B — Corollary 3.3 and `FactorReady`, added 2026-08-19.  2 declarations.

   `isMH_boxProd_of_factorReady` was proved but took `FactorReady` on both factors, and nothing
   produced `FactorReady` for a realization graph — so two of §10.1's five branches had nothing
   behind them.  `corollary_3_3` supplies the bipartite disjunct's `IsSpanning2DPCOpposite`, which is
   strictly stronger than laceability and is why §3 proves more than it appears to.

   Mostly assembled from machinery that already existed: `Brualdi.CORE'` finished the crown-free case
   outright and `crown_spanning2_laceable` covered the crown.  The one new piece is the paired-2-DPC
   induction along a CT-leaf product, mirroring `ctLeafProduct_hamLaceable`.  `ctLeafProduct_paired_two`
   is `private`, so it is not traced here; its content is charged through the two below.
-/
#print axioms Brualdi.RealizationGraph.corollary_3_3
#print axioms Brualdi.RealizationGraph.factorReady_of_realizationGraph

/-
   PART B — §9's delivery theorem, added 2026-08-19.  1 declaration.

   Corollary 9.3 (`twoSidedDelivery`) was proved here too and REMOVED 2026-08-19: the one-pass
   assembly applies `ord` and `obi` directly, so nothing in the Lean or the prose ever used it.

   `obi` is manuscript Theorem 9.2 and `twoSidedDelivery` is Corollary 9.3.  §10.2 needs two DISTINCT
   entries into the buffer fibre, and these are what supply them.

   The quantifier order in `obi` is load-bearing, not stylistic: `bad` is an argument bound BEFORE the
   existential tuple, so the endpoint may depend on it.  The selection-first form — endpoint chosen
   first, then required to avoid every `bad` — is FALSE, and measurably so: 149,718 hops through
   ground order 7 have every connector-carrying endpoint holding exactly one target.
   (`compute/sec92_bad_avoidance_check.py`.)
-/
#print axioms Brualdi.RealizationGraph.SBPlusOrd.obi

/-
   PART B — the one-pass assembly, added 2026-08-19.  1 declaration.

   `mainLine_MH_of_IH` is §10.2-§10.3: the pivot from `sbPlus`, the quotient Hamilton path from
   `quotient_qstar`, fibre runs from `ord`, the two distinct buffer entries from `obi`, and the
   concatenation checked step by step.  The induction hypothesis is an explicit parameter because the
   theorem is true without it but not provable without it — §10.2 needs every fibre maximally
   Hamiltonian, and that is the induction on ground order.

   NOTE for §10.4: this trace does NOT charge `naddef_pulleyblank_baseExchange`.  The manuscript
   states that the Naddef-Pulleyblank route "is not used here", and this is the first declaration in
   the development able to bear on it.  Not yet decisive — the final theorem's trace is what settles
   it (PROSE_LEAN_GAPS Class 10.2).
-/
#print axioms Brualdi.RealizationGraph.SBPlusOrd.mainLine_MH_of_IH

/-
   PART B — manuscript Theorem 4.2, added 2026-08-19.  5 declarations.

   In a Tyshkevich composition the cross adjacencies are forced in every realization, so no 2-switch
   crosses and G(d) IS the Cartesian product of the two sides' realization graphs.  The isomorphism
   is `≃g` — adjacency in both directions — not a bijection; a bijection alone would not let §10.1's
   decomposable branch fire, and the wave was briefed not to weaken it to one.

   This gives `isMH_boxProd_of_factorReady` its FIRST consumer.  Until today it was proved and used
   nowhere, which is how the gap stayed invisible: a conditional theorem with no caller looks finished.

   Verified before dispatch over all 405 Tyshkevich witnesses of the 197 decomposable classes through
   order 7 — bijection AND box-product adjacency, zero failures.  Checking one witness per class was
   the first attempt and was not good enough: the hypothesis is existential, so the proof receives an
   arbitrary witness.  (`compute/thm42_boxproduct_check.py`.)
-/
#print axioms Brualdi.RealizationGraph.SBPlusOrd.tyshkevich_forced_in_every_realization
#print axioms Brualdi.RealizationGraph.SBPlusOrd.realization_edgeSymmDiff_card_ge_four
#print axioms Brualdi.RealizationGraph.SBPlusOrd.realizationGraph_iso_boxProd_of_tyshkevichWitness
#print axioms Brualdi.RealizationGraph.SBPlusOrd.realizationGraph_iso_boxProd_of_tyshkevichDecomposable
#print axioms Brualdi.RealizationGraph.SBPlusOrd.isMH_of_tyshkevichDecomposable_of_IH

/-
   PART B — manuscript Theorem 10.1 and its MainLine corollary, closed 2026-08-19.

   The general theorem is one strong induction on ground order with the five branches dispatched in
   manuscript order.  The `MainLine` statement is then an immediate specialization.
-/
#print axioms Brualdi.RealizationGraph.SBPlusOrd.mainLine_maximally_hamiltonian
#print axioms Brualdi.RealizationGraph.SBPlusOrd.realizationGraph_maximally_hamiltonian
-- ADDED 2026-08-27.  Corollary 10.2, homogeneous traceability.  It was the ONE numbered result
-- of sections 3-10 that section 11.1 had to except, being true and proved on the page with no
-- declaration behind it.  With this line the exception is gone and 11.1's claim is unqualified.
#print axioms Brualdi.RealizationGraph.SBPlusOrd.realizationGraph_homogeneously_traceable

/-
   PART B — the MainLine anti-vacuity witness, added 2026-08-19.  1 declaration.

   Seven declarations are of the form `MainLine d → …`: `separator_buffer` (Thm 6.1),
   `no_rich_failure_of_mainLine`, `splitIncidenceModel_exists_of_failure`, `sbPlus` (Thm 8.1),
   `atMostTwoExceptional`, `mainLine_MH_of_IH` (§10.2-10.3) and `mainLine_maximally_hamiltonian`.
   Had `MainLine` been unsatisfiable, every one would be VACUOUSLY TRUE and no gate here would say
   so — `lake build`, the axiom baseline and the `sorry` count all look identical either way.  The
   main theorem itself is unconditional and was never at risk; §§6, 8 and 10.2-10.3 were.

   `mainLine_witness : MainLine ![3,3,3,3,2]` closes that, on FOUNDATIONS ALONE — kernel `decide`
   only, no `native_decide`.  `G(d)` here is the octahedron: 6 realizations, every vertex carrying
   two realizable neighborhoods, 8 triangles, and not Tyshkevich-decomposable.
-/
#print axioms Brualdi.RealizationGraph.SBPlusOrd.mainLine_witness

-- ANTI-VACUITY FOR THE EXCEPTIONAL BRANCH, added 2026-08-24.  `mainLine_witness` above does NOT
-- reach it: `yFamilyPivot_degreeClass_card` forces the pivot's degree class to exactly three members
-- and `![3,3,3,3,2]`'s classes have four and one.  Without these two, `sbPlus`'s extra strength over
-- `separator_buffer` could have been dead code with no gate noticing.
#print axioms Brualdi.RealizationGraph.SBPlusOrd.yfwPivot_witness
#print axioms Brualdi.RealizationGraph.SBPlusOrd.yfw_mainLine

/-
   PART B — item D stage 1, added 2026-08-19.  3 declarations, all on FOUNDATIONS ALONE.

   Item D replaces two Barrus axioms with one narrower classical citation, and needs Barrus's
   (b) ⇒ (d): a triangle-free G(d) forces every realization to be {2K₂, C₄, chair, kite}-free.
   §6.4 already had the 2K₂ and C₄ halves — no triangle implies no RICH triangle, so those apply a
   fortiori.  These are the missing two, plus the machinery that made the second nearly free.

   `realizationGraph_complementIso` is worth more than the stage.  It carries `Graphical d`, and that
   hypothesis is not optional: truncated `Nat` subtraction is not involutive for invalid degree
   functions.  That is the same failure mode that made `barrus_theorem9_bipartite_classification`
   FALSE earlier the same day — a classification statement applied to a non-graphical `d`.  Here the
   wave carried the guard unprompted.

   The kite is the COMPLEMENT of the chair (6 edges to 4, on five vertices), so Barrus's four
   forbidden graphs are closed under complementation — 2K₂↔C₄, chair↔kite — and
   `triangle_of_induced_kite` transports rather than repeating the construction.
   Verified before dispatch: 366/366 for the isomorphism, 144/144 for each lemma.
-/
#print axioms Brualdi.RealizationGraph.SBPlusOrd.realizationGraph_complementIso
#print axioms Brualdi.RealizationGraph.SBPlusOrd.triangle_of_induced_chair
#print axioms Brualdi.RealizationGraph.SBPlusOrd.triangle_of_induced_kite

/- ======================================================================
   PART C — THE OPEN SURFACE.  No declarations currently remain here.
   NEVER add these to Part A + Part B.  See the header.
   ====================================================================== -/

-- §6's pieces, stated 2026-08-18.  `separator_buffer` is four arguments, not one, and stating them
-- separately is what makes it provable in stages.  Verified through order 7 before being written:
-- 179,442 triangles and 2,411,461 pairs, 0 failures.

-- §6.3's rich four-core lemma, stated 2026-08-18 in the form §6 consumes it.

-- §4's reductions, stated 2026-08-18.  Until now §4 had NO Lean at all, so the main theorem could
-- not close even with everything else proved -- two of §10.1's five branches had nothing behind them.

-- `sbPlus` sat here from 2026-08-18 to 2026-08-19 because Part B means `sorryAx`-FREE and it was
-- not: its argument was complete but its one named input, `separator_buffer`, was open.  It was
-- moved to Part B once on 08-18 and the gate refused it, correctly.  With `separator_buffer` proved
-- on 08-19 both moved to Part B on their own merits.  "The argument is complete" and "the
-- declaration is proved" stayed different claims throughout, which is the whole point of this file.
