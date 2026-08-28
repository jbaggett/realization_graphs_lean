#!/usr/bin/env python3
"""check_axiom_baseline.py — run AxiomBaseline.lean and GATE its output.

WHY THIS EXISTS.  `AxiomBaseline.lean` printed the trust surface; nothing checked what it printed.
On 2026-08-18 that gap had teeth: the generator traced 28 declarations and reported five cited
axioms, every figure correct, while a SIXTH cited axiom taken onto the surface the day before
(`realizationGraph_preconnected`) was invisible because no §5 declaration was in its list.  Green,
and wrong.  A count nobody asserts is a comment.

WHAT IT ASSERTS
  1. Every declaration named in the generator is actually traced, and nothing is traced that is not
     named.  Measured, not assumed: a MISTYPED name is an unknown identifier, so Lean exits 1 and
     `run_generator` aborts on the exit code -- that failure mode never reaches the parser.  What
     this assertion actually guards is the silent one: a declaration DROPPED from the list, or a
     rename that still resolves.  Neither changes any exit code; both shrink the audit.
  2. The three strata have exactly the sizes the generator's header claims, and Part A + Part B are
     NEVER summed with Part C.  `SEC_COMPUTATION.md` §11.4 reports them separately and says so.
  3. Part A and Part B carry NO `sorryAx`.  Part C carries `sorryAx` on EVERY line -- a Part C
     declaration that stops printing it has been proved and must be moved, and one that never
     printed it was never open.  Both directions are failures, because both mean the ledger is
     describing a surface that no longer exists.
  4. NO DOC COMMENT CONTRADICTS ITS OWN DECLARATION.  Added 2026-08-18 after three were found at
     once: `quotientGraph` and `quotient_adjacency` both said Theorem 5.4 "carries a `sorry`" when it
     had been proved, and the module header said "seven `sorry`s" when there were twelve.  This is
     the lane's recorded defect class -- a doc comment claiming more than its statement -- appearing
     in the UNDER-claiming direction, which is why it survived: a comment calling a proved theorem
     open reads as conservative.  It is not.  §11.4 of the manuscript was written from the first of
     those comments, so an under-claiming comment became a false published sentence.
  5. NO OPEN DECLARATION ESCAPES THE AUDIT.  Every declaration in the target's own modules that
     carries a `sorry` must appear in Part C.  Added 2026-08-18 after I fell into exactly the hole
     this file's header warns about: `fourCorner_of_hookPivot` was stated with a `sorry` and
     committed WITHOUT being added to the generator, and the gate passed, because a gate that only
     inspects the declarations it is told about cannot notice one it was never told about.  That is
     the stale-in-scope failure this whole file exists to prevent, recurring one level down.
  6. The cited axioms are exactly the expected set.  A NEW one is the event this whole file exists
     to catch, so it fails loudly and names the declarations that charge it.

WHY NOT A BYTE-COMPARE against a stored baseline.  Because of the failure recorded in the root
`CLAUDE.md`: `#print axioms` output depends on the generator's `open` context and carries a
`file:line:col` prefix, so a byte gate breaks when nothing has moved -- and it breaks in the
SAFE-LOOKING direction, which invites regenerating the baseline and discarding what the gate was
for.  This parses instead, and asserts structure.

RUN
    python3 topics/flipgraphs/realization/compute/check_axiom_baseline.py
Exit 0 = the surface is what the generator says it is.
"""
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[4]
GEN = REPO / "topics/flipgraphs/realization/compute/AxiomBaseline.lean"
FOUNDATIONS = {"propext", "Classical.choice", "Quot.sound"}

# The strata, by the count each is declared to have in the generator's header.
EXPECT = {"A": 25, "B": 90, "C": 0}   # 2026-08-27: B 89 -> 90, realizationGraph_homogeneously_traceable
                                      # ADDED -- Corollary 10.2, the one numbered result of
                                      # sections 3-10 that section 11.1 had to except.
                                      # 2026-08-25: B 90 -> 89, lemma_5_7c_common_neighborhood_isClique
                                      # CUT -- consumed by no proof in paper or Lean (Jeff, 08-25).
                                      # 2026-08-24: B 87 -> 88 (erdosGallaiSlack_nonneg_of_graphical)
                                      # -> 90 (yfwPivot_witness, yfw_mainLine)

# Cited axioms and certificates expected on this target.  A sixth entry joined on 2026-08-17 by
# Jeff's call; anything NOT on this list is the finding.
EXPECT_CITED = {
    # RETIRED 2026-08-20: `johnson_isMH` (Alspach) and `naddef_pulleyblank_baseExchange` left this
    # target with `BaseStructureJohnson`, parked into `ParkedBaseStructure`.  Their only consumers
    # -- `regularCore_base_isMH`, `nearRegular_admissible_laminar_baseFamily`,
    # `intervalLaminar_baseExchange_hamConnected` -- were unreachable from the main theorem, being
    # the superseded matroid route that manuscript section 10.4 disclaims.  The cited surface is now
    # 7 and EQUALS `realizationGraph_maximally_hamiltonian`'s trace, so the disclaimer is a property
    # of the build.  If either name reappears here, something re-imported the parked target.
    # RETIRED 2026-08-19: barrus_theorem9_triangle_free_classification is now a THEOREM.
    # It bundled the classification with a transport of maximal Hamiltonicity, which is why
    # Corollary 3.3 needed a second Barrus axiom this morning.  With (a)<=>(c) exposed
    # structurally it is derivable: triangle-free -> bipartite -> iso to a normalized family ->
    # isMH_iso.  Two Barrus axioms added today, one removed, and the two that remain are clean
    # directions of Theorem 9 rather than a classification-plus-transport package.
    # RETIRED 2026-08-19: threshold_iff_dominance_maximal is now a THEOREM.  It was a
    # biconditional, used ONCE and only through .mp, and the direction actually consumed was
    # already proved -- as `threshold_dominance_maximal` in SeparatorTheorem.lean, a 1,353-line
    # module importing no BrualdiLean and phrasing everything in its own vocabulary.  Bridging
    # the two `Realization` types made it usable.  The bridge needed no threshold-graph theory:
    # both modules already prove "count = 1 iff threshold" for their own notions, so an
    # equivalence of the carrier types chains them.  A duplicated definition had hidden a proof
    # from the axiom that assumed it.
    # RETIRED 2026-08-19: threshold_iff_unique_realization is now a THEOREM.  `IsThreshold` says
    # the realization graph has no edges; no edges plus realizationGraph_preconnected gives at
    # most one realization, and graphical gives at least one.  It cost nothing to derive because
    # the connectivity axiom was already on the surface -- so the paper loses a SOURCE
    # (Mahadev-Peled) rather than merely an entry.
    "Brualdi.RealizationGraph.realizationGraph_preconnected",
    # Seventh, Jeff's call 2026-08-18: the SUFFICIENCY direction of Erdős–Gallai, which
    # §8.2 of the manuscript already states as a known theorem with this citation.
    "Brualdi.RealizationGraph.SBPlusOrd.erdos_gallai_sufficiency",
    # Eighth and ninth, 2026-08-19, both classical and both inside the standing policy.
    # Brualdi, Combinatorial Matrix Classes (2006) Thm 3.4.1 p.63 + consequence p.65
    # (Ryser/Haber/Chen): an invariant position forces the block decomposition.
    "Brualdi.RealizationGraph.SBPlusOrd.invariantPosition_forces_block",
    # Barrus 2016 Thm 9, (a)<=>(b).  NOT a new source -- the same theorem already carries
    # barrus_theorem9_triangle_free_classification; this is a second direction of it.
    "Brualdi.RealizationGraph.barrus_theorem9_bipartite_iff_triangleFree",
    # Tenth and eleventh, 2026-08-19: INCOMING from the companion paper, not chosen here.
    # splitIncidence_buffer_of_tyshkevichIndecomposable consumes buffer_line_exists_of_cellVaries,
    # and these two ride in with it.  active_prime_cell_varies does NOT -- that is the whole
    # point of the Sec5 generalization, and its absence from this list is load-bearing.
    "Brualdi.Ledger.flipGraph_connected",
    "Brualdi.Ledger.invariantFree_nonbip_has_triangle",
    # Twelfth, 2026-08-19: Barrus 2016 Thm 9 (a)<=>(c), the structural classification.  THIRD
    # direction of an equivalence this surface already cites twice.  It exists because the older
    # barrus_theorem9_triangle_free_classification INTERNALIZES the classification -- it takes a
    # bundle of MH facts and concludes MH, so it transports exactly one property.  Corollary 3.3
    # needed the same fact to carry IsSpanning2DPCOpposite instead.  Stated structurally so any
    # property transports; with it exposed, the older axiom could become a THEOREM and the count
    # would go down rather than up.  Not attempted yet.
    "Brualdi.RealizationGraph.barrus_theorem9_bipartite_classification",
}


def run_generator():
    cmd = ("ulimit -v 67108864; LEAN_NUM_THREADS=6 "
           f"lake env lean {GEN}")          # ulimit takes KiB; 64 GiB.  never `lake -j`.
    r = subprocess.run(["bash", "-c", cmd], cwd=REPO / "lean",
                       capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"generator exited {r.returncode}:\n{r.stdout}\n{r.stderr}")
    return r.stdout


def declared_order():
    """The declarations the generator names, in order, tagged by the PART they sit under."""
    part, out = "A", []
    for line in GEN.read_text().splitlines():
        m = re.match(r"\s*PART ([ABC])\s+—|.*PART ([ABC]) — ", line)
        if m:
            part = (m.group(1) or m.group(2))
            continue
        m = re.match(r"#print axioms\s+(\S+)?\s*$", line)
        if m and m.group(1):
            out.append((part, m.group(1)))
        elif line.strip() == "#print axioms":
            out.append((part, None))          # name wrapped onto the next line
        elif out and out[-1][1] is None and line.strip() and not line.startswith("--"):
            out[-1] = (out[-1][0], line.strip())
    return out


def traced(stdout):
    """{declaration: set(axioms)} from the printed lists, which wrap across lines."""
    flat = re.sub(r"\s+", " ", stdout)
    got = {}
    for m in re.finditer(r"'([\w.]+)' (?:depends on axioms: \[([^\]]*)\]"
                         r"|does not depend on any axioms)", flat):
        got[m.group(1)] = {a.strip() for a in (m.group(2) or "").split(",") if a.strip()}
    return got


DOC_CLAIMS_SORRY = re.compile(
    r"carries a `sorry`|carry a `sorry`|is `sorry`|declaration is `sorry`|not machine-checked",
    re.IGNORECASE)
DECL = re.compile(
    r"/--(.*?)-/\s*\n\s*(?:@\[[^\]]*\]\s*)?(?:private |noncomputable |protected )*"
    r"(?:theorem|lemma|def|structure|abbrev|instance)\s+([A-Za-z_][\w']*)(.*?)"
    r"(?=\n(?:/--|(?:@\[|private |noncomputable |protected )*"
    r"(?:theorem|lemma|def|structure|abbrev|instance|end|namespace)\s))", re.S)
COUNT_WORDS = {"two": 2, "three": 3, "four": 4, "five": 5, "six": 6, "seven": 7,
               "eight": 8, "nine": 9, "ten": 10, "eleven": 11, "twelve": 12,
               "thirteen": 13, "fourteen": 14, "fifteen": 15}
SORRY_LINE = re.compile(r"(?m)^\s*sorry\s*$")


def open_declarations_audit(named):
    """Every declaration carrying a `sorry` must be named in Part C.

    The strata check counts what the generator lists; this checks what the SOURCE contains.  Without
    it a new `sorry` is invisible to the audit until somebody remembers to add it, which is precisely
    how a baseline goes stale in scope.
    """
    part_c = {n.split(".")[-1] for p, n in named if p == "C" and n}
    problems = []
    root = REPO / "lean" / "BrualdiLean" / "RealizationGraph"
    for f in sorted(root.glob("*.lean")):
        if f.name == "HladikFink.lean":
            continue                     # parked in its own target, `sorry`-carrying by design
        src_text = f.read_text(errors="replace")
        for name, body in split_declarations(src_text):
            if not SORRY_LINE.search(body):
                continue
            if name is None:
                problems.append(f"{f.name}: an ANONYMOUS declaration carries a `sorry`")
            elif name.split(".")[-1] not in part_c:
                problems.append(f"{f.name}: `{name}` carries a `sorry` but is not in Part C")
    return problems


MODULE_SIZES = {
    # SEC_COMPUTATION.md 11.1 says Section 7 is "proved in a module of N declarations".  That
    # number was hand-counted and sat in the very subsection whose opening sentence promises the
    # counts are "produced by a gate rather than by hand" -- so it could drift silently, which is
    # the exact failure this file's own header records for its stratum sizes (stale 08-18 to 08-20).
    # It is asserted here now.  If you add a declaration to QStar.lean, this fails and the
    # manuscript sentence has to move with it.  That is the point.
    # 279 -> 284 on 2026-08-24: Lemma 7.10's arm-exchange clause got its five declarations, closing
    # the gap the blind back-translation found.  The gate did exactly what it exists for.
    "QStar.lean": 284,
}

# LEADING ATTRIBUTES, fixed 2026-08-23 -- TWICE, and the second time is the instructive one.
#
# The original patterns required the declaration keyword to START the line, so every `@[simp]`
# declaration was invisible: the module count read 266 where the module has 279, missing 13 -- among
# them `dualSet_dualSet`, which the note's OWN axiom gate names.  The same blind spot sat in
# `open_declarations_audit`, the check whose whole job is that no `sorry` escapes the audit.
#
# The first repair widened the two pattern HEADS and added a regression test.  An adversary then
# showed the repair was half a repair and the regression was worthless: the audit's LOOKAHEAD
# terminator still carried a bare `@\[`, which cannot consume `@[simp] `, so an attributed
# declaration was not recognised as a boundary and its `sorry` was attributed to the PRECEDING
# declaration -- and the regression had rebuilt its own copy of the pattern, so narrowing the
# production one left it green.  A regression that does not run production code tests nothing.
#
# So: ONE pattern, compiled once, used by production and by the regression, and the audit is a
# SPLITTER rather than a lookahead -- chunk boundaries are declaration starts and scope enders, which
# removes the terminator problem instead of widening it.
_ATTR  = r"(?:@\[[^\]]*\]\s*)*"
_MODS  = r"(?:private |protected |noncomputable |scoped |local )*"
# TWO kind-lists, deliberately.  COUNTING is about NAMED results, which is what the manuscript's
# "a module of N declarations" means, so `example` is excluded -- QStar carries five of them and they
# are checks, not results.  CHUNKING must see EVERYTHING that can carry a proof, `example` included,
# or an anonymous declaration could hide a `sorry` by not being recognised as a boundary.
_COUNT_KINDS = r"(?:theorem|lemma|def|abbrev|instance|structure)"
_KINDS = r"(?:theorem|lemma|def|abbrev|instance|structure|example)"
_ENDERS = r"(?:end|namespace|section|mutual|open|variable|import)\b"

DECL_ANY = re.compile(r"^" + _ATTR + _MODS + _ATTR + _COUNT_KINDS + r"\s", re.M)
DECL_CHUNK = re.compile(r"^" + _ATTR + _MODS + _ATTR + _KINDS + r"\s", re.M)
CHUNK_START = re.compile(r"(?m)^(?=" + _ATTR + _MODS + _ATTR + _KINDS + r"\s|" + _ENDERS + r")")
DECL_NAME = re.compile(r"^" + _ATTR + _MODS + _ATTR + _KINDS + r"\s+([A-Za-z_][\w'.]*)")


def split_declarations(text):
    """(name_or_None, chunk) for every declaration-like block; a SPLITTER, not a lookahead.

    Whatever sits between two starts belongs to the first, so an unrecognised form can never
    silently hand its body to its neighbour -- which is exactly how the lookahead version failed."""
    cuts = [m.start() for m in CHUNK_START.finditer(text)] + [len(text)]
    out = []
    for a, b in zip(cuts, cuts[1:]):
        chunk = text[a:b]
        if not DECL_CHUNK.match(chunk):        # chunking sees `example`; counting does not
            continue
        m = DECL_NAME.match(chunk)
        out.append((m.group(1) if m else None, chunk))
    return out


def open_declarations_audit(named):
    """Every declaration carrying a `sorry` must be named in Part C.

    The strata check counts what the generator lists; this checks what the SOURCE contains.  Without
    it a new `sorry` is invisible to the audit until somebody remembers to add it, which is precisely
    how a baseline goes stale in scope.
    """
    part_c = {n.split(".")[-1] for p, n in named if p == "C" and n}
    problems = []
    root = REPO / "lean" / "BrualdiLean" / "RealizationGraph"
    for f in sorted(root.glob("*.lean")):
        if f.name == "HladikFink.lean":
            continue                     # parked in its own target, `sorry`-carrying by design
        src = f.read_text(errors="replace")
        for m in re.finditer(r"(?m)^" + _ATTR + _MODS + _ATTR +
                             r"(?:theorem|lemma|def|abbrev|instance)\s+([A-Za-z_][\w']*)(.*?)"
                             r"(?=\n(?:/--|(?:@\[|private |noncomputable |protected )*"
                             r"(?:theorem|lemma|def|structure|abbrev|instance|axiom|end|namespace)\s))",
                             src, re.S):
            name, body = m.group(1), m.group(2)
            if SORRY_LINE.search(body) and name not in part_c:
                problems.append(f"{f.name}: `{name}` carries a `sorry` but is not in Part C")
    return problems


MODULE_SIZES = {
    # SEC_COMPUTATION.md 11.1 says Section 7 is "proved in a module of N declarations".  That
    # number was hand-counted and sat in the very subsection whose opening sentence promises the
    # counts are "produced by a gate rather than by hand" -- so it could drift silently, which is
    # the exact failure this file's own header records for its stratum sizes (stale 08-18 to 08-20).
    # It is asserted here now.  If you add a declaration to QStar.lean, this fails and the
    # manuscript sentence has to move with it.  That is the point.
    "QStar.lean": 284,
}

def module_size_audit():
    """Declaration counts the manuscript quotes, checked against the modules."""
    problems = []
    root = REPO / "lean" / "BrualdiLean" / "RealizationGraph"
    for fname, claimed in MODULE_SIZES.items():
        src = (root / fname).read_text(errors="replace")
        actual = len(DECL_ANY.findall(src))
        if actual != claimed:
            problems.append(
                f"{fname}: manuscript 11.1 says {claimed} declarations, the module has {actual}")
    return problems


def doc_comment_audit():
    """Every prose claim in the module about `sorry` status, checked against the declarations."""
    problems = []
    root = REPO / "lean" / "BrualdiLean" / "RealizationGraph"
    for f in sorted(root.glob("*.lean")):
        src = f.read_text(errors="replace")
        for m in DECL.finditer(src):
            doc, name, body = m.group(1), m.group(2), m.group(3)
            if DOC_CLAIMS_SORRY.search(doc) and not SORRY_LINE.search(body):
                problems.append(f"{f.name}: `{name}`'s doc comment claims a `sorry` it does not have")
        actual = len(SORRY_LINE.findall(src))
        # Only the MODULE HEADER -- the text before the first import -- makes a file-wide count
        # claim.  A "the two `sorry`s above" further down is a local claim about named statements
        # and is correct in context; HladikFink.lean has exactly that and it is not a defect.
        head = src.split("\nimport ", 1)[0]
        for m in re.finditer(r"\b(" + "|".join(COUNT_WORDS) + r")\s+`sorry`s", head):
            claimed = COUNT_WORDS[m.group(1).lower()]
            if claimed != actual:
                problems.append(f"{f.name}: prose says {claimed} `sorry`s, the file has {actual}")
    return problems


def regression_attributed_declarations():
    """The 2026-08-23 defects, as tests that run every time -- through PRODUCTION code.

    The first version of this function rebuilt its own copy of the audit pattern, so narrowing the
    production one left it green.  It therefore tested nothing.  Everything below goes through
    `DECL_ANY` and `split_declarations`, which are what the gate actually uses."""
    problems = []

    counting = ("@[simp] theorem attributed_one : True := trivial\n\n"
                "@[simp] private theorem attributed_two : True := trivial\n\n"
                "private theorem plain_one : True := trivial\n")
    seen = len(DECL_ANY.findall(counting))
    if seen != 3:
        problems.append(f"REGRESSION: the module-size pattern sees {seen} of 3; a declaration "
                        "behind an attribute is invisible again")

    # THE CASE THE FIRST REPAIR MISSED: an attributed declaration AFTER a plain one.  The old
    # lookahead handed this `sorry` to `plain_before` and never returned `attributed_open`.
    cases = [
        ("attributed after plain",
         "theorem plain_before : True := trivial\n\n"
         "@[simp] theorem attributed_open : True := by\n  sorry\n\n"
         "theorem after_it : True := trivial\n",
         "attributed_open"),
        ("structure", "structure S_open where\n  f : Nat := by\n    sorry\n", "S_open"),
        ("scoped instance",
         "scoped instance inst_open : Inhabited Nat := by\n  sorry\n", "inst_open"),
    ]
    for label, text, want in cases:
        got = {n for n, b in split_declarations(text) if SORRY_LINE.search(b)}
        if want not in got:
            problems.append(f"REGRESSION [{label}]: the `sorry` is not attributed to `{want}`; "
                            f"the audit blamed {sorted(got) or 'nothing'}")

    # an ANONYMOUS declaration carrying a sorry must still be seen -- it cannot be named in Part C,
    # so it has to be reported rather than skipped
    anon = "example : True := by\n  sorry\n"
    if not any(n is None and SORRY_LINE.search(b) for n, b in split_declarations(anon)):
        problems.append("REGRESSION: an anonymous declaration carrying a `sorry` is invisible")
    return problems


def main():
    named = declared_order()
    got = traced(run_generator())
    fail = regression_attributed_declarations()

    missing = [n for _, n in named if n not in got]
    if missing:
        fail.append(f"named in the generator but NOT traced (typo silently drops a declaration): {missing}")
    extra = [n for n in got if n not in {x for _, x in named}]
    if extra:
        fail.append(f"traced but not named -- the parser and the generator disagree: {extra}")

    counts = {p: sum(1 for q, _ in named if q == p) for p in "ABC"}
    if counts != EXPECT:
        fail.append(f"stratum sizes {counts} != the header's {EXPECT}")

    for part, name in named:
        if name not in got:
            continue
        has_sorry = "sorryAx" in got[name]
        if part in ("A", "B") and has_sorry:
            fail.append(f"PART {part} declaration carries sorryAx and is NOT proved: {name}")
        if part == "C" and not has_sorry:
            fail.append(f"PART C declaration carries NO sorryAx -- it is proved, move it to Part B: {name}")

    cited = {}
    for _, name in named:
        for ax in got.get(name, set()) - FOUNDATIONS - {"sorryAx"}:
            cited.setdefault(ax, []).append(name)
    for ax, users in sorted(cited.items()):
        if ax not in EXPECT_CITED:
            fail.append(f"UNEXPECTED cited axiom / native_decide certificate {ax}, charged by {users}")
    for ax in sorted(EXPECT_CITED - set(cited)):
        fail.append(f"expected cited axiom {ax} is charged by NOTHING -- the list or the tree moved")

    # THE MAIN THEOREM'S OWN TRACE, asserted rather than bounded.  Added 2026-08-24 after an
    # adversary pass on the assembly pointed out that everything above is a UNION over the 115
    # traced declarations, which bounds the main theorem's trace from above and never settles it.
    # That is the safe direction -- the union can over-list, not under-list -- but it is exactly the
    # "stale in SCOPE rather than in count" failure this file's own header warns about, one level up:
    # `SBPlusOrd.lean` says the seven are "read off this declaration's own axiom trace", and §10.4
    # of the manuscript rests on that trace being exactly the seven.
    #
    # ⚠ The first version of this comment justified the assertion with an example the OLD gate already
    # caught: an unexpected axiom like `naddef_pulleyblank_baseExchange` is not in `EXPECT_CITED`, so
    # the union loop above already fails on it whoever charges it.  The genuinely new coverage is the
    # OTHER direction -- MAIN's trace being a strict SUBSET of the seven, which the union check cannot
    # see at all and the `MISSING expected` branch below does.  Corrected same day by an adversary.
    MAIN = "Brualdi.RealizationGraph.SBPlusOrd.realizationGraph_maximally_hamiltonian"
    if MAIN not in got:
        fail.append(f"the main theorem {MAIN} was not traced at all")
    else:
        own = got[MAIN] - FOUNDATIONS - {"sorryAx"}
        if own != EXPECT_CITED:
            for ax in sorted(own - EXPECT_CITED):
                fail.append(f"the MAIN THEOREM's own trace carries unexpected {ax}")
            for ax in sorted(EXPECT_CITED - own):
                fail.append(f"the MAIN THEOREM's own trace is MISSING expected {ax} -- "
                            f"the seven are no longer its trace, only the union's")
        if "sorryAx" in got[MAIN]:
            fail.append("the MAIN THEOREM carries sorryAx")

    # ARTIFACT FRESHNESS.  Added 2026-08-24 after an adversary pass on Lemma 8.3d pointed out that
    # `lakefile.toml` has `defaultTargets = ["BrualdiLean"]` and `BrualdiLean.lean` does NOT import
    # `SBPlusOrd` -- nothing in the tree does.  So a bare `lake build` is GREEN without elaborating a
    # single line of §8, and this repo has the identical failure on record for `Sec5`.  The documented
    # procedure names `Realization` and tests the .olean, but a gate that trusts whatever artifact
    # happens to be on disk inherits the hazard.  Assert the artifact is present and not older than
    # its source.
    # WIDENED 2026-08-24, same day, after an adversary produced a witness against the first version:
    # it compared `SBPlusOrd.olean`/`QStar.olean` against their OWN sources only.  Edit
    # `InterfaceSaturation.lean` -- which `SBPlusOrd` imports -- and do not rebuild, and both named
    # oleans are still newer than their own sources, the generator loads the stale import, and the
    # gate PASSES while its own message says the trace describes a source no longer on disk.  The
    # comparison is now against the newest source anywhere in the directory.
    # `SBPlusOrd` imports every other module of this directory that the audit touches -- including
    # `QStar` and `InterfaceSaturation` -- so ITS artifact is the one that must postdate every source
    # here.  `QStar` sits below it and is checked against its own source only: holding QStar.olean to
    # a directory-wide maximum is a FALSE POSITIVE, and the first version of this check did exactly
    # that and failed on a clean tree.  (Found by running it, minutes after an adversary found the
    # opposite error in the version before.)
    srcdir = REPO / "lean" / "BrualdiLean" / "RealizationGraph"
    newest_src = max((f.stat().st_mtime for f in srcdir.glob("*.lean")), default=0.0)
    bounds = {"RealizationGraph/SBPlusOrd": newest_src,
              "RealizationGraph/QStar": (srcdir / "QStar.lean").stat().st_mtime}
    for rel, bound in bounds.items():
        art = REPO / "lean" / ".lake" / "build" / "lib" / "lean" / "BrualdiLean" / f"{rel}.olean"
        if not art.exists():
            # NOTE: in practice `run_generator` aborts first, since `lake env lean` does not build and
            # the generator imports these modules directly.  Kept as a belt-and-braces check, not as
            # the thing that catches a bare `lake build`; the mtime comparison below is the new cover.
            fail.append(f"{art.name} is MISSING -- `lake build Realization` did not run, "
                        f"or ran against a different target")
        elif art.stat().st_mtime < bound:
            fail.append(f"{art.name} is OLDER than a source it is built from -- the trace below "
                        f"describes a source that is no longer on disk")

    size_problems = module_size_audit()
    fail.extend(size_problems)
    doc_problems = doc_comment_audit()
    fail.extend(doc_problems)
    open_problems = open_declarations_audit(named)
    fail.extend(open_problems)

    print(f"declarations traced : {len(got)}")
    print(f"module-size audit   : {'clean' if not size_problems else str(len(size_problems)) + ' PROBLEM(S)'}")
    print(f"doc-comment audit   : {'clean' if not doc_problems else str(len(doc_problems)) + ' PROBLEM(S)'}")
    print(f"open-declaration audit: {'clean' if not open_problems else str(len(open_problems)) + ' PROBLEM(S)'}")
    print(f"strata              : A={counts['A']} proved, B={counts['B']} proved, "
          f"C={counts['C']} open   (NEVER summed)")
    print(f"cited axioms        : {len(cited)}")
    for ax, users in sorted(cited.items()):
        print(f"  {ax}")
        for u in users:
            print(f"      charged by {u}")
    if fail:
        print("\nRESULT: FAIL")
        for f in fail:
            print(f"  - {f}")
        return 1
    print("\nRESULT: PASS — the surface is what the generator says it is.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
