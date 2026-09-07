# Realization graphs are maximally Hamiltonian — the Lean development

The formal development accompanying *Maximal Hamiltonicity of realization graphs of degree
sequences*. It proves, in Lean 4 against mathlib, that

> the realization graph `G(d)` of every graphical degree sequence is **maximally Hamiltonian** —
> Hamilton-laceable when it is bipartite and Hamilton-connected otherwise.

That is `realizationGraph_maximally_hamiltonian` in `Realization/SBPlusOrd.lean`.
It is unconditional, carries no `sorry`, and its axiom trace is the ambient foundations
`propext`, `Classical.choice`, `Quot.sound` together with **seven cited results from the literature
and nothing else**.

**This repository is a verification artifact, not a second copy of the paper.** Read the paper for
the mathematics. Read this to check that what the kernel proves is what the paper claims — which is
why the largest section below is the one listing every place the two differ.

## Building it

```bash
ulimit -v 67108864          # 64 GiB of ADDRESS SPACE, in KiB.  Not optional: without it the build
                            # dies with a bare `exit 134  failed to create thread`, which is
                            # unsearchable if you do not know to expect it.  This is address space,
                            # not memory — peak RSS on this build is about 3.3 GB — so raising it
                            # does not raise your OOM risk, and lowering the thread count instead
                            # makes the problem worse.
lake exe cache get            # FETCH MATHLIB'S PREBUILT CACHE FIRST.  `lake build` does not do
                              # this for you: without it, Lake compiles mathlib from source, which
                              # is hours instead of the seventeen seconds the cache takes.  There
                              # is no warning; it simply starts building and does not stop.
LEAN_NUM_THREADS=6 lake build Realization
```

`lake -j` does not exist in Lake 5.0.0 and `lake -Kjobs=N` silently does nothing; `LEAN_NUM_THREADS`
is the knob. With the cache fetched, the remaining work is the companion development and this
paper's 25 modules.

**A pass is `exit 0` AND the expected `.olean` on disk.** A bare green is not a gate: a root file
once failed to import a module and `lake build` stayed green while errors accumulated behind it.

## What a passing audit prints

```bash
python3 compute/check_axiom_baseline.py
```

```
declarations traced : 115
open-declaration audit: clean
strata              : A=25 proved, B=90 proved, C=0 open   (NEVER summed)
cited axioms        : 7
RESULT: PASS — the surface is what the generator says it is.
```

The three strata are reported separately and **are never summed**; the paper's Section 11 says so and
this gate enforces it.

```bash
python3 compute/check_qstar_note_axioms.py
```

checks the other claim Section 11.1 makes about the kernel — that Section 7's development charges no
cited axiom of any kind — over all 46 of its declarations.

Both gates detect which layout they are in. Two others that ship in the authors' tree are **not**
here: `check_axiom_provenance.py` reads the manuscript's section sources and
`check_trust_surface_pointers.py` reads `TRUST_SURFACE.md`, and neither document belongs in this
repository. They were removed rather than shipped inert — a gate that cannot run, inside a
verification artifact, is worse than no gate.

## How this repository is put together

```
Realization/      the 25 modules of this paper
compute/          the axiom-baseline generator, the gates that read it, and the scripts
                  behind every number the paper prints
results/          pinned outputs of those gates and scripts
lakefile.toml     one library target; a pinned require on the companion
```

⚠ **The modules are `Realization.*` here and `BrualdiLean.RealizationGraph.*` in the authors' working
tree, and the difference is forced.** `brualdi_lean` is a dependency, and it declares a library that
owns the whole `BrualdiLean` module namespace; two packages cannot both own it, and while ours tried
to, this repository did not build at all — every module resolved against the dependency's source
directory, which does not contain them. Lean namespaces are independent of module paths, so
`namespace Brualdi.RealizationGraph` is untouched: **every declaration name, and therefore every
axiom trace the paper cites, is the same on both sides.** Only `import` lines differ.

**The companion development is a pinned dependency, not a vendored copy.** The `require` in
`lakefile.toml` points at `brualdi-interchange-lean` at tag `arxiv-v3`, which is the artifact that
paper's own arXiv submission cites. Depending rather than copying links two papers to one immutable
object instead of creating a second, keeps provenance legible — a reader sees which 25 modules are
this paper's rather than hunting through 78,000 lines for them — and records *which version this
paper was verified against*, which a copy silently loses the moment either side is corrected.

The import closure is **43 modules, about 78,000 lines**: 25 here and 18 from the companion, and
those 18 are exactly that paper's frozen closure.

The companion repository is **public**, so this dependency resolves for anyone; no credentials are
needed to build.

⚠ **A git dependency has a failure mode a copy does not**: rename the account, move the repository or
lose the tag and the build stops reproducing. That is a real risk on the horizon a verification
artifact is for. A self-contained frozen snapshot — every dependency vendored at its pinned revision,
buildable with no network beyond the toolchain — is what the paper should cite for archival, and it
is not cut yet.

## The scripts behind the printed numbers

Section 11.4 of the paper says the scripts that produced the numbers quoted there are in this
repository. They are in `compute/`, alongside the Lean gates, and `results/README.md` maps each one
to the sentence it supports and holds its pinned output.

Four of them the paper names by path, so they are here under exactly those names:
`sec10_walkthrough_build.py`, `sec10_walkthrough_instance_sweep.py`, `sec63_witnesses.py` and
`sec64_two_active_lines_seal.py`. The rest support Section 11.2's five computational claims,
Section 11.3's census and Section 11.4's independent reproduction.

Each script re-derives its object rather than reading a stored answer, and most refuse to report
success unless their own checks pass — `sec10_walkthrough_build.py`, for instance, runs Section
10.2's construction step by step and will not emit unless the result really is a Hamilton
`G_0`--`G_1` path of `G(d)`.

**Two of them need `numpy` and `scipy`** (`skeleton_test.py`, for the polytope skeleton). The others
need only the standard library. Paths are derived from each script's own location, so they run from a
clone; where a script writes structured output it goes to `compute/data/`, which is not tracked.

⚠ **One claim's script did not exist until this deposit.** Section 11.2's "the running example is the
smallest of its kind" had been verified during a 2026-09-06 accuracy pass and recorded in prose,
which is not the same as being reproducible. `sec11_yfamily_census.py` was written for this
repository: it enumerates the realizations from scratch, applies the same bad-template predicate the
Section 7 seals use, and refuses to emit unless it reproduces both the counts and all four
order-six witnesses the paper prints. It does.

## How the Lean differs from the printed proof

A reader who opens a formalization expects the theorems to be the paper's theorems. Where that is not
literally true, saying so is the difference between a verification artifact and a claim.

---

### The Lean statement is not always the printed sentence

**Theorem 7.7.** The paper states it in **Y-family** vocabulary — *"unless `F` is a Y-family and
`{A,B}` is its universal pair."* The Lean's `qstar` states it in **clique-sum** vocabulary:
`HasHamPath (exchangeGraph F) A B ↔ ¬ IsCliqueSum F A B`. These are equivalent for shifted families,
and that equivalence is **Theorem 7.6, which is itself proved here** — but they are not the same
sentence. One consequence is visible in the dependency graph: `qstar` invokes Lemma 7.4 and *not*
Theorem 7.6, where §7.6's prose describes the obstruction half as "Lemma 7.4 together with Theorem
7.6". Theorem 7.6 enters one step later, at Corollary 7.8.

**Lemma 7.10, the arm-exchange clause.** The paper says *"the two arms exchanged: the inner arm of `F`
maps onto the outer arm of `F*`."* **No declaration states that.** What is proved is the containment
identity the clause is derived from — `X ⊆ u ∪ v ↔ dualSet u ∩ dualSet v ⊆ dualSet X` — together with
the fact, supplied inline in Lemma 7.10's proof and not formalized, that inner-arm membership *is*
`X ⊆ u ∪ v` and outer-arm membership *is* `X* ⊇ u* ∩ v*`. Nothing in the tree relates `yInnerArm` or
`yOuterArm` to the duality. *Found 2026-08-24 by a blind back-translation; the gate's labels were
corrected to claim the identity rather than the clause.*

**Corollary 7.9.** The paper hypothesizes a **Gale-greatest member**. Until 2026-08-23 every carrier
instead hypothesized the **principal equation** `X ∈ F ↔ (X.card = κ ∧ GaleLE X M)`, and those are
**not** equivalent: the equation never forces `M.card = κ`, hence never forces `M ∈ F`, so an `M` of
the wrong size can cut out `F` while lying outside it. `qstar_hamConnected_of_galeGreatest` now states
the printed form. *Found 2026-08-23 reading prose against Lean.*

### A printed result carried by several declarations, or by none of its own

- **Theorem 4.4** is not a lemma in the Lean; its dispatch **is** the induction's own case split.
- **Lemma 5.7b** (vicinal trichotomy) is its three regimes, proved separately in
  `InterfaceSaturation.lean`; the three together are the lemma.
- **Theorem 7.11** has a carrier, `crossingLemma`, but that is a thin wrapper — the case analysis,
  the range reduction and the duality transports live in `not_crossingFailure_general`.
- **Theorem 5.4** is two claims and the correspondence table names one carrier. `quotient_adjacency`
  (`SBPlusOrd.lean:157`) is the existence biconditional and says nothing about *how many* connectors
  there are; the quantitative *"with at least `f(a) − f(b)` choices"* clause is
  `residualConnectorCandidates_card_lower` (`QuotientAdjacency.lean:394`) together with its S-side
  image `sSideConnectorTargets`. Found 2026-08-24 while applying F3, and worth an entry because a
  reader who looks up 5.4 in the table and reads only `quotient_adjacency` would conclude the printed
  count is unbacked. It is backed, and it is what `theorem_5_7_cross_degree` uses.

### Definitions broader in Lean than in the paper

- **`GaleLE`** is defined by upper-tail counts on **arbitrary** finite sets. §7.1's Gale order is for
  sets of equal size and is stated two ways; the kernel reasons in the threshold form and
  `galeLE_iff_pointwise` proves the two agree. This breadth is not cosmetic — it is exactly why the
  principal equation above fails to force `M ∈ F`.
- **`exchangeGraph`** does not require members to be equicardinal, so symmetric difference two could
  in principle be two insertions. `IsShifted` supplies equal cardinality at every use, and §7.1 works
  inside `J(n,k)` where it is ambient.
- **`IsShifted`** bundles nonemptiness and fixed cardinality into the definition where the paper
  carries them as standing conventions.
- **`yFamily_isCliqueSum` is vacuous for `k ≤ 1`.** Intended: §7.5 defines `F(k;r,s)` only for
  `k ≥ 2`. Satisfiability at `k = 2` is exhibited in `compute/`.

### Cited axioms: where the encoding differs from the source

Full detail per axiom is in `TRUST_SURFACE.md` §3, including each source statement quoted from the
article. Two differences a reader should not have to find:

- **Erdős–Gallai (A4).** The source ranges `j` over `1, …, n−1`; the axiom quantifies over **all**
  `t ≤ Fintype.card W`. The axiom therefore **assumes more** than the source provides — a burden on
  the caller, never a stronger conclusion.
- **Fulkerson–Hoffman–McAndrew (A3).** The applicable result is their **Theorem 5.2** (ordinary
  graphs), not the general Theorem 4.1, whose even-set hypothesis §5 of that paper discharges for the
  all-capacities-one case.
- **Barrus Theorem 9 (A2)** requires a graphicality hypothesis and **is false without it** — found
  2026-08-19 by adversary, certificate archived in `results/`.

### A divergence that was found and closed, recorded because it is the pattern

**Theorem 9.2.** The paper's printed proof opened by taking *"a matching of the connector graph
saturating its smaller side"*, and **nothing in the Lean states that conclusion**; `obi`'s 178-line
proof contains no matching at all and routes through the signed identity instead. So the Lean proved
the theorem by a different argument than the paper printed. **Resolved 2026-08-20 on Jeff's call by
rewriting the prose to the argument the kernel checks**, on the reasoning that there is no reason for
the printed route and the checked route to differ. The two Hall engines it would have needed remain in
the tree, unconsumed.

### Two proofs were shortened after the first push, and the surface did not move

`QStar.lean` and `SBPlusOrd.lean` here carry shorter internal proofs than the versions pushed on
2026-08-28, and two modules are new: `EqualityCase.lean` and `TightUnion.lean`. The substantive
change is Lemma 8.3d. It propagated a lower Erdős–Gallai witness upward by a slack recurrence on the
sorted degree sequence — the paper's longest internal argument — and it now argues instead that a
union of equal-sized tight sets whose vertices all have degree at least that size is itself tight,
which reaches the larger prefix in one step. The manuscript prints the second argument, so the
development had to as well.

**Nothing about what is proved changed, and that was checked rather than assumed.** Two gates compare
the shortened development against the one it replaces: one reads the axiom trace of every audited
declaration, the other `#check`s every one and compares the printed type. Both report the same 115
declarations, the same axioms declaration for declaration, and — this is the half a name-and-axiom
comparison cannot see — the same statements. A dropped hypothesis keeps a theorem's name and its
axioms, so only the type comparison rules one out.

### What is not machine-checked at all

- §11.3's **order-seven census** ran on separate hardware; only its summary line survives, and §11.4
  says so.

---

**Excluded, deliberately, and the README should say so rather than leave gaps:** `ParkedHladikFink`
and `ParkedBaseStructure` (both `sorry`-carrying by design, both off the audited surface), the other
lanes' `RealizationGraph/` modules that share the directory but not the target — `MatroidTrackB*`,
`TraversalT2/*`, `Keystone*`, `Proposition43Wave35*` — and the ~176 MB of `compute/data/`.

That last exclusion is worth stating precisely, since **the directory `RealizationGraph/` is shared by
four papers**. Copying it wholesale would ship three other lanes' work, including `native_decide`
certificates that this paper's trust surface claims not to have. The filter is the target's import
closure, not the directory listing.

## Mechanization detail that the paper points here for

**Jeff, 2026-08-24: "The mechanization section in the paper is much too long. Most of that belongs in
the repo readme file."** §11 was cut from **1,846 words to 1,315** (5.0% of the paper to 3.7%). What a
paper owes is the claim, the accounting and the disclosures; what a repository owes is the detail that
lets someone reproduce them. Everything below was removed from the manuscript and must appear in the
README, or it has been deleted rather than moved. It is reproduced here verbatim where the sentence
was already right.

**Nothing was removed that is a claim or a disclosure.** The sampled-seal admission, the skipped and
undecided counts, "every skipped instance is reported as skipped and none as passed", the
Tyshkevich-convention divergence, the two enumerations of the Theorem 7.7 rate, and the
available-on-request sentence all stayed in the paper. What left is method, provenance and history.

### From §11.1 — how Section 7's formalization is put together

* **The Gale order agrees with itself.** *"Section 7.1 states it pointwise on sorted entries and uses
  the threshold form interchangeably, and the module proves the two agree, so the order the kernel
  reasons about is the order the section defines."*
* **What attaches Section 7 to the rest.** *"Theorem 5.3 and Corollary 5.5 identify the neighborhood
  quotient with the Johnson graph of a shifted family, which is what allows Theorem 7.7 to be applied
  to a realization graph at all. Until they were proved, the formalization of Section 7 stood complete
  and unused."*
* **Where the text was brought to the formal route.** Section 9.3 and Lemma 7.4 are the two places.
  Lemma 7.4 in detail: *"the text proved its existence half by exhibiting the paths while the
  formalization derived that half from Theorem 7.7. The text now follows the formal route — Lemma 7.4
  is the obstruction alone, and the other pairs are recorded after Corollary 7.8."* This item overlaps
  the divergence section above and belongs in whichever of the two the README keeps.

### From §11.1 — the six conditions the gate fails on

The paper now says there are six and points here. They are: a wrong stratum count; a `sorry` anywhere
in the audited surface; a declaration named but not traced; a doc comment that contradicts its own
declaration; any cited axiom outside the expected list; a module whose declaration count has moved
away from the figure the manuscript quotes. **Print the passing output too** — 115 declarations,
strata 25-90-0, seven cited axioms, zero `sorry` — because a verification artifact that does not tell
you what success looks like cannot be used to check anything.

### From §11.1 — why the Tyshkevich hypothesis was replaced, which is history and not a convention

*"Tyshkevich indecomposability was for a time carried by a criterion — that a sequence is decomposable
exactly when Erdős–Gallai holds with equality at some rank — which is false in both directions, the
path on four vertices being indecomposable with an equality and a sequence with an isolated vertex
decomposable with none."* The paper keeps the divergence that is still live (the `∃`-over-realizations
reading against the canonical decomposition); this is the record of the stand-in that preceded it.

### From §11.2 — where the enumeration figures come from

* **The 13,888.** *"There are 127 nonempty shifted families of rank two on `[8]`; a family with one
  member has no pair to test, and the 13,888 is the number of pairs those 126 contribute between
  them."*
* **The range that starts at `[2]`.** *"The range starts at `[2]` because the producing sweep does;
  grounds `[4]` through `[8]` alone contribute 15,469 of those instances and all 70 of the
  clique-sums, the two smallest grounds carrying none."*
* **Why the rate is evidence of tightness.** *"The rank-two count rises by exactly one per ground
  order, which is the number of rank-two Y-families available at that order, so the sweep confirms
  both halves of the theorem rather than merely the absence of counterexamples."*
* **The declaration behind "the exhibited families really are shifted"** is `yFamily_isShifted`
  (`QStar.lean:4144`). ⚠ The manuscript named it **`Y-familyFamily_isShifted`**, which is not a Lean
  identifier and never was — a **rename-sweep artifact** from the 2026-08-23 clique-sum/Y-family
  renaming, which rewrote the `y` in `yFamily_isShifted` and then doubled the word. It shipped in the
  PDF. Name declarations in the README from the tree, never from the prose.

### From §11.3 — how each order-seven instance was decided

*"Of those, 64 have a single realization and are maximally Hamiltonian by the convention of Section 2,
137 were settled by exact search, and 130 by the Chvátal–Erdős condition; the remaining 9 were left
undecided by a search cap."* 64 + 137 + 130 = 331, which is the decided count the paper still quotes,
so the README is what makes that number checkable.

### The E3-sat pointer that used to be here — STRUCK 2026-08-24, Jeff's call

The list above carried *"the E3-sat end-to-end seal defect, disclosed in §11.5."* **There is no
§11.5**, and `PAPER.md` contains no occurrence of "E3-sat". It was traced on 2026-08-24: E3-sat —
*every base interface has a matching saturating its smaller side* — belongs to the **superseded**
matroid/base route, whose modules were parked in `ParkedBaseStructure` on 2026-08-20 and which this
manuscript does not take. **There is no undischarged obligation and nothing to disclose.**

**The reference was not invented, and the reason is worth keeping.**
`lean/Realization/InterfaceSaturation.lean` — the module carrying §5.4 — was *titled*
"Interface saturation (E3-sat)" and still contains that route's apparatus: `edge_component_biregular`,
`edgeFreeComponent_support_eq_singleton`, `leftPart`/`rightPart`, and `biregular_matching`, the last
being E3-sat's statement in general form, still labelled "Item 5". **All four are consumed by
nothing**, and §5.4 says as much — *"We record that and do not use it"*. So the Lean carries more than
the paper claims, which is the safe direction. The module header now says so.

⚠ **One thing the README should carry, because it is not obvious**: `biregular_matching` **is** among
the 115 audited declarations while nothing on the main theorem's cone reaches it. A reader taking
"115 audited declarations" to mean *the declarations Theorem 10.1 rests on* would be wrong. This is
the mirror of §5.6 of the trust surface, which records the opposite case — the prism declarations are
load-bearing and are **not** among the 115. Whether the four should stay on the audited surface is an
open question for Jeff; keeping them costs nothing. Full trace:
`results/2026-08-24e_e3sat_divergence_and_witnesses.md`.
