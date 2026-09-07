# Maximal Hamiltonicity of realization graphs of degree sequences — Lean 4 formalization

This repository is the machine-checked companion to the paper of the same title. It contains the Lean
4 development, the gates that audit it, and the programs behind the computational figures the paper
reports.

The realization graph `G(d)` of a graphical degree sequence `d` has the labeled realizations of `d`
as its vertices, two joined when they differ by a 2-switch. The paper proves that `G(d)` is always
maximally Hamiltonian. The main declaration is

```lean
theorem realizationGraph_maximally_hamiltonian {V : Type u} [Fintype V] [DecidableEq V]
    (d : V → ℕ) : IsMaximallyHamiltonianRealizationGraph d
```

in `Realization/SBPlusOrd.lean`. It carries no graphicality hypothesis: `Realization d` is empty
exactly when `d` is not graphical, so the ungraphical case holds with an empty vertex type.
`IsMaximallyHamiltonianRealizationGraph d` unfolds to `IsMH (RealizationGraph d)`, where `IsMH` is
*Hamilton-connected, or there is a proper surjective 2-coloring for which the graph is
Hamilton-laceable*. Hamilton paths are mathlib's `SimpleGraph.Walk.IsHamiltonian`.

## Building

```bash
ulimit -v 67108864          # 64 GiB of address space, in KiB. Without it the build can exit 134
                            # with "failed to create thread". This is address space, not memory:
                            # peak resident set on this build is about 3.3 GB.
lake exe cache get          # Fetch mathlib's prebuilt cache first. `lake build` does not do this,
                            # and without it Lake compiles mathlib from source.
LEAN_NUM_THREADS=6 lake build Realization
```

`lake -j` does not exist in Lake 5.0.0 and `lake -Kjobs=N` has no effect; `LEAN_NUM_THREADS` is the
knob. A pass is `exit 0` **and** the expected `.olean` files present under
`.lake/build/lib/lean/Realization/`.

Toolchain and dependency versions are pinned in `lean-toolchain` and `lakefile.toml`.

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

The three strata are reported separately and are never summed. The gate fails on any of six
conditions: a wrong stratum count; a `sorry` anywhere in the audited surface; a declaration named but
not traced; a doc comment that contradicts its own declaration; a cited axiom outside the expected
list; or a module whose declaration count has moved away from the figure the paper quotes.

```bash
python3 compute/check_qstar_note_axioms.py
```

checks the paper's other claim about the kernel — that Section 7's development charges no cited axiom
of any kind — over all 46 of its declarations. Both gates print their expected output above; pinned
runs are in `results/`.

## What is assumed

Seven results are taken from the literature as axioms. Everything else in the development is proved
from Lean's foundations (`propext`, `Classical.choice`, `Quot.sound`). There is no `sorry` and no
compiled-evaluation certificate on the audited surface.

| | declaration | source |
|---|---|---|
| A1 | `barrus_theorem9_bipartite_iff_triangleFree` | Barrus 2016, Theorem 9 (a)⟺(b) |
| A2 | `barrus_theorem9_bipartite_classification` | Barrus 2016, Theorem 9 (a)⟹(c) |
| A3 | `realizationGraph_preconnected` | Fulkerson, Hoffman and McAndrew 1965, Theorem 5.2 |
| A4 | `SBPlusOrd.erdos_gallai_sufficiency` | Erdős and Gallai 1960, (1.2) |
| A5 | `SBPlusOrd.invariantPosition_forces_block` | Brualdi 2006, Theorem 3.4.1 |
| A6 | `Ledger.flipGraph_connected` | Ryser 1957, Theorem 3.1 |
| A7 | `Ledger.invariantFree_nonbip_has_triangle` | Brualdi 2006, Theorem 6.3.4 |

Three encodings differ from their sources in ways a reader should not have to discover:

- **A4.** The source ranges its index over `1, …, n−1`; the axiom quantifies over all
  `t ≤ Fintype.card W`. The axiom therefore assumes more than the source provides — a burden on the
  caller, never a stronger conclusion.
- **A3.** The applicable result is Theorem 5.2 of that paper, for ordinary graphs, not the general
  Theorem 4.1, whose even-set hypothesis their Section 5 discharges in the all-capacities-one case.
- **A2.** Barrus's Theorem 9 (a)⟹(c) requires a graphicality hypothesis and is false without it. The
  axiom carries it.

Sorted-margin conventions are a fourth, smaller difference: several sources state results for
nonincreasing margin vectors while the development represents margins as arbitrary functions. Row and
column permutations preserve invariant positions, primeness, feasibility and the interchange
relation, so the readings agree — but that argument is made on paper and is not formalized.

## Repository layout

```
Realization/      the 25 modules of this paper
compute/          the audit gates and the programs behind the paper's computational figures
results/          pinned outputs of both
lakefile.toml     one library target; a pinned dependency on the companion development
```

The modules are `Realization.*` rather than `BrualdiLean.*`. The pinned dependency
`brualdi-interchange-lean` declares a library owning the `BrualdiLean` module namespace, and two
packages cannot both own it. Lean namespaces are independent of module paths, so the declarations
remain in `Brualdi.RealizationGraph.*` as the paper names them.

That dependency is the Lean development of *Interchange graphs of (0,1)-matrices are maximally
Hamiltonian* (arXiv:2607.13165), pinned at the tag `realization-dep-v1`, which marks the state this
paper was verified against. The import closure is 43 modules: 25 here and 18 from that development.

## The programs behind the paper's figures

Section 11.4 of the paper states that the programs producing the numbers it quotes are in this
repository. They are in `compute/`, and `results/README.md` maps each one to the sentence it supports
and holds its pinned output. Four are named in the paper by path:
`sec10_walkthrough_build.py`, `sec10_walkthrough_instance_sweep.py`, `sec63_witnesses.py` and
`sec64_two_active_lines_seal.py`. The rest support Section 11.2's computational claims, Section
11.3's census and Section 11.4's independent reproduction.

Each program re-derives its object rather than reading a stored answer, and most refuse to report
success unless their own checks pass: `sec10_walkthrough_build.py`, for instance, runs Section 10.2's
construction step by step and will not emit unless the result is a Hamilton `G_0`–`G_1` path of
`G(d)`. Two require `numpy` and `scipy`; the rest need only the standard library. Paths are derived
from each program's own location, so they run from a clone.

## How the Lean differs from the printed proof

A reader who opens a formalization expects the theorems to be the paper's theorems. Where that is not
literally true, saying so is the difference between a verification artifact and a claim.

### The formal statement is not always the printed sentence

- **Theorem 7.7.** The paper states it in Y-family vocabulary — *"unless `F` is a Y-family and
  `{A,B}` is its universal pair"*. The declaration `qstar` states it in clique-sum vocabulary:
  `HasHamPath (exchangeGraph F) A B ↔ ¬ IsCliqueSum F A B`. These are equivalent for shifted
  families, and that equivalence is Theorem 7.6, proved here — but they are not the same sentence.
  The difference is visible in the dependency graph: `qstar` invokes Lemma 7.4 and not Theorem 7.6,
  which enters one step later at Corollary 7.8.
- **Lemma 7.10, the arm-exchange clause.** The paper says *"the two arms exchanged: the inner arm of
  `F` maps onto the outer arm of `F*`"*. No declaration states that. What is proved is the
  containment identity it is derived from, `X ⊆ u ∪ v ↔ dualSet u ∩ dualSet v ⊆ dualSet X`, together
  with the fact — supplied in the paper's proof and not formalized — that inner-arm membership *is*
  `X ⊆ u ∪ v` and outer-arm membership *is* `X* ⊇ u* ∩ v*`. Nothing in the development relates
  `yInnerArm` or `yOuterArm` to the duality.

### A printed result carried by several declarations, or by none of its own

- **Theorem 4.4** is not a lemma here; its dispatch is the induction's own case split.
- **Lemma 5.7b** (vicinal trichotomy) is its three regimes, proved separately in
  `InterfaceSaturation.lean`; the three together are the lemma.
- **Theorem 7.11** has a carrier, `crossingLemma`, but it is a thin wrapper: the case analysis, the
  range reduction and the duality transports are in `not_crossingFailure_general`.
- **Theorem 5.4** is two claims. `quotient_adjacency` is the existence biconditional and says nothing
  about how many connectors there are; the quantitative clause *"with at least `f(a) − f(b)`
  choices"* is `residualConnectorCandidates_card_lower` in `QuotientAdjacency.lean`, together with
  its S-side image `sSideConnectorTargets`.

### Definitions broader in Lean than in the paper

- **`GaleLE`** is defined by upper-tail counts on arbitrary finite sets, where Section 7.1's Gale
  order is for sets of equal size. The section states the order two ways; the kernel reasons in the
  threshold form and `galeLE_iff_pointwise` proves the two agree.
- **`exchangeGraph`** does not require members to be equicardinal, so a symmetric difference of size
  two could in principle be two insertions. `IsShifted` supplies equal cardinality at every use.
- **`IsShifted`** bundles nonemptiness and fixed cardinality into the definition, where the paper
  carries them as standing conventions.
- **`yFamily_isCliqueSum` is vacuous for `k ≤ 1`**, as intended: Section 7.5 defines `F(k;r,s)` only
  for `k ≥ 2`. Satisfiability at `k = 2` is exhibited in `compute/`.

### The audited surface is not the main theorem's cone

`biregular_matching` and three related declarations in `InterfaceSaturation.lean` are among the 115
audited declarations, and nothing on the main theorem's cone reaches them. They belong to a route the
paper records and does not use — Section 5.4 says as much. A reader taking "115 audited declarations"
to mean *the declarations Theorem 10.1 rests on* would be reading it too narrowly in this direction
and, for a small number of load-bearing helper declarations, too broadly in the other.

### What is not machine-checked

The order-seven verification reported in Section 11.3 was run on separate hardware and only its
summary survives; the paper says so. Every other number the paper reports has a program here.

## Detail the paper points here for

**How Section 7 attaches to the rest.** Theorem 5.3 and Corollary 5.5 identify the neighborhood
quotient with the Johnson graph of a shifted family, which is what allows Theorem 7.7 to be applied
to a realization graph at all.

**Where the enumeration figures come from.**

- *The 13,888.* There are 127 nonempty shifted families of rank two on `[8]`; a family with one
  member has no pair to test, and 13,888 is the number of pairs the other 126 contribute between
  them.
- *Why the range starts at `[2]`.* It starts there because the producing sweep does. Grounds `[4]`
  through `[8]` alone contribute 15,469 of the instances and all 70 of the clique-sums, the two
  smallest grounds carrying none.
- *Why the rate is evidence of tightness.* The rank-two count rises by exactly one per ground order,
  which is the number of rank-two Y-families available at that order, so the sweep confirms both
  halves of the theorem rather than merely the absence of counterexamples.
- *The declaration behind "the exhibited families really are shifted"* is `yFamily_isShifted` in
  `QStar.lean`.

**How each order-seven instance was decided.** Of the 342 graphical degree sequences at ground order
seven, 64 have a single realization and are maximally Hamiltonian by the convention of Section 2, 137
were settled by exact search, and 130 by the Chvátal–Erdős condition; the remaining 9 were left
undecided by a search cap. The first three sum to 331, the decided count the paper quotes.

## License

The Lean development and the programs in this repository are released under the Apache License 2.0.
