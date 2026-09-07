# Pinned outputs

Each file is the verbatim output of the named program. They are recorded rather than regenerated so
a reader can compare a fresh run against the run the paper reports.

## The audit gates

- `axiom_baseline_2026-09-07.txt` — `compute/check_axiom_baseline.py`: 115 declarations, strata
  25-90-0, seven cited axioms, open-declaration audit clean.
- `qstar_note_axioms_2026-09-07.txt` — `compute/check_qstar_note_axioms.py`: all 46 of Section 7's
  declarations trace to `{propext, Classical.choice, Quot.sound}` and nothing else.

## The programs behind the printed numbers

Each entry names the claim its program supports, so a reader can go from a sentence in the paper to
the file that backs it in one step.

| file | program | the claim it supports |
|---|---|---|
| `sec10_walkthrough_build.out.txt` | `sec10_walkthrough_build.py` | §10's worked example: the construction is run and the result checked to be a Hamilton `G_0`–`G_1` path |
| `sec10_walkthrough_instance_sweep.out.txt` | `sec10_walkthrough_instance_sweep.py` | §10's instance was chosen by computation |
| `sec63_witnesses.out.txt` | `sec63_witnesses.py` | §6.3's six excluded cells, each with an explicit witness |
| `sec64_two_active_lines_seal.out.txt` | `sec64_two_active_lines_seal.py` | §6.4's two-active-lines branch, all five facts |
| `sec11_yfamily_census.out.txt` | `sec11_yfamily_census.py` | §11.2: none through ground order four, one at five, four at six |
| `sec11_matroid_pivot_census.out.txt` | `sec11_matroid_pivot_census.py` | §11.2: no ground vertex need have a matroid family — none through ground order ten, exactly **six** at eleven, over 59,348 sequences |
| `skeleton_test.out.txt` | `skeleton_test.py` | §11.2: the skeleton of `conv(F)` strictly contains `J(F)` — **88 of 172** |
| `qstar_ord_steps.out.txt` | `qstar_ord_steps.py` | §11.2: `δ < 0` occurs — **8,876 of 88,518** |
| `crown_dpc_k34.out.txt` | `crown_dpc_k34.py` | §3.3: the **3,600** admissible demands on the crown |
| `seal_step_lemma_inputs.out.txt` | `seal_step_lemma_inputs.py` | §11.2 and §11.4: **70 of 15,477**, and every figure in §11.4's biconditional sentence — at ground order seven **409,416** non-exceptional and **40** exceptional, cumulatively **427,156** = **427,086** + **70** |
| `seal_step_lemma_inputs_2026_08_15.json` | the same run's structured output | where those totals are recorded: the program's stdout reports coverage, the JSON reports the totals |
| `quotient_matroid_witness_bruteforce.out.txt` | `quotient_matroid_witness_bruteforce.py` | §11.2: an independent, graph-level reproduction of the matroid witness |
| `independent_sec7_seal.out.txt` | `independent_sec7_seal.py` | §11.4: the second implementation, written from the printed statements alone — **0 violations over 17,670 instances** |

## §11.2's rank-two claim, checked two ways

`qstar_rank2_base.py` sweeps every rank-two shifted family on `[n]` and every pair in it, deciding
Hamilton-connectivity by exact depth-first search. The sweep over `[8]` is a long run, so both halves
of the paper's sentence — *"on the ground `[8]` alone, at rank two, five non-Hamiltonian pairs among
13,888"* — can also be checked directly, and the two agree:

- **13,888.** `enum_rank2(8)` returns the 126 rank-two shifted families with at least two members; it
  filters `|F| ≥ 2` because a one-member family has no pair to test, and that singleton is the 127th
  nonempty family. Those 126 contribute exactly **13,888** unordered pairs.
- **Five.** The exceptions all have the shape `F = {12, 13, 23, 14, …, 1r}` at the pair `{12,13}`.
  Six such families exist on `[8]`, for `r = 3, …, 8`, and exhaustive search finds a Hamilton path in
  exactly one: `r = 3`, where `F = {12,13,23}` and `J(F) = K_3`, which is Hamilton-connected. The
  other five have none. That is why the count is five rather than six, and it is the same reason a
  Y-family is required to have at least four members.

## What is not pinned, and why

Three programs ship without a pinned output.

- `quotient_matroid_scan.py` — the per-pivot exchange scan, a long run. It is here because
  `sec11_matroid_pivot_census.py` imports its exchange test and family construction, so the two agree
  by construction on what a matroid basis family is. It is **not** the producer of §11.2's
  order-eleven claim: it counts pivots whose family fails exchange, where the paper's claim is per
  sequence — a sequence fails only when every pivot fails — which is what the census computes.
- `base_object_census.py` — §11.3's indecomposable census through ground order eight: 504 decided,
  133 skipped by a vertex cap, 7 undecided. Those dispositions are reported from the original run.
  The paper reports every skipped instance as skipped and none as passed.
- `seal_step_lemma_inputs.py` — pinned above, but note that it writes its markdown report to a fixed
  path by default and will overwrite it. Pass `--report <path>` when re-running.

One program is not here at all: the order-seven verification reported in §11.3 was run on separate
hardware and only its summary survives. §11.4 of the paper says so.
