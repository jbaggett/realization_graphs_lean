# Pinned gate and seal outputs

Each file is the verbatim output of the named script on the commit it was recorded at. They are
recorded rather than regenerated so a reader can compare a fresh run against what the authors saw.

## The axiom gate

- `axiom_baseline_2026-09-07.txt` — `compute/check_axiom_baseline.py`, 2026-09-07, **run inside a
  clone of this repository**: 115 declarations, strata 25-90-0, seven cited axioms,
  open-declaration audit clean.
- `qstar_note_axioms_2026-09-07.txt` — `compute/check_qstar_note_axioms.py`, same run: all 46 of
  Section 7's declarations trace to `{propext, Classical.choice, Quot.sound}` and nothing else.
- `axiom_baseline_2026-08-28.txt` — the same gate on 2026-08-28, kept for comparison. ⚠ It was
  produced in the authors' working tree. At that date this gate could not run here at all: it
  assumed that layout unconditionally, so in a clone it measured nothing and still exited 0.

## The scripts behind the printed numbers, run 2026-09-07

Each was run and its output matched against the number the paper prints. The claim each supports is
named so a reader can go from a sentence in the paper to the file that supports it in one step.

| file | script | the claim it supports |
|---|---|---|
| `sec10_walkthrough_build.out.txt` | `sec10_walkthrough_build.py` | §10's worked example: the construction is run and the result is checked to be a Hamilton `G_0`–`G_1` path |
| `sec10_walkthrough_instance_sweep.out.txt` | `sec10_walkthrough_instance_sweep.py` | §10's instance was chosen by computation, not picked |
| `sec63_witnesses.out.txt` | `sec63_witnesses.py` | §6.3's six excluded cells, each with an explicit witness |
| `sec64_two_active_lines_seal.out.txt` | `sec64_two_active_lines_seal.py` | §6.4's two-active-lines branch, all five facts |
| `sec11_yfamily_census.out.txt` | `sec11_yfamily_census.py` | §11.2: none through order four, one at order five, four at order six |
| `sec11_matroid_pivot_census.out.txt` | `sec11_matroid_pivot_census.py` | §11.2: no ground vertex need have a matroid family — none through ground order ten, exactly **six** at eleven, on 59,348 sequences |
| `skeleton_test.out.txt` | `skeleton_test.py` | §11.2: the skeleton of `conv(F)` strictly contains `J(F)` — **88 of 172** |
| `qstar_ord_steps.out.txt` | `qstar_ord_steps.py` | §11.2: `δ < 0` occurs — **8,876 of 88,518** |
| `crown_dpc_k34.out.txt` | `crown_dpc_k34.py` | §3.3: the **3,600** admissible demands on the crown |
| `seal_step_lemma_inputs.out.txt` | `seal_step_lemma_inputs.py` | §11.2/§11.4: **70 of 15,477**; and every figure in §11.4's biconditional sentence — order seven alone **409,416** non-exceptional and **40** exceptional, cumulatively **427,156** = **427,086** + **70** |
| `seal_step_lemma_inputs_2026_08_15.json` | *(the same run's structured output)* | where those two counts are actually recorded — the script's stdout reports coverage, the JSON reports the totals |
| `quotient_matroid_witness_bruteforce.out.txt` | `quotient_matroid_witness_bruteforce.py` | §11.2: the independent, graph-level reproduction of the matroid witness |
| `independent_sec7_seal.out.txt` | `independent_sec7_seal.py` | §11.4: the second implementation, written from the printed statements alone — **0 violations over 17,670 instances** |

⚠ **409,416 occurs twice in this tree, in unrelated quantities.** `layer_calib7_2026_08_15.py`
reports `e_choice_counts` of exactly 409,416, and a trace through the working records points there
first. It is a coincidence: the paper's 409,416 is the count of non-exceptional configurations at
ground order seven, and it comes from `seal_step_lemma_inputs.py`, whose per-order breakdown reads
409,456 = 409,416 + 40 at `n = 7` and sums to the cumulative 427,156. `layer_calib7` is behind no
number the paper prints and is not shipped.

## What is NOT pinned here, and why

Two scripts are shipped without a pinned output because re-running them is a long job rather than a
check a reader would repeat casually. Both are honest to run; neither was re-run for this deposit.

- `quotient_matroid_scan.py` — the per-PIVOT exchange scan. It ships because
  `sec11_matroid_pivot_census.py` imports its exchange test and family construction, so the two
  agree by construction on what a matroid basis family is. ⚠ It is **not** the producer of §11.2's
  order-eleven claim: it counts pivots whose family fails exchange and stops at the first, which is
  the running example at ground order five. The paper's claim is per-sequence — a sequence fails
  only when *every* pivot fails — and that is what the census computes.
- `seal_step_lemma_inputs.py` writes its markdown report to a **dated file** by default and will
  overwrite it. Pass `--report <path>` when re-running.
- `base_object_census.py` — §11.3's indecomposable census through ground order eight
  (504 decided, 133 skipped by a vertex cap, 7 undecided). Those dispositions are historical: they
  are reported from the original 2026-07-24 run, and the paper reports every skipped instance as
  skipped and none as passed.

And one script does not exist at all: the order-**seven** verification of §11.3 ran on separate
hardware and only its summary survives. §11.4 of the paper says so.
