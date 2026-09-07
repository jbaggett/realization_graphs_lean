#!/usr/bin/env python3
"""sec11_matroid_pivot_census.py -- Section 11.2's "no ground vertex need have a matroid family".

WHY THIS EXISTS, and it is not the reason the sibling census exists.  `quotient_matroid_scan.py`
was the obvious candidate for this claim and IS NOT IT.  It counts PIVOTS whose realizable family
fails basis exchange, and it stops at the first one -- which is the running example's Y-family at
ground order five.  Section 11.2 claims something different and stronger:

    every degree sequence on at most TEN ground vertices has SOME ground vertex whose realizable
    family is the basis family of a matroid, and at ELEVEN exactly SIX do not.

That is a per-SEQUENCE quantity: a sequence fails only when EVERY pivot fails.  A per-pivot count
cannot decide it, and reading the sibling's `failures` field as though it could would have put a
number in the paper that the script does not compute.  Found 2026-09-07 while assembling the
companion repository, after a first pass had mapped the claim to the sibling on the strength of its
name.

The exchange test and the family construction are IMPORTED from `quotient_matroid_scan.py` rather
than rewritten, so the two agree by construction on what "is a matroid basis family" means; what is
new here is only the quantifier.  One representative pivot per degree class is enough, because
equal-degree labels are symmetric.

It REFUSES to emit unless the counts and the six order-eleven witnesses are what the paper prints.
"""
import json, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from quotient_matroid_scan import degree_partitions, is_graphical, family, exchange_failure

NMAX = 11
OUT = HERE / "data" / "sec11_matroid_pivot_census.json"

EXPECTED_11 = [
    (8, 8, 8, 4, 4, 4, 4, 2, 2, 2, 2),
    (8, 8, 8, 5, 5, 4, 4, 2, 2, 2, 2),
    (8, 8, 8, 5, 5, 5, 5, 2, 2, 2, 2),
    (8, 8, 8, 8, 5, 5, 5, 5, 2, 2, 2),
    (8, 8, 8, 8, 6, 6, 5, 5, 2, 2, 2),
    (8, 8, 8, 8, 6, 6, 6, 6, 2, 2, 2),
]

failures = {n: [] for n in range(1, NMAX + 1)}
totals = {n: 0 for n in range(1, NMAX + 1)}
for n in range(1, NMAX + 1):
    for degrees in degree_partitions(n):
        if not is_graphical(degrees):
            continue
        totals[n] += 1
        seen, ok = set(), False
        for pivot, pd in enumerate(degrees):
            if pd in seen:
                continue
            seen.add(pd)
            _, bases = family(degrees, pivot)
            if exchange_failure(bases) is None:      # this pivot's family IS a matroid
                ok = True
                break
        if not ok:
            failures[n].append(tuple(degrees))
    print(f"  order {n:2d}: {totals[n]:6d} graphical sequences, "
          f"{len(failures[n])} with NO matroid pivot", flush=True)

problems = []
for n in range(1, NMAX):
    if failures[n]:
        problems.append(f"order {n}: {len(failures[n])} sequences with no matroid pivot, "
                        f"paper says none through order ten")
if sorted(failures[NMAX]) != sorted(EXPECTED_11):
    problems.append(f"order {NMAX}: found {sorted(failures[NMAX])}, "
                    f"paper prints {sorted(EXPECTED_11)}")
if problems:
    print("\nREFUSING TO EMIT:")
    for p in problems:
        print("  - " + p)
    sys.exit(1)

OUT.parent.mkdir(exist_ok=True)
OUT.write_text(json.dumps({"nmax": NMAX, "graphical_sequences": totals,
                           "no_matroid_pivot": {str(n): [list(d) for d in sorted(failures[n])]
                                                for n in failures}}, indent=1))
print(f"\nRESULT: PASS -- none through ground order ten, exactly {len(failures[NMAX])} at order "
      f"eleven, and they are the six the paper prints. Written to {OUT}")
