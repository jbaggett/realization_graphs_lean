#!/usr/bin/env python3
"""sec11_yfamily_census.py -- Section 11.2's "the running example is the smallest of its kind".

WHY THIS EXISTS.  Section 11.4 says the scripts that produced the numbers quoted in the paper are in
the companion repository.  Every other computational claim of Section 11.2 has a tracked script
behind it; this one did not.  The counts were verified during the 2026-09-06 accuracy pass and
recorded in prose, which is not the same as being reproducible -- and a claim whose only support is a
sentence in a record is exactly what a companion repository exists to stop.

THE CLAIM, from Section 11.2, supporting Section 5.1's "there is no other of its order":

    Exhaustive over all graphical sequences through ground order six, counting those with a pivot
    whose realizable family is a Y-family: NONE at orders four and below, exactly ONE at order five,
    and FOUR at order six.

DEFINITIONS, taken from the ones the Section 7 seals already use rather than reinvented:

  * `I_v`, the realizable family at a pivot, is the set of neighborhoods of `v` over all
    realizations of `d` -- computed by enumerating the realizations, not from a criterion.
  * `J(F)`, the Johnson graph: vertices are the members, adjacent when their symmetric difference
    has size two.
  * a **bad template** -- equivalently a Y-family, by Theorem 7.6 -- is: at least four vertices,
    exactly two universal vertices, and the remaining induced graph has exactly two nonempty
    connected components, each a clique.

It REFUSES to emit unless the counts and the order-six witnesses are what the paper prints.
"""
import json, sys
from itertools import combinations
from pathlib import Path

NMAX = 6
OUT = Path(__file__).with_name("data") / "sec11_yfamily_census.json"

EXPECTED_COUNTS = {1: 0, 2: 0, 3: 0, 4: 0, 5: 1, 6: 4}
EXPECTED_5 = [(3, 2, 2, 2, 1)]
EXPECTED_6 = [(5, 4, 3, 3, 3, 2), (4, 4, 3, 3, 3, 1), (4, 2, 2, 2, 1, 1), (3, 2, 2, 2, 1, 0)]


def realizations(n, d):
    """Every labelled graph on [n] with degree sequence exactly d. Enumerated, not sampled."""
    edges = list(combinations(range(n), 2))
    out = []
    for r in range(len(edges) + 1):
        if 2 * r != sum(d):
            continue
        for S in combinations(edges, r):
            deg = [0] * n
            for u, v in S:
                deg[u] += 1; deg[v] += 1
            if tuple(deg) == tuple(d):
                out.append(frozenset(S))
    return out


def nbrs(G, v):
    return frozenset(u for e in G for u in e if v in e and u != v)


def is_bad_template(F):
    """At least four vertices, exactly two universal, the rest two nonempty cliques."""
    F = list(F)
    if len(F) < 4:
        return False
    adj = {A: {B for B in F if B != A and len(A ^ B) == 2} for A in F}
    universal = [A for A in F if len(adj[A]) == len(F) - 1]
    if len(universal) != 2:
        return False
    rest = [A for A in F if A not in universal]
    seen, comps = set(), []
    for A in rest:
        if A in seen:
            continue
        comp, stack = set(), [A]
        while stack:
            x = stack.pop()
            if x in comp:
                continue
            comp.add(x); seen.add(x)
            stack += [y for y in adj[x] & set(rest) if y not in comp]
        comps.append(comp)
    if len(comps) != 2 or any(not c for c in comps):
        return False
    return all(len(X ^ Y) == 2 for c in comps for X, Y in combinations(sorted(c, key=sorted), 2))


hits = {n: [] for n in range(1, NMAX + 1)}
for n in range(1, NMAX + 1):
    # every non-increasing degree sequence on n vertices with entries in 0..n-1
    def gen(prefix):
        if len(prefix) == n:
            yield tuple(prefix); return
        hi = prefix[-1] if prefix else n - 1
        for x in range(hi, -1, -1):
            yield from gen(prefix + [x])
    for d in gen([]):
        if sum(d) % 2:
            continue
        R = realizations(n, d)
        if not R:                                            # not graphical
            continue
        for v in range(n):
            fam = {nbrs(G, v) for G in R}
            if is_bad_template(fam):
                hits[n].append(d)
                break

counts = {n: len(hits[n]) for n in hits}
problems = []
for n, c in EXPECTED_COUNTS.items():
    if counts.get(n, 0) != c:
        problems.append(f"order {n}: found {counts.get(n, 0)}, paper says {c}")
if sorted(hits[5]) != sorted(EXPECTED_5):
    problems.append(f"order 5 witnesses: {sorted(hits[5])} != {sorted(EXPECTED_5)}")
if sorted(hits[6]) != sorted(EXPECTED_6):
    problems.append(f"order 6 witnesses: {sorted(hits[6])} != {sorted(EXPECTED_6)}")

for n in range(1, NMAX + 1):
    print(f"  order {n}: {counts[n]} graphical sequence(s) with a Y-family pivot"
          + (f"   {sorted(hits[n])}" if hits[n] else ""))
if problems:
    print("\nREFUSING TO EMIT:")
    for p in problems:
        print("  - " + p)
    sys.exit(1)

OUT.parent.mkdir(exist_ok=True)
OUT.write_text(json.dumps({"nmax": NMAX, "counts": counts,
                           "witnesses": {str(n): [list(d) for d in sorted(hits[n])] for n in hits}},
                          indent=1))
print(f"\nRESULT: PASS -- none through order four, one at order five, four at order six, and the "
      f"witnesses are the ones Section 11.2 prints. Written to {OUT}")
