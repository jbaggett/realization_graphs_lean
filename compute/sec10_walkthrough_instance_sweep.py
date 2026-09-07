#!/usr/bin/env python3
"""Pick the degree sequence for Section 10's worked example, by computing rather than guessing.

Worklist item B13.  Section 10 assembles the theorem and has no instance and no figure; the
companion paper threads a 694-word worked example through its Section 5.  The instance has to be
chosen honestly: it must actually exercise the machinery Section 10 describes, not merely be small.

WHAT WE NEED OF THE SEQUENCE
  * it must reach the MAIN LINE -- so: graphical, every ground vertex active, Tyshkevich-
    indecomposable, G(d) non-bipartite, and more than three realizations (past the K_3 base);
  * the pivot choice must be INTERESTING: Section 6 supplies an admissible pivot (it separates the
    prescribed pair and carries a non-bipartite fibre) and Section 8 says a further condition is
    needed and is not implied.  The example is worth its space only if some admissible separating
    pivot is EXCEPTIONAL, so the walkthrough shows the dodge of Section 8 rather than a pivot that
    was never in danger;
  * the buffer must be real -- at least one fibre non-bipartite, and more than one fibre, so the
    quotient path has hops to make;
  * it must be DRAWABLE: |V(G(d))| small enough to put on a page.

`(3,2,2,2,1)` is excluded up front: it is Figure 1's sequence and its realization graph is
`K_6 - 3K_2`, too small to show the branches.

Reuses the audited machinery of adversary_sbplus_n9n10_2026_08_15.py rather than reimplementing --
in particular its Tyshkevich test, which is taken from the DEFINITION after the Erdos-Gallai
equality proxy was found wrong on 2026-08-18 and cost 16% of the main line.
"""
import resource, sys, json, itertools
resource.setrlimit(resource.RLIMIT_AS, (8_000_000_000, 8_000_000_000))
# Paths derived from this file, not from a home directory, so the script runs in a clone of the
# companion repository too; in the working tree this is the same location as before.
HERE = __import__("pathlib").Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import adversary_sbplus_n9n10_2026_08_15 as A

def realization_graph(d):
    """Vertices = realizations as frozensets of edges; edges = 2-switches."""
    n = len(d)
    pairs = list(itertools.combinations(range(n), 2))
    V = []
    for r in range(sum(d) // 2, sum(d) // 2 + 1):
        for S in itertools.combinations(pairs, r):
            deg = [0] * n
            for u, v in S: deg[u] += 1; deg[v] += 1
            if tuple(deg) == tuple(d): V.append(frozenset(S))
    E = {(a, b) for i, a in enumerate(V) for b in V[i+1:] if len(a ^ b) == 4}
    return V, E

def bipartite(V, E):
    adj = {v: set() for v in V}
    for a, b in E: adj[a].add(b); adj[b].add(a)
    color = {}
    for s in V:
        if s in color: continue
        color[s] = 0; stack = [s]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if w not in color: color[w] = 1 - color[u]; stack.append(w)
                elif color[w] == color[u]: return False
    return True

def fibres(V, v):
    out = {}
    for G in V:
        nb = frozenset(y for x, y in G if x == v) | frozenset(x for x, y in G if y == v)
        out.setdefault(nb, []).append(G)
    return out

rows = []
for n in range(5, 8):
    for d in itertools.product(range(n), repeat=n):
        if list(d) != sorted(d, reverse=True): continue
        if sum(d) % 2 or sum(d) == 0: continue
        if not A.graphical(tuple(d)): continue
        if any(x == 0 for x in d): continue                    # every ground vertex active
        if 0 in d or min(d) == 0: continue
        if A.tyshkevich_decomposable_seq(d): continue
        V, E = realization_graph(d)
        if len(V) <= 3: continue                                # past the K_3 base
        if len(V) > 40: continue                                # must be drawable
        if bipartite(V, E): continue
        if tuple(d) == (3, 2, 2, 2, 1): continue                # Figure 1's sequence

        # pivot analysis
        adm, exc_adm, nonbip_fib = [], [], {}
        for v in range(n):
            F = fibres(V, v)
            if len(F) < 2: continue
            nb_count = 0
            for nb, part in F.items():
                sub = [g for g in part]
                subE = {(a, b) for i, a in enumerate(sub) for b in sub[i+1:] if len(a ^ b) == 4}
                if len(sub) >= 3 and not bipartite(sub, subE): nb_count += 1
            nonbip_fib[v] = (len(F), nb_count)
            if nb_count >= 1: adm.append(v)
            order, fam = A.pivot_family(tuple(d), v)
            if A.hook_universal_pair(order, fam, d[v]) is not None:
                exc_adm.append(v)
        live = sorted(set(adm) & set(exc_adm))
        if not adm: continue
        rows.append({
            "d": list(d), "|V(G(d))|": len(V), "|E|": len(E),
            "admissible_pivots": adm,
            "exceptional_pivots": exc_adm,
            "admissible_AND_exceptional": live,
            "fibres_per_pivot": {str(k): v2 for k, v2 in nonbip_fib.items()},
        })

rows.sort(key=lambda r: (0 if r["admissible_AND_exceptional"] else 1, r["|V(G(d))|"], r["d"]))
out = str(HERE / "data" / "sec10_walkthrough_candidates.json")
(HERE / "data").mkdir(exist_ok=True)
with open(out, "w") as f: json.dump(rows, f, indent=1)

live = [r for r in rows if r["admissible_AND_exceptional"]]
print(f"main-line candidates found: {len(rows)}   with a LIVE Section 8 exception: {len(live)}")
print(f"written to {out}\n")
print("--- best candidates (exception live, then smallest) ---")
for r in rows[:12]:
    tag = "EXCEPTION LIVE" if r["admissible_AND_exceptional"] else "no live exception"
    print(f"  d={tuple(r['d'])!s:22s} |V(G(d))|={r['|V(G(d))|']:3d}  adm={r['admissible_pivots']}"
          f"  exc={r['exceptional_pivots']}  [{tag}]")
