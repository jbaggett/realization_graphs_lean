#!/usr/bin/env python3
"""sec63_witnesses.py -- the six excluded cells of the Section 6.3 table, with witnesses.

The table asserts that certain pairs of outside types cannot occur in a FAILING configuration
(one where D = {0,1,2,3} is the common core of every triangle of G(d)).  The manuscript names
the support type each exclusion produces but displays no witness, and a hand check of the
A-Z_0 cell did not find one.  So: build each configuration explicitly, enumerate the whole
realization graph, and report a triangle whose ground support MISSES a vertex of D.

Outside types, on D = {0,1,2,3}:  A: N_D(w) = {}   B: N_D(w) = D   Z_j: N_D(w) = D - {j}
"""
import itertools, sys
from itertools import combinations

def degseq(n, edges):
    d = [0]*n
    for u,v in edges: d[u]+=1; d[v]+=1
    return tuple(d)

def realizations(n, d):
    """all labelled graphs on [n] with degree sequence d, as frozensets of edges"""
    allpairs = list(combinations(range(n),2))
    out = []
    # prune by degree as we go
    def rec(i, chosen, deg):
        if i == len(allpairs):
            if deg == list(d): out.append(frozenset(chosen))
            return
        u,v = allpairs[i]
        rem = allpairs[i:]
        # bound: remaining capacity
        for w in range(n):
            if deg[w] > d[w]: return
        cap = [0]*n
        for (a,b) in rem: cap[a]+=1; cap[b]+=1
        for w in range(n):
            if deg[w] + cap[w] < d[w]: return
        deg[u]+=1; deg[v]+=1; chosen.append((u,v))
        rec(i+1, chosen, deg)
        chosen.pop(); deg[u]-=1; deg[v]-=1
        rec(i+1, chosen, deg)
    rec(0, [], [0]*n)
    return out

def support(e1, e2):
    s = set()
    for (u,v) in e1 ^ e2: s.add(u); s.add(v)
    return s

def analyse(name, n, edges):
    d = degseq(n, edges)
    R = realizations(n, d)
    idx = {r:i for i,r in enumerate(R)}
    G0 = frozenset(tuple(sorted(e)) for e in edges)
    assert G0 in idx, f"{name}: the constructed graph is not in its own realization list"
    adj = {r:set() for r in R}
    for a,b in combinations(R,2):
        if len(a ^ b) == 4: adj[a].add(b); adj[b].add(a)
    D = {0,1,2,3}
    tri_missing = []
    for a in R:
        for b,c in combinations(sorted(adj[a], key=lambda x: idx[x]),2):
            if c in adj[b]:
                sup = support(a,b) | support(b,c) | support(a,c)
                if not D <= sup:
                    tri_missing.append((sorted(sup), sorted(D-sup)))
    return d, len(R), tri_missing

def build(outside):
    """outside: list of (type, extra_edges_to_other_outside).  D induces 01|23."""
    n = 4 + len(outside)
    edges = [(0,1),(2,3)]
    for i,(typ,_) in enumerate(outside):
        w = 4+i
        if typ == 'A':   nd = []
        elif typ == 'B': nd = [0,1,2,3]
        else:            nd = [x for x in range(4) if x != int(typ[1])]
        edges += [(x,w) for x in nd]
    for i,(typ,ex) in enumerate(outside):
        for j in ex:
            e = tuple(sorted((4+i, 4+j)))
            if e not in edges: edges.append(e)
    return n, edges

CASES = [
 ("A-A joined by an edge",        [('A',[1]), ('A',[])]),
 ("B-B not joined",               [('B',[]),  ('B',[])]),
 ("A-Z_0 joined by an edge",      [('A',[1]), ('Z0',[])]),
 ("B-Z_0 not joined",             [('B',[]),  ('Z0',[])]),
 ("Z_0-Z_0, joined",              [('Z0',[1]),('Z0',[])]),
 ("Z_0-Z_0, not joined",          [('Z0',[]), ('Z0',[])]),
 ("Z_0-Z_1, joined",              [('Z0',[1]),('Z1',[])]),
 ("Z_0-Z_1, not joined",          [('Z0',[]), ('Z1',[])]),
]
def classify(a, b, c):
    """Which of Section 6.2's three types is the triangle {a,b,c}?  The two common edges of the
    two switches out of `a` are removed, mixed, or added, and that is the trichotomy."""
    d1, d2 = a ^ b, a ^ c
    common = d1 & d2
    removed = sum(1 for e in common if e in a)
    return {2: "I (both common edges removed)",
            1: "II (one removed, one added)",
            0: "III (both common edges added)"}[removed]

def typeII_labelling(a, b, c):
    """Recover Section 6.2's Type II quintuple (x,y,z,t,t') from a triangle, or None.

    Type II is {xy, zt} -> {xz, yt} against {xy, zt'} -> {xz, yt'}, so of the two edges the two
    switches share, the REMOVED one is xy and the ADDED one is xz; their common vertex is x.
    """
    d1, d2 = a ^ b, a ^ c
    common = d1 & d2
    rem = [e for e in common if e in a]
    add = [e for e in common if e not in a]
    if len(rem) != 1 or len(add) != 1: return None
    xy, xz = rem[0], add[0]
    shared = set(xy) & set(xz)
    if len(shared) != 1: return None
    x = shared.pop()
    y = (set(xy) - {x}).pop()
    z = (set(xz) - {x}).pop()
    def other(delta, want_removed):
        es = [e for e in delta if e != xy and e != xz
              and ((e in a) == want_removed)]
        return es[0] if len(es) == 1 else None
    zt, zt2 = other(d1, True), other(d2, True)
    if zt is None or zt2 is None: return None
    if z not in zt or z not in zt2: return None
    tt = (set(zt) - {z}).pop(); tt2 = (set(zt2) - {z}).pop()
    if len({x, y, z, tt, tt2}) != 5: return None
    return dict(x=x, y=y, z=z, t=tt, tprime=tt2)

def exhibit(name, n, edges):
    """One explicit triangle for a cell, with its type and the vertex of D it misses."""
    d = degseq(n, edges)
    R = realizations(n, d)
    adj = {r: set() for r in R}
    for x, y in combinations(R, 2):
        if len(x ^ y) == 4: adj[x].add(y); adj[y].add(x)
    D = {0, 1, 2, 3}
    for a in R:
        for b, c in combinations(sorted(adj[a]), 2):
            if c in adj[b]:
                sup = support(a, b) | support(b, c) | support(a, c)
                if not D <= sup:
                    lab = typeII_labelling(a, b, c)
                    return {"type": classify(a, b, c), "misses": sorted(D - sup),
                            "support": sorted(sup), "labelling": lab,
                            "realizations": [sorted(x) for x in (a, b, c)]}
    return None

print(f"{'excluded cell':32} {'d':26} {'|V(G(d))|':>9}  triangle support missing")
print("-"*100)
for name, spec in CASES:
    n, edges = build(spec)
    d, nr, miss = analyse(name, n, edges)
    if miss:
        sup, absent = miss[0]
        print(f"{name:32} {str(d):26} {nr:>9}  support {sup} misses {absent}   ({len(miss)} such)")
    else:
        print(f"{name:32} {str(d):26} {nr:>9}  *** NONE FOUND ***")


# ---------------------------------------------------------------------------------------------
# The Z_0-Z_1 row of Section 6.3's table displays ONE Type II labelling and claims it covers the
# edge and the non-edge case together.  It does not: that labelling takes x = u, z = w, and Type II
# requires xz = uw ABSENT, so it witnesses the non-edge case only.  Both cases are genuinely
# excluded -- the sweep above shows it -- but the edge case needs its own witness, and this prints
# one.  Found by a comprehension read on 2026-08-26.
print()
print("The Z_0-Z_1 row, each status separately, with an explicit triangle for each:")
for name, spec in [("Z_0-Z_1, joined (uw an EDGE)",   [('Z0',[1]),('Z1',[])]),
                   ("Z_0-Z_1, not joined",           [('Z0',[]), ('Z1',[])])]:
    n, edges = build(spec)
    w = exhibit(name, n, edges)
    L = w["labelling"]
    lab = (f"x={L['x']} y={L['y']} z={L['z']} t={L['t']} t'={L['tprime']}"
           if L else "(not a Type II labelling)")
    print(f"  {name:30} type {w['type']:32} misses {w['misses']} of D")
    print(f"      {lab}")
    for r in w["realizations"]:
        print(f"      {' '.join(f'{u}{v}' for u, v in r)}")
