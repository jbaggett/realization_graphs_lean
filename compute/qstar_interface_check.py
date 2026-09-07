"""(Q) <-> (Q*) interface check  [worklist item 1, 2026-08-16]

The one-pass route (ONE_PASS_INTERFACE_2026-08-14.md sec.6) consumes:
  "the actual-neighborhood quotient is Hamilton-connected", and picks a quotient
  Hamilton path from A = pi_mu(X) to B = pi_mu(Y).
(Q*) (QSTAR_DESIGN_2026-08-15.md sec.1) delivers that EXCEPT when J(F) = K2 v (K_p u K_q)
and {A,B} is its universal pair.

This script checks, exhaustively over small ground orders:
  (A) quotient adjacency == Johnson adjacency on the quotient family   [same objects]
  (B) the quotient family is a Gale ideal / shifted family w.r.t. degree-descending order
  (C) whether J(I_mu) is ever a bad template K2 v (K_p u K_q)          [exception reachable?]
  (D) if so, whether the pivot is admissible for the separator-buffer theorem
      (some mu-fibre non-bipartite) and whether the prescribed pair can be its universal pair
  (E) the decisive one: is there a pair X!=Y with NO admissible non-exceptional pivot?
"""
import sys, itertools
from collections import deque

# ---------- graph plumbing: edge-index bitmasks ----------
def setup(n):
    ed = [(i, j) for i in range(n) for j in range(i + 1, n)]
    idx = {e: k for k, e in enumerate(ed)}
    for (i, j), k in list(idx.items()):
        idx[(j, i)] = k
    return ed, idx

def degrees(mask, n, ed):
    d = [0] * n
    m = mask
    while m:
        b = m & -m; k = b.bit_length() - 1; m ^= b
        i, j = ed[k]; d[i] += 1; d[j] += 1
    return tuple(d)

def havel_hakimi(d, n, idx):
    """seed realization of degree function d (list, indexed by vertex); None if not graphical"""
    rem = list(d); mask = 0
    for _ in range(n):
        order = sorted(range(n), key=lambda v: -rem[v])
        v = order[0]
        k = rem[v]
        if k == 0: continue
        targets = [u for u in order[1:] if rem[u] > 0][:k]
        if len(targets) < k: return None
        rem[v] = 0
        for u in targets:
            if mask >> idx[(v, u)] & 1: return None
            mask |= 1 << idx[(v, u)]
            rem[u] -= 1
            if rem[u] < 0: return None
    return mask if all(r == 0 for r in rem) else None

def two_switch_nbrs(mask, n, ed, idx):
    """all masks reachable by one 2-switch"""
    es = []
    m = mask
    while m:
        b = m & -m; k = b.bit_length() - 1; m ^= b
        es.append(ed[k])
    out = []
    for p in range(len(es)):
        a, b = es[p]
        for q in range(p + 1, len(es)):
            c, dd = es[q]
            if len({a, b, c, dd}) != 4: continue
            base = mask & ~(1 << idx[(a, b)]) & ~(1 << idx[(c, dd)])
            for (x, y), (z, w) in (((a, c), (b, dd)), ((a, dd), (b, c))):
                if (mask >> idx[(x, y)] & 1) or (mask >> idx[(z, w)] & 1): continue
                out.append(base | (1 << idx[(x, y)]) | (1 << idx[(z, w)]))
    return out

def realizations(d, n, ed, idx):
    seed = havel_hakimi(list(d), n, idx)
    if seed is None: return None
    seen = {seed}; dq = deque([seed]); adj = {}
    while dq:
        g = dq.popleft(); nb = set(two_switch_nbrs(g, n, ed, idx))
        adj[g] = nb
        for h in nb:
            if h not in seen: seen.add(h); dq.append(h)
    return adj

def nbrhood(mask, v, n, idx):
    return frozenset(u for u in range(n) if u != v and (mask >> idx[(v, u)] & 1))

def is_bipartite(verts, adj):
    col = {}
    for s in verts:
        if s in col: continue
        col[s] = 0; dq = deque([s])
        while dq:
            v = dq.popleft()
            for w in adj[v]:
                if w not in col: col[w] = col[v] ^ 1; dq.append(w)
                elif col[w] == col[v]: return False
    return True

def bad_template(verts, adj):
    """is the graph K2 v (K_p u K_q), p,q>=1?  return the universal pair or None"""
    V = list(verts); N = len(V)
    if N < 4: return None
    univ = [v for v in V if len(adj[v] & set(V)) == N - 1]
    if len(univ) < 2: return None
    for u, w in itertools.combinations(univ, 2):
        rest = [v for v in V if v != u and v != w]
        if len(rest) < 2: continue
        # rest must induce exactly K_p u K_q (two cliques, no edges between)
        comp = {}; ncomp = 0
        for s in rest:
            if s in comp: continue
            ncomp += 1
            if ncomp > 2: break
            comp[s] = ncomp; dq = deque([s])
            while dq:
                v = dq.popleft()
                for z in adj[v] & set(rest):
                    if z not in comp: comp[z] = ncomp; dq.append(z)
        if ncomp != 2: continue
        ok = True
        for a, b in itertools.combinations(rest, 2):
            want = (comp[a] == comp[b])
            if (b in adj[a]) != want: ok = False; break
        if ok: return (u, w)
    return None

# ---------- main sweep ----------
def graphical_seqs(n):
    """all non-increasing graphical degree sequences on [n] (WLOG by relabeling)"""
    out = []
    def rec(pref, lo):
        if len(pref) == n:
            if sum(pref) % 2 == 0: out.append(tuple(pref))
            return
        for v in range(lo, -1, -1):
            rec(pref + [v], v)
    rec([], n - 1)
    return out

def eg_equality_ks(d, n):
    """k in 1..n-1 where Erdos-Gallai holds with equality.

    ⚠ NOT a decomposability test.  The docstring here used to call this a "Tyshkevich decomposability
    signal" and every main-line sweep filtered on it.  Measured 2026-08-18
    (`results/2026-08-18_tyshkevich_not_equivalent_to_eg.md`): it is not equivalent to Tyshkevich
    decomposability in either direction.  P4 = (2,2,1,1) is INDECOMPOSABLE and has equality at k=2;
    (1,1,1,1,0) is DECOMPOSABLE with no equality anywhere.  Under the other main-line hypotheses the
    error is one-sided and costs coverage: 26 of the 161 main-line sequences through order 7 are
    indecomposable yet carry an equality, so filtering on this SKIPS 16% of the main line.

    The function itself is fine and is still used for what it actually says.  For the main line use
    `tyshkevich_decomposable` below.
    """
    ks = []
    for k in range(1, n):
        lhs = sum(d[:k]); rhs = k * (k - 1) + sum(min(x, k) for x in d[k:])
        if lhs == rhs: ks.append(k)
    return ks


def tyshkevich_decomposable(mask, n, idx):
    """Is the graph `mask` Tyshkevich-decomposable?  From the DEFINITION, no criterion involved.

    A composition splits the vertices as A + B + C with A + B and C both nonempty, A a clique, B
    independent, A complete to C, and B anticomplete to C.  (Edges inside C and between A and B are
    unconstrained; that is the splitted-graph factor composed with an arbitrary graph.)

    Decomposability is a property of the DEGREE SEQUENCE -- Tyshkevich's theorem -- so any one
    realization answers for all of them.  That is checked rather than assumed: over every graph on at
    most 6 vertices, all realizations of a sequence agree, 0 disagreements, and
    `tyshkevich_agreement_check` below re-runs it for a given order.
    """
    adj = [[bool(mask >> idx[(u, w)] & 1) if u != w else False for w in range(n)] for u in range(n)]
    for assign in itertools.product((0, 1, 2), repeat=n):
        A = [v for v in range(n) if assign[v] == 0]
        B = [v for v in range(n) if assign[v] == 1]
        C = [v for v in range(n) if assign[v] == 2]
        if not C or not (A or B):
            continue
        if any(not adj[u][w] for u, w in itertools.combinations(A, 2)):
            continue
        if any(adj[u][w] for u, w in itertools.combinations(B, 2)):
            continue
        if any(not adj[a][c] for a in A for c in C):
            continue
        if any(adj[b][c] for b in B for c in C):
            continue
        return True
    return False


def tyshkevich_agreement_check(n, ed, idx):
    """All realizations of a sequence agree on decomposability.  Returns the count of disagreements.

    This is the hypothesis that lets `tyshkevich_decomposable` be called on one realization.  Run it
    before trusting a sweep at a new order, rather than inheriting the result from order 6.
    """
    bad = 0
    for d in graphical_seqs(n):
        adjR = realizations(d, n, ed, idx)
        if adjR is None:
            continue
        vals = {tyshkevich_decomposable(g, n, idx) for g in adjR}
        if len(vals) > 1:
            bad += 1
    return bad

def run(n, verbose=False):
    ed, idx = setup(n)
    stats = dict(seqs=0, pivots=0, adjmismatch=0, notshifted=0, badtemplate=0,
                 badtempl_admissible=0, gap_pairs=0, gap_seqs=0)
    badlist = []; gaplist = []
    for d in graphical_seqs(n):
        adjR = realizations(d, n, ed, idx)
        if adjR is None or len(adjR) < 2: continue
        stats['seqs'] += 1
        R = list(adjR)
        Rset = set(R)
        gbip = is_bipartite(R, adjR)
        egk = eg_equality_ks(d, n)
        # degree-descending order on ground, tie-break by index  -> Gale order position
        pos_all = sorted(range(n), key=lambda v: (-d[v], v))
        # per-pivot data
        pivdata = {}
        for mu in range(n):
            I = {}
            for g in R: I.setdefault(nbrhood(g, mu, n, idx), []).append(g)
            if len(I) < 2: continue          # mu inactive as a pivot
            stats['pivots'] += 1
            keys = list(I)
            # quotient adjacency (actual) vs Johnson adjacency
            qadj = {S: set() for S in keys}
            for g in R:
                S = nbrhood(g, mu, n, idx)
                for h in adjR[g]:
                    T = nbrhood(h, mu, n, idx)
                    if T != S: qadj[S].add(T); qadj[T].add(S)
            jadj = {S: set() for S in keys}
            for S, T in itertools.combinations(keys, 2):
                if len(S ^ T) == 2: jadj[S].add(T); jadj[T].add(S)
            if qadj != jadj:
                stats['adjmismatch'] += 1
                if verbose: print("ADJ-MISMATCH", d, mu)
            # shifted / Gale ideal test under degree-descending order of [n]\{mu}
            ordv = [v for v in pos_all if v != mu]
            rank = {v: i for i, v in enumerate(ordv)}
            def galevec(S): return tuple(sorted(rank[v] for v in S))
            vecs = {galevec(S) for S in keys}
            shifted = True
            for vec in vecs:                     # down-closed: lower any coordinate
                for i in range(len(vec)):
                    for newv in range(0, vec[i]):
                        cand = sorted(vec[:i] + (newv,) + vec[i+1:])
                        if len(set(cand)) != len(cand): continue
                        if tuple(cand) not in vecs: shifted = False; break
                    if not shifted: break
                if not shifted: break
            if not shifted:
                stats['notshifted'] += 1
                if verbose: print("NOT-SHIFTED", d, mu)
            # bad template?
            bt = bad_template(keys, qadj)
            fibnb = {S: not is_bipartite(I[S], {g: adjR[g] & set(I[S]) for g in I[S]}) for S in keys}
            anyfibnb = any(fibnb.values())
            if bt is not None:
                stats['badtemplate'] += 1
                if anyfibnb: stats['badtempl_admissible'] += 1
                badlist.append((d, mu, tuple(sorted(map(sorted, bt))), len(keys), anyfibnb, gbip, egk))
            pivdata[mu] = (I, bt, anyfibnb)
        # (E) the decisive pair sweep -- only meaningful for non-bipartite non-K3 G(d)
        if gbip or len(R) == 3: continue
        if not any(v[1] is not None for v in pivdata.values()): continue   # no exception anywhere
        for X, Y in itertools.combinations(R, 2):
            admissible = []; good = []
            for mu, (I, bt, anyfibnb) in pivdata.items():
                SX = nbrhood(X, mu, n, idx); SY = nbrhood(Y, mu, n, idx)
                if SX == SY or not anyfibnb: continue
                admissible.append(mu)
                if bt is None or {SX, SY} != {bt[0], bt[1]}: good.append(mu)
            if admissible and not good:
                stats['gap_pairs'] += 1
                gaplist.append((d, X, Y, admissible))
    return stats, badlist, gaplist

if __name__ == '__main__':
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    for n in range(4, NMAX + 1):
        st, bad, gap = run(n)
        print(f"n={n}: {st}", flush=True)
        for b in bad[:12]: print("   BADTEMPLATE d=%s mu=%s univ=%s |I|=%d fibreNB=%s G(d)bip=%s EGeq=%s" % b, flush=True)
        if len(bad) > 12: print(f"   ... {len(bad)} bad-template pivots total", flush=True)
        for g in gap[:6]: print("   GAP d=%s admissible-but-all-exceptional pivots=%s" % (g[0], g[3]), flush=True)
