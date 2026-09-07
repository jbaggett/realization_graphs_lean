"""Rank-2 (Q*) base check: for every rank-2 shifted family on [n] (n <= NMAX),
every pair A != B: Hamilton A-B path exists in J(F) iff NOT (F = {12,13,23,14..1r} and {A,B}={12,13}).
Exact DFS with connectivity pruning."""
import sys
sys.setrecursionlimit(100000)

def enum_rank2(n):
    """down-closed families of 2-sets (i<j) under (i,j)<=(i',j') iff i<=i', j<=j'. BFS over ideals."""
    cells = [(i, j) for i in range(1, n+1) for j in range(i+1, n+1)]
    below = {c: [d for d in cells if d[0] <= c[0] and d[1] <= c[1]] for c in cells}
    from collections import deque
    seen = {frozenset()}; dq = deque([frozenset()]); out = []
    while dq:
        D = dq.popleft(); out.append(D)
        for c in cells:
            if c in D: continue
            if all(d in D or d == c for d in below[c]):
                E = D | {c}
                if E not in seen: seen.add(E); dq.append(E)
    return [D for D in out if len(D) >= 2]

def ham_path(adj, nverts, s, t):
    """exact: Hamilton s-t path exists? DFS + connectivity/degree pruning."""
    if nverts == 1: return s == t
    if s == t: return False
    full = (1 << nverts) - 1
    from functools import lru_cache
    def prune(cur, visited):
        # remaining graph (unvisited + cur) must be connected, and no unvisited vertex
        # other than t may have all neighbors visited (dead end); count deg-1 obstructions
        rem = full & ~visited
        # connectivity of rem | {cur}: BFS from cur over rem
        stack = [cur]; seen = 1 << cur
        while stack:
            v = stack.pop()
            m = adj[v] & rem & ~seen
            while m:
                b = m & -m; w = b.bit_length() - 1
                seen |= b; stack.append(w); m ^= b
        if (rem | (1 << cur)) & ~seen: return False
        # dead-end check
        m = rem
        while m:
            b = m & -m; w = b.bit_length() - 1; m ^= b
            if w != t:
                free = adj[w] & (rem | (1 << cur)) & ~(1 << w)
                if free == 0: return False
                # a non-t vertex whose only remaining neighbor is cur must be next
        return True
    sys.setrecursionlimit(10000)
    def dfs(cur, visited):
        if visited == full: return cur == t
        if cur == t: return False
        if not prune(cur, visited): return False
        m = adj[cur] & ~visited
        # visit forced vertices first: neighbors with only cur available
        while m:
            b = m & -m; w = b.bit_length() - 1; m ^= b
            if dfs(w, visited | (1 << w)): return True
        return False
    return dfs(s, 1 << s)

if __name__ == '__main__':
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    viol = 0; pairs = 0; fams = 0; nonham = 0
    for n in range(2, NMAX+1):
        for D in enum_rank2(n):
            if not any(c[1] == n for c in D): continue
            fams += 1
            vs = sorted(D)
            idx = {v: i for i, v in enumerate(vs)}
            m = len(vs)
            adj = [0]*m
            for a in range(m):
                for b in range(a+1, m):
                    if len(set(vs[a]) ^ set(vs[b])) == 2:
                        adj[a] |= 1 << b; adj[b] |= 1 << a
            # template test (explicit rank-2 hook): {12,13,23} + {1a: 4<=a<=r}, nothing else
            S = set(vs)
            is_hook = ((1,2) in S and (1,3) in S and (2,3) in S and
                       all(c == (2,3) or c[0] == 1 for c in S) and
                       sorted(c[1] for c in S if c[0] == 1) == list(range(2, 2 + sum(1 for c in S if c[0]==1))) and
                       len(S) >= 4)
            for a in range(m):
                for b in range(a+1, m):
                    pairs += 1
                    ok = ham_path(adj, m, a, b)
                    exc = is_hook and {vs[a], vs[b]} == {(1,2), (1,3)}
                    if not ok: nonham += 1
                    if ok == exc:
                        viol += 1
                        if viol <= 5: print("VIOL", n, vs, vs[a], vs[b], "ham", ok, "exc", exc)
        print(f"through n={n}: families {fams}, pairs {pairs}, non-Ham pairs {nonham}, violations {viol}", flush=True)
