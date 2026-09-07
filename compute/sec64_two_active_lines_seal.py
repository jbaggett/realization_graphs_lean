#!/usr/bin/env python3
"""Seal for Section 6.4's two-active-lines branch (worklist item B2).

The branch asserts four structural facts and proves none of them.  This recomputes each one
from scratch over an exhaustive range and refuses to report success unless every instance holds.
It also checks a FIFTH fact the branch needs and never states: that "at most two active lines on
a side" is always "exactly two".

The passage matters because the 2026-08-24 readability pass found a FALSE statement inside it
(Part D item 1 of the worklist) after thirteen correctness-aimed adversaries had missed it.

CLAIMS SEALED
  C0  a class with two distinct matrices has >= 2 active rows AND >= 2 active columns
  C1  with exactly two active rows, every active column has exactly one 1 among them,
      the class is named by k-subsets of the f active columns, and the interchange graph
      is exactly the Johnson graph J(f,k), with 1 <= k <= f-1 (hence f >= 2)
  C2  at a differing opposite line the two fibers are J(f-1,k-1) and J(f-1,k), and for
      f >= 4 at least one is nondegenerate and contains a triangle
  C3  f = 3 forces the split graph to be the chair (3,2,1,1,1) or its complement, and G(d) = K_3
  C4  f = 2 forces G(d) = K_2, which is bipartite
  CJ  for 1 <= j <= m-1, J(m,j) contains a triangle IFF m >= 3
"""
import resource, sys
resource.setrlimit(resource.RLIMIT_AS, (6_000_000_000, 6_000_000_000))
from itertools import combinations, product

def mats(rs, cs):
    """All 0/1 matrices with row sums rs and column sums cs."""
    m, n = len(rs), len(cs)
    out = []
    def rec(i, rem):
        if i == m:
            if all(v == 0 for v in rem): out.append(tuple(cur))
            return
        for S in combinations(range(n), rs[i]):
            if any(rem[j] == 0 for j in S): continue
            row = tuple(1 if j in S else 0 for j in range(n))
            nr = list(rem)
            for j in S: nr[j] -= 1
            if sum(nr) != sum(rs[i+1:]): continue
            cur.append(row); rec(i+1, nr); cur.pop()
    cur = []
    rec(0, list(cs))
    return out

def adjacent(A, B):
    d = [(i, j) for i in range(len(A)) for j in range(len(A[0])) if A[i][j] != B[i][j]]
    if len(d) != 4: return False
    rows = {i for i, _ in d}; cols = {j for _, j in d}
    return len(rows) == 2 and len(cols) == 2

def johnson(f, k):
    V = [frozenset(S) for S in combinations(range(f), k)]
    E = {(a, b) for a in V for b in V if a != b and len(a ^ b) == 2}
    return V, E

def has_triangle(V, E):
    adj = {v: set() for v in V}
    for a, b in E: adj[a].add(b)
    for a in V:
        for b in adj[a]:
            if adj[a] & adj[b]: return True
    return False

fails, checked = [], {c: 0 for c in ["C0","C1","C2","C3","C4","CJ"]}

# ---------------- CJ : the triangle criterion, on its own ----------------
for m in range(2, 13):
    for j in range(1, m):
        V, E = johnson(m, j)
        got, want = has_triangle(V, E), (m >= 3)
        checked["CJ"] += 1
        if got != want: fails.append(f"CJ J({m},{j}): triangle={got} expected {want}")

# ---------------- the matrix sweep ----------------
MAXR, MAXC, MAXSUM = 4, 6, 9
for m in range(2, MAXR + 1):
    for n in range(2, MAXC + 1):
        for rs in product(range(n + 1), repeat=m):
            if sum(rs) > MAXSUM: continue
            for cs in product(range(m + 1), repeat=n):
                if sum(cs) != sum(rs): continue
                C = mats(list(rs), list(cs))
                if len(C) < 2: continue
                arows = [i for i in range(m) if len({M[i] for M in C}) > 1]
                acols = [j for j in range(n) if len({tuple(M[i][j] for i in range(m)) for M in C}) > 1]

                # ---- C0 : two distinct matrices force two active lines on each side ----
                checked["C0"] += 1
                if len(arows) < 2 or len(acols) < 2:
                    fails.append(f"C0 rs={rs} cs={cs}: |arows|={len(arows)} |acols|={len(acols)}")
                    continue
                # The branch runs under Section 6.4's ACTIVITY hypothesis, which has already
                # removed every inactive line.  Restricting here is what makes "the matrix is
                # exactly 2 x f" meaningful; the first run of this seal omitted the restriction
                # and reported 100+ chair failures that were padding, not mathematics.
                if len(arows) != m or len(acols) != n: continue
                if len(arows) != 2: continue

                r1, r2 = arows
                f = len(acols)
                # ---- C1a : each active column meets exactly one of the two active rows ----
                checked["C1"] += 1
                if not all(M[r1][j] + M[r2][j] == 1 for M in C for j in acols):
                    fails.append(f"C1a rs={rs} cs={cs}: an active column does not meet exactly one active row"); continue
                name = {M: frozenset(j for j in acols if M[r1][j] == 1) for M in C}
                ks = {len(s) for s in name.values()}
                if len(ks) != 1:
                    fails.append(f"C1b rs={rs} cs={cs}: named sets of differing size {ks}"); continue
                k = ks.pop()
                if not (1 <= k <= f - 1) or f < 2:
                    fails.append(f"C1c rs={rs} cs={cs}: f={f} k={k} outside 1<=k<=f-1"); continue
                # ---- C1d : the naming is an isomorphism onto J(f,k) ----
                idx = {c: i for i, c in enumerate(sorted(acols))}
                got = {frozenset(idx[j] for j in name[M]) for M in C}
                JV, JE = johnson(f, k)
                if got != set(JV):
                    fails.append(f"C1d rs={rs} cs={cs}: named sets are not all k-subsets"); continue
                bad = any(adjacent(A, B) != (len(name[A] ^ name[B]) == 2)
                          for A in C for B in C if A != B)
                if bad:
                    fails.append(f"C1e rs={rs} cs={cs}: interchange != symmetric difference two"); continue

                # ---- C2 : fibers at a differing opposite line ----
                for c in acols:
                    checked["C2"] += 1
                    inn = [M for M in C if c in name[M]]
                    out = [M for M in C if c not in name[M]]
                    for part, kk in ((inn, k - 1), (out, k)):
                        JV2, _ = johnson(f - 1, kk)
                        if len(part) != len(JV2):
                            fails.append(f"C2 rs={rs} cs={cs} c={c}: fiber size {len(part)} != |J({f-1},{kk})|")
                if f >= 4:
                    nd = [kk for kk in (k - 1, k) if 1 <= kk <= f - 2]
                    if not nd:
                        fails.append(f"C2b rs={rs} cs={cs}: f={f} k={k} has NO nondegenerate fiber")
                    elif not any(has_triangle(*johnson(f - 1, kk)) for kk in nd):
                        fails.append(f"C2c rs={rs} cs={cs}: no nondegenerate fiber carries a triangle")

                # ---- C3 / C4 : the small parents ----
                if f == 3:
                    checked["C3"] += 1
                    # every line active, so the matrix is exactly 2 x 3; the split graph it codes
                    deg = sorted([1 + k, 1 + (3 - k)] + [1, 1, 1], reverse=True)
                    if m != 2 or n != 3 or deg != [3, 2, 1, 1, 1]:
                        fails.append(f"C3 rs={rs} cs={cs}: shape {m}x{n} degrees {deg} not the chair")
                    if len(C) != 3 or not has_triangle(*johnson(3, k)):
                        fails.append(f"C3b rs={rs} cs={cs}: class is not K_3")
                if f == 2:
                    checked["C4"] += 1
                    if len(C) != 2:
                        fails.append(f"C4 rs={rs} cs={cs}: |class|={len(C)} not 2")

# ---------------- the two-active-row family, pushed ----------------
# Under activity the matrix IS exactly 2 x f with every column sum one, so the family is small
# and can be swept in full rather than sampled.  MAXC above only reaches f = 6; this reaches 12,
# and it is where C2's "f >= 4" clause gets real coverage.
wide = 0
for f in range(2, 13):
    for k in range(1, f):
        rs, cs = [k, f - k], [1] * f
        C = mats(rs, cs)
        wide += 1
        arows = [i for i in range(2) if len({M[i] for M in C}) > 1]
        acols = [j for j in range(f) if len({tuple(M[i][j] for i in range(2)) for M in C}) > 1]
        if len(arows) != 2 or len(acols) != f:
            fails.append(f"WIDE f={f} k={k}: not every line active ({len(arows)},{len(acols)})"); continue
        name = {M: frozenset(j for j in range(f) if M[0][j] == 1) for M in C}
        JV, JE = johnson(f, k)
        if {name[M] for M in C} != set(JV):
            fails.append(f"WIDE f={f} k={k}: named sets are not the k-subsets"); continue
        if any(adjacent(A, B) != (len(name[A] ^ name[B]) == 2) for A in C for B in C if A != B):
            fails.append(f"WIDE f={f} k={k}: interchange != symmetric difference two"); continue
        for c in range(f):
            for part, kk in (([M for M in C if c in name[M]], k - 1),
                             ([M for M in C if c not in name[M]], k)):
                if len(part) != len(johnson(f - 1, kk)[0]):
                    fails.append(f"WIDE f={f} k={k} c={c}: fiber size wrong for J({f-1},{kk})")
        if f >= 4:
            nd = [kk for kk in (k - 1, k) if 1 <= kk <= f - 2]
            if not nd:
                fails.append(f"WIDE f={f} k={k}: NO nondegenerate fiber")
            elif not any(has_triangle(*johnson(f - 1, kk)) for kk in nd):
                fails.append(f"WIDE f={f} k={k}: no nondegenerate fiber carries a triangle")
        if f == 3 and len(C) != 3: fails.append(f"WIDE f=3 k={k}: class is not K_3")
        if f == 2 and len(C) != 2: fails.append(f"WIDE f=2 k={k}: class is not K_2")
checked["WIDE"] = wide

print(f"instances checked per claim: {checked}")
if fails:
    from collections import Counter
    print(f"\nFAILURES: {len(fails)}  by claim: {Counter(s.split()[0] for s in fails)}")
    for s in fails[:25]: print("  ", s)
    sys.exit(1)
print("\nRESULT: PASS — every claim of Section 6.4's two-active-lines branch holds on the swept range.")
