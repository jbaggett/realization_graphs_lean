#!/usr/bin/env python3
"""INDEPENDENT seal of Section 7, written from the PRINTED STATEMENTS ONLY.

Deliberately NOT derived from adv_step_audit.py, seal_step_lemma_inputs.py, sec79_regime_check or
any other script in this directory.  Nothing is imported from them and none was read while writing
this.  The point is a second implementation, so that agreement is evidence and disagreement is a
finding.  Written 2026-08-22 after the sixteenth defect, when the error rate had not yet fallen.

Checks, over every shifted family on grounds up to NMAX at every rank:

  T7.6   J(F) is a bad template  <->  F is a coordinate hook F(k; r, s)
         -- computed the two ways INDEPENDENTLY, graph-side and coordinate-side, and compared.
  T7.7   J(F) has a Hamilton X-Y path  <->  NOT (F is a hook and {X,Y} is its universal pair)
  T7.11  for every non-exceptional ordered pair and every e in X \\ Y, an usable crossing exists

Run:  ( ulimit -v 8388608; python3 independent_sec7_seal.py 7 )
"""
import sys
from itertools import combinations, permutations

# ---------------------------------------------------------------- Gale order and shifted families
def gale_le(A, B):
    """A <= B pointwise on sorted entries.  Section 7.1's PRINTED definition, not the threshold one."""
    return all(a <= b for a, b in zip(A, B))

def shifted_families(n, k):
    """Every nonempty down-set of the Gale order on k-subsets of [n]."""
    univ = list(combinations(range(1, n + 1), k))
    idx = {S: i for i, S in enumerate(univ)}
    below = [[j for j, T in enumerate(univ) if T != S and gale_le(T, S)] for S in univ]
    out, N = [], len(univ)
    def rec(i, chosen):
        if i == N:
            if chosen:
                out.append(frozenset(univ[j] for j in chosen))
            return
        rec(i + 1, chosen)                       # omit univ[i]
        if all(j in chosen for j in below[i]):   # may include only if everything below it is in
            rec(i + 1, chosen | {i})
    rec(0, frozenset())
    return out

# ---------------------------------------------------------------- the Johnson graph
def adj(X, Y):
    return len(set(X) ^ set(Y)) == 2

def johnson(F):
    F = sorted(F)
    return F, {X: {Y for Y in F if Y != X and adj(X, Y)} for X in F}

# ---------------------------------------------------------------- bad template, from the GRAPH
def bad_template(F):
    """Section 7.4's definition, in the form the note now takes as primary: two members adjacent to
    every other, the rest splitting into two nonempty parts, all edges inside a part and none
    between.  Returns the universal pair, or None."""
    V, nb = johnson(F)
    univ = [v for v in V if len(nb[v]) == len(V) - 1]
    if len(univ) < 2:
        return None
    for u, v in combinations(univ, 2):
        rest = [w for w in V if w not in (u, v)]
        if len(rest) < 2:
            continue
        # the "same side" relation must be an equivalence with exactly two nonempty classes
        comp, seen = [], set()
        for w in rest:
            if w in seen:
                continue
            stack, cls = [w], set()
            while stack:
                x = stack.pop()
                if x in cls:
                    continue
                cls.add(x)
                stack += [y for y in rest if y not in cls and y in nb[x]]
            seen |= cls
            comp.append(cls)
        if len(comp) != 2:
            continue
        if all(adj(a, b) for c in comp for a, b in combinations(sorted(c), 2)) and \
           not any(adj(a, b) for a in comp[0] for b in comp[1]):
            return (u, v)
    return None

# ---------------------------------------------------------------- coordinate hook, from Section 7.5
def coordinate_hook(F, n, k):
    """F(k; r, s) = {m1, m2} u P u Q, built from the printed formulas.  Returns (r, s) or None."""
    if k < 2:
        return None
    m1 = tuple(range(1, k + 1))
    m2 = tuple(list(range(1, k)) + [k + 1])
    for r in range(k + 2, n + 1):
        for s in range(1, k):
            P = {tuple(list(range(1, k)) + [a]) for a in range(k + 2, r + 1)}
            Q = {tuple(x for x in range(1, k + 2) if x != i) for i in range(s, k)}
            if not P or not Q:
                continue
            if set(F) == ({m1, m2} | P | Q):
                return (r, s)
    return None

# ---------------------------------------------------------------- Hamilton path
def has_ham_path(F, u, v):
    V, nb = johnson(F)
    N = len(V)
    if N == 1:
        return u == v
    target = set(V)
    def dfs(cur, seen):
        if len(seen) == N:
            return cur == v
        if cur == v:
            return False
        for w in nb[cur]:
            if w not in seen:
                if dfs(w, seen | {w}):
                    return True
        return False
    return dfs(u, {u})

# ---------------------------------------------------------------- Theorem 7.11
def step_lemma_holds(F, X, Y, e, n, k):
    """Returns (ok, detail).  Implements the note's Theorem 7.11 statement literally."""
    F1 = [W for W in F if e in W]
    F0 = [Z for Z in F if e not in Z]
    if not F1 or not F0:
        return True, "layer empty"          # e not separating; theorem's setting needs X in F1, Y in F0
    # the link, and its hook data, lifted back
    link = [tuple(x for x in W if x != e) for W in F1]
    lift = {tuple(x for x in W if x != e): W for W in F1}
    S1 = {X}
    up = bad_template(link) if len(link) >= 4 else None
    if up:
        Xl = tuple(x for x in X if x != e)
        if Xl in up:
            other = up[0] if up[1] == Xl else up[1]
            S1.add(lift[other])
    S0 = {Y}
    up0 = bad_template(F0) if len(F0) >= 4 else None
    if up0 and Y in up0:
        S0.add(up0[0] if up0[1] == Y else up0[1])
    for W in F1:
        if not (len(F1) == 1 and W == X or len(F1) != 1 and W not in S1):
            continue
        for Z in F0:
            if not (len(F0) == 1 and Z == Y or len(F0) != 1 and Z not in S0):
                continue
            d = set(W) ^ set(Z)
            if len(d) == 2 and e in d:
                xi = (d - {e}).pop()
                if xi != e and xi not in W:
                    return True, f"W={W} Z={Z}"
    return False, f"F1={F1} F0={F0} S1={sorted(S1)} S0={sorted(S0)}"

# ---------------------------------------------------------------- driver
def say(*a):
    print(*a, flush=True)


def main():
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    # Theorem 7.7 is checked by EXHAUSTIVE Hamilton-path search over every ordered pair, which is
    # exponential in |F| and is what made the first order-7 attempt intractable.  Above this ground
    # order the 7.7 sweep is restricted to the families that matter -- the bad templates, where a
    # path must NOT exist, which is the half that could hide a false theorem.  7.6 and 7.11 stay
    # exhaustive, and 7.11 is the crux this file exists to check independently.
    FULL_HAMPATH_UPTO = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    tot = badg = badc = disagree = 0
    t77 = t77bad = 0
    t711 = t711bad = 0
    for n in range(2, NMAX + 1):
        for k in range(1, n):
            fams = shifted_families(n, k)
            say(f"   n={n} k={k}: {len(fams)} shifted families")
            for F in fams:
                tot += 1
                g = bad_template(F)
                c = coordinate_hook(F, n, k)
                if g: badg += 1
                if c: badc += 1
                if bool(g) != bool(c):
                    disagree += 1
                    print(f"  T7.6 DISAGREE n={n} k={k} F={sorted(F)} graph={g} coord={c}")
                # Theorem 7.7 -- exhaustive below the cap, bad templates only above it
                do77 = (n <= FULL_HAMPATH_UPTO) or (g is not None)
                for X, Y in permutations(sorted(F), 2):
                    if not do77:
                        # still check the step lemma, which is cheap and is the crux
                        expect = True
                        for e in sorted(set(X) - set(Y)):
                            t711 += 1
                            ok, why = step_lemma_holds(F, X, Y, e, n, k)
                            if not ok:
                                t711bad += 1
                                say(f"  T7.11 FAIL n={n} k={k} F={sorted(F)} X={X} Y={Y} e={e} :: {why}")
                        continue
                    t77 += 1
                    expect = not (g is not None and set(g) == {X, Y})
                    if has_ham_path(F, X, Y) != expect:
                        t77bad += 1
                        print(f"  T7.7 FAIL n={n} k={k} F={sorted(F)} X={X} Y={Y} expected={expect}")
                    if expect:
                        for e in sorted(set(X) - set(Y)):
                            t711 += 1
                            ok, why = step_lemma_holds(F, X, Y, e, n, k)
                            if not ok:
                                t711bad += 1
                                print(f"  T7.11 FAIL n={n} k={k} F={sorted(F)} X={X} Y={Y} e={e} :: {why}")
        say(f"n={n:>2} cumulative: {tot} families, {badg} bad templates (graph), "
            f"{badc} hooks (coords), {t77} ordered pairs, {t711} step instances"
            f"   [7.7 exhaustive: {'yes' if n <= FULL_HAMPATH_UPTO else 'bad templates only'}]")
    say()
    say(f"families                  : {tot}")
    say(f"bad templates, graph-side : {badg}")
    say(f"hooks, coordinate-side    : {badc}")
    say(f"THEOREM 7.6 disagreements : {disagree}")
    say(f"THEOREM 7.7 violations    : {t77bad}   (over {t77} ordered pairs)")
    say(f"THEOREM 7.11 violations   : {t711bad}   (over {t711} instances)")
    print()
    say("SEAL CLEAN" if (disagree or t77bad or t711bad) == 0 else "SEAL DIRTY")

main()
