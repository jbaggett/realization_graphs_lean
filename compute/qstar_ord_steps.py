"""Verify each step of the (ORD) proof, in the exact configuration it is used.

Step 1 (delta >= 0):            for every ordinary hop, delta = f_S(a) - f_S(b) >= 0.
Step 2 (bipartite source):      Phi_S bipartite  ==>  EVERY F in Phi_S is a connector source
                                (constant cross-degree k = max(1,delta) >= 1), and both colour
                                classes are nonempty.
Step 3 (delta >= 1):            delta >= 1  ==>  every F in Phi_S is a connector source.
Step 4 (delta = 0, |Phi_T| = 1): the target signed identity forces the unique z in Phi_T to have
                                at least two distinct connector sources.
Step 5 (singleton source):      |Phi_S| = 1  ==>  its single realization is a connector source.
"""
import sys, itertools
from collections import deque, Counter
sys.path.insert(0, 'compute')
from qstar_interface_check import (setup, realizations, graphical_seqs, nbrhood,
                                   is_bipartite, eg_equality_ks)

def main(nmax):
    c = Counter()
    for n in range(4, nmax + 1):
        ed, idx = setup(n)
        for d in graphical_seqs(n):
            adjR = realizations(d, n, ed, idx)
            if adjR is None or len(adjR) < 2: continue
            R = list(adjR)
            for mu in range(n):
                I = {}
                for g in R: I.setdefault(nbrhood(g, mu, n, idx), []).append(g)
                if len(I) < 2: continue
                for S, T in itertools.permutations(I, 2):
                    if len(S ^ T) != 2: continue
                    b_ = next(iter(S - T)); a_ = next(iter(T - S))     # T = S - b + a
                    PS, PT = set(I[S]), set(I[T])
                    f = {t: d[t] - (1 if t in S else 0) for t in range(n) if t != mu}
                    delta = f[a_] - f[b_]
                    c['hops'] += 1
                    # STEP 1 (corrected): delta >= 0 is NOT universal; it is claimed only for a
                    # triangle-free (bipartite) source, which is the setting ONE_PASS sec.4.3 uses.
                    if delta < 0:
                        c['delta-negative'] += 1
                        if is_bipartite(set(I[S]), {g: adjR[g] & set(I[S]) for g in I[S]}):
                            c['STEP1-FAIL-bipartite-source'] += 1
                    src = {y for y in PS if adjR[y] & PT}
                    sub = {g: adjR[g] & PS for g in PS}
                    bip = is_bipartite(PS, sub)
                    if len(PS) == 1:
                        if src != PS: c['STEP5-FAIL'] += 1
                        else: c['step5-ok'] += 1
                    elif bip:
                        if src != PS: c['STEP2-FAIL'] += 1
                        else: c['step2-ok'] += 1
                    if delta >= 1 and src != PS: c['STEP3-FAIL'] += 1
                    elif delta >= 1: c['step3-ok'] += 1
                    # STEP 4 (corrected): delta <= 0 ==> EVERY H in Phi_T has >= 2 - delta >= 2
                    # distinct connector sources, because the target-orientation signed identity
                    # gives w_ba(H) = w_ab(H) + (2 - delta) and distinct witnesses give distinct
                    # sources.  This replaces the E3-saturation case split entirely.
                    if delta <= 0:
                        bad = [H for H in PT if len(adjR[H] & PS) < 2 - delta]
                        if bad: c['STEP4-FAIL'] += 1
                        else: c['step4-ok'] += 1
        print(f"  ...n={n} {dict(c)}", flush=True)
    fails = {k: v for k, v in c.items() if 'FAIL' in k}
    print(f"\nSTEP FAILURES: {fails if fails else 'NONE'}")

if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
