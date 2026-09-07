#!/usr/bin/env python3
"""Run Section 10.2's construction on the worked-example instance and verify its output.

⚠ DISPLAY IS 1-BASED (OFF = 1), changed 2026-09-07 on Jeff's comment that the paper labels its
ground 1..n everywhere else and 0..n-1 here read as odd.  The construction and every check still
run on 0..n-1; only printing moved, so the "refuses to emit unless it is a Hamilton path" property
is untouched.

Worklist item B13.  Section 10 describes a construction and never runs it.  This runs it, on
d = (4,2,2,2,1,1) chosen by sec10_walkthrough_instance_sweep.py, following 10.2 STEP BY STEP --
pivot, quotient Hamilton path, buffer, two chains in, spanning buffer run, concatenate -- and then
applies Section 10.3's own test to the result.  It refuses to emit unless the list really is a
Hamilton G_0-G_1 path of G(d).

Every number Section 10's worked example quotes comes out of here.
"""
import resource, sys, itertools, json
resource.setrlimit(resource.RLIMIT_AS, (8_000_000_000, 8_000_000_000))
# Paths are derived from this file, not from a home directory: the same script has to run in a
# clone of the companion repository, where no such home directory exists.  In the working
# tree this resolves to exactly the location the absolute paths named before 2026-09-07.
HERE = __import__("pathlib").Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

D = (4, 2, 2, 2, 1, 1)
N = len(D)
import adversary_sbplus_n9n10_2026_08_15 as A   # for pivot_family / hook_universal_pair

pairs = list(itertools.combinations(range(N), 2))
V = []
for S in itertools.combinations(pairs, sum(D) // 2):
    deg = [0] * N
    for u, v in S: deg[u] += 1; deg[v] += 1
    if tuple(deg) == D: V.append(frozenset(S))
adj = {g: {h for h in V if h != g and len(g ^ h) == 4} for g in V}

def nb(G, v): return frozenset(y for x, y in G if x == v) | frozenset(x for x, y in G if y == v)
OFF = 1   # DISPLAY ONLY: the paper labels its ground 1..n everywhere else, so emit 1-based.
          # The construction and every check below still run on 0..n-1; nothing but printing moves.
def show(G): return " ".join(f"{u+OFF}{v+OFF}" for u, v in sorted(G))
def sh(xs): return [x+OFF for x in sorted(xs)]

def bipartite(nodes):
    sub = {u: adj[u] & set(nodes) for u in nodes}; col = {}
    for s in nodes:
        if s in col: continue
        col[s] = 0; st = [s]
        while st:
            u = st.pop()
            for w in sub[u]:
                if w not in col: col[w] = 1 - col[u]; st.append(w)
                elif col[w] == col[u]: return False
    return True

def mask(s): return sum(1 << i for i in s)

# ---- Section 8's notion: EXCEPTIONAL means the quotient family at v is a Y-family AND the
# ---- prescribed pair {N_{G_0}(v), N_{G_1}(v)} is its universal pair.  It depends on the PAIR.
UP = {}
for v in range(N):
    order, fam = A.pivot_family(D, v)
    UP[v] = A.hook_universal_pair(order, fam, D[v])

def fibres_at(v):
    F = {}
    for G in V: F.setdefault(nb(G, v), []).append(G)
    return F

def classify(G0, G1):
    adm, exc = [], []
    for v in range(N):
        if nb(G0, v) == nb(G1, v): continue
        F = fibres_at(v)
        if not any(len(p) >= 3 and not bipartite(p) for p in F.values()): continue
        adm.append(v)
        if UP[v] is not None and {mask(nb(G0, v)), mask(nb(G1, v))} == set(UP[v]): exc.append(v)
    return adm, exc

# choose the prescribed pair: it must have a GENUINELY exceptional admissible pivot, so the
# walkthrough shows Section 8 dodging rather than a pivot that was never in danger.
CHOICE = None
for G0, G1 in itertools.combinations(V, 2):
    adm, exc = classify(G0, G1)
    if not exc: continue
    dclass = [u for u in range(N) if D[u] == D[exc[0]]]
    survivors = [u for u in dclass if u in adm and u not in exc]
    if survivors: CHOICE = (G0, G1, adm, exc, dclass, survivors); break
if CHOICE is None:
    print("REFUSING TO EMIT: no pair exercises the Section 8 dodge."); sys.exit(1)
G0c, G1c, ADM, EXC, DCLASS, SURV = CHOICE
PIV = SURV[0]

FIB = {}
for G in V: FIB.setdefault(nb(G, PIV), []).append(G)
QV = sorted(FIB, key=lambda s: sorted(s))
QI = {s: i for i, s in enumerate(QV)}
QE = {(i, j) for i in range(len(QV)) for j in range(len(QV)) if i < j and len(QV[i] ^ QV[j]) == 2}
qadj = {i: set() for i in range(len(QV))}
for a, b in QE: qadj[a].add(b); qadj[b].add(a)

BUFFERS = [i for i, s in enumerate(QV) if len(FIB[s]) >= 3 and not bipartite(FIB[s])]

def ham_in_fibre(nodes, start, end=None):
    """Spanning run of a fibre from `start`, to `end` if prescribed."""
    nodes = set(nodes); out = []
    def rec(path, seen):
        if len(path) == len(nodes):
            if end is None or path[-1] == end: out.append(list(path)); return True
            return False
        for w in adj[path[-1]] & nodes:
            if w in seen: continue
            path.append(w); seen.add(w)
            if rec(path, seen): return True
            seen.discard(w); path.pop()
        return False
    rec([start], {start})
    return out[0] if out else None

def qham(a, b):
    out = []
    def rec(path, seen):
        if len(path) == len(QV):
            if path[-1] == b: out.append(list(path)); return True
            return False
        for w in qadj[path[-1]] - seen:
            path.append(w); seen.add(w)
            if rec(path, seen): return True
            seen.discard(w); path.pop()
        return False
    rec([a], {a})
    return out[0] if out else None

def build(G0, G1, buf, want="interior"):
    A, B = QI[nb(G0, PIV)], QI[nb(G1, PIV)]
    if A == B: return None
    q = qham(A, B)
    if not q or buf not in q: return None
    j = q.index(buf)
    m = len(q) - 1
    if want == "interior" and not (0 < j < m): return None
    if want == "start"    and j != 0: return None
    if want == "end"      and j != m: return None
    # left chain: G_0 through q_0..q_{j-1}, entering the buffer at x
    left, cur, conn_l = [], G0, []
    for i in range(j):
        nxt = set(FIB[QV[q[i + 1]]])
        run = None
        for run_try in [ham_in_fibre(FIB[QV[q[i]]], cur, e) for e in FIB[QV[q[i]]]]:
            if run_try and (adj[run_try[-1]] & nxt): run = run_try; break
        if run is None: return None
        left.append(run); cur = next(iter(adj[run[-1]] & nxt)); conn_l.append((run[-1], cur))
    x = cur
    # right chain: G_1 backwards through q_m..q_{j+1}, last hop landing on y != x
    right, cur2, conn_r = [], G1, []
    for i in range(len(q) - 1, j, -1):
        nxt = set(FIB[QV[q[i - 1]]])
        if i - 1 == j: nxt = nxt - {x}                # Theorem 9.2: prescribed target excluded
        run = None
        for run_try in [ham_in_fibre(FIB[QV[q[i]]], cur2, e) for e in FIB[QV[q[i]]]]:
            if run_try and (adj[run_try[-1]] & nxt): run = run_try; break
        if run is None: return None
        right.append(run); cur2 = next(iter(adj[run[-1]] & nxt)); conn_r.append((run[-1], cur2))
    y = cur2
    if y == x: return None
    mid = ham_in_fibre(FIB[QV[buf]], x, y)
    if mid is None: return None
    path = [g for run in left for g in run] + mid + [g for run in reversed(right) for g in reversed(run)]
    return dict(A=A, B=B, q=q, j=j, x=x, y=y, left=left, mid=mid, right=right,
                conn_l=conn_l, conn_r=conn_r, path=path)

# ---- all three buffer positions are constructed and checked, because Section 10.2 claims a
# ---- different concatenation shape in each and Section 10.3 asserts the endpoints once for all.
POSITIONS = {}
for want in ("start", "interior", "end"):
    hit = None
    for G0, G1 in itertools.permutations(V, 2):
        for buf in BUFFERS:
            r = build(G0, G1, buf, want)
            if r: hit = (G0, G1, buf, r); break
        if hit: break
    POSITIONS[want] = hit

sol = POSITIONS["interior"]        # the worked example uses the generic position

if not sol:
    print("REFUSING TO EMIT: the construction produced no path."); sys.exit(1)
G0, G1, buf, r = sol
P = r["path"]

ok, why = True, []
def chk(c, t):
    global ok
    if not c: ok = False; why.append(t)
chk(len(P) == len(V), f"path has {len(P)} entries, G(d) has {len(V)} realizations")
chk(len(set(P)) == len(P), "no realization repeats")
chk(P[0] == G0 and P[-1] == G1, "endpoints are the prescribed pair")
chk(all(P[i + 1] in adj[P[i]] for i in range(len(P) - 1)), "every consecutive pair is a 2-switch")

nq = len(QV)
complete = (len(QE) == nq * (nq - 1) // 2)
print(f"d = {D},  {len(V)} realizations")
print(f"Section 6 hands over an admissible pivot; admissible = {sh(ADM)}")
print(f"  EXCEPTIONAL for this pair: {sh(EXC)}   degree class of {EXC[0]+OFF}: {sh(DCLASS)}")
print(f"  Section 8 dodges within the degree class to {sh(SURV)} -- using v = {PIV+OFF}")
print(f"quotient at v = {PIV+OFF}: {nq} vertices, {len(QE)} edges"
      f"{' (complete, K_%d)' % nq if complete else ' (NOT complete)'}")
print(f"  fibres {[len(FIB[s]) for s in QV]} at neighbourhoods {[sh(s) for s in QV]}")
print(f"  non-bipartite fibres (buffer candidates): {[sh(QV[i]) for i in BUFFERS] if BUFFERS and not isinstance(BUFFERS[0],int) else BUFFERS}\n")
print(f"G_0 = {show(G0)}   N(v) = A = {sh(QV[r['A']])}")
print(f"G_1 = {show(G1)}   N(v) = B = {sh(QV[r['B']])}")
print(f"quotient Hamilton A-B path: {[sh(QV[i]) for i in r['q']]}")
print(f"buffer is q_{r['j']} = {sh(QV[buf])}, entered at x and y:")
print(f"  x = {show(r['x'])}\n  y = {show(r['y'])}")
print(f"buffer run: {[show(g) for g in r['mid']]}\n")
print("the concatenated path:")
for i, g in enumerate(P): print(f"  {i+1}. {show(g)}   [fibre {QI[nb(g,PIV)]}]")
print()
for t in ["path has all 9 entries", "no realization repeats", "endpoints are the prescribed pair",
          "every consecutive pair is a 2-switch"]:
    print(f"  [{'FAIL' if any(t.split()[0] in w for w in why) else 'ok '}] {t}")
if not ok:
    print("\nREFUSING TO EMIT:", why); sys.exit(1)
out = str(HERE / "data" / "sec10_walkthrough_build.json")
(HERE / "data").mkdir(exist_ok=True)
json.dump({"d": list(D), "pivot": PIV,
           "admissible_pivots": ADM, "exceptional_for_this_pair": EXC,
           "degree_class": DCLASS, "section8_survivors": SURV,
           "quotient_is_complete": complete, "quotient_n": nq, "quotient_m": len(QE),
           "G0": show(G0), "G1": show(G1),
           "A": sorted(QV[r["A"]]), "B": sorted(QV[r["B"]]),
           "quotient_path": [sorted(QV[i]) for i in r["q"]],
           "buffer_index_on_path": r["j"], "buffer": sorted(QV[buf]),
           "x": show(r["x"]), "y": show(r["y"]),
           "buffer_run": [show(g) for g in r["mid"]],
           # run lengths IN THE ORDER THE PATH VISITS THE FIBRES -- the figure generator draws from
           # this rather than re-deriving it, so the picture cannot disagree with the verified path.
           "fibre_runs_in_path_order": [len(FIB[QV[qi]]) for qi in r["q"]],
           "fibre_sizes": [len(FIB[s]) for s in QV],
           "path": [show(g) for g in P]}, open(out, "w"), indent=1)
print("\nall three buffer positions, on this same instance:")
for want in ("start", "interior", "end"):
    h = POSITIONS[want]
    if h is None: print(f"  {want:9s}: NO INSTANCE"); chk(False, f"{want} position constructs"); continue
    g0, g1, _, rr = h; pp = rr["path"]
    good = (len(pp) == len(V) and len(set(pp)) == len(pp) and pp[0] == g0 and pp[-1] == g1
            and all(pp[i + 1] in adj[pp[i]] for i in range(len(pp) - 1)))
    chk(good, f"{want} position yields a Hamilton path")
    print(f"  {want:9s}: j={rr['j']} of m={len(rr['q'])-1}, left chain {len(rr['left'])} fibres, "
          f"right chain {len(rr['right'])}, x={'G_0' if rr['x']==g0 else 'interior'}, "
          f"y={'G_1' if rr['y']==g1 else 'interior'}  -> Hamilton path {good}")
if not ok:
    print("\nREFUSING TO EMIT:", why); sys.exit(1)

print(f"\nRESULT: PASS — Section 10.3's own test passes on the constructed list. Written to {out}")
