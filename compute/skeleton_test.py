"""LEAD: is J(I) the SKELETON of the 0/1-polytope conv(I)?

Mutze's Gray-code survey (arXiv:2202.01280, sec 2.7) states Naddef-Pulleyblank [NP81,NP84] as:
EVERY 0/1-polytope is either Hamilton-connected or a hypercube.  That is far stronger than the
matroid-base version we cite.  A Gale ideal I is a set of 0/1 vectors, so conv(I) is a 0/1-polytope.
IF its skeleton equals J(I), then (Q) follows from NP immediately -- no induction, no (INS-b').

Two things to check:
 1. Hamming distance 2 => polytope edge.  (Proof for constant weight: for S=C+a, T=C+b take
    c = 1 on C, 1/2 on {a,b}, 0 elsewhere; the max of c over I is attained exactly on {S,T}.)
 2. Does the skeleton have EXTRA edges (pairs at Hamming distance >= 4 that are polytope-adjacent)?
    If yes for some I, NP applies to a supergraph of J(I) and does NOT give (Q).
A bad template K_2 v (K_p + K_q) is neither Hamilton-connected nor a hypercube, so for those the
skeleton MUST have extra edges.  The question is whether that is the only obstruction.
"""
from itertools import combinations
import numpy as np
from scipy.optimize import linprog

def gale_le(A,B): return all(a<=b for a,b in zip(A,B))
def adjacent(u,v): return len(set(u)^set(v))==2

def all_ideals(n,k,cap=4000):
    sets=[tuple(sorted(s)) for s in combinations(range(1,n+1),k)]
    below={S:frozenset(T for T in sets if gale_le(T,S)) for S in sets}
    seen={frozenset()}; fr=[frozenset()]
    while fr:
        nx=[]
        for I in fr:
            for S in sets:
                if S in I: continue
                J=I|below[S]
                if J not in seen:
                    seen.add(J); nx.append(J)
                    if len(seen)>cap: return None
        fr=nx
    return [I for I in seen if I]

def vec(S,n): 
    v=np.zeros(n); 
    for i in S: v[i-1]=1
    return v

def is_polytope_edge(I,S,T,n):
    """Segment ST is an edge of conv(I) iff the midpoint is NOT in conv(I - {S,T})."""
    others=[vec(U,n) for U in I if U not in (S,T)]
    if not others: return True
    mid=(vec(S,n)+vec(T,n))/2
    m=len(others)
    A_eq=np.vstack([np.array(others).T, np.ones((1,m))])
    b_eq=np.concatenate([mid,[1.0]])
    r=linprog(np.zeros(m),A_eq=A_eq,b_eq=b_eq,bounds=[(0,None)]*m,method='highs')
    return not r.success          # midpoint not representable => ST is an edge

def bad_pair(V):
    n=len(V)
    if n<4: return None
    nb={v:{w for w in V if w!=v and adjacent(v,w)} for v in V}
    univ=[v for v in V if len(nb[v])==n-1]
    if len(univ)!=2: return None
    a,b=univ; rest=[v for v in V if v not in (a,b)]
    radj={v:nb[v]&set(rest) for v in rest}
    comp,seen=[],set()
    for v in rest:
        if v in seen: continue
        c,st=set(),[v]
        while st:
            u=st.pop()
            if u in c: continue
            c.add(u); seen.add(u); st.extend(radj[u])
        comp.append(c)
    if len(comp)!=2: return None
    if not all(all(len(radj[v]&c)==len(c)-1 for v in c) for c in comp): return None
    return frozenset((a,b))

tot=0; d2notedge=0; extra=0; extra_bad=0; extra_good=[]
for n in range(3,7):
    for k in range(1,n):
        IS=all_ideals(n,k)
        if IS is None: print(f"  n={n} k={k} SKIPPED"); continue
        for I in IS:
            V=sorted(I)
            if len(V)<3: continue
            tot+=1
            isbad = bad_pair(tuple(V)) is not None
            ex=0
            for i,S in enumerate(V):
                for T in V[i+1:]:
                    e=is_polytope_edge(V,S,T,n)
                    if adjacent(S,T) and not e: d2notedge+=1
                    if (not adjacent(S,T)) and e: ex+=1
            if ex:
                extra+=1
                if isbad: extra_bad+=1
                elif len(extra_good)<5: extra_good.append((n,k,tuple(V),ex))
    print(f"  ... n={n} done ({tot} ideals)",flush=True)

print(f"\n=== is J(I) the skeleton of conv(I)? ===")
print(f"  Gale ideals with >=3 members            : {tot}")
print(f"  ★ Hamming-distance-2 pairs NOT edges    : {d2notedge}   (expect 0)")
print(f"  ideals whose skeleton has EXTRA edges   : {extra}")
print(f"     ... of which are bad templates       : {extra_bad}")
print(f"     ... NOT bad templates (fatal if >0)  : {extra-extra_bad}")
for g in extra_good: print(f"        n={g[0]} k={g[1]} extra={g[3]} I={g[2]}")
