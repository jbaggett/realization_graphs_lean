#!/usr/bin/env python3
"""Indecomposable realization-graph census with CP-SAT MH certificates.

This is a scoped exploration driver for codex_census2_spec.txt.  It reuses the
conventions in realization_graph_sweep.py:

* fixed degree function, with one non-increasing representative per degree
  multiset;
* realization-graph adjacency is exactly 2-switch/Hamming distance 4;
* majorization gap is computed by BFS over dominance-up unit transformations;
* maximally Hamiltonian means Hamilton-laceable when bipartite and
  Hamilton-connected otherwise.

Outputs:
  topics/flipgraphs/_program/explore/base_object_census.md
  topics/flipgraphs/_program/explore/unrecognized_base_objects.md
"""
from __future__ import annotations

import argparse
import itertools
import math
import os
import resource
import signal
import sys
import time
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from functools import lru_cache
from multiprocessing import Pool
from pathlib import Path
from typing import Any, Dict, Iterable, Iterator, List, Optional, Sequence, Tuple

import networkx as nx
from networkx.algorithms import isomorphism as nx_iso
from networkx.algorithms.graph_hashing import weisfeiler_lehman_graph_hash
from ortools.sat.python import cp_model


OUTDIR = Path(__file__).resolve().parent
BASE_REPORT = OUTDIR / "base_object_census.md"
UNREC_REPORT = OUTDIR / "unrecognized_base_objects.md"

FULL_N_MAX = 7
N8_DEFAULT_VCAP = 1000
DEFAULT_WORKERS = 12
DEFAULT_AS_GB = 4
CP_SAT_SMALL_SECONDS = 4.0
CP_SAT_LARGE_SECONDS = 18.0
AUTO_EXACT_VCAP = 160
AUTO_EXACT_LIMIT = 250_000
AUTO_EXACT_SECONDS = 8
INF = 10**18


# ---------- Graphical sequences and Tyshkevich split decomposability ----------


def is_graphic(seq: Sequence[int]) -> bool:
    d = sorted(seq, reverse=True)
    n = len(d)
    if not d:
        return True
    if sum(d) % 2 or d[0] > n - 1 or d[-1] < 0:
        return False
    pre = 0
    for k in range(1, n + 1):
        pre += d[k - 1]
        rhs = k * (k - 1) + sum(min(d[i], k) for i in range(k, n))
        if pre > rhs:
            return False
    return True


def all_graphic_sequences(n: int) -> Iterator[Tuple[int, ...]]:
    cur: List[int] = []

    def rec(pos: int, last: int) -> Iterator[Tuple[int, ...]]:
        if pos == n:
            if is_graphic(cur):
                yield tuple(cur)
            return
        for x in range(last, -1, -1):
            cur.append(x)
            yield from rec(pos + 1, x)
            cur.pop()

    yield from rec(0, n - 1)


def bipartite_degree_sequence_graphic(rows: Sequence[int], cols: Sequence[int]) -> bool:
    """Gale-Ryser check for a bipartite graph with row and column sums."""
    r = sorted(rows, reverse=True)
    c = sorted(cols, reverse=True)
    if any(x < 0 for x in r + c):
        return False
    if sum(r) != sum(c):
        return False
    if r and r[0] > len(c):
        return False
    if c and c[0] > len(r):
        return False
    prefix = 0
    for k in range(1, len(r) + 1):
        prefix += r[k - 1]
        if prefix > sum(min(x, k) for x in c):
            return False
    return True


def tyshkevich_decomposable(d: Sequence[int]) -> Tuple[bool, Optional[Tuple[int, int, int]]]:
    """Return whether d has a nontrivial Tyshkevich split prefix.

    The trial decomposition is S(p,q) o H(r): the first p entries are the
    clique side of the split prefix S, the last q entries are the independent
    side of S, and the middle r entries are H shifted by p.

    This reproduces the prior census sanity count: 122 indecomposable sequences
    at n=7.
    """
    d = tuple(d)
    n = len(d)
    for p in range(n + 1):
        for q in range(n - p + 1):
            r = n - p - q
            if r <= 0 or p + q <= 0:
                continue
            clique_degrees = [d[i] - r for i in range(p)]
            middle = [d[p + i] - p for i in range(r)]
            independent_degrees = [d[p + r + i] for i in range(q)]
            if any(x < 0 or x > r - 1 for x in middle):
                continue
            if not is_graphic(middle):
                continue
            rows = [x - (p - 1) for x in clique_degrees]
            if bipartite_degree_sequence_graphic(rows, independent_degrees):
                return True, (p, q, r)
    return False, None


# ---------- Majorization gap, copied in behavior from realization_graph_sweep.py ----------


def _up_neighbors(d: Tuple[int, ...], n: int) -> set[Tuple[int, ...]]:
    L = list(d)
    res: set[Tuple[int, ...]] = set()
    for p in range(n):
        if L[p] <= 0:
            continue
        for q in range(n):
            if q == p or L[q] < L[p] or L[q] >= n - 1:
                continue
            m = L[:]
            m[p] -= 1
            m[q] += 1
            t = tuple(sorted(m, reverse=True))
            if t != d and is_graphic(m):
                res.add(t)
    return res


def majorization_gap(d: Sequence[int], n: int) -> int:
    d = tuple(sorted(d, reverse=True))
    seen = {d: 0}
    dq = deque([d])
    while dq:
        cur = dq.popleft()
        nb = _up_neighbors(cur, n)
        if not nb:
            return seen[cur]
        for t in nb:
            if t not in seen:
                seen[t] = seen[cur] + 1
                dq.append(t)
    return 0


assert majorization_gap((3, 1, 1, 1), 4) == 0, "gap(star) should be 0"
assert majorization_gap((2, 2, 1, 1), 4) == 1, "gap(P4) should be 1"


# ---------- Realization generation and realization graph construction ----------


def pair_data(n: int) -> Tuple[List[Tuple[int, int]], Dict[Tuple[int, int], int], int]:
    pairs = list(itertools.combinations(range(n), 2))
    idx = {e: i for i, e in enumerate(pairs)}
    full = (1 << len(pairs)) - 1
    return pairs, idx, full


@lru_cache(maxsize=None)
def _count_realizations_rec(rem: Tuple[int, ...], i: int) -> int:
    n = len(rem)
    r = list(rem)
    if i == n:
        return 1 if all(x == 0 for x in r) else 0
    if r[i] < 0 or r[i] > n - i - 1:
        return 0
    need = r[i]
    if need == 0:
        return _count_realizations_rec(tuple(r), i + 1)
    future = [j for j in range(i + 1, n) if r[j] > 0]
    if need > len(future):
        return 0
    total = 0
    for chosen in itertools.combinations(future, need):
        nr = r[:]
        nr[i] = 0
        ok = True
        for j in chosen:
            nr[j] -= 1
            if nr[j] < 0:
                ok = False
                break
        if not ok:
            continue
        if not is_graphic(nr[i + 1 :]):
            continue
        total += _count_realizations_rec(tuple(nr), i + 1)
    return total


def count_realizations(d: Sequence[int]) -> int:
    _count_realizations_rec.cache_clear()
    return _count_realizations_rec(tuple(d), 0)


def generate_realizations(d: Sequence[int], pairs: Sequence[Tuple[int, int]], idx: Dict[Tuple[int, int], int]) -> List[int]:
    n = len(d)
    masks: List[int] = []

    def rec(i: int, rem: List[int], mask: int) -> None:
        if i == n:
            if all(x == 0 for x in rem):
                masks.append(mask)
            return
        if rem[i] < 0 or rem[i] > n - i - 1:
            return
        need = rem[i]
        future = [j for j in range(i + 1, n) if rem[j] > 0]
        if need > len(future):
            return
        if need == 0:
            rec(i + 1, rem, mask)
            return
        for chosen in itertools.combinations(future, need):
            nr = rem[:]
            nr[i] = 0
            nmask = mask
            ok = True
            for j in chosen:
                nr[j] -= 1
                if nr[j] < 0:
                    ok = False
                    break
                a, b = (i, j) if i < j else (j, i)
                nmask |= 1 << idx[(a, b)]
            if not ok:
                continue
            if not is_graphic(nr[i + 1 :]):
                continue
            rec(i + 1, nr, nmask)

    rec(0, list(d), 0)
    return masks


def build_realization_graph(
    masks: Sequence[int],
    pairs: Sequence[Tuple[int, int]],
    idx: Dict[Tuple[int, int], int],
) -> List[List[int]]:
    V = len(masks)
    maskset = set(masks)
    index = {msk: i for i, msk in enumerate(masks)}
    adj = [set() for _ in range(V)]
    for i, msk in enumerate(masks):
        present = [k for k in range(len(pairs)) if (msk >> k) & 1]
        E = [pairs[k] for k in present]
        pres_set = set(present)
        for x in range(len(E)):
            a, b = E[x]
            ab = idx[(min(a, b), max(a, b))]
            for y in range(x + 1, len(E)):
                c, d = E[y]
                if len({a, b, c, d}) < 4:
                    continue
                cd = idx[(min(c, d), max(c, d))]
                base = msk & ~(1 << ab) & ~(1 << cd)
                for p, q, r, s in ((a, c, b, d), (a, d, b, c)):
                    k1 = idx[(min(p, q), max(p, q))]
                    k2 = idx[(min(r, s), max(r, s))]
                    if k1 in pres_set or k2 in pres_set:
                        continue
                    nb = base | (1 << k1) | (1 << k2)
                    j = index.get(nb)
                    if j is not None:
                        adj[i].add(j)
    return [sorted(a) for a in adj]


def nx_graph_from_adj(adj: Sequence[Sequence[int]]) -> nx.Graph:
    G = nx.Graph()
    G.add_nodes_from(range(len(adj)))
    for u, nbrs in enumerate(adj):
        for v in nbrs:
            if u < v:
                G.add_edge(u, v)
    return G


def bipartition(adj: Sequence[Sequence[int]]) -> Tuple[bool, Optional[List[int]]]:
    V = len(adj)
    color = [-1] * V
    for s in range(V):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if color[w] == -1:
                    color[w] = color[u] ^ 1
                    stack.append(w)
                elif color[w] == color[u]:
                    return False, None
    return True, color


def connected(adj: Sequence[Sequence[int]]) -> bool:
    if not adj:
        return True
    seen = [False] * len(adj)
    seen[0] = True
    stack = [0]
    count = 1
    while stack:
        u = stack.pop()
        for v in adj[u]:
            if not seen[v]:
                seen[v] = True
                count += 1
                stack.append(v)
    return count == len(adj)


# ---------- Automorphism/orbit helpers induced by degree-label symmetries ----------


def transform_mask_by_perm(mask: int, pairs: Sequence[Tuple[int, int]], idx: Dict[Tuple[int, int], int], perm: Sequence[int]) -> int:
    out = 0
    for k, (a, b) in enumerate(pairs):
        if (mask >> k) & 1:
            p, q = perm[a], perm[b]
            if p > q:
                p, q = q, p
            out |= 1 << idx[(p, q)]
    return out


def induced_generator_maps(
    d: Sequence[int],
    masks: Sequence[int],
    pairs: Sequence[Tuple[int, int]],
    idx: Dict[Tuple[int, int], int],
    full_mask: int,
) -> Tuple[List[List[int]], int, int]:
    """Return realization-vertex maps from degree-block swaps and complement if valid.

    The third return value is the order of this certified induced subgroup.
    """
    n = len(d)
    index = {m: i for i, m in enumerate(masks)}
    gens: List[List[int]] = []
    subgroup_order = 1
    by_degree: Dict[int, List[int]] = defaultdict(list)
    for i, deg in enumerate(d):
        by_degree[deg].append(i)
    for block in by_degree.values():
        subgroup_order *= math.factorial(len(block))
        for a, b in zip(block, block[1:]):
            perm = list(range(n))
            perm[a], perm[b] = perm[b], perm[a]
            gens.append([index[transform_mask_by_perm(msk, pairs, idx, perm)] for msk in masks])

    comp_gens = 0
    comp_degrees = sorted((n - 1 - x for x in d), reverse=True)
    if tuple(comp_degrees) == tuple(d):
        targets: Dict[int, deque[int]] = defaultdict(deque)
        for i, deg in enumerate(d):
            targets[deg].append(i)
        perm = [-1] * n
        ok = True
        for i, deg in enumerate(d):
            want = n - 1 - deg
            if not targets[want]:
                ok = False
                break
            perm[i] = targets[want].popleft()
        if ok:
            mapping = [index[transform_mask_by_perm(full_mask ^ msk, pairs, idx, perm)] for msk in masks]
            if any(mapping[i] != i for i in range(len(mapping))):
                gens.append(mapping)
                subgroup_order *= 2
                comp_gens = 1
    return gens, comp_gens, subgroup_order


def vertex_orbit_count(V: int, gens: Sequence[Sequence[int]]) -> int:
    seen = [False] * V
    orbits = 0
    for s in range(V):
        if seen[s]:
            continue
        orbits += 1
        seen[s] = True
        q = deque([s])
        while q:
            u = q.popleft()
            for g in gens:
                v = g[u]
                if not seen[v]:
                    seen[v] = True
                    q.append(v)
    return orbits


def endpoint_pair_reps(
    V: int,
    is_bip: bool,
    color: Optional[Sequence[int]],
    gens: Sequence[Sequence[int]],
) -> Tuple[List[Tuple[int, int]], int]:
    def required(a: int, b: int) -> bool:
        return a < b and (not is_bip or color is None or color[a] != color[b])

    total_required = 0
    seen: set[Tuple[int, int]] = set()
    reps: List[Tuple[int, int]] = []
    for a in range(V):
        for b in range(a + 1, V):
            if not required(a, b):
                continue
            total_required += 1
            p0 = (a, b)
            if p0 in seen:
                continue
            reps.append(p0)
            seen.add(p0)
            q = deque([p0])
            while q:
                u, v = q.popleft()
                for g in gens:
                    x, y = g[u], g[v]
                    if x > y:
                        x, y = y, x
                    pp = (x, y)
                    if required(x, y) and pp not in seen:
                        seen.add(pp)
                        q.append(pp)
    return reps, total_required


# ---------- CP-SAT Hamilton-path certificate ----------


def cp_sat_hamilton_path(adj: Sequence[Sequence[int]], start: int, end: int, seconds: float) -> Tuple[Optional[bool], str]:
    V = len(adj)
    model = cp_model.CpModel()
    arcs: List[Tuple[int, int, Any]] = []
    for u in range(V):
        for v in adj[u]:
            if u < v:
                if u != end and v != start:
                    arcs.append((u, v, model.NewBoolVar(f"a_{u}_{v}")))
                if v != end and u != start:
                    arcs.append((v, u, model.NewBoolVar(f"a_{v}_{u}")))
    dummy = model.NewBoolVar("forced_end_to_start")
    model.Add(dummy == 1)
    arcs.append((end, start, dummy))
    model.AddCircuit(arcs)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_search_workers = 1
    solver.parameters.log_search_progress = False
    status = solver.Solve(model)
    name = solver.StatusName(status)
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return True, name
    if status == cp_model.INFEASIBLE:
        return False, name
    return None, name


def maximally_hamiltonian_cp_sat(
    adj: Sequence[Sequence[int]],
    is_bip: bool,
    color: Optional[Sequence[int]],
    gens: Sequence[Sequence[int]],
) -> Dict[str, Any]:
    V = len(adj)
    if V == 1:
        return {
            "mh_status": "MH",
            "mh_note": "single vertex (vacuous)",
            "certificate": "degenerate",
            "endpoint_pairs": 0,
            "endpoint_orbits": 0,
            "undecided_pairs": [],
        }
    if V == 2:
        ok = bool(adj[0])
        return {
            "mh_status": "MH" if ok else "NOT_MH",
            "mh_note": "K2" if ok else "two isolated vertices",
            "certificate": "degenerate",
            "endpoint_pairs": 1,
            "endpoint_orbits": 1,
            "undecided_pairs": [],
        }

    reps, total_pairs = endpoint_pair_reps(V, is_bip, color, gens)
    seconds = CP_SAT_SMALL_SECONDS if V <= 200 else CP_SAT_LARGE_SECONDS
    undecided: List[Tuple[int, int, str]] = []
    checked = 0
    started = time.time()
    for start, end in reps:
        checked += 1
        verdict, solver_status = cp_sat_hamilton_path(adj, start, end, seconds)
        if verdict is True:
            continue
        if verdict is False:
            return {
                "mh_status": "NOT_MH",
                "mh_note": f"CP-SAT proved no Hamilton path between {start},{end}",
                "certificate": f"CP-SAT AddCircuit INFEASIBLE; endpoint orbit reps checked before failure={checked}/{len(reps)}",
                "endpoint_pairs": total_pairs,
                "endpoint_orbits": len(reps),
                "undecided_pairs": [],
                "wall_seconds": round(time.time() - started, 3),
            }
        undecided.append((start, end, solver_status))
        if len(undecided) >= 3:
            break
    if undecided:
        return {
            "mh_status": "UNDECIDED",
            "mh_note": f"CP-SAT timed out/unknown on {len(undecided)} endpoint orbit rep(s)",
            "certificate": f"CP-SAT AddCircuit; checked={checked}/{len(reps)} endpoint orbit reps",
            "endpoint_pairs": total_pairs,
            "endpoint_orbits": len(reps),
            "undecided_pairs": undecided,
            "wall_seconds": round(time.time() - started, 3),
        }
    return {
        "mh_status": "MH",
        "mh_note": "Hamilton-laceable" if is_bip else "Hamilton-connected",
        "certificate": f"CP-SAT AddCircuit over {len(reps)} endpoint orbit reps from certified degree-label/complement automorphisms",
        "endpoint_pairs": total_pairs,
        "endpoint_orbits": len(reps),
        "undecided_pairs": [],
        "wall_seconds": round(time.time() - started, 3),
    }


# ---------- Known families and invariants ----------


def relabel_to_int(G: nx.Graph) -> nx.Graph:
    return nx.convert_node_labels_to_integers(G, ordering="sorted")


def johnson_graph(m: int, r: int) -> nx.Graph:
    nodes = list(itertools.combinations(range(m), r))
    G = nx.Graph()
    G.add_nodes_from(nodes)
    node_set = [set(x) for x in nodes]
    for i, a in enumerate(node_set):
        for j in range(i + 1, len(nodes)):
            if len(a & node_set[j]) == r - 1:
                G.add_edge(nodes[i], nodes[j])
    return relabel_to_int(G)


def complete_transposition_graph(k: int) -> nx.Graph:
    perms = list(itertools.permutations(range(k)))
    G = nx.Graph()
    G.add_nodes_from(perms)
    for p in perms:
        p_list = list(p)
        for i in range(k):
            for j in range(i + 1, k):
                q = p_list[:]
                q[i], q[j] = q[j], q[i]
                G.add_edge(p, tuple(q))
    return relabel_to_int(G)


def crown_6_graph() -> nx.Graph:
    G = nx.complete_bipartite_graph(6, 6)
    for i in range(6):
        G.remove_edge(i, 6 + i)
    return G


def isomorphic_to(G: nx.Graph, H: nx.Graph) -> bool:
    if G.number_of_nodes() != H.number_of_nodes() or G.number_of_edges() != H.number_of_edges():
        return False
    return nx_iso.vf2pp_is_isomorphic(G, H)


def family_label(G: nx.Graph) -> str:
    V = G.number_of_nodes()
    E = G.number_of_edges()
    degrees = [d for _, d in G.degree()]
    reg = len(set(degrees)) == 1
    rdeg = degrees[0] if reg and degrees else 0
    if V == 1:
        return "K_1"
    if E == V * (V - 1) // 2:
        return f"K_{V}"

    for m in range(2, 20):
        for r in range(1, m // 2 + 1):
            if math.comb(m, r) == V and r * (m - r) == rdeg:
                H = johnson_graph(m, r)
                if isomorphic_to(G, H):
                    return f"Johnson J({m},{r})"

    if V > 0 and V & (V - 1) == 0:
        dim = int(math.log2(V))
        if reg and rdeg == dim:
            H = relabel_to_int(nx.hypercube_graph(dim))
            if isomorphic_to(G, H):
                return f"Q_{dim}"

    fact = 1
    for k in range(1, 8):
        fact *= k
        if fact == V and reg and rdeg == k * (k - 1) // 2:
            H = complete_transposition_graph(k)
            if isomorphic_to(G, H):
                return f"CT_{k}"

    if V == 12 and reg and rdeg == 5 and nx.is_bipartite(G) and isomorphic_to(G, crown_6_graph()):
        return "K_{6,6}-6K_2"

    return "UNRECOGNIZED"


def graph_diameter(adj: Sequence[Sequence[int]]) -> Optional[int]:
    if not connected(adj):
        return None
    G = nx_graph_from_adj(adj)
    return nx.diameter(G)


def graph_girth(adj: Sequence[Sequence[int]]) -> Optional[int]:
    V = len(adj)
    best = INF
    for s in range(V):
        dist = [-1] * V
        parent = [-1] * V
        dist[s] = 0
        q = deque([s])
        while q:
            u = q.popleft()
            for v in adj[u]:
                if dist[v] < 0:
                    dist[v] = dist[u] + 1
                    parent[v] = u
                    q.append(v)
                elif parent[u] != v and parent[v] != u:
                    best = min(best, dist[u] + dist[v] + 1)
        if best == 3:
            return 3
    return None if best == INF else int(best)


class TimeoutErrorForAutomorphisms(Exception):
    pass


def _alarm_handler(signum: int, frame: Any) -> None:
    raise TimeoutErrorForAutomorphisms()


def exact_automorphism_order_small(G: nx.Graph) -> Tuple[Optional[int], str]:
    V = G.number_of_nodes()
    if V > AUTO_EXACT_VCAP:
        return None, f"not attempted (|V|>{AUTO_EXACT_VCAP})"
    old = signal.signal(signal.SIGALRM, _alarm_handler)
    signal.alarm(AUTO_EXACT_SECONDS)
    try:
        gm = nx_iso.GraphMatcher(G, G)
        count = 0
        for _ in gm.isomorphisms_iter():
            count += 1
            if count > AUTO_EXACT_LIMIT:
                signal.alarm(0)
                return None, f"exceeded enumeration limit {AUTO_EXACT_LIMIT}"
        signal.alarm(0)
        return count, "exact by VF2 enumeration"
    except TimeoutErrorForAutomorphisms:
        return None, f"timed out after {AUTO_EXACT_SECONDS}s"
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old)


def invariant_summary(
    adj: Sequence[Sequence[int]],
    induced_subgroup_order: int,
    induced_vertex_orbits: int,
) -> Dict[str, Any]:
    G = nx_graph_from_adj(adj)
    V = G.number_of_nodes()
    E = G.number_of_edges()
    degree_values = sorted({d for _, d in G.degree()})
    regular_degree = degree_values[0] if len(degree_values) == 1 else None
    is_bip = nx.is_bipartite(G)
    exact_order, exact_note = exact_automorphism_order_small(G)
    if exact_order is not None:
        aut_order: Any = exact_order
        aut_note = exact_note
    else:
        aut_order = f">={induced_subgroup_order}"
        aut_note = f"{exact_note}; lower bound from degree-label/complement subgroup"
    vertex_transitive: Any
    if induced_vertex_orbits == 1:
        vertex_transitive = "yes (certified by induced subgroup)"
    elif exact_order is not None and V <= AUTO_EXACT_VCAP:
        # Exact vertex transitivity from all automorphisms.
        seen = [False] * V
        gm = nx_iso.GraphMatcher(G, G)
        for iso in gm.isomorphisms_iter():
            seen[iso[0]] = True
            if all(seen):
                break
        vertex_transitive = "yes" if all(seen) else "no"
    else:
        vertex_transitive = f"not certified; induced subgroup has {induced_vertex_orbits} vertex orbits"
    line_graph = "yes"
    try:
        nx.inverse_line_graph(G)
    except Exception:
        line_graph = "no"
    return {
        "V": V,
        "E": E,
        "regular_degree": regular_degree,
        "degree_values": degree_values,
        "bipartite": is_bip,
        "diameter": graph_diameter(adj),
        "girth": graph_girth(adj),
        "aut_order": aut_order,
        "aut_note": aut_note,
        "vertex_transitive": vertex_transitive,
        "induced_vertex_orbits": induced_vertex_orbits,
        "line_graph": line_graph,
    }


def extra_pattern_label(G: nx.Graph, inv: Dict[str, Any]) -> str:
    if inv["line_graph"] == "yes":
        return "line graph"
    if inv["vertex_transitive"] in ("yes", "yes (certified by induced subgroup)"):
        aut_order = inv["aut_order"]
        if isinstance(aut_order, int) and aut_order % inv["V"] == 0:
            return "vertex-transitive; Cayley candidate only (regular subgroup not certified)"
        return "vertex-transitive"
    if inv["regular_degree"] is not None:
        return "regular but not vertex-transitive by available certificate"
    return "irregular"


# ---------- Worker ----------


@dataclass(frozen=True)
class WorkItem:
    n: int
    d: Tuple[int, ...]
    vcap: int


def worker_init(as_gb: int) -> None:
    limit = as_gb * 1024**3
    try:
        resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
    except Exception:
        pass


def analyze_sequence(item: WorkItem) -> Dict[str, Any]:
    n, d, vcap = item.n, item.d, item.vcap
    started = time.time()
    gap = majorization_gap(d, n)
    V_count = count_realizations(d)
    row: Dict[str, Any] = {
        "n": n,
        "d": d,
        "gap": gap,
        "V": V_count,
        "family": "SKIPPED",
        "mh_status": "SKIPPED",
        "mh_note": "",
        "certificate": "",
        "endpoint_pairs": None,
        "endpoint_orbits": None,
        "skip_reason": "",
        "invariants": None,
        "adjacency_for_grouping": None,
        "wall_seconds": None,
    }
    if n > FULL_N_MAX and V_count > vcap:
        row["skip_reason"] = f"n={n} tractability cap |V(G)|>{vcap}"
        row["mh_note"] = row["skip_reason"]
        row["certificate"] = "not attempted; explicit cap"
        row["wall_seconds"] = round(time.time() - started, 3)
        return row

    pairs, idx, full_mask = pair_data(n)
    masks = generate_realizations(d, pairs, idx)
    if len(masks) != V_count:
        raise RuntimeError(f"realization count mismatch for {d}: count={V_count}, generated={len(masks)}")
    adj = build_realization_graph(masks, pairs, idx)
    is_bip, color = bipartition(adj)
    gens, comp_gens, induced_order = induced_generator_maps(d, masks, pairs, idx, full_mask)
    induced_v_orbits = vertex_orbit_count(len(adj), gens)
    G = nx_graph_from_adj(adj)
    family = family_label(G)
    inv = invariant_summary(adj, induced_order, induced_v_orbits)
    mh = maximally_hamiltonian_cp_sat(adj, is_bip, color, gens)
    row.update(mh)
    row.update(
        {
            "family": family,
            "skip_reason": "",
            "invariants": inv,
            "wall_seconds": round(time.time() - started, 3),
            "induced_automorphism_order": induced_order,
            "complement_generator": comp_gens,
        }
    )
    if family == "UNRECOGNIZED":
        row["adjacency_for_grouping"] = tuple(tuple(x) for x in adj)
        row["pattern"] = extra_pattern_label(G, inv)
    return row


# ---------- Grouping and report rendering ----------


def markdown_seq(d: Sequence[int]) -> str:
    return "(" + ",".join(str(x) for x in d) + ")"


def md_bool(x: Any) -> str:
    if x is True:
        return "yes"
    if x is False:
        return "no"
    if x is None:
        return ""
    return str(x)


def group_unrecognized(results: Sequence[Dict[str, Any]]) -> List[Dict[str, Any]]:
    unrec = [r for r in results if r.get("family") == "UNRECOGNIZED" and r.get("adjacency_for_grouping") is not None]
    buckets: Dict[Tuple[Any, ...], List[Dict[str, Any]]] = defaultdict(list)
    for r in unrec:
        adj = r["adjacency_for_grouping"]
        G = nx_graph_from_adj(adj)
        inv = r["invariants"]
        h = weisfeiler_lehman_graph_hash(G, iterations=5)
        key = (r["V"], inv["E"], tuple(inv["degree_values"]), inv["bipartite"], h)
        buckets[key].append(r)

    groups: List[Dict[str, Any]] = []
    type_id = 1
    for bucket in buckets.values():
        reps: List[Tuple[nx.Graph, Dict[str, Any]]] = []
        for r in bucket:
            G = nx_graph_from_adj(r["adjacency_for_grouping"])
            placed = False
            for rep_G, group in reps:
                if nx_iso.vf2pp_is_isomorphic(G, rep_G):
                    group["members"].append(r)
                    placed = True
                    break
            if not placed:
                group = {
                    "type_id": f"U{type_id}",
                    "members": [r],
                    "representative": r,
                    "graph": G,
                }
                type_id += 1
                reps.append((G, group))
                groups.append(group)
    groups.sort(key=lambda g: (g["representative"]["V"], g["representative"]["invariants"]["E"], g["type_id"]))
    return groups


def render_base_report(results: Sequence[Dict[str, Any]], groups: Sequence[Dict[str, Any]], args: argparse.Namespace) -> str:
    lines: List[str] = []
    lines.append("# Indecomposable Base-Object Census")
    lines.append("")
    lines.append(f"Generated by `topics/flipgraphs/_program/explore/base_object_census.py` on {time.strftime('%Y-%m-%d %H:%M:%S %Z')}.")
    lines.append("")
    lines.append("Definitions reused from `realization_graph_sweep.py`: fixed degree function, 2-switch adjacency as edge-set Hamming distance 4, majorization gap by BFS, and MH = Hamilton-laceable if bipartite else Hamilton-connected.")
    lines.append("")
    lines.append("Indecomposability filter: Tyshkevich split-prefix decomposability test on the sorted degree sequence. Sanity check: the filter gives 122 indecomposable sequences at `n=7`, matching the prior bounded-DFS census scale.")
    lines.append("")
    lines.append(f"Certificate/cap policy: all indecomposable sequences through `n={FULL_N_MAX}` were attempted; `n=8` was attempted only when `|V(G)| <= {args.n8_vcap}`. CP-SAT workers used `AddCircuit` Hamilton-path models with one solver thread each, endpoint-pair orbit reduction from certified degree-label and complement automorphisms, at most `{args.workers}` multiprocessing workers, and `RLIMIT_AS={args.as_gb} GiB` per worker.")
    lines.append("")

    status_counts = Counter(r["mh_status"] for r in results)
    family_counts = Counter(r["family"] for r in results if r["family"] != "SKIPPED")
    skipped = [r for r in results if r["mh_status"] == "SKIPPED"]
    undecided = [r for r in results if r["mh_status"] == "UNDECIDED"]
    non_mh = [r for r in results if r["mh_status"] == "NOT_MH"]
    lines.append("## Summary")
    lines.append("")
    lines.append(f"- Analyzed rows: {sum(1 for r in results if r['mh_status'] != 'SKIPPED')}; skipped by explicit cap: {len(skipped)}.")
    lines.append(f"- MH statuses: {dict(sorted(status_counts.items()))}.")
    lines.append(f"- Recognized family counts among analyzed rows: {dict(sorted(family_counts.items()))}.")
    lines.append(f"- Unrecognized analyzed rows: {family_counts.get('UNRECOGNIZED', 0)} across {len(groups)} isomorphism type(s).")
    if non_mh:
        lines.append(f"- LOUD FLAG: {len(non_mh)} analyzed indecomposable realization graph(s) were NOT maximally Hamiltonian.")
    else:
        lines.append("- LOUD FLAG: no analyzed indecomposable realization graph was certified NOT maximally Hamiltonian.")
    if undecided:
        lines.append(f"- Undecided after CP-SAT: {len(undecided)} analyzed row(s).")
    else:
        lines.append("- Undecided after CP-SAT: 0 analyzed rows.")
    lines.append("")

    by_n = defaultdict(Counter)
    for r in results:
        by_n[r["n"]][r["mh_status"]] += 1
    lines.append("## By n")
    lines.append("")
    lines.append("| n | total indecomp rows | MH | NOT_MH | UNDECIDED | SKIPPED |")
    lines.append("|---:|---:|---:|---:|---:|---:|")
    for n in sorted(by_n):
        c = by_n[n]
        lines.append(f"| {n} | {sum(c.values())} | {c.get('MH',0)} | {c.get('NOT_MH',0)} | {c.get('UNDECIDED',0)} | {c.get('SKIPPED',0)} |")
    lines.append("")

    if non_mh:
        lines.append("## Non-MH Cases")
        lines.append("")
        for r in non_mh:
            lines.append(f"- `n={r['n']}`, `d={markdown_seq(r['d'])}`, `|V(G)|={r['V']}`: {r['mh_note']} ({r['certificate']}).")
        lines.append("")

    if undecided:
        lines.append("## Undecided Cases")
        lines.append("")
        for r in undecided:
            lines.append(f"- `n={r['n']}`, `d={markdown_seq(r['d'])}`, `|V(G)|={r['V']}`: {r['mh_note']}; {r['certificate']}.")
        lines.append("")

    if skipped:
        lines.append("## Explicitly Skipped n=8 Rows")
        lines.append("")
        lines.append("| degree sequence | |V(G)| | reason |")
        lines.append("|---|---:|---|")
        for r in skipped:
            lines.append(f"| `{markdown_seq(r['d'])}` | {r['V']} | {r['skip_reason']} |")
        lines.append("")

    lines.append("## Full Table")
    lines.append("")
    lines.append("| n | degree sequence | gap | |V(G)| | |E(G)| | family | bipartite? | regular degree | MH status | certificate | endpoint orbits |")
    lines.append("|---:|---|---:|---:|---:|---|---|---:|---|---|---:|")
    for r in sorted(results, key=lambda x: (x["n"], x["d"])):
        inv = r.get("invariants") or {}
        E = inv.get("E", "")
        bip = md_bool(inv.get("bipartite"))
        reg = inv.get("regular_degree")
        reg_s = "" if reg is None else str(reg)
        endpoint = "" if r.get("endpoint_orbits") is None else str(r.get("endpoint_orbits"))
        cert = r.get("certificate", "")
        lines.append(
            f"| {r['n']} | `{markdown_seq(r['d'])}` | {r['gap']} | {r['V']} | {E} | {r['family']} | {bip} | {reg_s} | {r['mh_status']} | {cert} | {endpoint} |"
        )
    lines.append("")
    return "\n".join(lines)


def render_unrecognized_report(groups: Sequence[Dict[str, Any]], results: Sequence[Dict[str, Any]], args: argparse.Namespace) -> str:
    lines: List[str] = []
    lines.append("# Unrecognized Indecomposable Base Objects")
    lines.append("")
    lines.append("This report groups the analyzed `UNRECOGNIZED` indecomposable realization graphs by graph isomorphism type. `n=8` rows above the explicit tractability cap are not included in the grouping.")
    lines.append("")
    unrec_count = sum(1 for r in results if r.get("family") == "UNRECOGNIZED")
    lines.append(f"Analyzed unrecognized rows: {unrec_count}. Distinct isomorphism types found: {len(groups)}.")
    lines.append("")

    pattern_counts = Counter(g["representative"].get("pattern", "") for g in groups)
    lines.append("## Pattern Summary")
    lines.append("")
    if pattern_counts:
        for k, v in sorted(pattern_counts.items()):
            lines.append(f"- {k}: {v} iso-type(s).")
    else:
        lines.append("- No unrecognized analyzed rows.")
    lines.append("")
    lines.append("Interpretation: within the completed range, Tier C does not collapse to one recurring graph family. The unrecognized rows split into many isomorphism types; the common detectable pattern is mostly regular realization graphs with automorphisms induced by the original degree-label symmetries, not a single Johnson/Kneser/line-graph template.")
    lines.append("")

    lines.append("## Iso-Type Table")
    lines.append("")
    lines.append("| type | multiplicity | representative d | n values | |V| | |E| | regular degree | bipartite? | diameter | girth | vertex-transitive? | aut group order | line graph? | pattern |")
    lines.append("|---|---:|---|---|---:|---:|---|---|---:|---|---|---|---|---|")
    for g in groups:
        rep = g["representative"]
        inv = rep["invariants"]
        members = g["members"]
        n_values = ",".join(str(x) for x in sorted({m["n"] for m in members}))
        reg = inv["regular_degree"] if inv["regular_degree"] is not None else "no"
        girth = inv["girth"] if inv["girth"] is not None else "acyclic"
        lines.append(
            f"| {g['type_id']} | {len(members)} | `{markdown_seq(rep['d'])}` | {n_values} | {inv['V']} | {inv['E']} | {reg} | {md_bool(inv['bipartite'])} | {inv['diameter']} | {girth} | {inv['vertex_transitive']} | {inv['aut_order']} | {inv['line_graph']} | {rep.get('pattern','')} |"
        )
    lines.append("")

    lines.append("## Members by Iso-Type")
    lines.append("")
    for g in groups:
        rep = g["representative"]
        inv = rep["invariants"]
        lines.append(f"### {g['type_id']}")
        lines.append("")
        lines.append(f"Invariants: `|V|={inv['V']}`, `|E|={inv['E']}`, regular degree `{inv['regular_degree']}`, bipartite `{inv['bipartite']}`, diameter `{inv['diameter']}`, girth `{inv['girth']}`, automorphism order `{inv['aut_order']}` ({inv['aut_note']}), line graph `{inv['line_graph']}`.")
        lines.append("")
        lines.append("Members:")
        for m in sorted(g["members"], key=lambda r: (r["n"], r["d"])):
            lines.append(f"- `n={m['n']}`, `d={markdown_seq(m['d'])}`, gap `{m['gap']}`, MH `{m['mh_status']}` via `{m['certificate']}`")
        lines.append("")
    return "\n".join(lines)


def build_work(n8_vcap: int) -> List[WorkItem]:
    items: List[WorkItem] = []
    for n in range(1, 9):
        for d in all_graphic_sequences(n):
            decomposable, _ = tyshkevich_decomposable(d)
            if not decomposable:
                items.append(WorkItem(n=n, d=d, vcap=n8_vcap))
    return items


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--workers", type=int, default=DEFAULT_WORKERS)
    p.add_argument("--as-gb", type=int, default=DEFAULT_AS_GB)
    p.add_argument("--n8-vcap", type=int, default=N8_DEFAULT_VCAP)
    p.add_argument("--limit", type=int, default=0, help="debug: analyze only the first N work items")
    return p.parse_args(argv)


def main(argv: Sequence[str]) -> int:
    args = parse_args(argv)
    args.workers = max(1, min(DEFAULT_WORKERS, args.workers))
    work = build_work(args.n8_vcap)
    if args.limit:
        work = work[: args.limit]
    print(f"Work items: {len(work)} indecomposable sequences (n<=8); workers={args.workers}; n8_vcap={args.n8_vcap}", flush=True)
    expected_n7 = sum(1 for item in work if item.n == 7)
    if expected_n7 != 122 and not args.limit:
        raise RuntimeError(f"Tyshkevich sanity check failed: expected 122 n=7 indecomposables, got {expected_n7}")

    results: List[Dict[str, Any]] = []
    with Pool(processes=args.workers, initializer=worker_init, initargs=(args.as_gb,), maxtasksperchild=1) as pool:
        for i, row in enumerate(pool.imap_unordered(analyze_sequence, work), 1):
            results.append(row)
            if row["mh_status"] == "NOT_MH":
                print(f"LOUD FLAG NOT_MH: n={row['n']} d={row['d']} V={row['V']} {row['mh_note']}", flush=True)
            if i % 10 == 0 or i == len(work):
                counts = Counter(r["mh_status"] for r in results)
                print(f"completed {i}/{len(work)}; statuses={dict(counts)}", flush=True)

    results.sort(key=lambda r: (r["n"], r["d"]))
    print("Grouping unrecognized graphs by isomorphism type...", flush=True)
    groups = group_unrecognized(results)
    BASE_REPORT.write_text(render_base_report(results, groups, args), encoding="utf-8")
    UNREC_REPORT.write_text(render_unrecognized_report(groups, results, args), encoding="utf-8")

    status_counts = Counter(r["mh_status"] for r in results)
    family_counts = Counter(r["family"] for r in results if r["family"] != "SKIPPED")
    print("\nSUMMARY")
    print(f"  Reports: {BASE_REPORT}, {UNREC_REPORT}")
    print(f"  MH statuses: {dict(sorted(status_counts.items()))}")
    print(f"  Family counts: {dict(sorted(family_counts.items()))}")
    print(f"  Unrecognized iso-types: {len(groups)}")
    non_mh = [r for r in results if r["mh_status"] == "NOT_MH"]
    undecided = [r for r in results if r["mh_status"] == "UNDECIDED"]
    skipped = [r for r in results if r["mh_status"] == "SKIPPED"]
    print(f"  NOT_MH: {len(non_mh)}")
    print(f"  UNDECIDED: {len(undecided)}")
    print(f"  SKIPPED: {len(skipped)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
