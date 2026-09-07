#!/usr/bin/env python3
"""Independent exact (SB+) search for ground orders 9 and 10.

This implementation is deliberately self-contained.  It does not import any
repository module and does not use the earlier sbplus/qstar search programs.
"""

from __future__ import annotations

import argparse
import itertools
import json
import time
from collections import Counter, deque
from functools import lru_cache

# ---------------------------------------------------------------------------
# ⚠ MAIN-LINE FILTER CORRECTED 2026-08-18.  This sweep used a proper Erdos-Gallai equality as its
# Tyshkevich-decomposability test.  That is not one: P4 = (2,2,1,1) is INDECOMPOSABLE and has an
# equality at k=2, and (1,1,1,1,0) is DECOMPOSABLE with none.  Under the other main-line hypotheses
# the error is one-sided and costs coverage -- 26 of the 161 main-line sequences through order 7 are
# indecomposable yet carry an equality, so the old filter SKIPPED 16% of the main line.  The test
# below is from the DEFINITION.  See results/2026-08-18_tyshkevich_not_equivalent_to_eg.md.
#
# Kept self-contained, per this file's own design note that it imports no repository module.
# ---------------------------------------------------------------------------

def _hh_realization(d):
    """One realization by Havel-Hakimi, or None if the sequence is not graphical."""
    n = len(d)
    adj = [[False] * n for _ in range(n)]
    rem = list(d)
    for _ in range(n):
        order = sorted(range(n), key=lambda v: -rem[v])
        v = order[0]
        k = rem[v]
        if k == 0:
            break
        picks = [u for u in order[1:] if rem[u] > 0][:k]
        if len(picks) < k:
            return None
        for u in picks:
            if adj[v][u]:
                return None
            adj[v][u] = adj[u][v] = True
            rem[u] -= 1
        rem[v] = 0
    return adj

def tyshkevich_decomposable_seq(d):
    """From the DEFINITION, not the Erdos-Gallai criterion -- the two are not equivalent.

    Decomposability depends only on the degree sequence (Tyshkevich), so one realization answers;
    verified to 0 disagreements through order 7.
    """
    n = len(d)
    adj = _hh_realization(tuple(d))
    if adj is None:
        return False
    for cmask in range(1, (1 << n) - 1):
        C = [v for v in range(n) if cmask >> v & 1]
        rest = [v for v in range(n) if not (cmask >> v & 1)]
        A, B, ok = [], [], True
        for v in rest:
            if all(adj[v][c] for c in C):
                A.append(v)
            elif all(not adj[v][c] for c in C):
                B.append(v)
            else:
                ok = False
                break
        if not ok:
            continue
        if any(not adj[u][w] for u, w in itertools.combinations(A, 2)):
            continue
        if any(adj[u][w] for u, w in itertools.combinations(B, 2)):
            continue
        return True
    return False



@lru_cache(maxsize=None)
def graphical(seq: tuple[int, ...]) -> bool:
    d = tuple(sorted(seq, reverse=True))
    n = len(d)
    if any(x < 0 or x >= n for x in d) or sum(d) % 2:
        return False
    prefix = 0
    for k, x in enumerate(d, 1):
        prefix += x
        if prefix > k * (k - 1) + sum(min(k, y) for y in d[k:]):
            return False
    return True


def canonical_sequences(n: int):
    for asc in itertools.combinations_with_replacement(range(n), n):
        d = tuple(reversed(asc))
        if graphical(d):
            yield d


def proper_eg_equality(d: tuple[int, ...]) -> bool:
    prefix = 0
    for k in range(1, len(d)):
        prefix += d[k - 1]
        if prefix == k * (k - 1) + sum(min(k, x) for x in d[k:]):
            return True
    return False


def pivot_family(d: tuple[int, ...], pivot: int) -> tuple[tuple[int, ...], frozenset[int]]:
    order = tuple(v for v in range(len(d)) if v != pivot)
    k = d[pivot]
    if not 0 <= k <= len(order):
        return order, frozenset()
    family: set[int] = set()
    for chosen in itertools.combinations(range(len(order)), k):
        posmask = sum(1 << i for i in chosen)
        residual = [d[v] - ((posmask >> i) & 1) for i, v in enumerate(order)]
        if graphical(tuple(sorted(residual, reverse=True))):
            family.add(posmask)
    return order, frozenset(family)


def hook_universal_pair(
    order: tuple[int, ...], family: frozenset[int], k: int
) -> tuple[int, int] | None:
    m = len(order)
    if k < 2 or k + 2 > m:
        return None
    m1 = (1 << k) - 1
    m2 = (1 << (k - 1)) - 1 | (1 << k)
    pencil = {
        (1 << (k - 1)) - 1 | (1 << j): j for j in range(k + 1, m)
    }
    coatom = {
        ((1 << (k + 1)) - 1) ^ (1 << i): i for i in range(k - 1)
    }
    p_positions = sorted(pencil[x] for x in family if x in pencil)
    q_positions = sorted(coatom[x] for x in family if x in coatom)
    allowed = {m1, m2} | set(pencil) | set(coatom)
    if not p_positions or not q_positions or not family <= allowed:
        return None
    if p_positions != list(range(k + 1, max(p_positions) + 1)):
        return None
    if q_positions != list(range(min(q_positions), k - 1)):
        return None
    expected = {m1, m2}
    expected.update(x for x, j in pencil.items() if j <= max(p_positions))
    expected.update(x for x, i in coatom.items() if i >= min(q_positions))
    if family != expected:
        return None

    def actual(posmask: int) -> int:
        return sum(1 << order[i] for i in range(m) if (posmask >> i) & 1)

    return actual(m1), actual(m2)


@lru_cache(maxsize=None)
def edge_data(n: int):
    index = [[-1] * n for _ in range(n)]
    edges = []
    for i in range(n):
        for j in range(i + 1, n):
            index[i][j] = index[j][i] = len(edges)
            edges.append((i, j))
    quartets = []
    for a, b, c, d in itertools.combinations(range(n), 4):
        pairs = (((a, b), (c, d)), ((a, c), (b, d)), ((a, d), (b, c)))
        quartets.append(
            tuple((1 << index[x][y]) | (1 << index[z][w]) for (x, y), (z, w) in pairs)
        )
    return tuple(edges), tuple(tuple(row) for row in index), tuple(quartets)


@lru_cache(maxsize=None)
def realizations(degree_tuple: tuple[int, ...]) -> tuple[int, ...]:
    d0 = tuple(degree_tuple)
    n = len(d0)
    if not graphical(tuple(sorted(d0, reverse=True))):
        return tuple()
    _, edge_index, _ = edge_data(n)
    output: list[int] = []

    def visit(deg: tuple[int, ...], mask: int) -> None:
        positive = [v for v, x in enumerate(deg) if x]
        if not positive:
            output.append(mask)
            return
        v = min(positive, key=lambda x: (-deg[x], x))
        need = deg[v]
        candidates = [w for w in positive if w != v]
        if need > len(candidates):
            return
        for nbrs in itertools.combinations(candidates, need):
            nxt = list(deg)
            nxt[v] = 0
            added = 0
            ok = True
            for w in nbrs:
                nxt[w] -= 1
                if nxt[w] < 0:
                    ok = False
                    break
                added |= 1 << edge_index[v][w]
            if ok and graphical(tuple(sorted(nxt, reverse=True))):
                visit(tuple(nxt), mask | added)

    visit(d0, 0)
    return tuple(output)


@lru_cache(maxsize=None)
def realization_graph_nonbipartite(canonical_degree_tuple: tuple[int, ...]) -> bool:
    seq = tuple(sorted(canonical_degree_tuple, reverse=True))
    graphs = realizations(seq)
    if len(graphs) < 3:
        return False
    graph_set = set(graphs)
    _, _, quartets = edge_data(len(seq))
    colour: dict[int, int] = {}
    for root in graphs:
        if root in colour:
            continue
        colour[root] = 0
        queue = deque([root])
        while queue:
            g = queue.popleft()
            for matchings in quartets:
                for present in matchings:
                    if g & present != present:
                        continue
                    for absent in matchings:
                        if absent == present or g & absent:
                            continue
                        h = g ^ present ^ absent
                        if h not in graph_set:
                            raise AssertionError("2-switch escaped realization class")
                        if h not in colour:
                            colour[h] = colour[g] ^ 1
                            queue.append(h)
                        elif colour[h] == colour[g]:
                            return True
    return False


def neighbourhoods(graphs: tuple[int, ...], n: int) -> tuple[tuple[int, ...], ...]:
    edges, _, _ = edge_data(n)
    rows = []
    for g in graphs:
        ng = [0] * n
        for bit, (u, v) in enumerate(edges):
            if (g >> bit) & 1:
                ng[u] |= 1 << v
                ng[v] |= 1 << u
        rows.append(tuple(ng))
    return tuple(rows)


def residual_sequence(d: tuple[int, ...], pivot: int, actual_neighbours: int) -> tuple[int, ...]:
    return tuple(
        sorted(
            (d[v] - ((actual_neighbours >> v) & 1) for v in range(len(d)) if v != pivot),
            reverse=True,
        )
    )


def audit_order(n: int) -> dict:
    started = time.monotonic()
    stats = Counter()
    histogram = Counter()
    violations = []
    minimum_spares = None

    for d in canonical_sequences(n):
        stats["graphical_sequences"] += 1
        families = []
        hooks = []
        for v in range(n):
            order, family = pivot_family(d, v)
            families.append((order, family))
            hooks.append(hook_universal_pair(order, family, d[v]))
        if not any(hooks):
            continue
        stats["hook_sequences"] += 1
        stats["hook_pivots"] += sum(h is not None for h in hooks)

        if any(len(family) < 2 for _, family in families):
            stats["inactive_sequences"] += 1
            continue
        if tyshkevich_decomposable_seq(d):
            stats["decomposable_sequences"] += 1
            continue

        nbcap = []
        for v, (order, family) in enumerate(families):
            capable = False
            for posmask in family:
                actual = sum(1 << order[i] for i in range(n - 1) if (posmask >> i) & 1)
                residual = residual_sequence(d, v, actual)
                if realization_graph_nonbipartite(residual):
                    capable = True
                    break
            nbcap.append(capable)

        relevant_hooks = [v for v in range(n) if hooks[v] is not None and nbcap[v]]
        if not relevant_hooks:
            continue
        stats["target_sequences"] += 1
        stats["relevant_hook_pivots"] += len(relevant_hooks)

        graphs = realizations(d)
        stats["realizations"] += len(graphs)
        rows = neighbourhoods(graphs, n)
        candidates: set[tuple[int, int]] = set()
        for v in relevant_hooks:
            left, right = hooks[v]
            left_ids = [i for i, ng in enumerate(rows) if ng[v] == left]
            right_ids = [i for i, ng in enumerate(rows) if ng[v] == right]
            candidates.update((min(i, j), max(i, j)) for i in left_ids for j in right_ids if i != j)

        stats["candidate_pairs"] += len(candidates)
        for i, j in candidates:
            def exceptional(v: int) -> bool:
                if hooks[v] is None:
                    return False
                return {rows[i][v], rows[j][v]} == set(hooks[v])

            good = [
                v
                for v in range(n)
                if rows[i][v] != rows[j][v] and nbcap[v] and not exceptional(v)
            ]
            spare = len(good)
            histogram[spare] += 1
            minimum_spares = spare if minimum_spares is None else min(minimum_spares, spare)
            if spare == 0:
                violations.append({"degree_sequence": d, "graphs": [graphs[i], graphs[j]]})

    return {
        "order": n,
        "stats": dict(stats),
        "spare_histogram": dict(sorted(histogram.items())),
        "minimum_spares": minimum_spares,
        "violations": violations,
        "elapsed_seconds": time.monotonic() - started,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("orders", nargs="*", type=int, default=[9, 10])
    parser.add_argument("--json", dest="json_path")
    args = parser.parse_args()
    result = {"implementation": "independent-self-contained", "orders": []}
    for n in args.orders:
        item = audit_order(n)
        result["orders"].append(item)
        print(json.dumps(item, sort_keys=True), flush=True)
    if args.json_path:
        with open(args.json_path, "w", encoding="utf-8") as handle:
            json.dump(result, handle, indent=2, sort_keys=True)
            handle.write("\n")


if __name__ == "__main__":
    main()
