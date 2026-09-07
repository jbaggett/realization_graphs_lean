#!/usr/bin/env python3
"""Independent graph-level verification of the five-vertex matroid witness."""

from itertools import combinations
import json


DEGREES = (3, 2, 2, 2, 1)
PIVOT = 1


def degree_vector(vertices, edges):
    return tuple(sum(v in edge for edge in edges) for v in vertices)


def pivot_neighborhood(edges):
    return frozenset(
        v if u == PIVOT else u
        for u, v in edges
        if u == PIVOT or v == PIVOT
    )


def switch_adjacent(left, right):
    difference = left ^ right
    if len(difference) != 4:
        return False
    support = set().union(*difference)
    return len(support) == 4 and all(
        sum(v in edge for edge in difference) == 2 for v in support
    )


def encode_set(values):
    return sorted(values)


def main():
    vertices = tuple(range(len(DEGREES)))
    possible_edges = tuple(combinations(vertices, 2))
    realizations = []
    for mask in range(1 << len(possible_edges)):
        edges = frozenset(
            edge for i, edge in enumerate(possible_edges) if (mask >> i) & 1
        )
        if degree_vector(vertices, edges) == DEGREES:
            realizations.append((pivot_neighborhood(edges), edges))

    family = sorted({S for S, _ in realizations}, key=encode_set)
    fiber_sizes = {
        str(encode_set(S)): sum(T == S for T, _ in realizations) for S in family
    }
    quotient_edges = set()
    for (S, left), (T, right) in combinations(realizations, 2):
        if S != T and switch_adjacent(left, right):
            quotient_edges.add(frozenset((S, T)))

    B = frozenset({0, 4})
    C = frozenset({2, 3})
    e = 0
    exchanges = [frozenset((B - {e}) | {f}) for f in sorted(C - B)]
    union = set().union(*family)
    intersection = set(vertices) - {PIVOT}
    intersection.intersection_update(*family)

    print(
        json.dumps(
            {
                "degrees": DEGREES,
                "pivot": PIVOT,
                "realization_count": len(realizations),
                "family": [encode_set(S) for S in family],
                "fiber_sizes": fiber_sizes,
                "loops": sorted((set(vertices) - {PIVOT}) - union),
                "coloops": sorted(intersection),
                "exchange_failure": {
                    "B": encode_set(B),
                    "C": encode_set(C),
                    "e": e,
                    "candidates": [
                        {"set": encode_set(S), "realizable": S in family}
                        for S in exchanges
                    ],
                },
                "actual_quotient_edges": sorted(
                    ([encode_set(S) for S in edge] for edge in quotient_edges),
                    key=str,
                ),
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
