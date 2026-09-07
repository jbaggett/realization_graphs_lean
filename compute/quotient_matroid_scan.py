#!/usr/bin/env python3
"""Exhaustively test pivot-neighborhood families for basis exchange.

For a graphical labeled degree vector d and pivot mu, the tested family is

    N(d, mu) = {S subset V - {mu} : |S| = d[mu]
                and d|_(V-{mu}) - 1_S is graphical}.

The scan uses only the Erdos--Gallai criterion.  Degree vectors are enumerated
as nonincreasing partitions; one representative pivot from each degree class
is enough because equal-degree labels are symmetric.
"""

from itertools import combinations
import argparse
import json


def eg_failure(seq):
    """Return None iff seq is graphical, otherwise an exact failed condition."""
    a = sorted(seq, reverse=True)
    n = len(a)
    if any(x < 0 or x >= n for x in a):
        return {"kind": "range", "sorted": a}
    if sum(a) % 2:
        return {"kind": "parity", "sorted": a, "sum": sum(a)}
    prefix = 0
    for k in range(1, n + 1):
        prefix += a[k - 1]
        rhs = k * (k - 1) + sum(min(x, k) for x in a[k:])
        if prefix > rhs:
            return {
                "kind": "erdos-gallai",
                "sorted": a,
                "k": k,
                "lhs": prefix,
                "rhs": rhs,
            }
    return None


def is_graphical(seq):
    return eg_failure(seq) is None


def degree_partitions(n):
    """All nonincreasing length-n vectors with entries in [0,n-1]."""
    for d in combinations(range(2 * n - 1), n):
        # Standard combinations-to-partitions bijection, generated increasing.
        inc = tuple(d[i] - i for i in range(n))
        yield tuple(reversed(inc))


def family(degrees, pivot):
    ground = tuple(i for i in range(len(degrees)) if i != pivot)
    rank = degrees[pivot]
    bases = []
    for choice in combinations(ground, rank):
        S = frozenset(choice)
        residual = tuple(
            degrees[u] - (u in S) for u in ground
        )
        if is_graphical(residual):
            bases.append(S)
    return ground, bases


def exchange_failure(bases):
    base_set = set(bases)
    for B in bases:
        for C in bases:
            for e in sorted(B - C):
                candidates = []
                for f in sorted(C - B):
                    exchanged = frozenset((B - {e}) | {f})
                    candidates.append((f, exchanged, exchanged in base_set))
                if not any(ok for _, _, ok in candidates):
                    return B, C, e, candidates
    return None


def encode_set(S):
    return sorted(S)


def describe_failure(degrees, pivot, ground, bases, failure):
    B, C, e, candidates = failure
    union = set().union(*bases)
    intersection = set(ground).intersection(*bases)

    def residual(S):
        return [degrees[u] - (u in S) for u in ground]

    return {
        "n": len(degrees),
        "degrees": list(degrees),
        "pivot": pivot,
        "pivot_degree": degrees[pivot],
        "ground": list(ground),
        "base_count": len(bases),
        "bases": [encode_set(S) for S in bases],
        "loops": sorted(set(ground) - union),
        "coloops": sorted(intersection),
        "exchange_failure": {
            "B": encode_set(B),
            "B_residual": residual(B),
            "B_residual_sorted": sorted(residual(B), reverse=True),
            "C": encode_set(C),
            "C_residual": residual(C),
            "C_residual_sorted": sorted(residual(C), reverse=True),
            "e": e,
            "candidates": [
                {
                    "f": f,
                    "set": encode_set(S),
                    "residual": residual(S),
                    "failure": eg_failure(residual(S)),
                }
                for f, S, _ in candidates
            ],
        },
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--nmax", type=int, default=8)
    parser.add_argument("--all-failures", action="store_true")
    parser.add_argument(
        "--continue-scan",
        action="store_true",
        help="scan the full range but retain only the first detailed witness",
    )
    args = parser.parse_args()

    stats = {"graphical_sequences": 0, "pivot_families": 0, "failures": 0}
    by_n = {}
    reports = []
    for n in range(1, args.nmax + 1):
        for degrees in degree_partitions(n):
            if not is_graphical(degrees):
                continue
            stats["graphical_sequences"] += 1
            row = by_n.setdefault(
                n, {"graphical_sequences": 0, "pivot_families": 0, "failures": 0}
            )
            row["graphical_sequences"] += 1
            seen_degrees = set()
            for pivot, pivot_degree in enumerate(degrees):
                if pivot_degree in seen_degrees:
                    continue
                seen_degrees.add(pivot_degree)
                ground, bases = family(degrees, pivot)
                assert bases, (degrees, pivot)
                stats["pivot_families"] += 1
                row["pivot_families"] += 1
                failure = exchange_failure(bases)
                if failure is None:
                    continue
                stats["failures"] += 1
                row["failures"] += 1
                report = describe_failure(degrees, pivot, ground, bases, failure)
                if args.all_failures or not reports:
                    reports.append(report)
                if not args.all_failures and not args.continue_scan:
                    print(
                        json.dumps(
                            {"stats": stats, "by_n": by_n, "first_failure": reports[0]},
                            indent=2,
                        )
                    )
                    return

    key = "failures" if args.all_failures else "first_failure"
    value = reports if args.all_failures else (reports[0] if reports else None)
    print(json.dumps({"stats": stats, "by_n": by_n, key: value}, indent=2))


if __name__ == "__main__":
    main()
