#!/usr/bin/env python3
"""Exhaustive paired k-DPC census for the 12-vertex crown, k = 2, 3, 4.

Vertices are a_0,...,a_5 = 0,...,5 and b_0,...,b_5 = 6,...,11, with
a_i adjacent to b_j exactly when i != j.

Rigid counting convention
-------------------------
A rigid demand is a matching of k unordered pairs on a chosen 2k-set.  Reversing a
path or permuting the k paths does not change the demand.  Thus there are

    binom(12, 2k) (2k - 1)!!

demands.  The ordered/oriented role-tuple count is larger by 2^k k!.  In
particular, the paper's k=2 opposite-pair domain has 450 matching demands and
3,600 ordered/oriented role tuples.

Flexible counting convention
----------------------------
For k distinct prescribed roots x_1,...,x_k, give root x_i a three-element menu
M_i contained in V minus {x_1,...,x_k}.  Menus may overlap.  A selection chooses
distinct y_i in M_i and asks for paths pairing x_i with y_i.  A flexible demand is
parity-admissible if it has at least one distinct parity-admissible selection, and
is servable if it has at least one servable such selection.  Roots are kept in
increasing order, so the menus remain attached to named roots while the paths
themselves are unordered.  Exact three-sets imply the >=3 version by monotonicity.

Reliability design
------------------
* validate_cover is deliberately defined before any search code.  Every positive
  rigid result is passed through it, including every witness later reused by the
  flexible census.
* Search state uses immutable integer masks.  There is no mutating set.pop()
  backtracking.
* Hamilton paths on every induced vertex set are computed by subset DP.  For each
  demand, all allocations of the nonterminals among the k paths are exhausted.
* The flexible census is exact but does not iterate billions of menu tuples.  It
  counts all tuples by last-menu inclusion/exclusion and evaluates one representative
  of every root-set orbit under the full crown automorphism group S_6 x C_2.

Run (the ulimit argument is in KiB):

    ( ulimit -v 67108864; python3 -u \
      topics/flipgraphs/realization/compute/crown_dpc_k34.py )

Pass --json for the machine-readable record printed to stdout.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from itertools import combinations, permutations, product
from math import comb, factorial


N = 12
SIDE = 6
ALL = (1 << N) - 1
COLOR = tuple(0 if v < SIDE else 1 for v in range(N))
INDEX = tuple(v % SIDE for v in range(N))
ADJ_MASK = tuple(
    sum(1 << w for w in range(N) if COLOR[v] != COLOR[w] and INDEX[v] != INDEX[w])
    for v in range(N)
)


def adjacent(u: int, v: int) -> bool:
    return bool(ADJ_MASK[u] & (1 << v))


def validate_cover(demand: tuple[tuple[int, int], ...],
                   paths: tuple[tuple[int, ...], ...]) -> None:
    """Raise AssertionError unless paths are exactly a valid spanning paired cover."""
    assert len(paths) == len(demand)
    used = 0
    for pair, path in zip(demand, paths):
        assert len(path) >= 2
        assert (path[0], path[-1]) == pair
        path_mask = 0
        for v in path:
            assert 0 <= v < N
            assert not (path_mask & (1 << v))
            path_mask |= 1 << v
        for u, v in zip(path, path[1:]):
            assert adjacent(u, v), (pair, path, u, v)
        assert not (used & path_mask)
        used |= path_mask
    assert used == ALL, (demand, paths, used)


def bits(mask: int):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def double_factorial_odd(k: int) -> int:
    out = 1
    for x in range(1, 2 * k, 2):
        out *= x
    return out


def perfect_matchings(vertices: tuple[int, ...]):
    """All matchings once, with each pair and the tuple of pairs canonicalized."""
    if not vertices:
        yield ()
        return
    first = vertices[0]
    for j in range(1, len(vertices)):
        second = vertices[j]
        rest = vertices[1:j] + vertices[j + 1:]
        for tail in perfect_matchings(rest):
            yield ((first, second),) + tail


def all_demands(k: int):
    for terminals in combinations(range(N), 2 * k):
        yield from perfect_matchings(terminals)


def delta(pair: tuple[int, int]) -> int:
    u, v = pair
    if COLOR[u] != COLOR[v]:
        return 0
    return 1 if COLOR[u] == 0 else -1


def parity_admissible(demand: tuple[tuple[int, int], ...]) -> bool:
    return sum(delta(pair) for pair in demand) == 0


def feature_tuple(demand: tuple[tuple[int, int], ...]) -> tuple[int, int, int, int]:
    """(A-A pairs, B-B pairs, diagonal cross pairs, off-diagonal cross pairs)."""
    aa = bb = diagonal = off_diagonal = 0
    for u, v in demand:
        if COLOR[u] == COLOR[v] == 0:
            aa += 1
        elif COLOR[u] == COLOR[v] == 1:
            bb += 1
        elif INDEX[u] == INDEX[v]:
            diagonal += 1
        else:
            off_diagonal += 1
    return aa, bb, diagonal, off_diagonal


def forced_interior_lower_bound(demand: tuple[tuple[int, int], ...]) -> int:
    """One interior vertex per same-side pair, two per missing diagonal cross edge."""
    aa, bb, diagonal, _ = feature_tuple(demand)
    return aa + bb + 2 * diagonal


class HamiltonSubsetPaths:
    """Hamilton-path witnesses for every (start, induced mask, end) triple."""

    def __init__(self) -> None:
        self.reach: list[list[int]] = []
        self.pred: list[bytearray] = []
        for start in range(N):
            reachable_ends = [0] * (1 << N)
            predecessor = bytearray([255]) * ((1 << N) * N)
            start_mask = 1 << start
            reachable_ends[start_mask] = start_mask
            predecessor[start_mask * N + start] = start
            for mask in range(1 << N):
                if not (mask & start_mask):
                    continue
                ends = reachable_ends[mask]
                for end in bits(ends):
                    available = ADJ_MASK[end] & ~mask & ALL
                    for nxt in bits(available):
                        new_mask = mask | (1 << nxt)
                        if not (reachable_ends[new_mask] & (1 << nxt)):
                            reachable_ends[new_mask] |= 1 << nxt
                            predecessor[new_mask * N + nxt] = end
            self.reach.append(reachable_ends)
            self.pred.append(predecessor)

    def exists(self, start: int, end: int, mask: int) -> bool:
        return bool(self.reach[start][mask] & (1 << end))

    def path(self, start: int, end: int, mask: int) -> tuple[int, ...] | None:
        if not self.exists(start, end, mask):
            return None
        rev = [end]
        cur = end
        cur_mask = mask
        while cur != start:
            prev = self.pred[start][cur_mask * N + cur]
            assert prev != 255
            rev.append(prev)
            cur_mask ^= 1 << cur
            cur = prev
        rev.reverse()
        return tuple(rev)


def solve_demand(demand: tuple[tuple[int, int], ...], hp: HamiltonSubsetPaths):
    endpoint_mask = 0
    for u, v in demand:
        endpoint_mask |= (1 << u) | (1 << v)
    interior = ALL ^ endpoint_mask
    k = len(demand)

    # Try the pair with the fewest feasible supports first.  The original indices are
    # retained so the returned paths line up with the demand for validation.
    candidates = []
    for i, (u, v) in enumerate(demand):
        pair_mask = (1 << u) | (1 << v)
        feasible = []
        sub = interior
        while True:
            mask = pair_mask | sub
            if hp.exists(u, v, mask):
                feasible.append(sub)
            if sub == 0:
                break
            sub = (sub - 1) & interior
        candidates.append((len(feasible), i, tuple(feasible)))
    candidates.sort()

    assigned = [0] * k

    def search(pos: int, remaining: int) -> bool:
        _, original_i, feasible = candidates[pos]
        if pos == k - 1:
            if remaining in feasible:
                assigned[original_i] = remaining
                return True
            return False
        for sub in feasible:
            if sub & ~remaining:
                continue
            assigned[original_i] = sub
            if search(pos + 1, remaining ^ sub):
                return True
        return False

    if not search(0, interior):
        return None
    paths = []
    for (u, v), internal_mask in zip(demand, assigned):
        path = hp.path(u, v, (1 << u) | (1 << v) | internal_mask)
        assert path is not None
        paths.append(path)
    answer = tuple(paths)
    validate_cover(demand, answer)
    return answer


def rigid_census(hp: HamiltonSubsetPaths):
    results = {}
    status_by_k = {}
    witnesses_by_k = {}
    validator_calls = 0

    for k in (2, 3, 4):
        total = admissible = servable = 0
        strict_opposite = strict_opposite_servable = 0
        failure_features = Counter()
        positive_features = Counter()
        status = {}
        witnesses = {}
        first_failure = None
        lower_bound_equivalence = True

        for demand in all_demands(k):
            total += 1
            pa = parity_admissible(demand)
            if not pa:
                continue
            admissible += 1
            opposite = all(COLOR[u] != COLOR[v] for u, v in demand)
            if opposite:
                strict_opposite += 1
            cover = solve_demand(demand, hp)
            ok = cover is not None
            status[demand] = ok
            if ok:
                # solve_demand has just run the validator.  Store the witness so every
                # flexible positive is reduced to one of these already validated covers.
                validator_calls += 1
                witnesses[demand] = cover
                servable += 1
                positive_features[feature_tuple(demand)] += 1
                if opposite:
                    strict_opposite_servable += 1
            else:
                failure_features[feature_tuple(demand)] += 1
                if first_failure is None:
                    first_failure = demand

            predicted = forced_interior_lower_bound(demand) <= N - 2 * k
            if predicted != ok:
                lower_bound_equivalence = False

        expected = comb(N, 2 * k) * double_factorial_odd(k)
        assert total == expected
        results[str(k)] = {
            "canonical_demands": total,
            "ordered_oriented_role_tuples": total * (2 ** k) * factorial(k),
            "parity_admissible": admissible,
            "parity_inadmissible": total - admissible,
            "admissible_servable": servable,
            "admissible_unservable": admissible - servable,
            "strict_opposite_pair_subdomain": strict_opposite,
            "strict_opposite_pair_subdomain_servable": strict_opposite_servable,
            "strict_opposite_ordered_oriented_role_tuples":
                strict_opposite * (2 ** k) * factorial(k),
            "admissible_features": {
                str(key): positive_features[key] + failure_features[key]
                for key in sorted(positive_features.keys() | failure_features.keys())
            },
            "servable_features": {
                str(key): value for key, value in sorted(positive_features.items())
            },
            "failure_features": {
                str(key): value for key, value in sorted(failure_features.items())
            },
            "first_failure": first_failure,
            "forced_interior_bound_iff_servable_on_admissible_domain": lower_bound_equivalence,
        }
        status_by_k[k] = status
        witnesses_by_k[k] = witnesses

    # Exact reconciliation with Lemma 3.2's demand model.
    assert results["2"]["strict_opposite_pair_subdomain"] == 450
    assert results["2"]["strict_opposite_pair_subdomain_servable"] == 450
    assert results["2"]["strict_opposite_ordered_oriented_role_tuples"] == 3600
    assert results["3"]["canonical_demands"] == 13860
    assert results["4"]["canonical_demands"] == 51975
    return results, status_by_k, witnesses_by_k, validator_calls


def crown_automorphisms():
    maps = []
    for perm in permutations(range(SIDE)):
        maps.append(tuple(COLOR[v] * SIDE + perm[INDEX[v]] for v in range(N)))
        maps.append(tuple((1 - COLOR[v]) * SIDE + perm[INDEX[v]] for v in range(N)))
    assert len(maps) == 1440 and len(set(maps)) == 1440
    return tuple(maps)


def canonical_demand_under_automorphisms(demand, automorphisms):
    return min(
        tuple(sorted(tuple(sorted((mapping[u], mapping[v]))) for u, v in demand))
        for mapping in automorphisms
    )


def vertex_name(v: int) -> str:
    return ("a" if COLOR[v] == 0 else "b") + str(INDEX[v])


def demand_names(demand):
    return tuple((vertex_name(u), vertex_name(v)) for u, v in demand)


def rigid_failure_orbits(status, automorphisms):
    groups = Counter(
        canonical_demand_under_automorphisms(demand, automorphisms)
        for demand, ok in status.items() if not ok
    )
    rows = []
    for representative, count in sorted(
            groups.items(), key=lambda item: (feature_tuple(item[0]), item[0])):
        rows.append({
            "representative": representative,
            "representative_named": demand_names(representative),
            "feature_tuple_AA_BB_diagonalCross_offDiagonalCross":
                feature_tuple(representative),
            "forced_interior_lower_bound": forced_interior_lower_bound(representative),
            "canonical_demands_in_orbit": count,
        })
    return rows


def root_orbits(k: int, automorphisms):
    buckets = {}
    for roots in combinations(range(N), k):
        canonical = min(tuple(sorted(mapping[v] for v in roots)) for mapping in automorphisms)
        buckets.setdefault(canonical, []).append(roots)
    assert sum(map(len, buckets.values())) == comb(N, k)
    return tuple((representative, len(members))
                 for representative, members in sorted(buckets.items()))


def canonical_demand_from_selection(roots: tuple[int, ...],
                                    selected: tuple[int, ...]):
    return tuple(sorted(tuple(sorted(pair)) for pair in zip(roots, selected)))


def three_menus(pool_size: int):
    return tuple(
        (sum(1 << x for x in choice), choice)
        for choice in combinations(range(pool_size), 3)
    )


def choose_count(n: int, r: int) -> int:
    return comb(n, r) if n >= r else 0


def flexible_orbit_census(k: int, roots: tuple[int, ...], rigid_status):
    """Count all menu tuples for a root representative, exactly.

    For each tuple of the first k-1 menus, legal_last (respectively good_last)
    records the last-pool vertices completing some distinct parity-admissible
    (respectively servable) selection.  The number of three-menus intersecting a
    q-set is C(p,3)-C(p-q,3), which counts the final menu without iterating it.
    """
    pool = tuple(v for v in range(N) if v not in roots)
    p = len(pool)
    menus = three_menus(p)
    menu_choices = tuple(choice for _, choice in menus)
    leaf = {}

    for prefix in product(range(p), repeat=k - 1):
        if len(set(prefix)) != len(prefix):
            leaf[prefix] = (0, 0)
            continue
        legal_last = good_last = 0
        used = set(prefix)
        for last in range(p):
            if last in used:
                continue
            local_selection = prefix + (last,)
            selected = tuple(pool[i] for i in local_selection)
            demand = canonical_demand_from_selection(roots, selected)
            if not parity_admissible(demand):
                continue
            legal_last |= 1 << last
            if rigid_status[demand]:
                good_last |= 1 << last
        leaf[prefix] = (legal_last, good_last)

    total_admissible = total_servable = 0
    failure_sample = None
    prefix_menu_tuples = 0
    for prefix_menus in product(menu_choices, repeat=k - 1):
        prefix_menu_tuples += 1
        legal_last = good_last = 0
        for selected_prefix in product(*prefix_menus):
            legal, good = leaf[selected_prefix]
            legal_last |= legal
            good_last |= good
        nlegal = legal_last.bit_count()
        ngood = good_last.bit_count()
        legal_menu_count = len(menus) - choose_count(p - nlegal, 3)
        good_menu_count = len(menus) - choose_count(p - ngood, 3)
        total_admissible += legal_menu_count
        total_servable += good_menu_count

        if failure_sample is None and legal_menu_count > good_menu_count:
            bad_completers = legal_last & ~good_last
            bad_last = next(bits(bad_completers))
            allowed_for_last_menu = ((1 << p) - 1) & ~good_last
            fill = [bad_last] + [x for x in bits(allowed_for_last_menu) if x != bad_last][:2]
            assert len(fill) == 3
            final_menu = tuple(fill)
            actual_menus = tuple(tuple(pool[i] for i in menu) for menu in prefix_menus) + \
                (tuple(pool[i] for i in final_menu),)

            # Validate the compressed counterexample claim by direct enumeration of all
            # 3^k menu selections.  It must have a legal selection and no good one.
            direct_legal = direct_good = False
            for selected in product(*actual_menus):
                if len(set(selected)) != k:
                    continue
                demand = canonical_demand_from_selection(roots, selected)
                if not parity_admissible(demand):
                    continue
                direct_legal = True
                if rigid_status[demand]:
                    direct_good = True
            assert direct_legal and not direct_good
            failure_sample = {"roots": roots, "menus": actual_menus}

    expected_prefixes = len(menus) ** (k - 1)
    assert prefix_menu_tuples == expected_prefixes
    return {
        "roots": roots,
        "pool_size": p,
        "menus_per_root": len(menus),
        "menu_tuples": len(menus) ** k,
        "parity_admissible": total_admissible,
        "servable": total_servable,
        "unservable": total_admissible - total_servable,
        "failure_sample": failure_sample,
    }


def flexible_census(status_by_k, automorphisms):
    out = {}
    for k in (3, 4):
        orbit_rows = []
        total = admissible = servable = 0
        for roots, orbit_size in root_orbits(k, automorphisms):
            row = flexible_orbit_census(k, roots, status_by_k[k])
            row["root_orbit_size"] = orbit_size
            orbit_rows.append(row)
            total += orbit_size * row["menu_tuples"]
            admissible += orbit_size * row["parity_admissible"]
            servable += orbit_size * row["servable"]
        menu_count = comb(N - k, 3)
        expected = comb(N, k) * menu_count ** k
        assert total == expected
        out[str(k)] = {
            "prescribed_roots": k,
            "flexible_partners": k,
            "menu_size": 3,
            "menus_avoid_all_roots": True,
            "menus_may_overlap": True,
            "selected_partners_must_be_distinct": True,
            "root_set_orbits_under_S6_x_C2": len(orbit_rows),
            "all_menu_demands": total,
            "parity_admissible": admissible,
            "parity_inadmissible": total - admissible,
            "admissible_servable": servable,
            "admissible_unservable": admissible - servable,
            "orbit_rows": orbit_rows,
        }
    return out


def make_record():
    hp = HamiltonSubsetPaths()
    rigid, status_by_k, _witnesses_by_k, validator_calls = rigid_census(hp)
    automorphisms = crown_automorphisms()
    exception_orbits = rigid_failure_orbits(status_by_k[4], automorphisms)
    assert len(exception_orbits) == 9
    assert sum(row["canonical_demands_in_orbit"] for row in exception_orbits) == 1935
    flexible = flexible_census(status_by_k, automorphisms)
    return {
        "schema": "crown-dpc-k34-v1",
        "graph": {
            "name": "K_{6,6} - 6K_2",
            "vertices": ["a0..a5", "b0..b5"],
            "adjacency": "a_i ~ b_j iff i != j",
        },
        "rigid_counting": "unoriented pairs and unordered path family",
        "rigid": rigid,
        "rigid_exception_characterization": {
            "statement": (
                "There are no k=2 or k=3 exceptions.  The k=4 exceptions are exactly "
                "the S_6 x C_2 images of the nine listed representatives; path reversal "
                "and path-family reordering are already factored out."
            ),
            "k4_exception_orbits": exception_orbits,
            "coarse_necessary_bound": (
                "Every same-side pair needs at least one interior vertex and every diagonal "
                "cross pair a_i--b_i needs at least two.  Hence (#same-side)+2*(#diagonal "
                "cross) <= 4 is necessary at k=4, but the orbit list shows it is not sufficient."
            ),
        },
        "flexible": flexible,
        "validation": {
            "positive_rigid_covers_validated": validator_calls,
            "checks_per_cover": [
                "endpoint pair for every path",
                "every consecutive edge",
                "simplicity of every path",
                "pairwise vertex-disjointness",
                "union of path vertices is all 12 vertices",
            ],
            "mutable_set_pop_used": False,
        },
        "skipped": [],
    }


def human_summary(record):
    print("Crown K_{6,6} - 6K_2 exhaustive paired-DPC census")
    print("Rigid demands: canonical unoriented matching count; role count = canonical * 2^k k!\n")
    for k in ("2", "3", "4"):
        row = record["rigid"][k]
        print(
            f"k={k}: total={row['canonical_demands']:,}; "
            f"parity-admissible={row['parity_admissible']:,}; "
            f"servable={row['admissible_servable']:,}; "
            f"failures={row['admissible_unservable']:,}"
        )
        if row["failure_features"]:
            print(f"     failure features (AA,BB,diagonal-cross,off-diagonal-cross): "
                  f"{row['failure_features']}")
    control = record["rigid"]["2"]
    print(
        "\nk=2 Lemma 3.2 control: "
        f"{control['strict_opposite_pair_subdomain_servable']:,}/"
        f"{control['strict_opposite_pair_subdomain']:,} canonical = "
        f"{control['strict_opposite_ordered_oriented_role_tuples']:,}/3,600 role tuples"
    )
    for k in ("3", "4"):
        row = record["flexible"][k]
        print(
            f"flexible k={k}: total={row['all_menu_demands']:,}; "
            f"parity-admissible={row['parity_admissible']:,}; "
            f"servable={row['admissible_servable']:,}; "
            f"failures={row['admissible_unservable']:,}; "
            f"root orbits={row['root_set_orbits_under_S6_x_C2']}"
        )
    print(f"\nValidated positive rigid covers: "
          f"{record['validation']['positive_rigid_covers_validated']:,}")
    print("Skipped: none")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true", help="print only JSON")
    args = parser.parse_args()
    record = make_record()
    if args.json:
        print(json.dumps(record, indent=2, sort_keys=True))
    else:
        human_summary(record)


if __name__ == "__main__":
    main()
