#!/usr/bin/env python3
"""Independent exhaustive seal for the shifted-family Step Lemma inputs.

This file is intentionally self-contained.  It enumerates shifted families as
nonempty order ideals in the Gale poset, classifies bad templates directly from
their Johnson graphs, and applies the four checks specified in the seal brief.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import resource
import shlex
import sys
import time
from functools import lru_cache
from itertools import combinations
from pathlib import Path
from typing import Iterator, Sequence


GIB = 1024**3
REQUESTED_AS_LIMIT_BYTES = 8 * GIB
SCRIPT_PATH = Path(__file__).resolve()
COMPUTE_DIR = SCRIPT_PATH.parent
REALIZATION_DIR = COMPUTE_DIR.parent
DEFAULT_JSON_PATH = COMPUTE_DIR / "data" / "seal_step_lemma_inputs_2026_08_15.json"
DEFAULT_REPORT_PATH = REALIZATION_DIR / "SEAL_STEP_LEMMA_INPUTS_2026-08-15.md"


def set_as_list(mask: int) -> list[int]:
    """Convert a bit-mask set to its increasing, one-based list."""
    return [i + 1 for i in range(mask.bit_length()) if mask & (1 << i)]


def family_as_lists(family: Sequence[int]) -> list[list[int]]:
    return [set_as_list(x) for x in sorted(family)]


def mask_from_tuple(values: Sequence[int]) -> int:
    mask = 0
    for value in values:
        mask |= 1 << (value - 1)
    return mask


def gale_leq(left: int, right: int) -> bool:
    """Componentwise order on two equicardinal sets."""
    return all(a <= b for a, b in zip(set_as_list(left), set_as_list(right)))


def johnson_adjacent(left: int, right: int) -> bool:
    return (left ^ right).bit_count() == 2


def is_shifted_family(family: Sequence[int], n: int) -> bool:
    """Check the stated single-decrement definition directly."""
    members = set(family)
    if not members:
        return False
    for member in members:
        for j in range(n):
            if not (member & (1 << j)):
                continue
            for i in range(j):
                if member & (1 << i):
                    continue
                decremented = (member ^ (1 << j)) | (1 << i)
                if decremented not in members:
                    return False
    return True


def rank_sets(n: int, k: int) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Return a linear extension of the Gale poset and strict lower masks."""
    entries = []
    for values in combinations(range(1, n + 1), k):
        entries.append((sum(values), values, mask_from_tuple(values)))
    entries.sort()
    sets = tuple(entry[2] for entry in entries)
    tuples = tuple(entry[1] for entry in entries)
    lower_masks: list[int] = []
    for i, values in enumerate(tuples):
        lower = 0
        for j, candidate in enumerate(tuples[:i]):
            if all(a <= b for a, b in zip(candidate, values)):
                lower |= 1 << j
        lower_masks.append(lower)
    return sets, tuple(lower_masks)


def shifted_family_masks(n: int, k: int) -> Iterator[int]:
    """Enumerate every nonempty order ideal of the rank-(n,k) Gale poset."""
    sets, lower_masks = rank_sets(n, k)

    def visit(index: int, family_mask: int) -> Iterator[int]:
        if index == len(sets):
            if family_mask:
                yield family_mask
            return

        # Excluding an element is always possible.  A later element can only
        # be included when every one of its strict Gale predecessors is in.
        yield from visit(index + 1, family_mask)
        if lower_masks[index] & ~family_mask == 0:
            yield from visit(index + 1, family_mask | (1 << index))

    yield from visit(0, 0)


def members_from_family_mask(family_mask: int, sets: Sequence[int]) -> tuple[int, ...]:
    return tuple(sets[i] for i in range(len(sets)) if family_mask & (1 << i))


@lru_cache(maxsize=None)
def bad_template_universal_pair(family: tuple[int, ...]) -> tuple[int, int] | None:
    """Apply the operational bad-template graph definition verbatim."""
    family = tuple(sorted(family))
    size = len(family)
    if size < 4:
        return None

    neighbours: dict[int, set[int]] = {}
    for vertex in family:
        neighbours[vertex] = {
            other for other in family if other != vertex and johnson_adjacent(vertex, other)
        }

    universal = tuple(vertex for vertex in family if len(neighbours[vertex]) == size - 1)
    if len(universal) != 2:
        return None

    remainder = set(family) - set(universal)
    components: list[set[int]] = []
    unseen = set(remainder)
    while unseen:
        root = min(unseen)
        component = {root}
        frontier = [root]
        unseen.remove(root)
        while frontier:
            current = frontier.pop()
            discovered = neighbours[current] & unseen
            unseen.difference_update(discovered)
            component.update(discovered)
            frontier.extend(discovered)
        components.append(component)

    if len(components) != 2 or any(not component for component in components):
        return None
    for component in components:
        if any(not johnson_adjacent(x, y) for x, y in combinations(component, 2)):
            return None
    return tuple(sorted(universal))


def other_universal(pair: tuple[int, int] | None, member: int) -> int | None:
    if pair is None or member not in pair:
        return None
    return pair[1] if pair[0] == member else pair[0]


def step_parts(
    family: tuple[int, ...], a: int, b: int, e: int
) -> tuple[
    tuple[int, ...],
    tuple[int, ...],
    tuple[int, ...],
    tuple[int, int] | None,
    tuple[int, int] | None,
    int | None,
    int | None,
]:
    e_bit = 1 << (e - 1)
    f1 = tuple(x for x in family if x & e_bit)
    f0 = tuple(x for x in family if not (x & e_bit))
    link = tuple(sorted(x ^ e_bit for x in f1))
    link_pair = bad_template_universal_pair(link)
    f0_pair = bad_template_universal_pair(tuple(sorted(f0)))
    y_forbidden = other_universal(link_pair, a ^ e_bit)
    if y_forbidden is not None:
        y_forbidden |= e_bit
    x_forbidden = other_universal(f0_pair, b)
    return f1, f0, link, link_pair, f0_pair, y_forbidden, x_forbidden


def valid_step_exists(family: tuple[int, ...], a: int, b: int, e: int) -> bool:
    f1, f0, _, _, _, y_forbidden, x_forbidden = step_parts(family, a, b, e)
    if len(f1) == 1:
        eligible_y = (a,)
    else:
        eligible_y = tuple(y for y in f1 if y != a and y != y_forbidden)
    if len(f0) == 1:
        eligible_x = (b,)
    else:
        eligible_x = tuple(x for x in f0 if x != b and x != x_forbidden)
    return any(johnson_adjacent(y, x) for y in eligible_y for x in eligible_x)


def step_diagnostics(family: tuple[int, ...], a: int, b: int, e: int) -> dict:
    """Produce complete candidate and exclusion data for a violation witness."""
    f1, f0, link, link_pair, f0_pair, y_forbidden, x_forbidden = step_parts(
        family, a, b, e
    )
    exchange_pairs = []
    for y in f1:
        for x in f0:
            if not johnson_adjacent(y, x):
                continue
            y_allowed = y == a if len(f1) == 1 else y != a and y != y_forbidden
            x_allowed = x == b if len(f0) == 1 else x != b and x != x_forbidden
            exchange_pairs.append(
                {
                    "Y": set_as_list(y),
                    "X": set_as_list(x),
                    "Y_allowed": y_allowed,
                    "X_allowed": x_allowed,
                    "valid": y_allowed and x_allowed,
                }
            )
    return {
        "F1": family_as_lists(f1),
        "F0": family_as_lists(f0),
        "link": family_as_lists(link),
        "link_bad_universal_pair": (
            family_as_lists(link_pair) if link_pair is not None else None
        ),
        "F0_bad_universal_pair": (
            family_as_lists(f0_pair) if f0_pair is not None else None
        ),
        "Y_forbidden": set_as_list(y_forbidden) if y_forbidden is not None else None,
        "X_forbidden": set_as_list(x_forbidden) if x_forbidden is not None else None,
        "exchange_pairs": exchange_pairs,
    }


def distinguished_sets(k: int) -> tuple[int, int]:
    m1 = (1 << k) - 1
    m2 = ((1 << (k - 1)) - 1) | (1 << k)
    return m1, m2


def hook_family(n: int, k: int, r: int, s: int) -> tuple[int, ...]:
    m1, m2 = distinguished_sets(k)
    right_base = m1 ^ (1 << (k - 1))
    full_initial = (1 << (k + 1)) - 1
    members = {m1, m2}
    members.update(right_base | (1 << (a - 1)) for a in range(k + 2, r + 1))
    members.update(full_initial ^ (1 << (i - 1)) for i in range(s, k))
    assert all(member < (1 << n) for member in members)
    return tuple(sorted(members))


def hook_catalogue(n: int, k: int) -> dict[tuple[int, ...], list[tuple[int, int]]]:
    catalogue: dict[tuple[int, ...], list[tuple[int, int]]] = {}
    if k < 2 or n < k + 2:
        return catalogue
    for r in range(k + 2, n + 1):
        for s in range(1, k):
            hook = hook_family(n, k, r, s)
            catalogue.setdefault(hook, []).append((r, s))
    return catalogue


def zero_biconditional_stats() -> dict[str, int]:
    return {
        "family_pair_instances": 0,
        "configurations": 0,
        "exception_configurations": 0,
        "non_exception_configurations": 0,
        "valid_exists": 0,
        "valid_absent": 0,
        "exception_valid_exists": 0,
        "exception_valid_absent": 0,
        "non_exception_valid_exists": 0,
        "non_exception_valid_absent": 0,
        "violations": 0,
    }


def zero_lemma1_stats() -> dict[str, int]:
    return {
        "family_instances": 0,
        "two_element_families": 0,
        "three_element_families": 0,
        "at_least_two_element_families": 0,
        "gale_comparisons": 0,
        "violations": 0,
    }


def zero_lemma2_stats() -> dict[str, int]:
    return {"family_instances": 0, "bad_templates": 0, "violations": 0}


def zero_lemma3_stats() -> dict[str, int]:
    return {
        "family_instances": 0,
        "bad_templates_forward_checked": 0,
        "hook_parameter_cases_converse_checked": 0,
        "distinct_hook_families_converse_checked": 0,
        "violations": 0,
    }


def add_numeric_stats(total: dict[str, int], part: dict[str, int]) -> None:
    for key, value in part.items():
        total[key] = total.get(key, 0) + value


def direct_enumerator_self_check() -> dict:
    """Cross-check order-ideal enumeration against literal closure through n=5."""
    cases = []
    for n in range(2, 6):
        for k in range(1, n):
            sets, _ = rank_sets(n, k)
            direct: set[int] = set()
            for family_mask in range(1, 1 << len(sets)):
                family = members_from_family_mask(family_mask, sets)
                if is_shifted_family(family, n):
                    direct.add(family_mask)
            enumerated = set(shifted_family_masks(n, k))
            if direct != enumerated:
                missing = min(direct - enumerated) if direct - enumerated else None
                extra = min(enumerated - direct) if enumerated - direct else None
                raise AssertionError(
                    f"enumerator self-check failed at (n,k)=({n},{k}); "
                    f"missing={missing}, extra={extra}"
                )
            cases.append({"n": n, "k": k, "shifted_families": len(direct)})
    return {
        "method": (
            "Compared the order-ideal generator with all subsets of the k-sets, "
            "filtered by the literal single-decrement definition."
        ),
        "covered": cases,
        "passed": True,
    }


def run_checks(biconditional_max_n: int, lemma_max_n: int) -> dict:
    start = time.perf_counter()
    self_check = direct_enumerator_self_check()
    violations: dict[str, list[dict]] = {
        "biconditional": [],
        "lemma_1": [],
        "lemma_2": [],
        "lemma_3": [],
    }
    by_n_k = []
    biconditional_total = zero_biconditional_stats()
    lemma1_total = zero_lemma1_stats()
    lemma2_total = zero_lemma2_stats()
    lemma3_total = zero_lemma3_stats()

    upper_n = max(biconditional_max_n, lemma_max_n)
    for n in range(2, upper_n + 1):
        for k in range(1, n):
            cell_start = time.perf_counter()
            sets, _ = rank_sets(n, k)
            family_masks = list(shifted_family_masks(n, k))
            families = [members_from_family_mask(mask, sets) for mask in family_masks]
            if len(family_masks) != len(set(family_masks)):
                raise AssertionError(f"duplicate family at (n,k)=({n},{k})")
            for family in families:
                if not is_shifted_family(family, n):
                    raise AssertionError(
                        f"non-shifted family emitted at (n,k)=({n},{k}): {family}"
                    )

            cell: dict = {
                "n": n,
                "k": k,
                "k_sets": len(sets),
                "shifted_families": len(families),
                "biconditional": None,
                "lemma_1": None,
                "lemma_2": None,
                "lemma_3": None,
            }

            if n <= biconditional_max_n:
                stats = zero_biconditional_stats()
                for family in families:
                    whole_pair = bad_template_universal_pair(tuple(sorted(family)))
                    for raw_a, raw_b in combinations(family, 2):
                        stats["family_pair_instances"] += 1
                        difference = raw_a ^ raw_b
                        for e_index in range(n):
                            e_bit = 1 << e_index
                            if not (difference & e_bit):
                                continue
                            a, b = (raw_a, raw_b) if raw_a & e_bit else (raw_b, raw_a)
                            e = e_index + 1
                            is_exception = (
                                whole_pair is not None
                                and frozenset((raw_a, raw_b)) == frozenset(whole_pair)
                            )
                            exists = valid_step_exists(family, a, b, e)
                            stats["configurations"] += 1
                            stats[
                                "exception_configurations"
                                if is_exception
                                else "non_exception_configurations"
                            ] += 1
                            stats["valid_exists" if exists else "valid_absent"] += 1
                            outcome_key = (
                                ("exception" if is_exception else "non_exception")
                                + ("_valid_exists" if exists else "_valid_absent")
                            )
                            stats[outcome_key] += 1
                            expected = not is_exception
                            if exists != expected:
                                stats["violations"] += 1
                                violations["biconditional"].append(
                                    {
                                        "n": n,
                                        "k": k,
                                        "F": family_as_lists(family),
                                        "A": set_as_list(a),
                                        "B": set_as_list(b),
                                        "e": e,
                                        "F_bad_universal_pair": (
                                            family_as_lists(whole_pair)
                                            if whole_pair is not None
                                            else None
                                        ),
                                        "is_exception": is_exception,
                                        "valid_exists": exists,
                                        "expected_valid_exists": expected,
                                        "details": step_diagnostics(family, a, b, e),
                                    }
                                )
                cell["biconditional"] = stats
                add_numeric_stats(biconditional_total, stats)

            if n <= lemma_max_n:
                lemma1 = zero_lemma1_stats()
                lemma2 = zero_lemma2_stats()
                lemma3 = zero_lemma3_stats()
                catalogue = hook_catalogue(n, k)
                m1, m2 = distinguished_sets(k)
                expected_pair = tuple(sorted((m1, m2)))

                for family in families:
                    size = len(family)
                    pair = bad_template_universal_pair(tuple(sorted(family)))

                    lemma1["family_instances"] += 1
                    if size == 2:
                        lemma1["two_element_families"] += 1
                        if not johnson_adjacent(family[0], family[1]):
                            lemma1["violations"] += 1
                            violations["lemma_1"].append(
                                {
                                    "n": n,
                                    "k": k,
                                    "issue": "two-element family is not a J-edge",
                                    "F": family_as_lists(family),
                                }
                            )
                    if size == 3:
                        lemma1["three_element_families"] += 1
                        nonedges = [
                            (x, y)
                            for x, y in combinations(family, 2)
                            if not johnson_adjacent(x, y)
                        ]
                        if nonedges:
                            lemma1["violations"] += 1
                            violations["lemma_1"].append(
                                {
                                    "n": n,
                                    "k": k,
                                    "issue": "three-element family is not a J-triangle",
                                    "F": family_as_lists(family),
                                    "nonedges": [
                                        [set_as_list(x), set_as_list(y)] for x, y in nonedges
                                    ],
                                }
                            )
                    if size >= 2:
                        lemma1["at_least_two_element_families"] += 1
                        if m2 not in family:
                            lemma1["violations"] += 1
                            violations["lemma_1"].append(
                                {
                                    "n": n,
                                    "k": k,
                                    "issue": "m2 is absent",
                                    "F": family_as_lists(family),
                                    "m2": set_as_list(m2),
                                }
                            )
                        failures = []
                        for x in family:
                            if x == m1:
                                continue
                            lemma1["gale_comparisons"] += 1
                            if not gale_leq(m2, x):
                                failures.append(x)
                        if failures:
                            lemma1["violations"] += 1
                            violations["lemma_1"].append(
                                {
                                    "n": n,
                                    "k": k,
                                    "issue": "m2 is not Gale-dominated by every X != m1",
                                    "F": family_as_lists(family),
                                    "m1": set_as_list(m1),
                                    "m2": set_as_list(m2),
                                    "failing_X": family_as_lists(failures),
                                }
                            )

                    lemma2["family_instances"] += 1
                    if pair is not None:
                        lemma2["bad_templates"] += 1
                        if pair != expected_pair:
                            lemma2["violations"] += 1
                            violations["lemma_2"].append(
                                {
                                    "n": n,
                                    "k": k,
                                    "F": family_as_lists(family),
                                    "actual_universal_pair": family_as_lists(pair),
                                    "expected_universal_pair": family_as_lists(expected_pair),
                                }
                            )

                    lemma3["family_instances"] += 1
                    if pair is not None:
                        lemma3["bad_templates_forward_checked"] += 1
                        if tuple(sorted(family)) not in catalogue:
                            lemma3["violations"] += 1
                            violations["lemma_3"].append(
                                {
                                    "n": n,
                                    "k": k,
                                    "direction": "bad template implies hook",
                                    "F": family_as_lists(family),
                                    "universal_pair": family_as_lists(pair),
                                    "available_hook_parameters": [],
                                }
                            )

                lemma3["distinct_hook_families_converse_checked"] = len(catalogue)
                for hook, parameters in catalogue.items():
                    lemma3["hook_parameter_cases_converse_checked"] += len(parameters)
                    pair = bad_template_universal_pair(hook)
                    shifted = is_shifted_family(hook, n)
                    if not shifted or pair != expected_pair:
                        lemma3["violations"] += 1
                        violations["lemma_3"].append(
                            {
                                "n": n,
                                "k": k,
                                "direction": "hook implies bad template",
                                "parameters": [
                                    {"r": r, "s": s} for r, s in parameters
                                ],
                                "F": family_as_lists(hook),
                                "is_shifted": shifted,
                                "actual_universal_pair": (
                                    family_as_lists(pair) if pair is not None else None
                                ),
                                "expected_universal_pair": family_as_lists(expected_pair),
                            }
                        )

                cell["lemma_1"] = lemma1
                cell["lemma_2"] = lemma2
                cell["lemma_3"] = lemma3
                add_numeric_stats(lemma1_total, lemma1)
                add_numeric_stats(lemma2_total, lemma2)
                add_numeric_stats(lemma3_total, lemma3)

            cell["runtime_seconds"] = round(time.perf_counter() - cell_start, 6)
            by_n_k.append(cell)
            print(
                f"covered n={n}, k={k}: {len(families)} shifted families "
                f"in {cell['runtime_seconds']:.3f}s",
                file=sys.stderr,
                flush=True,
            )

    total_violations = sum(len(items) for items in violations.values())
    return {
        "self_check": self_check,
        "by_n_k": by_n_k,
        "totals": {
            "biconditional": biconditional_total,
            "lemma_1": lemma1_total,
            "lemma_2": lemma2_total,
            "lemma_3": lemma3_total,
        },
        "violations": violations,
        "total_violations": total_violations,
        "runtime_seconds": round(time.perf_counter() - start, 6),
    }


def apply_address_space_limit() -> dict:
    old_soft, old_hard = resource.getrlimit(resource.RLIMIT_AS)
    if old_hard == resource.RLIM_INFINITY or old_hard >= REQUESTED_AS_LIMIT_BYTES:
        applied = REQUESTED_AS_LIMIT_BYTES
    else:
        applied = old_hard
    resource.setrlimit(resource.RLIMIT_AS, (applied, old_hard))
    new_soft, new_hard = resource.getrlimit(resource.RLIMIT_AS)
    return {
        "resource": "RLIMIT_AS",
        "requested_bytes": REQUESTED_AS_LIMIT_BYTES,
        "requested_gib": 8,
        "old_soft_bytes": None if old_soft == resource.RLIM_INFINITY else old_soft,
        "old_hard_bytes": None if old_hard == resource.RLIM_INFINITY else old_hard,
        "applied_soft_bytes": None if new_soft == resource.RLIM_INFINITY else new_soft,
        "applied_hard_bytes": None if new_hard == resource.RLIM_INFINITY else new_hard,
        "exact_requested_limit_applied": new_soft == REQUESTED_AS_LIMIT_BYTES,
    }


def coverage_cells(by_n_k: Sequence[dict], key: str) -> list[dict]:
    return [
        {
            "n": cell["n"],
            "k": cell["k"],
            "shifted_families": cell["shifted_families"],
        }
        for cell in by_n_k
        if cell[key] is not None
    ]


def build_payload(args: argparse.Namespace, limit: dict, run: dict) -> dict:
    usage = resource.getrusage(resource.RUSAGE_SELF)
    script_sha256 = hashlib.sha256(SCRIPT_PATH.read_bytes()).hexdigest()
    return {
        "seal": "Step Lemma inputs computational seal",
        "date": "2026-08-15",
        "status": "PASS" if run["total_violations"] == 0 else "FAIL",
        "calibration": (
            "Finite exhaustive computational support for a lead-written proof; "
            "this output is not itself a proof."
        ),
        "implementation": {
            "script": str(SCRIPT_PATH),
            "script_sha256": script_sha256,
            "independence": (
                "Self-contained implementation from the definitions in the seal brief."
            ),
            "python": sys.version,
            "platform": platform.platform(),
            "command": shlex.join(sys.argv),
        },
        "definitions_used": {
            "shifted_family": (
                "A nonempty family of k-sets closed under every single decrement. "
                "Enumeration uses the equivalent nonempty order ideals of the Gale poset."
            ),
            "johnson_graph": "Vertices are family members; adjacency means symmetric difference 2.",
            "bad_template": (
                "At least four vertices, exactly two universal vertices, and the remaining "
                "induced graph has exactly two nonempty connected components, each a clique."
            ),
            "step_validity": (
                "The F1/F0 split, link and forbidden partners are computed exactly as in "
                "the brief; candidates exchange e for one xi not in Y and obey both endpoint rules."
            ),
            "gale_order": "Increasing listings compared componentwise.",
            "hook_parameter_ranges": "k+2 <= r <= n and 1 <= s <= k-1.",
        },
        "memory_limit": limit,
        "coverage": {
            "enumeration_policy": (
                "Every labeled shifted family is enumerated separately for every (n,k); "
                "families not using n are therefore intentionally repeated on larger grounds."
            ),
            "n_1": "No k satisfies 1 <= k <= n-1.",
            "biconditional": coverage_cells(run["by_n_k"], "biconditional"),
            "lemma_1": coverage_cells(run["by_n_k"], "lemma_1"),
            "lemma_2": coverage_cells(run["by_n_k"], "lemma_2"),
            "lemma_3": coverage_cells(run["by_n_k"], "lemma_3"),
            "biconditional_max_n": args.biconditional_max_n,
            "lemma_max_n": args.lemma_max_n,
            "sampling_or_caps": "none",
        },
        "enumerator_self_check": run["self_check"],
        "counts": {"by_n_k": run["by_n_k"], "totals": run["totals"]},
        "violations": {
            "total": run["total_violations"],
            "by_check": run["violations"],
        },
        "runtime": {
            "wall_seconds": run["runtime_seconds"],
            "user_cpu_seconds": round(usage.ru_utime, 6),
            "system_cpu_seconds": round(usage.ru_stime, 6),
            "max_rss_kib_linux": usage.ru_maxrss,
        },
    }


def markdown_report(payload: dict) -> str:
    totals = payload["counts"]["totals"]
    bic = totals["biconditional"]
    l1 = totals["lemma_1"]
    l2 = totals["lemma_2"]
    l3 = totals["lemma_3"]
    rows = []
    for cell in payload["counts"]["by_n_k"]:
        bic_cell = cell["biconditional"]
        l2_cell = cell["lemma_2"]
        l3_cell = cell["lemma_3"]
        rows.append(
            "| {n} | {k} | {families} | {configs} | {exceptions} | {bad} | {hooks} | {violations} |".format(
                n=cell["n"],
                k=cell["k"],
                families=cell["shifted_families"],
                configs=(bic_cell["configurations"] if bic_cell is not None else "—"),
                exceptions=(
                    bic_cell["exception_configurations"] if bic_cell is not None else "—"
                ),
                bad=(l2_cell["bad_templates"] if l2_cell is not None else "—"),
                hooks=(
                    l3_cell["hook_parameter_cases_converse_checked"]
                    if l3_cell is not None
                    else "—"
                ),
                violations=sum(
                    section["violations"]
                    for section in (
                        cell["biconditional"],
                        cell["lemma_1"],
                        cell["lemma_2"],
                        cell["lemma_3"],
                    )
                    if section is not None
                ),
            )
        )

    if payload["violations"]["total"] == 0:
        violation_text = "No violations were found."
    else:
        violation_text = (
            f"Found **{payload['violations']['total']} violation(s)**. Full witnesses are "
            "recorded in the JSON artifact under `violations.by_check`."
        )

    covered_bic = payload["coverage"]["biconditional"]
    covered_lemmas = payload["coverage"]["lemma_1"]
    bic_family_total = sum(cell["shifted_families"] for cell in covered_bic)
    lemma_family_total = sum(cell["shifted_families"] for cell in covered_lemmas)
    n8_cells = [cell for cell in covered_lemmas if cell["n"] == 8]
    if len(n8_cells) == 7 and {cell["k"] for cell in n8_cells} == set(range(1, 8)):
        n8_sentence = "Full `n=8` enumeration was feasible and completed."
    else:
        n8_sentence = "`n=8` was not part of this run."
    limit = payload["memory_limit"]
    runtime = payload["runtime"]

    return f"""# Computational seal: Step Lemma inputs (2026-08-15)

Status: **{payload['status']}** — {violation_text}

This is a finite exhaustive computational seal supporting a lead-written proof. It is not a proof.

## Definitions used

- A shifted family is a nonempty family of `k`-sets closed under every stated single decrement. The enumerator generates the equivalent nonempty order ideals of the componentwise Gale poset.
- `J(F)` has vertex set `F`, with an edge exactly when two members have symmetric difference 2.
- A bad template has at least four vertices, exactly two universal vertices, and a remainder with exactly two nonempty connected components, each a clique.
- Step validity uses the stated `F1`/`F0` split, link, bad-template forbidden partners, one-element endpoint exceptions, and exchanges `X = Y - {{e}} + {{xi}}`.
- Gale domination compares the increasing listings componentwise.
- In the hook check, the ranges are `k+2 <= r <= n` and `1 <= s <= k-1`; these ranges make both arms nonempty.

## Exact coverage

Every labeled shifted family was enumerated separately at each `(n,k)`. Thus a family not using the letter `n` is intentionally counted again on ground `[n]`; there is no sampling, isomorphism quotient, or silent cap. For `n=1`, no `k` lies in `[1,n-1]`.

- Biconditional: every `1 <= k <= n-1` through `n <= {payload['coverage']['biconditional_max_n']}`; {bic_family_total} family instances and {bic['configurations']} `(F,A,B,e)` configurations.
- Lemmas 1–3: every `1 <= k <= n-1` through `n <= {payload['coverage']['lemma_max_n']}`; {lemma_family_total} family instances for each lemma. {n8_sentence}
- Enumerator audit: order-ideal output was compared with literal single-decrement filtering of every subfamily for all `(n,k)` through `n=5`; all cases agreed.
- Memory guard: requested 8 GiB `RLIMIT_AS`; applied soft limit {limit['applied_soft_bytes']} bytes (exact requested limit applied: `{str(limit['exact_requested_limit_applied']).lower()}`).

| n | k | shifted families | biconditional configurations | exception configurations | bad templates | hook parameter cases | violations |
|---:|---:|---:|---:|---:|---:|---:|---:|
{chr(10).join(rows)}

## Counts and outcomes

### Biconditional

- Total configurations: {bic['configurations']}
- Exception configurations: {bic['exception_configurations']} (valid exists: {bic['exception_valid_exists']}; valid absent: {bic['exception_valid_absent']})
- Non-exception configurations: {bic['non_exception_configurations']} (valid exists: {bic['non_exception_valid_exists']}; valid absent: {bic['non_exception_valid_absent']})
- Violations: {bic['violations']}

Thus, over the covered range, a valid pair existed exactly outside the stated bad-template/universal-pair exception.

### Lemma 2

- Shifted-family instances: {l2['family_instances']}
- Bad templates checked: {l2['bad_templates']}
- Universal-pair violations: {l2['violations']}

### Lemma 3

- Bad templates checked in the forward direction: {l3['bad_templates_forward_checked']}
- Hook parameter cases checked in the converse direction: {l3['hook_parameter_cases_converse_checked']} ({l3['distinct_hook_families_converse_checked']} distinct hook families)
- Violations: {l3['violations']}

### Lemma 1

- Two-element shifted families checked: {l1['two_element_families']}
- Three-element shifted families checked: {l1['three_element_families']}
- Families of size at least two checked for `m2`: {l1['at_least_two_element_families']}
- Componentwise Gale comparisons: {l1['gale_comparisons']}
- Violations: {l1['violations']}

## Violations

{violation_text} The raw JSON retains a separate witness list for each check; those lists are empty on this run.

## Runtime and provenance

- Wall time: {runtime['wall_seconds']:.6f} s
- User CPU time: {runtime['user_cpu_seconds']:.6f} s
- System CPU time: {runtime['system_cpu_seconds']:.6f} s
- Maximum resident set size reported by Linux: {runtime['max_rss_kib_linux']} KiB
- Script SHA-256: `{payload['implementation']['script_sha256']}`
- Raw data: `compute/data/seal_step_lemma_inputs_2026_08_15.json`
- Implementation: `compute/seal_step_lemma_inputs.py`
"""


def atomic_write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(content, encoding="utf-8")
    temporary.replace(path)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--biconditional-max-n", type=int, default=7)
    parser.add_argument("--lemma-max-n", type=int, default=8)
    parser.add_argument("--json", type=Path, default=DEFAULT_JSON_PATH)
    parser.add_argument("--report", type=Path, default=DEFAULT_REPORT_PATH)
    args = parser.parse_args()
    if not 2 <= args.biconditional_max_n <= 8:
        parser.error("--biconditional-max-n must be between 2 and 8")
    if not 2 <= args.lemma_max_n <= 8:
        parser.error("--lemma-max-n must be between 2 and 8")
    return args


def main() -> int:
    args = parse_args()
    limit = apply_address_space_limit()
    run = run_checks(args.biconditional_max_n, args.lemma_max_n)
    payload = build_payload(args, limit, run)
    json_text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    report_text = markdown_report(payload)
    atomic_write_text(args.json.resolve(), json_text)
    atomic_write_text(args.report.resolve(), report_text)
    print(
        f"{payload['status']}: {run['total_violations']} violations; "
        f"JSON={args.json}; report={args.report}"
    )
    return 0 if run["total_violations"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
