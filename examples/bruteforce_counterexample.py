#!/usr/bin/env python3
"""Brute-force check for the extremal graph counterexample.

This is intentionally small and dependency-free. It enumerates all simple
graphs on n labeled vertices for n <= 6 and computes the three extremal values
used in the README proof.
"""

from itertools import combinations


def all_edges(n):
    return list(combinations(range(n), 2))


def graph_from_mask(candidate_edges, mask):
    return [
        edge
        for index, edge in enumerate(candidate_edges)
        if mask & (1 << index)
    ]


def contains_two_edge_star(n, edges):
    degree = [0] * n
    for u, v in edges:
        degree[u] += 1
        degree[v] += 1
    return any(d >= 2 for d in degree)


def contains_two_disjoint_edges(edges):
    for first, second in combinations(edges, 2):
        if len(set(first + second)) == 4:
            return True
    return False


def extremal(n, is_allowed):
    candidate_edges = all_edges(n)
    best_count = -1
    best_edges = []

    for mask in range(1 << len(candidate_edges)):
        edges = graph_from_mask(candidate_edges, mask)
        if is_allowed(n, edges) and len(edges) > best_count:
            best_count = len(edges)
            best_edges = edges

    return best_count, best_edges


def free_of_k12(n, edges):
    return not contains_two_edge_star(n, edges)


def free_of_2k2(_n, edges):
    return not contains_two_disjoint_edges(edges)


def free_of_family(n, edges):
    return free_of_k12(n, edges) and free_of_2k2(n, edges)


def expected_2k2_value(n):
    if n <= 1:
        return 0
    if n == 2:
        return 1
    if n == 3:
        return 3
    return n - 1


def main():
    print(
        "n  ex(K1,2)  witness            "
        "ex(2K2)  witness                  ex(F)  witness"
    )

    for n in range(7):
        k12_count, k12_witness = extremal(n, free_of_k12)
        two_k2_count, two_k2_witness = extremal(n, free_of_2k2)
        family_count, family_witness = extremal(n, free_of_family)

        assert k12_count == n // 2
        assert two_k2_count == expected_2k2_value(n)
        assert family_count == (0 if n <= 1 else 1)

        print(
            f"{n:<2} {k12_count:<9} {str(k12_witness):<18} "
            f"{two_k2_count:<8} {str(two_k2_witness):<24} "
            f"{family_count:<6} {family_witness}"
        )

    print()
    print("Concrete n=4 interpretation:")
    print("  K1,2-free extremal graph: [(0, 1), (2, 3)]")
    print("  2K2-free extremal graph:  [(0, 1), (0, 2), (0, 3)]")
    print("  Family-free extremal graph: [(0, 1)]")


if __name__ == "__main__":
    main()
