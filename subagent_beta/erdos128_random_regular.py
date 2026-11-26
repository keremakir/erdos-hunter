import time
import numpy as np
import networkx as nx
from erdos128_check import exact_min_edges_subset, is_triangle_free
from erdos128_srg_test import sa_min_subset_edges


def random_d_regular_triangle_free(n: int, d: int, seed: int = 0) -> np.ndarray | None:
    rng = np.random.default_rng(seed)
    # Try configuration model / switching from a triangle-free d-regular start or greedy random matching
    for attempt in range(200):
        A = np.zeros((n, n), dtype=int)
        degs = np.zeros(n, dtype=int)
        ok = True
        while np.any(degs < d):
            # Pick vertex with minimum degree
            min_d = int(degs.min())
            u_cands = np.where(degs == min_d)[0]
            u = int(rng.choice(u_cands))
            # Valid neighbors: deg < d, not u, not already adjacent, no common neighbor with u
            common = A[u] @ A
            valid = [v for v in range(n) if v != u and degs[v] < d and A[u, v] == 0 and common[v] == 0]
            if not valid:
                ok = False
                break
            # Prefer vertices with smaller degree
            min_vd = min(degs[v] for v in valid)
            best_v = [v for v in valid if degs[v] <= min_vd + 1]
            v = int(rng.choice(best_v))
            A[u, v] = A[v, u] = 1
            degs[u] += 1
            degs[v] += 1
        if ok and np.all(degs == d) and is_triangle_free(A):
            return A
    return None


def main():
    t0 = time.time()
    print("=== RANDOM REGULAR TRIANGLE-FREE GRAPHS ===")
    configs = [(10, 3), (12, 4), (14, 4), (16, 5), (18, 5), (20, 6), (24, 6), (30, 7)]
    for n, d in configs:
        best_ratio = 0.0
        found = 0
        for trial in range(15):
            A = random_d_regular_triangle_free(n, d, seed=1000 * n + trial)
            if A is None:
                continue
            found += 1
            if n <= 18:
                e_min, _ = exact_min_edges_subset(A, n // 2)
            else:
                e_min, _ = sa_min_subset_edges(A, n // 2, restarts=10, steps=1500, seed=trial)
            ratio = e_min / (n * n)
            if ratio > best_ratio:
                best_ratio = ratio
        print(f"(n={n:2d}, d={d}): generated={found:2d}/15 | max min_e(n/2)/n^2 = {best_ratio:.6f} (1/50=0.020000)")
    print(f"Done in {time.time() - t0:.2f}s")


if __name__ == "__main__":
    main()
