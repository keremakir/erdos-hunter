import time
import numpy as np
import networkx as nx
from erdos128_check import (
    exact_min_edges_subset,
    exact_continuous_blowup_uniform,
    is_triangle_free,
)
from erdos128_deep_search import (
    exact_weighted_blowup_limit,
    optimize_weights_for_graph,
)


def generalized_petersen(n: int, k: int) -> nx.Graph:
    G = nx.Graph()
    G.add_nodes_from(range(2 * n))
    for i in range(n):
        G.add_edge(i, (i + 1) % n)
        G.add_edge(i, n + i)
        G.add_edge(n + i, n + ((i + k) % n))
    return G


def main():
    t0 = time.time()
    print("=== GENERALIZED PETERSEN GP(n, k) TRIANGLE-FREE CHECK ===")
    best_gp = (0.0, "")
    for n in range(5, 12):
        for k in range(1, (n - 1) // 2 + 1):
            G = generalized_petersen(n, k)
            A = nx.to_numpy_array(G, dtype=int)
            if not is_triangle_free(A):
                continue
            N = 2 * n
            if N <= 22:
                ef, _ = exact_min_edges_subset(A, N // 2)
                bl = ef / (N * N)
                if bl >= 0.015:
                    print(f"GP({n},{k}) (N={N:2d}): floor_e={ef}, ratio={bl:.6f}")
                if bl > best_gp[0]:
                    best_gp = (bl, f"GP({n},{k})")
    print(f"Best GP(n,k): {best_gp}")

    print("\n=== TWISTED 3-LIFTS OF C5 (k=15) & MAXIMAL TF COMPLETIONS ===")
    rng = np.random.default_rng(2026)
    C5 = nx.cycle_graph(5)
    best_15 = (0.0, "")
    for trial in range(25):
        # Random 3-lift of C5 (each C5 edge gets a random permutation matching of size 3, OR complement of matching)
        A = np.zeros((15, 15), dtype=int)
        for u, v in C5.edges():
            perm = rng.permutation(3)
            if trial % 2 == 0:
                for a in range(3):
                    b = perm[a]
                    A[3*u + a, 3*v + b] = A[3*v + b, 3*u + a] = 1
            else:
                for a in range(3):
                    for b in range(3):
                        if b != perm[a]:
                            A[3*u + a, 3*v + b] = A[3*v + b, 3*u + a] = 1
        while True:
            common = A @ A
            np.fill_diagonal(common, 1)
            cands = np.argwhere(np.triu((A == 0) & (common == 0), 1))
            if len(cands) == 0:
                break
            a, b = cands[rng.integers(len(cands))]
            A[a, b] = A[b, a] = 1
        val, _ = exact_continuous_blowup_uniform(A)
        if val > best_15[0]:
            best_15 = (val, f"trial={trial}, edges={A.sum()//2}")
        if val > 0.020001:
            print(f"!!! BEAT 0.02 at k=15: {val:.6f} !!!", flush=True)
    print(f"Best twisted C5 3-lift completion (k=15): {best_15}", flush=True)

    print("\n=== TWISTED 2-LIFTS OF PETERSEN (k=20) ===", flush=True)
    P = nx.petersen_graph()
    p_edges = list(P.edges())
    best_20 = (0.0, "")
    for trial in range(15):
        A = np.zeros((20, 20), dtype=int)
        for u, v in p_edges:
            if rng.random() < 0.5:
                A[2*u, 2*v] = A[2*v, 2*u] = 1
                A[2*u+1, 2*v+1] = A[2*v+1, 2*u+1] = 1
            else:
                A[2*u, 2*v+1] = A[2*v+1, 2*u] = 1
                A[2*u+1, 2*v] = A[2*v, 2*u+1] = 1
        while True:
            common = A @ A
            np.fill_diagonal(common, 1)
            cands = np.argwhere(np.triu((A == 0) & (common == 0), 1))
            if len(cands) == 0:
                break
            a, b = cands[rng.integers(len(cands))]
            A[a, b] = A[b, a] = 1
        ef, _ = exact_min_edges_subset(A, 10)
        val = ef / 400.0
        if val > best_20[0]:
            best_20 = (val, f"trial={trial}, e_min={ef}, edges={A.sum()//2}")
    print(f"Best twisted Petersen 2-lift completion (k=20): {best_20}")
    print(f"Done in {time.time() - t0:.2f}s")


if __name__ == "__main__":
    main()
