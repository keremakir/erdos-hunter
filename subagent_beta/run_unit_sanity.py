import itertools
import numpy as np
import networkx as nx
from erdos628_check import is_k_colorable, exact_chromatic_number
from erdos128_deep_search import exact_weighted_blowup_limit


def brute_force_k_colorable(G: nx.Graph, k: int) -> bool:
    n = G.number_of_nodes()
    edges = list(G.edges())
    for cols in itertools.product(range(k), repeat=n):
        if all(cols[u] != cols[v] for u, v in edges):
            return True
    return False


def main():
    # 1. Verify is_k_colorable against brute force on 50 random graphs (n=7..8, k=3..5)
    rng = np.random.default_rng(1234)
    for trial in range(50):
        n = int(rng.integers(6, 9))
        G = nx.erdos_renyi_graph(n, rng.uniform(0.3, 0.85), seed=trial)
        adj_list = [list(G.neighbors(u)) for u in range(n)]
        for k in [3, 4, 5]:
            got = is_k_colorable(adj_list, n, k)
            exp = brute_force_k_colorable(G, k)
            assert got == exp, f"Mismatch at trial={trial}, n={n}, k={k}: got {got}, exp {exp}"

    # Verify the false-positive n=9 graph caught earlier truly has chi=5
    G_fp = nx.Graph()
    G_fp.add_nodes_from(range(9))
    G_fp.add_edges_from([(0, 1), (0, 3), (0, 4), (0, 7), (1, 3), (1, 4), (1, 7), (2, 8), (3, 4), (3, 7), (4, 5), (4, 6), (4, 7), (6, 8)])
    assert exact_chromatic_number(G_fp) == 5

    # 2. Verify exact_weighted_blowup_limit on random w against random feasible x sampling
    c5 = nx.to_numpy_array(nx.cycle_graph(5), dtype=float)
    pet = nx.to_numpy_array(nx.petersen_graph(), dtype=float)
    for A in [c5, pet]:
        k = A.shape[0]
        for s in range(10):
            w = rng.uniform(0.05, 0.3, size=k)
            w /= w.sum()
            exact_val = exact_weighted_blowup_limit(A, w)
            # Sample 1000 feasible x with 0 <= x <= w and sum(x) = 0.5 via hit-and-run / rejection
            min_sampled = 1e9
            for _ in range(1000):
                # Start with x = 0.5 * w, then random feasible swaps
                x = 0.5 * w.copy()
                for _ in range(20):
                    i, j = rng.choice(k, size=2, replace=False)
                    max_add = min(w[i] - x[i], x[j])
                    max_sub = min(x[i], w[j] - x[j])
                    delta = rng.uniform(-max_sub, max_add)
                    x[i] += delta
                    x[j] -= delta
                val = 0.5 * float(x @ A @ x)
                if val < min_sampled:
                    min_sampled = val
            assert exact_val <= min_sampled + 1e-11, f"Exact {exact_val} > sampled {min_sampled}"

    print("ALL 50 brute-force coloring checks, false-positive check, and 20 continuous blowup bounds PASSED!")


if __name__ == "__main__":
    main()
