import itertools
import math
import time
import numpy as np
import networkx as nx
from erdos128_check import is_triangle_free


def multi_start_sa_small_n(n: int, m: int, restarts: int = 8, steps: int = 600, seed: int = 42) -> tuple[int, int]:
    rng = np.random.default_rng(seed)
    all_subs = np.array(list(itertools.combinations(range(n), m)))
    S = np.zeros((len(all_subs), n), dtype=np.float32)
    S[np.repeat(np.arange(len(all_subs)), m), all_subs.ravel()] = 1.0

    def eval_mat(mat):
        mat_f = mat.astype(np.float32)
        vals = ((S @ mat_f) * S).sum(axis=1) * 0.5
        min_v = int(round(float(vals.min())))
        cnt = int((vals <= min_v + 0.1).sum())
        return min_v, min_v - 0.00001 * cnt

    best_e = 0
    best_edges = 0
    for r in range(restarts):
        A = np.zeros((n, n), dtype=int)
        if r == 0 and n == 10:
            A = nx.to_numpy_array(nx.petersen_graph(), dtype=int)
        elif r == 0 and n == 11:
            A = nx.to_numpy_array(nx.circulant_graph(11, [1, 4]), dtype=int)
        elif r == 0 and n == 12:
            A = nx.to_numpy_array(nx.chvatal_graph(), dtype=int)
        elif r == 0 and n == 13:
            A = nx.to_numpy_array(nx.circulant_graph(13, [1, 5]), dtype=int)
        else:
            while True:
                common = A @ A
                np.fill_diagonal(common, 1)
                cands = np.argwhere(np.triu((A == 0) & (common == 0), 1))
                if len(cands) == 0:
                    break
                a, b = cands[rng.integers(len(cands))]
                A[a, b] = A[b, a] = 1
        assert is_triangle_free(A)
        e_v, cur_s = eval_mat(A)
        if e_v > best_e:
            best_e = e_v
            best_edges = int(A.sum()) // 2

        for step in range(steps):
            B = A.copy()
            ones = np.argwhere(np.triu(B, 1) == 1)
            if len(ones) == 0:
                break
            a, b = ones[rng.integers(len(ones))]
            B[a, b] = B[b, a] = 0
            if rng.random() < 0.3 and len(ones) > 1:
                a2, b2 = ones[rng.integers(len(ones))]
                B[a2, b2] = B[b2, a2] = 0
            while True:
                common = B @ B
                np.fill_diagonal(common, 1)
                cands = np.argwhere(np.triu((B == 0) & (common == 0), 1))
                if len(cands) == 0:
                    break
                u, v = cands[rng.integers(len(cands))]
                B[u, v] = B[v, u] = 1
            nv_e, nv_s = eval_mat(B)
            if nv_s >= cur_s or rng.random() < 0.05:
                A = B
                cur_s = nv_s
                if nv_e > best_e:
                    best_e = nv_e
                    best_edges = int(A.sum()) // 2
    return best_e, best_edges


def main():
    t0 = time.time()
    print("=== CLEAN MULTI-START MAXIMAL-TF SA FOR n=8..16 (EXACT LEAN m=floor(n/2)) ===")
    for n in range(8, 17):
        m_lean = n // 2
        req = (n * n) // 50 + 1
        best_e, best_edges = multi_start_sa_small_n(n, m_lean, restarts=8, steps=500, seed=500 + n)
        print(f"n={n:2d} (m_lean={m_lean}): best min_e = {best_e:2d} (ratio={best_e/(n*n):.6f}), req >= {req:2d} -> Lean CE? {best_e >= req} (|E|={best_edges})")
    print(f"Done in {time.time() - t0:.2f}s")


if __name__ == "__main__":
    main()
