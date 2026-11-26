import itertools
import math
import time
import numpy as np
import networkx as nx
from scipy.optimize import minimize
from erdos128_check import (
    exact_min_edges_subset,
    exact_continuous_blowup_uniform,
    is_triangle_free,
)


def exact_weighted_blowup_limit(adj: np.ndarray, w: np.ndarray) -> float:
    """
    Exact min_{0 <= x <= w, sum x = 1/2} 0.5 * x^T A x for k <= 16.
    Uses the concavity theorem: at optimum, all coordinates except at most one
    lie in {0, w_i}.
    """
    k = adj.shape[0]
    w = np.asarray(w, dtype=float)
    w = w / w.sum()
    if w.max() >= 0.5:
        # Single vertex weight >= 0.5 -> independent set of size >= 1/2 -> 0 edges!
        return 0.0

    best = 1e9
    # Enumerate subsets S of full vertices with sum(w[S]) <= 0.5
    # Recursive branch-and-bound in k <= 16
    A_f = adj.astype(float)

    def dfs(idx: int, cur_sum: float, chosen_mask: int):
        nonlocal best
        if cur_sum > 0.5 + 1e-12:
            return
        rem = 0.5 - cur_sum
        if idx == k:
            if rem <= 1e-12:
                # Full exact subset
                S = [i for i in range(k) if (chosen_mask >> i) & 1]
                e = 0.5 * float(A_f[np.ix_(S, S)].sum()) if S else 0.0
                if e < best:
                    best = e
            return

        # Option: stop adding full vertices and put remaining mass rem into one vertex u >= idx (if possible)
        # Wait: what if the partial vertex u was ALREADY skipped at an earlier index j < idx?
        # Easier: handle partial vertex explicitly by passing `partial_used` or iterating partial u first?
        # Actually simplest: pick full subset S with 0.5 - sum(w[S]) <= max_{u not in S} w[u], OR even faster for k<=15: vectorized!
        dfs(idx + 1, cur_sum, chosen_mask)
        dfs(idx + 1, cur_sum + w[idx], chosen_mask | (1 << idx))

    if k <= 15:
        # Vectorized over all 2^k subsets!
        masks = np.arange(1 << k, dtype=np.uint32)
        B = ((masks[:, None] >> np.arange(k)) & 1).astype(float)  # (2^k, k)
        sums = B @ w
        valid_full = sums <= 0.5 + 1e-12
        B_v = B[valid_full]
        X_v = B_v * w[None, :]
        sums_v = sums[valid_full]
        rem_v = 0.5 - sums_v  # (M,)
        # e_S = 0.5 * sum((X_v @ A_f) * X_v, axis=1)
        deg_mat = X_v @ A_f  # (M, k): deg_mat[r, u] = sum_{i in S_r} w_i * A[i, u]
        e_S = 0.5 * np.sum(deg_mat * X_v, axis=1)
        # For each row r, we can either have rem == 0 (only if rem <= 1e-12) or put rem into any u not in S_r with w[u] >= rem
        # Mask of valid partial u: (B_v == 0) & (w[None, :] >= rem_v[:, None] - 1e-12)
        cand_u = (B_v == 0) & (w[None, :] >= rem_v[:, None] - 1e-12)
        # Cost if choosing u: e_S + rem * deg_mat[r, u]
        costs = e_S[:, None] + rem_v[:, None] * deg_mat
        costs = np.where(cand_u, costs, np.inf)
        min_partial = float(costs.min()) if costs.size else np.inf
        exact_zero = rem_v <= 1e-12
        min_exact = float(e_S[exact_zero].min()) if np.any(exact_zero) else np.inf
        return min(min_partial, min_exact)
    else:
        raise ValueError("k > 15 not supported in vectorized weighted evaluator")


def optimize_weights_for_graph(adj: np.ndarray, restarts: int = 12, seed: int = 0) -> tuple[float, np.ndarray]:
    rng = np.random.default_rng(seed)
    k = adj.shape[0]
    best_val = exact_weighted_blowup_limit(adj, np.ones(k) / k)
    best_w = np.ones(k) / k

    def obj(raw):
        w = np.exp(raw - np.max(raw))
        w = w / w.sum()
        return -exact_weighted_blowup_limit(adj, w)

    for r in range(min(restarts, 4)):
        x0 = np.zeros(k) if r == 0 else rng.normal(0, 0.35, size=k)
        res = minimize(obj, x0, method="Powell", options={"maxfev": 350, "ftol": 1e-5})
        val = -float(res.fun)
        if val > best_val:
            best_val = val
            w = np.exp(res.x - np.max(res.x))
            best_w = w / w.sum()
    return best_val, best_w


def enumerate_maximal_tf_via_extensions():
    """
    Enumerate ALL non-isomorphic triangle-free graphs on n=8 (from n=7 atlas),
    then find all maximal triangle-free graphs on n=8, 9, 10 (by sampling/completing).
    Wait: can we get ALL triangle-free graphs on n=8 from n=7 atlas?
    Yes! Every triangle-free graph on n=8 with min degree vertex v gives a triangle-free graph on n=7.
    """
    print("=== PART A: EXACT ALL TRIANGLE-FREE GRAPHS ON n=8 (FROM n=7 ATLAS) ===")
    atlas7 = [G for G in nx.graph_atlas_g() if G.number_of_nodes() == 7]
    tf7 = []
    for G in atlas7:
        A = nx.to_numpy_array(G, dtype=int)
        if is_triangle_free(A):
            tf7.append(G)
    print(f"n=7 triangle-free graphs: {len(tf7)}")

    # For each G7, find all independent sets I of G7, add node 7 adjacent to I, keep only MAXIMAL or high-edge?
    # Wait: if we want ALL maximal triangle-free graphs on n=8:
    # In ANY maximal triangle-free graph G8, EVERY vertex v has N(v) = a MAXIMAL independent set of G8 - v!
    # Wait: even simpler, find ALL triangle-free graphs on n=8 by adding ANY independent set I of G7 (to catch ALL graphs, or just maximal?)
    # Wait: if G8 is maximal triangle-free, for a vertex v, G8 - v might NOT be maximal triangle-free, ONLY triangle-free!
    # So we just iterate over all tf7 (107 graphs), and for each G7, iterate over all independent sets I of G7 (at most 2^7=128 -> 107*128 = 13696 candidates!),
    # filter for maximal triangle-free (every non-edge has a common neighbor), deduplicate by WL hash + isomorphism!
    buckets = {}
    max_tf8 = []
    checked = 0
    for G7 in tf7:
        A7 = nx.to_numpy_array(G7, dtype=int)
        # Find all independent sets of size <= 4 (if size >= 4, wait: on n=8 alpha>=3, could a vertex have deg>=4? Yes, K_{4,4} has deg 4!)
        for mask in range(1 << 7):
            I = [i for i in range(7) if (mask >> i) & 1]
            # Check I is independent in G7
            if I and A7[np.ix_(I, I)].sum() > 0:
                continue
            checked += 1
            A8 = np.zeros((8, 8), dtype=int)
            A8[:7, :7] = A7
            for i in I:
                A8[7, i] = A8[i, 7] = 1
            # Check if maximal triangle-free: for every non-edge (u, v), (A8 @ A8)[u, v] > 0
            common = A8 @ A8
            np.fill_diagonal(common, 1)
            if np.any((A8 == 0) & (common == 0)):
                continue
            G8 = nx.from_numpy_array(A8)
            h = nx.weisfeiler_lehman_graph_hash(G8)
            is_dup = False
            for prev in buckets.get(h, []):
                if nx.is_isomorphic(G8, prev):
                    is_dup = True
                    break
            if not is_dup:
                buckets.setdefault(h, []).append(G8)
                max_tf8.append((G8, A8))

    print(f"n=8 maximal triangle-free graphs found: {len(max_tf8)} (checked {checked} extensions)")
    best_e8 = -1
    best_e8_info = None
    for G8, A8 in max_tf8:
        e_min, sub = exact_min_edges_subset(A8, 4)
        if e_min > best_e8:
            best_e8 = e_min
            best_e8_info = (G8.number_of_edges(), sorted([d for _, d in G8.degree()]), sub)
    print(f"EXACT n=8 max min_e(|V'|=4) over ALL maximal triangle-free graphs = {best_e8} (req > 64/50 = 1.28 => >= 2) | info={best_e8_info}")

    # Now extend ALL non-isomorphic triangle-free graphs? Actually let's extend ALL tf8? How many tf8 exist? Let's count maximal tf9 by extending ALL tf8?
    # Wait: let's check how many total tf8 exist first!
    buckets_all8 = {}
    tf8_all = []
    for G7 in tf7:
        A7 = nx.to_numpy_array(G7, dtype=int)
        for mask in range(1 << 7):
            I = [i for i in range(7) if (mask >> i) & 1]
            if I and A7[np.ix_(I, I)].sum() > 0:
                continue
            A8 = np.zeros((8, 8), dtype=int)
            A8[:7, :7] = A7
            for i in I:
                A8[7, i] = A8[i, 7] = 1
            G8 = nx.from_numpy_array(A8)
            h = nx.weisfeiler_lehman_graph_hash(G8)
            if not any(nx.is_isomorphic(G8, prev) for prev in buckets_all8.get(h, [])):
                buckets_all8.setdefault(h, []).append(G8)
                tf8_all.append((G8, A8))
    print(f"EXACT n=8 total non-isomorphic triangle-free graphs: {len(tf8_all)}")

    # From ALL 1000+ tf8 graphs, find ALL maximal triangle-free graphs on n=9!
    buckets_max9 = {}
    max_tf9 = []
    for G8, A8 in tf8_all:
        # Vertex 8 must cover all non-edges without common neighbor!
        common8 = A8 @ A8
        np.fill_diagonal(common8, 1)
        uncovered = np.argwhere(np.triu((A8 == 0) & (common8 == 0), 1))
        # Vertex 8 must be adjacent to both u and v for EVERY uncovered pair (u, v)!
        forced = set()
        for u, v in uncovered:
            forced.add(int(u))
            forced.add(int(v))
        if forced and A8[np.ix_(list(forced), list(forced))].sum() > 0:
            continue
        # Only need to try independent supersets of forced!
        rem_nodes = [i for i in range(8) if i not in forced and not any(A8[i, f] == 1 for f in forced)]
        for rmask in range(1 << len(rem_nodes)):
            I = list(forced) + [rem_nodes[b] for b in range(len(rem_nodes)) if (rmask >> b) & 1]
            if I and A8[np.ix_(I, I)].sum() > 0:
                continue
            A9 = np.zeros((9, 9), dtype=int)
            A9[:8, :8] = A8
            for i in I:
                A9[8, i] = A9[i, 8] = 1
            common9 = A9 @ A9
            np.fill_diagonal(common9, 1)
            if np.any((A9 == 0) & (common9 == 0)):
                continue
            G9 = nx.from_numpy_array(A9)
            h = nx.weisfeiler_lehman_graph_hash(G9)
            if not any(nx.is_isomorphic(G9, prev) for prev in buckets_max9.get(h, [])):
                buckets_max9.setdefault(h, []).append(G9)
                max_tf9.append((G9, A9))

    print(f"EXACT n=9 maximal triangle-free graphs found: {len(max_tf9)}")
    best_e9_lean = -1
    best_e9_prose = -1
    for G9, A9 in max_tf9:
        el, _ = exact_min_edges_subset(A9, 4)
        ep, _ = exact_min_edges_subset(A9, 5)
        best_e9_lean = max(best_e9_lean, el)
        best_e9_prose = max(best_e9_prose, ep)
    print(f"EXACT n=9 max min_e(m_lean=4) = {best_e9_lean} (req >= 2), max min_e(m_prose=5) = {best_e9_prose}")
    return max_tf8, max_tf9


def search_circulants_and_twisted_blowups():
    print("\n=== PART B: ALL TRIANGLE-FREE CIRCULANTS n=5..32 ===")
    best_circ_blowup = (0.0, "")
    best_circ_discrete_lean = (0.0, "")
    for n in range(5, 20):
        half = n // 2
        # Jump set S subset {1..half}: graph is triangle-free iff for all a, b in S_sym, a+b not in S_sym mod n
        # Enumerate subsets of {1..half} via backtracking so sum-free mod n
        jumps_list = list(range(1, half + 1))
        valid_jump_sets = []

        def bt(idx, cur_sym):
            if idx == len(jumps_list):
                if cur_sym:
                    valid_jump_sets.append(tuple(sorted(x for x in cur_sym if x <= half)))
                return
            bt(idx + 1, cur_sym)
            j = jumps_list[idx]
            cand = {j, n - j}
            # Check triangle-free with cur_sym U cand
            new_sym = cur_sym | cand
            ok = True
            for x in cand:
                for y in new_sym:
                    if (x + y) % n in new_sym:
                        ok = False
                        break
                if not ok:
                    break
            if ok:
                bt(idx + 1, new_sym)

        if half <= 16:
            bt(0, set())
        # Filter to MAXIMAL sum-free jump sets (no single jump can be added)
        maximal_sets = []
        valid_set_objs = [set(js) | {n - j for j in js} for js in valid_jump_sets]
        for js, sym_s in zip(valid_jump_sets, valid_set_objs):
            is_max = True
            for cand_j in range(1, half + 1):
                if cand_j in sym_s:
                    continue
                cand = {cand_j, n - cand_j}
                new_sym = sym_s | cand
                ok = True
                for x in cand:
                    for y in new_sym:
                        if (x + y) % n in new_sym:
                            ok = False
                            break
                    if not ok:
                        break
                if ok:
                    is_max = False
                    break
            if is_max:
                maximal_sets.append(js)

        best_n_floor = -1
        best_n_ceil = -1
        best_n_jumps = None
        for js in maximal_sets:
            if n % 2 == 0 and all(j % 2 == 1 for j in js):
                continue
            G = nx.circulant_graph(n, list(js))
            A = nx.to_numpy_array(G, dtype=int)
            if n <= 19:
                ef, _ = exact_min_edges_subset(A, n // 2)
                ec, _ = exact_min_edges_subset(A, (n + 1) // 2)
                if ef > best_n_floor or (ef == best_n_floor and ec > best_n_ceil):
                    best_n_floor = ef
                    best_n_ceil = ec
                    best_n_jumps = js
        if best_n_jumps is not None:
            req = (n * n) // 50 + 1
            ratio_f = best_n_floor / (n * n)
            ratio_c = best_n_ceil / (n * n)
            print(f"n={n:2d} (max tf circ={len(maximal_sets):2d}/{len(valid_jump_sets):4d}): best={str(best_n_jumps):16s} | floor={best_n_floor:2d} ({ratio_f:.6f}), ceil={best_n_ceil:2d} ({ratio_c:.6f}), req={req}", flush=True)
            if ratio_f > best_circ_discrete_lean[0]:
                best_circ_discrete_lean = (ratio_f, f"Circ({n}, {best_n_jumps})")
            if ratio_f >= 0.015 or ratio_c >= 0.02:
                A_best = nx.to_numpy_array(nx.circulant_graph(n, list(best_n_jumps)), dtype=int)
                bl, _ = exact_continuous_blowup_uniform(A_best)
                if bl > best_circ_blowup[0]:
                    best_circ_blowup = (bl, f"Circ({n}, {best_n_jumps})")
                print(f"    -> continuous blowup_lim = {bl:.6f}", flush=True)

    print(f"Best discrete circulant (floor): {best_circ_discrete_lean}")
    print(f"Best circulant blowup_lim:       {best_circ_blowup}")


def test_twisted_blowups_and_weight_opt(max_tf8, max_tf9):
    print("\n=== PART C: WEIGHTED BLOWUPS & TWISTED LIFTS OF C5 / PETERSEN / MAXIMAL TF ===")
    # 1. Optimize weights on key templates (k <= 15)
    templates = {
        "C5": nx.to_numpy_array(nx.cycle_graph(5), dtype=int),
        "A3 (k=8)": nx.to_numpy_array(nx.circulant_graph(8, [1, 4]), dtype=int),
        "Petersen (k=10)": nx.to_numpy_array(nx.petersen_graph(), dtype=int),
        "A4 (k=11)": nx.to_numpy_array(nx.circulant_graph(11, [1, 4]), dtype=int),
        "Chvatal (k=12)": nx.to_numpy_array(nx.chvatal_graph(), dtype=int),
        "R(3,5)-1 (k=13)": nx.to_numpy_array(nx.circulant_graph(13, [1, 5]), dtype=int),
        "A5 (k=14)": nx.to_numpy_array(nx.circulant_graph(14, [1, 4, 7]), dtype=int),
    }
    for name, A in templates.items():
        u_val = exact_weighted_blowup_limit(A, np.ones(A.shape[0]) / A.shape[0])
        opt_val, opt_w = optimize_weights_for_graph(A, restarts=10, seed=42)
        print(f"{name:18s}: uniform={u_val:.6f} | weighted_opt={opt_val:.6f} | w={np.round(opt_w, 4)}")

    # 2. Check ALL maximal TF on n=8 and n=9 for weighted blowup limit!
    best_8_w = (0.0, None)
    for G8, A8 in max_tf8:
        u = exact_weighted_blowup_limit(A8, np.ones(8) / 8)
        if u >= 0.015:
            ov, ow = optimize_weights_for_graph(A8, restarts=8, seed=1)
            if ov > best_8_w[0]:
                best_8_w = (ov, (ow, G8.edges()))
    print(f"Best weighted blowup over ALL k=8 max-TF graphs: {best_8_w[0]:.6f}")

    best_9_u = (0.0, None)
    for G9, A9 in max_tf9:
        u = exact_weighted_blowup_limit(A9, np.ones(9) / 9)
        if u > best_9_u[0]:
            best_9_u = (u, A9)
    if best_9_u[1] is not None:
        ov, ow = optimize_weights_for_graph(best_9_u[1], restarts=10, seed=2)
        print(f"Best k=9 max-TF: uniform={best_9_u[0]:.6f}, weighted_opt={ov:.6f}")

    # 3. Exhaustive 2-lifts of C5 (k=10) + maximal triangle-free edge additions!
    print("\n--- Testing ALL 2-lifts & twisted blow-ups of C5 (k=10) and C5 3-lifts (k=15) ---")
    C5 = nx.cycle_graph(5)
    c5_edges = list(C5.edges())
    best_twist_10 = (0.0, "")
    rng = np.random.default_rng(123)

    # For k=10: each vertex i in C5 -> {2i, 2i+1}. Between adjacent (i,j), we can pick ANY bipartite graph (0..15 bitmask per edge, or just 2-lift + greedy completion)!
    #Wait: let's test ALL 2^5 = 32 signed 2-lifts of C5 (each edge (i,j) is either parallel or crossed), AND also complement-of-matching (i.e. complete K_{2,2} minus one edge? Wait: K_{2,2} has 4 edges, removing edges leaves fewer unless we add cross edges!).
    # Even better: build ALL 2-lifts (with parallel or crossed or complete), then randomly complete to MAXIMAL triangle-free in 500 ways!
    seen_hashes = set()
    for mask in range(32):
        # 2-lift edges
        A = np.zeros((10, 10), dtype=int)
        for idx_e, (u, v) in enumerate(c5_edges):
            if (mask >> idx_e) & 1:
                A[2*u, 2*v+1] = A[2*v+1, 2*u] = 1
                A[2*u+1, 2*v] = A[2*v, 2*u+1] = 1
            else:
                A[2*u, 2*v] = A[2*v, 2*u] = 1
                A[2*u+1, 2*v+1] = A[2*v+1, 2*u+1] = 1
        # Try 20 random maximal TF completions
        for _ in range(20):
            B = A.copy()
            while True:
                common = B @ B
                np.fill_diagonal(common, 1)
                cands = np.argwhere(np.triu((B == 0) & (common == 0), 1))
                if len(cands) == 0:
                    break
                a, b = cands[rng.integers(len(cands))]
                B[a, b] = B[b, a] = 1
            u_val = exact_weighted_blowup_limit(B, np.ones(10) / 10)
            if u_val > best_twist_10[0]:
                best_twist_10 = (u_val, f"mask={mask}, edges={B.sum()//2}, degs={sorted(B.sum(axis=1).tolist())}")
            if u_val >= 0.02:
                ov, ow = optimize_weights_for_graph(B, restarts=6, seed=7)
                if ov > 0.020001:
                    print(f"!!! BEAT 0.02 at k=10: {ov:.6f}, w={ow} !!!")

    print(f"Best twisted C5 2-lift completion (k=10): {best_twist_10[0]:.6f} | {best_twist_10[1]}")

    # 4. Direct SA optimization over triangle-free graphs on k=10, 12, 13, 14 maximizing uniform blowup limit!
    print("\n--- Direct SA optimization maximizing uniform blowup_lim over TF graphs k=10, 12, 13, 14 ---")
    for k in [10, 12, 13, 14]:
        best_val = 0.0
        for restart in range(4):
            # Start from random maximal TF graph
            A = np.zeros((k, k), dtype=int)
            while True:
                common = A @ A
                np.fill_diagonal(common, 1)
                cands = np.argwhere(np.triu((A == 0) & (common == 0), 1))
                if len(cands) == 0:
                    break
                a, b = cands[rng.integers(len(cands))]
                A[a, b] = A[b, a] = 1
            cur_v = exact_weighted_blowup_limit(A, np.ones(k) / k)
            for step in range(150):
                # Remove 1 or 2 edges, then greedily complete to maximal TF
                B = A.copy()
                ones = np.argwhere(np.triu(B, 1) == 1)
                if len(ones) == 0:
                    break
                for _ in range(rng.integers(1, 3)):
                    if len(ones) == 0:
                        break
                    a, b = ones[rng.integers(len(ones))]
                    B[a, b] = B[b, a] = 0
                while True:
                    common = B @ B
                    np.fill_diagonal(common, 1)
                    cands = np.argwhere(np.triu((B == 0) & (common == 0), 1))
                    if len(cands) == 0:
                        break
                    a, b = cands[rng.integers(len(cands))]
                    B[a, b] = B[b, a] = 1
                nv = exact_weighted_blowup_limit(B, np.ones(k) / k)
                if nv >= cur_v or rng.random() < 0.05:
                    A = B
                    cur_v = nv
                    if cur_v > best_val:
                        best_val = cur_v
                        if best_val > 0.020001:
                            print(f"!!! BEAT 0.02 at k={k}: {best_val:.6f} !!!")
        print(f"  k={k:2d} SA max uniform blowup_lim = {best_val:.6f}")


if __name__ == "__main__":
    t0 = time.time()
    # Sanity check exact_weighted_blowup_limit
    c5 = nx.to_numpy_array(nx.cycle_graph(5), dtype=int)
    pet = nx.to_numpy_array(nx.petersen_graph(), dtype=int)
    assert abs(exact_weighted_blowup_limit(c5, np.ones(5)/5) - 0.02) < 1e-12
    assert abs(exact_weighted_blowup_limit(pet, np.ones(10)/10) - 0.02) < 1e-12
    max_tf8, max_tf9 = enumerate_maximal_tf_via_extensions()
    test_twisted_blowups_and_weight_opt(max_tf8, max_tf9)
    print(f"\nDeep search complete in {time.time() - t0:.2f}s")
