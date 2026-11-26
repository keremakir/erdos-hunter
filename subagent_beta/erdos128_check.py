import itertools
import math
import time
import numpy as np
import networkx as nx
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy import sparse


def exact_min_edges_subset(adj: np.ndarray, m: int) -> tuple[int, tuple[int, ...]]:
    """Exact minimum number of edges induced by any subset of size m (for small n <= 24 or MILP)."""
    n = adj.shape[0]
    if n <= 22:
        best = 10**9
        best_sub = ()
        # Precompute bitmask adjacency or use numpy slicing if comb(n, m) <= 250000
        if math.comb(n, m) <= 300000:
            for sub in itertools.combinations(range(n), m):
                idx = list(sub)
                e = int(adj[np.ix_(idx, idx)].sum()) // 2
                if e < best:
                    best = e
                    best_sub = sub
            return best, best_sub

    # MILP fallback for larger n
    # Variables: x_0..x_{n-1} in {0,1}, y_e in {0,1} for each edge e=(u,v)
    # Minimize sum y_e
    # s.t. sum x_i >= m
    #      y_e >= x_u + x_v - 1  =>  x_u + x_v - y_e <= 1
    edges = list(zip(*np.where(np.triu(adj, 1) > 0)))
    E = len(edges)
    num_vars = n + E
    c = np.zeros(num_vars)
    c[n:] = 1.0
    integrality = np.ones(num_vars)
    bounds = Bounds(lb=np.zeros(num_vars), ub=np.ones(num_vars))

    rows, cols, vals = [], [], []
    # Constraint 0: sum x_i >= m
    for i in range(n):
        rows.append(0)
        cols.append(i)
        vals.append(1.0)
    lb = [float(m)]
    ub = [float(n)]

    # Edge constraints: x_u + x_v - y_e <= 1
    for idx_e, (u, v) in enumerate(edges):
        r = idx_e + 1
        rows.extend([r, r, r])
        cols.extend([int(u), int(v), n + idx_e])
        vals.extend([1.0, 1.0, -1.0])
        lb.append(-np.inf)
        ub.append(1.0)

    A_mat = sparse.csc_matrix((vals, (rows, cols)), shape=(1 + E, num_vars))
    res = milp(c=c, integrality=integrality, bounds=bounds,
               constraints=LinearConstraint(A_mat, lb, ub),
               options={"time_limit": 15.0})
    if not res.success and res.x is None:
        raise RuntimeError(f"MILP failed: {res.message}")
    chosen = tuple(i for i in range(n) if res.x[i] > 0.5)
    # Verify exact integer count
    exact_e = int(adj[np.ix_(list(chosen), list(chosen))].sum()) // 2
    if not res.success:
        print(f"  [MILP time limit: best={exact_e}, lb={getattr(res, 'mip_dual_bound', '?')}]")
    return exact_e, chosen


def exact_continuous_blowup_uniform(adj: np.ndarray) -> tuple[float, dict]:
    """
    Exact min_{0 <= x <= 1/k, sum x = 1/2} 0.5 * x^T A x.
    For even k: exact min_{|S| = k/2} e(S) / k^2.
    For odd k: exact min_{|S| = (k-1)/2, u not in S} (e(S) + 0.5 * deg_S(u)) / k^2.
    """
    k = adj.shape[0]
    if k % 2 == 0:
        m = k // 2
        e_min, sub = exact_min_edges_subset(adj, m)
        return e_min / (k * k), {"k": k, "m": m, "e_min": e_min, "subset": sub}
    else:
        m = (k - 1) // 2
        if k <= 23 and math.comb(k, m) <= 300000:
            best_num = 1e18
            best_info = {}
            all_idx = set(range(k))
            for sub in itertools.combinations(range(k), m):
                idx = list(sub)
                e_S = int(adj[np.ix_(idx, idx)].sum()) // 2
                # min degree from outside into S
                outside = [u for u in range(k) if u not in sub]
                degs = adj[np.ix_(outside, idx)].sum(axis=1)
                min_deg = int(degs.min())
                u_best = outside[int(np.argmin(degs))]
                val = e_S + 0.5 * min_deg
                if val < best_num:
                    best_num = val
                    best_info = {"k": k, "m": m, "e_S": e_S, "min_deg": min_deg, "subset": sub, "u": u_best}
            return best_num / (k * k), best_info
        else:
            # MILP on 2k scaling (so x_i in {0, 1, 2} with sum x_i = k? Wait: x_i <= 1/k -> in units of 1/(2k), x_i in {0, 2}, except one in {1}, sum = k)
            # Actually exact MILP with x_i in {0, 1, 2} is quadratic unless we use 2-bit encoding:
            # Let z_i in {0,1} (full vertex weight 2) and p_i in {0,1} (half vertex weight 1), sum(2*z_i + p_i) = k, sum p_i = 1, z_i + p_i <= 1
            # Wait: edges among (2z + p): 4 z_u z_v + 2 z_u p_v + 2 p_u z_v + 0 (since sum p = 1, p_u p_v = 0!)
            edges = list(zip(*np.where(np.triu(adj, 1) > 0)))
            E = len(edges)
            # Variables: z_0..z_{k-1} (0..k-1), p_0..p_{k-1} (k..2k-1), y_zz (2k..2k+E-1), y_zp_uv (2k+E..2k+2E-1), y_zp_vu (2k+2E..2k+3E-1)
            # Wait: simpler! 2z_u + p_u is binary-sum; (2z_u + p_u)(2z_v + p_v) = 4 y_zz + 2 y_up_v + 2 y_vp_u
            num_vars = 2 * k + 3 * E
            c = np.zeros(num_vars)
            c[2 * k: 2 * k + E] = 4.0
            c[2 * k + E: 2 * k + 3 * E] = 2.0
            integrality = np.ones(num_vars)
            bounds = Bounds(lb=np.zeros(num_vars), ub=np.ones(num_vars))
            rows, cols, vals, lb, ub = [], [], [], [], []
            r = 0
            # sum z_i = m
            for i in range(k):
                rows.append(r); cols.append(i); vals.append(1.0)
            lb.append(float(m)); ub.append(float(m)); r += 1
            # sum p_i = 1
            for i in range(k):
                rows.append(r); cols.append(k + i); vals.append(1.0)
            lb.append(1.0); ub.append(1.0); r += 1
            # z_i + p_i <= 1
            for i in range(k):
                rows.extend([r, r]); cols.extend([i, k + i]); vals.extend([1.0, 1.0])
                lb.append(-np.inf); ub.append(1.0); r += 1
            for idx_e, (u, v) in enumerate(edges):
                u, v = int(u), int(v)
                # y_zz >= z_u + z_v - 1
                rows.extend([r, r, r]); cols.extend([u, v, 2 * k + idx_e]); vals.extend([1.0, 1.0, -1.0])
                lb.append(-np.inf); ub.append(1.0); r += 1
                # y_zu_pv >= z_u + p_v - 1
                rows.extend([r, r, r]); cols.extend([u, k + v, 2 * k + E + idx_e]); vals.extend([1.0, 1.0, -1.0])
                lb.append(-np.inf); ub.append(1.0); r += 1
                # y_zv_pu >= z_v + p_u - 1
                rows.extend([r, r, r]); cols.extend([v, k + u, 2 * k + 2 * E + idx_e]); vals.extend([1.0, 1.0, -1.0])
                lb.append(-np.inf); ub.append(1.0); r += 1
            A_mat = sparse.csc_matrix((vals, (rows, cols)), shape=(r, num_vars))
            res = milp(c=c, integrality=integrality, bounds=bounds, constraints=LinearConstraint(A_mat, lb, ub))
            if not res.success:
                raise RuntimeError(res.message)
            z = [i for i in range(k) if res.x[i] > 0.5]
            p = [i for i in range(k) if res.x[k + i] > 0.5]
            e_S = int(adj[np.ix_(z, z)].sum()) // 2
            deg_u = int(adj[p[0], z].sum())
            val = (e_S + 0.5 * deg_u) / (k * k)
            return val, {"k": k, "m": m, "e_S": e_S, "min_deg": deg_u, "subset": tuple(z), "u": p[0]}


def is_triangle_free(adj: np.ndarray) -> bool:
    a3 = np.trace(adj @ adj @ adj)
    return int(a3) == 0


def build_famous_triangle_free_graphs():
    graphs = {}

    # 1. C5
    G = nx.cycle_graph(5)
    graphs["C5 (k=5, d=2)"] = nx.to_numpy_array(G, dtype=int)

    # 2. Andrasfai graphs A_r: vertices 0..3r-2, edge (i,j) if (i-j) mod (3r-1) in {r, r+1, ..., 2r-1}?
    # Wait: let's check standard definition of Andrasfai graph And(r):
    # n = 3r - 1 vertices, edges between i and j iff |i - j| mod n is congruent to 1 mod 3?
    # Let's check: r=1 -> n=2, diff=1 -> K2.
    # r=2 -> n=5, diffs={1, 4} -> C5.
    # r=3 -> n=8, diffs={1, 4, 7} -> 3-regular! Wait: are 1,4,7 triangle-free? 1+1=2 (not in {1,4,7}), 1+4=5 (no), 4+4=8=0 (no), 1+7=8=0 (no), 4+7=11=3 (no), 7+7=14=6 (no)! YES!
    # r=4 -> n=11, diffs={1, 4, 7, 10} -> 4-regular, sum of two elements congruent to 2 mod 3, never 1 mod 3! So ALWAYS triangle-free!
    for r in [2, 3, 4, 5, 6, 8, 10]:
        n = 3 * r - 1
        G = nx.Graph()
        G.add_nodes_from(range(n))
        diffs = [d for d in range(1, n) if d % 3 == 1]
        for i in range(n):
            for d in diffs:
                G.add_edge(i, (i + d) % n)
        graphs[f"Andrasfai A_{r} (k={n}, d={r})"] = nx.to_numpy_array(G, dtype=int)

    # 3. Petersen graph
    G = nx.petersen_graph()
    graphs["Petersen (k=10, d=3)"] = nx.to_numpy_array(G, dtype=int)

    # 4. Grotzsch graph (Mycielski of C5, k=11)
    G = nx.mycielski_graph(4)  # M_4 is Grotzsch on 11 vertices
    graphs["Grotzsch M4 (k=11)"] = nx.to_numpy_array(G, dtype=int)

    # 5. Chvatal graph (k=12, d=4)
    G = nx.chvatal_graph()
    graphs["Chvatal (k=12, d=4)"] = nx.to_numpy_array(G, dtype=int)

    # 6. Ramsey R(3,5)-1 graph on k=13: circulant(13, [1, 5]) -> diffs {1, 5, 8, 12}
    G = nx.circulant_graph(13, [1, 5])
    graphs["Circulant(13, {1,5}) R(3,5)-1 (k=13, d=4)"] = nx.to_numpy_array(G, dtype=int)

    # 7. Clebsch / Greenwood-Gleason graph on k=16, d=5:
    # GF(16) cubic residues, OR vertices in {0,1}^4, adjacent if Hamming distance = 4, OR complement of folded 5-cube?
    # Wait: Clebsch graph (5-regular triangle-free on 16 vertices):
    # Folded 5-cube: vertices are {0,1}^5 / ~ (identify x and 1-x), i.e., 16 vertices of even weight in {0,1}^5? No, in Q_5, quotient by antipodal x <-> ~x has 16 vertices, degree 5, girth 4, triangle-free!
    # Wait: let's check! In Q_5, shortest odd cycle between x and ~x has length 5! So quotienting Q_5 by x ~ (1-x) yields a 5-regular triangle-free graph on 16 vertices (Clebsch graph)!
    G = nx.Graph()
    reps = [v for v in range(32) if bin(v).count("1") % 2 == 0]  # each antipodal pair {v, 31^v} has one even-weight and one odd-weight!
    # Wait: weight(31^v) = 5 - weight(v), so EXACTLY one has even weight!
    idx_map = {v: i for i, v in enumerate(reps)}
    for v in reps:
        for b in range(5):
            nb = v ^ (1 << b)  # odd weight
            nb_rep = 31 ^ nb   # even weight!
            G.add_edge(idx_map[v], idx_map[nb_rep])
    graphs["Clebsch / Folded Q5 (k=16, d=5)"] = nx.to_numpy_array(G, dtype=int)

    # 8. Circulant(17, ...) and Circulant(21, ...) - let's check R(3,6)-1 on 17 vertices!
    # Known triangle-free on 17 vertices with alpha=5: circulant(17, [1, 3, 7])? Let's test if {1,3,7,10,14,16} is sum-free mod 17: 1+3=4, 1+7=8, 3+7=10 (BAD! 10=-7!).
    # Try {1, 4, 6}? 1+4=5, 1+6=7, 4+6=10, 4+11=15, 6+11=17, 1+11=12, 1+13=14, 4+13=17, 6+13=19=2, 1+16=17, 4+16=3, 6+16=5. Wait: 6+6=12, 4+4=8, 1+1=2, 11+11=5, 13+13=9, 16+16=15.
    # Let's test {1, 4, 6} mod 17? Wait: 16=-1, 13=-4, 11=-6. Sums: {1,4,6,-1,-4,-6} -> 6-(-1)=7, no; 6+(-4)=2; 4+(-6)=-2; 1+4=5; 1+6=7; 4+6=10! Wait: NONE of {2,5,7,10,12,15} are in {1,4,6,11,13,16}! Wait: 6+6=12, 4+4=8, 1+1=2 -> 0 triangles!!Wait: {1,4,6} gives 6-regular on 17?Wait: 17*6/2 = 51 edges, let's check alpha!
    for name, n, jumps in [
        ("Circulant(17, {1,4,6}) (k=17, d=6)", 17, [1, 4, 6]),
        ("Circulant(19, {1,4,7}) (k=19, d=6)", 19, [1, 4, 7]),
        ("Circulant(21, {1,5,8}) (k=21, d=6)", 21, [1, 5, 8]),
        ("Circulant(23, {1,3,8}) (k=23, d=6)", 23, [1, 3, 8]),
        ("Circulant(26, {1,4,10,13}) (k=26, d=7)", 26, [1, 4, 10, 13]),
    ]:
        CG = nx.circulant_graph(n, jumps)
        A = nx.to_numpy_array(CG, dtype=int)
        if is_triangle_free(A):
            graphs[name] = A

    # 9. Hoffman-Singleton graph (k=50, d=7)
    HS = nx.hoffman_singleton_graph()
    graphs["Hoffman-Singleton (k=50, d=7)"] = nx.to_numpy_array(HS, dtype=int)

    # 10. Mycielski of Petersen (k=21) and Mycielski M5 (k=23)
    graphs["Mycielski(Petersen) (k=21)"] = nx.to_numpy_array(nx.mycielskian(nx.petersen_graph()), dtype=int)
    graphs["Mycielski M5 (k=23)"] = nx.to_numpy_array(nx.mycielski_graph(5), dtype=int)

    return graphs


def analyze_small_n():
    print("=== PART 1: EXACT SMALL-N ANALYSIS OF LEAN 128.lean ===")
    print("Lean condition: 2 * |V'| + 1 >= n  (i.e. |V'| >= floor(n/2))")
    print("Threshold:      50 * e(G[V']) > n^2 (i.e. e(G[V']) >= floor(n^2/50) + 1)")
    print()

    # For small n, compute:
    # - exact max over all triangle-free G on n vertices of min_{|V'| = floor(n/2)} e(G[V'])
    # For n <= 7: analytical + exhaustive check for n=4..7; for n=8..13: check circulant, blowups, greedy/SA
    for n in range(1, 16):
        m_lean = n // 2
        m_prose = (n + 1) // 2
        req_e = (n * n) // 50 + 1
        mantel_lean = (m_lean * m_lean) // 4
        mantel_prose = (m_prose * m_prose) // 4
        print(f"n={n:2d}: m_lean={m_lean:2d} (Mantel max={mantel_lean:2d}), m_prose={m_prose:2d} (Mantel max={mantel_prose:2d}), req_e > n^2/50 => >= {req_e}")


def exhaustive_small_n_check():
    print("\n=== PART 1B: EXACT EXHAUSTIVE SEARCH FOR n=4..8 & HEURISTIC SEARCH n=8..25 ===")
    # For n <= 7, test ALL triangle-free graphs (or up to n=7 via bitmasks/nauty? For n=6 there are 156 graphs, n=7 there are 1044 graphs -> easy with backtracking of triangle-free graphs!)
    # Actually let's use networkx graph atlas for n <= 7!
    atlas = nx.graph_atlas_g()
    for n in range(1, 8):
        best_lean = -1
        best_prose = -1
        req_e = (n * n) // 50 + 1
        m_lean = n // 2
        m_prose = (n + 1) // 2
        tf_count = 0
        for G in atlas:
            if G.number_of_nodes() != n:
                continue
            A = nx.to_numpy_array(G, dtype=int)
            if not is_triangle_free(A):
                continue
            tf_count += 1
            e_lean, _ = exact_min_edges_subset(A, m_lean)
            e_prose, _ = exact_min_edges_subset(A, m_prose)
            if e_lean > best_lean:
                best_lean = e_lean
            if e_prose > best_prose:
                best_prose = e_prose
        print(f"n={n} (atlas tf graphs={tf_count:3d}): max min_e(m_lean={m_lean}) = {best_lean}, max min_e(m_prose={m_prose}) = {best_prose}, req_e = {req_e} -> Lean CE? {best_lean >= req_e}")


def sa_search_triangle_free(n: int, m: int, steps: int = 8000, seed: int = 42):
    """Simulated annealing to maximize min_{|V'|=m} e(G[V']) over triangle-free graphs on n vertices."""
    rng = np.random.default_rng(seed)
    # Start from balanced C5 blowup
    A = np.zeros((n, n), dtype=int)
    parts = [i % 5 for i in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if (parts[i] - parts[j]) % 5 in (1, 4):
                A[i, j] = A[j, i] = 1

    # Maintain current exact min_e (if C(n,m) small) or approximate with witness pool
    use_exact = math.comb(n, m) <= 15000
    all_subs = np.array(list(itertools.combinations(range(n), m))) if use_exact else None

    # Fast edge-counting via binary subset matrix S (K x n) @ A? No, for edge list:
    # Even faster: for each subset, edges = (S @ adj * S).sum() / 2 -> one BLAS matmul!
    S = np.zeros((len(all_subs), n), dtype=np.float32)
    rows_s = np.repeat(np.arange(len(all_subs)), m)
    cols_s = all_subs.ravel()
    S[rows_s, cols_s] = 1.0

    def score(mat):
        if use_exact:
            mat_f = mat.astype(np.float32)
            vals = ((S @ mat_f) * S).sum(axis=1) * 0.5
            min_v = int(round(float(vals.min())))
            cnt = int((vals <= min_v + 0.1).sum())
            return min_v - 0.0001 * cnt
        else:
            return 0.0

    if not use_exact:
        return None, None

    cur_s = score(A)
    best_s = cur_s
    best_A = A.copy()
    for step in range(steps):
        u, v = rng.choice(n, size=2, replace=False)
        if A[u, v] == 1:
            # try removing edge (sometimes swap with adding a non-triangle edge)
            A[u, v] = A[v, u] = 0
            # also try adding a valid non-edge
            cand_pairs = []
            # fast check: pairs with no common neighbor
            common = A @ A
            zeros = np.argwhere(np.triu((A == 0) & (common == 0), 1))
            added = None
            if len(zeros) > 0 and rng.random() < 0.8:
                a, b = zeros[rng.integers(len(zeros))]
                A[a, b] = A[b, a] = 1
                added = (a, b)
            new_s = score(A)
            temp = max(0.01, 0.5 * (1 - step / steps))
            if new_s >= cur_s or rng.random() < math.exp((new_s - cur_s) / temp):
                cur_s = new_s
                if cur_s > best_s:
                    best_s = cur_s
                    best_A = A.copy()
            else:
                A[u, v] = A[v, u] = 1
                if added is not None:
                    A[added[0], added[1]] = A[added[1], added[0]] = 0
        else:
            # try adding edge if no common neighbor
            if np.dot(A[u], A[v]) == 0:
                A[u, v] = A[v, u] = 1
                new_s = score(A)
                if new_s >= cur_s:
                    cur_s = new_s
                    if cur_s > best_s:
                        best_s = cur_s
                        best_A = A.copy()
                else:
                    A[u, v] = A[v, u] = 0
    return int(math.floor(best_s + 1e-6)), best_A


def main():
    t0 = time.time()
    analyze_small_n()
    exhaustive_small_n_check()

    print("\n=== PART 1C: SA MAXIMIZATION OF min_e(m_lean) FOR n=8..16 ===")
    for n in range(8, 17):
        m_lean = n // 2
        req_e = (n * n) // 50 + 1
        best_e, best_A = sa_search_triangle_free(n, m_lean, steps=4000, seed=100 + n)
        if best_e is not None:
            assert is_triangle_free(best_A)
            # Also check m_prose if different
            m_prose = (n + 1) // 2
            e_prose, _ = exact_min_edges_subset(best_A, m_prose)
            print(f"n={n:2d}: best min_e(m_lean={m_lean}) = {best_e:2d} (ratio={best_e/(n*n):.6f}), req_e={req_e} | m_prose={m_prose}: e={e_prose} -> Lean CE? {best_e >= req_e}")

    print("\n=== PART 2: FAMOUS TRIANGLE-FREE GRAPHS & BLOW-UP LIMIT ===")
    graphs = build_famous_triangle_free_graphs()
    results = []
    for name, A in graphs.items():
        k = A.shape[0]
        tf = is_triangle_free(A)
        assert tf, f"{name} is NOT triangle-free!"
        val, info = exact_continuous_blowup_uniform(A)
        # Also compute exact discrete min for G itself (not blowup) on floor(k/2) and ceil(k/2)
        e_floor, _ = exact_min_edges_subset(A, k // 2)
        e_ceil, _ = exact_min_edges_subset(A, (k + 1) // 2)
        results.append((val, name, k, e_floor, e_ceil, info))
        print(f"{name:42s} | blowup_lim = {val:.6f} (1/50=0.020000) | exact G: floor={e_floor}/{k}^2 ({e_floor/(k*k):.6f}), ceil={e_ceil}/{k}^2 ({e_ceil/(k*k):.6f})")

    results.sort(reverse=True)
    print("\nTop 5 by blowup_lim:")
    for r in results[:5]:
        print(f"  {r[0]:.6f} : {r[1]} | info={r[5]}")
    print(f"\nDone in {time.time() - t0:.2f}s")


if __name__ == "__main__":
    main()
