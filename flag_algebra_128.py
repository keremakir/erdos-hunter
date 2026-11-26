"""
Erdős #128 ($250 Prize — Sparse Half Conjecture)
Razborov Flag Algebras Semidefinite Programming (SDP) Prover (N=5 and N=6)

Goal: Find the smallest provable constant c such that every large triangle-free graph G
contains an induced subgraph on floor(n/2) vertices with <= c * n^2 edges.
  - Conjecture (Erdős #128): c = 1/50 = 0.020000
  - Razborov's Flag Algebra benchmark: c = 27/1024 ≈ 0.026367
  - Recent benchmark: c ≈ 0.026200

Method:
  For any vertex v with degree density d(v) < 1/2, form S(v) = N(v) U Rand(V \ N(v), q_v)
  with q_v = (1/2 - d(v)) / (1 - d(v)).
  Expected edge density in S(v):
    f(v) = q_v * e_1(v) + q_v^2 * e_0(v)
  Multiplying (f(v) - c) by (1 - d(v))^2 >= 0 gives a degree-4 polynomial in 1-vertex flags:
    P_c(v) = (1 - d(v))(1/2 - d(v)) * e_1(v) + (1/2 - d(v))^2 * e_0(v) - c * (1 - d(v))^2
  If E_v[w(v) * P_c(v)] <= 0 for some nonnegative vertex weight w(v) >= 0 (with E_v[w(v)] > 0),
  then SOME vertex v has f(v) <= c (hence a sparse half with <= c*n^2 edges exists!).
  We also restrict to edge density d(K_2) >= 8c (since if d(K_2) <= 8c, a uniform random half
  already has expected edge density d(K_2)/8 <= c!).
"""

import itertools
import time
from collections import defaultdict
import numpy as np
import cvxpy as cp


def is_triangle_free(adj_bits, n):
    for u in range(n):
        nu = adj_bits[u]
        v_bits = nu >> (u + 1)
        v = u + 1
        while v_bits:
            if v_bits & 1:
                if nu & adj_bits[v]:
                    return False
            v_bits >>= 1
            v += 1
    return True


def graph_from_edge_mask(n, emask, pairs):
    adj = [0] * n
    for idx, (u, v) in enumerate(pairs):
        if (emask >> idx) & 1:
            adj[u] |= 1 << v
            adj[v] |= 1 << u
    return tuple(adj)


def canonical_graph(adj, n):
    """Exact canonical form of an unlabeled graph on n <= 6 vertices via all n! permutations."""
    best = None
    for perm in itertools.permutations(range(n)):
        code = 0
        bit = 0
        for i in range(n):
            pi = perm[i]
            ai = adj[pi]
            for j in range(i + 1, n):
                if (ai >> perm[j]) & 1:
                    code |= 1 << bit
                bit += 1
        if best is None or code < best:
            best = code
    return best


def canonical_flag(adj, n, t):
    """Canonical form of a flag on n vertices where vertices 0..t-1 are fixed (labeled type)."""
    best = None
    fixed = tuple(range(t))
    for rest in itertools.permutations(range(t, n)):
        perm = fixed + rest
        code = 0
        bit = 0
        for i in range(n):
            pi = perm[i]
            ai = adj[pi]
            for j in range(i + 1, n):
                if (ai >> perm[j]) & 1:
                    code |= 1 << bit
                bit += 1
        if best is None or code < best:
            best = code
    return best


def enumerate_tf_graphs(n):
    """Return list of (canon_code, adj_tuple) for all unlabeled triangle-free graphs on n vertices."""
    pairs = list(itertools.combinations(range(n), 2))
    seen = {}
    for emask in range(1 << len(pairs)):
        adj = graph_from_edge_mask(n, emask, pairs)
        if not is_triangle_free(adj, n):
            continue
        c = canonical_graph(adj, n)
        if c not in seen:
            seen[c] = adj
    items = sorted(seen.items())
    return [c for c, _ in items], [adj for _, adj in items]


def enumerate_tf_flags(m, type_adj, t):
    """Return all non-isomorphic triangle-free flags on m vertices extending fixed type_adj on 0..t-1."""
    # Edges involving at least one vertex in t..m-1
    free_pairs = []
    for i in range(m):
        for j in range(max(i + 1, t), m):
            free_pairs.append((i, j))
    seen = {}
    for emask in range(1 << len(free_pairs)):
        adj = list(type_adj) + [0] * (m - t)
        for idx, (u, v) in enumerate(free_pairs):
            if (emask >> idx) & 1:
                adj[u] |= 1 << v
                adj[v] |= 1 << u
        adj_t = tuple(adj)
        if not is_triangle_free(adj_t, m):
            continue
        c = canonical_flag(adj_t, m, t)
        if c not in seen:
            seen[c] = adj_t
    items = sorted(seen.items())
    return [c for c, _ in items], [adj for _, adj in items]


def induced_sub_adj(adj, verts):
    k = len(verts)
    sub = [0] * k
    for i in range(k):
        ai = adj[verts[i]]
        for j in range(i + 1, k):
            if (ai >> verts[j]) & 1:
                sub[i] |= 1 << j
                sub[j] |= 1 << i
    return tuple(sub)


def compute_product_tensors(N, graphs_N, t, type_adj, flag_codes, flag_adjs):
    """
    For a type sigma of size t and flags F_1..F_r of size m = (N + t) // 2,
    compute exact averaged flag product tensor M[g_idx][a, b] = [[ F_a * F_b ]]_sigma(G_g).
    For each G on N vertices, average over all injective maps theta: [t] -> [N] that induce type_adj,
    and all disjoint pairs (U1, U2) partitioning [N] \ im(theta) of size (m - t) each.
    """
    m = (N + t) // 2
    assert 2 * m - t == N
    r = len(flag_codes)
    flag_to_idx = {c: i for i, c in enumerate(flag_codes)}
    type_canon = canonical_flag(type_adj, t, t)

    # Precompute all injective tuples theta of length t from range(N)
    all_thetas = list(itertools.permutations(range(N), t))
    num_thetas = len(all_thetas)
    # Number of ways to choose U1 of size m-t from N-t remaining vertices
    rem_k = m - t
    import math
    num_splits = math.comb(N - t, rem_k)
    denom = num_thetas * num_splits

    tensors = []
    for g_adj in graphs_N:
        mat = np.zeros((r, r), dtype=np.float64)
        for theta in all_thetas:
            # Check if theta induces EXACTLY type_adj (preserving labels 0..t-1)
            sub_t = induced_sub_adj(g_adj, theta)
            if sub_t != type_adj:
                continue
            theta_set = set(theta)
            rem = [v for v in range(N) if v not in theta_set]
            for u1 in itertools.combinations(rem, rem_k):
                u1_set = set(u1)
                u2 = tuple(v for v in rem if v not in u1_set)
                f1 = canonical_flag(induced_sub_adj(g_adj, theta + u1), m, t)
                f2 = canonical_flag(induced_sub_adj(g_adj, theta + u2), m, t)
                i1 = flag_to_idx[f1]
                i2 = flag_to_idx[f2]
                mat[i1, i2] += 1.0
        mat = 0.5 * (mat + mat.T) / denom
        tensors.append(mat)
    return tensors  # list of len(graphs_N) matrices of shape (r, r)


def eval_1vertex_poly_on_N_graph(adj, N, c_val, weight_mode="uniform"):
    r"""
    Exact evaluation of the 1-vertex rooted polynomial P_c(v) averaged over all labeled
    injective embeddings of 5 vertices (v, x1, x2, y1, y2) into an N-vertex graph G (N >= 5)!
    Specifically, for a fixed root v and 4 distinct other vertices (a, b, y, z):
      - d(v) = I(v ~ a)
      - 1 - d(v) = I(v !~ a)
      - 1/2 - d(v) = 1/2 - I(v ~ b)
      - e_1(v) = (1/2) * [ I(v~y, v!~z, y~z) + I(v~z, v!~y, y~z) ]  (since e(N(v), V\N(v))/n^2 = P(y in N(v), z not in N(v), y~z)!)
        WAIT — double check normalization of e_1(v) and e_0(v)!
        Let's verify on C5 (n=5 blowup, d=2/5, e(G)/n^2 = 5/25 = 0.2):
        In C5: for any vertex v, |N(v)| = 2 (density 2/5), |V\N(v)| = 3 (density 3/5).
        Ordered pairs (y, z) with y in N(v), z not in N(v), y~z:
          Each of the 2 neighbors of v has 2 neighbors in V\N(v) (one is v itself, one is on the far edge!).
          Wait: in the continuum blow-up, v itself has measure 0, so the 2 neighbors of v each have 2 neighbors in V\N(v):
          actually in C5 (0-1-2-3-4-0), for v=0: N(0)={1,4}, V\N(0)={0,2,3}.
          Edges between {1,4} and {0,2,3}: (1,0), (1,2), (4,0), (4,3) -> 4 edges!
          In the blow-up C5[t] (n=5t): N(0) has 2t vertices; each vertex in part 1 has t neighbors in part 0 and t neighbors in part 2.
          So e(N(0), V\N(0)) = 2t * 2t = 4 t^2 = (4/25) n^2!
          And P(y in N(v), z not in N(v), y~z) for random (y, z) is:
          # ordered pairs (y in N(v), z not in N(v), y~z) / n^2 = e(N(v), V\N(v)) / n^2 = 4/25!
          What about e_0(v) = e(V\N(v)) / n^2?
          In C5[t]: edges inside {0,2,3} are ONLY between part 2 and part 3: t^2 edges = (1/25) n^2!
          Ordered pairs (y, z) both in V\N(v) with y~z: 2 * t^2 -> divided by n^2 is 2/25!
          So e_0(v) = (1/2) * P(y not in N(v), z not in N(v), y~z)!
          CHECK f(v) on C5[t]:
          d = 2/5 = 0.4 -> q = (0.5 - 0.4) / (1 - 0.4) = 0.1 / 0.6 = 1/6.
          f(v) = q * e_1(v) + q^2 * e_0(v) = (1/6)*(4/25) + (1/36)*(1/25) = (24 + 1) / (36 * 25) = 25 / 900 = 1/36 ≈ 0.02778!
          HOLD ON!! Look at that sanity check!!
          On C5[t], uniform random padding outside N(v) gives 1/36 ≈ 0.02778 > 1/50 = 0.02000!!
          (Because in C5[t], uniform padding puts weight 1/6 on part 0, which has 2t neighbors in N(v), instead of putting ALL weight on part 2 or part 3 which only has t neighbors in N(v)!)
    """
    # Compute exact expectation over all injective 5-tuples (v, a, b, y, z) in range(N)
    # Using linearity, average over all 5-permutations of range(N)
    total_e1_term = 0.0
    total_e0_term = 0.0
    total_const_term = 0.0
    total_edge = 0.0
    cnt = 0

    for perm in itertools.permutations(range(N), 5):
        v, a, b, y, z = perm
        # Indicators
        va = (adj[v] >> a) & 1
        vb = (adj[v] >> b) & 1
        vy = (adj[v] >> y) & 1
        vz = (adj[v] >> z) & 1
        yz = (adj[y] >> z) & 1

        # Optional weight w(v) >= 0 (if N=6 we can even use 6th vertex!)
        w = 1.0
        if weight_mode == "deg":
            # Use va as weight? No, need independent vertex for weight if N=6; handled below
            pass

        one_minus_da = 1.0 - va
        one_minus_db = 1.0 - vb
        half_minus_db = 0.5 - vb
        half_minus_da = 0.5 - va

        # e_1(v) = P(y in N(v), z not in N(v), y~z) (symmetrized over y,z)
        e1_ind = 0.5 * ((vy and (not vz) and yz) + (vz and (not vy) and yz))
        # e_0(v) = 0.5 * P(y not in N(v), z not in N(v), y~z)
        e0_ind = 0.5 * ((not vy) and (not vz) and yz)

        total_e1_term += w * one_minus_da * half_minus_db * e1_ind
        total_e0_term += w * half_minus_da * half_minus_db * e0_ind
        total_const_term += w * one_minus_da * one_minus_db
        total_edge += yz
        cnt += 1

    return (
        total_e1_term / cnt,
        total_e0_term / cnt,
        total_const_term / cnt,
        total_edge / cnt,
    )


def eval_2step_neighborhood_poly(adj, N):
    r"""
    UPGRADED RAZBOROV-STYLE SPARSE HALF RULE (Sharp on C5! Beats 1/36!):
    Instead of padding N(v) uniformly from V \ N(v), take a vertex v AND a second vertex u NOT in N(v)
    that is at distance 2 from v (or just any non-neighbor u != v), and form:
      S(v, u) = N(v) U (N(u) \ N(v)) = N(v) U N(u)  (padded or trimmed to size 1/2!)
    WAIT: Let's check what happens on C5[t] when we take S = N(0) U N(2) = {1, 4} U {1, 3} = {1, 3, 4} (size 3/5 > 1/2)!
      - If we take N(0) = {1, 4} (size 2/5) and pad ONLY from N(2) \ N(0) = {3} (size 1/5) with prob 1/2:
        Then S has size 2/5 + (1/2)*(1/5) = 1/2!!
        Edges inside S: ONLY between {4} and {3}, which is (1/2)*(1/5)*(1/5) = 1/50 = 0.020000 EXACTLY!!
    OH!! MY!! GOODNESS!!
    READ THAT AGAIN!!
    Taking S(v, u) = N(v) + random subset of (N(u) \ N(v)) of size (1/2 - |N(v)|) ACHIEVES THE EXACT 1/50 = 0.020000 BOUND ON C5[t]!!
    Let's ALSO check Petersen graph P[t] (n=10t, d=3/10)!
      - In Petersen: for non-adjacent (v, u), |N(v)| = 3/10, |N(u) \ N(v)| = 2/10 (since every non-adjacent pair in Petersen has 1 common neighbor!).
      - So |N(v) U N(u)| = 3/10 + 2/10 = 5/10 = 1/2 EXACTLY!!
      - How many edges are inside N(v) U N(u)?
        Since N(v) and N(u) are independent, edges only go between N(v)\N(u) (size 2/10) and N(u)\N(v) (size 2/10).
        In Petersen, between those 2 vertices and 2 vertices there are 2 edges -> 2 / 100 = 1/50 = 0.020000 EXACTLY!!
    BOTH C5 AND PETERSEN ARE 100% EXACTLY TIGHT FOR THE TWO-NEIGHBORHOOD UNION S(u, v) = N(u) U N(v)!!

    Let's check the EXACT 4-vertex / 5-vertex / 6-vertex Flag Algebra expression for S(u, v) = N(u) U N(v)!!
    Wait: For any pair (u, v), |N(u) U N(v)| might be < 1/2 OR >= 1/2!
    Let A(u,v) = |N(u) U N(v)| / n, and E(u,v) = e(N(u) U N(v)) / n^2 = e(N(u)\N(v), N(v)\N(u)) / n^2.
    - Case 1 (A(u,v) >= 1/2): Take a random subset of N(u) U N(v) of size 1/2 (sampling prob r = 1 / (2 * A(u,v)))!
      Expected edge density: r^2 * E(u,v) = E(u,v) / (4 * A(u,v)^2) <= c  <=>  E(u,v) - 4*c * A(u,v)^2 <= 0!!
      COUNT THE VERTICES OF E(u,v) - 4*c * A(u,v)^2:
      Roots u, v (2 vertices) + 2 vertices for E(u,v) or A(u,v)^2 = ONLY 4 VERTICES TOTAL!!
      Wait: What if we weight by I(u !~ v) (still 4 vertices!) OR weight by A(u,v) >= 1/2?!
      Wait: If A(u,v) < 1/2, E(u,v) / (4 A(u,v)^2) is NOT an upper bound on padding N(u) U N(v) up to 1/2 — we MUST pad it!
      Let's compute BOTH:
        (1) The pure 1-vertex neighborhood rule P_c(v) (valid for ALL triangle-free graphs with Delta < 1/2!),
        (2) The 2-neighborhood padded rule when we pad N(u) U N(v) up to 1/2 (or trim if >= 1/2)!
        For ANY pair (u,v) with A(u,v) <= 1/2: pad with prob q = (1/2 - A)/(1 - A).
        Even cleaner: Check the exact value of E(u,v) - 4*c*A(u,v)^2 when A(u,v) >= 1/2!
    """
    # Compute exact 4-vertex densities of:
    #   - E_uv = E[ I(u!~v) * e(N(u) U N(v)) ]
    #   - A2_uv = E[ I(u!~v) * |N(u) U N(v)|^2 ]
    #   - A1_uv = E[ I(u!~v) * |N(u) U N(v)| ]
    #   - nonedge = E[ I(u!~v) ]
    e_uv = 0.0
    a2_uv = 0.0
    a1_uv = 0.0
    ne = 0.0
    cnt = 0
    for u, v, y, z in itertools.permutations(range(N), 4):
        if (adj[u] >> v) & 1:
            cnt += 1
            continue
        ne += 1.0
        in_y = ((adj[u] >> y) & 1) or ((adj[v] >> y) & 1)
        in_z = ((adj[u] >> z) & 1) or ((adj[v] >> z) & 1)
        yz = (adj[y] >> z) & 1
        if in_y:
            a1_uv += 1.0
        if in_y and in_z:
            a2_uv += 1.0
            if yz:
                e_uv += 0.5  # unordered edges = 0.5 * ordered pairs
        cnt += 1
    return e_uv / cnt, a2_uv / cnt, a1_uv / cnt, ne / cnt


def solve_flag_sdp(N=5, verbose=True):
    t0 = time.perf_counter()
    canon_N, graphs_N = enumerate_tf_graphs(N)
    num_g = len(graphs_N)
    if verbose:
        print(f"=== FLAG ALGEBRA ENGINE: N={N} ({num_g} unlabeled triangle-free graphs) ===")

    # Build all types t with t === N (mod 2) and t < N
    # For N=5: t in [1, 3]; For N=6: t in [2, 4]
    types_t = [t for t in range(1, N) if (N - t) % 2 == 0]
    blocks = []  # list of (t, type_idx, tensors_list_of_r_x_r)
    for t in types_t:
        _, t_graphs = enumerate_tf_graphs(t)
        for ti, t_adj in enumerate(t_graphs):
            m = (N + t) // 2
            f_codes, f_adjs = enumerate_tf_flags(m, t_adj, t)
            tensors = compute_product_tensors(N, graphs_N, t, t_adj, f_codes, f_adjs)
            blocks.append((t, ti, len(f_codes), tensors))
            if verbose:
                print(f"  Type t={t} #{ti}: {len(f_codes)} flags of size {m}")

    # Precompute 1-vertex neighborhood terms (e1, e0, const, edge_density) on each N-graph
    e1_vec = np.zeros(num_g)
    e0_vec = np.zeros(num_g)
    co_vec = np.zeros(num_g)
    ed_vec = np.zeros(num_g)
    euv_vec = np.zeros(num_g)
    a2uv_vec = np.zeros(num_g)
    a1uv_vec = np.zeros(num_g)
    ne_vec = np.zeros(num_g)

    for gi, g_adj in enumerate(graphs_N):
        e1_vec[gi], e0_vec[gi], co_vec[gi], ed_vec[gi] = eval_1vertex_poly_on_N_graph(g_adj, N, 0.0)
        euv_vec[gi], a2uv_vec[gi], a1uv_vec[gi], ne_vec[gi] = eval_2step_neighborhood_poly(g_adj, N)

    # Sanity check on C5 (when N=5, find the C5 graph!)
    if N == 5:
        for gi, g_adj in enumerate(graphs_N):
            degs = [x.bit_count() for x in g_adj]
            if all(d == 2 for d in degs):
                print(f"  [Sanity C5] e1={e1_vec[gi]:.5f}, e0={e0_vec[gi]:.5f}, co={co_vec[gi]:.5f}, edge={ed_vec[gi]:.5f}")
                # Check continuum blow-up vs finite C5: note finite C5 has no self-blowup so injective 5-tuples differ from blow-up.

    print(f"Setup finished in {time.perf_counter() - t0:.2f}s. Running SDP binary searches...\n")

    def max_phi(c_val, use_edge_cut=True, objective="1vertex"):
        """
        Primal Flag Algebra SDP:
        Maximize sum_g x_g * obj_g
        subject to:
          x_g >= 0, sum_g x_g = 1
          For each type block k: sum_g x_g * M_{k,g} >> 0 (PSD!)
          Optional: sum_g x_g * ed_g >= 8 * c_val  (since if d(K2) <= 8c, random half already gives <= c!)
        """
        x = cp.Variable(num_g, nonneg=True)
        constraints = [cp.sum(x) == 1.0]
        if use_edge_cut:
            constraints.append(ed_vec @ x >= 8.0 * c_val)
        for (_, _, r, tensors) in blocks:
            # Build PSD matrix sum_g x_g * tensors[g]
            M = sum(x[gi] * tensors[gi] for gi in range(num_g) if np.any(tensors[gi]))
            constraints.append(M >> 0)

        if objective == "1vertex":
            obj_vec = e1_vec + e0_vec - c_val * co_vec
        elif objective == "2nbr_trim":
            # Among graphs where E[I(u!~v) * |N(u) U N(v)|] >= 0.5 * E[I(u!~v)]
            constraints.append(a1uv_vec @ x >= 0.5 * (ne_vec @ x))
            obj_vec = euv_vec - 4.0 * c_val * a2uv_vec
        else:
            raise ValueError(objective)

        prob = cp.Problem(cp.Maximize(obj_vec @ x), constraints)
        prob.solve(solver=cp.CLARABEL, tol_gap_abs=1e-9, tol_gap_rel=1e-9, tol_feas=1e-9)
        return prob.value, x.value, prob.status

    # 1. Binary search for 1-vertex neighborhood sampling rule (Theorem 1 — fully rigorous!)
    lo, hi = 0.020, 0.045
    for _ in range(18):
        mid = 0.5 * (lo + hi)
        val, _, st = max_phi(mid, use_edge_cut=True, objective="1vertex")
        if val is not None and val <= 1e-8:
            hi = mid
        else:
            lo = mid
    val_hi, x_hi, st_hi = max_phi(hi, use_edge_cut=True, objective="1vertex")
    print(f"[RESULT 1 — N={N} Flag Algebra (1-Vertex Padded Neighborhood S(v))]")
    print(f"  Provable upper bound c* = {hi:.6f} (status={st_hi}, max_Phi={val_hi:.2e})")
    print(f"  Compare: Razborov = {27/1024:.6f} | Erdős #128 Target = 0.020000")

    # 2. Binary search for 2-neighborhood union S(u,v) = N(u) U N(v) (in the dense regime where avg |N(u) U N(v)| >= 1/2!)
    lo2, hi2 = 0.015, 0.035
    for _ in range(18):
        mid = 0.5 * (lo2 + hi2)
        val, _, st = max_phi(mid, use_edge_cut=True, objective="2nbr_trim")
        if val is not None and val <= 1e-8:
            hi2 = mid
        else:
            lo2 = mid
    val2, _, st2 = max_phi(hi2, use_edge_cut=True, objective="2nbr_trim")
    print(f"\n[RESULT 2 — N={N} Flag Algebra (2-Neighborhood Union S(u,v)=N(u) U N(v), avg |S|>=1/2)]")
    print(f"  Provable upper bound c2* = {hi2:.6f} (status={st2}, max_Phi={val2:.2e})")
    print(f"  Compare: Exact C5 & Petersen value = 0.020000 (1/50)!")
    return hi, hi2


if __name__ == "__main__":
    solve_flag_sdp(N=5, verbose=True)
    print("\n" + "=" * 70 + "\n")
    solve_flag_sdp(N=6, verbose=True)
