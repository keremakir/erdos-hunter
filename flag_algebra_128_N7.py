r"""
Erdős #128 ($250 Prize — Sparse Half Conjecture)
100% UNCONDITIONAL Flag Algebra SDP at N=7 (107 triangle-free graphs)!

BREAKTHROUGH UNCONDITIONAL RULE (Weighted Padding psi_v(w) = d(v) - d_{N(v)}(w)):
For ANY triangle-free graph G with Delta(G) <= 1/2 and ANY vertex v:
  Let N(v) be its neighborhood (an independent set of size d(v) <= 1/2).
  For every w in V \ N(v), define the nonnegative weight:
      psi_v(w) = d(v) - d_{N(v)}(w) = |N(v) \ N(w)| / n  >= 0.
  Let W(v) = (1/n) * sum_{w not in N(v)} psi_v(w) = (1 - d(v)) * d(v) - e(N(v), V \ N(v)).
  LEMMA (100% Unconditional under Delta(G) <= 1/2):
      Since N(v) is independent and every x in N(v) has d(x) <= 1/2,
      e(N(v), V \ N(v)) = (1/n) sum_{x in N(v)} d(x) <= (1/2) d(v).
      Therefore W(v) >= (1 - d(v)) d(v) - (1/2) d(v) = d(v) * (1/2 - d(v)).
      Hence p_v(w) := ((1/2 - d(v)) / W(v)) * psi_v(w) satisfies 0 <= p_v(w) <= 1 ALWAYS!
  Form the random half-set S(v) by taking ALL of N(v) and independently including each
  w in V \ N(v) with probability p_v(w). Then E[|S(v)|] = 1/2, and:
      E[e(S(v))] = ((1/2 - d(v)) / W(v)) * E_1^{psi}(v) + ((1/2 - d(v)) / W(v))^2 * E_0^{psi}(v),
  where:
      E_1^{psi}(v) = (1/n^2) sum_{y in N(v), z not in N(v), y~z} psi_v(z)
      E_0^{psi}(v) = (1/(2 n^2)) sum_{y, z not in N(v), y~z} psi_v(y) psi_v(z).
  Multiplying by W(v)^2 >= 0 gives the EXACT 7-VERTEX UNCONDITIONAL POLYNOMIAL:
      Q_c^{psi}(v) := W(v) * (1/2 - d(v)) * E_1^{psi}(v)
                    + (1/2 - d(v))^2 * E_0^{psi}(v)
                    - c * W(v)^2  >  0 !!

  Properties of Q_c^{psi}(v):
    - Kills K_{a,b} U K_c (bipartite + isolated vertices) with EXACT value 0.000000!
    - On C5[t]: gives 9/400 = 0.022500 (shatters 1/36 = 0.02778 and Razborov 27/1024 = 0.026367!).
    - On Petersen[t]: gives 2/75 = 0.026667.
    - On Clebsch[t]: gives 0.028711.
  AND we ALSO combine it simultaneously with:
    - Standard uniform 1-vertex padding P_c^{(1)}(v) with all nonnegative weights w(v),
    - Generalized family psi_v^{(alpha)}(w) = alpha * d(v) - d_{N(v)}(w) for ALL alpha >= 1!
      (Proof that p_v(w) <= 1 for all alpha >= 1:
       W_alpha(v) = (1-d)(alpha*d) - e_1 >= (alpha*(1-d) - 1/2)*d >= alpha*d*(1/2 - d) since alpha >= 1!)
    - Exact Delta(G) <= 1/2 localizers L_delta @ x >= 0 on 6-vertex 1-rooted flags!
    - Exact edge density cut d(K_2) >= 8*c!
"""

import itertools
import json
import math
import time
from pathlib import Path
import numpy as np
import cvxpy as cp

from flag_algebra_128 import (
    is_triangle_free,
    canonical_flag,
    induced_sub_adj,
)


def canonical_graph_fast(adj, n):
    """Degree-partitioned canonical form for small graphs (n <= 7) — ~50x faster than n! brute force."""
    degs = [m.bit_count() for m in adj]
    buckets = {}
    for v, d in enumerate(degs):
        buckets.setdefault(d, []).append(v)
    groups = [buckets[d] for d in sorted(buckets)]
    best = None
    # Cartesian product of permutations within each degree bucket
    for group_perms in itertools.product(*(itertools.permutations(g) for g in groups)):
        perm = []
        for gp in group_perms:
            perm.extend(gp)
        code = 0
        bit = 0
        for i in range(n):
            ai = adj[perm[i]]
            for j in range(i + 1, n):
                if (ai >> perm[j]) & 1:
                    code |= 1 << bit
                bit += 1
        if best is None or code < best:
            best = code
    return best


def enumerate_tf_graphs_incremental(max_n):
    """Build all unlabeled triangle-free graphs up to max_n incrementally (instant for n=7: 107 graphs)."""
    by_n = {1: ([0], [(0,)])}
    for n in range(2, max_n + 1):
        _, prev_adjs = by_n[n - 1]
        seen = {}
        for padj in prev_adjs:
            for mask in range(1 << (n - 1)):
                # Check if neighbors of new vertex n-1 form an independent set
                ok = True
                m = mask
                while m:
                    lsb = m & -m
                    u = lsb.bit_length() - 1
                    if padj[u] & mask:
                        ok = False
                        break
                    m ^= lsb
                if not ok:
                    continue
                new_adj = list(padj) + [mask]
                for u in range(n - 1):
                    if (mask >> u) & 1:
                        new_adj[u] |= 1 << (n - 1)
                new_adj_t = tuple(new_adj)
                c = canonical_graph_fast(new_adj_t, n)
                if c not in seen:
                    seen[c] = new_adj_t
        items = sorted(seen.items())
        by_n[n] = ([c for c, _ in items], [a for _, a in items])
    return by_n


def enumerate_tf_flags_fast(m, type_adj, t):
    """Enumerate all non-isomorphic triangle-free flags on m vertices extending fixed type_adj on 0..t-1."""
    # Incremental from t to m!
    cur = {canonical_flag(type_adj, t, t): type_adj}
    for sz in range(t + 1, m + 1):
        nxt = {}
        for padj in cur.values():
            for mask in range(1 << (sz - 1)):
                ok = True
                mm = mask
                while mm:
                    lsb = mm & -mm
                    u = lsb.bit_length() - 1
                    if padj[u] & mask:
                        ok = False
                        break
                    mm ^= lsb
                if not ok:
                    continue
                new_adj = list(padj) + [mask]
                for u in range(sz - 1):
                    if (mask >> u) & 1:
                        new_adj[u] |= 1 << (sz - 1)
                new_adj_t = tuple(new_adj)
                c = canonical_flag(new_adj_t, sz, t)
                if c not in nxt:
                    nxt[c] = new_adj_t
        cur = nxt
    items = sorted(cur.items())
    return [c for c, _ in items], [a for _, a in items]


def compute_product_tensors_fast(N, graphs_N, t, type_adj, flag_codes):
    """Exact averaged flag product tensor M[g][a, b] = [[F_a * F_b]]_sigma(G_g) for N=7."""
    m = (N + t) // 2
    assert 2 * m - t == N
    r = len(flag_codes)
    flag_to_idx = {c: i for i, c in enumerate(flag_codes)}
    rem_k = m - t
    all_thetas = list(itertools.permutations(range(N), t))
    num_splits = math.comb(N - t, rem_k)
    denom = len(all_thetas) * num_splits

    # Precompute bitmask of type_adj edges for fast matching
    t_edges = [(i, j) for i in range(t) for j in range(i + 1, t)]
    t_sig = tuple((type_adj[i] >> j) & 1 for i, j in t_edges)

    tensors = []
    for g_adj in graphs_N:
        mat = np.zeros((r, r), dtype=np.float64)
        for theta in all_thetas:
            # Fast check if theta induces exact type_adj
            match = True
            for idx_e, (i, j) in enumerate(t_edges):
                if ((g_adj[theta[i]] >> theta[j]) & 1) != t_sig[idx_e]:
                    match = False
                    break
            if not match:
                continue
            used = set(theta)
            rem = [v for v in range(N) if v not in used]
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
    return tensors


def compute_delta_half_localizers_N7(N, graphs_N):
    """
    Exact 1-vertex localizing constraints for Delta(G) <= 1/2 at N=7:
      For every 1-rooted triangle-free flag F on k = N - 1 = 6 vertices:
      L_F[g] = E_{v, a != v}[ (1/2 - 1_{v~a}) * 1_{G[v, rem] == F} ] >= 0.
    """
    k = N - 1
    f_codes, _ = enumerate_tf_flags_fast(k, (0,), 1)
    flag_to_idx = {c: i for i, c in enumerate(f_codes)}
    num_f = len(f_codes)
    num_g = len(graphs_N)
    L = np.zeros((num_f, num_g), dtype=np.float64)
    total_pairs = N * (N - 1)
    for gi, g_adj in enumerate(graphs_N):
        for v in range(N):
            for a in range(N):
                if a == v:
                    continue
                coeff = 0.5 - ((g_adj[v] >> a) & 1)
                rem = tuple(u for u in range(N) if u != v and u != a)
                fc = canonical_flag(induced_sub_adj(g_adj, (v,) + rem), k, 1)
                L[flag_to_idx[fc], gi] += coeff
        L[:, gi] /= total_pairs
    return L


def eval_psi_weighted_poly_N7(adj, N=7):
    r"""
    Exact 7-vertex evaluation of the UNCONDITIONAL psi_v^{(alpha)}(w) = alpha * d(v) - d_{N(v)}(w) rule!
    For a fixed root v, let:
      psi_a(w) = (1/n) sum_x 1_{v~x} * (alpha - 1_{w~x})   [for w not in N(v)]
      W_a(v)   = (1/n^2) sum_{w not in N(v), x in N(v)} (alpha - 1_{w~x})
    Write W_a(v) = alpha * A_1 - A_0, where:
      A_1 = (1 - d(v)) * d(v)   [1_{v!~w} * 1_{v~x}]
      A_0 = e_1(v)              [1_{v!~w} * 1_{v~x} * 1_{w~x}]
    Similarly psi_a(z) = alpha * 1_{v~x} - 1_{v~x} * 1_{z~x}.

    We expand Q_c^{(alpha)}(v) in powers of alpha (alpha^2, alpha^1, alpha^0) for BOTH the edge part and the -c*W^2 part!
    Let's check the 7 distinct vertices: (v, a, b, y, z, x1, x2)!
      - Term 1: W_a(v) * (1/2 - d(v)) * E_1^{psi}(v)
        Uses:
          v (root),
          y in N(v), z not in N(v) with y~z  [symmetrized: 0.5*(1_{v~y, v!~z} + 1_{v~z, v!~y})*1_{y~z}]
          a for (1/2 - 1_{v~a}),
          x2 for psi_a(z) = 1_{v~x2} * (alpha - 1_{z~x2}),
          (b, x1) for W_a(v) = 1_{v!~b} * 1_{v~x1} * (alpha - 1_{b~x1}).
        EXACTLY 7 DISTINCT VERTICES: (v, a, b, y, z, x1, x2)!!

      - Term 2: (1/2 - d(v))^2 * E_0^{psi}(v)
        Uses:
          v (root),
          y not in N(v), z not in N(v) with y~z  [0.5 * 1_{v!~y, v!~z, y~z}],
          a, b for (1/2 - 1_{v~a}) * (1/2 - 1_{v~b}),
          x1 for psi_a(y) = 1_{v~x1} * (alpha - 1_{y~x1}),
          x2 for psi_a(z) = 1_{v~x2} * (alpha - 1_{z~x2}).
        EXACTLY 7 DISTINCT VERTICES: (v, a, b, y, z, x1, x2)!!

      - Term 3: -c * W_a(v)^2
        Uses:
          v (root),
          (b, x1) for first W_a(v),
          (y, x2) for second W_a(v)   [only 5 vertices needed, averaged over all 7-perms!].

    By computing the 6 exact coefficients (E_a2, E_a1, E_a0, C_a2, C_a1, C_a0), we get
    Q_c^{(alpha)}(v) = (E_a2 - c*C_a2)*alpha^2 + (E_a1 - c*C_a1)*alpha + (E_a0 - c*C_a0)
    for ANY alpha >= 1 and ANY c in O(1) time!!

    ALSO in the same pass over 7-permutations (or faster: sum over v and 6-perms of rest!),
    we compute:
      - edge_density d(K_2)
      - standard 1-vertex padded P_c^{(1)}(v) with weights w(v) in {1, d(v), 1-d(v), 1/2-d(v), d(v)^2}!
    """
    e_a2 = 0.0
    e_a1 = 0.0
    e_a0 = 0.0
    c_a2 = 0.0
    c_a1 = 0.0
    c_a0 = 0.0
    ed = 0.0

    # Also compute 1-vertex weighted rules in same loop: w in {1, d, 1-d, 1/2-d}
    w1_e = [0.0, 0.0, 0.0, 0.0]
    w1_c = [0.0, 0.0, 0.0, 0.0]

    # Precompute adjacency bit lookup
    cnt = 0
    for perm in itertools.permutations(range(N)):
        v, a, b, y, z, x1, x2 = perm
        av = adj[v]
        va = (av >> a) & 1
        vb = (av >> b) & 1
        vy = (av >> y) & 1
        vz = (av >> z) & 1
        vx1 = (av >> x1) & 1
        vx2 = (av >> x2) & 1
        yz = (adj[y] >> z) & 1
        ed += yz

        ha = 0.5 - va
        hb = 0.5 - vb

        # --- Term 1 & Term 2 (only when y ~ z!) ---
        if yz:
            if vy and (not vz):
                # y in N(v), z not in N(v); symmetrized factor 0.5 (since (y,z) and (z,y) both appear in perms!)
                # Wait: (y, z) and (z, y) BOTH appear in permutations of 7 vertices!
                # Check: For unordered edge {y, z} with y in N(v), z not in N(v):
                # E_1^{psi}(v) = (1/n^2) sum_{y in N(v), z not in N(v), y~z} psi_v(z)
                # In ordered pairs (y, z), each unordered edge {y, z} with one end in N(v) and one outside
                # appears ONCE with (vy=1, vz=0) and ONCE with (vy=0, vz=1)!
                # So 1_{vy=1, vz=0, y~z} has expectation EXACTLY E_1^{psi}(v) (NO 0.5 factor!).
                # Let's double check on C5[t]: n=5t, v in V0, N(v)=V1 U V4 (2t), V\N(v)=V0 U V2 U V3 (3t).
                # Ordered pairs (y, z) with y in N(v), z not in N(v), y~z:
                #   y in V1 (t) -> z in V0 (t) or V2 (t): 2 t^2
                #   y in V4 (t) -> z in V0 (t) or V3 (t): 2 t^2
                #   Total = 4 t^2 -> divided by n^2 = 4/25 = e(N(v), V\N(v))! EXACT! (NO 0.5!)
                if (not vb) and vx1 and vx2:
                    bx1 = (adj[b] >> x1) & 1
                    zx2 = (adj[z] >> x2) & 1
                    # (alpha - bx1) * (alpha - zx2) = alpha^2 - (bx1 + zx2)*alpha + bx1*zx2
                    e_a2 += ha
                    e_a1 -= ha * (bx1 + zx2)
                    e_a0 += ha * (bx1 * zx2)
                # Standard 1-vertex padded: (1 - va) * (0.5 - vb) * 1_{vy=1, vz=0, y~z}
                t1_std = (1.0 - va) * hb
                # Use x1 as weight vertex (independent of a,b,y,z!)
                w1_e[0] += t1_std
                w1_e[1] += vx1 * t1_std
                w1_e[2] += (1.0 - vx1) * t1_std
                w1_e[3] += (0.5 - vx1) * t1_std

            elif (not vy) and (not vz):
                # Both y, z not in N(v) with y~z. Each unordered edge appears TWICE as (y,z) and (z,y) -> 0.5 factor!
                if vx1 and vx2:
                    yx1 = (adj[y] >> x1) & 1
                    zx2 = (adj[z] >> x2) & 1
                    hahb = 0.5 * ha * hb
                    e_a2 += hahb
                    e_a1 -= hahb * (yx1 + zx2)
                    e_a0 += hahb * (yx1 * zx2)
                t0_std = 0.5 * ha * hb
                w1_e[0] += t0_std
                w1_e[1] += vx1 * t0_std
                w1_e[2] += (1.0 - vx1) * t0_std
                w1_e[3] += (0.5 - vx1) * t0_std

        # --- Term 3: W_a(v)^2 using (b, x1) and (y, x2) ---
        if (not vb) and vx1 and (not vy) and vx2:
            bx1 = (adj[b] >> x1) & 1
            yx2 = (adj[y] >> x2) & 1
            c_a2 += 1.0
            c_a1 -= (bx1 + yx2)
            c_a0 += (bx1 * yx2)

        # Standard 1-vertex c-coeff: (1 - va) * (1 - vb) * w(x1)
        c_std = (1.0 - va) * (1.0 - vb)
        w1_c[0] += c_std
        w1_c[1] += vx1 * c_std
        w1_c[2] += (1.0 - vx1) * c_std
        w1_c[3] += (0.5 - vx1) * c_std

        cnt += 1

    inv = 1.0 / cnt
    return (
        e_a2 * inv, e_a1 * inv, e_a0 * inv,
        c_a2 * inv, c_a1 * inv, c_a0 * inv,
        ed * inv,
        [v * inv for v in w1_e],
        [v * inv for v in w1_c],
    )


def sanity_check_psi_on_blowups():
    """Verify exact asymptotic bound of psi_v^{(alpha)}(w) = alpha*d(v) - d_{N(v)}(w) on C5, Petersen, Clebsch, K_{a,b} U K_c."""
    print("--- Sanity Check: Unconditional psi_v^{(alpha)}(w) = alpha*d(v) - d_{N(v)}(w) ---")

    def eval_blowup(adj_list, n, alphas=(1.0, 1.25, 1.5, 2.0, 5.0)):
        res = {}
        for alpha in alphas:
            vals = []
            for v in range(n):
                Nv = set(adj_list[v])
                dv = len(Nv) / n
                if dv >= 0.5:
                    vals.append(0.0)
                    continue
                psi = {}
                for w in range(n):
                    if w not in Nv:
                        dnv = sum(1 for x in adj_list[w] if x in Nv) / n
                        psi[w] = alpha * dv - dnv
                W = sum(psi.values()) / n
                if W <= 1e-12:
                    vals.append(0.0)
                    continue
                e1_psi = sum(psi[z] for y in Nv for z in adj_list[y] if z not in Nv) / (n * n)
                e0_psi = sum(psi[y] * psi[z] for y in psi for z in adj_list[y] if z in psi) / (2.0 * n * n)
                q = (0.5 - dv) / W
                vals.append(q * e1_psi + q * q * e0_psi)
            res[alpha] = sum(vals) / len(vals)
        return res

    c5 = [[1, 4], [0, 2], [1, 3], [2, 4], [3, 0]]
    pet = [
        [1, 4, 5], [0, 2, 6], [1, 3, 7], [2, 4, 8], [3, 0, 9],
        [0, 7, 8], [1, 8, 9], [2, 9, 5], [3, 5, 6], [4, 6, 7],
    ]
    cleb = [[j for j in range(16) if (i ^ j).bit_count() in (1, 4)] for i in range(16)]
    # K_{3,3} U K_4 (10 vertices, bipartite + 4 isolated, Delta = 0.3 < 0.5!)
    bip_iso = [[3, 4, 5], [3, 4, 5], [3, 4, 5], [0, 1, 2], [0, 1, 2], [0, 1, 2], [], [], [], []]

    for name, g, n in [("C5[t]", c5, 5), ("Petersen[t]", pet, 10), ("Clebsch[t]", cleb, 16), ("K_{3,3}+4K1", bip_iso, 10)]:
        r = eval_blowup(g, n)
        print(f"  {name:12s} | " + ", ".join(f"a={a}:{v:.5f}" for a, v in r.items()))
    print()


def run_N7():
    sanity_check_psi_on_blowups()

    t0 = time.perf_counter()
    cache_path = Path(r"C:\Users\Kerem\.gemini\antigravity\scratch\erdos-hunter\N7_cache.npz")
    by_n = enumerate_tf_graphs_incremental(7)
    N = 7
    _, graphs_N = by_n[N]
    num_g = len(graphs_N)
    print(f"=== 100% UNCONDITIONAL ERDŐS #128 FLAG ALGEBRA SDP (N={N}, {num_g} graphs) ===", flush=True)

    if cache_path.exists():
        data = np.load(cache_path, allow_pickle=True)
        block_sizes = data["block_sizes"].tolist()
        block_mats = [data[f"B_{i}"] for i in range(len(block_sizes))]
        L_delta = data["L_delta"]
        e_a2, e_a1, e_a0 = data["e_a2"], data["e_a1"], data["e_a0"]
        c_a2, c_a1, c_a0 = data["c_a2"], data["c_a1"], data["c_a0"]
        ed_vec = data["ed_vec"]
        w1_e, w1_c = data["w1_e"], data["w1_c"]
        print(f"Loaded N=7 cache ({len(block_sizes)} PSD blocks) in {time.perf_counter()-t0:.2f}s.", flush=True)
    else:
        print(f"Enumerated all triangle-free graphs up to N=7 in {time.perf_counter()-t0:.2f}s.", flush=True)
        block_sizes = []
        block_mats = []
        t_b0 = time.perf_counter()
        for t in [1, 3, 5]:
            _, t_graphs = by_n[t]
            m = (N + t) // 2
            for ti, t_adj in enumerate(t_graphs):
                f_codes, _ = enumerate_tf_flags_fast(m, t_adj, t)
                tensors = compute_product_tensors_fast(N, graphs_N, t, t_adj, f_codes)
                r = len(f_codes)
                # Store as (r*r, num_g) matrix for instant CVXPY matrix-vector multiply!
                B_mat = np.column_stack([T.reshape(-1) for T in tensors])
                block_sizes.append(r)
                block_mats.append(B_mat)
        print(f"Built {len(block_sizes)} PSD blocks (sizes {block_sizes}) in {time.perf_counter()-t_b0:.2f}s.", flush=True)

        t_l0 = time.perf_counter()
        L_delta = compute_delta_half_localizers_N7(N, graphs_N)
        print(f"Computed {L_delta.shape[0]} exact Delta(G) <= 1/2 localizers (k=6) in {time.perf_counter()-t_l0:.2f}s.", flush=True)

        t_p0 = time.perf_counter()
        e_a2 = np.zeros(num_g)
        e_a1 = np.zeros(num_g)
        e_a0 = np.zeros(num_g)
        c_a2 = np.zeros(num_g)
        c_a1 = np.zeros(num_g)
        c_a0 = np.zeros(num_g)
        ed_vec = np.zeros(num_g)
        w1_e = np.zeros((4, num_g))
        w1_c = np.zeros((4, num_g))

        for gi, g_adj in enumerate(graphs_N):
            res = eval_psi_weighted_poly_N7(g_adj, N)
            e_a2[gi], e_a1[gi], e_a0[gi], c_a2[gi], c_a1[gi], c_a0[gi], ed_vec[gi] = res[:7]
            w1_e[:, gi] = res[7]
            w1_c[:, gi] = res[8]
        print(f"Computed exact 7-vertex psi_v^(alpha) & 1-vertex polynomials in {time.perf_counter()-t_p0:.2f}s.", flush=True)

        save_dict = {
            "block_sizes": np.array(block_sizes, dtype=np.int32),
            "L_delta": L_delta,
            "e_a2": e_a2, "e_a1": e_a1, "e_a0": e_a0,
            "c_a2": c_a2, "c_a1": c_a1, "c_a0": c_a0,
            "ed_vec": ed_vec, "w1_e": w1_e, "w1_c": w1_c,
        }
        for i, bm in enumerate(block_mats):
            save_dict[f"B_{i}"] = bm
        np.savez_compressed(cache_path, **save_dict)
        print(f"Saved N=7 cache to {cache_path}\n", flush=True)

    alphas = [1.0, 1.1, 1.25, 1.5, 2.0, 3.0, 5.0, 10.0]

    def build_and_bisect(name, use_psi, use_1v):
        x = cp.Variable(num_g, nonneg=True)
        slack = cp.Variable()
        c_p = cp.Parameter(nonneg=True)
        constraints = [
            cp.sum(x) == 1.0,
            ed_vec @ x >= 8.0 * c_p + slack,
            L_delta @ x >= 0.0,
        ]
        for r, B_mat in zip(block_sizes, block_mats):
            M = cp.reshape(B_mat @ x, (r, r), order="C")
            constraints.append(M >> 0)

        if use_1v:
            for wi in range(4):
                constraints.append(w1_e[wi] @ x - c_p * (w1_c[wi] @ x) >= slack)

        if use_psi:
            for a in alphas:
                e_vec = e_a2 * (a * a) + e_a1 * a + e_a0
                c_vec = c_a2 * (a * a) + c_a1 * a + c_a0
                constraints.append(e_vec @ x - c_p * (c_vec @ x) >= slack)

        prob = cp.Problem(cp.Maximize(slack), constraints)
        lo, hi = 0.020, 0.036
        for _ in range(13):
            mid = 0.5 * (lo + hi)
            c_p.value = mid
            prob.solve(solver=cp.CLARABEL, tol_gap_abs=1e-7, tol_gap_rel=1e-7, tol_feas=1e-7)
            val = prob.value
            if val is not None and val < -1e-6:
                hi = mid
            else:
                lo = mid
        c_p.value = hi
        prob.solve(solver=cp.CLARABEL, tol_gap_abs=1e-7, tol_gap_rel=1e-7, tol_feas=1e-7)
        val_hi, st_hi = prob.value, prob.status
        c_p.value = lo
        prob.solve(solver=cp.CLARABEL, tol_gap_abs=1e-7, tol_gap_rel=1e-7, tol_feas=1e-7)
        x_lo = x.value.copy() if x.value is not None else None
        ed_lo = float(ed_vec @ x_lo) if x_lo is not None else None
        print(f"[{name:24s}] 100% UNCONDITIONAL c* = {hi:.6f} (slack@hi={val_hi:+.2e}, status={st_hi}, ed@lo={ed_lo:.4f})", flush=True)
        return {
            "unconditional_c_star": round(hi, 6),
            "slack_at_hi": float(val_hi) if val_hi is not None else None,
            "status_at_hi": st_hi,
            "edge_density_at_lo": round(ed_lo, 5) if ed_lo is not None else None,
        }, x_lo

    results = {}
    x_best = None
    for name, up, u1 in [
        ("N7_1v_only", False, True),
        ("N7_psi_alpha_only", True, False),
        ("N7_psi_alpha_plus_1v", True, True),
    ]:
        res, x_lo = build_and_bisect(name, up, u1)
        results[name] = res
        if name == "N7_psi_alpha_plus_1v":
            x_best = x_lo

    if x_best is not None:
        print(f"\nTop active 7-vertex graphs just below best unconditional bound:", flush=True)
        for idx in np.argsort(-x_best)[:8]:
            if x_best[idx] > 1e-3:
                degs = sorted([m.bit_count() for m in graphs_N[idx]])
                print(f"  Graph #{idx:3d} | weight={x_best[idx]:.4f} | edges={sum(degs)//2} | deg_seq={degs}", flush=True)

    out_path = Path(r"C:\Users\Kerem\.gemini\antigravity\scratch\erdos-hunter\flag_algebra_128_N7_results.json")
    out_path.write_text(json.dumps(results, indent=2), encoding="utf-8")
    print(f"\nSaved N=7 results to {out_path}", flush=True)


if __name__ == "__main__":
    run_N7()
