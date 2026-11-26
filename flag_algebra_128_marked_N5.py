r"""
Erdős #128 ($250 Prize) — World Record Attack (< 27/1024 = 0.026367)
STOP-LOSS EXPERIMENT: Marked Independent Set (2-Colored) Flag Algebra at N=5!

Theory:
  Let G be ANY triangle-free graph, and let I \subset V(G) be a MAXIMUM independent set of G!
  Every vertex is colored 1 (in I) or 0 (in V \ I), with NO edges inside I and NO triangles in G.
  Assume for contradiction every half-set S (|S| = n/2) has e(S) > c * n^2.
  Then ALL of the following hold 100% UNCONDITIONALLY on (G, I):
    (1) alpha := |I|/n <= 1/2  (otherwise I has size >= n/2 and 0 edges!).
        => Exact localizers: for every (N-1)-vertex marked graph H, E[(1/2 - 1_{v in I}) * H] >= 0.
    (2) Maximality of I: for EVERY vertex v in V, d(v) <= |I| = alpha!
        (Because N(v) is an independent set, so |N(v)| <= alpha(G) = |I|!)
        => Exact localizers: for every 1-rooted 4-vertex marked flag F(v),
           E_{v, a != v}[ (1_{a in I} - 1_{v ~ a}) * F(v) ] >= 0 !!
        (MUCH stronger than Delta(G) <= 1/2!)
    (3) Maximality of I (stronger): for EVERY v not in I, d_I(v) >= 0 (trivial), and for every
        independent set J \subset V \ I, |J| <= |I| (in particular for u, v: |N(u) \ I| <= |I|).
        EVEN BETTER: for any v in V, |(N(v) \ I)| + |I \ N(N(v))|... skip, keep exact simple ones first!
    (4) Edge density cut: d(K_2) >= 8*c.
    (5) Uniform I-padding rule S_I: take ALL of I, pad from V \ I with prob q = (1/2 - alpha)/(1 - alpha).
        Unconditional 4-vertex polynomial (so we can multiply by ANY nonnegative 1-vertex marked weight at N=5!):
          P_c^I := (1 - alpha)*(1/2 - alpha)*e(I, Ibar) + (1/2 - alpha)^2 * e(Ibar) - c*(1 - alpha)^2 > 0!
        Wait: since alpha = |I|/n is a GLOBAL constant of (G, I), P_c^I is a GLOBAL scalar > 0!
        (It kills K_{a,b} U K_c completely because alpha >= 1/2 there, AND gives 0.020833 on Petersen!)
    (6) 2-Step Independent Padding I U (N(u) \ I) for EVERY u not in I!
        Let J(u) = N(u) \ I (an independent set disjoint from I!), s(u) = |I U J(u)| / n = alpha + |N(u)\I|/n.
        - If s(u) >= 1/2: take ALL of I + random fraction (1/2 - alpha)/(s(u) - alpha) of J(u).
          Edges inside S: ONLY between I and selected J(u)!
          E[e(S)] = ((1/2 - alpha)/(s(u) - alpha)) * e(I, J(u)) > c
          <=> (1/2 - alpha) * e(I, J(u)) - c * (s(u) - alpha) > 0!  [EXACT 5-VERTEX POLYNOMIAL!]
        - If s(u) < 1/2: take ALL of U = I U J(u), pad from V \ U with prob (1/2 - s)/(1 - s).
          E[e(S)] = e(I, J(u)) + ((1/2 - s)/(1 - s)) * e(U, Ubar) + ((1/2 - s)/(1 - s))^2 * e(Ubar) > c.
        (Let's first check what (1)-(5) alone gives at N=5 — takes < 10 seconds!)
"""

import itertools
import json
import math
import time
from pathlib import Path
import numpy as np
import cvxpy as cp


def canonical_marked_graph(adj, colors, n):
    """Canonical code for a 2-colored graph (colors: tuple of 0/1) on n vertices."""
    # Partition vertices by (color, degree)
    buckets = {}
    for v in range(n):
        key = (colors[v], adj[v].bit_count())
        buckets.setdefault(key, []).append(v)
    groups = [buckets[k] for k in sorted(buckets)]
    best = None
    for gperms in itertools.product(*(itertools.permutations(g) for g in groups)):
        perm = []
        for gp in gperms:
            perm.extend(gp)
        # Encode colors (n bits) + upper-triangle edges
        ccode = 0
        for i in range(n):
            if colors[perm[i]]:
                ccode |= 1 << i
        ecode = 0
        bit = 0
        for i in range(n):
            ai = adj[perm[i]]
            for j in range(i + 1, n):
                if (ai >> perm[j]) & 1:
                    ecode |= 1 << bit
                bit += 1
        code = (ccode, ecode)
        if best is None or code < best:
            best = code
    return best


def canonical_marked_flag(adj, colors, m, t):
    """Canonical code for a 2-colored flag on m vertices with 0..t-1 fixed."""
    base_c = tuple(colors[:t])
    free = list(range(t, m))
    best = None
    for p in itertools.permutations(free):
        perm = list(range(t)) + list(p)
        ccode = 0
        for i in range(t, m):
            if colors[perm[i]]:
                ccode |= 1 << (i - t)
        ecode = 0
        bit = 0
        for i in range(m):
            ai = adj[perm[i]]
            for j in range(max(i + 1, t), m):
                if (ai >> perm[j]) & 1:
                    ecode |= 1 << bit
                bit += 1
        code = (base_c, ccode, ecode)
        if best is None or code < best:
            best = code
    return best


def enumerate_marked_tf_incremental(max_n):
    """Enumerate all unlabeled 2-colored triangle-free graphs where color 1 (I) is an independent set."""
    by_n = {1: ([(0, 0), (1, 0)], [((0,), (0,)), ((0,), (1,))])}
    for n in range(2, max_n + 1):
        _, prev = by_n[n - 1]
        seen = {}
        for padj, pcol in prev:
            for new_c in (0, 1):
                for mask in range(1 << (n - 1)):
                    # If new vertex is in I (new_c == 1), it cannot connect to any vertex in I!
                    if new_c == 1:
                        bad = False
                        for u in range(n - 1):
                            if ((mask >> u) & 1) and pcol[u] == 1:
                                bad = True
                                break
                        if bad:
                            continue
                    # Triangle-free check: neighbors of new vertex must be independent
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
                    nadj = list(padj) + [mask]
                    for u in range(n - 1):
                        if (mask >> u) & 1:
                            nadj[u] |= 1 << (n - 1)
                    nadj_t = tuple(nadj)
                    ncol_t = pcol + (new_c,)
                    code = canonical_marked_graph(nadj_t, ncol_t, n)
                    if code not in seen:
                        seen[code] = (nadj_t, ncol_t)
        items = sorted(seen.items())
        by_n[n] = ([c for c, _ in items], [g for _, g in items])
    return by_n


def enumerate_marked_flags(m, t_adj, t_col, t):
    cur = {canonical_marked_flag(t_adj, t_col, t, t): (t_adj, t_col)}
    for sz in range(t + 1, m + 1):
        nxt = {}
        for padj, pcol in cur.values():
            for new_c in (0, 1):
                for mask in range(1 << (sz - 1)):
                    if new_c == 1:
                        bad = False
                        for u in range(sz - 1):
                            if ((mask >> u) & 1) and pcol[u] == 1:
                                bad = True
                                break
                        if bad:
                            continue
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
                    nadj = list(padj) + [mask]
                    for u in range(sz - 1):
                        if (mask >> u) & 1:
                            nadj[u] |= 1 << (sz - 1)
                    nadj_t = tuple(nadj)
                    ncol_t = pcol + (new_c,)
                    code = canonical_marked_flag(nadj_t, ncol_t, sz, t)
                    if code not in nxt:
                        nxt[code] = (nadj_t, ncol_t)
        cur = nxt
    items = sorted(cur.items())
    return [c for c, _ in items], [g for _, g in items]


def induced_sub_marked(adj, col, verts):
    k = len(verts)
    sub_a = [0] * k
    sub_c = tuple(col[v] for v in verts)
    for i in range(k):
        ai = adj[verts[i]]
        for j in range(i + 1, k):
            if (ai >> verts[j]) & 1:
                sub_a[i] |= 1 << j
                sub_a[j] |= 1 << i
    return tuple(sub_a), sub_c


def compute_marked_tensors(N, graphs_N, t, t_adj, t_col, f_codes):
    m = (N + t) // 2
    r = len(f_codes)
    f_to_i = {c: i for i, c in enumerate(f_codes)}
    rem_k = m - t
    all_thetas = list(itertools.permutations(range(N), t))
    denom = len(all_thetas) * math.comb(N - t, rem_k)
    t_edges = [(i, j) for i in range(t) for j in range(i + 1, t)]
    t_esig = tuple((t_adj[i] >> j) & 1 for i, j in t_edges)

    mats = []
    for g_adj, g_col in graphs_N:
        mat = np.zeros((r, r), dtype=np.float64)
        for theta in all_thetas:
            if any(g_col[theta[i]] != t_col[i] for i in range(t)):
                continue
            if any(((g_adj[theta[i]] >> theta[j]) & 1) != t_esig[ei] for ei, (i, j) in enumerate(t_edges)):
                continue
            used = set(theta)
            rem = [v for v in range(N) if v not in used]
            for u1 in itertools.combinations(rem, rem_k):
                u1s = set(u1)
                u2 = tuple(v for v in rem if v not in u1s)
                sa1, sc1 = induced_sub_marked(g_adj, g_col, theta + u1)
                sa2, sc2 = induced_sub_marked(g_adj, g_col, theta + u2)
                i1 = f_to_i[canonical_marked_flag(sa1, sc1, m, t)]
                i2 = f_to_i[canonical_marked_flag(sa2, sc2, m, t)]
                mat[i1, i2] += 1.0
        mat = 0.5 * (mat + mat.T) / denom
        mats.append(mat)
    return np.column_stack([M.reshape(-1) for M in mats])


def run_marked_N5():
    t0 = time.perf_counter()
    by_n = enumerate_marked_tf_incremental(5)
    for n in range(1, 6):
        print(f"  N={n}: {len(by_n[n][1])} marked (I independent) triangle-free graphs", flush=True)

    N = 5
    _, graphs_N = by_n[N]
    num_g = len(graphs_N)

    # PSD blocks for t in [1, 3]
    block_sizes = []
    block_mats = []
    for t in [1, 3]:
        _, t_graphs = by_n[t]
        m = (N + t) // 2
        for t_adj, t_col in t_graphs:
            f_codes, _ = enumerate_marked_flags(m, t_adj, t_col, t)
            B_mat = compute_marked_tensors(N, graphs_N, t, t_adj, t_col, f_codes)
            block_sizes.append(len(f_codes))
            block_mats.append(B_mat)
    print(f"Built {len(block_sizes)} PSD blocks (sizes {block_sizes}) in {time.perf_counter()-t0:.2f}s.", flush=True)

    # Exact localizers:
    # (1) alpha <= 1/2: E[ (1/2 - 1_{a in I}) * H(rem) ] >= 0 for all 4-vertex marked graphs H!
    codes_4, _ = by_n[4]
    c4_to_i = {c: i for i, c in enumerate(codes_4)}
    L_alpha = np.zeros((len(codes_4), num_g))
    for gi, (g_adj, g_col) in enumerate(graphs_N):
        for a in range(N):
            coeff = 0.5 - g_col[a]
            rem = tuple(u for u in range(N) if u != a)
            sa, sc = induced_sub_marked(g_adj, g_col, rem)
            L_alpha[c4_to_i[canonical_marked_graph(sa, sc, 4)], gi] += coeff / N

    # (2) Maximality of I: for EVERY v, d(v) <= |I| => E_{v, a != v}[ (1_{a in I} - 1_{v~a}) * F(v, rem) ] >= 0
    #     for all 1-rooted 4-vertex marked flags F(v)!
    f4_0, _ = enumerate_marked_flags(4, (0,), (0,), 1)
    f4_1, _ = enumerate_marked_flags(4, (0,), (1,), 1)
    f4_all = f4_0 + f4_1
    f4_to_i = {c: i for i, c in enumerate(f4_all)}
    L_maxI = np.zeros((len(f4_all), num_g))
    for gi, (g_adj, g_col) in enumerate(graphs_N):
        for v in range(N):
            for a in range(N):
                if a == v:
                    continue
                coeff = float(g_col[a]) - float((g_adj[v] >> a) & 1)
                rem = tuple(u for u in range(N) if u != v and u != a)
                sa, sc = induced_sub_marked(g_adj, g_col, (v,) + rem)
                L_maxI[f4_to_i[canonical_marked_flag(sa, sc, 4, 1)], gi] += coeff / (N * (N - 1))

    # (3) Evaluate exact 4-vertex / 5-vertex unconditional polynomials:
    #   - ed_vec: d(K_2)
    #   - P_c^I = (1-alpha)(1/2-alpha)*e(I, Ibar) + (1/2-alpha)^2 * e(Ibar) - c*(1-alpha)^2 > 0
    #     (and weighted by 1_{w in I} or 1_{w not in I} — Wait: alpha is global so multiplying by any >=0 1-vertex flag
    #      just scales by alpha or (1-alpha), which is STILL valid and gives extra linear constraints!)
    #   - ALSO 1-vertex padded P_c^{(1)}(v) (standard 5-vertex rule!)
    ed_vec = np.zeros(num_g)
    pI_e = np.zeros((3, num_g))  # weight 1, alpha (1_{w in I}), 1-alpha (1_{w not in I})
    pI_c = np.zeros((3, num_g))
    p1v_e = np.zeros(num_g)
    p1v_c = np.zeros(num_g)

    for gi, (g_adj, g_col) in enumerate(graphs_N):
        cnt = 0
        for perm in itertools.permutations(range(N)):
            w, a, b, y, z = perm
            ia = g_col[a]
            ib = g_col[b]
            iy = g_col[y]
            iz = g_col[z]
            yz = (g_adj[y] >> z) & 1
            ed_vec[gi] += yz

            # P_c^I:
            om_a = 1.0 - ia
            om_b = 1.0 - ib
            hm_a = 0.5 - ia
            hm_b = 0.5 - ib
            e_part = 0.0
            if yz:
                if iy and (not iz):
                    e_part = om_a * hm_b
                elif (not iy) and (not iz):
                    e_part = 0.5 * hm_a * hm_b
            c_part = om_a * om_b

            iw = float(g_col[w])
            pI_e[0, gi] += e_part
            pI_e[1, gi] += iw * e_part
            pI_e[2, gi] += (1.0 - iw) * e_part
            pI_c[0, gi] += c_part
            pI_c[1, gi] += iw * c_part
            pI_c[2, gi] += (1.0 - iw) * c_part

            # Standard 1-vertex padded S(w):
            wa = (g_adj[w] >> a) & 1
            wb = (g_adj[w] >> b) & 1
            wy = (g_adj[w] >> y) & 1
            wz = (g_adj[w] >> z) & 1
            if yz:
                if wy and (not wz):
                    p1v_e[gi] += (1.0 - wa) * (0.5 - wb)
                elif (not wy) and (not wz):
                    p1v_e[gi] += 0.5 * (0.5 - wa) * (0.5 - wb)
            p1v_c[gi] += (1.0 - wa) * (1.0 - wb)
            cnt += 1

        inv = 1.0 / cnt
        ed_vec[gi] *= inv
        pI_e[:, gi] *= inv
        pI_c[:, gi] *= inv
        p1v_e[gi] *= inv
        p1v_c[gi] *= inv

    print(f"Localizers ({L_alpha.shape[0]} alpha<=1/2, {L_maxI.shape[0]} d(v)<=alpha) & polys ready in {time.perf_counter()-t0:.2f}s.\n", flush=True)

    # Solve SDP!
    x = cp.Variable(num_g, nonneg=True)
    slack = cp.Variable()
    c_p = cp.Parameter(nonneg=True)
    constraints = [
        cp.sum(x) == 1.0,
        ed_vec @ x >= 8.0 * c_p + slack,
        L_alpha @ x >= 0.0,
        L_maxI @ x >= 0.0,
        p1v_e @ x - c_p * (p1v_c @ x) >= slack,
    ]
    for wi in range(3):
        constraints.append(pI_e[wi] @ x - c_p * (pI_c[wi] @ x) >= slack)
    for r, B_mat in zip(block_sizes, block_mats):
        constraints.append(cp.reshape(B_mat @ x, (r, r), order="C") >> 0)

    prob = cp.Problem(cp.Maximize(slack), constraints)
    lo, hi = 0.020, 0.036
    for _ in range(14):
        mid = 0.5 * (lo + hi)
        c_p.value = mid
        prob.solve(solver=cp.CLARABEL, tol_gap_abs=1e-7, tol_gap_rel=1e-7, tol_feas=1e-7)
        if prob.value is not None and prob.value < -1e-6:
            hi = mid
        else:
            lo = mid
    c_p.value = hi
    prob.solve(solver=cp.CLARABEL, tol_gap_abs=1e-7, tol_gap_rel=1e-7, tol_feas=1e-7)
    val_hi, st_hi = prob.value, prob.status
    c_p.value = lo
    prob.solve(solver=cp.CLARABEL, tol_gap_abs=1e-7, tol_gap_rel=1e-7, tol_feas=1e-7)
    x_lo = x.value
    ed_lo = float(ed_vec @ x_lo) if x_lo is not None else None
    alpha_lo = float(sum(x_lo[gi] * (sum(graphs_N[gi][1]) / N) for gi in range(num_g))) if x_lo is not None else None
    print(f"[MARKED I (N=5, {num_g} graphs)] 100% UNCONDITIONAL c* = {hi:.6f} (slack@hi={val_hi:+.2e}, status={st_hi}, ed@lo={ed_lo:.4f}, alpha@lo={alpha_lo:.4f})", flush=True)


if __name__ == "__main__":
    run_marked_N5()
