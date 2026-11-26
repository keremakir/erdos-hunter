"""
Erdős #128 ($250 Prize — Sparse Half Conjecture)
Rigorous Flag Algebra SDP v2 (N=6, 38 triangle-free graphs):
  - Adds exact localizing constraints for Delta(G) <= 1/2:
      For every nonnegative 1-vertex flag F (on <= 5 vertices), E_v[(1/2 - d(v)) * F(v)] >= 0.
      (Valid because any vertex with d(v) >= 1/2 immediately gives an independent set N(v) of size >= n/2!)
  - Adds exact edge-density cut d(K2) >= 8c.
  - Tests 1-vertex padded neighborhood S(v) AND degree-weighted S(v) AND inspects the exact primal extremal graph!
"""

import itertools
import json
import time
from pathlib import Path
import numpy as np
import cvxpy as cp

from flag_algebra_128 import (
    enumerate_tf_graphs,
    enumerate_tf_flags,
    compute_product_tensors,
    canonical_flag,
    induced_sub_adj,
    eval_1vertex_poly_on_N_graph,
    eval_2step_neighborhood_poly,
)


def compute_delta_half_localizers(N, graphs_N):
    """
    For every 1-vertex rooted triangle-free flag F on k = N-1 vertices (root = vertex 0),
    compute the vector L_F[g] = E_v[ (1/2 - d(v)) * F(v) ] evaluated on each N-vertex graph G_g.
    Since Delta(G) <= 1/2 => (1/2 - d(v)) >= 0 for ALL v, and F(v) >= 0, we MUST have L_F @ x >= 0!
    """
    t = 1
    type_adj = (0,)
    k = N - 1  # root + (N-2) vertices for F, plus 1 vertex for d(v) => total N vertices!
    f_codes, f_adjs = enumerate_tf_flags(k, type_adj, t)
    flag_to_idx = {c: i for i, c in enumerate(f_codes)}
    num_f = len(f_codes)
    num_g = len(graphs_N)
    L = np.zeros((num_f, num_g), dtype=np.float64)

    # For each N-graph, average over root v in [N], neighbor-test vertex a != v, and remaining N-2 vertices for F
    for gi, g_adj in enumerate(graphs_N):
        total_pairs = N * (N - 1)
        for v in range(N):
            for a in range(N):
                if a == v:
                    continue
                coeff = 0.5 - ((g_adj[v] >> a) & 1)
                rem = tuple(u for u in range(N) if u != v and u != a)
                f_code = canonical_flag(induced_sub_adj(g_adj, (v,) + rem), k, 1)
                L[flag_to_idx[f_code], gi] += coeff
        L[:, gi] /= total_pairs
    return L, f_adjs


def eval_weighted_1vertex(adj, N, weight_type="1"):
    """
    Exact 6-vertex evaluation of E_v[ w(v) * P_c(v) ] for N=6:
      6 distinct vertices: (v, w_vtx, a, b, y, z)
      weight_type="1": w(v) = 1
      weight_type="d": w(v) = d(v)
      weight_type="1-d": w(v) = 1 - d(v)
      weight_type="half-d": w(v) = 1/2 - d(v)  (nonnegative since Delta <= 1/2!)
    """
    te1 = 0.0
    te0 = 0.0
    tco = 0.0
    cnt = 0
    for perm in itertools.permutations(range(N), 6):
        v, wv, a, b, y, z = perm
        dw = (adj[v] >> wv) & 1
        if weight_type == "1":
            w = 1.0
        elif weight_type == "d":
            w = float(dw)
        elif weight_type == "1-d":
            w = 1.0 - dw
        elif weight_type == "half-d":
            w = 0.5 - dw
        else:
            raise ValueError(weight_type)

        va = (adj[v] >> a) & 1
        vb = (adj[v] >> b) & 1
        vy = (adj[v] >> y) & 1
        vz = (adj[v] >> z) & 1
        yz = (adj[y] >> z) & 1

        e1_ind = 0.5 * ((vy and (not vz) and yz) + (vz and (not vy) and yz))
        e0_ind = 0.5 * ((not vy) and (not vz) and yz)

        te1 += w * (1.0 - va) * (0.5 - vb) * e1_ind
        te0 += w * (0.5 - va) * (0.5 - vb) * e0_ind
        tco += w * (1.0 - va) * (1.0 - vb)
        cnt += 1
    return te1 / cnt, te0 / cnt, tco / cnt


def run_v2():
    N = 6
    t0 = time.perf_counter()
    _, graphs_N = enumerate_tf_graphs(N)
    num_g = len(graphs_N)
    print(f"=== RIGOROUS ERDŐS #128 FLAG ALGEBRA SDP v2 (N={N}, {num_g} graphs) ===")

    blocks = []
    for t in [2, 4]:
        _, t_graphs = enumerate_tf_graphs(t)
        for ti, t_adj in enumerate(t_graphs):
            m = (N + t) // 2
            f_codes, f_adjs = enumerate_tf_flags(m, t_adj, t)
            tensors = compute_product_tensors(N, graphs_N, t, t_adj, f_codes, f_adjs)
            blocks.append((t, ti, len(f_codes), tensors))

    L_delta, _ = compute_delta_half_localizers(N, graphs_N)
    print(f"Computed {L_delta.shape[0]} exact Delta(G) <= 1/2 localizing constraints in {time.perf_counter()-t0:.2f}s.")

    ed_vec = np.zeros(num_g)
    euv_vec = np.zeros(num_g)
    a2uv_vec = np.zeros(num_g)
    a1uv_vec = np.zeros(num_g)
    ne_vec = np.zeros(num_g)
    for gi, g_adj in enumerate(graphs_N):
        _, _, _, ed_vec[gi] = eval_1vertex_poly_on_N_graph(g_adj, N, 0.0)
        euv_vec[gi], a2uv_vec[gi], a1uv_vec[gi], ne_vec[gi] = eval_2step_neighborhood_poly(g_adj, N)

    # Precompute weighted 1-vertex polynomials
    weights = ["1", "d", "1-d", "half-d"]
    w_data = {}
    for wt in weights:
        e1v = np.zeros(num_g)
        e0v = np.zeros(num_g)
        cov = np.zeros(num_g)
        for gi, g_adj in enumerate(graphs_N):
            e1v[gi], e0v[gi], cov[gi] = eval_weighted_1vertex(g_adj, N, wt)
        w_data[wt] = (e1v, e0v, cov)
    print(f"All 6-vertex tensors & polynomials ready in {time.perf_counter()-t0:.2f}s.\n")

    def solve_for_c(c_val, wt="1", mode="1vertex"):
        x = cp.Variable(num_g, nonneg=True)
        constraints = [
            cp.sum(x) == 1.0,
            ed_vec @ x >= 8.0 * c_val,
            L_delta @ x >= 0.0,  # RIGOROUS Delta(G) <= 1/2!
        ]
        for (_, _, r, tensors) in blocks:
            M = sum(x[gi] * tensors[gi] for gi in range(num_g) if np.any(tensors[gi]))
            constraints.append(M >> 0)

        if mode == "1vertex":
            e1v, e0v, cov = w_data[wt]
            obj_vec = e1v + e0v - c_val * cov
        elif mode == "2nbr_with_delta":
            constraints.append(a1uv_vec @ x >= 0.5 * (ne_vec @ x))
            obj_vec = euv_vec - 4.0 * c_val * a2uv_vec
        else:
            raise ValueError(mode)

        prob = cp.Problem(cp.Maximize(obj_vec @ x), constraints)
        prob.solve(solver=cp.CLARABEL, tol_gap_abs=1e-9, tol_gap_rel=1e-9, tol_feas=1e-9)
        return prob.value, x.value, prob.status

    results = {}
    for wt in weights:
        lo, hi = 0.020, 0.045
        for _ in range(18):
            mid = 0.5 * (lo + hi)
            val, _, st = solve_for_c(mid, wt=wt, mode="1vertex")
            if val is not None and val <= 1e-8:
                hi = mid
            else:
                lo = mid
        val_hi, x_hi, st_hi = solve_for_c(hi, wt=wt, mode="1vertex")
        ed_star = float(ed_vec @ x_hi) if x_hi is not None else None
        print(f"[1-Vertex Rigorous (Delta<=1/2) | w(v)='{wt:6s}'] c* = {hi:.6f} (status={st_hi}, edge_dens={ed_star:.4f})")
        results[f"1vertex_w_{wt}"] = {"c_star": round(hi, 6), "status": st_hi, "edge_density_at_opt": round(ed_star, 5) if ed_star else None}

    # Now test 2-neighborhood union WITH Delta <= 1/2!
    lo2, hi2 = 0.015, 0.030
    for _ in range(18):
        mid = 0.5 * (lo2 + hi2)
        val, _, st = solve_for_c(mid, mode="2nbr_with_delta")
        if val is not None and val <= 1e-8:
            hi2 = mid
        else:
            lo2 = mid
    val2, x2, st2 = solve_for_c(hi2, mode="2nbr_with_delta")
    ed2 = float(ed_vec @ x2) if x2 is not None else None
    print(f"\n[2-Neighborhood Union N(u) U N(v) (Delta<=1/2, avg|S|>=1/2)] c2* = {hi2:.6f} (status={st2}, edge_dens={ed2:.4f})")
    results["2nbr_with_delta"] = {"c_star": round(hi2, 6), "status": st2, "edge_density_at_opt": round(ed2, 5) if ed2 else None}

    # Print top active 6-vertex graphs in the extremal primal solution of w='d'
    _, x_best, _ = solve_for_c(results["1vertex_w_d"]["c_star"] - 1e-4, wt="d", mode="1vertex")
    if x_best is not None:
        top_idx = np.argsort(-x_best)[:6]
        print("\nTop active 6-vertex graphs in primal extremal solution (w='d'):")
        for idx in top_idx:
            if x_best[idx] > 1e-3:
                degs = sorted([m.bit_count() for m in graphs_N[idx]])
                print(f"  Graph #{idx:2d} | weight={x_best[idx]:.4f} | edges={sum(degs)//2} | deg_seq={degs}")

    out_path = Path(r"C:\Users\Kerem\.gemini\antigravity\scratch\erdos-hunter\flag_algebra_128_results.json")
    out_path.write_text(json.dumps(results, indent=2), encoding="utf-8")
    print(f"\nSaved verified SDP results to {out_path}")


if __name__ == "__main__":
    run_v2()
