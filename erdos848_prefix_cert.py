r"""
Erdős #848 — Stepwise Endpoint Clique-Cover (Graph Coloring) Certifier!

EXACT REDUCTION THEOREM:
  Notice that |A_7(N)| is CONSTANT equal to K for all N in [8 + 25*(K-1), 7 + 25*K]
  (and equal to 0 for N in [0, 7]).
  Since V_N is monotone increasing in N, proving `Erdos848For(N)` for ALL 0 <= N <= 7 + 25*K_max
  reduces to checking ONLY the K_max + 1 right-endpoints N_K = 7 + 25*K (K = 0 .. K_max)!
  And at each endpoint N_K, if G_{N_K} admits a proper K-coloring, then every clique in G_{N_K}
  (hence every valid set A \subseteq {0..N-1} for any N in that interval!) has size <= K = |A_7(N)|!

Let's check via HiGHS MILP whether chi(G_{N_K}) == K holds for ALL K = 1 .. 100 (covering ALL N <= 2507)!
"""

import json
import time
from pathlib import Path
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import csc_matrix


def verify_all_endpoints(K_max=40):
    t0 = time.perf_counter()
    M = 7 + 25 * K_max
    limit = M * M + 2
    sqfree = bytearray([1]) * (limit + 1)
    for p in range(2, int(limit ** 0.5) + 1):
        p2 = p * p
        sqfree[p2::p2] = bytearray(len(range(p2, limit + 1, p2)))

    all_valid = [a for a in range(M) if not sqfree[a * a + 1]]
    assert [a for a in all_valid if a < 7] == [], "K=0 endpoint N_0=7 trivially holds (V_7 is empty)!"
    print(f"K=0 (N <= 7): V_7 = empty => |A| = 0 <= |A_7(N)| = 0 [TRIVIALLY VERIFIED!]", flush=True)

    certs = {}
    failed_K = []

    for K in range(1, K_max + 1):
        N_K = 7 + 25 * K
        valid = [a for a in all_valid if a < N_K]
        V = len(valid)
        edges = []
        for i in range(V):
            ai = valid[i]
            for j in range(i):
                if not sqfree[ai * valid[j] + 1]:
                    edges.append((j, i))

        # Note: {7 + 25*r : r = 0..K-1} is a K-clique in valid, so WLOG fix their colors to 0..K-1!
        forced = {i: (a - 7) // 25 for i, a in enumerate(valid) if a % 25 == 7}
        assert len(forced) == K

        var_map = {}
        vid = 0
        for i in range(V):
            if i in forced:
                var_map[(i, forced[i])] = vid
                vid += 1
            else:
                for c in range(K):
                    var_map[(i, c)] = vid
                    vid += 1

        rows, cols, vals = [], [], []
        lb, ub = [], []
        r_idx = 0
        for i in range(V):
            if i in forced:
                rows.append(r_idx); cols.append(var_map[(i, forced[i])]); vals.append(1.0)
                lb.append(1.0); ub.append(1.0); r_idx += 1
            else:
                for c in range(K):
                    rows.append(r_idx); cols.append(var_map[(i, c)]); vals.append(1.0)
                lb.append(1.0); ub.append(1.0); r_idx += 1

        for u, v in edges:
            for c in range(K):
                ku, kv = (u, c), (v, c)
                if ku in var_map and kv in var_map:
                    rows.append(r_idx); cols.append(var_map[ku]); vals.append(1.0)
                    rows.append(r_idx); cols.append(var_map[kv]); vals.append(1.0)
                    lb.append(0.0); ub.append(1.0); r_idx += 1

        A = csc_matrix((vals, (rows, cols)), shape=(r_idx, vid))
        res = milp(
            c=np.zeros(vid),
            integrality=np.ones(vid, dtype=np.int8),
            bounds=Bounds(0.0, 1.0),
            constraints=LinearConstraint(A, np.array(lb), np.array(ub)),
            options={"time_limit": 5.0, "disp": False},
        )
        if res.status == 0 and res.x is not None:
            col = {}
            for (i, c), v_idx in var_map.items():
                if res.x[v_idx] > 0.5:
                    col[valid[i]] = c
            # Strict independent verification: every same-color pair has a*b+1 SQUAREFREE!
            by_c = {}
            for a, c in col.items():
                by_c.setdefault(c, []).append(a)
            for c, els in by_c.items():
                for xi in range(len(els)):
                    for yi in range(xi):
                        assert sqfree[els[xi] * els[yi] + 1] == 1
            certs[K] = {"N_K": N_K, "V": V, "coloring": [col[a] for a in valid]}
        else:
            failed_K.append((K, N_K, res.status))
            print(f"  [!] K={K} (N_K={N_K}) failed K-coloring (status={res.status}) — chi > omega gap!", flush=True)

    print(
        f"\nChecked K = 1..{K_max} (covering ALL 0 <= N <= {M}) in {time.perf_counter()-t0:.2f}s | "
        f"Exact K-colorings found: {len(certs)}/{K_max} | Failed: {len(failed_K)}",
        flush=True,
    )
    if not failed_K:
        out_path = Path(r"C:\Users\Kerem\.gemini\antigravity\scratch\erdos-hunter\erdos848_endpoint_certs.json")
        out_path.write_text(json.dumps({"M_covered": M, "K_max": K_max, "valid_list": all_valid, "certs": certs}, indent=2), encoding="utf-8")
        print(f"[100% CERTIFIED] Saved dual K-coloring certificates for ALL N <= {M} to {out_path}!", flush=True)


if __name__ == "__main__":
    verify_all_endpoints(40)  # Covers ALL 0 <= N <= 1007!
