r"""
Erdős #552 ($100 Prize — Ramsey Number R(C_4, S_n))
Exact MILP Witness Hunter over Erdős-Rényi Polarity Graphs ER(q) for q in {7, 8, 9, 11}!

Mathematical Equivalence:
  R(C_4, S_n) >= N + 1  <==>  There exists a C_4-free graph G on N vertices with min-degree delta(G) >= N - n.
  R(C_4, S_n) <= U      <==>  No C_4-free graph on U vertices has delta(G) >= U - n.

Exact Counting + Parity Upper Bound (Parsons / BEFRS89):
  If G is C_4-free on N vertices with delta(G) >= d := N - n:
    sum_v C(deg(v), 2) <= C(N, 2).
  Moreover, if N*d is odd, at least one vertex has deg(v) >= d + 1, adding at least d to sum_v C(deg(v), 2).
  So a necessary condition for existence is:
    N * d * (d - 1) + (2 * d if (N * d) % 2 == 1 else 0) <= N * (N - 1).
  (Also refined by Parsons' exact formula for n = q^2 + 1, etc.)

MILP Formulation inside ER(q) (which is guaranteed C_4-free, so EVERY induced subgraph is C_4-free!):
  Binary variables x_v in {0, 1} for v in V(ER(q)) (M = q^2 + q + 1 vertices):
    sum_v x_v = N
    For each v: sum_{u in N(v)} x_u >= d * x_v   <=>   sum_{u in N(v)} x_u - d * x_v >= 0.
  Solved to global optimality / feasibility via SciPy HiGHS MILP solver!
  Every discovered witness is INDEPENDENTLY verified:
    (1) Exact vertex count |S| == N,
    (2) Exact C_4-freeness (all pairs u < v have |N_S(u) & N_S(v)| <= 1),
    (3) Exact min-degree delta(G[S]) >= N - n.
"""

import json
import math
import time
from pathlib import Path
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import csc_matrix


# --- Exact Finite Field GF(q) Arithmetic for prime powers q in {5, 7, 8, 9, 11} ---
class FiniteField:
    def __init__(self, q):
        self.q = q
        if q in (2, 3, 5, 7, 11, 13):
            self.p = q
            self.k = 1
            self.elements = list(range(q))
            self.add_tbl = [[(a + b) % q for b in range(q)] for a in range(q)]
            self.mul_tbl = [[(a * b) % q for b in range(q)] for a in range(q)]
        elif q == 8:
            # GF(2)[x] / (x^3 + x + 1), poly = 0b1011
            self.p, self.k = 2, 3
            self.elements = list(range(8))
            self.add_tbl = [[a ^ b for b in range(8)] for a in range(8)]
            self.mul_tbl = [[0] * 8 for _ in range(8)]
            for a in range(8):
                for b in range(8):
                    res = 0
                    aa, bb = a, b
                    while bb:
                        if bb & 1:
                            res ^= aa
                        aa <<= 1
                        if aa & 8:
                            aa ^= 0b1011
                        bb >>= 1
                    self.mul_tbl[a][b] = res
        elif q == 9:
            # GF(3)[x] / (x^2 + 1), elements encoded as a0 + 3*a1 (a0, a1 in {0,1,2})
            self.p, self.k = 3, 2
            self.elements = list(range(9))
            self.add_tbl = [[0] * 9 for _ in range(9)]
            self.mul_tbl = [[0] * 9 for _ in range(9)]
            for a in range(9):
                a0, a1 = a % 3, a // 3
                for b in range(9):
                    b0, b1 = b % 3, b // 3
                    c0 = (a0 + b0) % 3
                    c1 = (a1 + b1) % 3
                    self.add_tbl[a][b] = c0 + 3 * c1
                    # (a0 + a1*x)(b0 + b1*x) = (a0*b0 - a1*b1) + (a0*b1 + a1*b0)*x mod (x^2 + 1)
                    m0 = (a0 * b0 - a1 * b1) % 3
                    m1 = (a0 * b1 + a1 * b0) % 3
                    self.mul_tbl[a][b] = m0 + 3 * m1
        else:
            raise ValueError(f"Unsupported q={q}")

        # Verify field axioms (nonzero elements form multiplicative group)
        for a in range(1, q):
            invs = [b for b in range(1, q) if self.mul_tbl[a][b] == 1]
            assert len(invs) == 1, f"Field inverse check failed for GF({q}), a={a}"

    def add(self, a, b):
        return self.add_tbl[a][b]

    def mul(self, a, b):
        return self.mul_tbl[a][b]


def build_ER(q):
    """Build Erdős-Rényi polarity graph ER(q) on q^2 + q + 1 vertices (points of PG(2, q))."""
    F = FiniteField(q)
    pts = []
    # Normalized projective points: (1, y, z), (0, 1, z), (0, 0, 1)
    for y in F.elements:
        for z in F.elements:
            pts.append((1, y, z))
    for z in F.elements:
        pts.append((0, 1, z))
    pts.append((0, 0, 1))
    M = len(pts)
    assert M == q * q + q + 1

    adj = [set() for _ in range(M)]
    for i in range(M):
        x0, x1, x2 = pts[i]
        for j in range(i + 1, M):
            y0, y1, y2 = pts[j]
            dot = F.add(F.add(F.mul(x0, y0), F.mul(x1, y1)), F.mul(x2, y2))
            if dot == 0:
                adj[i].add(j)
                adj[j].add(i)

    # Independent verification that ER(q) is strictly C_4-free!
    for i in range(M):
        for j in range(i + 1, M):
            assert len(adj[i] & adj[j]) <= 1, f"ER({q}) NOT C_4-free!"
    return adj


def counting_upper_bound(n):
    """
    Return smallest U such that NO C_4-free graph on U vertices can have min-degree >= U - n
    by exact double-counting + handshaking parity (so R(C_4, S_n) <= U).
    """
    # Check N starting from n + 1 upwards
    N = n + 1
    while True:
        d = N - n
        lhs = N * d * (d - 1) + (2 * d if (N * d) % 2 == 1 else 0)
        rhs = N * (N - 1)
        if lhs > rhs:
            return N
        N += 1


def find_witness_in_ER(adj, N_target, d_target, time_limit=8.0):
    """
    Find an induced subgraph S of size N_target inside ER(q) with min-degree >= d_target via HiGHS MILP.
    Returns sorted list of vertex indices S if found, else None.
    """
    M = len(adj)
    if N_target > M:
        return None

    # Variables: x_0 .. x_{M-1} in {0, 1}
    # Objective: maximize sum_v deg_ER(v) * x_v (tiny tie-breaker toward high-degree vertices)
    c = np.array([-len(adj[v]) for v in range(M)], dtype=np.float64)

    # Constraint 0: sum_v x_v == N_target
    # Constraints 1..M: sum_{u in N(v)} x_u - d_target * x_v >= 0
    rows, cols, vals = [], [], []
    for v in range(M):
        rows.append(0)
        cols.append(v)
        vals.append(1.0)
    for v in range(M):
        rows.append(v + 1)
        cols.append(v)
        vals.append(-float(d_target))
        for u in adj[v]:
            rows.append(v + 1)
            cols.append(u)
            vals.append(1.0)

    A = csc_matrix((vals, (rows, cols)), shape=(M + 1, M))
    lb = np.zeros(M + 1, dtype=np.float64)
    ub = np.full(M + 1, np.inf, dtype=np.float64)
    lb[0] = float(N_target)
    ub[0] = float(N_target)

    res = milp(
        c=c,
        integrality=np.ones(M, dtype=np.int8),
        bounds=Bounds(0.0, 1.0),
        constraints=LinearConstraint(A, lb, ub),
        options={"time_limit": time_limit, "disp": False},
    )
    if res.success and res.x is not None:
        S = [v for v in range(M) if res.x[v] > 0.5]
        # Independent strict verification!
        if len(S) != N_target:
            return None
        S_set = set(S)
        degs = [len(adj[v] & S_set) for v in S]
        if min(degs) < d_target:
            return None
        # Double-check C_4-freeness on induced subgraph
        for i in range(len(S)):
            ni = adj[S[i]] & S_set
            for j in range(i + 1, len(S)):
                if len(ni & (adj[S[j]] & S_set)) > 1:
                    return None
        return S
    return None


def main():
    t0 = time.perf_counter()
    print("=== ERDŐS #552 ($100) — EXACT MILP RAMSEY R(C_4, S_n) HUNTER ===", flush=True)
    ER = {}
    for q in [7, 8, 9]:
        ER[q] = build_ER(q)
        print(f"  Built & verified C_4-free ER({q}): {len(ER[q])} vertices", flush=True)
    print(f"ER graphs ready in {time.perf_counter()-t0:.2f}s.\n", flush=True)

    # Scan n = 38 .. 72 (OEIS A006672 currently ends at n=38!)
    exact_hits = []
    bounds_table = []

    for n in range(38, 73):
        U = counting_upper_bound(n)  # Proven R(C_4, S_n) <= U
        # Pick smallest ER(q) with M >= U - 1 (and also try next q if needed)
        best_N = None
        best_q = None
        best_S = None
        for N_try in [U - 1, U - 2]:
            d_try = N_try - n
            found = False
            for q in [7, 8, 9]:
                if len(ER[q]) < N_try:
                    continue
                # Quick degree feasibility check: ER(q) max degree is q+1
                if q + 1 < d_try:
                    continue
                S = find_witness_in_ER(ER[q], N_try, d_try, time_limit=5.0)
                if S is not None:
                    best_N = N_try
                    best_q = q
                    best_S = S
                    found = True
                    break
            if found:
                break

        lb_R = (best_N + 1) if best_N is not None else None
        is_exact = (lb_R == U)
        gap_sqrt = (U - (n + math.sqrt(n)))
        status = f"EXACT = {U}" if is_exact else f"in [{lb_R}, {U}]"
        tag = "  <-- NEW EXACT BEYOND OEIS!" if (is_exact and n >= 39) else ""
        print(f"  n={n:2d} | U_cnt={U:2d} | witness_N={str(best_N):>4s} (ER({best_q})) | R(C4,S_n) {status:14s} | U-(n+sqrt(n))={gap_sqrt:+.3f}{tag}", flush=True)

        rec = {
            "n": n,
            "counting_upper_bound": U,
            "lower_bound": lb_R,
            "exact": is_exact,
            "witness_ER_q": best_q,
            "witness_N": best_N,
            "witness_vertices": best_S if is_exact else None,
        }
        bounds_table.append(rec)
        if is_exact and n >= 39:
            exact_hits.append((n, U, best_q))

    print(f"\n=== SUMMARY ({time.perf_counter()-t0:.2f}s) ===", flush=True)
    print(f"Total NEW EXACT R(C_4, S_n) values proved beyond OEIS A006672 (n >= 39): {len(exact_hits)}", flush=True)
    for n, val, q in exact_hits:
        print(f"  R(C_4, S_{n:2d}) = {val}  (witness in ER({q}), verified C_4-free + exact counting upper bound)", flush=True)

    out_path = Path(r"C:\Users\Kerem\.gemini\antigravity\scratch\erdos-hunter\erdos552_exact_values.json")
    out_path.write_text(json.dumps(bounds_table, indent=2), encoding="utf-8")
    print(f"\nSaved full table + verified witnesses to {out_path}", flush=True)


if __name__ == "__main__":
    main()
