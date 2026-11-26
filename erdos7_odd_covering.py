r"""
Erdős #7 ($25 Prize, verifiable — Odd Covering System of Z)
Exact HiGHS MILP Maximum-Coverage & Non-Existence Certifier!

Problem (Erdős 1950):
  Does there exist a finite covering system {a_i (mod m_i)} of Z with DISTINCT ODD moduli m_i > 1?
  Known milestones:
    - Necessary density condition: sum_{i} 1/m_i >= 1.
    - Hough & Nielsen (2019): at least one modulus must be divisible by 2 or 3.
    - Balister, Bollobás, Morris, Sahasrabudhe & Tiba (2022, Annals of Math): NO square-free odd
      covering system exists! So any odd covering system MUST use prime-power moduli (e.g. 9, 25, 27, 49...).

What this engine does:
  1) CALIBRATION: Independently discovers the classic even covering system on divisors of M = 12
     ({2, 3, 4, 6, 12}) via HiGHS MILP (100% coverage = 12/12 residues).
  2) ODD MODULI EXACT MILP & LOCAL SEARCH:
     For a target odd integer M (containing prime powers like 3^2, 3^3, 5^2, 7, 11):
     Let D = {d | M : d > 1} be all proper odd divisors > 1 of M.
     Check reciprocal sum S(M) = sum_{d in D} 1/d (must be >= 1 to even have a chance!).
     Formulate EXACT MILP:
       - Binary y_{d, r} in {0, 1} for d in D, r in {0..d-1}: sum_r y_{d, r} <= 1 (pick at most 1 residue per modulus d).
       - Binary z_x in {0, 1} for x in {0..M-1}: z_x <= sum_{d in D} y_{d, x mod d}.
       - Maximize sum_x z_x (total covered residues out of M).
     If MILP proves max_covered < M => EXACT NON-EXISTENCE CERTIFICATE that NO odd covering system
     exists using divisors of M!
     If max_covered == M => WE FOUND AN ODD COVERING SYSTEM ($25 PRIZE SOLVED!!).
"""

import json
import time
from fractions import Fraction
from pathlib import Path
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import csc_matrix


def divisors_gt1(M):
    divs = []
    for d in range(2, int(M ** 0.5) + 1):
        if M % d == 0:
            divs.append(d)
            if d * d != M:
                divs.append(M // d)
    divs.append(M)
    return sorted(divs)


def solve_covering_milp(M, time_limit=15.0):
    """Exact HiGHS MILP for max number of residues mod M covered by distinct divisors d > 1 of M."""
    divs = divisors_gt1(M)
    recip_sum = sum(Fraction(1, d) for d in divs)

    # Symmetry breaking: fix the smallest divisor d0 to residue 0 (translation invariance of Z/MZ!)
    d0 = divs[0]

    # Variables: first all y_{d, r} (total Y_cnt = sum(divs)), then z_0 .. z_{M-1}
    y_offset = {}
    idx = 0
    for d in divs:
        y_offset[d] = idx
        idx += d
    Y_cnt = idx
    Z_off = Y_cnt
    total_vars = Y_cnt + M

    # Objective: maximize sum z_x  <=>  minimize -sum z_x
    c = np.zeros(total_vars, dtype=np.float64)
    c[Z_off:] = -1.0

    rows, cols, vals = [], [], []
    lb, ub = [], []
    r_idx = 0

    # 1) For each divisor d: sum_{r=0..d-1} y_{d, r} == 1
    for d in divs:
        off = y_offset[d]
        for r in range(d):
            rows.append(r_idx)
            cols.append(off + r)
            vals.append(1.0)
        lb.append(1.0)
        ub.append(1.0)
        r_idx += 1

    # 2) For each x in 0..M-1: sum_{d in divs} y_{d, x % d} - z_x >= 0
    for x in range(M):
        for d in divs:
            rows.append(r_idx)
            cols.append(y_offset[d] + (x % d))
            vals.append(1.0)
        rows.append(r_idx)
        cols.append(Z_off + x)
        vals.append(-1.0)
        lb.append(0.0)
        ub.append(np.inf)
        r_idx += 1

    # Symmetry breaking: y_{d0, 0} == 1
    var_lb = np.zeros(total_vars, dtype=np.float64)
    var_ub = np.ones(total_vars, dtype=np.float64)
    var_lb[y_offset[d0] + 0] = 1.0

    A = csc_matrix((vals, (rows, cols)), shape=(r_idx, total_vars))
    t0 = time.perf_counter()
    res = milp(
        c=c,
        integrality=np.ones(total_vars, dtype=np.int8),
        bounds=Bounds(var_lb, var_ub),
        constraints=LinearConstraint(A, np.array(lb), np.array(ub)),
        options={"time_limit": time_limit, "disp": False},
    )
    dt = time.perf_counter() - t0

    covered = int(round(-res.fun)) if res.fun is not None else None
    exact_opt = (res.status == 0)
    chosen = {}
    if res.x is not None:
        for d in divs:
            off = y_offset[d]
            for r in range(d):
                if res.x[off + r] > 0.5:
                    chosen[d] = r
                    break
        # Independent verification of actual covered count!
        cov_set = set()
        for d, r in chosen.items():
            for x in range(r, M, d):
                cov_set.add(x)
        assert len(cov_set) >= (covered or 0), "Verification mismatch!"
        covered = len(cov_set)

    return {
        "M": M,
        "num_divisors": len(divs),
        "recip_sum": round(float(recip_sum), 5),
        "covered": covered,
        "uncovered": (M - covered) if covered is not None else None,
        "coverage_pct": round(100.0 * covered / M, 3) if covered is not None else None,
        "exact_global_opt": exact_opt,
        "status": int(res.status),
        "time_s": round(dt, 3),
        "is_full_cover": (covered == M),
        "chosen_sample": {str(k): v for k, v in list(chosen.items())[:10]},
    }


def main():
    print("=== ERDŐS #7 ($25) — ODD COVERING SYSTEM EXACT MILP ENGINE ===\n", flush=True)
    # 1) Calibration on M = 12 (even): must hit 12/12 = 100%!
    cal = solve_covering_milp(12, time_limit=5.0)
    print(f"[CALIBRATION M=12] covered={cal['covered']}/12 ({cal['coverage_pct']}%) | exact={cal['exact_global_opt']} | {cal['chosen_sample']}", flush=True)
    assert cal["is_full_cover"], "Calibration on M=12 failed!"

    # 2) Odd prime-power moduli universes (all have recip_sum > 1 except 315; let's test!)
    # Note: 315 = 3^2*5*7 (recip_sum = 0.981 < 1), 945 = 3^3*5*7 (1.032), 1575 = 3^2*5^2*7 (1.063),
    #       3465 = 3^2*5*7*11 (1.161), 4725 = 3^3*5^2*7 (1.119)
    targets = [
        ("3^2*5*7", 315, 10.0),
        ("3^3*5*7", 945, 15.0),
        ("3^2*5^2*7", 1575, 20.0),
        ("3^2*5*7*11", 3465, 20.0),
    ]
    results = {"calibration_12": cal, "odd_universes": []}
    for label, M, tl in targets:
        r = solve_covering_milp(M, time_limit=tl)
        r["factorization"] = label
        verdict = "FULL COVER FOUND!!" if r["is_full_cover"] else (
            "PROVEN IMPOSSIBLE (exact global opt < M)" if r["exact_global_opt"] else "BEST FOUND (time limit)"
        )
        print(
            f"[ODD M={M:4d} ({label:10s})] divs={r['num_divisors']:2d} | sum(1/d)={r['recip_sum']:.4f} | "
            f"covered={r['covered']}/{M} ({r['coverage_pct']:6.2f}%, gap={r['uncovered']}) | {verdict} ({r['time_s']}s)",
            flush=True,
        )
        results["odd_universes"].append(r)

    out_path = Path(r"C:\Users\Kerem\.gemini\antigravity\scratch\erdos-hunter\erdos7_odd_covering_results.json")
    out_path.write_text(json.dumps(results, indent=2), encoding="utf-8")
    print(f"\nSaved results to {out_path}", flush=True)


if __name__ == "__main__":
    main()
