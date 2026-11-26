import math, random
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from analyze_552_polarity import build_ER

# 1. Exact MILP on ER(9) for N'=83..78 and N'=73..69
def solve_er_milp(q, Np_list, timeout_s=8):
    pts, adj, is_abs = build_ER(q)
    N = len(pts)
    print(f"=== Exact MILP on ER({q}) (N={N}) ===")
    c = np.zeros(N + 1)
    c[N] = -1.0
    integrality = np.ones(N + 1)
    lb = np.zeros(N + 1)
    ub = np.ones(N + 1)
    ub[N] = q + 1
    bounds = Bounds(lb, ub)
    A_rows = []
    b_lb = []
    b_ub = []
    for v in range(N):
        row = np.zeros(N + 1)
        for u in adj[v]:
            row[u] = 1.0
        row[v] = -(q + 1)
        row[N] = -1.0
        A_rows.append(row)
        b_lb.append(-(q + 1))
        b_ub.append(np.inf)
    sum_row = np.zeros(N + 1); sum_row[:N] = 1.0
    A_rows.append(sum_row)
    A_mat = np.array(A_rows)
    for Np in Np_list:
        con = LinearConstraint(A_mat, np.array(b_lb + [float(Np)]), np.array(b_ub + [float(Np)]))
        res = milp(c=c, integrality=integrality, bounds=bounds, constraints=con, options={"time_limit": timeout_s})
        if res.success:
            d_opt = int(round(-res.fun))
            nw = Np - d_opt
            print(f"  ER({q}) N'={Np:3d} (del {N-Np:2d}): EXACT max delta = {d_opt:2d} -> R(C4,S_{nw})>={Np+1} (target={nw+math.ceil(math.sqrt(nw))})")
        else:
            d_best = None if res.x is None else int(round(-res.fun))
            print(f"  ER({q}) N'={Np:3d} (del {N-Np:2d}): timeout/status={res.status}, best_delta>={d_best}")

solve_er_milp(9, [83, 82, 81, 80, 79, 78], timeout_s=6)

# 2. Fast EML + heuristic deletion on ER(11) (N=133) for s = 0..45 (N' = 133..88)
pts, adj, is_abs = build_ER(11)
N = len(pts)
q = 11
adj_list = [list(adj[i]) for i in range(N)]
rng = random.Random(123)
print(f"\n=== ER(11) (N={N}) EML vs heuristic deletions ===")
for s in range(0, 44, 2):
    Np = N - s
    # EML upper bound on dbar(S)
    min_abs_in_S = max(0, Np - (N - (q + 1)))
    ub_eml = ((q + 1) * Np * Np / N + math.sqrt(q) * Np * (1 - Np / N) - min_abs_in_S) / Np
    # Fast greedy/local search from random + abs-first
    best_d = 0
    for restart in range(6):
        if restart == 0:
            abs_i = [i for i in range(N) if is_abs[i]]
            non_i = [i for i in range(N) if not is_abs[i]]
            rng.shuffle(abs_i); rng.shuffle(non_i)
            surv = set((non_i + abs_i)[:Np])
        else:
            surv = set(rng.sample(range(N), Np))
        in_S = [i in surv for i in range(N)]
        degs = [sum(1 for u in adj_list[v] if in_S[u]) for v in range(N)]
        surv_l = [i for i in range(N) if in_S[i]]
        del_l = [i for i in range(N) if not in_S[i]]
        cur_min = min(degs[v] for v in surv_l)
        if cur_min > best_d: best_d = cur_min
        for step in range(300):
            if s == 0: break
            # pick a min deg in S, swap with best in del_l
            min_vs = [v for v in surv_l if degs[v] == cur_min]
            u = rng.choice(min_vs)
            # tentatively remove u
            in_S[u] = False
            for nbr in adj_list[u]: degs[nbr] -= 1
            # find w in del_l with highest deg into S\{u}
            cand = del_l if len(del_l) <= 20 else rng.sample(del_l, 20)
            best_w = max(cand, key=lambda w: degs[w])
            # add best_w
            in_S[best_w] = True
            for nbr in adj_list[best_w]: degs[nbr] += 1
            new_min = min(degs[v] for v in surv_l if v != u)
            new_min = min(new_min, degs[best_w])
            if new_min >= cur_min or rng.random() < 0.05:
                # accept
                surv_l[surv_l.index(u)] = best_w
                del_l[del_l.index(best_w)] = u
                cur_min = new_min
                if cur_min > best_d: best_d = cur_min
            else:
                # revert
                in_S[best_w] = False
                for nbr in adj_list[best_w]: degs[nbr] -= 1
                in_S[u] = True
                for nbr in adj_list[u]: degs[nbr] += 1
    nw = Np - best_d
    targ = nw + math.ceil(math.sqrt(nw))
    # Also compute upper bound on n_witness if d <= floor(ub_eml):
    d_eml_floor = math.floor(ub_eml)
    print(f"  s={s:2d}, N'={Np:3d}: ub_EML={ub_eml:5.2f} (floor={d_eml_floor:2d}), heur_d={best_d:2d} -> n={nw:3d}: R>={Np+1:3d} vs n+ceil(sqrt(n))={targ:3d} (diff={Np+1-targ:+d}), EML_max_diff={d_eml_floor - math.ceil(math.sqrt(Np - d_eml_floor)):+d}")
