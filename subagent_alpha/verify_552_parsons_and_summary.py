import math, random
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from analyze_552_polarity import build_ER, verify_c4_free

# 1. Extract and verify explicit 45-vertex induced subgraph of ER(7) with delta=6 (witnessing R(C4, S_39) >= 46)!
pts7, adj7, is_abs7 = build_ER(7)
N7 = len(pts7)
c = np.zeros(N7 + 1); c[N7] = -1.0
integrality = np.ones(N7 + 1)
bounds = Bounds(np.zeros(N7 + 1), np.array([1.0]*N7 + [8.0]))
A_rows = []; b_lb = []; b_ub = []
for v in range(N7):
    row = np.zeros(N7 + 1)
    for u in adj7[v]: row[u] = 1.0
    row[v] = -8.0; row[N7] = -1.0
    A_rows.append(row); b_lb.append(-8.0); b_ub.append(np.inf)
sum_row = np.zeros(N7 + 1); sum_row[:N7] = 1.0
A_rows.append(sum_row)
con = LinearConstraint(np.array(A_rows), np.array(b_lb + [45.0]), np.array(b_ub + [45.0]))
res = milp(c=c, integrality=integrality, bounds=bounds, constraints=con)
assert res.success
keep = [i for i in range(N7) if res.x[i] > 0.5]
deleted = [i for i in range(N7) if res.x[i] <= 0.5]
assert len(keep) == 45
# Verify induced subgraph independently!
sub_adj = {u: [v for v in adj7[u] if v in keep] for u in keep}
min_deg = min(len(sub_adj[u]) for u in keep)
max_deg = max(len(sub_adj[u]) for u in keep)
# Verify C4-free directly
c4_found = False
for u in keep:
    seen = set()
    for w in sub_adj[u]:
        for v in sub_adj[w]:
            if v > u:
                if v in seen: c4_found = True
                seen.add(v)
print(f"Verified ER(7) witness for R(C4, S_39) >= 46: N'={len(keep)}, C4_found={c4_found}, delta={min_deg}, Delta={max_deg}")
print(f"  Deleted 12 vertices (#abs deleted = {sum(1 for i in deleted if is_abs7[i])}/8): {[pts7[i] for i in deleted]}")

# 2. Check if adding edges to an 82-vertex deletion of ER(9) can reach delta = 9 (N'=82, n=73 -> R>=83)!
pts9, adj9, is_abs9 = build_ER(9)
N9 = len(pts9)
# Get optimal 82-vertex subgraph of ER(9) (we know it has delta=8)
c9 = np.zeros(N9 + 1); c9[N9] = -1.0
integ9 = np.ones(N9 + 1)
b9 = Bounds(np.zeros(N9 + 1), np.array([1.0]*N9 + [10.0]))
A9 = []; lb9 = []; ub9 = []
for v in range(N9):
    row = np.zeros(N9 + 1)
    for u in adj9[v]: row[u] = 1.0
    row[v] = -10.0; row[N9] = -1.0
    A9.append(row); lb9.append(-10.0); ub9.append(np.inf)
sr9 = np.zeros(N9 + 1); sr9[:N9] = 1.0
A9.append(sr9)
res9 = milp(c=c9, integrality=integ9, bounds=b9, constraints=LinearConstraint(np.array(A9), np.array(lb9 + [82.0]), np.array(ub9 + [82.0])), options={"time_limit": 8})
keep9 = [i for i in range(N9) if res9.x[i] > 0.5]
sub9 = {u: set(v for v in adj9[u] if v in keep9) for u in keep9}
degs9 = [len(sub9[u]) for u in keep9]
from collections import Counter
print(f"ER(9) N'=82 induced subgraph deg dist: {dict(sorted(Counter(degs9).items()))}")
# Check which pairs of deg-8 vertices can have an edge added without forming C4!
low8 = [u for u in keep9 if len(sub9[u]) == 8]
addable = []
for i in range(len(low8)):
    u = low8[i]
    for j in range(i + 1, len(low8)):
        v = low8[j]
        if v in sub9[u]: continue
        # Adding edge (u, v) creates C4 iff:
        # 1) u and v already have a common neighbor? Wait: u-v-w-u is C3 (ok), u-x-v-y-u is C4! So u,v have >= 1 common neighbor -> NO! Actually a C4 containing (u,v) has paths of length 3 between u and v!
        # Check directly: does there exist x in N(u), y in N(v) with x != y and x ~ y (not using u,v)?
        ok = True
        for x in sub9[u]:
            for y in sub9[v]:
                if x != y and y in sub9[x]:
                    ok = False; break
            if not ok: break
        if ok:
            addable.append((u, v))
print(f"Number of low-deg (deg=8) vertices: {len(low8)}, addable edges among them without C4: {len(addable)}")

# 3. Check ER(11) MILP at N'=100 (s=33) and N'=92 (s=41) with 6s timeout
pts11, adj11, is_abs11 = build_ER(11)
N11 = len(pts11)
c11 = np.zeros(N11 + 1); c11[N11] = -1.0
integ11 = np.ones(N11 + 1)
b11 = Bounds(np.zeros(N11 + 1), np.array([1.0]*N11 + [12.0]))
A11 = []; lb11 = []; ub11 = []
for v in range(N11):
    row = np.zeros(N11 + 1)
    for u in adj11[v]: row[u] = 1.0
    row[v] = -12.0; row[N11] = -1.0
    A11.append(row); lb11.append(-12.0); ub11.append(np.inf)
sr11 = np.zeros(N11 + 1); sr11[:N11] = 1.0
A11.append(sr11)
A11_mat = np.array(A11)
for Np in [100, 92]:
    res11 = milp(c=c11, integrality=integ11, bounds=b11, constraints=LinearConstraint(A11_mat, np.array(lb11 + [float(Np)]), np.array(ub11 + [float(Np)])), options={"time_limit": 6})
    d_val = None if res11.x is None else int(round(-res11.fun))
    print(f"ER(11) N'={Np}: status={res11.status}, best_delta={d_val}")
