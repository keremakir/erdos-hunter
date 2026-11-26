import urllib.request, json, math
from collections import Counter
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from analyze_552_polarity import build_ER

# 1. Inspect HoG 53036..56945 structure (especially 56941 on 35 vertices where every edge is in 1 triangle!)
for gid in [53036, 56941, 56942, 56943, 56944, 56945]:
    req = urllib.request.Request(f"https://houseofgraphs.org/api/graphs/{gid}", headers={"User-Agent": "Mozilla/5.0"})
    d = json.loads(urllib.request.urlopen(req, timeout=10).read().decode())
    adj = d["adjacencyList"]
    N = len(adj)
    # Check connected components of vertex neighborhoods!
    nbr_types = Counter()
    for u in range(N):
        nbrs = set(adj[u])
        # edges inside N(u)
        sub_degs = tuple(sorted(len(set(adj[v]) & nbrs) for v in nbrs))
        nbr_types[sub_degs] += 1
    # Count triangles
    tris = set()
    for u in range(N):
        nu = set(adj[u])
        for v in adj[u]:
            if v > u:
                for w in (nu & set(adj[v])):
                    if w > v:
                        tris.add((u, v, w))
    # Check non-triangle edges!
    tri_edges = set()
    for a, b, c in tris:
        tri_edges.update([(a,b),(b,a),(a,c),(c,a),(b,c),(c,b)])
    non_tri_edges = [(u, v) for u in range(N) for v in adj[u] if u < v and (u, v) not in tri_edges]
    print(f"HoG {gid} (N={N}): #tris={len(tris)}, #non_tri_edges={len(non_tri_edges)}, nbr_sub_degs={dict(nbr_types)}")
    if gid == 56941:
        # Check vertex degrees in triangle hypergraph and check if it's a quotient/Cayley/graph!
        # Wait: 35 vertices, 35 triangles, each vertex in 3 triangles, each pair of triangles shares at most 1 vertex (since C4-free? Wait: two triangles sharing an edge would be C4! Can two triangles share 1 vertex? Yes, each vertex is in 3 triangles!)
        # Actually, 35 vertices, 35 blocks of size 3, each vertex in 3 blocks -> a (35_3) configuration?!
        # Wait: in a (35_3) configuration, each point is in 3 blocks of size 3, so 3*2 = 6 neighbors!
        # No two blocks share 2 points (else C4), so it's a linear space / partial triple system where every point has degree 3 and blocks are triples!
        # Wait: ANY 3-regular linear hypergraph (partial STS) of triples on N vertices has NO C4 in its collinearity graph?
        # WAIT A SECOND!! CHECK THAT!!
        # In a partial Steiner Triple System (every pair of points in <= 1 triple):
        # Could the collinearity graph have a C4 (a-b-c-d-a)?
        # Yes if (a,b), (b,c), (c,d), (d,a) are in 4 DIFFERENT triples (a 4-cycle of lines / Pasch-free? No, 4-gon in linear space!).
        # So HoG 56941 is a girth-5 (no 4-gon!) 3-regular partial STS on 35 points! (Generalized polygon? Wait: generalized quadrangle GQ(2,2) has 15 points; GQ(3,3) has 40 points; deleting 5 points or lines from GQ(3,3)?!)
        # WAIT A SECOND! GQ(2,2) has 15 points, 15 lines of size 3, 3 lines per point (degree 6? Wait: 3*(3-1)=6?! No, 3*(2)=6 neighbors? Wait: in GQ(s,t), line size s+1, lines per point t+1, vertices (s+1)(st+1), degree s(t+1)!
        # For s=2, t=2: line size 3, 3 lines/pt -> degree 2*3 = 6! Vertices = 3*5 = 15!
        # What about a 3-cover or something on 35 vertices? Look at eigenvalues of HoG 56941: [6.0, 3.0, 2.646=sqrt(7), 2.449=sqrt(6), 1.732=sqrt(3)]!
        pass

# 2. Exact MILP for ER(7) and ER(8) vertex deletions!
def solve_er_deletion_milp(q, Np_list, timeout_s=10):
    pts, adj, is_abs = build_ER(q)
    N = len(pts)
    print(f"\n=== Exact MILP on ER({q}) (N={N}) ===")
    # Variables: x_0..x_{N-1} binary, d integer in [0, q+1]
    # Maximize d (minimize -d)
    c = np.zeros(N + 1)
    c[N] = -1.0
    integrality = np.ones(N + 1)
    lb = np.zeros(N + 1)
    ub = np.ones(N + 1)
    ub[N] = q + 1
    bounds = Bounds(lb, ub)

    # Build degree constraints: sum_{u in N(v)} x_u - d - (q+1)*x_v >= -(q+1)
    # Wait: if x_v = 1 -> sum x_u - d >= 0 -> deg_S(v) >= d!
    # If x_v = 0 -> sum x_u - d >= -(q+1) (always true since sum x_u >= 0 and d <= q+1)!
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
    # Sum x_v == Np constraint (last row)
    sum_row = np.zeros(N + 1)
    sum_row[:N] = 1.0
    A_rows.append(sum_row)
    A_mat = np.array(A_rows)

    for Np in Np_list:
        cur_lb = np.array(b_lb + [float(Np)])
        cur_ub = np.array(b_ub + [float(Np)])
        con = LinearConstraint(A_mat, cur_lb, cur_ub)
        res = milp(c=c, integrality=integrality, bounds=bounds, constraints=con,
                   options={"time_limit": timeout_s})
        if res.success:
            d_opt = int(round(-res.fun))
            n_wit = Np - d_opt
            print(f"  ER({q}) N'={Np:2d} (del {N-Np:2d}): EXACT max delta = {d_opt} -> R(C4, S_{n_wit}) >= {Np+1} (n+ceil(sqrt(n))={n_wit+math.ceil(math.sqrt(n_wit))})")
        else:
            # Check best bound / status
            print(f"  ER({q}) N'={Np:2d}: status={res.status} msg={res.message}, x={None if res.x is None else round(-res.fun)}")

solve_er_deletion_milp(7, [45, 44, 43, 42, 41, 40, 39, 38], timeout_s=8)
solve_er_deletion_milp(8, [64, 63, 62, 61, 60, 59, 53, 51, 49], timeout_s=8)
