import time
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy import sparse


def build_golay_s3622():
    """Construct extended binary Golay code G24 and extract S(3, 6, 22)."""
    # Standard generator matrix [I_12 | P] where P is 12x12 circulant/Paley matrix mod 11 + border
    # Using Paley construction for p=11: quadratic residues mod 11 are {1, 3, 4, 5, 9}
    qr = {1, 3, 4, 5, 9}
    B = np.zeros((12, 12), dtype=int)
    B[0, 1:] = 1
    B[1:, 0] = 1
    for i in range(11):
        for j in range(11):
            if i == j or ((j - i) % 11) in qr:
                B[1 + i, 1 + j] = 1
    # Wait: check standard Golay [I | B]: rows of B have weight 11 (row 0) and 6 (rows 1..11)?
    # Let's check: in row 1..11, 1 at col 0, and 1 at 6 entries (i==j or diff in qr: 1+5=6) -> total weight 7 in B, + 1 in I = 8!
    # Check row 0: weight 11 in B + 1 in I = 12!
    # Check orthogonality mod 2: G @ G.T mod 2 == 0!
    G = np.hstack([np.eye(12, dtype=int), B])
    assert np.all((G @ G.T) % 2 == 0), "Golay generator matrix not self-orthogonal!"

    # Generate all 4096 codewords
    msgs = ((np.arange(4096)[:, None] >> np.arange(12)) & 1)
    codewords = (msgs @ G) % 2
    weights = codewords.sum(axis=1)
    octads = codewords[weights == 8]
    assert len(octads) == 759, f"Expected 759 octads, got {len(octads)}"

    # Fix coordinates 22 and 23 -> S(3, 6, 22)
    mask_22_23 = (octads[:, 22] == 1) & (octads[:, 23] == 1)
    blocks_mat = octads[mask_22_23][:, :22]
    assert len(blocks_mat) == 77, f"Expected 77 blocks, got {len(blocks_mat)}"
    assert np.all(blocks_mat.sum(axis=1) == 6)
    return blocks_mat


def build_higman_sims_family():
    blocks = build_golay_s3622()  # 77 x 22
    # 1. Higman-Sims (100 vertices): 0=*, 1..22=points, 23..99=blocks
    A_hs = np.zeros((100, 100), dtype=int)
    A_hs[0, 1:23] = 1
    A_hs[1:23, 0] = 1
    # points to blocks
    A_hs[1:23, 23:] = blocks.T
    A_hs[23:, 1:23] = blocks
    # blocks to blocks: disjoint iff blocks @ blocks.T == 0
    inter = blocks @ blocks.T
    block_adj = (inter == 0).astype(int)
    np.fill_diagonal(block_adj, 0)
    A_hs[23:, 23:] = block_adj

    # Verify SRG(100, 22, 0, 6)
    assert np.all(A_hs.sum(axis=1) == 22)
    assert np.trace(A_hs @ A_hs @ A_hs) == 0
    A2 = A_hs @ A_hs
    assert np.all(A2 + 6 * A_hs - 16 * np.eye(100, dtype=int) == 6)

    # 2. M22 (77 vertices) = block_adj -> SRG(77, 16, 0, 4)
    A_m22 = block_adj.copy()
    assert np.all(A_m22.sum(axis=1) == 16)
    assert np.trace(A_m22 @ A_m22 @ A_m22) == 0
    M2 = A_m22 @ A_m22
    assert np.all(M2 + 4 * A_m22 - 12 * np.eye(77, dtype=int) == 4)

    # 3. Gewirtz (56 vertices) = blocks NOT containing point 0 -> SRG(56, 10, 0, 2)
    idx_gew = np.where(blocks[:, 0] == 0)[0]
    assert len(idx_gew) == 56
    A_gew = A_m22[np.ix_(idx_gew, idx_gew)].copy()
    assert np.all(A_gew.sum(axis=1) == 10)
    assert np.trace(A_gew @ A_gew @ A_gew) == 0
    G2 = A_gew @ A_gew
    assert np.all(G2 + 2 * A_gew - 8 * np.eye(56, dtype=int) == 2)

    return {
        "Gewirtz (n=56, d=10)": A_gew,
        "M22 (n=77, d=16)": A_m22,
        "Higman-Sims (n=100, d=22)": A_hs,
    }


def sa_min_subset_edges(adj: np.ndarray, m: int, restarts: int = 20, steps: int = 5000, seed: int = 42) -> tuple[int, list[int]]:
    n = adj.shape[0]
    rng = np.random.default_rng(seed)
    best_e = 10**9
    best_S = []
    for r in range(restarts):
        # Half of restarts start from a greedy independent set + lowest-deg additions
        if r % 2 == 0:
            # Build maximal independent set greedily
            avail = list(range(n))
            rng.shuffle(avail)
            S_set = set()
            for u in avail:
                if all(adj[u, v] == 0 for v in S_set):
                    S_set.add(u)
                    if len(S_set) == m:
                        break
            # Add vertices with smallest degree into S_set
            while len(S_set) < m:
                rem = [u for u in range(n) if u not in S_set]
                degs = [int(adj[u, list(S_set)].sum()) for u in rem]
                min_d = min(degs)
                cands = [rem[i] for i, d in enumerate(degs) if d == min_d]
                S_set.add(int(rng.choice(cands)))
            in_S = np.zeros(n, dtype=bool)
            in_S[list(S_set)] = True
        else:
            perm = rng.permutation(n)
            in_S = np.zeros(n, dtype=bool)
            in_S[perm[:m]] = True

        deg_in_S = adj[:, in_S].sum(axis=1).astype(int)
        cur_e = int(deg_in_S[in_S].sum()) // 2
        if cur_e < best_e:
            best_e = cur_e
            best_S = np.where(in_S)[0].tolist()

        for step in range(steps):
            # Swap 1 vertex in S with 1 vertex outside S
            s_idx = np.where(in_S)[0]
            out_idx = np.where(~in_S)[0]
            # Mostly pick worst in S / best outside S, with noise
            if rng.random() < 0.7:
                # pick u in S with near-max deg_in_S, v out with near-min deg_in_S
                d_in = deg_in_S[s_idx]
                u = int(s_idx[rng.choice(np.where(d_in >= d_in.max() - 1)[0])])
                d_out = deg_in_S[out_idx] - adj[out_idx, u]
                v = int(out_idx[rng.choice(np.where(d_out <= d_out.min() + 1)[0])])
            else:
                u = int(rng.choice(s_idx))
                v = int(rng.choice(out_idx))
            delta = int(deg_in_S[v]) - int(adj[u, v]) - int(deg_in_S[u])
            temp = max(0.05, 1.5 * (1.0 - step / steps))
            if delta <= 0 or rng.random() < np.exp(-delta / temp):
                in_S[u] = False
                in_S[v] = True
                deg_in_S = deg_in_S - adj[:, u] + adj[:, v]
                cur_e += delta
                if cur_e < best_e:
                    best_e = cur_e
                    best_S = np.where(in_S)[0].tolist()
    # Verify exact edge count
    exact_e = int(adj[np.ix_(best_S, best_S)].sum()) // 2
    assert exact_e == best_e
    return best_e, best_S


def milp_min_subset_edges(adj: np.ndarray, m: int, time_limit: float = 20.0):
    n = adj.shape[0]
    edges = list(zip(*np.where(np.triu(adj, 1) > 0)))
    E = len(edges)
    num_vars = n + E
    c = np.zeros(num_vars)
    c[n:] = 1.0
    integrality = np.ones(num_vars)
    bounds = Bounds(lb=np.zeros(num_vars), ub=np.ones(num_vars))
    rows, cols, vals = [], [], []
    for i in range(n):
        rows.append(0); cols.append(i); vals.append(1.0)
    lb = [float(m)]; ub = [float(n)]
    for idx_e, (u, v) in enumerate(edges):
        r = idx_e + 1
        rows.extend([r, r, r]); cols.extend([int(u), int(v), n + idx_e]); vals.extend([1.0, 1.0, -1.0])
        lb.append(-np.inf); ub.append(1.0)
    A_mat = sparse.csc_matrix((vals, (rows, cols)), shape=(1 + E, num_vars))
    res = milp(c=c, integrality=integrality, bounds=bounds,
               constraints=LinearConstraint(A_mat, lb, ub),
               options={"time_limit": time_limit})
    chosen = [i for i in range(n) if res.x[i] > 0.5] if res.x is not None else []
    exact_e = int(adj[np.ix_(chosen, chosen)].sum()) // 2 if chosen else None
    return res.success, exact_e, getattr(res, "mip_dual_bound", None)


def main():
    t0 = time.time()
    graphs = build_higman_sims_family()
    for name, A in graphs.items():
        n = A.shape[0]
        m = n // 2
        req = (n * n) // 50 + 1
        sa_e, sa_S = sa_min_subset_edges(A, m, restarts=30, steps=6000, seed=42)
        print(f"{name:28s}: SA min_e(m={m}) = {sa_e:3d} (ratio={sa_e/(n*n):.6f}) | req > n^2/50 => {req}")
        ok, milp_e, lb = milp_min_subset_edges(A, m, time_limit=12.0)
        print(f"    MILP (12s): success={ok}, best={milp_e}, dual_lb={lb}")
    print(f"Done in {time.time() - t0:.2f}s")


if __name__ == "__main__":
    main()
