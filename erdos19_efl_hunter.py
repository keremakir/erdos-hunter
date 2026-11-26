r"""
Erdős #19 ($500 Prize — Erdős–Faber–Lovász Conjecture, decidable; smallest open case n = 13!)
Linear Hypergraph Edge-Coloring & Counterexample Hunter at n = 13 (and n = 14, 15)!

Equivalence (Dual Linear Hypergraph Form):
  EFL(n) holds  <==>  Every linear hypergraph H = (V, E) on |V| = n vertices
                      (every pair of hyperedges shares at most 1 vertex, |e| >= 2)
                      has chromatic index chi'(H) <= n.
  Since adding uncovered pairs as 2-edges only increases chi'(H), maximal candidates are
  Linear Spaces on n vertices (every pair {u, v} lies in a UNIQUE block e in E).

Key Observation for n = 13:
  - 13 = 3^2 + 3 + 1 = |PG(2, 3)| (projective plane of order 3: 13 lines of size 4, chi' = 13).
  - Any counterexample at n = 13 must have chi'(H) >= 14, and in particular a dense core of
    intersecting large blocks (size 3, 4, 5) plus 2-edges where greedy/Seymour bounds are tight.
  - Note: By the Faber-Lovász / Erdős theorem, if every block has size >= 3 and total blocks > n,
    wait — in a linear space on n=13, maximum number of intersecting blocks is 13 (de Bruijn-Erdős!),
    so chi'(H) >= 14 can ONLY happen if the line graph L(H) has clique number omega(L(H)) <= 13
    (since de Bruijn-Erdős says any pairwise intersecting family has size <= n!) YET chi(L(H)) >= 14!
  - THAT'S THE EXACT STRUCTURAL TARGET:
    Build linear spaces H on n=13 vertices (including PG(2,3) mutations, STS(13) mutations,
    near-pencils, symmetric/cyclic PBD(13, K) families, and greedy-adversarial linear spaces)
    and compute EXACT chi'(H) (or check 13-colorability) via HiGHS MILP + DSATUR/backtracking!
"""

import itertools
import json
import random
import time
from pathlib import Path
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import csc_matrix


def is_linear_hypergraph(n, blocks):
    """Verify every pair of vertices is covered at most once and all blocks have size >= 2."""
    seen_pairs = set()
    for b in blocks:
        if len(b) < 2:
            return False
        for u, v in itertools.combinations(sorted(b), 2):
            if (u, v) in seen_pairs:
                return False
            seen_pairs.add((u, v))
    return True


def complete_to_linear_space(n, blocks):
    """Add all uncovered pairs as 2-edges (maximizes chi'(H) without breaking linearity)."""
    covered = set()
    res = [tuple(sorted(b)) for b in blocks if len(b) >= 2]
    for b in res:
        for u, v in itertools.combinations(b, 2):
            covered.add((u, v))
    for u in range(n):
        for v in range(u + 1, n):
            if (u, v) not in covered:
                res.append((u, v))
    return res


def build_PG2_3():
    """Projective plane PG(2, 3): 13 points, 13 lines of size 4."""
    pts = [(1, y, z) for y in range(3) for z in range(3)] + [(0, 1, z) for z in range(3)] + [(0, 0, 1)]
    lines = []
    for a, b, c in pts:
        line = [i for i, (x, y, z) in enumerate(pts) if (a * x + b * y + c * z) % 3 == 0]
        lines.append(tuple(line))
    assert len(lines) == 13 and all(len(l) == 4 for l in lines)
    assert is_linear_hypergraph(13, lines)
    return lines


def build_STS13_cyclic():
    """Cyclic Steiner Triple System STS(13): 26 triples on Z_13 via base blocks {0,1,4}, {0,2,7}."""
    blocks = []
    for base in [(0, 1, 4), (0, 2, 7)]:
        for s in range(13):
            blocks.append(tuple(sorted((x + s) % 13 for x in base)))
    assert len(blocks) == 26 and is_linear_hypergraph(13, blocks)
    return blocks


def greedy_dsatur_color(n, blocks, max_colors):
    """
    Fast DSATUR + Kempe-free greedy edge-coloring of linear hypergraph H (equivalently vertex coloring of L(H)).
    Returns (True, coloring) if <= max_colors found, else (False, None).
    """
    m = len(blocks)
    # Build conflict adjacency in L(H) (two blocks conflict iff they share a vertex)
    bsets = [set(b) for b in blocks]
    adj = [[] for _ in range(m)]
    for i in range(m):
        for j in range(i + 1, m):
            if bsets[i] & bsets[j]:
                adj[i].append(j)
                adj[j].append(i)

    # Order: largest blocks first, then DSATUR
    colors = [-1] * m
    sat = [set() for _ in range(m)]
    degs = [len(adj[i]) for i in range(m)]

    for _ in range(m):
        # Pick uncolored block with highest (len(sat[i]), len(blocks[i]), degs[i])
        best = -1
        best_key = (-1, -1, -1)
        for i in range(m):
            if colors[i] == -1:
                key = (len(sat[i]), len(blocks[i]), degs[i])
                if key > best_key:
                    best_key = key
                    best = i
        used = sat[best]
        chosen = -1
        for c in range(max_colors):
            if c not in used:
                chosen = c
                break
        if chosen == -1:
            return False, None
        colors[best] = chosen
        for nb in adj[best]:
            sat[nb].add(chosen)
    return True, colors


def exact_milp_colorable(n, blocks, num_colors, time_limit=5.0):
    """
    Exact check whether linear hypergraph H = (V, blocks) is `num_colors`-edge-colorable via HiGHS MILP!
    Variables: x_{e, c} in {0, 1} for e in 0..m-1, c in 0..num_colors-1.
    Constraints:
      - Every block e gets exactly 1 color: sum_c x_{e, c} == 1
      - Every vertex v sees each color c at most once: sum_{e ni v} x_{e, c} <= 1
    (Using vertex-color formulation has only m + n*C constraints instead of O(m^2*C) — SUPER FAST!)
    """
    m = len(blocks)
    C = num_colors
    # Symmetry breaking: fix a maximum clique of blocks (e.g., all blocks containing vertex 0) to colors 0, 1, ...
    v0_blocks = [i for i, b in enumerate(blocks) if 0 in b]

    num_vars = m * C
    rows, cols, vals = [], [], []
    lb, ub = [], []
    r_idx = 0

    # 1) sum_c x_{e, c} == 1
    for e in range(m):
        for c in range(C):
            rows.append(r_idx)
            cols.append(e * C + c)
            vals.append(1.0)
        lb.append(1.0)
        ub.append(1.0)
        r_idx += 1

    # 2) For each vertex v and color c: sum_{e ni v} x_{e, c} <= 1
    v_to_blocks = [[] for _ in range(n)]
    for e, b in enumerate(blocks):
        for v in b:
            v_to_blocks[v].append(e)
    for v in range(n):
        bs = v_to_blocks[v]
        if len(bs) <= 1:
            continue
        for c in range(C):
            for e in bs:
                rows.append(r_idx)
                cols.append(e * C + c)
                vals.append(1.0)
            lb.append(0.0)
            ub.append(1.0)
            r_idx += 1

    # Symmetry breaking bounds
    var_lb = np.zeros(num_vars, dtype=np.float64)
    var_ub = np.ones(num_vars, dtype=np.float64)
    for ci, e in enumerate(v0_blocks):
        if ci < C:
            var_lb[e * C + ci] = 1.0
            for c2 in range(C):
                if c2 != ci:
                    var_ub[e * C + c2] = 0.0

    A = csc_matrix((vals, (rows, cols)), shape=(r_idx, num_vars))
    res = milp(
        c=np.zeros(num_vars),
        integrality=np.ones(num_vars, dtype=np.int8),
        bounds=Bounds(var_lb, var_ub),
        constraints=LinearConstraint(A, np.array(lb), np.array(ub)),
        options={"time_limit": time_limit, "disp": False},
    )
    if res.status == 0 and res.x is not None:
        return "COLORABLE", res.x
    elif res.status == 2:
        return "INFEASIBLE_COUNTEREXAMPLE", None
    else:
        return f"TIMEOUT(status={res.status})", None


def random_maximal_linear_space(n, rng, size_weights=(0.0, 0.0, 0.2, 0.4, 0.3, 0.1)):
    """Generate a diverse maximal linear space on n vertices by greedily packing random large blocks (sizes 3..6)."""
    covered = set()
    blocks = []
    # Try adding blocks of sizes 6, 5, 4, 3
    verts = list(range(n))
    for _ in range(300):
        k = rng.choices([3, 4, 5, 6], weights=[40, 35, 18, 7])[0]
        if k >= n:
            continue
        cand = tuple(sorted(rng.sample(verts, k)))
        ok = True
        for u, v in itertools.combinations(cand, 2):
            if (u, v) in covered:
                ok = False
                break
        if ok:
            blocks.append(cand)
            for u, v in itertools.combinations(cand, 2):
                covered.add((u, v))
    return complete_to_linear_space(n, blocks)


def mutate_linear_space(n, base_blocks, rng, num_drop=2):
    """Drop `num_drop` random large blocks, repack with different random large blocks, complete with 2-edges."""
    large = [b for b in base_blocks if len(b) >= 3]
    if len(large) <= num_drop:
        return random_maximal_linear_space(n, rng)
    kept = rng.sample(large, len(large) - num_drop)
    covered = set()
    for b in kept:
        for u, v in itertools.combinations(b, 2):
            covered.add((u, v))
    verts = list(range(n))
    for _ in range(150):
        k = rng.choices([3, 4, 5], weights=[50, 35, 15])[0]
        cand = tuple(sorted(rng.sample(verts, k)))
        if all((u, v) not in covered for u, v in itertools.combinations(cand, 2)):
            kept.append(cand)
            for u, v in itertools.combinations(cand, 2):
                covered.add((u, v))
    return complete_to_linear_space(n, kept)


def main():
    t0 = time.perf_counter()
    print("=== ERDŐS #19 ($500 — ERDŐS-FABER-LOVÁSZ) LINEAR SPACE HUNTER (n = 13, 14, 15) ===", flush=True)
    rng = random.Random(20261125)

    pg13 = build_PG2_3()
    sts13 = build_STS13_cyclic()

    stats = {}
    for n in [13, 14, 15]:
        tested = 0
        dsatur_hard = 0
        milp_solved = 0
        milp_timeouts = 0
        counterexamples = []

        candidates = []
        if n == 13:
            candidates.append(("PG(2,3)", pg13))
            candidates.append(("STS(13)", sts13))
            for i in range(120):
                candidates.append((f"PG_mut_{i}", mutate_linear_space(13, pg13, rng, num_drop=rng.randint(1, 5))))
            for i in range(120):
                candidates.append((f"STS_mut_{i}", mutate_linear_space(13, sts13, rng, num_drop=rng.randint(2, 8))))
            for i in range(260):
                candidates.append((f"Rand13_{i}", random_maximal_linear_space(13, rng)))
        else:
            for i in range(200):
                candidates.append((f"Rand{n}_{i}", random_maximal_linear_space(n, rng)))

        for cname, blocks in candidates:
            assert is_linear_hypergraph(n, blocks)
            tested += 1
            ok, _ = greedy_dsatur_color(n, blocks, n)
            if ok:
                continue
            dsatur_hard += 1
            status, _ = exact_milp_colorable(n, blocks, n, time_limit=4.0)
            if status == "COLORABLE":
                milp_solved += 1
            elif status == "INFEASIBLE_COUNTEREXAMPLE":
                print(f"  [!!! COUNTEREXAMPLE FOUND !!!] n={n}, {cname}, {len(blocks)} blocks!", flush=True)
                counterexamples.append((cname, blocks))
            else:
                milp_timeouts += 1

        print(
            f"  n={n:2d} | tested={tested:3d} | DSATUR-hard={dsatur_hard:3d} | "
            f"MILP-colorable={milp_solved:3d} | timeouts={milp_timeouts:2d} | counterexamples={len(counterexamples)}",
            flush=True,
        )
        stats[f"n_{n}"] = {
            "tested": tested,
            "dsatur_hard": dsatur_hard,
            "milp_colorable": milp_solved,
            "milp_timeouts": milp_timeouts,
            "counterexamples": len(counterexamples),
        }

    print(f"\nFinished in {time.perf_counter()-t0:.2f}s.", flush=True)
    out_path = Path(r"C:\Users\Kerem\.gemini\antigravity\scratch\erdos-hunter\erdos19_hunter_results.json")
    out_path.write_text(json.dumps(stats, indent=2), encoding="utf-8")
    print(f"Saved results to {out_path}", flush=True)


if __name__ == "__main__":
    main()
