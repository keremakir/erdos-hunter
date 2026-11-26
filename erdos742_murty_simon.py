r"""
Erdős #742 (decidable — Murty–Simon Conjecture: Minimal Diameter-2 Graphs have <= floor(n^2/4) edges!)
Smallest open cases in FormalConjectures/742.lean: n = 25 (bound 156), n = 27 (182), n = 28 (196).

Fast 64-bit Bitmask Exact Checker & 8-Core Local Search:
  A graph G is diameter-2-critical iff:
    (1) diam(G) == 2: for every non-adjacent pair u != v, (adj[u] & adj[v]) != 0 (and G != K_n).
    (2) Every edge (u, v) is CRITICAL:
        Either (adj[u] & adj[v]) == 0 (removing (u,v) breaks dist(u,v) <= 2),
        OR there exists w != u, v with (w !~ u and (adj[w] & adj[u]) == (1 << v)),
        OR there exists w != u, v with (w !~ v and (adj[w] & adj[v]) == (1 << u)).

Search Strategy:
  Start from perturbed dense diameter-2 graphs (K_{a,b} + triangles, blowups of C_5 / Petersen / cliques,
  random dense graphs), apply randomized minimalization (delete non-critical edges in random order)
  and simulated annealing over edge-flips + re-minimalization to maximize e(G) over exact
  diameter-2-critical graphs!
"""

import concurrent.futures
import json
import os
import random
import time
from pathlib import Path


def is_diam2(adj, n):
    full = (1 << n) - 1
    non_complete = False
    for u in range(n):
        non_nbrs = full ^ adj[u] ^ (1 << u)
        if non_nbrs:
            non_complete = True
        m = non_nbrs
        while m:
            lsb = m & -m
            v = lsb.bit_length() - 1
            if v > u and (adj[u] & adj[v]) == 0:
                return False
            m ^= lsb
    return non_complete


def critical_edges_mask(adj, n):
    """Return list of non-critical edges (u, v) with u < v (empty list <=> G is diameter-2-critical!)."""
    full = (1 << n) - 1
    # Mark every edge (u, v) that is the UNIQUE common neighbor bridge for some non-edge (u, w)
    crit = [0] * n
    for u in range(n):
        au = adj[u]
        # Any edge (u, v) not in a triangle is immediately critical
        m = au
        while m:
            lsb = m & -m
            v = lsb.bit_length() - 1
            if v > u and (au & adj[v]) == 0:
                crit[u] |= 1 << v
                crit[v] |= 1 << u
            m ^= lsb
        # Any non-edge (u, w) with unique common neighbor v makes edges (u, v) and (v, w) critical
        non_nbrs = full ^ au ^ (1 << u)
        m = non_nbrs
        while m:
            lsb = m & -m
            w = lsb.bit_length() - 1
            if w > u:
                common = au & adj[w]
                if common and (common & (common - 1)) == 0:
                    v = common.bit_length() - 1
                    crit[u] |= 1 << v
                    crit[v] |= 1 << u
                    crit[w] |= 1 << v
                    crit[v] |= 1 << w
            m ^= lsb

    non_crit = []
    for u in range(n):
        nc = adj[u] & (~crit[u])
        m = nc
        while m:
            lsb = m & -m
            v = lsb.bit_length() - 1
            if v > u:
                non_crit.append((u, v))
            m ^= lsb
    return non_crit


def minimalize_to_diam2_critical(adj, n, rng):
    """Delete non-critical edges in random order until G is EXACTLY diameter-2-critical."""
    a = list(adj)
    while True:
        nc = critical_edges_mask(a, n)
        if not nc:
            return a
        u, v = nc[rng.randrange(len(nc))]
        a[u] ^= 1 << v
        a[v] ^= 1 << u


def edge_count(adj):
    return sum(x.bit_count() for x in adj) // 2


def worker_murty_simon(args):
    n, seed, time_budget = args
    rng = random.Random(seed)
    t0 = time.perf_counter()
    target = (n * n) // 4

    best_e = 0
    best_nonbip_e = 0
    best_adj = None
    restarts = 0

    while time.perf_counter() - t0 < time_budget:
        restarts += 1
        # Diverse initializations:
        mode = restarts % 4
        adj = [0] * n
        if mode == 0:
            # Perturbed K_{a, b} with extra edges inside parts
            a = n // 2 + rng.randint(-2, 2)
            for u in range(a):
                for v in range(a, n):
                    adj[u] |= 1 << v
                    adj[v] |= 1 << u
            # Add random chords inside A and B, delete a few cross edges
            for _ in range(rng.randint(2, n)):
                u, v = rng.sample(range(n), 2)
                adj[u] |= 1 << v
                adj[v] |= 1 << u
            for _ in range(rng.randint(1, n // 2)):
                u = rng.randrange(a)
                v = rng.randrange(a, n)
                adj[u] &= ~(1 << v)
                adj[v] &= ~(1 << u)
        elif mode == 1:
            # Clique + bipartite hybrid (inspired by Füredi's near-extremal constructions!)
            k = rng.randint(3, 6)
            for u in range(k):
                for v in range(u + 1, k):
                    adj[u] |= 1 << v
                    adj[v] |= 1 << u
            for u in range(k, n):
                for v in range(n):
                    if u != v and rng.random() < 0.65:
                        adj[u] |= 1 << v
                        adj[v] |= 1 << u
        elif mode == 2:
            # Dense Erdős-Rényi G(n, p)
            p = rng.uniform(0.45, 0.75)
            for u in range(n):
                for v in range(u + 1, n):
                    if rng.random() < p:
                        adj[u] |= 1 << v
                        adj[v] |= 1 << u
        else:
            # Perturb best known non-bipartite or best graph
            if best_adj is not None:
                adj = list(best_adj)
                for _ in range(rng.randint(3, 10)):
                    u, v = rng.sample(range(n), 2)
                    adj[u] |= 1 << v
                    adj[v] |= 1 << u
            else:
                continue

        if not is_diam2(adj, n):
            continue

        crit_adj = minimalize_to_diam2_critical(adj, n, rng)
        if not is_diam2(crit_adj, n):
            continue
        ec = edge_count(crit_adj)

        # Check if non-bipartite (has any triangle)
        has_tri = any((crit_adj[u] & crit_adj[v]) != 0 for u in range(n) for v in range(u + 1, n) if (crit_adj[u] >> v) & 1)
        if ec > best_e:
            best_e = ec
            best_adj = list(crit_adj)
        if has_tri and ec > best_nonbip_e:
            best_nonbip_e = ec
        if ec > target:
            # Independent exact check before returning!
            assert is_diam2(crit_adj, n) and len(critical_edges_mask(crit_adj, n)) == 0
            return {
                "n": n, "target": target, "best_e": ec, "best_nonbip_e": best_nonbip_e,
                "restarts": restarts, "COUNTEREXAMPLE": True, "adj": crit_adj,
            }

    return {
        "n": n, "target": target, "best_e": best_e, "best_nonbip_e": best_nonbip_e,
        "restarts": restarts, "COUNTEREXAMPLE": False, "adj": None,
    }


def main():
    t0 = time.perf_counter()
    n_workers = min(8, os.cpu_count() or 4)
    print(f"=== ERDŐS #742 (MURTY-SIMON) — 8-CORE DIAMETER-2-CRITICAL HUNTER ({n_workers} workers) ===\n", flush=True)

    tasks = [
        (25, 11, 14.0), (25, 12, 14.0), (25, 13, 14.0), (25, 14, 14.0),
        (27, 21, 14.0), (27, 22, 14.0),
        (28, 31, 14.0), (28, 32, 14.0),
    ]
    results = []
    with concurrent.futures.ProcessPoolExecutor(max_workers=n_workers) as ex:
        for r in ex.map(worker_murty_simon, tasks):
            results.append(r)
            tag = "  <-- COUNTEREXAMPLE FOUND!!" if r["COUNTEREXAMPLE"] else ""
            print(
                f"  n={r['n']:2d} (bound={r['target']:3d}) | restarts={r['restarts']:5d} | "
                f"best_e={r['best_e']:3d} | best_nonbip_e={r['best_nonbip_e']:3d}{tag}",
                flush=True,
            )

    dt = time.perf_counter() - t0
    print(f"\nFinished {sum(r['restarts'] for r in results):,} exact diameter-2-critical minimalizations in {dt:.2f}s.", flush=True)
    out_path = Path(r"C:\Users\Kerem\.gemini\antigravity\scratch\erdos-hunter\erdos742_results.json")
    out_path.write_text(json.dumps(results, indent=2), encoding="utf-8")
    print(f"Saved to {out_path}", flush=True)


if __name__ == "__main__":
    main()
