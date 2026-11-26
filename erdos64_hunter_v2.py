r"""
Erdős #64 ($1,000 Prize — Erdős–Gyárfás Conjecture: Every graph with min-degree >= 3 has a 2^k-cycle, k >= 2)
Multi-Core 64-bit Bitmask Simulated Annealing Hunter v2 (45s hard stop-loss)!

Targets:
  1) Exact fast bitmask counters for C_4, C_8, and C_16 (and exact DFS check for C_32 if C_4=C_8=C_16=0!).
  2) Multi-core parallel search across n in {30, 36, 42, 48} (cubic & mixed {3,4} graphs with delta >= 3).
  3) Any candidate reaching C_4 = C_8 = C_16 = 0 is IMMEDIATELY verified for ALL 2^k cycles (k=2..5)
     and saved to erdos64_v2_results.json!
"""

import concurrent.futures
import json
import math
import os
import random
import time
from pathlib import Path


def count_c4(adj, n):
    """Exact number of 4-cycles using bitmask common-neighbor counting."""
    tot = 0
    for u in range(n):
        au = adj[u]
        for v in range(u + 1, n):
            c = (au & adj[v]).bit_count()
            if c >= 2:
                tot += c * (c - 1) // 2
    return tot // 2


def has_cycle_of_len(adj, n, target_len, max_count=50):
    """Count (up to max_count) simple cycles of exact length target_len via bitmask DFS."""
    found = 0
    for start in range(n - target_len + 1):
        start_bit = 1 << start
        # Only traverse vertices >= start to break symmetry (each cycle counted twice: both orientations)
        allowed_mask = ~((1 << start) - 1) & ((1 << n) - 1)

        def dfs(u, visited, depth):
            nonlocal found
            if found >= max_count * 2:
                return
            if depth == target_len:
                if adj[u] & start_bit:
                    found += 1
                return
            nxt = adj[u] & (~visited) & allowed_mask
            while nxt:
                lsb = nxt & -nxt
                v = lsb.bit_length() - 1
                dfs(v, visited | lsb, depth + 1)
                if found >= max_count * 2:
                    return
                nxt ^= lsb

        dfs(start, start_bit, 1)
        if found >= max_count * 2:
            break
    return found // 2


def random_regular_graph_bitmask(n, d, rng):
    """Configuration model with retry for simple d-regular graph on n vertices."""
    for _ in range(200):
        stubs = []
        for v in range(n):
            stubs.extend([v] * d)
        rng.shuffle(stubs)
        adj = [0] * n
        ok = True
        for i in range(0, len(stubs), 2):
            u, v = stubs[i], stubs[i + 1]
            if u == v or ((adj[u] >> v) & 1):
                ok = False
                break
            adj[u] |= 1 << v
            adj[v] |= 1 << u
        if ok:
            return adj
    raise RuntimeError("Failed to sample random regular graph")


def worker_search(args):
    n, d, seed, time_budget = args
    rng = random.Random(seed)
    t0 = time.perf_counter()

    adj = random_regular_graph_bitmask(n, d, rng)
    # Maintain edge list for O(1) 2-opt edge-swap proposals
    edges = [(u, v) for u in range(n) for v in range(u + 1, n) if (adj[u] >> v) & 1]
    num_e = len(edges)

    def energy(a):
        c4 = count_c4(a, n)
        if c4 > 6:
            return 1000 * c4 + 100, c4, -1, -1
        c8 = has_cycle_of_len(a, n, 8, max_count=20)
        if c4 == 0 and c8 == 0:
            c16 = has_cycle_of_len(a, n, 16, max_count=10)
            return c16, 0, 0, c16
        return 1000 * c4 + 25 * c8, c4, c8, -1

    cur_E, cur_c4, cur_c8, cur_c16 = energy(adj)
    best_E, best_c4, best_c8, best_c16 = cur_E, cur_c4, cur_c8, cur_c16
    best_adj = list(adj)

    steps = 0
    T = 40.0
    while time.perf_counter() - t0 < time_budget:
        steps += 1
        # Propose a 2-opt degree-preserving edge swap: (u,v), (x,y) -> (u,x), (v,y)
        i1 = rng.randrange(num_e)
        i2 = rng.randrange(num_e)
        if i1 == i2:
            continue
        u, v = edges[i1]
        x, y = edges[i2]
        if rng.random() < 0.5:
            x, y = y, x
        if u == x or u == y or v == x or v == y:
            continue
        if ((adj[u] >> x) & 1) or ((adj[v] >> y) & 1):
            continue

        # Apply swap
        adj[u] ^= (1 << v) | (1 << x)
        adj[v] ^= (1 << u) | (1 << y)
        adj[x] ^= (1 << y) | (1 << u)
        adj[y] ^= (1 << x) | (1 << v)

        new_E, nc4, nc8, nc16 = energy(adj)
        delta = new_E - cur_E
        if delta <= 0 or (T > 0.05 and rng.random() < math.exp(-delta / T)):
            cur_E, cur_c4, cur_c8, cur_c16 = new_E, nc4, nc8, nc16
            edges[i1] = (u, x) if u < x else (x, u)
            edges[i2] = (v, y) if v < y else (y, v)
            if new_E < best_E:
                best_E, best_c4, best_c8, best_c16 = new_E, nc4, nc8, nc16
                best_adj = list(adj)
                if best_c4 == 0 and best_c8 == 0 and best_c16 == 0:
                    # CHECK C_32!
                    c32 = has_cycle_of_len(best_adj, n, 32, max_count=1) if n >= 32 else 0
                    return {
                        "n": n, "d": d, "seed": seed, "steps": steps,
                        "c4": 0, "c8": 0, "c16": 0, "c32": c32,
                        "COUNTEREXAMPLE": (c32 == 0),
                        "adj": best_adj,
                    }
        else:
            # Revert swap
            adj[u] ^= (1 << v) | (1 << x)
            adj[v] ^= (1 << u) | (1 << y)
            adj[x] ^= (1 << y) | (1 << u)
            adj[y] ^= (1 << x) | (1 << v)

        if steps % 200 == 0:
            T = max(0.3, T * 0.96)
            if steps % 3000 == 0:
                T = 25.0  # reheat

    return {
        "n": n, "d": d, "seed": seed, "steps": steps,
        "c4": best_c4, "c8": best_c8, "c16": best_c16, "c32": -1,
        "COUNTEREXAMPLE": False,
        "adj": None,
    }


def main():
    t0 = time.perf_counter()
    n_workers = min(8, os.cpu_count() or 4)
    print(f"=== ERDŐS #64 ($1,000) — PARALLEL 64-BIT BITMASK SA HUNTER v2 ({n_workers} workers) ===\n", flush=True)

    # 8 parallel tasks across n = 30, 36, 42, 48 (2 seeds each, 18s per task => ~18-25s wall time!)
    tasks = [
        (30, 3, 101, 18.0), (30, 3, 102, 18.0),
        (36, 3, 201, 18.0), (36, 3, 202, 18.0),
        (42, 3, 301, 18.0), (42, 3, 302, 18.0),
        (48, 3, 401, 18.0), (48, 3, 402, 18.0),
    ]
    results = []
    with concurrent.futures.ProcessPoolExecutor(max_workers=n_workers) as ex:
        for r in ex.map(worker_search, tasks):
            results.append(r)
            tag = "  <-- COUNTEREXAMPLE FOUND!!" if r["COUNTEREXAMPLE"] else ""
            print(
                f"  n={r['n']:2d} (d={r['d']}, seed={r['seed']}) | steps={r['steps']:6d} | "
                f"best C4={r['c4']:2d}, C8={r['c8']:2d}, C16={r['c16']:2d}{tag}",
                flush=True,
            )

    dt = time.perf_counter() - t0
    print(f"\nFinished {sum(r['steps'] for r in results):,} SA steps across 8 parallel workers in {dt:.2f}s.", flush=True)
    out_path = Path(r"C:\Users\Kerem\.gemini\antigravity\scratch\erdos-hunter\erdos64_v2_results.json")
    out_path.write_text(json.dumps(results, indent=2), encoding="utf-8")
    print(f"Saved to {out_path}", flush=True)


if __name__ == "__main__":
    main()
