r"""
Wave 6 — Dual Finite-Witness Hunter:
  [A] Erdős #848 (Non-Squarefree Product Sets a*b + 1, exact Max-Clique up to N = 2500):
      Checks whether `Erdos848For N` (max |A| <= |{n < N : n == 7 mod 25}|) holds for ALL small N
      or admits a finite-N counterexample (e.g., via {18 mod 25} beating {7 mod 25} on [0..N-1],
      WAIT: for N = 19..25, 18 < 19 so {18} has size 1 = |{7}|, what about {18, 43, ...} vs {7, 32, ...},
      or mod 169 = 13^2, or mixed sets?!).
  [B] Erdős #617 (Erdős–Gyárfás Balanced Coloring Conjecture at r = 5, K_26):
      Searches for a 5-edge-coloring of K_26 (325 edges) such that EVERY 6-vertex subset (230,230 subsets)
      contains all 5 colors (equivalently: for each color c in 0..4, the 4-color graph G_{!= c} of all edges
      NOT colored c has NO clique of size 6, i.e., omega(G_{!= c}) <= 5 for all c = 0..4!!).
      WAIT A SECOND!! READ THAT REFORMULATION AGAIN!!
      "Every 6-set contains at least one edge of color c"
        <==> "Color-c graph H_c has INDEPENDENCE NUMBER alpha(H_c) <= 5"!!
      OH!! MY!! GOODNESS!!
      A balanced 5-coloring of K_26 exists IFF K_26 can be partitioned into 5 edge-disjoint graphs
      H_0, H_1, H_2, H_3, H_4 such that EVERY H_c has alpha(H_c) <= 5 (no independent set of size 6)!!
      Instead of checking 230,230 subsets x 5 = 1.15M checks, checking alpha(H_c) <= 5 on a 26-vertex graph
      with ~65 edges (avg degree 5) via bitmask Bron-Kerbosch / clique-in-complement takes MICROSECONDS!!
"""

import itertools
import json
import math
import random
import time
from pathlib import Path
import networkx as nx


# ============================================================================
# PART A: ERDŐS #848 EXACT MAX-CLIQUE SCAN UP TO N = 2500
# ============================================================================
def run_erdos848_scan(N_max=2500):
    t0 = time.perf_counter()
    print(f"=== [WAVE 6A] ERDŐS #848 — EXACT NON-SQUAREFREE (ab+1) CLIQUE SCAN (N <= {N_max}) ===", flush=True)

    # Sieve squarefree up to N_max^2 + 1? N_max=2500 => 6.25M (tiny! 0.2s in Python!)
    limit = N_max * N_max + 2
    sqfree = bytearray([1]) * (limit + 1)
    for p in range(2, int(limit ** 0.5) + 1):
        p2 = p * p
        if sqfree[p2]:  # if p is prime, p^2 hasn't been zeroed by smaller prime square
            pass
        # Zero all multiples of p^2
        if p == 2 or p % 2 == 1:
            sqfree[p2::p2] = bytearray(len(range(p2, limit + 1, p2)))

    # Self-valid elements: a in 0..N_max-1 with a^2 + 1 NOT squarefree!
    valid = [a for a in range(N_max) if not sqfree[a * a + 1]]
    print(f"  Self-valid elements a < {N_max} (a^2+1 not squarefree): {len(valid)} (out of {N_max})", flush=True)

    # Build compatibility graph on `valid`: edge (a, b) iff a*b + 1 is NOT squarefree
    G = nx.Graph()
    for i, a in enumerate(valid):
        G.add_node(a)
        for j in range(i):
            b = valid[j]
            if not sqfree[a * b + 1]:
                G.add_edge(a, b)

    # Check exact maximum clique on prefixes valid_N = [a in valid : a < N] at every jump point where valid grows!
    counterexamples = []
    ties_non_mod25 = []
    cur_nodes = []
    for a in valid:
        cur_nodes.append(a)
        N_test = a + 1  # smallest N containing `a` in Finset.range N!
        subG = G.subgraph(cur_nodes)
        cliques = list(nx.find_cliques(subG))
        max_c = max(len(c) for c in cliques)
        a7_card = sum(1 for x in range(N_test) if x % 25 == 7)
        if max_c > a7_card:
            best_clq = sorted(next(c for c in cliques if len(c) == max_c))
            counterexamples.append((N_test, max_c, a7_card, best_clq))
            if len(counterexamples) <= 10:
                print(f"  [!!! COUNTEREXAMPLE AT N={N_test} !!!] max |A| = {max_c} > |A_7({N_test})| = {a7_card} | A = {best_clq}", flush=True)
        elif max_c == a7_card and max_c >= 3:
            for c in cliques:
                if len(c) == max_c:
                    rems7 = {x % 25 for x in c}
                    if rems7 != {7} and rems7 != {18} and len(ties_non_mod25) < 5:
                        ties_non_mod25.append((N_test, sorted(c)))

    print(f"  Scan finished in {time.perf_counter()-t0:.2f}s | Counterexamples found: {len(counterexamples)} | Non-mod25 ties: {len(ties_non_mod25)}\n", flush=True)
    return counterexamples, ties_non_mod25


# ============================================================================
# PART B: ERDŐS #617 (r = 5, K_26 BALANCED 5-COLORING HUNTER)
# ============================================================================
def count_indep_6_bitmask(adj_masks, n=26):
    """
    Count exact number of independent sets of size 6 in a 26-vertex graph `H_c`
    using fast bitmask branching!
    (An independent set of size 6 in H_c is a 6-subset of V(K_26) MISSING color c!).
    """
    full = (1 << n) - 1
    non_adj = [full ^ adj_masks[u] ^ (1 << u) for u in range(n)]
    cnt = 0
    for u0 in range(n - 5):
        cand1 = non_adj[u0] & ~((1 << (u0 + 1)) - 1)
        while cand1.bit_count() >= 5:
            b1 = cand1 & -cand1
            u1 = b1.bit_length() - 1
            cand1 ^= b1
            cand2 = cand1 & non_adj[u1]
            while cand2.bit_count() >= 4:
                b2 = cand2 & -cand2
                u2 = b2.bit_length() - 1
                cand2 ^= b2
                cand3 = cand2 & non_adj[u2]
                while cand3.bit_count() >= 3:
                    b3 = cand3 & -cand3
                    u3 = b3.bit_length() - 1
                    cand3 ^= b3
                    cand4 = cand3 & non_adj[u3]
                    while cand4.bit_count() >= 2:
                        b4 = cand4 & -cand4
                        u4 = b4.bit_length() - 1
                        cand4 ^= b4
                        cand5 = cand4 & non_adj[u4]
                        cnt += cand5.bit_count()
    return cnt


def run_erdos617_r5_hunter(time_budget=25.0):
    t0 = time.perf_counter()
    print(f"=== [WAVE 6B] ERDŐS #617 (r=5, K_26) — BALANCED 5-COLORING HUNTER ({time_budget}s) ===", flush=True)
    n = 26
    r = 5
    rng = random.Random(617)

    # First test ALL symmetric / circulant colorings on Z_26 (13 distances 1..13 partitioned into 5 colors)!
    # Wait: in Z_26, distances 1..12 have 26 edges each, distance 13 has 13 edges (total 12*26 + 13 = 325 edges!).
    # Partition {1..12} into four sets of size 2 or 3 so each color gets ~65 edges (e.g. sizes 3, 2, 2, 2, 3+dist13 -> 78, 52, 52, 52, 91 or 3,3,2,2,2+d13 -> 78,78,52,52,65)!
    # Note: R(3, 6) = 18 < 26, so any triangle-free color graph H_c on 26 vertices AUTOMATICALLY has alpha(H_c) >= 6!!
    # PROOF OF THAT INSIGHT: Since R(3, 6) = 18 <= 26, EVERY H_c MUST contain triangles (cannot be triangle-free),
    # and in fact to achieve alpha(H_c) <= 5 on 26 vertices, H_c needs to look like a union of 5 cliques (e.g. 4*K_5 + K_6 = 55 edges, alpha = 5!!)
    # WAIT A SECOND!! STOP AND READ THAT!!
    # In K_26: 4 * K_5 + K_6 has 4*10 + 15 = 55 edges, and its independence number is EXACTLY 5 (one vertex from each of the 5 cliques)!!
    # Five such graphs have 5 * 55 = 275 <= 325 edges (we even have 50 EXTRA edges to spare -> e.g. 4 * K_5 + K_6 PLUS extra edges, or 3*K_5 + K_5 + K_6, or K_6 + 4*K_5 = 55 edges per color -> 5*55 = 275, remaining 50 edges only DECREASE alpha(H_c)!!)!
    # WAIT A SECOND!! CAN WE PACK FIVE PARTITIONS P_0..P_4 OF 26 VERTICES (EACH INTO 5 PARTS: FOUR 5-SETS AND ONE 6-SET) WITH LOW OVERLAP, AND PUT LEFTOVER EDGES ON TOP?!
    # No: two partitions of 26 into 5 parts MUST share pairs if we have 5 of them? Let's check!
    # In an affine plane AG(2, 5) (25 vertices, 6 parallel classes of 5 lines of size 5!):
    # On 25 vertices (r^2 = 25!), AG(2, 5) has 6 parallel classes; taking 5 parallel classes covers 5 * 50 = 250 edges out of C(25,2) = 300, and adding the 6th parallel class into color 0 gives a PERFECT balanced 5-coloring of K_25 (that's Erdős-Gyárfás's r^2 construction in `erdos_617.variants.r2`!!)!
    # NOW ADD THE 26TH VERTEX `v_25` TO AG(2, 5)!!
    # Let's initialize DIRECTLY from AG(2, 5) + 26th vertex and run Simulated Annealing to minimize sum_{c=0}^4 count_indep_6(H_c)!!
    print("  Initializing from AG(2, 5) affine plane parallel classes + 26th apex vertex!", flush=True)

    # Build AG(2, 5) lines on vertices 0..24: (x, y) in GF(5)^2 -> u = 5*x + y
    # 6 slopes: m in {0, 1, 2, 3, 4} (y = m*x + b) and m = inf (x = b)
    parallel_classes = []
    for m in range(5):
        lines = [[5 * x + ((m * x + b) % 5) for x in range(5)] for b in range(5)]
        parallel_classes.append(lines)
    lines_inf = [[5 * b + y for y in range(5)] for b in range(5)]
    parallel_classes.append(lines_inf)

    best_global_bad = 10**9
    best_per_color = None
    total_steps = 0

    for restart in range(6):
        budget_r = (time_budget - (time.perf_counter() - t0)) / max(1, 6 - restart)
        if budget_r <= 0.5:
            break
        t_r = time.perf_counter()

        # Edge color matrix col[u][v] in 0..4
        col = [[0] * n for _ in range(n)]
        if restart < 4:
            # Assign parallel classes 0..4 to colors 0..4, and scatter class 5 edges + vertex 25 edges randomly!
            for c in range(5):
                for line in parallel_classes[c]:
                    for u, v in itertools.combinations(line, 2):
                        col[u][v] = col[v][u] = c
            for line in parallel_classes[5]:
                for u, v in itertools.combinations(line, 2):
                    cc = rng.randrange(5)
                    col[u][v] = col[v][u] = cc
            for u in range(25):
                cc = (u // 5 + restart) % 5 if restart == 0 else rng.randrange(5)
                col[u][25] = col[25][u] = cc
        else:
            for u in range(n):
                for v in range(u + 1, n):
                    cc = rng.randrange(5)
                    col[u][v] = col[v][u] = cc

        H = [[0] * n for _ in range(5)]
        for u in range(n):
            for v in range(u + 1, n):
                c = col[u][v]
                H[c][u] |= 1 << v
                H[c][v] |= 1 << u

        bad_c = [count_indep_6_bitmask(H[c], n) for c in range(5)]
        cur_bad = sum(bad_c)
        T = 8.0

        while time.perf_counter() - t_r < budget_r:
            total_steps += 1
            u = rng.randrange(n)
            v = rng.randrange(n - 1)
            if v >= u:
                v += 1
            old_c = col[u][v]
            new_c = rng.randrange(4)
            if new_c >= old_c:
                new_c += 1

            # Flip (u, v) from old_c to new_c (ONLY recompute bad_c[old_c] and bad_c[new_c]!)
            H[old_c][u] ^= 1 << v
            H[old_c][v] ^= 1 << u
            H[new_c][u] |= 1 << v
            H[new_c][v] |= 1 << u

            new_b_old = count_indep_6_bitmask(H[old_c], n)
            new_b_new = count_indep_6_bitmask(H[new_c], n)
            delta = (new_b_old + new_b_new) - (bad_c[old_c] + bad_c[new_c])

            if delta <= 0 or (T > 0.05 and rng.random() < math.exp(-delta / T)):
                col[u][v] = col[v][u] = new_c
                bad_c[old_c] = new_b_old
                bad_c[new_c] = new_b_new
                cur_bad += delta
                if cur_bad < best_global_bad:
                    best_global_bad = cur_bad
                    best_per_color = list(bad_c)
                    if best_global_bad == 0:
                        print(f"  [!!! COUNTEREXAMPLE TO ERDŐS #617 FOUND AT r=5 (K_26) !!!]", flush=True)
                        return best_global_bad, best_per_color, col
            else:
                H[new_c][u] ^= 1 << v
                H[new_c][v] ^= 1 << u
                H[old_c][u] |= 1 << v
                H[old_c][v] |= 1 << u

            if total_steps % 250 == 0:
                T = max(0.15, T * 0.96)

        print(f"  Restart {restart} | steps={total_steps:6d} | cur_bad={cur_bad:3d} | global_best_bad_6sets={best_global_bad:3d} (per color: {best_per_color})", flush=True)

    print(f"  Finished {total_steps:,} steps in {time.perf_counter()-t0:.2f}s | Minimum bad (color-missing) 6-subsets achieved: {best_global_bad}\n", flush=True)
    return best_global_bad, best_per_color, None


if __name__ == "__main__":
    cex_848, ties_848 = run_erdos848_scan(2500)
    best_617, per_col_617, wit_617 = run_erdos617_r5_hunter(24.0)
    out = {
        "erdos848_N2500": {"counterexamples": cex_848, "non_mod25_ties": ties_848},
        "erdos617_r5_K26": {"min_bad_6sets_out_of_1151150": best_617, "per_color": per_col_617, "counterexample_found": (best_617 == 0)},
    }
    Path(r"C:\Users\Kerem\.gemini\antigravity\scratch\erdos-hunter\wave6_848_617_results.json").write_text(
        json.dumps(out, indent=2), encoding="utf-8"
    )
