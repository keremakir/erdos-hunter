"""
Erdős-Hunter Yalın Pilot (Rota B — GravityCourt Revize MVP)
Hedef: Erdős Problem #64 ($1.000 — Erdős–Gyárfás Sanısı, falsifiable)
Mimari: Antigravity (Dış Döngü Stratejist) + 64-bit Bitmask Yerel Arama + Bağımsız Doğrulayıcı
Kısıtlar: Sıfır API çağrısı, sıfır VRAM, katı zaman zarar-kes (stop-loss) ve ön-kalibrasyon kapısı.
"""

import json
import math
import random
import time
from pathlib import Path
import numpy as np


def adj_to_masks(adj_list):
    return [sum(1 << v for v in nbrs) for nbrs in adj_list]


def count_c4_fast(masks):
    """Exact count of 4-cycles in O(n^2) bit ops: sum_{u<v} C(|N(u) & N(v)|, 2) / 2."""
    n = len(masks)
    total = 0
    for u in range(n):
        mu = masks[u]
        for v in range(u + 1, n):
            k = (mu & masks[v]).bit_count()
            if k >= 2:
                total += k * (k - 1) // 2
    return total // 2


def has_cycle_of_length(masks, target_len, max_nodes_visit=200000):
    """Exact bitmask DFS with vertex-order symmetry breaking (start is min vertex in cycle)."""
    n = len(masks)
    nodes_visited = 0

    for start in range(n - target_len + 1):
        # Only explore vertices >= start to avoid counting each cycle target_len times
        allowed = ((1 << n) - 1) ^ ((1 << start) - 1)
        start_nbrs = masks[start] & allowed
        if start_nbrs.bit_count() < 2:
            continue

        # Iterative or recursive DFS; for length 8/16/32 recursion depth <= 32 is tiny
        found = False

        def dfs(curr, depth, visited, first_nbr):
            nonlocal found, nodes_visited
            if found:
                return
            nodes_visited += 1
            if nodes_visited > max_nodes_visit:
                return
            rem = target_len - depth
            if rem == 1:
                if (masks[curr] >> start) & 1:
                    # Symmetry break: enforce second vertex < last vertex
                    if curr > first_nbr:
                        found = True
                return
            cand = masks[curr] & allowed & ~visited
            while cand:
                lsb = cand & -cand
                nxt = lsb.bit_length() - 1
                cand ^= lsb
                dfs(nxt, depth + 1, visited | lsb, first_nbr)
                if found or nodes_visited > max_nodes_visit:
                    return

        nbr_bits = start_nbrs
        while nbr_bits:
            lsb = nbr_bits & -nbr_bits
            v1 = lsb.bit_length() - 1
            nbr_bits ^= lsb
            dfs(v1, 2, (1 << start) | lsb, v1)
            if found:
                return True, nodes_visited
            if nodes_visited > max_nodes_visit:
                return None, nodes_visited  # Budget hit (inconclusive)
    return False, nodes_visited


def count_c8_capped(masks, cap=50):
    """Count C8 cycles up to a cap using fast bitmask DFS for smooth hill-climbing."""
    n = len(masks)
    count = 0

    for start in range(n - 7):
        allowed = ((1 << n) - 1) ^ ((1 << start) - 1)
        start_nbrs = masks[start] & allowed
        if start_nbrs.bit_count() < 2:
            continue

        # Meet-in-the-middle for C8: paths of length 4 from start!
        # Map: end_vertex -> list of internal_mask (3 internal vertices, bitmask)
        by_end = {}

        def gen4(curr, depth, vis, first_v):
            if depth == 4:
                lst = by_end.get(curr)
                if lst is None:
                    by_end[curr] = [(vis, first_v)]
                else:
                    lst.append((vis, first_v))
                return
            cand = masks[curr] & allowed & ~vis
            while cand:
                lsb = cand & -cand
                nxt = lsb.bit_length() - 1
                cand ^= lsb
                gen4(nxt, depth + 1, vis | lsb, first_v)

        nb = start_nbrs
        start_bit = 1 << start
        while nb:
            lsb = nb & -nb
            v1 = lsb.bit_length() - 1
            nb ^= lsb
            gen4(v1, 1, start_bit | lsb, v1)

        for mid, plist in by_end.items():
            m = len(plist)
            if m < 2:
                continue
            shared_bits = start_bit | (1 << mid)
            for i in range(m):
                vi, fi = plist[i]
                vi_int = vi ^ shared_bits
                for j in range(i + 1, m):
                    vj, fj = plist[j]
                    if (vi_int & vj) == 0:
                        count += 1
                        if count >= cap:
                            return count
    return count


def random_regular_or_mixed_graph(n, degree_seq, rng):
    """Generate a simple graph with exact degree sequence via configuration model + restarts."""
    for _ in range(500):
        stubs = []
        for v, d in enumerate(degree_seq):
            stubs.extend([v] * d)
        rng.shuffle(stubs)
        adj = [set() for _ in range(n)]
        ok = True
        for i in range(0, len(stubs), 2):
            u, v = stubs[i], stubs[i + 1]
            if u == v or v in adj[u]:
                ok = False
                break
            adj[u].add(v)
            adj[v].add(u)
        if ok:
            return adj_to_masks(adj)
    raise RuntimeError("Failed to sample simple graph")


def double_edge_swap(masks, rng):
    """Degree-preserving 2-switch (u-v, x-y) -> (u-x, v-y) or (u-y, v-x)."""
    n = len(masks)
    for _ in range(40):
        u = rng.randrange(n)
        mu = masks[u]
        if not mu:
            continue
        # Pick random neighbor v of u
        v_choices = [i for i in range(n) if (mu >> i) & 1]
        v = rng.choice(v_choices)

        x = rng.randrange(n)
        if x == u or x == v:
            continue
        mx = masks[x]
        y_choices = [i for i in range(n) if (mx >> i) & 1 and i != u and i != v]
        if not y_choices:
            continue
        y = rng.choice(y_choices)

        # Try (u-x, v-y)
        if not ((masks[u] >> x) & 1) and not ((masks[v] >> y) & 1):
            new_masks = masks[:]
            new_masks[u] = (new_masks[u] ^ (1 << v)) | (1 << x)
            new_masks[v] = (new_masks[v] ^ (1 << u)) | (1 << y)
            new_masks[x] = (new_masks[x] ^ (1 << y)) | (1 << u)
            new_masks[y] = (new_masks[y] ^ (1 << x)) | (1 << v)
            return new_masks
    return None


def independent_verify(masks, n):
    """Zero-Hallucination Gate: independently check graph validity, min degree, and 2^k cycles."""
    assert len(masks) == n
    min_deg = n
    max_deg = 0
    edge_count = 0
    for u in range(n):
        assert not ((masks[u] >> u) & 1), "Self-loop detected!"
        d = masks[u].bit_count()
        min_deg = min(min_deg, d)
        max_deg = max(max_deg, d)
        edge_count += d
        for v in range(n):
            if (masks[u] >> v) & 1:
                assert (masks[v] >> u) & 1, "Asymmetric adjacency!"
    edge_count //= 2

    res = {
        "n": n,
        "edges": edge_count,
        "min_deg": min_deg,
        "max_deg": max_deg,
        "valid_min_deg_3": min_deg >= 3,
        "cycles": {},
    }
    length = 4
    while length <= n:
        if length == 4:
            c4 = count_c4_fast(masks)
            res["cycles"]["C4"] = {"exists": c4 > 0, "count": c4}
        elif length == 8:
            c8 = count_c8_capped(masks, cap=1000)
            res["cycles"]["C8"] = {"exists": c8 > 0, "count_capped": c8}
        else:
            # Generous exact budget for C16 / C32 verification
            has_c, visited = has_cycle_of_length(masks, length, max_nodes_visit=500000)
            res["cycles"][f"C{length}"] = {"exists": has_c, "dfs_nodes": visited}
        length *= 2
    return res


def run_search(n, degree_seq, time_budget_sec, target_c4_c8_zero=True, check_c16=False, seed=42):
    rng = random.Random(seed)
    t0 = time.perf_counter()

    best_masks = None
    best_score = 10**9
    best_detail = None
    evals = 0
    restarts = 0

    while time.perf_counter() - t0 < time_budget_sec:
        restarts += 1
        curr = random_regular_or_mixed_graph(n, degree_seq, rng)
        c4 = count_c4_fast(curr)
        c8 = count_c8_capped(curr, cap=40) if c4 <= 2 else 40
        c16_pen = 0
        if check_c16 and c4 == 0 and c8 == 0:
            has16, _ = has_cycle_of_length(curr, 16, max_nodes_visit=15000)
            c16_pen = 1 if has16 is not False else 0
        curr_score = c4 * 100 + c8 * 2 + c16_pen
        evals += 1

        if curr_score < best_score:
            best_score = curr_score
            best_masks = curr[:]
            best_detail = (c4, c8, c16_pen)

        # Simulated Annealing / Steepest Local Search with Stagnation Restart
        temp = 3.5
        stagnation = 0
        while stagnation < 350 and (time.perf_counter() - t0 < time_budget_sec):
            cand = double_edge_swap(curr, rng)
            if cand is None:
                continue
            evals += 1
            nc4 = count_c4_fast(cand)
            if nc4 <= 2:
                nc8 = count_c8_capped(cand, cap=40)
            else:
                nc8 = 40
            nc16 = 0
            if check_c16 and nc4 == 0 and nc8 == 0:
                has16, _ = has_cycle_of_length(cand, 16, max_nodes_visit=15000)
                nc16 = 1 if has16 is not False else 0

            cand_score = nc4 * 100 + nc8 * 2 + nc16
            delta = cand_score - curr_score
            if delta <= 0 or (temp > 0.05 and rng.random() < math.exp(-delta / temp)):
                curr = cand
                curr_score = cand_score
                c4, c8, c16_pen = nc4, nc8, nc16
                if cand_score < best_score:
                    best_score = cand_score
                    best_masks = cand[:]
                    best_detail = (nc4, nc8, nc16)
                    stagnation = 0
                    if target_c4_c8_zero and not check_c16 and nc4 == 0 and nc8 == 0:
                        return best_masks, best_score, best_detail, evals, restarts, time.perf_counter() - t0
                    if check_c16 and nc4 == 0 and nc8 == 0 and nc16 == 0:
                        return best_masks, best_score, best_detail, evals, restarts, time.perf_counter() - t0
                else:
                    stagnation += 1
            else:
                stagnation += 1
            temp *= 0.992

    return best_masks, best_score, best_detail, evals, restarts, time.perf_counter() - t0


def main():
    out_dir = Path(r"C:\Users\Kerem\.gemini\antigravity\scratch\erdos-hunter\pilot_results")
    out_dir.mkdir(parents=True, exist_ok=True)

    print("=== FAZ 1: ÖN-KALİBRASYON KAPISI (n=24 Kübik — Markström Sınıfı: C4=0 ve C8=0) ===")
    print("Stop-Loss Kotası: 20 saniye | API Çağrısı: 0")
    cal_masks, cal_score, cal_detail, cal_evals, cal_restarts, cal_time = run_search(
        n=24,
        degree_seq=[3] * 24,
        time_budget_sec=20.0,
        target_c4_c8_zero=True,
        check_c16=False,
        seed=2026,
    )
    cal_verify = independent_verify(cal_masks, 24)
    print(f"Süre: {cal_time:.2f}s | Değerlendirme: {cal_evals:,} ({cal_evals/max(cal_time,1e-6):.0f}/sn) | Restart: {cal_restarts}")
    print(f"En İyi Skor: {cal_score} | Detay (C4, C8, C16): {cal_detail}")
    print(f"Bağımsız Doğrulama: {json.dumps(cal_verify, indent=2)}")

    cal_passed = (not cal_verify["cycles"]["C4"]["exists"]) and (not cal_verify["cycles"]["C8"]["exists"])
    print(f"--> KALİBRASYON KAPISI: {'GEÇTİ (Markström sınıfı sıfırdan keşfedildi!)' if cal_passed else 'BAŞARISIZ (Sınır taraması iptal)'}")

    report = {
        "calibration_n24": {
            "passed": cal_passed,
            "time_sec": round(cal_time, 3),
            "evals": cal_evals,
            "evals_per_sec": round(cal_evals / max(cal_time, 1e-6), 1),
            "restarts": cal_restarts,
            "verification": cal_verify,
            "masks": cal_masks,
        }
    }

    if cal_passed:
        print("\n=== FAZ 2: KEŞFEDİLMEMİŞ SINIR YOKLAMASI (n=42 Karma Dereceli {3,4} — n<=40 Genel Sınırı Ötesi) ===")
        print("Stop-Loss Kotası: 35 saniye | API Çağrısı: 0")
        # 38 vertices of degree 3 + 4 vertices of degree 4 (non-cubic, min degree 3!)
        deg_42 = [3] * 38 + [4] * 4
        f_masks, f_score, f_detail, f_evals, f_restarts, f_time = run_search(
            n=42,
            degree_seq=deg_42,
            time_budget_sec=35.0,
            target_c4_c8_zero=True,
            check_c16=True,
            seed=42026,
        )
        f_verify = independent_verify(f_masks, 42)
        print(f"Süre: {f_time:.2f}s | Değerlendirme: {f_evals:,} ({f_evals/max(f_time,1e-6):.0f}/sn) | Restart: {f_restarts}")
        print(f"En İyi Skor: {f_score} | Detay (C4, C8, C16_flag): {f_detail}")
        print(f"Bağımsız Doğrulama: {json.dumps(f_verify, indent=2)}")

        report["frontier_n42_mixed"] = {
            "time_sec": round(f_time, 3),
            "evals": f_evals,
            "evals_per_sec": round(f_evals / max(f_time, 1e-6), 1),
            "restarts": f_restarts,
            "verification": f_verify,
            "masks": f_masks,
        }

    report_path = out_dir / "pilot_erdos64_report.json"
    report_path.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(f"\nRapor kaydedildi: {report_path}")


if __name__ == "__main__":
    main()
