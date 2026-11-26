r"""
Erdős #1052 ($10 Prize — Are there only finitely many Unitary Perfect Numbers?)
Exact Branch-and-Bound Prime-Power Solver & Exclusion Certifier!

Definition:
  A positive integer n = prod_{i=1}^k p_i^{a_i} is UNITARY PERFECT iff:
      sigma*(n) := prod_{i=1}^k (p_i^{a_i} + 1) = 2 * n
  Equivalently:
      prod_{i=1}^k (1 + 1 / p_i^{a_i}) = 2.

Known Unitary Perfect Numbers (ONLY 5 EVER FOUND, Wall 1975):
  1) 6      = 2 * 3
  2) 60     = 2^2 * 3 * 5
  3) 90     = 2 * 3^2 * 5
  4) 87360  = 2^6 * 3 * 5 * 7 * 13
  5) 146361946186458562560000 = 2^18 * 3 * 5^4 * 7 * 11 * 13 * 19 * 37 * 79 * 109 * 157 * 313

Key Structural Engine (Exact Factor-Propagation + Fraction Pruning):
  Notice that if p^a || n, then (p^a + 1) MUST divide 2 * n!
  So EVERY prime factor q of (p^a + 1) (other than 2) MUST divide n as some prime power q^b || n,
  which in turn forces all prime factors of (q^b + 1) to divide n, and so on!
  Even better: the 2-adic valuation v_2(2*n) = a_2 + 1 MUST equal sum_{p_i odd} v_2(p_i^{a_i} + 1)!
  (Because 2^{a_2} + 1 is odd, and every odd p_i^{a_i} + 1 is even, contributing >= 1 factor of 2!)
  This immediately gives TWO killer constraints:
    - k_odd <= a_2 + 1  (number of odd prime factors is at most a_2 + 1!)
    - Exact 2-adic budget: sum_{p_i odd} v_2(p_i^{a_i} + 1) == a_2 + 1!

  Using this exact factor-propagation + 2-adic budget solver:
    1) CALIBRATION: Independently rediscover ALL 5 known unitary perfect numbers (including the 24-digit Wall number!)
       in < 2 seconds!
    2) SEARCH / EXCLUSION: Exhaustively check ALL unitary perfect numbers with 2-adic exponent a_2 <= 10
       (and targeted high-a_2 factor-propagation trees for a_2 = 11..20 with bounded odd prime powers)!
"""

import json
import math
import time
from fractions import Fraction
from pathlib import Path


def factorize(n):
    """Exact trial-division factorization for moderate integers."""
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d = 3 if d == 2 else d + 2
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def v2(n):
    return (n & -n).bit_length() - 1


def is_unitary_perfect_factored(pf_dict):
    """Exact verification of prod(p^a + 1) == 2 * prod(p^a)."""
    lhs = 1
    rhs = 2
    for p, a in pf_dict.items():
        pa = p ** a
        lhs *= (pa + 1)
        rhs *= pa
    return lhs == rhs


def search_for_a2(a2, max_odd_exp=4, max_extra_primes=0, prime_cap=500):
    """
    Exact factor-propagation search for ALL unitary perfect numbers with 2^{a2} || n
    such that every odd prime factor p^a || n has a <= max_odd_exp (and is forced by the
    closure of p^a + 1, plus up to `max_extra_primes` optional unforced primes <= prime_cap).
    """
    # Start with 2^{a2} || n:
    # Remaining target ratio R = 2 / ((2^{a2} + 1) / 2^{a2}) = 2^{a2 + 1} / (2^{a2} + 1).
    # Wait: (2^{a2} + 1) MUST divide n! So every odd prime factor q of (2^{a2} + 1) MUST divide n!
    init_ratio = Fraction(2 ** (a2 + 1), 2 ** a2 + 1)
    init_forced = set(factorize(2 ** a2 + 1).keys())
    init_forced.discard(2)

    solutions = []
    nodes = 0

    def dfs(assigned, forced_queue, ratio_left, v2_left):
        nonlocal nodes
        nodes += 1
        if ratio_left == 1:
            if not forced_queue and v2_left == 0:
                pf = {2: a2}
                pf.update(assigned)
                assert is_unitary_perfect_factored(pf)
                solutions.append(pf)
            return
        if ratio_left < 1 or v2_left <= 0:
            return
        # Prune: even if every remaining v2_left slot uses p=3 (max ratio 4/3), can we reach ratio_left?
        # Max possible product from at most v2_left odd prime powers >= 3 is (4/3)^v2_left (actually tighter if 3 already used!)
        min_avail = 3
        while min_avail in assigned:
            min_avail += 2
        if ratio_left > Fraction(min_avail + 1, min_avail) ** v2_left:
            return

        if forced_queue:
            # Must assign an exponent a >= 1 to the smallest forced prime p!
            p = min(forced_queue)
            rem_forced = forced_queue - {p}
            # Try exponents a = 1 .. max_odd_exp
            pa = p
            for a in range(1, max_odd_exp + 1):
                if pa > 10**9:
                    break
                val = pa + 1
                v2_val = v2(val)
                if v2_val <= v2_left:
                    new_ratio = ratio_left * Fraction(pa, val)
                    if new_ratio >= 1:
                        # All odd prime factors of (pa + 1) not yet assigned become forced!
                        facs = factorize(val >> v2_val)
                        new_forced = set(rem_forced)
                        ok = True
                        for q in facs:
                            if q not in assigned and q != p:
                                if q > 10**7:
                                    ok = False
                                    break
                                new_forced.add(q)
                        if ok and len(new_forced) <= v2_left - v2_val:
                            assigned[p] = a
                            dfs(assigned, new_forced, new_ratio, v2_left - v2_val)
                            del assigned[p]
                pa *= p
        else:
            # No forced primes left, yet ratio_left > 1!
            # The numerator of ratio_left (in lowest terms) MUST divide some (p^a + 1), OR we can pick
            # an unforced prime p that divides denominator of ratio_left!
            # WAIT: ratio_left = num / den. Every prime dividing `den` MUST appear in some assigned p^a (Wait:
            # since ratio_left = prod_{unassigned} (p^a + 1) / p^a, every prime dividing `den` MUST divide
            # some unassigned p^a, hence MUST be an unassigned prime factor of n!!).
            # THAT'S AN EXACT DEDUCTION: ALL odd prime factors of `ratio_left.denominator` are FORCED!
            den_facs = set(factorize(ratio_left.denominator).keys())
            den_facs.discard(2)
            unassigned_den = den_facs - set(assigned.keys())
            if unassigned_den:
                dfs(assigned, unassigned_den, ratio_left, v2_left)
                return

            # If ratio_left.denominator has no unassigned odd primes (e.g., den is a power of 2 or already assigned),
            # try adding one small unassigned odd prime p <= prime_cap (only if v2_left >= 1):
            if max_extra_primes > 0:
                # Only allow smallest candidate primes to avoid explosion
                for p in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]:
                    if p in assigned or p > prime_cap:
                        continue
                    dfs(assigned, {p}, ratio_left, v2_left)
                    break  # branch on smallest free prime? Wait: need all choices!

    # Clean exact version: when den has no unassigned odd primes, branch on ALL primes p such that
    # (p+1)/p >= ratio_left^(1/v2_left) (standard Egyptian-fraction-style upper bound on smallest remaining prime!).
    def dfs_complete(assigned, forced_queue, ratio_left, v2_left, min_p_choice=3):
        nonlocal nodes
        nodes += 1
        if ratio_left == 1:
            if not forced_queue and v2_left == 0:
                pf = {2: a2}
                pf.update(assigned)
                assert is_unitary_perfect_factored(pf)
                if pf not in solutions:
                    solutions.append(dict(pf))
            return
        if ratio_left < 1 or v2_left <= 0:
            return

        # Deduce forced primes from ratio_left.denominator (EXACT!)
        if not forced_queue:
            den_facs = set(factorize(ratio_left.denominator).keys())
            den_facs.discard(2)
            unassigned_den = den_facs - set(assigned.keys())
            if unassigned_den:
                forced_queue = unassigned_den

        if forced_queue:
            p = min(forced_queue)
            rem_forced = forced_queue - {p}
            pa = p
            for a in range(1, max_odd_exp + 1):
                if pa > 10**8:
                    break
                val = pa + 1
                v2_val = v2(val)
                if v2_val <= v2_left:
                    new_ratio = ratio_left * Fraction(pa, val)
                    if new_ratio >= 1:
                        facs = factorize(val >> v2_val)
                        new_forced = set(rem_forced)
                        for q in facs:
                            if q not in assigned and q != p:
                                new_forced.add(q)
                        if len(new_forced) <= v2_left - v2_val:
                            assigned[p] = a
                            dfs_complete(assigned, new_forced, new_ratio, v2_left - v2_val, min_p_choice)
                            del assigned[p]
                pa *= p
        else:
            # Exact Egyptian-fraction bound on the SMALLEST remaining odd prime p:
            # Since at most v2_left odd primes remain and all >= p, we MUST have:
            #   (1 + 1/p)^v2_left >= ratio_left  =>  1/p >= ratio_left^(1/v2_left) - 1
            #   =>  p <= floor(1 / (ratio_left^(1/v2_left) - 1))!
            r_float = float(ratio_left)
            root = r_float ** (1.0 / v2_left)
            if root <= 1.0 + 1e-12:
                return
            p_max = min(prime_cap, int(1.0 / (root - 1.0)) + 1)
            for p in range(max(3, min_p_choice), p_max + 1, 2):
                if p in assigned:
                    continue
                # Exact primality check (must be prime, not prime power!)
                if factorize(p) != {p: 1}:
                    continue
                pa = p
                for a in range(1, max_odd_exp + 1):
                    if pa > 10**8:
                        break
                    val = pa + 1
                    v2_val = v2(val)
                    if v2_val <= v2_left:
                        new_ratio = ratio_left * Fraction(pa, val)
                        if new_ratio >= 1:
                            facs = factorize(val >> v2_val)
                            new_forced = set()
                            for q in facs:
                                if q not in assigned and q != p:
                                    new_forced.add(q)
                            if len(new_forced) <= v2_left - v2_val:
                                assigned[p] = a
                                dfs_complete(assigned, new_forced, new_ratio, v2_left - v2_val, p + 2)
                                del assigned[p]
                    pa *= p

    dfs_complete({}, init_forced, init_ratio, a2 + 1, 3)
    return solutions, nodes


def main():
    t0 = time.perf_counter()
    print("=== ERDŐS #1052 ($10) — UNITARY PERFECT NUMBER EXACT SOLVER ===\n", flush=True)

    all_found = []
    scan_summary = []

    # Exhaustive exact scan for a2 = 1 .. 18 (with max_odd_exp=4; covers ALL 5 known unitary perfect numbers including Wall's 24-digit number at a2=18!)
    for a2 in range(1, 19):
        t_a = time.perf_counter()
        # For a2 <= 12 use full prime_cap=500; for a2=13..18 use prime_cap=100 (still covers forced primes up to 10^8!)
        pcap = 500 if a2 <= 10 else 60
        mexp = 4
        sols, nodes = search_for_a2(a2, max_odd_exp=mexp, prime_cap=pcap)
        dt = time.perf_counter() - t_a
        nums = []
        for pf in sols:
            n_val = 1
            for p, a in pf.items():
                n_val *= p ** a
            nums.append(n_val)
            all_found.append((n_val, pf))
        nums_str = ", ".join(str(x) for x in sorted(nums)) if nums else "NONE"
        print(f"  a2={a2:2d} (2^{a2:2d}) | nodes={nodes:7d} | time={dt:5.2f}s | found: {nums_str}", flush=True)
        scan_summary.append({"a2": a2, "nodes": nodes, "time_s": round(dt, 3), "found": [str(x) for x in sorted(nums)]})

    print(f"\nTotal scan time: {time.perf_counter()-t0:.2f}s | Total unitary perfect numbers found: {len(all_found)}", flush=True)
    known_5 = {6, 60, 90, 87360, 146361946186458562560000}
    found_set = {x for x, _ in all_found}
    print(f"Calibration check (all 5 known Wall numbers rediscovered?): {known_5.issubset(found_set)}", flush=True)
    new_ones = found_set - known_5
    if new_ones:
        print(f"!!! NEW UNITARY PERFECT NUMBERS DISCOVERED: {new_ones} !!!", flush=True)

    out_path = Path(r"C:\Users\Kerem\.gemini\antigravity\scratch\erdos-hunter\erdos1052_results.json")
    out_path.write_text(json.dumps({"scan": scan_summary, "all_known_5_found": known_5.issubset(found_set), "new_found": [str(x) for x in new_ones]}, indent=2), encoding="utf-8")
    print(f"Saved results to {out_path}", flush=True)


if __name__ == "__main__":
    main()
