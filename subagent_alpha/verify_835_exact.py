import math
from fractions import Fraction
from itertools import combinations
import numpy as np
from scipy.optimize import linprog

def jb(n, d, w):
    if n == 0 or w == 0:
        return 1
    if 2 * w < d:
        return 1
    return (n * jb(n - 1, d, w - 1)) // w

def eberlein(n, k, i, j):
    total = 0
    for s in range(i + 1):
        if s <= j and i - s <= k - j and i - s <= n - k - j:
            total += ((-1) ** s) * math.comb(j, s) * math.comb(k - j, i - s) * math.comb(n - k - j, i - s)
    return total

def is_prime(m):
    if m < 2: return False
    for d in range(2, int(m**0.5) + 1):
        if m % d == 0: return False
    return True

print("=== 1. Johnson bound vs C_k for k=3..200 ===")
anomalies = []
for k in range(3, 201):
    C_k = math.comb(2 * k, k) // (k + 1) if math.comb(2 * k, k) % (k + 1) == 0 else None
    jval = jb(2 * k, 4, k)
    p = is_prime(k + 1)
    if p:
        assert jval * (k + 1) == math.comb(2 * k, k), f"Prime mismatch at k={k}"
    else:
        if jval * (k + 1) >= math.comb(2 * k, k):
            anomalies.append((k, jval, math.comb(2 * k, k)))
print("Composite k+1 where jb(2k,4,k)*(k+1) >= C(2k,k) for k in 3..200:", anomalies)

print("\n=== 2. Exact Rational Verification of Delsarte LP for even k=4..18 ===")
# For even k, a hypothetical Steiner system S(k-1, k, 2k) has inner distribution:
# a_i = n_{k-i} for i=2..k (since Johnson distance i means |A cap B| = k - i).
# Note: n_0 = 1 -> a_k = 1; n_1 = 0 -> a_{k-1} = 0.
# Let's compute exact a_i from Mendelsohn equations and verify ALL Delsarte inequalities sum_i a_i P_i(j)/v_i >= 0!
for k in [4, 6, 8, 10, 12, 14, 16, 18]:
    n = 2 * k
    v_total = math.comb(n, k)
    v = [math.comb(k, i) * math.comb(n - k, i) for i in range(k + 1)]
    # Solve Mendelsohn for n_0..n_{k-2}
    lam = [Fraction(math.comb(n - r, k - 1 - r), math.comb(k - r, k - 1 - r)) for r in range(k)]
    nj = [Fraction(0)] * (k - 1)
    for r in range(k - 2, -1, -1):
        rhs = math.comb(k, r) * (lam[r] - 1)
        for s in range(r + 1, k - 1):
            rhs -= math.comb(s, r) * nj[s]
        nj[r] = rhs
    a = [Fraction(1)] + [Fraction(0)] + [nj[k - i] for i in range(2, k + 1)]
    assert sum(a) == Fraction(v_total, k + 1)
    # Check primal LP feasibility: Q_j(a) >= 0 for j=1..k
    q_vals = []
    for j in range(1, k + 1):
        s = sum(a[i] * Fraction(eberlein(n, k, i, j), v[i]) for i in range(k + 1))
        q_vals.append(s)
    # Also check Hoffman dual polynomial!
    # Dual LP: min 1 + sum_{j=1}^k y_j s.t. y_j >= 0, sum_{j=1}^k y_j (P_i(j)/v_i) <= -1 for i=2..k?
    # Wait: Primal max 1 + sum_{i>=2} a_i s.t. sum_{i>=2} (-P_i(j)/v_i) a_i <= 1.
    # Dual: min sum_{j=1}^k y_j + 1 s.t. y_j >= 0, sum_{j=1}^k (-P_i(j)/v_i) y_j >= 1 for i=2..k.
    # Let's check Hoffman dual: only y_k > 0!
    # Specifically, P_i(k) = sum_s (-1)^s C(k,s) C(0, i-s) C(0, i-s) = (-1)^i C(k, i) for i=0..k.
    #Wait! For i=1: P_1(k) = -k, v_1 = k^2, so -P_1(k)/v_1 = 1/k.
    # What if we check dual LP with scipy or exact y_k = ?
    # If y_k = C_k - 1, wait: for i >= 2, (-1)^(i+1) C(k, i) / (C(k,i)^2) = (-1)^(i+1) / C(k, i) can be negative for odd i!
    # So Hoffman alone doesn't give dual >= 1 for i>=2; a multi-eigenspace dual polynomial is needed!
    # Let's solve dual LP with exact check or inspect q_vals:
    zero_j = [j for j, val in enumerate(q_vals, 1) if val == 0]
    neg_j = [j for j, val in enumerate(q_vals, 1) if val < 0]
    print(f"k={k:2d}: sum(a)=C_k={sum(a)}, min_q={min(q_vals)}, neg_j={neg_j}, tight_j={zero_j}")

print("\n=== 3. Exact computation on J(8,4) and S(3,4,8) ===")
verts = list(combinations(range(8), 4))
v_idx = {v: i for i, v in enumerate(verts)}
# Generate all S(3,4,8) by finding 14-element independent sets of J(8,4) or using all 8!/|AGL(3,2)| = 40320/1344 = 30 systems!
# Actually S(3,4,8) is unique up to isomorphism with group AGL(3,2) of order 8*168 = 1344, so there are 8!/1344 = 30 systems!
# Let's construct the canonical S(3,4,8) = affine planes in F_2^3 (points 0..7 as 3-bit vectors, 4-subsets with XOR sum = 0)!
base_blocks = []
for c in combinations(range(8), 4):
    if (c[0] ^ c[1] ^ c[2] ^ c[3]) == 0:
        base_blocks.append(frozenset(c))
print("Base S(3,4,8) size:", len(base_blocks))
# Verify it's an S(3,4,8):
triples_covered = set()
for b in base_blocks:
    for t in combinations(b, 3):
        triples_covered.add(frozenset(t))
assert len(triples_covered) == math.comb(8, 3) == 56

# Generate all distinct S(3,4,8) under S_8
from itertools import permutations
all_s348 = set()
for perm in permutations(range(8)):
    # speed up: just build frozenset of blocks
    sys_blocks = frozenset(frozenset(perm[x] for x in b) for b in base_blocks)
    all_s348.add(sys_blocks)
all_s348 = list(all_s348)
print("Total distinct S(3,4,8) on 8 points:", len(all_s348))

# Compute pairwise intersection sizes between distinct S(3,4,8) systems!
inter_counts = {}
disjoint_pairs = 0
for i in range(len(all_s348)):
    for j in range(i + 1, len(all_s348)):
        inter = len(all_s348[i] & all_s348[j])
        inter_counts[inter] = inter_counts.get(inter, 0) + 1
        if inter == 0:
            disjoint_pairs += 1
print("Pairwise intersections among the 30 S(3,4,8) systems:", sorted(inter_counts.items()))
# Build disjointness graph on the 30 systems and find max clique!
adj = {i: set() for i in range(len(all_s348))}
for i in range(len(all_s348)):
    for j in range(i + 1, len(all_s348)):
        if not (all_s348[i] & all_s348[j]):
            adj[i].add(j)
            adj[j].add(i)
print("Degrees in disjointness graph of S(3,4,8):", set(len(adj[i]) for i in adj))
# Check max clique (max pairwise disjoint S(3,4,8)s)
max_disjoint = 1
for i in adj:
    for j in adj[i]:
        max_disjoint = max(max_disjoint, 2)
        common = adj[i] & adj[j]
        if common:
            max_disjoint = max(max_disjoint, 3)
print("Max pairwise disjoint S(3,4,8) systems:", max_disjoint)
