# Check ALL 5040 copies of W_12 = S(5, 6, 12) and their disjointness graph!
from itertools import combinations
import random

def psl2_11_orbit(seed):
    def act_add(x): return 11 if x == 11 else (x + 1) % 11
    def act_mul(x): return 11 if x == 11 else (4 * x) % 11
    def act_inv(x):
        if x == 11: return 0
        if x == 0: return 11
        return (-pow(x, -1, 11)) % 11
    orbit = {frozenset(seed)}
    queue = [frozenset(seed)]
    while queue:
        cur = queue.pop()
        for fn in (act_add, act_mul, act_inv):
            nxt = frozenset(fn(x) for x in cur)
            if nxt not in orbit:
                orbit.add(nxt)
                queue.append(nxt)
    return orbit

w0 = psl2_11_orbit({11, 1, 3, 4, 5, 9})
assert len(w0) == 132

# Notice: any permutation of {0..11} that fixes {0,1,2,3,4} setwise and sends blocks?
# Actually M_12 is 5-transitive! So every W_12 is determined by a bijection of 12 points up to M_12.
# Wait: since M_12 is sharply 5-transitive! Order of M_12 = 12*11*10*9*8 = 95040!
# That means for ANY ordered 5-tuple (a0,a1,a2,a3,a4), there is a UNIQUE element of M_12 sending (0,1,2,3,4) to it!
# Therefore, the 5040 cosets of M_12 in S_12 are in 1-1 correspondence with permutations of the remaining 7 elements {5,6,7,8,9,10,11}!!
# WAIT A SECOND! IS THAT TRUE?!
# YES!! Because M_12 is sharply 5-transitive on 12 points, S_12 = (S_7 fixing 0..4) * M_12!!
# Wait: 7! = 5040!! EXACTLY 5040!!
# AND the parity of a permutation in S_7 fixing 0..4 is JUST its parity in S_7!
# Since M_12 <= A_12, the even cosets are EXACTLY A_7 (2520) and the odd cosets are S_7 \ A_7 (2520)!!

from itertools import permutations

def perm_parity(p):
    seen = [False]*len(p)
    cyc = 0
    for i in range(len(p)):
        if not seen[i]:
            cyc += 1
            j = i
            while not seen[j]:
                seen[j] = True
                j = p[j]
    return (len(p) - cyc) % 2

# Let's represent each W_12 as a bitmask or frozenset of block IDs!
all_6sets = list(combinations(range(12), 6))
idx6 = {frozenset(s): i for i, s in enumerate(all_6sets)}
w0_bits = 0
for b in w0:
    w0_bits |= (1 << idx6[b])

w0_blocks = [tuple(b) for b in w0]

# Enumerate all 5040 images under S_7 acting on {5..11} (Wait: check if S_7 fixing 0..4 really gives 5040 distinct W_12s!)
# To be fast, map 0..4 to 0..4 and 5..11 to perm of 5..11!
even_masks = []
odd_masks = []
seen_masks = set()

for p7 in permutations(range(5, 12)):
    perm = (0, 1, 2, 3, 4) + p7
    m = 0
    for b in w0_blocks:
        nb = frozenset((perm[b[0]], perm[b[1]], perm[b[2]], perm[b[3]], perm[b[4]], perm[b[5]]))
        m |= (1 << idx6[nb])
    if m not in seen_masks:
        seen_masks.add(m)
        if perm_parity(perm) == 0:
            even_masks.append(m)
        else:
            odd_masks.append(m)

print(f"Distinct W_12 found: {len(seen_masks)} (even={len(even_masks)}, odd={len(odd_masks)})")

# Check how many even_masks are disjoint from w0_bits, and how many odd_masks are disjoint from w0_bits!
# Notice by symmetry of M_12 acting on W_12s, w0 is representative of even_masks!
even_disj_from_w0 = [i for i, m in enumerate(even_masks) if (m & w0_bits) == 0]
odd_disj_from_w0 = [i for i, m in enumerate(odd_masks) if (m & w0_bits) == 0]
print(f"Disjoint from w0 in SAME (even) orbit: {len(even_disj_from_w0)}")
print(f"Disjoint from w0 in OPPOSITE (odd) orbit: {len(odd_disj_from_w0)}")

# Check intersection sizes with w0!
inter_even = {}
for m in even_masks:
    c = (m & w0_bits).bit_count()
    inter_even[c] = inter_even.get(c, 0) + 1
inter_odd = {}
for m in odd_masks:
    c = (m & w0_bits).bit_count()
    inter_odd[c] = inter_odd.get(c, 0) + 1
print("Intersection sizes with w0 (even):", sorted(inter_even.items()))
print("Intersection sizes with w0 (odd):", sorted(inter_odd.items()))

# Now check if ANY pair among odd_disj_from_w0 (or even_disj_from_w0) are disjoint!
candidates = [even_masks[i] for i in even_disj_from_w0] + [odd_masks[i] for i in odd_disj_from_w0]
print("Total W_12 disjoint from w0:", len(candidates))
pair_disj = 0
for i in range(len(candidates)):
    for j in range(i + 1, len(candidates)):
        if (candidates[i] & candidates[j]) == 0:
            pair_disj += 1
print("Number of triangles containing w0 in disjointness graph:", pair_disj)
