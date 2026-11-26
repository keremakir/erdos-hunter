import math, random
from itertools import combinations

# Part A: Why are there at most 2 mutually disjoint S(3,4,8) systems?
# Check A_8 orbits and parity of permutations mapping base S(3,4,8) to others!
base = frozenset(frozenset(c) for c in combinations(range(8), 4) if (c[0]^c[1]^c[2]^c[3]) == 0)

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

from itertools import permutations
sys_parity = {}
for p in permutations(range(8)):
    s = frozenset(frozenset(p[x] for x in b) for b in base)
    par = perm_parity(p)
    if s not in sys_parity:
        sys_parity[s] = set()
    sys_parity[s].add(par)

print("Unique S(3,4,8) systems:", len(sys_parity))
print("Parity sets appearing:", {tuple(sorted(v)) for v in sys_parity.values()})
systems = list(sys_parity.keys())
even_sys = [s for s in systems if 0 in sys_parity[s]]
odd_sys = [s for s in systems if 1 in sys_parity[s]]
print(f"Even orbit size: {len(even_sys)}, Odd orbit size: {len(odd_sys)}")

same_even_disj = sum(1 for i in range(len(even_sys)) for j in range(i+1, len(even_sys)) if not (even_sys[i] & even_sys[j]))
same_odd_disj = sum(1 for i in range(len(odd_sys)) for j in range(i+1, len(odd_sys)) if not (odd_sys[i] & odd_sys[j]))
cross_disj = sum(1 for a in even_sys for b in odd_sys if not (a & b))
print(f"Disjoint pairs within even: {same_even_disj}, within odd: {same_odd_disj}, across: {cross_disj}")

# Also compute chromatic number of J(8,4) directly or verify chi(J(8,4)) = 6!
# We know max indep set has size 14 (which is S(3,4,8)), wait: can a non-S(3,4,8) independent set exist of size 14?
# By our proof, any indep set of size 14 in J(8,4) MUST cover all 56 triples once, so it IS an S(3,4,8)!
# What about chi(J(8,4)) = 6? We can easily check if 5 independent sets can cover all 70 vertices:
# If 5 indep sets cover 70 vertices, each has size <= 14 -> all 5 MUST have size 14 -> all 5 MUST be pairwise disjoint S(3,4,8)!
# Since max pairwise disjoint S(3,4,8) is 2 (bipartite disjointness graph!), 5 is IMPOSSIBLE!
# Let's also check if 6 colors work explicitly on J(8,4) via Graham-Sloane or greedy!
verts84 = list(combinations(range(8), 4))
# Sum mod 6? No, sum mod 8 gives 8 colors. What about sum mod 7? If S1 \triangle S2 = {a,b}, a != b in 0..7, 0 and 7 are congruent mod 7!
# Wait: Brouwer's table says chi(J(8,4)) = 6! Let's find an explicit 6-coloring of J(8,4) (e.g. two disjoint S(3,4,8) + 4 other sets)!
s1 = even_sys[0]
s2 = next(s for s in odd_sys if not (s1 & s))
rem = [frozenset(v) for v in verts84 if frozenset(v) not in s1 and frozenset(v) not in s2]
print("Remaining vertices after removing 2 disjoint S(3,4,8):", len(rem))

# Part B: Construct S(5, 6, 12) (Small Witt Design W_12) and test disjoint pairs!
# Construction of S(5, 6, 12) via extended quadratic residue code over F_3 (or PSL(2, 11) on PG(1, 11) = F_11 U {inf})!
# Over F_11 U {inf}: Let Q = squares in F_11 = {0, 1, 3, 4, 5, 9} (size 6: 0 and nonzero squares 1,4,9,5,3!).
# Wait: in PG(1, 11), the 6-set B0 = {inf, 1, 3, 4, 5, 9} (Wait: check orbit of B0 under PSL(2, 11)!)
# Let's test B0 = {11, 1, 3, 4, 5, 9} (using 11 for inf) or {0, 1, 3, 4, 5, 9}?
# In PSL(2, 11), order is (11*10*12)/2 = 660. If stabilizer has order 5 (or 10 or 5?), 660/5 = 132!!
# Wait: let's test stabilizer of Q_nz = {1, 3, 4, 5, 9} U {11}:
# Wait: under x -> a*x + b (a in QR_11 = {1,3,4,5,9}, b in F_11): x -> x + 1? No, x -> a*x fixes 0 and inf.
# Let's check ALL 6-sets under PGL(2,11) or PSL(2,11) in Python!
def psl2_11_orbit(seed):
    # generators of PSL(2, 11) on {0..10, 11=inf}: x->x+1, x->4x (4=2^2), x->-1/x
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

for seed in [{11, 1, 3, 4, 5, 9}, {0, 1, 3, 4, 5, 9}, {11, 0, 2, 6, 7, 8}]:
    orb = psl2_11_orbit(seed)
    print(f"Seed {sorted(seed)} -> orbit size {len(orb)}")
    if len(orb) == 132:
        # check if it's an S(5, 6, 12)!
        quints = set()
        ok = True
        for b in orb:
            for q5 in combinations(b, 5):
                fq = frozenset(q5)
                if fq in quints:
                    ok = False
                    break
                quints.add(fq)
        print("  Is S(5,6,12)?", ok, "covered 5-sets:", len(quints))
        if ok:
            w12 = list(orb)
            # Check how many transpositions / random permutations give a disjoint W_12!
            w12_set = set(w12)
            # Check all elements of S_12? Wait: PGL(2,11) \ PSL(2,11) has coset x -> -x (or x -> 2x)!
            # What does x -> 2x do to w12?
            w12_neg = {frozenset((2*x)%11 if x!=11 else 11 for x in b) for b in w12}
            print("  Intersection with x->2x image:", len(w12_set & w12_neg))
            # Search random permutations for disjoint copies of W_12!
            # Wait: 5040 copies total; prob of hitting a disjoint one randomly is tiny? Let's check!
            # Actually let's check all transpositions/3-cycles/involutions or check Kramer-Magliveras!
            hits = set()
            for a, b in combinations(range(12), 2):
                p = list(range(12)); p[a], p[b] = p[b], p[a]
                img = frozenset(frozenset(p[x] for x in blk) for blk in w12)
                hits.add(len(w12_set & img))
            print("  Transposition intersections:", sorted(hits))
            break
