import math, random
from fractions import Fraction

# Analyze Erdos-Renyi polarity graphs ER(q) over F_q for prime powers q!
def build_gf(q):
    # Return addition table, multiplication table for GF(q)
    # Prime or prime power: let's support prime p and p^2, p^3, 2^k cleanly
    # Factor q = p^k
    for p in range(2, q + 1):
        if q % p == 0:
            tmp = q
            k = 0
            while tmp % p == 0:
                tmp //= p
                k += 1
            if tmp == 1:
                break
    if k == 1:
        elems = list(range(p))
        add = [[(a + b) % p for b in elems] for a in elems]
        mul = [[(a * b) % p for b in elems] for a in elems]
        return elems, add, mul
    # Irreducible polynomial over F_p of degree k
    # Represent elements as integers 0..p^k-1 (base p coeffs)
    def poly_mul(a, b, mod_poly):
        # a, b lists of coeffs
        res = [0] * (len(a) + len(b) - 1)
        for i, ca in enumerate(a):
            for j, cb in enumerate(b):
                res[i + j] = (res[i + j] + ca * cb) % p
        # reduce mod mod_poly
        while len(res) >= len(mod_poly):
            c = res[-1]
            if c != 0:
                shift = len(res) - len(mod_poly)
                for i in range(len(mod_poly)):
                    res[shift + i] = (res[shift + i] - c * mod_poly[i]) % p
            res.pop()
        while len(res) < k:
            res.append(0)
        return res
    def int_to_poly(x):
        r = []
        for _ in range(k):
            r.append(x % p)
            x //= p
        return r
    def poly_to_int(poly):
        val = 0
        for c in reversed(poly):
            val = val * p + (c % p)
        return val
    # Find irreducible polynomial of degree k
    # A polynomial of degree k is irreducible iff it has no root in F_{p^m} for 1 <= m <= k//2; for k<=4, just check irreducibility by trial division!
    def is_irred(mp):
        # check no divisor of deg 1..k//2
        for d in range(1, k // 2 + 1):
            for divisor_int in range(p**d, 2 * p**d):
                div = []
                x = divisor_int
                for _ in range(d + 1):
                    div.append(x % p); x //= p
                # polynomial mod mp % div
                rem = list(mp)
                while len(rem) >= len(div):
                    if rem[-1] != 0:
                        inv = pow(div[-1], -1, p)
                        coef = (rem[-1] * inv) % p
                        sh = len(rem) - len(div)
                        for i in range(len(div)):
                            rem[sh + i] = (rem[sh + i] - coef * div[i]) % p
                    rem.pop()
                if all(c == 0 for c in rem):
                    return False
        return True
    mod_poly = None
    for tail in range(p**k):
        mp = int_to_poly(tail) + [1]
        if is_irred(mp):
            mod_poly = mp
            break
    assert mod_poly is not None
    elems = list(range(q))
    polys = [int_to_poly(i) for i in elems]
    add = [[poly_to_int([(polys[a][i] + polys[b][i]) % p for i in range(k)]) for b in elems] for a in elems]
    mul = [[poly_to_int(poly_mul(polys[a], polys[b], mod_poly)) for b in elems] for a in elems]
    return elems, add, mul

def build_ER(q):
    elems, add, mul = build_gf(q)
    # Canonical projective points (x, y, z) where last nonzero coord is 1
    pts = []
    # (x, y, 1)
    for x in elems:
        for y in elems:
            pts.append((x, y, 1))
    # (x, 1, 0)
    for x in elems:
        pts.append((x, 1, 0))
    # (1, 0, 0)
    pts.append((1, 0, 0))
    N = len(pts)
    assert N == q*q + q + 1
    adj = [set() for _ in range(N)]
    is_abs = [False] * N
    for i in range(N):
        x1, y1, z1 = pts[i]
        # dot with self
        dself = add[add[mul[x1][x1]][mul[y1][y1]]][mul[z1][z1]]
        if dself == 0:
            is_abs[i] = True
        for j in range(i + 1, N):
            x2, y2, z2 = pts[j]
            dot = add[add[mul[x1][x2]][mul[y1][y2]]][mul[z1][z2]]
            if dot == 0:
                adj[i].add(j)
                adj[j].add(i)
    return pts, adj, is_abs

def verify_c4_free(adj):
    N = len(adj)
    for u in range(N):
        seen = set()
        for w in adj[u]:
            for v in adj[w]:
                if v > u:
                    if v in seen:
                        return False
                    seen.add(v)
    return True

for q in [2, 3, 4, 5, 7, 8, 9, 11]:
    pts, adj, is_abs = build_ER(q)
    degs = [len(adj[i]) for i in range(len(pts))]
    abs_degs = {degs[i] for i in range(len(pts)) if is_abs[i]}
    nonabs_degs = {degs[i] for i in range(len(pts)) if not is_abs[i]}
    ok = verify_c4_free(adj) if q <= 9 else "skipped"
    print(f"ER({q:2d}): N={len(pts):3d}, C4-free={ok}, #abs={sum(is_abs)}, abs_deg={abs_degs}, nonabs_deg={nonabs_degs}")
