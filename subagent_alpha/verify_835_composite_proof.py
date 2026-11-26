import math

def jb(n, d, w):
    if n == 0 or w == 0:
        return 1
    if 2 * w < d:
        return 1
    return (n * jb(n - 1, d, w - 1)) // w

def is_prime(m):
    if m < 2: return False
    for d in range(2, int(m**0.5) + 1):
        if m % d == 0: return False
    return True

# Verify our exact proof for ALL composite k+1 in 3..500:
# For composite k+1, write k+1 = p^a * m where p is prime, a >= 1, p \nmid m.
# Case 1: m > 1 (at least two prime factors, or m > 1). Choose t = p^a <= (k+1)/2 <= k.
# Wait: check t = p^a vs t = p^{a-1} when m=1 (prime power a>=2)!
# If m = 1 and a >= 2: choose t = p^{a-1}. Notice 2 <= p^{a-1} <= (k+1)/p <= k.
# If m > 1: choose t = p^a (wait: if p=2, a=1, t=2 <= k).
# Verify in BOTH cases that p^a does NOT divide C(k+t, t) = C(p^a*m - 1 + t, t)!
for k in range(3, 501):
    if is_prime(k + 1):
        continue
    # factor out smallest prime power
    n = k + 1
    p = 2
    while n % p != 0:
        p += 1
    a = 0
    tmp = n
    while tmp % p == 0:
        tmp //= p
        a += 1
    m = tmp
    t = p**(a - 1) if m == 1 else p**a
    assert 2 <= t <= k
    # Check v_p(C(k+t, t)) < a!
    val = math.comb(k + t, t)
    vp = 0
    while val % p == 0:
        val //= p
        vp += 1
    assert vp < a, f"Failed at k={k}, p={p}, a={a}, m={m}, t={t}, vp={vp}"
    # Also check jb(2k, 4, k) * (k+1) < C(2k, k)
    assert jb(2 * k, 4, k) * (k + 1) < math.comb(2 * k, k)

print("Verified for ALL composite k+1 in [4..501]:")
print("1) v_p(C(k+t, t)) < v_p(k+1) at explicit t in [2, k], causing strict floor loss in Johnson bound.")
print("2) jb(2k, 4, k) * (k+1) < C(2k, k), hence chi(J(2k, k)) >= k + 2.")
