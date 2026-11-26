import math
from fractions import Fraction
from analyze_552_polarity import build_ER

def jb(n, d, w):
    if n == 0 or w == 0: return 1
    if 2*w < d: return 1
    return (n * jb(n-1, d, w-1)) // w

def is_prime(m):
    if m < 2: return False
    for d in range(2, int(m**0.5)+1):
        if m % d == 0: return False
    return True

print("=== 835 SUMMARY TABLE ===")
for k in range(3, 19):
    C_binom = math.comb(2*k, k)
    jval = jb(2*k, 4, k)
    p = is_prime(k + 1)
    ck = Fraction(C_binom, k + 1)
    lb_jb = math.ceil(C_binom / jval)
    print(f"k={k:2d} | k+1={k+1:2d} ({'PRIME' if p else 'comp ':5s}) | C(2k,k)={C_binom:11d} | jb={jval:9d} | C(2k,k)/(k+1)={str(ck):12s} | ceil(C/jb)={lb_jb:2d}")

print("\n=== 552 EML CHECK FOR HoG 53036 (N=34, d=6) AND HoG 56941 (N=35, d=6) IN ER(q) ===")
for Np in [34, 35]:
    vals = []
    for q in [7, 8, 9, 11, 13, 16, 17, 19, 23]:
        N = q*q + q + 1
        min_abs = max(0, Np - (N - (q + 1)))
        ub = ((q + 1) * Np * Np / N + math.sqrt(q) * Np * (1 - Np / N) - min_abs) / Np
        vals.append((q, round(ub, 4)))
    print(f"N'={Np}: max EML avg deg in ER(q) = {vals}")

print("\n=== 552 EML FOR ER(11) AT N'=82 (f(73)=83 check) ===")
q = 11; N = 133; Np = 82
ub = ((q + 1) * Np * Np / N + math.sqrt(q) * Np * (1 - Np / N)) / Np
print(f"ER(11) at N'=82: ub_EML = {ub:.4f} < 9")
