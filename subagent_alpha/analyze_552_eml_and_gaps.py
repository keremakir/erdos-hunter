import math
import numpy as np
from analyze_552_polarity import build_ER

# 1. Exact spectrum of ER(q) and exact upper bound on e(S) for ANY induced subgraph S <= ER(q) of size N' = N - s!
for q in [5, 7, 8, 9, 11]:
    pts, adj, is_abs = build_ER(q)
    N = len(pts)
    A = np.zeros((N, N), dtype=float)
    for u in range(N):
        for v in adj[u]:
            A[u, v] = 1.0
    # Also A_loop with +1 on diagonal for absolute points (since v \perp v!)
    A_loop = A.copy()
    for u in range(N):
        if is_abs[u]:
            A_loop[u, u] = 1.0
    eigs = np.linalg.eigvalsh(A)
    eigs_loop = np.linalg.eigvalsh(A_loop)
    # Check A_loop^2 = J + q*I
    err = np.max(np.abs(A_loop @ A_loop - (np.ones((N, N)) + q * np.eye(N))))
    print(f"ER({q:2d}): N={N:3d}, max|A_loop^2 - (J+qI)|={err:.1e}, spec(A_loop) unique={np.unique(np.round(eigs_loop, 4))}, spec(A) top3={np.round(eigs[-3:], 4)}, bot2={np.round(eigs[:2], 4)}")

    # Compare EML upper bound on dbar(S) for induced subgraphs S of size N' = N - s
    # EML on A_loop:
    # For indicator 1_S of size N':
    # 1_S^T A_loop 1_S = 2 e(S) + |S cap Abs|
    # Writing 1_S = (N'/N) 1 + x (with x perp 1, ||x||^2 = N' (1 - N'/N)):
    # 1_S^T A_loop 1_S <= (q+1) N'^2 / N + sqrt(q) * N' * (1 - N'/N)!
    # Wait! That's direct on S WITHOUT even needing D!
    # Check how strong direct EML on S is vs EML on D!!
    #Wait: on S: 2 e(S) <= (q+1) N'^2 / N + sqrt(q) * N' * (1 - N'/N) - s_a_in_S!
    # Wait: if N' = N - s, (1 - N'/N) = s/N, so:
    # dbar(S) = 2e(S)/N' <= (q+1) N'/N + sqrt(q) * s / N !!
    # WAIT A SECOND! Look at direct EML on S vs EML on D:
    # On S: dbar(S) <= (q+1)(1 - s/N) + sqrt(q)*(s/N) ~ (q+1) - s/q + s/(q^{3/2})!
    # On D: dbar(S) <= [q(q+1)^2 - 2(q+1)s + 2*s_a_in_D + (q+1)s^2/N + sqrt(q)*s*(1-s/N)] / (N-s)!
    # Which one is tighter?! Notice (q+1) - s/q loses 1 per q deleted, whereas EML on S loses ~1 per q deleted TOO, WAIT:
    # Check both numerically for ER(7) at N'=34..45!
    if q == 7:
        print("  Comparing upper bounds on delta(S) <= floor(dbar(S)) inside ER(7):")
        E_tot = sum(len(adj[u]) for u in range(N)) // 2
        for Np in [45, 43, 41, 40, 39, 38, 37, 36, 35, 34]:
            s = N - Np
            # Bound 1: direct EML on S (assuming 0 abs vertices in S if Np <= N-(q+1))
            min_abs_in_S = max(0, Np - (N - (q + 1)))
            ub_S_eml = ((q + 1) * Np * Np / N + math.sqrt(q) * Np * (1 - Np / N) - min_abs_in_S) / Np
            # Bound 2: EML on D (assuming all q+1 abs vertices are in D to maximize remaining edges!)
            sa_D = min(s, q + 1)
            # 1_D^T A_loop 1_D <= (q+1)s^2/N + sqrt(q)*s*(1-s/N)
            # Also 2 e(D) = 1_D^T A_loop 1_D - sa_D
            two_eD_eml = (q + 1) * s * s / N + math.sqrt(q) * s * (1 - s / N) - sa_D
            # Note: also 2 e(D) <= 2 * floor(s/4*(1+sqrt(4s-3)))
            two_eD_kst = int(s * (1 + math.sqrt(4 * s - 3)) / 2)
            two_eD = min(two_eD_eml, two_eD_kst)
            # sum_{u in D} d(u) >= sa_D * q + (s - sa_D) * (q + 1) = (q+1)*s - sa_D
            two_eS_D = 2 * E_tot - 2 * ((q + 1) * s - sa_D) + two_eD
            ub_D_eml = two_eS_D / Np
            print(f"    N'={Np:2d} (s={s:2d}): ub_S_eml={ub_S_eml:.3f}, ub_D_eml={ub_D_eml:.3f} (2eD_eml={two_eD_eml:.2f}, 2eD_kst={two_eD_kst})")

# 2. Check consecutive prime powers and prime gaps up to 200,000!
def is_prime_power(n):
    if n < 2: return False
    for p in range(2, int(n**0.5) + 1):
        if n % p == 0:
            while n % p == 0:
                n //= p
            return n == 1
    return True

pps = [x for x in range(2, 50000) if is_prime_power(x)]
max_gap = 0
big_gaps = []
for i in range(len(pps) - 1):
    g = pps[i + 1] - pps[i]
    if g > max_gap:
        max_gap = g
        big_gaps.append((pps[i], pps[i + 1], g))
print("\n=== Record prime-power gaps up to 50,000 ===")
for q1, q2, g in big_gaps:
    # Midpoint n ~ ((q1+q2)/2)^2
    mid_q = (q1 + q2) / 2.0
    n_mid = int(round(mid_q**2))
    # If we delete from ER(q2) to hit n_mid:
    # N' ~ n_mid + d, s ~ q2^2 + q2 + 1 - N' ~ (q2^2 - n_mid) + (q2 - d)
    # Using exact direct EML bound on S <= ER(q2) of size N':
    # d <= dbar(S) <= (q2+1)*N'/N2 + sqrt(q2)*(N2-N')/N2
    # Approximate loss vs sqrt(n_mid):
    # Wait: N' = n_mid + d, N2 = q2^2 + q2 + 1.
    # Let's solve exactly: d <= (q2+1)*(n_mid+d)/N2 + sqrt(q2)*(N2 - n_mid - d)/N2
    N2 = q2*q2 + q2 + 1
    # d * (1 - (q2+1 - sqrt(q2))/N2) <= ((q2+1)*n_mid + sqrt(q2)*(N2 - n_mid)) / N2
    num = (q2 + 1) * n_mid + math.sqrt(q2) * (N2 - n_mid)
    den = N2 - (q2 + 1 - math.sqrt(q2))
    d_eml_S = num / den
    # Also check D-deletion bound:
    # 2 e(S) <= 2 E2 - 2*(q2+1)*s + 2*(q2+1) + (q2+1)*s^2/N2 + sqrt(q2)*s*(1 - s/N2)
    # Approximate s = N2 - (n_mid + d_eml_S)
    s_approx = N2 - (n_mid + d_eml_S)
    two_eD = (q2 + 1) * s_approx**2 / N2 + math.sqrt(q2) * s_approx * (1 - s_approx / N2)
    d_eml_D = (q2 * (q2 + 1)**2 - 2 * (q2 + 1) * s_approx + 2 * (q2 + 1) + two_eD) / (n_mid + d_eml_S)
    best_ub = min(d_eml_S, d_eml_D)
    deficit = math.sqrt(n_mid) - best_ub
    print(f"  q1={q1:5d}, q2={q2:5d}, gap={g:2d}, n_mid={n_mid:10d}, sqrt(n)={math.sqrt(n_mid):8.2f}, ub_EML(ER(q2))={best_ub:8.2f}, deficit(sqrt(n)-ub)={deficit:+6.2f}")
