import math
import numpy as np
import networkx as nx
from erdos128_check import exact_min_edges_subset, is_triangle_free


def c5_blowup(t: int) -> np.ndarray:
    n = 5 * t
    A = np.zeros((n, n), dtype=int)
    for i in range(5):
        j = (i + 1) % 5
        A[i*t:(i+1)*t, j*t:(j+1)*t] = 1
        A[j*t:(j+1)*t, i*t:(i+1)*t] = 1
    return A


def exact_c5_blowup_min_edges(t: int, m: int) -> tuple[int, tuple[int, ...]]:
    """Exact minimum over all integer (x0,x1,x2,x3,x4) in [0, t]^5 with sum = m."""
    best = 10**12
    best_x = ()
    for x0 in range(min(t, m) + 1):
        for x1 in range(min(t, m - x0) + 1):
            for x2 in range(min(t, m - x0 - x1) + 1):
                for x3 in range(min(t, m - x0 - x1 - x2) + 1):
                    x4 = m - x0 - x1 - x2 - x3
                    if 0 <= x4 <= t:
                        e = x0*x1 + x1*x2 + x2*x3 + x3*x4 + x4*x0
                        if e < best:
                            best = e
                            best_x = (x0, x1, x2, x3, x4)
    return best, best_x


def main():
    print("=== VERIFYING C5[t] FOR PROSE (|V'| >= n/2) VS LEAN (2|V'| + 1 >= n) ===")
    for t in range(1, 16):
        n = 5 * t
        m_lean = n // 2
        m_prose = (n + 1) // 2
        e_lean, x_lean = exact_c5_blowup_min_edges(t, m_lean)
        e_prose, x_prose = exact_c5_blowup_min_edges(t, m_prose)
        thresh = (n * n) / 50.0
        # Also verify matrix triangle-freeness for t <= 6
        if t <= 6:
            A = c5_blowup(t)
            assert is_triangle_free(A)
        print(
            f"t={t:2d}, n={n:2d}, n^2/50={thresh:6.2f} | "
            f"Lean(m={m_lean:2d}): min_e={e_lean:3d} {x_lean} (> thresh? {e_lean > thresh}) | "
            f"Prose(m={m_prose:2d}): min_e={e_prose:3d} {x_prose} (> thresh? {e_prose > thresh})"
        )

    # Also verify algebraic identity for t = 2s + 1 up to s = 100
    for s in range(1, 20):
        t = 2 * s + 1
        n = 5 * t
        m_prose = 5 * s + 3
        e_prose, x_prose = exact_c5_blowup_min_edges(t, m_prose)
        assert e_prose == 2 * s * s + 3 * s + 1
        assert 50 * e_prose > n * n
    print("Verified exact algebraic formula e_min(C5[2s+1], ceil(n/2)) = 2s^2 + 3s + 1 > (10s+5)^2 / 50 for s=1..19!")


if __name__ == "__main__":
    main()
