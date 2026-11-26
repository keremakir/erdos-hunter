import math
from fractions import Fraction

def analyze_steiner(k):
    v = 2 * k
    t = k - 1
    div_ok = True
    lam = []
    for i in range(k):
        num = math.comb(v - i, t - i)
        den = math.comb(k - i, t - i)
        if num % den != 0:
            div_ok = False
        lam.append(Fraction(num, den))
    # Mendelsohn equations for n_0 .. n_{k-2}:
    # sum_{j=i}^{k-2} C(j, i) * n_j = C(k, i) * (lam[i] - 1) for i = 0 .. k-2
    n = [Fraction(0)] * (k - 1)
    for i in range(k - 2, -1, -1):
        rhs = math.comb(k, i) * (lam[i] - 1)
        for j in range(i + 1, k - 1):
            rhs -= math.comb(j, i) * n[j]
        n[i] = rhs
    all_int = all(x.denominator == 1 for x in n)
    all_nonneg = all(x >= 0 for x in n)
    return div_ok, all_int, all_nonneg, lam, n

def main():
    ks = [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 18, 22, 28, 30, 36, 40, 42]
    for k in ks:
        div_ok, all_int, all_nonneg, lam, n = analyze_steiner(k)
        status = f"k={k:2d} (k+1={k+1:2d}): div_ok={str(div_ok):5s}, all_int={str(all_int):5s}, all_nonneg={str(all_nonneg):5s}"
        if k <= 16:
            n_str = [int(x) if x.denominator == 1 else str(x) for x in n]
            print(f"{status}, n_j={n_str}")
        else:
            bad = [(j, str(n[j])) for j in range(k - 1) if n[j].denominator != 1 or n[j] < 0]
            print(f"{status}, n_0={n[0]}, bad={bad[:4]}")

if __name__ == "__main__":
    main()
