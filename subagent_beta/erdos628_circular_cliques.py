import time
import networkx as nx
from erdos628_check import exact_chromatic_number, exact_clique_number, check_tihany_3_4
from erdos628_circulants_and_critical import check_tihany_general


def circular_clique(p: int, q: int) -> nx.Graph:
    G = nx.Graph()
    G.add_nodes_from(range(p))
    for i in range(p):
        for j in range(i + 1, p):
            d = min((j - i) % p, (i - j) % p)
            if d >= q:
                G.add_edge(i, j)
    return G


def main():
    t0 = time.time()
    print("=== CIRCULAR CLIQUES K_{p/q} WITH 5 < p/q < 6 (chi=6, omega=5, alpha=q) ===")
    cases = [(11, 2), (16, 3), (17, 3), (21, 4), (22, 4), (23, 4), (26, 5)]
    for p, q in cases:
        G = circular_clique(p, q)
        omega = exact_clique_number(G)
        chi = exact_chromatic_number(G, max_k=8) if p <= 23 else 6
        ok34, r34 = check_tihany_3_4(G)
        ok25, r25 = check_tihany_general(G, 2, 5)
        print(f"K_{{{p}/{q}}} (n={p:2d}, alpha={q}, chi={chi}, omega={omega}): (3,4)={ok34} ({r34}) | (2,5)={ok25}")
    print(f"Done in {time.time() - t0:.2f}s")


if __name__ == "__main__":
    main()
