import itertools
import time
import numpy as np
import networkx as nx
from erdos628_check import (
    is_k_colorable,
    exact_chromatic_number,
    exact_clique_number,
    check_tihany_3_4,
    graph_join,
    build_schrijver,
)


def hajos_merge(G1: nx.Graph, G2: nx.Graph) -> nx.Graph:
    """Hajós construction on two graphs: remove edge (u1,v1) in G1 and (u2,v2) in G2, identify u1=u2, add edge (v1,v2)."""
    G1 = nx.convert_node_labels_to_integers(G1)
    G2 = nx.convert_node_labels_to_integers(G2)
    n1 = G1.number_of_nodes()
    u1, v1 = list(G1.edges())[0]
    u2, v2 = list(G2.edges())[0]
    G = nx.Graph()
    G.add_nodes_from(range(n1 + G2.number_of_nodes() - 1))

    def map2(x):
        if x == u2:
            return u1
        return n1 + (x - 1 if x > u2 else x)

    for a, b in G1.edges():
        if {a, b} != {u1, v1}:
            G.add_edge(a, b)
    for a, b in G2.edges():
        if {a, b} != {u2, v2}:
            G.add_edge(map2(a), map2(b))
    G.add_edge(v1, map2(v2))
    return G


def test_more_structured_graphs():
    print("=== PART 1: HAJOS, CRITICAL, SCHRIJVER(10,3), EXPANDED STRUCTURED SUITE ===")
    graphs = {}
    K6 = nx.complete_graph(6)
    H11 = hajos_merge(K6, K6)
    graphs["Hajos(K6, K6) (n=11)"] = H11
    graphs["Hajos(H11, K6) (n=16)"] = hajos_merge(H11, K6)
    graphs["Hajos(K3+C5, K3+C5) (n=15)"] = hajos_merge(
        graph_join(nx.complete_graph(3), nx.cycle_graph(5)),
        graph_join(nx.complete_graph(3), nx.cycle_graph(5)),
    )
    # Complement of line graph of Petersen? (n=15)
    L_P = nx.line_graph(nx.petersen_graph())
    graphs["Comp(Line(Petersen)) (n=15)"] = nx.complement(L_P)
    # Complement of Clebsch (n=16)
    # Build Clebsch
    reps = [v for v in range(32) if bin(v).count("1") % 2 == 0]
    idx_map = {v: i for i, v in enumerate(reps)}
    Clebsch = nx.Graph()
    Clebsch.add_nodes_from(range(16))
    for v in reps:
        for b in range(5):
            Clebsch.add_edge(idx_map[v], idx_map[31 ^ (v ^ (1 << b))])
    graphs["Comp(Clebsch) (n=16)"] = nx.complement(Clebsch)

    # K5 + K1? No, omega=6. What about C7 + C5? chi = 3+3=6, omega=4, n=12
    graphs["C7 + C5 (n=12)"] = graph_join(nx.cycle_graph(7), nx.cycle_graph(5))
    # Join of three C5s? chi=9. Join of K2 + C5 + C5? chi=2+3+3=8.
    # Mycielskian(Grotzsch) = M5 (chi=5), join K1 -> chi=6, omega=3
    # Schrijver SG(10, 3) (n=50, chi=6, omega=3)
    SG10_3 = build_schrijver(10, 3)
    graphs["Schrijver SG(10,3) (n=50)"] = SG10_3

    for name, G in graphs.items():
        n = G.number_of_nodes()
        omega = exact_clique_number(G)
        if n <= 25:
            chi = exact_chromatic_number(G, max_k=10)
        else:
            chi = 6  # SG(10,3) known chi = 10 - 2*3 + 2 = 6
        if chi == 6 and omega <= 5:
            if n <= 25:
                ok, reason = check_tihany_3_4(G)
                print(f"[chi=6, omega={omega}] {name:30s} (n={n:2d}) -> Tihany(3,4)={ok} | {reason}")
            else:
                # Test triangle removal on SG(10,3)
                G_int = nx.convert_node_labels_to_integers(G)
                adj_list = [list(G_int.neighbors(u)) for u in range(n)]
                found = False
                for u in range(n):
                    nu = set(adj_list[u])
                    for v in adj_list[u]:
                        if v > u:
                            for w in adj_list[v]:
                                if w > v and w in nu:
                                    rem = [i for i in range(n) if i not in (u, v, w)]
                                    imap = {old: new for new, old in enumerate(rem)}
                                    sub_adj = [[imap[x] for x in adj_list[y] if x in imap] for y in rem]
                                    if not is_k_colorable(sub_adj, len(rem), 3):
                                        print(f"[chi=6, omega={omega}] {name:30s} (n={n:2d}) -> Tihany(3,4)=True | Triangle {(u,v,w)} leaves chi>=4")
                                        found = True
                                        break
                            if found:
                                break
                    if found:
                        break
                if not found:
                    print(f"[chi=6, omega={omega}] {name:30s} (n={n:2d}) -> NO triangle leaves chi>=4! Need C5 check!")
        else:
            print(f"[SKIP chi={chi}, omega={omega}] {name:30s} (n={n:2d})")


def count_bad_triangles(G: nx.Graph) -> tuple[int, int]:
    """Return (total triangles, triangles whose removal leaves chi >= 4)."""
    G_int = nx.convert_node_labels_to_integers(G)
    n = G_int.number_of_nodes()
    adj_list = [list(G_int.neighbors(u)) for u in range(n)]
    tris = []
    for u in range(n):
        nu = set(adj_list[u])
        for v in adj_list[u]:
            if v > u:
                for w in adj_list[v]:
                    if w > v and w in nu:
                        tris.append((u, v, w))
    bad = 0
    for tri in tris:
        rem = [i for i in range(n) if i not in tri]
        imap = {old: new for new, old in enumerate(rem)}
        sub_adj = [[imap[x] for x in adj_list[y] if x in imap] for y in rem]
        if not is_k_colorable(sub_adj, len(rem), 3):
            bad += 1
    return len(tris), bad


def hunt_counterexample_sa():
    print("\n=== PART 2: SIMULATED ANNEALING COUNTEREXAMPLE HUNTER FOR (3,4)-TIHANY ===")
    rng = np.random.default_rng(777)
    for n in [9, 10, 11, 12, 13, 14, 15, 16]:
        min_bad_seen = 10**9
        chi6_found = 0
        for restart in range(15):
            # Start from a random K6-free graph with chi >= 6 (or K3 + C5 + extra vertices, or dense random)
            if n <= 12:
                # Start from random dense K6-free graph
                G = nx.erdos_renyi_graph(n, 0.72, seed=int(rng.integers(10**9)))
            else:
                G = nx.erdos_renyi_graph(n, 0.62, seed=int(rng.integers(10**9)))
            # Repair omega <= 5
            while True:
                cliques = [c for c in nx.find_cliques(G) if len(c) >= 6]
                if not cliques:
                    break
                c = cliques[0]
                G.remove_edge(c[0], c[1])

            # Ensure chi >= 6 by adding non-K6 edges greedily if needed
            for _ in range(40):
                G_int = nx.convert_node_labels_to_integers(G)
                adj_list = [list(G_int.neighbors(u)) for u in range(n)]
                if not is_k_colorable(adj_list, n, 5):
                    break
                # Add random edge that doesn't create K6
                non_edges = list(nx.non_edges(G))
                if not non_edges:
                    break
                rng.shuffle(non_edges)
                added = False
                for u, v in non_edges[:20]:
                    G.add_edge(u, v)
                    # Check if u, v in a K6
                    if exact_clique_number(G.subgraph([u, v] + list(set(G[u]) & set(G[v])))) <= 5:
                        added = True
                        break
                    G.remove_edge(u, v)
                if not added:
                    break

            chi = exact_chromatic_number(G, max_k=9)
            if chi != 6:
                continue
            chi6_found += 1
            _, cur_bad = count_bad_triangles(G)
            if cur_bad < min_bad_seen:
                min_bad_seen = cur_bad

            # SA: mutate edges keeping chi == 6 and omega <= 5, trying to minimize bad_triangles!
            for step in range(80):
                edges = list(G.edges())
                non_edges = list(nx.non_edges(G))
                if not edges or not non_edges:
                    break
                # Remove an edge, or swap an edge with a non-edge
                G2 = G.copy()
                u, v = edges[rng.integers(len(edges))]
                G2.remove_edge(u, v)
                if rng.random() < 0.35:
                    a, b = non_edges[rng.integers(len(non_edges))]
                    G2.add_edge(a, b)
                    if exact_clique_number(G2.subgraph([a, b] + list(set(G2[a]) & set(G2[b])))) > 5:
                        continue
                G2_int = nx.convert_node_labels_to_integers(G2)
                adj2 = [list(G2_int.neighbors(x)) for x in range(n)]
                # Must stay non-5-colorable! (chi=6 since we didn't raise omega>5, check chi<=6 too)
                if is_k_colorable(adj2, n, 5):
                    continue
                if not is_k_colorable(adj2, n, 6):
                    continue
                _, new_bad = count_bad_triangles(G2)
                if new_bad <= cur_bad or rng.random() < 0.15:
                    G = G2
                    cur_bad = new_bad
                    if cur_bad < min_bad_seen:
                        min_bad_seen = cur_bad
                    if cur_bad == 0:
                        ok, reason = check_tihany_3_4(G)
                        if not ok:
                            print(f"!!! COUNTEREXAMPLE FOUND AT n={n} !!! {reason}")
                            print("Edges:", list(G.edges()))
                            return

        print(f"n={n:2d}: chi=6 starts={chi6_found:2d}/15 | min bad triangles (leaving chi>=4) = {min_bad_seen}")


if __name__ == "__main__":
    t0 = time.time()
    test_more_structured_graphs()
    hunt_counterexample_sa()
    print(f"\nDone in {time.time() - t0:.2f}s")
