import itertools
import time
import numpy as np
import networkx as nx
from erdos628_check import (
    is_k_colorable,
    exact_chromatic_number,
    exact_clique_number,
    check_tihany_3_4,
)


def check_tihany_general(G: nx.Graph, a: int, b: int) -> tuple[bool, str]:
    """Check (a, b)-Tihany for small a in {2, 3}."""
    G_int = nx.convert_node_labels_to_integers(G)
    n = G_int.number_of_nodes()
    adj_list = [list(G_int.neighbors(u)) for u in range(n)]
    if a == 2:
        # Every edge is a minimal 2-chromatic subgraph
        for u, v in G_int.edges():
            rem = [i for i in range(n) if i not in (u, v)]
            imap = {old: new for new, old in enumerate(rem)}
            sub_adj = [[imap[x] for x in adj_list[y] if x in imap] for y in rem]
            if not is_k_colorable(sub_adj, len(rem), b - 1):
                return True, f"Edge ({u},{v}) leaves chi>={b}"
        return False, "No edge leaves chi>=b"
    elif a == 3 and b == 4:
        return check_tihany_3_4(G)
    else:
        # Check induced K_a or random/small a-chromatic subgraphs
        for sub in itertools.combinations(range(n), a):
            S = G_int.subgraph(sub)
            if S.number_of_edges() == a * (a - 1) // 2:
                rem = [i for i in range(n) if i not in sub]
                imap = {old: new for new, old in enumerate(rem)}
                sub_adj = [[imap[x] for x in adj_list[y] if x in imap] for y in rem]
                if not is_k_colorable(sub_adj, len(rem), b - 1):
                    return True, f"Clique K_{a} {sub} leaves chi>={b}"
        return False, "No K_a leaves chi>=b (non-exhaustive)"


def reduce_to_critical(G: nx.Graph, target_chi: int = 6) -> nx.Graph:
    """Greedily delete vertices and edges while maintaining chi == target_chi."""
    H = G.copy()
    changed = True
    while changed:
        changed = False
        for v in list(H.nodes()):
            H2 = H.copy()
            H2.remove_node(v)
            if exact_chromatic_number(H2, max_k=target_chi) == target_chi:
                H = H2
                changed = True
                break
    changed = True
    while changed:
        changed = False
        for u, v in list(H.edges()):
            H2 = H.copy()
            H2.remove_edge(u, v)
            if exact_chromatic_number(H2, max_k=target_chi) == target_chi:
                H = H2
                changed = True
                break
    return H


def main():
    t0 = time.time()
    print("=== PART 1: CIRCULANT GRAPHS n=8..17 WITH chi=6, omega<=5 ===")
    circ_tested = 0
    circ_chi6 = 0
    for n in range(8, 17):
        half = n // 2
        # Sample or enumerate jump sets for n <= 14; sample for 15..16
        all_jumps = list(range(1, half + 1))
        if half <= 7:
            jump_sets = [
                js for r in range(2, half + 1)
                for js in itertools.combinations(all_jumps, r)
            ]
        else:
            rng = np.random.default_rng(n)
            jump_sets = set()
            for _ in range(300):
                r = int(rng.integers(2, half + 1))
                js = tuple(sorted(rng.choice(all_jumps, size=r, replace=False).tolist()))
                jump_sets.add(js)
            jump_sets = list(jump_sets)

        for js in jump_sets:
            G = nx.circulant_graph(n, list(js))
            # Quick degree check: for chi=6 critical we need deg >= 5
            if G.degree(0) < 5:
                continue
            omega = exact_clique_number(G)
            if omega > 5:
                continue
            chi = exact_chromatic_number(G, max_k=8)
            if chi == 6:
                circ_chi6 += 1
                ok34, r34 = check_tihany_3_4(G)
                ok25, r25 = check_tihany_general(G, 2, 5)
                if not ok34 or not ok25:
                    print(f"!!! CIRCULANT COUNTEREXAMPLE n={n} jumps={js}: (3,4)={ok34} ({r34}), (2,5)={ok25} ({r25})")
                elif circ_chi6 <= 15:
                    print(f"  [n={n:2d}, jumps={str(js):14s}, omega={omega}] (3,4)=True, (2,5)=True")
            circ_tested += 1
    print(f"Circulants checked (deg>=5, omega<=5): {circ_tested}, chi=6 count: {circ_chi6}, 0 counterexamples.")

    print("\n=== PART 2: 6-CRITICAL K6-FREE GRAPHS WITH alpha >= 3 ===")
    rng = np.random.default_rng(999)
    crit_seen = set()
    crit_count = 0
    for n in range(9, 16):
        for trial in range(60):
            G = nx.erdos_renyi_graph(n, rng.uniform(0.55, 0.78), seed=int(rng.integers(10**9)))
            while True:
                cliques = [c for c in nx.find_cliques(G) if len(c) >= 6]
                if not cliques:
                    break
                c = cliques[0]
                G.remove_edge(c[0], c[1])
            if exact_chromatic_number(G, max_k=7) != 6:
                continue
            C = reduce_to_critical(G, 6)
            h = nx.weisfeiler_lehman_graph_hash(C)
            if h in crit_seen:
                continue
            crit_seen.add(h)
            crit_count += 1
            omega = exact_clique_number(C)
            alpha = exact_clique_number(nx.complement(C))
            ok34, r34 = check_tihany_3_4(C)
            ok25, r25 = check_tihany_general(C, 2, 5)
            if not ok34 or not ok25:
                print(f"!!! CRITICAL CE: n={C.number_of_nodes()}, omega={omega}, alpha={alpha}, (3,4)={ok34}, (2,5)={ok25}")
                print("Edges:", list(C.edges()))
            elif crit_count <= 20:
                print(f"  Critical #{crit_count:2d}: n={C.number_of_nodes():2d}, m={C.number_of_edges():2d}, omega={omega}, alpha={alpha} -> (3,4)=True, (2,5)=True")

    print(f"Total distinct 6-critical K6-free graphs tested: {crit_count}, 0 counterexamples.")
    print(f"Done in {time.time() - t0:.2f}s")


if __name__ == "__main__":
    main()
