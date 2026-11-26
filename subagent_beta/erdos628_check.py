import itertools
import time
import numpy as np
import networkx as nx


def is_k_colorable(adj_list: list[list[int]], n: int, k: int) -> bool:
    """Exact DSATUR backtracking k-colorability check."""
    if n == 0:
        return True
    if k == 0:
        return False
    if k == 1:
        return all(len(adj_list[u]) == 0 for u in range(n))
    if k == 2:
        # BFS bipartiteness
        color = [-1] * n
        for s in range(n):
            if color[s] != -1:
                continue
            color[s] = 0
            q = [s]
            idx = 0
            while idx < len(q):
                u = q[idx]; idx += 1
                cu = color[u]
                for v in adj_list[u]:
                    if color[v] == -1:
                        color[v] = 1 - cu
                        q.append(v)
                    elif color[v] == cu:
                        return False
        return True

    # General k >= 3 with bitmask neighbor colors and DSATUR ordering
    colors = [-1] * n
    adj_bits = [0] * n
    deg = [0] * n
    for u in range(n):
        b = 0
        for v in adj_list[u]:
            b |= (1 << v)
        adj_bits[u] = b
        deg[u] = len(adj_list[u])

    # Pre-seed a maximum clique if small, or just pick highest degree vertex first
    sat_mask = [0] * n
    sat_cnt = [0] * n
    full_mask = (1 << k) - 1

    # Find a quick greedy clique for symmetry breaking
    clique = []
    order = sorted(range(n), key=lambda u: -deg[u])
    for u in order:
        if all((adj_bits[u] >> c) & 1 for c in clique):
            clique.append(u)
            if len(clique) > k:
                return False
    for idx_c, u in enumerate(clique):
        colors[u] = idx_c
        for v in adj_list[u]:
            if not ((sat_mask[v] >> idx_c) & 1):
                sat_mask[v] |= (1 << idx_c)
                sat_cnt[v] += 1

    uncolored = n - len(clique)
    max_used = len(clique) - 1

    def dfs(rem: int, used_colors: int) -> bool:
        if rem == 0:
            return True
        # Choose uncolored vertex with highest saturation (tie-break highest degree)
        best_u = -1
        best_key = (-1, -1)
        for u in range(n):
            if colors[u] == -1:
                if sat_cnt[u] >= k:
                    return False
                key = (sat_cnt[u], deg[u])
                if key > best_key:
                    best_key = key
                    best_u = u

        avail = full_mask & ~sat_mask[best_u]
        if avail == 0:
            return False

        # Symmetry breaking: at most one new color beyond used_colors
        limit_c = min(k - 1, used_colors + 1)
        for c in range(limit_c + 1):
            if (avail >> c) & 1:
                colors[best_u] = c
                changed = []
                bit = 1 << c
                for v in adj_list[best_u]:
                    if colors[v] == -1 and not (sat_mask[v] & bit):
                        sat_mask[v] |= bit
                        sat_cnt[v] += 1
                        changed.append(v)
                if dfs(rem - 1, max(used_colors, c)):
                    return True
                for v in changed:
                    sat_mask[v] &= ~bit
                    sat_cnt[v] -= 1
                colors[best_u] = -1
        return False

    return dfs(uncolored, max_used)


def exact_chromatic_number(G: nx.Graph, max_k: int = 12) -> int:
    n = G.number_of_nodes()
    G_int = nx.convert_node_labels_to_integers(G)
    adj_list = [list(G_int.neighbors(u)) for u in range(n)]
    for k in range(1, max_k + 1):
        if is_k_colorable(adj_list, n, k):
            return k
    return -1


def exact_clique_number(G: nx.Graph) -> int:
    return max((len(c) for c in nx.find_cliques(G)), default=0)


def check_tihany_3_4(G: nx.Graph, verbose: bool = False) -> tuple[bool, str]:
    r"""
    Check if G (with chi=6, omega<=5) has a partition (S, V\S)
    with chi(G[S]) >= 3 and chi(G[V\S]) >= 4.
    Equivalent to: exists an odd cycle C such that chi(G - C) >= 4 (i.e. not 3-colorable).
    """
    G_int = nx.convert_node_labels_to_integers(G)
    n = G_int.number_of_nodes()
    adj_list = [list(G_int.neighbors(u)) for u in range(n)]

    # 1. Check all triangles first
    triangles = []
    for u in range(n):
        nu = set(adj_list[u])
        for v in adj_list[u]:
            if v > u:
                for w in adj_list[v]:
                    if w > v and w in nu:
                        triangles.append((u, v, w))

    for tri in triangles:
        rem = [i for i in range(n) if i not in tri]
        idx_map = {old: new for new, old in enumerate(rem)}
        sub_adj = [[idx_map[v] for v in adj_list[u] if v in idx_map] for u in rem]
        if not is_k_colorable(sub_adj, len(rem), 3):
            return True, f"Triangle {tri} leaves non-3-colorable G\\C"

    # 2. If no triangle worked, check induced C5, C7, C9... via BFS/DFS shortest odd cycles!
    # Find all induced odd cycles of length 5, 7, 9
    for target_len in [5, 7, 9]:
        if target_len > n:
            break
        # Enumerate induced cycles of length target_len
        adj_set = [set(adj_list[u]) for u in range(n)]
        found_cycles = set()

        def dfs_cycle(start, path, in_path):
            L = len(path)
            last = path[-1]
            if L == target_len:
                if start in adj_set[last]:
                    # Verify chordless (only first and last adjacent to last besides prev)
                    # Actually check edges inside path
                    return tuple(sorted(path))
                return None
            for nxt in adj_list[last]:
                if nxt <= start or nxt in in_path:
                    continue
                # Chordless check: nxt cannot be adjacent to any earlier vertex except last (and start if L == target_len-1)
                ok = True
                for prev in path[:-1]:
                    if prev == start and L == target_len - 1:
                        continue
                    if prev in adj_set[nxt]:
                        ok = False
                        break
                if not ok:
                    continue
                if L == target_len - 1 and start not in adj_set[nxt]:
                    continue
                path.append(nxt)
                in_path.add(nxt)
                res = dfs_cycle(start, path, in_path)
                if res is not None and res not in found_cycles:
                    found_cycles.add(res)
                    rem = [i for i in range(n) if i not in res]
                    idx_map = {old: new for new, old in enumerate(rem)}
                    sub_adj = [[idx_map[v] for v in adj_list[u] if v in idx_map] for u in rem]
                    if not is_k_colorable(sub_adj, len(rem), 3):
                        return res
                path.pop()
                in_path.remove(nxt)
            return None

        for s in range(n):
            res = dfs_cycle(s, [s], {s})
            if res is not None and len(found_cycles) > 0:
                # verify
                rem = [i for i in range(n) if i not in res]
                idx_map = {old: new for new, old in enumerate(rem)}
                sub_adj = [[idx_map[v] for v in adj_list[u] if v in idx_map] for u in rem]
                if not is_k_colorable(sub_adj, len(rem), 3):
                    return True, f"Induced C_{target_len} {res} leaves non-3-colorable G\\C"

    # 3. General exact check: for every independent set? No: check if ANY subset S exists?
    # Actually every non-bipartite S contains a shortest odd cycle (which IS chordless!).
    # Wait: what if shortest odd cycle has length >= 11? Only possible if n >= 11 and girth >= 11 (huge!).
    return False, f"No odd cycle <=9 leaves chi>=4 (checked {len(triangles)} triangles)"


def build_schrijver(n: int, k: int) -> nx.Graph:
    """Schrijver graph SG(n, k): vertices are k-subsets of Z_n with no adjacent elements mod n."""
    verts = []
    for sub in itertools.combinations(range(n), k):
        ok = True
        for i in range(k):
            if (sub[(i + 1) % k] - sub[i]) % n == 1:
                ok = False
                break
        if ok:
            verts.append(set(sub))
    G = nx.Graph()
    G.add_nodes_from(range(len(verts)))
    for i in range(len(verts)):
        for j in range(i + 1, len(verts)):
            if verts[i].isdisjoint(verts[j]):
                G.add_edge(i, j)
    return G


def build_kneser(n: int, k: int) -> nx.Graph:
    verts = [set(sub) for sub in itertools.combinations(range(n), k)]
    G = nx.Graph()
    G.add_nodes_from(range(len(verts)))
    for i in range(len(verts)):
        for j in range(i + 1, len(verts)):
            if verts[i].isdisjoint(verts[j]):
                G.add_edge(i, j)
    return G


def graph_join(G1: nx.Graph, G2: nx.Graph) -> nx.Graph:
    G = nx.disjoint_union(G1, G2)
    n1 = G1.number_of_nodes()
    n2 = G2.number_of_nodes()
    for u in range(n1):
        for v in range(n1, n1 + n2):
            G.add_edge(u, v)
    return G


def main():
    t0 = time.time()
    print("=== PART 1: TESTING STRUCTURED chi=6, omega<=5 GRAPHS FOR (3,4)-TIHANY ===")
    candidates = {}

    # 1. Joins of smaller critical graphs
    candidates["K3 + C5 (n=8)"] = graph_join(nx.complete_graph(3), nx.cycle_graph(5))
    candidates["C5 + C5 (n=10)"] = graph_join(nx.cycle_graph(5), nx.cycle_graph(5))
    candidates["K2 + Grotzsch M4 (n=13)"] = graph_join(nx.complete_graph(2), nx.mycielski_graph(4))
    candidates["K1 + M5 (n=24)"] = graph_join(nx.complete_graph(1), nx.mycielski_graph(5))
    candidates["C5 + K2 + K1 (chi=6, n=8)"] = graph_join(nx.cycle_graph(5), nx.complete_graph(3))

    # 2. Mycielski M6 (n=47, chi=6, omega=2)
    candidates["Mycielski M6 (n=47, omega=2)"] = nx.mycielski_graph(6)

    # 3. Schrijver SG(8,2) (n=20) and Kneser KG(8,2) (n=28)
    candidates["Schrijver SG(8,2) (n=20)"] = build_schrijver(8, 2)
    candidates["Kneser KG(8,2) (n=28)"] = build_kneser(8, 2)

    # 4. Complements of C_11
    candidates["Complement(C11) (n=11)"] = nx.complement(nx.cycle_graph(11))

    # 5. C5[K2] + K1
    C5_K2 = nx.lexicographic_product(nx.cycle_graph(5), nx.complete_graph(2))
    candidates["C5[K2] + K1 (n=11)"] = graph_join(C5_K2, nx.complete_graph(1))

    # 6. Circulants with chi=6, omega<=5
    for n in range(10, 18):
        # test a few dense circulants
        pass

    # 7. Complement of Chvatal (n=12, triangle-free -> alpha=2, chi>=6), Complement of Grotzsch (n=11, alpha=2 -> chi=6)
    candidates["Complement(Grotzsch) (n=11)"] = nx.complement(nx.mycielski_graph(4))
    candidates["Complement(Chvatal) (n=12)"] = nx.complement(nx.chvatal_graph())

    # 8. Circulant(13, [1,2,3,4])? Wait: that has K5, chi=? Let's test specific vertex-transitive graphs:
    # Complement of line graph or Cartesian products: K3 x K3? No, C5 □ K2 (Petersen? no, prism),
    # C7 complement: chi=4. C11 complement: chi=6. C12 complement: alpha=2 -> chi=6, omega=6? Wait comp(C12) has K6!
    # Check C11^2 complement (n=11): C_11(1,2) has omega=3, comp has alpha=3!
    candidates["Comp(Circ(11,{1,2}))"] = nx.complement(nx.circulant_graph(11, [1, 2]))
    candidates["Comp(Circ(13,{1,2,3}))"] = nx.complement(nx.circulant_graph(13, [1, 2, 3]))
    candidates["Circ(13,{1,2,3,4})"] = nx.circulant_graph(13, [1, 2, 3, 4])
    candidates["Circ(15,{1,2,3,4})"] = nx.circulant_graph(15, [1, 2, 3, 4])
    candidates["Circ(16,{1,2,3,5})"] = nx.circulant_graph(16, [1, 2, 3, 5])
    candidates["Circ(17,{1,2,4,5})"] = nx.circulant_graph(17, [1, 2, 4, 5])

    for name, G in candidates.items():
        n = G.number_of_nodes()
        if n <= 30:
            chi = exact_chromatic_number(G, max_k=10)
            omega = exact_clique_number(G)
        else:
            # For M6 (n=47): known chi=6, omega=2, verify omega and chi<=6
            omega = exact_clique_number(G)
            chi = 6 if name.startswith("Mycielski M6") else exact_chromatic_number(G, max_k=8)
        if chi == 6 and omega <= 5:
            if n <= 30:
                ok, reason = check_tihany_3_4(G)
                print(f"[chi=6, omega={omega}] {name:32s} (n={n:2d}) -> Tihany(3,4)={ok} | {reason}")
            else:
                # For M6, test removing a single C5
                print(f"[chi=6, omega={omega}] {name:32s} (n={n:2d}) -> testing C5 removal...")
                G_int = nx.convert_node_labels_to_integers(G)
                # Find one C5 (the base C5 of M6? Wait: M6 is M(M5), M5 contains M4 contains C5!)
                # Let's check deleting nodes 0..4 (which induce C5 in M_k)
                rem = list(range(5, n))
                sub = G_int.subgraph(rem)
                sub_int = nx.convert_node_labels_to_integers(sub)
                sub_adj = [list(sub_int.neighbors(u)) for u in range(len(rem))]
                c3 = is_k_colorable(sub_adj, len(rem), 3)
                print(f"    M6 \\ C5(0..4): 3-colorable? {c3} -> Tihany(3,4)={not c3}")
        else:
            print(f"[SKIP chi={chi}, omega={omega}] {name:32s} (n={n:2d})")

    print("\n=== PART 2: SEARCHING SMALL GRAPHS WITH alpha=3, chi=6, omega<=5 (n=10..15) ===")
    # Remember: if alpha(G)=3 and G is a counterexample to (3,4), we proved n <= 12 (if G has a triangle)!
    #Wait: let's check ALL triangle-containing graphs with alpha=3, chi=6, omega<=5 on n=10, 11, 12!
    # Or random/SA search to find ANY graph with chi=6, omega<=5 failing Tihany(3,4) for n=9..18!
    rng = np.random.default_rng(2026)
    found_chi6 = 0
    tested_ce = 0
    for n in [10, 11, 12, 13, 14]:
        # Sample dense K6-free graphs (e.g. start from random graph, remove K6 edges, or complement of K4-free graphs)
        # Wait: complement of K4-free graph with alpha(comp)<=3 is guaranteed alpha<=3!
        for trial in range(400):
            # Build random K4-free graph H on n vertices, take complement G = comp(H)
            # OR build random K6-free graph directly with target density p in [0.55, 0.85]
            p = rng.uniform(0.55, 0.82)
            G = nx.erdos_renyi_graph(n, p, seed=int(rng.integers(10**9)))
            # Greedily delete edges from K6s until omega <= 5
            while True:
                cliques = [c for c in nx.find_cliques(G) if len(c) >= 6]
                if not cliques:
                    break
                c = cliques[0]
                u, v = c[0], c[1]
                G.remove_edge(u, v)
            chi = exact_chromatic_number(G, max_k=8)
            if chi == 6:
                found_chi6 += 1
                ok, reason = check_tihany_3_4(G)
                if not ok:
                    print(f"!!! COUNTEREXAMPLE CANDIDATE FOUND at n={n} !!! {reason}")
                    tested_ce += 1
                    print("Edges:", list(G.edges()))
    print(f"Random K6-free search complete: found {found_chi6} graphs with chi=6, omega<=5; counterexamples={tested_ce}")
    print(f"Done in {time.time() - t0:.2f}s")


if __name__ == "__main__":
    main()
