import urllib.request, json, math
from collections import Counter
from analyze_552_polarity import build_ER

# 1. Check max degree of any single vertex added to ER(q) without creating C4!
for q in [3, 4, 5, 7]:
    pts, adj, is_abs = build_ER(q)
    N = len(pts)
    # Two vertices u, v can both be adjacent to new vertex w iff u and v have NO common neighbor in ER(q)!
    # Build "compatible pair" graph on V(ER(q)): u ~ v iff |N(u) cap N(v)| == 0!
    comp = [set() for _ in range(N)]
    for u in range(N):
        for v in range(u + 1, N):
            if len(adj[u] & adj[v]) == 0:
                comp[u].add(v)
                comp[v].add(u)
    # Find max clique in comp (greedy + exact branch for small q)
    # Wait: what ARE the compatible pairs in ER(q)?!
    deg_comp = Counter(len(comp[u]) for u in range(N))
    # Also find exact max clique in comp!
    best_clique = []
    def branch(cand, cur):
        global best_clique
        if len(cur) + len(cand) <= len(best_clique):
            return
        if not cand:
            best_clique = list(cur)
            return
        # pick first vertex
        for i, v in enumerate(cand):
            nxt = [u for u in cand[i+1:] if u in comp[v]]
            branch(nxt, cur + [v])
    branch(list(range(N)), [])
    print(f"ER({q}): max deg of an added vertex without C4 = {len(best_clique)}, comp_degs={dict(deg_comp)}, example={[(i, is_abs[i]) for i in best_clique]}")

# 2. Check if HoG 56941 (N=35) is vertex-transitive or Cayley or Sidon sum graph!
req = urllib.request.Request("https://houseofgraphs.org/api/graphs/56941", headers={"User-Agent": "Mozilla/5.0"})
d = json.loads(urllib.request.urlopen(req, timeout=10).read().decode())
adj = d["adjacencyList"]
N = len(adj)
# Check eigenvalues and degree of vertex-neighborhoods and 2-hop sizes
for u in [0, 1, 2]:
    one = set(adj[u])
    two = set()
    for v in one:
        two.update(adj[v])
    two -= one
    two.discard(u)
    print(f"HoG 56941 vertex {u}: |N1|={len(one)}, |N2|={len(two)}, total={1+len(one)+len(two)}")
# Check if all pairs in N2? No, diam > 2 since 1+6+24 = 31 < 35!
# Wait: 4 vertices at distance 3 from u! Let's check distance profile from every vertex!
from collections import deque
profiles = Counter()
for s in range(N):
    dist = [-1]*N
    dist[s] = 0
    q = deque([s])
    while q:
        u = q.popleft()
        for v in adj[u]:
            if dist[v] == -1:
                dist[v] = dist[u] + 1
                q.append(v)
    profiles[tuple(sorted(Counter(dist).items()))] += 1
print("HoG 56941 BFS distance profiles:", dict(profiles))
