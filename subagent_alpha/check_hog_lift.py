import urllib.request, json
from collections import deque

# Check if HoG 56941 has distance-3 equivalence classes of size 5!
req = urllib.request.Request("https://houseofgraphs.org/api/graphs/56941", headers={"User-Agent": "Mozilla/5.0"})
d = json.loads(urllib.request.urlopen(req, timeout=10).read().decode())
adj = d["adjacencyList"]
N = len(adj)

dist3 = [set() for _ in range(N)]
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
    dist3[s] = {v for v in range(N) if dist[v] == 3 or v == s}

classes = sorted({frozenset(x) for x in dist3})
print("Number of distinct {u} U N3(u) classes:", len(classes), "sizes:", [len(c) for c in classes])
disjoint_partition = (sum(len(c) for c in classes) == N)
print("Do they partition the 35 vertices?", disjoint_partition)
if disjoint_partition:
    # Check edges between classes!
    for i in range(len(classes)):
        for j in range(i+1, len(classes)):
            edges_ij = sum(1 for u in classes[i] for v in adj[u] if v in classes[j])
            if edges_ij != 5:
                print(f"  Mismatch edges between class {i} and {j}: {edges_ij}")
    print("Checked all pairs of classes!")
    # Check if there are edges within any class!
    internal = sum(1 for c in classes for u in c for v in adj[u] if v in c)
    print("Internal edges in classes:", internal)

# Also check HoG 53036 (N=34), 56942 (N=36), 56943 (N=37), 56944 (N=38), 56945 (N=39)!
for gid in [53036, 56942, 56943, 56944, 56945]:
    req = urllib.request.Request(f"https://houseofgraphs.org/api/graphs/{gid}", headers={"User-Agent": "Mozilla/5.0"})
    d2 = json.loads(urllib.request.urlopen(req, timeout=10).read().decode())
    adj2 = d2["adjacencyList"]
    N2 = len(adj2)
    # Check if HoG 56941 - 1 vertex = HoG 53036? No, 53036 is 6-regular!
    # Check BFS profiles!
    from collections import Counter
    profs = Counter()
    for s in range(N2):
        dist = [-1]*N2; dist[s]=0; q=deque([s])
        while q:
            u = q.popleft()
            for v in adj2[u]:
                if dist[v]==-1: dist[v]=dist[u]+1; q.append(v)
        profs[tuple(sorted(Counter(dist).items()))] += 1
    print(f"HoG {gid} (N={N2}) BFS profiles: {dict(profs)}")
