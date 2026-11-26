import urllib.request, json, math
from collections import Counter
from analyze_552_polarity import build_ER

# 1. Inspect Boza PDF table cleanly using fitz or pdfplumber or pypdf
import pypdf
r = pypdf.PdfReader(r"C:\Users\Kerem\.gemini\antigravity\scratch\erdos-hunter\subagent_alpha\boza_2409_12770.pdf")
print("=== BOZA PAGES 3-4 RAW TEXT ===")
for p in [2, 3]:
    print(f"--- Page {p+1} ---")
    print(r.pages[p].extract_text(extraction_mode="layout"))

# 2. Analyze HoG graphs 53036..52632: structure, eigenvalues, girth, triangles, bipartiteness, embeddability in ER(q)!
print("\n=== ANALYZING HoG WITNESS GRAPHS ===")
import numpy as np
for gid in [53036, 56941, 56942, 56943, 56944, 56945, 52632]:
    req = urllib.request.Request(f"https://houseofgraphs.org/api/graphs/{gid}", headers={"User-Agent": "Mozilla/5.0"})
    d = json.loads(urllib.request.urlopen(req, timeout=10).read().decode())
    adj = d["adjacencyList"]
    N = len(adj)
    A = np.zeros((N, N), dtype=int)
    for u, nbrs in enumerate(adj):
        for v in nbrs:
            A[u, v] = 1
    # Check triangles per vertex
    A3 = A @ A @ A
    tri_per_v = [int(A3[i, i]) // 2 for i in range(N)]
    # Check bipartite
    color = [-1]*N
    bip = True
    for s in range(N):
        if color[s] == -1:
            color[s] = 0
            q = [s]
            while q:
                u = q.pop()
                for v in adj[u]:
                    if color[v] == -1:
                        color[v] = 1 - color[u]
                        q.append(v)
                    elif color[v] == color[u]:
                        bip = False
    # Check common neighbors distribution for non-edges and edges
    A2 = A @ A
    cn_edge = Counter()
    cn_non = Counter()
    for i in range(N):
        for j in range(i+1, N):
            if A[i, j]: cn_edge[int(A2[i, j])] += 1
            else: cn_non[int(A2[i, j])] += 1
    eigs = np.round(np.linalg.eigvalsh(A), 3)
    print(f"HoG {gid} (N={N}): bip={bip}, tri_per_v={dict(Counter(tri_per_v))}, cn_edge={dict(cn_edge)}, cn_non={dict(cn_non)}, top_eigs={sorted(set(eigs), reverse=True)[:5]}")
