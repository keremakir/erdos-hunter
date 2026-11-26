## Audit

### Lean specification
The Lean statement is the Erdős–Lovász–Tihany conjecture in its standard graph-theoretic form:

- \(\chi(G)=k\);
- \(G\) is \(K_k\)-free;
- \(a,b\ge 2\) and \(a+b=k+1\);
- find a vertex partition \(V=s\sqcup s^c\) with
  \[
  \chi(G[s])\ge a,\qquad \chi(G[s^c])\ge b.
  \]

There is no `2 * |V'| + 1 >= n` issue in this specification: that inequality is unrelated to the Lean theorem. The complement \(s^\complement\) is a vertex-set complement, so the two induced subgraphs are genuinely disjoint and cover \(V\).

The main unresolved instance is \(k=6\), \((a,b)=(3,4)\), up to exchanging the two parts.

### Agent-output audit

1. **DeepSeek**
   - The process did not terminate:
     ```
     Exit Code: None | Time: Nones
     ```
   - There is therefore no computational result to credit.
   - The text contains unfinished speculation and several uncertain claims about smallest triangle-free high-chromatic graphs. None was verified by the run.

2. **Nemotron**
   - Also did not terminate:
     ```
     Exit Code: None | Time: Nones
     ```
   - No mathematical or computational conclusion was established.

3. **Gemma**
   - The only completed run exited successfully in 1.19 seconds.
   - It generated one 10-vertex graph and reported:
     ```
     Chromatic number: 3
     Has K6: False
     Graph does not meet criteria.
     No counterexample found in this construction.
     ```
   - This is **not** a test of Erdős #628:
     - The reported “chromatic number” is obtained from a greedy coloring upper bound, not an exact chromatic-number algorithm.
     - The graph has reported chromatic number \(3\), not \(6\).
     - It therefore does not satisfy the hypothesis \(\chi(G)=6\).
     - Testing one irrelevant graph cannot provide evidence against or for the conjecture.
   - The shown script is also truncated in the supplied transcript and appears to use approximate coloring for induced subgraphs, which is unsound for deciding the theorem.

Thus the three runs established no new theorem, counterexample, exact small-\(n\) value, LP bound, or verified construction.

## Strongest legitimate lead

The best computationally meaningful direction is the **Mycielski family**:

- \(M_2=K_2\);
- each Mycielski step raises chromatic number by one while preserving triangle-freeness;
- \(M_6\) has 47 vertices, \(\chi(M_6)=6\), and clique number \(2\), hence is certainly \(K_6\)-free.

This gives an explicit, highly structured \(6\)-chromatic \(K_6\)-free graph. The upgraded experiment below:

1. constructs \(M_6\);
2. computes its exact chromatic number using an exact DSATUR branch-and-bound routine;
3. verifies triangle-freeness;
4. searches random vertex partitions;
5. checks \(\chi(G[S])\ge3\) exactly via non-bipartiteness;
6. checks \(\chi(G[S^c])\ge4\) exactly by proving it is not 3-colorable.

A found partition is a valid witness for this construction. Failure to find one is not a counterexample, because the partition search is randomized and incomplete.

```python
import random
import time
from collections import deque

LIMIT = 20.5
SEED = 628
rng = random.Random(SEED)


def mycielski(adj):
    """Return the Mycielski graph of a simple graph represented by bit masks."""
    n = len(adj)
    out = [0] * (2 * n + 1)

    # Original-original edges.
    for i in range(n):
        out[i] |= adj[i]

    # Twin u_i has the same neighbors among the original vertices as v_i.
    for i in range(n):
        ui = n + i
        for j in range(n):
            if (adj[i] >> j) & 1:
                out[ui] |= 1 << j
                out[j] |= 1 << ui

    # New apex joined to all twins.
    w = 2 * n
    for i in range(n):
        ui = n + i
        out[w] |= 1 << ui
        out[ui] |= 1 << w

    return out


def make_mycielski_6():
    # M_2 = K_2.
    adj = [2, 1]
    for _ in range(4):  # M_3, ..., M_6
        adj = mycielski(adj)
    return adj


def clique_number_at_least_6(adj):
    """Exact enough for this purpose: test whether any vertex has 5 mutually adjacent neighbors."""
    n = len(adj)

    def search(cand, chosen):
        if chosen >= 6:
            return True
        if cand.bit_count() < 6 - chosen:
            return False
        while cand:
            lb = cand & -cand
            v = lb.bit_length() - 1
            cand ^= lb
            if search(cand & adj[v], chosen + 1):
                return True
        return False

    return search((1 << n) - 1, 0)


def is_bipartite(adj, mask):
    """Exact bipartiteness test on the induced subgraph."""
    color = {}
    bits = mask
    while bits:
        lb = bits & -bits
        start = lb.bit_length() - 1
        bits ^= lb
        if start in color:
            continue
        color[start] = 0
        q = deque([start])
        while q:
            v = q.popleft()
            nb = adj[v] & mask
            while nb:
                x = nb & -nb
                u = x.bit_length() - 1
                nb ^= x
                if u not in color:
                    color[u] = color[v] ^ 1
                    q.append(u)
                elif color[u] == color[v]:
                    return False
    return True


def colorable_at_most(adj, mask, k, deadline):
    """Exact k-colorability by DSATUR backtracking."""
    if mask == 0:
        return True

    verts = [i for i in range(len(adj)) if (mask >> i) & 1]
    color = [-1] * len(adj)
    neigh_col_masks = [0] * len(adj)

    def rec(left, used):
        if time.monotonic() > deadline:
            raise TimeoutError
        if left == 0:
            return True

        # DSATUR: maximum saturation, then maximum residual degree.
        best = -1
        best_key = (-1, -1)
        x = left
        while x:
            lb = x & -x
            v = lb.bit_length() - 1
            x ^= lb
            key = (neigh_col_masks[v].bit_count(),
                   (adj[v] & left).bit_count())
            if key > best_key:
                best_key, best = key, v

        forbidden = neigh_col_masks[best]
        avail = ((1 << k) - 1) & ~forbidden

        # Try existing colors first, then a new color.
        c = 0
        while avail:
            bit = avail & -avail
            avail ^= bit
            if c >= used and used == k:
                continue
            old = []
            affected = adj[best] & left
            while affected:
                lb = affected & -affected
                u = lb.bit_length() - 1
                affected ^= lb
                old.append((u, neigh_col_masks[u]))
                neigh_col_masks[u] |= bit
            color[best] = c
            if rec(left ^ (1 << best), max(used, c + 1)):
                return True
            color[best] = -1
            for u, val in old:
                neigh_col_masks[u] = val
            c += 1
        return False

    return rec(mask, 0)


def exact_chromatic_number(adj, deadline):
    n = len(adj)
    full = (1 << n) - 1
    if n == 0:
        return 0
    for k in range(1, n + 1):
        if not colorable_at_most(adj, full, k, deadline