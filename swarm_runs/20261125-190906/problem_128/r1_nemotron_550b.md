We are given a Lean 4 formalization of Erdős Problem 128. Let's parse the problem carefully.

**Problem Statement (informal):**
Let G be a graph with n vertices such that every induced subgraph on ≥ n/2 vertices has more than n²/50 edges. Must G contain a triangle?

**Formal Lean Statement:**
```lean4
theorem erdos_128 :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      (∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
        50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) → ¬ G.CliqueFree 3 := by sorry
```

**Interpretation:**
- `V` is a finite type (vertex set), `n = Fintype.card V`.
- `G` is a simple graph on `V`.
- Condition: For every subset `V' ⊆ V` such that `2 * |V'| + 1 ≥ n` (i.e., `|V'| ≥ (n-1)/2`, which is equivalent to `|V'| ≥ ⌈n/2⌉` because `|V'|` is integer), the induced subgraph `G[V']` has more than `n²/50` edges. In Lean: `50 * (G.induce V').edgeSet.ncard > n²`.
- Conclusion: `G` is not triangle-free (i.e., contains a triangle).

Note: The condition `2 * V'.ncard + 1 ≥ Fintype.card V` is equivalent to `V'.ncard ≥ (n - 1)/2`. Since `V'.ncard` is an integer, this means `V'.ncard ≥ ⌈(n-1)/2⌉ = ⌈n/2⌉ - 1`? Wait:
- If `n` is even, `n = 2k`, then `2|V'| + 1 ≥ 2k ⇒ 2|V'| ≥ 2k - 1 ⇒ |V'| ≥ k - 0.5 ⇒ |V'| ≥ k = n/2`.
- If `n` is odd, `n = 2k+1`, then `2|V'| + 1 ≥ 2k+1 ⇒ 2|V'| ≥ 2k ⇒ |V'| ≥ k = (n-1)/2 = ⌊n/2⌋`.
But the problem statement says "≥ n/2 vertices". For odd n, n/2 is not an integer, so "≥ n/2" means ≥ ⌈n/2⌉ = k+1. However, Lean's condition gives ≥ k = ⌊n/2⌋. There's a discrepancy!

Let's check: The Lean condition is `2 * V'.ncard + 1 ≥ n`. For `n=5`, this is `2|V'|+1 ≥ 5 ⇒ 2|V'| ≥ 4 ⇒ |V'| ≥ 2`. But `n/2 = 2.5`, so "≥ n/2" would mean `|V'| ≥ 3`. The Lean condition is weaker (allows smaller subsets). 

But the problem statement on erdosproblems.com says: "every induced subgraph on ≥ n/2 vertices has more than n²/50 edges". For n=5, ≥ 2.5 means ≥ 3 vertices. Lean says ≥ 2 vertices. Which is correct?

Looking at the Lean code comment: "Let G be a graph with n vertices such that every induced subgraph on ≥ n/2 vertices has more than n²/50 edges." But the formal condition is `2 * V'.ncard + 1 ≥ Fintype.card V`. This is a known issue in formalization: sometimes they use `2 * |V'| ≥ n` for "≥ n/2", but here it's `2 * |V'| + 1 ≥ n`. 

Let's check the original Erdős problem. The problem is from Erdős, maybe it's exactly as stated. The formalization might have a typo? Or perhaps the original problem uses "≥ n/2" meaning "≥ ⌈n/2⌉"? But `2|V'|+1 ≥ n` is equivalent to `|V'| ≥ (n-1)/2`, which is `⌊n/2⌋`. 

Wait, for n even, n=2k: `2|V'|+1 ≥ 2k ⇒ |V'| ≥ k - 0.5 ⇒ |V'| ≥ k = n/2`. So for even n it matches "≥ n/2". For odd n=2k+1: `2|V'|+1 ≥ 2k+1 ⇒ |V'| ≥ k = (n-1)/2 = ⌊n/2⌋`. But "≥ n/2" would be ≥ k+0.5 ⇒ ≥ k+1 = ⌈n/2⌉. So Lean's condition is weaker for odd n (requires the condition for smaller subsets). 

If the theorem is true with the weaker condition (Lean's), then it's also true with the stronger condition (original problem). But if we find a counterexample for Lean's condition, it might not be a counterexample for the original problem. However, the Lean theorem is what we need to prove or disprove. The problem says "falsifiable", so maybe there is a counterexample even with Lean's condition? Or maybe the Lean condition is exactly what Erdős meant? 

Let's check the reference: erdosproblems.com/128. I can't access it now, but we can reason. The problem asks: "Must G contain a triangle?" If the answer is "yes", then it's a theorem. If "no", there's a counterexample. The Lean formalization is the exact statement we need to address. Since it's marked "falsifiable", likely there is a counterexample (i.e., a triangle-free graph satisfying the condition). But we need to verify.

**Mathematical Reduction:**
We need to find a triangle-free graph G on n vertices such that for every subset V' with |V'| ≥ ⌈(n-1)/2⌉ (i.e., 2|V'|+1 ≥ n), the induced subgraph has > n²/50 edges. Equivalently, the minimum number of edges in an induced subgraph of size ≥ ⌈(n-1)/2⌉ is > n²/50.

Since G is triangle-free, by Turán's theorem, the maximum number of edges in a triangle-free graph on n vertices is ⌊n²/4⌋ (complete bipartite). But we need a lower bound on edges of large induced subgraphs.

We can think of constructions: complete bipartite graphs are triangle-free. Let's test complete bipartite graphs K_{a,b} with a+b=n. For any subset V', the induced subgraph is also bipartite (since subgraph of bipartite is bipartite). The number of edges in induced subgraph depends on how many vertices from each part are in V'. To minimize edges, we would take as many vertices as possible from the larger part? Actually, to minimize edges in an induced subgraph of a given size, we should take vertices that have few edges between them. In a complete bipartite graph, edges only exist between the two parts. So if we take a subset entirely from one part, it has 0 edges. But the condition requires that *every* subset of size ≥ ⌈(n-1)/2⌉ has > n²/50 edges. So we cannot have a subset of that size with 0 edges. That means neither part can have size ≥ ⌈(n-1)/2⌉. So both parts must have size < ⌈(n-1)/2⌉. For n even, n=2k, ⌈(n-1)/2⌉ = k. So both parts < k, but a+b=2k, impossible. For n odd, n=2k+1, ⌈(n-1)/2⌉ = k. Both parts < k, but a+b=2k+1, impossible. So complete bipartite graphs won't work because one part will be too large, allowing an independent set of size ≥ ⌈(n-1)/2⌉ with 0 edges.

Thus we need a triangle-free graph with no large independent set. The condition is essentially that the independence number α(G) < ⌈(n-1)/2⌉. But we also need that every large subset has many edges.

This is reminiscent of Ramsey theory and constructions of triangle-free graphs with high minimum degree. For example, the Clebsch graph (16 vertices, triangle-free, 5-regular) has independence number 5? Actually Clebsch graph has α=5, n=16, ⌈(16-1)/2⌉=8, so α=5 < 8. But we need to check edges in all subsets of size ≥ 8. The Clebsch graph has 40 edges total. n²/50 = 256/50 = 5.12, so >5.12 edges means ≥6 edges. Does every 8-vertex induced subgraph have ≥6 edges? Probably yes, but we need to check.

But the problem asks for a general statement for all n? No, it's "Let G be a graph with n vertices such that... Must G contain a triangle?" This is a statement for a given n? Actually it's a universal statement: for all n, for all graphs G on n vertices satisfying the condition, G contains a triangle. To falsify, we need to find some n and some triangle-free G on n vertices satisfying the condition.

So we need to find a counterexample: a triangle-free graph G on n vertices where every subset of size ≥ ⌈(n-1)/2⌉ has > n²/50 edges.

Let's try to search computationally for small n.

**Approach:**
We'll write a Python script to search for triangle-free graphs on n vertices (for small