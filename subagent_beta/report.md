# Elite Solver Subagent Beta — Verification Report (Erdős #128 & #628)

All scripts and exact outputs reside in `C:\Users\Kerem\.gemini\antigravity\scratch\erdos-hunter\subagent_beta\`.

---

## 1. Erdős Problem #128 (`128.lean`, \$250 Prize)

### 1.1 Exact Lean 4 Formalization vs. Prose Statement (Critical Odd-$n$ Gap)
In `C:\Users\Kerem\.gemini\antigravity\scratch\erdos-hunter\lean_statements\128.lean` (lines 37–41):
```lean
theorem erdos_128 :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      (∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
        50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) → ¬ G.CliqueFree 3
```
- **Lean subset size threshold:** `2 * |V'| + 1 >= n` is equivalent for integers to `|V'| >= ceil((n - 1)/2) = floor(n/2)` (for $n \ge 1$).
- **Prose subset size threshold:** `|V'| >= n/2` literally means `|V'| >= ceil(n/2)`.
- **Edge threshold:** `50 * e(G[V']) > n^2`, i.e., `e(G[V']) >= floor(n^2 / 50) + 1`.

**Key Structural Finding (`verify_c5_odd_blowup.py`):**
1. Under the **literal prose inequality** (`|V'| >= ceil(n/2)`), **an infinite family of triangle-free graphs** violates the threshold: the balanced blow-up $C_5[2s+1]$ on $n = 10s+5$ vertices ($s \ge 0$, starting at $C_5$ itself for $s=0$).
   - **Proof:** In $C_5[t]$ with $t = 2s+1$, any induced subset $V'$ of size $m = 5s+3 = 2t + (s+1)$ must use at least 3 parts (since $2t = 4s+2 < m$). Since at the minimum of $\sum x_i x_{i+1}$ over $[0,t]^5$ at most one part lies strictly inside $(0,t)$ (or an independent set of parts reduces linearly to $\le 1$ partial part), the minimum occurs at two non-adjacent full parts plus $s+1$ vertices in an adjacent part, giving:
     $$\min_{|V'| \ge 5s+3} e(G[V']) = (2s+1)(s+1) = 2s^2 + 3s + 1 > 2s^2 + 2s + \frac{1}{2} = \frac{(10s+5)^2}{50}.$$
   - Verified exhaustively across $t=1..15$ and $s=1..19$ (e.g., $C_5$: $1 > 0.50$; $C_5[3]$ ($n=15$): $6 > 4.50$; $C_5[5]$ ($n=25$): $15 > 12.50$; $C_5[15]$ ($n=75$): $120 > 112.50$). Other odd-$n$ graphs beating $n^2/50$ at $\lceil n/2 \rceil$ include Andrásfai $A_4$ ($n=11, \lceil n/2 \rceil=6$: $3/121 = 0.024793$), $\text{Circ}(13,\{1,5\})$ ($n=13, 7$: $4/169 = 0.023669$), and $\text{Circ}(17,\{1,4,6\})$ ($n=17, 9$: $6/289 = 0.020761$).
2. **Why `128.lean` is immune to this:** `128.lean` deliberately uses `2 * V'.ncard + 1 >= n` (`|V'| >= floor(n/2)`), under which $C_5[2s+1]$ has $\min_{|V'|=5s+2} e = 2s^2 + s < 2s^2 + 2s + 0.5$, and $C_5[2s]$ ($n=10s$) has $\min_{|V'|=5s} e = 2s^2 = n^2/50$, failing strict `>`.

### 1.2 Small-$n$ Exhaustive & Heuristic Search (`128.lean` Exact Inequality)
- **$n = 1..7$ (Exhaustive via NetworkX Graph Atlas, all 172 triangle-free graphs):** `max min_e(floor(n/2)) = 0` for all $n \in \{1..7\}$ (`erdos128_check.py`). No counterexample.
- **$n = 8$ (Exhaustive over all 410 non-isomorphic triangle-free graphs / 10 maximal TF):** Exact maximum of $\min_{|V'|=4} e(G[V'])$ is **1** ($1/64 = 0.015625$, achieved by 3-regular 12-edge $A_3$), strictly below required $\ge 2$ (`erdos128_deep_search.py`).
- **$n = 9$ (16 maximal TF graphs + Ramsey $R(3,4)=9$):** Since $R(3,4)=9$, every triangle-free graph on 9 vertices has $\alpha(G) \ge 4$, forcing $\min_{|V'|=4} e(G[V']) = 0 < 2$.
- **$n = 8..16$ Multi-Start Maximal-TF Simulated Annealing (`erdos128_small_n_recheck.py`):**

| $n$ | $m_{\text{Lean}} = \lfloor n/2 \rfloor$ | Observed Max $\min e$ | Ratio $/ n^2$ | Lean Req ($\lfloor n^2/50 \rfloor + 1$) | Counterexample? |
|---:|---:|---:|---:|---:|:---:|
| 8 | 4 | 1 | 0.015625 | 2 | False (Exact) |
| 9 | 4 | 0 | 0.000000 | 2 | False (Exact, $R(3,4)=9$) |
| 10 | 5 | **2** | **0.020000** | 3 | False (Petersen / $C_5[2]$) |
| 11 | 5 | 1 | 0.008264 | 3 | False |
| 12 | 6 | 2 | 0.013889 | 3 | False |
| 13 | 6 | 2 | 0.011834 | 4 | False |
| 14 | 7 | 3 | 0.015306 | 4 | False |
| 15 | 7 | 3 | 0.013333 | 5 | False |
| 16 | 8 | 4 | 0.015625 | 6 | False |

- **All Maximal Triangle-Free Circulants ($n = 5..19$, `erdos128_deep_search.py`):** Max discrete floor ratio is `0.020000` at $\text{Circ}(10, \{2,3\}) \cong C_5[2]$ (`floor_e = 2 < req 3`).

### 1.3 Large-$n$ Triangle-Free Graphs, SRGs, Blow-up Limits, & Twisted Blow-ups
For any template graph $H$ on $k$ vertices with weights $w \in \Delta_k$, since $\frac{\partial^2}{\partial x_i^2}(\frac{1}{2}x^T A x) = 0$, any global minimum of $\min_{0 \le x \le w, \sum x = 1/2} \frac{1}{2}x^T A x$ has at most one coordinate strictly inside $(0, w_i)$ (verified against random feasible sampling in `run_unit_sanity.py`).

**Maximum observed $\min_{|V'| \ge \lfloor n/2 \rfloor} e(G[V']) / n^2$ and asymptotic blow-up limit across ALL tested families:** **1/50 = 0.020000**, achieved exclusively by:
1. **$C_5$ ($k=5$) and balanced blow-ups $C_5[2s]$ ($n=10s$):** continuous limit **0.020000** (`1/50`). Pure algebra proves no unbalanced weight vector $w \in \Delta_5$ on $C_5$ can exceed `0.020000` (since $\frac{1}{5}\sum_i (w_i + w_{i+2}) = 0.4 \implies \max_i (w_i + w_{i+2}) \ge 0.4$, capping $\min(w_i, w_{i+2})(0.5 - w_i - w_{i+2}) \le 0.2 \times 0.1 = 0.02$).
2. **Petersen graph ($k=10, d=3$) and its balanced blow-ups $P[t]$ ($n=10t$):** exact discrete `2/100 = 0.020000` and continuous limit **0.020000** (`1/50`).

**Results for all major triangle-free families (`erdos128_check.py`, `erdos128_srg_test.py`, `erdos128_deep_search.py`, `erdos128_random_regular.py`):**

| Graph / Family | $k$ ($n$) | $d$ | Exact/SA Floor Ratio ($/ n^2$) | Uniform Blow-up Limit | Weighted Opt Blow-up Limit |
|---|---:|---:|---:|---:|---:|
| **$C_5$** | 5 | 2 | 0.000000 (`0/25`) | **0.020000** (`1/50`) | **0.020000** |
| **Petersen (`GP(5,2)`)** | 10 | 3 | **0.020000** (`2/100`) | **0.020000** (`1/50`) | **0.020000** |
| $\text{Circ}(10,\{2,3\}) = C_5[2]$ | 10 | 4 | **0.020000** (`2/100`) | **0.020000** (`1/50`) | **0.020000** |
| $\text{Circ}(13,\{1,5\})$ ($R(3,5)-1$) | 13 | 4 | 0.011834 (`2/169`) | 0.017751 | 0.017751 |
| **Higman-Sims SRG(100,22,0,6)** | 100 | 22 | **0.017500** (`175/10000`, matches spectral LB $175$) | — | — |
| **$M_{22}$ SRG(77,16,0,4)** | 77 | 16 | 0.016866 (`100/5929`, spectral LB $\ge 93$) | — | — |
| Andrásfai $A_4$ | 11 | 4 | 0.008264 (`1/121`) | 0.016529 | 0.016529 |
| Andrásfai $A_3$ ($M_8$) | 8 | 3 | 0.015625 (`1/64`) | 0.015625 | 0.015625 |
| Clebsch (Folded $Q_5$) | 16 | 5 | 0.015625 (`4/256`) | 0.015625 | — |
| $\text{Circ}(17,\{1,4,6\})$ / $A_6$ | 17 | 6 | 0.010381 (`3/289`) | 0.015571 | — |
| Andrásfai $A_5$ | 14 | 5 | 0.015306 (`3/196`) | 0.015306 | 0.015306 |
| Andrásfai $A_8$ / $A_{10}$ | 23 / 29 | 8 / 10 | 0.011342 / 0.011891 | 0.015123 / 0.014863 | — |
| Chvátal | 12 | 4 | 0.013889 (`2/144`) | 0.013889 | 0.015967 |
| **Gewirtz SRG(56,10,0,2)** | 56 | 10 | **0.013393** (`42/3136`, matches spectral LB $42$) | — | — |
| Hoffman-Singleton (50,7,0,1) | 50 | 7 | 0.010000 (`25/2500`, matches spectral LB $25$) | 0.010000 | — |
| Grötzsch $M_4$ | 11 | — | 0.000000 (`0/121`) | 0.008264 | — |
| Mycielski($P$) / $M_5$ | 21 / 23 | — | 0.000000 | 0.003401 / 0.002836 | — |

- **Twisted Blow-ups, Lifts, Random Regular, & Optimization:**
  - All 32 signed 2-lifts of $C_5$ $\times$ 20 maximal TF completions (`k=10`, 640 graphs): max `0.020000` (reached only by $C_5[2]$).
  - 25 twisted 3-lifts of $C_5$ + maximal TF completions (`k=15`): max `0.020000` (`edges=45`, $C_5[3]$).
  - 15 twisted 2-lifts of Petersen + maximal TF completions (`k=20`): max `0.012500` (`e_min=5`, `edges=61`).
  - Weighted continuous optimization on all $k=8$ maximal TF graphs: max `0.016146`; best $k=9$ maximal TF: `0.017827`.
  - Direct SA over maximal TF graphs ($k \in \{10,12,13,14\}$): max `0.014793`.
  - Generalized Petersen $GP(n,k)$ ($n=5..11$): max `0.020000` ($GP(5,2)$).
  - Random $d$-regular triangle-free graphs (`15` samples each for $(n,d) \in \{(10,3),(12,4),(14,4),(16,5),(18,5),(20,6),(24,6),(30,7)\}$): max `0.020000` at $(10,3)$, all $n \ge 12$ gave $\le 0.015625$.

**Erdős #128 Verdict:** No counterexample to the formal Lean statement (`128.lean`) exists in any tested finite or asymptotic regime. The sharp maximum ratio $\min_{|V'| \ge \lfloor n/2 \rfloor} e(G[V'])/n^2$ is **1/50 = 0.020000**, achieved tightly by $C_5[2s]$ and $P[t]$, with Higman-Sims (`0.017500`), $R(3,5)-1$ (`0.017751`), and $M_{22}$ (`0.016866`) strictly below `0.020000`. However, the prose inequality $|V'| \ge \lceil n/2 \rceil$ is broken by $C_5[2s+1]$ for all $s \ge 0$.

---

## 2. Erdős Problem #628 (`628.lean`, Erdős–Lovász Tihany Conjecture, $k=6, a=3, b=4$)

In `C:\Users\Kerem\.gemini\antigravity\scratch\erdos-hunter\lean_statements\628.lean` (lines 46–53), for $\chi(G)=6$ and $\omega(G) \le 5$, a $(3,4)$-partition $(S, V \setminus S)$ with $\chi(G[S]) \ge 3$ and $\chi(G[V \setminus S]) \ge 4$ exists **if and only if** there exists an induced odd cycle $C \subseteq G$ such that $\chi(G \setminus C) \ge 4$ (non-3-colorable).

**Solver Verification (`run_unit_sanity.py`):** Exact DSATUR $k$-coloring solver `is_k_colorable` passed 50/50 brute-force random graph cross-checks ($n=6..8, k=3..5$).

### 2.1 Tested $\chi=6, \omega \le 5$ Graph Families
1. **Structured, Critical, Kneser/Schrijver, Hajós & Mycielski Graphs (`erdos628_check.py`, `erdos628_deep_search.py`):**
   - `K3 + C5` ($n=8, \omega=5$): **True** — triangle `(0, 3, 4)` leaves non-3-colorable $K_2 + P_3$ ($\chi=4$).
   - `C5 + C5` ($n=10, \omega=4$): **True** — triangle `(0, 1, 5)`.
   - `K2 + Grötzsch M4` ($n=13, \omega=4$): **True** — triangle `(0, 2, 3)`.
   - `K1 + M5` ($n=24, \omega=3$): **True** — triangle `(0, 1, 2)`.
   - `C5 + K2 + K1` ($n=8, \omega=5$): **True** — triangle `(0, 1, 5)`.
   - `Mycielski M6` ($n=47, \omega=2$, triangle-free): **True** — $M_6 \setminus C_5(0..4)$ is non-3-colorable.
   - `Schrijver SG(8,2)` ($n=20, \omega=4$) & `Kneser KG(8,2)` ($n=28, \omega=4$): **True** — triangles `(0, 5, 17)` and `(0, 13, 22)`.
   - `Schrijver SG(10,3)` ($n=50, \omega=3$): **True** — triangle `(0, 16, 49)`.
   - `Complement(C11)` ($n=11, \omega=5$), `C5[K2] + K1` ($n=11, \omega=5$), `Complement(Grötzsch)` ($n=11, \omega=5$), `Complement(Chvátal)` ($n=12, \omega=4$): **True** (triangle witnesses).
   - `Hajós(K6, K6)` ($n=11, \omega=5$), `Hajós(H11, K6)` ($n=16, \omega=5$), `Hajós(K3+C5, K3+C5)` ($n=15, \omega=4$): **True** (triangle witnesses).
   - `Comp(Line(Petersen))` ($n=15, \omega=5$) & `C7 + C5` ($n=12, \omega=4$): **True**.
2. **Vertex-Transitive Circular Cliques $K_{p/q}$ ($5 < p/q < 6$, `erdos628_circular_cliques.py`):**
   - $K_{11/2}$ ($\alpha=2$), $K_{16/3}, K_{17/3}$ ($\alpha=3$), $K_{21/4}, K_{22/4}, K_{23/4}$ ($\alpha=4$), $K_{26/5}$ ($\alpha=5$): **All 7 True** for both `(3,4)` and `(2,5)` (witness triangles $(0, q, 2q)$).
3. **Circulants ($n=8..16$, `erdos628_circulants_and_critical.py`):**
   - Tested 344 circulants with $\deg \ge 5, \omega \le 5$; all **45** graphs with $\chi=6$ satisfied both `(3,4)`-Tihany and `(2,5)`-Tihany.
4. **Minimal 6-Critical $K_6$-Free Graphs (`erdos628_circulants_and_critical.py`):**
   - Reduced random $\chi=6, \omega \le 5$ graphs to **25 distinct vertex-and-edge 6-critical graphs** ($n=8..12$, including $\alpha=3$ cases at $n=9..12$): **25/25 True** for `(3,4)` and `(2,5)`.
5. **Random & Simulated Annealing Search (`erdos628_check.py`, `erdos628_deep_search.py`):**
   - **299** random $K_6$-free graphs with $\chi=6$ ($n=10..15$): **0 counterexamples**.
   - **120** SA trajectories ($n=9..16$, 15 starts each) actively minimizing the number of triangles leaving $\chi(G \setminus T) \ge 4$: minimum count across all runs never fell below **15**.

**Erdős #628 Verdict:** No counterexample found across any tested structured family, circular clique, circulant, 6-critical graph, or SA optimization run; all evidence strongly supports `erdos_628` for $(k=6, a=3, b=4)$.
