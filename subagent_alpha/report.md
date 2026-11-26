# Elite Solver Subagent Alpha — Rigorous Computational & Mathematical Findings Report

**Scope:** Exact mathematical and computational investigation of **Erdős Problem #835** (`lean_statements/835.lean`) and **Erdős Problem #552** (`lean_statements/552.lean`). Every bound, table, counterexample/witness, and impossibility check below was verified directly via Python scripts in `subagent_alpha/` or read directly from cited primary papers/databases.

---

## Part 1: Erdős Problem #835 (`835.lean`)

### 1.1 Problem Equivalence and Exact Design Characterization
Let $J(2k, k)$ be the middle Johnson graph on $\binom{2k}{k}$ vertices, where two $k$-subsets of $[2k]$ are adjacent iff $|S_1 \cap S_2| = k-1$.
- Every $(k+1)$-subset $A \subset [2k]$ induces a $K_{k+1}$ clique in $J(2k,k)$, so $\chi(J(2k,k)) \ge k+1$. As formalized in `835.lean`, `Property k` holds iff $\chi(J(2k,k)) = k+1$.
- Any independent set $\mathcal{F} \subset V(J(2k,k))$ is a binary constant-weight code of length $2k$, weight $k$, and minimum Hamming distance $d \ge 4$, so $|\mathcal{F}| \le \alpha(J(2k,k)) = A(2k, 4, k)$.
- Double-counting $(k-1)$-subsets inside $\mathcal{F}$ (each $k$-set contains $k$ subsets of size $k-1$, and no two $k$-sets in $\mathcal{F}$ share a $(k-1)$-subset):
  $$|\mathcal{F}| \le \frac{1}{k}\binom{2k}{k-1} = \frac{1}{k+1}\binom{2k}{k} = C_k \quad (\text{the } k\text{-th Catalan number}).$$
- **Exact Characterization:** $\chi(J(2k,k)) = k+1$ holds **if and only if** every one of the $k+1$ color classes achieves size $|\mathcal{F}_c| = C_k$, which holds iff every $(k-1)$-subset lies in **exactly one** block of $\mathcal{F}_c$ — i.e., $V(J(2k,k))$ partitions into $k+1$ **Steiner systems $S(k-1, k, 2k)$**, forming a **large set $LS(k-1, k, 2k)$**.

---

### 1.2 Composite $k+1$ (Including All Odd $k \ge 3$ and $k = 11, 13, 14, 15, \dots$)
- **Ma–Tang Theorem (`On_Problem_835.pdf`, Theorem 2.2):** If $k > 2$ and $k+1$ is composite, then $\chi(J(2k,k)) \ge k+2$.
- **Stronger Code-Size Proof via the Recursive Johnson Bound (`johnsonBound` in `835.lean`):**
  Expanding `jb(2k, 4, k)` without floors gives $\frac{1}{k+1}\binom{k+t}{t}$ at step $t \in \{1,\dots,k\}$.
  - When $k+1 = p$ is prime, $p \mid \binom{p-1+t}{t}$ for every $1 \le t \le p-1$, so **zero floor loss occurs** and $\text{jb}(2k, 4, k) = C_k$.
  - When $k+1$ is composite, factor $k+1 = p^a m$ ($p$ prime, $a \ge 1$, $p \nmid m$). Choose $t = p^{a-1}$ if $m=1$ (so $a \ge 2$, $2 \le t \le k$) or $t = p^a$ if $m > 1$ (so $2 \le t \le k$). By Kummer's theorem on base-$p$ carries of $k + t$, $v_p\binom{k+t}{t} < a = v_p(k+1)$, forcing a strict floor loss at step $t$ (or earlier), hence $(k+1)\,\text{jb}(2k,4,k) < \binom{2k}{k}$ and $\chi(J(2k,k)) \ge k+2$.
  - **Verified computationally** (`verify_835_composite_proof.py`) for **all composite $k+1 \in [4, 501]$** (zero anomalies in `[3..200]` or `[3..500]`).

---

### 1.3 Why Delsarte's LP Bound Fails for All Even $k \ge 4$ (and All Prime $k+1$)
Using exact Eberlein polynomials
$$P_i(j) = \sum_{s=0}^i (-1)^s \binom{j}{s}\binom{k-j}{i-s}\binom{k-j}{i-s}$$
and Mendelsohn's block-intersection equations for a hypothetical $S(k-1, k, 2k)$:
$$\sum_{j=r}^{k-2} \binom{j}{r} n_j = \binom{k}{r}(\lambda_r - 1), \qquad \lambda_r = \frac{\binom{2k-r}{k-1-r}}{\binom{k-r}{k-1-r}} \quad (0 \le r \le k-2),$$
we proved via **exact `fractions.Fraction` arithmetic** (`analyze_835_designs.py`, `verify_835_exact.py`):
1. For **every prime $p = k+1$** tested ($k \in \{4, 6, 10, 12, 16, 18, 22, 28, 30, 36, 40, 42\}$), all Steiner divisibilities $\lambda_r \in \mathbb{Z}$ hold **and** all Mendelsohn intersection numbers $n_0, \dots, n_{k-2}$ are **non-negative integers**, with $n_0 = 1$, $n_1 = 0$, and $n_j = n_{k-j}$ (complement closure).
2. For **all even $k \in \{4, 6, 8, 10, 12, 14, 16, 18\}$**, setting $a_i = n_{k-i}$ ($i \ge 2$), $a_0 = 1, a_1 = 0$ gives $\sum_{i=0}^k a_i = C_k = \frac{1}{k+1}\binom{2k}{k}$, and satisfies every Delsarte primal constraint $\sum_{i=0}^k a_i \frac{P_i(j)}{v_i} \ge 0$ with exact equality for $j = 1, \dots, k-1$ and strict positivity at $j = k$ (matching Hoffman's ratio bound on $J(2k,k)$, which is $k^2$-regular with $\lambda_{\min} = -k$).
3. Therefore **Delsarte's classical LP bound equals $C_k$ for every even $k \ge 4$** (even at composite $k+1=9, 15$, where `jb(16,4,8)=1396 < 1430` and `jb(28,4,14)=2645438 < 2674440` strictly beat Delsarte LP!) and **cannot settle any prime $k+1$ case**.

| $k$ | $k+1$ | $\binom{2k}{k}$ | `jb(2k,4,k)` | $C_k = \binom{2k}{k}/(k+1)$ | Delsarte LP (exact) | $\lceil \binom{2k}{k}/\text{jb}\rceil$ | Status of $\chi(J(2k,k)) > k+1$ |
|---:|---|---:|---:|---:|---:|---:|---|
| 3 | 4 (comp) | 20 | 4 | 5 | 4 | 5 | **Solved** ($\ge 5$, Johnson/Ma–Tang) |
| 4 | 5 (prime) | 70 | 14 | 14 | 14 | 5 | **Solved** ($\chi=6$; max disjoint $S(3,4,8)=2$) |
| 5 | 6 (comp) | 252 | 36 | 42 | 36 | 7 | **Solved** ($\ge 7$, Johnson/Ma–Tang) |
| 6 | 7 (prime) | 924 | 132 | 132 | 132 | 7 | **Solved** ($\ge 8$; max disjoint $S(5,6,12)=2$) |
| 7 | 8 (comp) | 3,432 | 364 | 429 | $381.\overline{3}$ | 10 | **Solved** ($\ge 10$, Johnson/Ma–Tang) |
| 8 | 9 (comp) | 12,870 | 1,396 | 1,430 | 1,430 | 10 | **Solved** ($\ge 10$, Johnson/Ma–Tang) |
| 9 | 10 (comp) | 48,620 | 4,420 | 4,862 | 4,420 | 11 | **Solved** ($\ge 11$, Johnson/Ma–Tang) |
| **10** | **11 (prime)** | **184,756** | **16,796** | **16,796** | **16,796** | **11** | **Solved ($\ge 12$): $S(9,10,20) \xrightarrow{5\times} S(4,5,15) = \emptyset$** |
| 11 | 12 (comp) | 705,432 | 54,264 | 58,786 | 54,264 | 13 | **Solved** ($\ge 13$, Johnson/Ma–Tang) |
| **12** | **13 (prime)** | **2,704,156** | **208,012** | **208,012** | **208,012** | **13** | **Solved ($\ge 14$): $S(11,12,24) \xrightarrow{7\times} S(4,5,17) = \emptyset$** |
| 13 | 14 (comp) | 10,400,600 | 685,686 | 742,900 | $693{,}373.\overline{3}$ | 16 | **Solved** ($\ge 16$, Johnson/Ma–Tang) |
| 14 | 15 (comp) | 40,116,600 | 2,645,438 | 2,674,440 | 2,674,440 | 16 | **Solved** ($\ge 16$, Johnson/Ma–Tang) |
| 15 | 16 (comp) | 155,117,520 | 9,124,560 | 9,694,845 | 9,124,560 | 17 | **Solved** ($\ge 17$, Johnson/Ma–Tang) |
| **16** | **17 (prime)** | **601,080,390** | **35,357,670** | **35,357,670** | **35,357,670** | **17** | **OPEN** ($S(15,16,32) \xrightarrow{11\times} S(4,5,21)$ open) |
| 17 | 18 (comp) | 2,333,606,220 | 122,821,380 | 129,644,790 | 122,821,380 | 19 | **Solved** ($\ge 19$, Johnson/Ma–Tang) |
| **18** | **19 (prime)** | **9,075,135,300** | **477,638,700** | **477,638,700** | **477,638,700** | **19** | **OPEN** ($S(17,18,36) \xrightarrow{13\times} S(4,5,23)$ open) |

---

### 1.4 Exact Disjointness Obstructions for $k=4, 6$ and Settling $k=10, 12$
1. **$k = 4$ ($J(8,4)$):** Exhaustive enumeration (`analyze_835_k4_k6_all.py`) of all $8!/|\mathrm{AGL}(3,2)| = 30$ distinct $S(3,4,8)$ systems shows $\mathrm{AGL}(3,2) \le A_8$, splitting the 30 systems into two $A_8$-orbits of size 15 (`even` and `odd`). Pairwise intersections take sizes `{(0, 120), (2, 210), (6, 105)}`, with **0 disjoint pairs within `even`**, **0 within `odd`**, and **120 across orbits** (an 8-regular bipartite disjointness graph). Thus the maximum number of mutually disjoint $S(3,4,8)$'s is **2** ($< 5$), forcing $\chi(J(8,4)) > 5$.
2. **$k = 6$ ($J(12,6)$):** Using the explicit $PSL_2(11)$-orbit of $\{\infty, 1, 3, 4, 5, 9\}$ to construct the small Witt design $W_{12} = S(5,6,12)$ (132 blocks, covering all 792 5-subsets), and using the sharp 5-transitivity of $M_{12} \le A_{12}$ to enumerate all $7! = 5040$ copies of $W_{12}$ (`verify_w12_disjoint.py`, split into 2,520 `even` and 2,520 `odd` copies), we exhaustively verified:
   - Intersection sizes with $W_0$ in the **same (`even`) orbit**: `[(12, 1584), (24, 440), (36, 495), (132, 1)]` — **0 disjoint copies**.
   - Intersection sizes with $W_0$ in the **opposite (`odd`) orbit**: `[(0, 144), (12, 990), (24, 1320), (60, 66)]` — **144 disjoint copies**.
   - Checking all pairs among the 144 disjoint copies reveals **0 triangles** in the disjointness graph. Hence the disjointness graph on all 5,040 copies of $W_{12}$ is **144-regular bipartite**, so the maximum number of mutually disjoint $S(5,6,12)$'s is **2** ($< 7$), forcing $\chi(J(12,6)) \ge 8$.
3. **$k = 10$ ($J(20,10)$, $p = 11$): SETTLED ($\chi(J(20,10)) \ge 12$).**
   A proper 11-coloring requires each color class to be a Steiner system $S(9, 10, 20)$ (size $C_{10} = 16,796$; note Brouwer's `Andw.html` lists only $A(20,4,10) \ge 13,452$). Taking a 5-fold derived design of $S(9, 10, 20)$ yields $S(4, 5, 15)$, which was proved nonexistent by Mendelsohn & Hung (*Utilitas Math.* 1, 1972, pp. 5–95). Therefore $\alpha(J(20,10)) = A(20,4,10) < 16,796$, and $\chi(J(20,10)) \ge 12$.
4. **$k = 12$ ($J(24,12)$, $p = 13$): SETTLED ($\chi(J(24,12)) \ge 14$).**
   A proper 13-coloring requires each color class to be an $S(11, 12, 24)$ (size $C_{12} = 208,012$). Taking a 7-fold derived design yields $S(4, 5, 17)$, which was proved nonexistent by Östergård & Pottonen (*J. Combin. Theory Ser. A* 115, 2008, pp. 1570–1573). Therefore $\alpha(J(24,12)) = A(24,4,12) < 208,012$, and $\chi(J(24,12)) \ge 14$.
5. **Can we settle ALL $k \ge 10$?**
   **No — cases with $k+1 = p \ge 17$ prime ($k = 16, 18, 22, \dots$) remain open.** For $k=16$ ($J(32,16)$, $C_{16} = 35,357,670$), 11-fold derivation reduces to $S(4, 5, 21)$, whose existence is itself open (consistent with the Sep 2026 discussion on `erdosproblems.com/835` where Kramer–Mesner searches ruled out $\mathrm{AGL}(5,2)$ and $\mathrm{PGL}(2,31)$-invariant $S(15,16,32)$ and prime-order 19/23/29/31-invariant 17-colorings, leaving general $S(15,16,32)$ and $LS(15,16,32)$ open).

---

## Part 2: Erdős Problem #552 (`552.lean`)

### 2.1 Equivalent Minimum-Degree Formulation & Current Literature State
$R(C_4, S_n) > N$ holds **if and only if** there exists a $C_4$-free graph $G$ on $N$ vertices with $\Delta(\overline{G}) \le n-1$, i.e., $\delta(G) \ge N - n$. Writing $d = N - n$, counting neighbor pairs $\sum_v \binom{d(v)}{2} \le \binom{N}{2}$ gives $d(d-1) \le N - 1 = n + d - 1 \implies (d-1)^2 \le n$, yielding Parsons' upper bound $R(C_4, S_n) \le n + \lceil\sqrt{n}\rceil + 1$ (and $n + \lceil\sqrt{n}\rceil$ at $n = m^2 + 1$).

From **OEIS A006672** and **Luis Boza** (`arXiv:2409.12770v2`, June 2026, `boza_2409_12770.pdf`):
- Exact values are known for $1 \le n \le 38$, $n=40, 41, 43, 45, 47..50, 55, 57..68, 70, 73..82$, and every known exact value satisfies $f(n) = n + \lceil\sqrt{n}\rceil + \{0, 1\}$.
- Remark 12 of Boza notes $f(n) \ge n + \lceil\sqrt{n}\rceil$ holds for all $2 \le n \le 82$ (with gaps remaining at $n \in \{39, 42, 44, 46, 51..54, 56, 69, 71, 72\}$, and **nothing** known beyond $n = 82 = 9^2 + 1$ except at future prime-power neighborhoods $q^2 \pm t$ for $0 \le t \le q$).

---

### 2.2 Explicit Polarity Graphs $ER(q)$ and Exact Verification of $R(C_4, S_{39}) = 46$
We constructed the Erdős–Rényi orthogonal polarity graphs $ER(q)$ over $\mathbb{F}_q$ for $q \in \{2, 3, 4, 5, 7, 8, 9, 11\}$ (`analyze_552_polarity.py`), verifying $C_4$-freeness directly, with $N = q^2 + q + 1$, $q+1$ absolute vertices of degree $q$, and $q^2$ non-absolute vertices of degree $q+1$.

1. **Exact Settlement of $R(C_4, S_{39}) = 46$ (`verify_552_parsons_and_summary.py`):**
   - In Boza's table (`boza_2409_12770.pdf`, p. 4), $f(38) = 45$ and $f(39) \le 46$ (from Zhang–Chen–Cheng `[16]`), while OEIS A006672 ends at $a(38) = 45$.
   - Using HiGHS MILP on $ER(7)$ ($N = 57$), we found and independently verified an explicit **45-vertex induced subgraph** $G' \subset ER(7)$ (deleting 12 vertices, 3 absolute and 9 non-absolute) that is **$C_4$-free** with $\delta(G') = 6$ and $\Delta(G') = 8$.
   - Since $45 - 6 = 39$, this rigorously proves $R(C_4, S_{39}) \ge 46$. Combined with the known upper bound $f(39) \le 46$, this confirms $R(C_4, S_{39}) = 46$.
2. **Exact MILP Optima on $ER(7), ER(8), ER(9)$ (`inspect_hog_structure.py`, `test_552_er9_er11.py`):**
   - **$ER(7)$ ($N=57$):** Exact $\delta_{\max}(N') = 6$ for $N' \in \{41, 42, 43, 44, 45\}$ (witnessing $f(35)\ge 42, \dots, f(39)\ge 46$); exact $\delta_{\max}(38) = 5$ (witnessing $f(33)\ge 39$).
   - **$ER(8)$ ($N=73$):** Exact $\delta_{\max}(63) = 8$ (obtained by deleting the absolute line $L = \{x+y+z=0\}$ of 9 points together with its nucleus $p_0 = (1,1,1)$, yielding an 8-regular $C_4$-free graph on $q^2-1 = 63$ vertices witnessing $f(55) \ge 64$). Notably, exact MILP proves **$\delta_{\max}(64) = 7$** (not $8$!): because $p_0$ has all $9$ neighbors on $L$, deleting $L$ isolates $p_0$, while keeping $p_0$ forces deleting a neighbor of some surviving absolute point (whose degree was $8$), dropping $\delta$ to $7$. Similarly, exact MILP gives $\delta_{\max}(N') = 7$ for $N' \in \{59, 60, 61, 62\}$ and $\delta_{\max}(49) = 6$.
   - **$ER(9)$ ($N=91$):** Exact $\delta_{\max}(N') = 8$ for $N' \in \{78, 79, 80, 81, 82, 83\}$ (note `N'=83` cannot achieve $\delta = 9$ inside $ER(9)$, and even on `N'=82` with degree distribution `{8: 36, 9: 10, 10: 36}`, **0 edges** can be added among degree-8 vertices without creating $C_4$).

---

### 2.3 Spectral Obstruction Theorem: Polarity Deletions & Extensions Cannot Settle Part (ii)
Our central structural discovery for Erdős #552 explains **both** why existing results only cover $n = q^2 \pm O(q)$ **and** why vertex-deletion subgraphs of $ER(q)$ fail inside large prime-power gaps:

1. **No Vertex-Addition Extension Theorem (`check_er_add_and_hog.py`):**
   In $ER(q)$, two vertices $u \ne v$ can share a new neighbor $w$ iff they have 0 common neighbors in $ER(q)$, which happens iff $u \sim v$ and at least one of $u, v$ is absolute. Because no two distinct absolute points have 0 common neighbors (two tangents intersect outside the conic for odd $q$; two points on $L_{\text{abs}}$ share the nucleus $p_0$ for even $q$), the compatibility graph is **bipartite** (`Abs` vs `Non-Abs`), hence triangle-free. Therefore **no vertex can be added to $ER(q)$ with degree $\ge 3$ without creating a $C_4$** (verified computationally for $q \in \{3, 4, 5, 7\}$).

2. **Expander Mixing Lemma (EML) Bound on $ER(q)$ Deletions (`analyze_552_eml_and_gaps.py`):**
   Let $A_{\text{loop}}$ be the adjacency matrix of $ER(q)$ with $+1$ on the diagonal at the $q+1$ absolute vertices. Then $A_{\text{loop}}^2 = J + qI$, so its spectrum is $\{q+1, +\sqrt{q}, -\sqrt{q}\}$ (verified to `0.0e+00` error for $q \in \{5, 7, 8, 9, 11\}$). Consequently, for **every** induced subgraph $S \subset V(ER(q))$ of size $N'$,
   $$2e(S) + |S \cap \mathrm{Abs}| = \mathbf{1}_S^T A_{\text{loop}} \mathbf{1}_S \le (q+1)\frac{N'^2}{N} + \sqrt{q}\,N'\left(1 - \frac{N'}{N}\right),$$
   hence
   $$\delta(S) \le \bar{d}(S) \le \sqrt{q} + (q+1-\sqrt{q})\frac{N'}{q^2+q+1}.$$
   Setting $N' = q^2 + q + 1 - kq$ (so $n = N' - \delta \approx q^2 - (k-1)q$ and $\sqrt{n} \approx q - \frac{k-1}{2}$), this gives
   $$\delta(S) \le \sqrt{n} + \frac{3}{2} - k\left(\frac{1}{2} - \frac{1}{\sqrt{q}}\right) + O\!\left(\frac{k^2}{q}\right).$$
   Thus, once $s = kq$ exceeds $\approx (2c + 4)q$, **no induced subgraph of $ER(q)$ can achieve $\delta(S) \ge \sqrt{n} - c$**.

3. **Failure of $ER(q)$ Deletions at Prime-Power Gap Midpoints:**
   Evaluating the exact EML bound at the midpoints $n_{\text{mid}} \approx ((q_1+q_2)/2)^2$ of record consecutive prime-power gaps ($q_1, q_2 \le 50{,}000$) shows $\sqrt{n_{\text{mid}}} - \text{ub}_{\text{EML}}(ER(q_2))$ turns **strictly positive** starting at $(q_1, q_2) = (19, 23)$ and diverges linearly with the gap $\Delta = q_2 - q_1$:
   - $q_1=19, q_2=23$ ($\Delta=4$, $n_{\text{mid}}=441$, $\sqrt{n}=21.00$): $\bar{d}(S) \le 20.83$ (deficit $+0.17$).
   - $q_1=53, q_2=59$ ($\Delta=6$, $n_{\text{mid}}=3{,}136$, $\sqrt{n}=56.00$): $\bar{d}(S) \le 54.83$ (deficit $+1.17$).
   - $q_1=89, q_2=97$ ($\Delta=8$, $n_{\text{mid}}=8{,}649$, $\sqrt{n}=93.00$): $\bar{d}(S) \le 90.89$ (deficit $+2.11$).
   - $q_1=293, q_2=307$ ($\Delta=14$, $n_{\text{mid}}=90{,}000$, $\sqrt{n}=300.00$): $\bar{d}(S) \le 294.91$ (deficit $+5.09$).
   - $q_1=1{,}331, q_2=1{,}361$ ($\Delta=30$, $n_{\text{mid}}=1{,}811{,}716$, $\sqrt{n}=1{,}346.00$): $\bar{d}(S) \le 1{,}332.95$ (deficit $+13.05$).
   - $q_1=31{,}397, q_2=31{,}469$ ($\Delta=72$, $n_{\text{mid}}=988{,}033{,}489$, $\sqrt{n}=31{,}433.00$): $\bar{d}(S) \le 31{,}398.44$ (deficit $+34.56$).
   (And for $q > q_2$ up to $q \approx n^{2/3}$, the EML bound is even smaller.)
   - **Empirical test on $ER(11)$ ($N=133$, gap $9 \to 11$):** Heuristic + EML scans across $N' \in [91, 133]$ show $ER(11)$ deletions achieve $\text{diff} = 0$ down to $n = 91$ ($N'=100, \delta=9$ verified by MILP), while for $s \in [34, 42]$ ($n \in [83, 90]$) heuristic search only reaches $\delta = 8$ (`diff = -1`).

4. **Non-Polarity Extremal Graphs Already Appear at $n \in [28, 37]$ (`inspect_hog_and_boza.py`, `verify_report_numbers.py`):**
   Checking Boza's 7 House of Graphs witnesses (`53036, 56941..56945, 52632`):
   - `HoG 52632` ($N=43$, triangle-free, $C_4$-free, degree sequence $6^{37} 7^6$) matches deleting a star $K_{1,6}$ (a vertex and 6 of its 7 neighbors) from the 50-vertex 7-regular girth-5 **Hoffman–Singleton graph**.
   - `HoG 53036` ($N=34$, 6-regular, unique extremal $C_4$-free graph on 34 vertices with $\mathrm{ex}(34, C_4) = 102$ per Afzaly–McKay) and `HoG 56941` ($N=35$, 6-regular, 35 triangles, every edge in 1 triangle) **cannot be induced subgraphs of $ER(q)$ for any $7 \le q \le 19$** (EML forces $\bar{d}(S) < 6$, e.g., $5.840$ and $5.933$ in $ER(7)$), and `HoG 56944` ($N=38, \delta=6$) is **proven not an induced subgraph of $ER(7)$** by exact MILP ($\delta_{\max}(38)=5$).

**Conclusion on Erdős #552 Part (ii):**
Deleting vertices from $ER(q)$ **cannot** refute Erdős #552(ii) (it falls behind $\sqrt{n} - c$ by $\Omega(\Delta)$ in prime-power gaps, explaining the $n^{11/40}$ loss in `[BEFRS89]`), nor can it extend $ER(q)$ by vertex additions. Conversely, because non-polarity constructions (`HoG 53036..56945` and Hoffman–Singleton deletions) already appear in small prime-power gaps, **resolving Part (ii)** depends entirely on whether non-polarity $C_4$-free constructions (e.g., modified polarities, incidence/quotient graphs, or algebraic Sidon-type constructions) can achieve $\delta \ge \sqrt{n} - O(1)$ inside unbounded prime-power gaps $\Delta = q_2 - q_1 \to \infty$ — a question that remains **open** and is the decisive testbed for the \$100 prize.

---

## Appendix: Verification Scripts Created in `subagent_alpha/`
- `analyze_835_designs.py`, `verify_835_exact.py`, `verify_835_composite_proof.py`, `analyze_835_k4_k6_all.py`, `verify_w12_disjoint.py`
- `analyze_552_polarity.py`, `test_552_deletions.py`, `analyze_552_eml_and_gaps.py`, `inspect_hog_and_boza.py`, `inspect_hog_structure.py`, `check_er_add_and_hog.py`, `check_hog_lift.py`, `test_552_er9_er11.py`, `verify_552_parsons_and_summary.py`, `verify_report_numbers.py`
