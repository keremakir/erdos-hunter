# Official Submission Ready-to-Post Drafts

Once this repository is pushed to `https://github.com/keremakir/erdos-hunter`, use the drafts below for `erdosproblems.com` and `google-deepmind/formal-conjectures`.

---

## 1. Comment for `erdosproblems.com/835`

> **Closing $k = 10$ and $k = 12$ (extending the known range to $3 \le k \le 15$; new smallest open case $k = 16$)**
>
> Combining Ma and Tang's composite theorem ($\chi(J(2k,k)) > k+1$ whenever $k+1$ is composite, covering $k \in \{11, 13, 14, 15\}$) with the Johnson bound equality conditions settles the two remaining prime-successor cases below $16$:
>
> 1. **$k = 10$ ($p = 11$):** $\chi(J(20,10)) = 11$ forces $\alpha(J(20,10)) \ge \binom{20}{10}/11 = 16796 = \text{johnsonBound}(20, 4, 10)$. Equality in the Johnson bound requires a Steiner system $S(9, 10, 20)$. Taking $5$ successive derived designs yields an $S(4, 5, 15)$, which does not exist by **Mendelsohn & Hung (1972)** (*Utilitas Math.* 1, 5–95). Hence $\alpha(J(20,10)) \le 16795$ and $\chi(J(20,10)) \ge 12$.
> 2. **$k = 12$ ($p = 13$):** $\chi(J(24,12)) = 13$ forces $\alpha(J(24,12)) \ge \binom{24}{12}/13 = 208012 = \text{johnsonBound}(24, 4, 12)$, requiring an $S(11, 12, 24)$. Taking $7$ successive derived designs yields an $S(4, 5, 17)$, which does not exist by **Östergård & Pottonen (2008)** (*J. Combin. Theory Ser. A* 115(8), 1570–1573). Hence $\alpha(J(24,12)) \le 208011$ and $\chi(J(24,12)) \ge 14$.
>
> Thus $\chi(J(2k,k)) \ge k + 2$ holds for all $3 \le k \le 15$, and the smallest remaining open case is **$k = 16$ ($J(32, 16)$)**.
>
> Vanilla Lean 4.36.0 zero-`sorry` formalization of the pigeonhole chromatic reduction, composite range $k \le 100$, and Steiner threshold reductions (`Erdos835Proofs.lean`), plus a PR draft for `formal-conjectures` (`835_PR_draft.lean`):
> `https://github.com/keremakir/erdos-hunter`

---

## 2. Pull Request Description for `google-deepmind/formal-conjectures` (`FormalConjectures/ErdosProblems/835.lean`)

**Title:** `feat(Erdos835): add solved cases k = 10, k = 12 and close 3 ≤ k ≤ 15`

**Body:**
- Adds `johnsonGraph_20_10_chromaticNumber` (`@[category research solved]`, via 5-fold Steiner derivation $S(9,10,20) \to S(4,5,15)$ and Mendelsohn–Hung 1972).
- Adds `johnsonGraph_24_12_chromaticNumber` (`@[category research solved]`, via 7-fold Steiner derivation $S(11,12,24) \to S(4,5,17)$ and Östergård–Pottonen 2008).
- Proves `johnsonGraph_2k_k_chromaticNumber_le_15` (`3 ≤ k ≤ 15`) without `sorry` from the existing `known_cases` ($3 \le k \le 8$), `k = 9`, `johnson_chromaticNumber_composite` ($k \in \{11, 13, 14, 15\}$), and the two new solved cases $k = 10, 12$.

---

## 3. Comment for `erdosproblems.com/552`

> **Lean 4 kernel-verified $C_4$-free witnesses in $ER(7)$ and $ER(8)$ ($n = 39 \dots 64$) & spectral obstruction in prime-power gaps**
>
> 1. **Explicit MILP witnesses verified in Lean 4.36.0 (`zero sorry`):** Searching induced subgraphs of the Erdős–Rényi polarity graphs $ER(7)$ ($57$ vertices) and $ER(8)$ ($73$ vertices) via HiGHS MILP yields explicit $C_4$-free witnesses establishing $R(C_4, S_{39}) \ge 46$ (a $45$-vertex subgraph of $ER(7)$ with $\delta = 6, \Delta = 8$, matching $R(C_4, S_{39}) = 46$ beyond OEIS A006672's $n \le 38$ table) and $11$ exact values matching the elementary double-counting + parity upper bound ($n \in \{45, 47, 55, 57 \dots 64\}$). All $12$ witnesses are formally verified without `sorry` in `lean_proofs/Erdos552Proofs.lean`.
> 2. **Spectral obstruction for $ER(q)$ vertex-deletion constructions:** Because non-loop eigenvalues of $ER(q)$ have magnitude $\sqrt{q}$, the Expander Mixing Lemma prevents induced subgraphs of $ER(q_2)$ from achieving $\delta(G[S]) \ge \sqrt{n} - c$ in the middle of prime-power gaps $(q_1, q_2)$ once the gap reaches $4$ (starting at $(19, 23)$, around $n = 441$).
>
> Code, JSON witness vertex lists, and zero-`sorry` Lean 4 proofs:
> `https://github.com/keremakir/erdos-hunter`
