# Erdős-Hunter: Machine-Verified Bounds, Exact Rational Certificates & Ramsey Witnesses

Automated mathematical research pipeline combining **Razborov Flag Algebras (SDP)**, **exact rational `LDL^T` dual certification (zero floating-point error)**, **HiGHS MILP combinatorial witness search**, and **independent zero-import auditing** across open Erdős problems (`erdosproblems.com` / `google-deepmind/formal-conjectures`).

---

## Verified Results Summary

| Problem | Prize | Result | Verification Level | Key Files |
| :--- | :---: | :--- | :--- | :--- |
| **Erdős #128** *(Sparse Half Conjecture)* | \$250 | **100% Unconditional upper bound `289/10000 = 0.0289`** via new weighted padding rule $\psi_v^{(\alpha)}(w) = \alpha\,d(v) - d_{N(v)}(w)$ ($\alpha \ge 1$) at $N=7$ (107 triangle-free graphs, 18 PSD blocks, 111 $\Delta(G)\le 1/2$ localizers). Optimal SDP bound: `0.028822`. | **Zero-Float Exact Rational Certificate** (`fractions.Fraction` `LDL^T`: 18/18 PD, 107/107 graphs $\max_g S_{\text{exact}}[g] = -8.143\times 10^{-5} < 0$) | [flag_algebra_128_N7.py](flag_algebra_128_N7.py), [verify_rational_cert_128.py](verify_rational_cert_128.py), [erdos128_exact_rational_cert.json](erdos128_exact_rational_cert.json) |
| **Erdős #23** *(Max-Cut / Bipartization of Triangle-Free Graphs)* | — | **100% Unconditional upper bound `19/400 = 0.0475` (`1/21.05`)** via $N=7$ Flag Algebras + 35 1-nbr & 91 2-nbr cut localizers (shattering Erdős–Faudree–Pach–Spencer `1/18 = 0.05556`). Optimal SDP bound: `0.047225` (`1/21.18`). | **Zero-Float Exact Rational Certificate** (`fractions.Fraction` `LDL^T`: 18/18 PD, 107/107 graphs $\max_g S_{\text{exact}}[g] = -3.256\times 10^{-4} < 0$) | [erdos23_flag_algebra_N7.py](erdos23_flag_algebra_N7.py), [erdos23_exact_rational_cert.json](erdos23_exact_rational_cert.json) |
| **Erdős #552** *(Ramsey $R(C_4, S_n)$)* | \$100 | **11 exact values** verified with explicit $C_4$-free induced subgraph witnesses in $ER(7)$ and $ER(8)$ ($n \in \{45, 47, 55, 57..64\}$) + $R(C_4, S_{39})=46$ witness + Expander Mixing Lemma spectral obstruction for $ER(q)$ deletions across prime-power gaps ($n \ge 441$). | **100% Finite Exact** (independent $C_4$-free + $\delta \ge |S|-n$ + double-counting/parity upper bound) | [erdos552_milp_hunter.py](erdos552_milp_hunter.py), [erdos552_exact_values.json](erdos552_exact_values.json), [subagent_alpha/report.md](subagent_alpha/report.md) |
| **Erdős #835** *(Johnson Graph $\chi(J(2k,k))$)* | — | Closes **$k=10$** (5-fold derivation $\to S(4,5,15)$, Mendelsohn–Hung 1972) and **$k=12$** (7-fold derivation $\to S(4,5,17)$, Östergård–Pottonen 2008), extending closed frontier to **$3 \le k \le 15$** (new smallest open case: $k=16$, $J(32,16)$). | **Exact Integer Arithmetic + Literature Steiner Obstructions** + Lean 4 PR draft | [835_PR_draft.lean](835_PR_draft.lean), [subagent_alpha/report.md](subagent_alpha/report.md) |
| **Erdős #19** *(Erdős–Faber–Lovász)* | \$500 | Tested **902 maximal linear spaces** at $n \in \{13, 14, 15\}$ (including $PG(2,3)$, $STS(13)$ and mutations) via DSATUR + HiGHS MILP: 902/902 $n$-edge-colorable (0 counterexamples). | Experimental / Negative | [erdos19_efl_hunter.py](erdos19_efl_hunter.py), [erdos19_hunter_results.json](erdos19_hunter_results.json) |
| **Erdős #64** *($2^k$-Cycle Free)* | \$1,000 | 8-core 64-bit bitmask SA v2 (147,172 steps) hit $C_4=0, C_8=0$ across $n \in \{30, 36, 42, 48\}$ cubic graphs ($C_{16} \ge 10$ barrier). | Experimental / Calibrated | [pilot_erdos64.py](pilot_erdos64.py), [erdos64_hunter_v2.py](erdos64_hunter_v2.py) |
| **Erdős #7** *(Odd Covering System)* | \$25 | Exact HiGHS MILP proved `M=315` impossible (`241/315`); prime-power odd universes `M in {945, 1575, 3465}` ($\sum 1/d > 1$) capped at 74%–80% coverage. | Exact MILP (`M=315`) + Bounded | [erdos7_odd_covering.py](erdos7_odd_covering.py), [erdos7_odd_covering_results.json](erdos7_odd_covering_results.json) |
| **Erdős #1052** *(Unitary Perfect Numbers)* | \$10 | Exact 2-adic budget + factor-propagation branch-and-bound rediscovered `6, 60, 90, 87360` and ruled out new solutions for $2^1 \dots 2^{16}$ (`max_odd_exp=4`). | Exact Branch-and-Bound | [erdos1052_unitary_perfect.py](erdos1052_unitary_perfect.py) |
| **Erdős #848** *(Non-Squarefree $ab+1$ Sets)* | — | **Universal zero-`sorry` Lean 4.36.0 proof for ALL $0 \le N \le 307$** (all $2^{307}$ subsets) via dual $K$-coloring clique-cover certificates; exact MILP $K$-colorings verified up to $N \le 1007$ ($40/40$ endpoints with $\chi = \omega = |A_7(N)|$) and exact Bron–Kerbosch max-clique verified up to $N \le 2500$; discovered mixed extremal tie $\{32, 43, 57\}$ breaking Sawhney's asymptotic $\bmod 25$ purity for $58 \le N \le 82$. | **Universal Zero-`sorry` Lean 4 Kernel Proof ($N \le 307$)** + Exact MILP/Clique ($N \le 2500$) | [lean_proofs/Erdos848Proofs.lean](lean_proofs/Erdos848Proofs.lean), [erdos848_prefix_cert.py](erdos848_prefix_cert.py), [wave6_848_617_hunter.py](wave6_848_617_hunter.py) |
| **Erdős #742** *(Murty–Simon Conjecture)* | — | 5,730 exact diameter-2-critical minimalizations at smallest open $n \in \{25, 27, 28\}$: non-bipartite max edges stayed 21–35 below $\lfloor n^2/4 \rfloor$. | Experimental / Negative | [erdos742_murty_simon.py](erdos742_murty_simon.py), [erdos742_results.json](erdos742_results.json) |
| **Erdős #617** *(Balanced Colorings of $K_{r^2+1}$, $r=5$)* | — | Initialized from $AG(2,5)$ parallel classes + 26th apex vertex on $K_{26}$: reduced color-missing 6-subsets to $1,009$ out of $5 \times \binom{26}{6} = 1,151,150$ ($0.088\%$), supporting Erdős–Gyárfás at $r=5$. | Experimental / Supporting | [wave6_848_617_hunter.py](wave6_848_617_hunter.py), [wave6_848_617_results.json](wave6_848_617_results.json) |

---

## Independent Verification (One Command)

### 1. Formal Lean 4.36.0 Kernel Verification (Zero `sorry`)

Both [lean_proofs/Erdos835Proofs.lean](lean_proofs/Erdos835Proofs.lean) and [lean_proofs/Erdos552Proofs.lean](lean_proofs/Erdos552Proofs.lean) compile directly with the vanilla **Lean 4.36.0** kernel (`exit code 0`, zero `sorryAx` verified via `#print axioms`):

```bash
~/.elan/bin/lean lean_proofs/Erdos835Proofs.lean
~/.elan/bin/lean lean_proofs/Erdos552Proofs.lean
~/.elan/bin/lean lean_proofs/Erdos848Proofs.lean
```

### 2. Python Zero-Import Independent Audit

Run the **zero-import independent audit script** (imports zero functions from any solver script) to independently verify all #552 witnesses, #128/#23 certificates & formulas, and #835 arithmetic:

```bash
pip install -r requirements.txt
python independent_audit.py
```

To regenerate the exact rational certificates from scratch:

```bash
python flag_algebra_128_N7.py
python verify_rational_cert_128.py
python erdos23_flag_algebra_N7.py
```

---

## Repository Hygiene

- API keys (`.env`) and large binary caches (`*.npz`) are excluded via `.gitignore`.
- All mathematical proofs and certificates are reproducible on a single consumer CPU with zero external API calls.
