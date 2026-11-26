/-
Draft addition for `google-deepmind/formal-conjectures`:
  FormalConjectures/ErdosProblems/835.lean

Closes the prime-successor cases k = 10 (J(20, 10)) and k = 12 (J(24, 12)),
extending the closed frontier from 3 ≤ k ≤ 9 to 3 ≤ k ≤ 15
(combining with Ma & Tang's `johnson_chromaticNumber_composite` for k ∈ {11, 13, 14, 15}).
The new smallest open case is k = 16 (J(32, 16), where k + 1 = 17 is prime).

Mathematical Proof Summary:
  - For k = 10: χ(J(20, 10)) = 11 implies α(J(20, 10)) ≥ C(20, 10) / 11 = 16796 = johnsonBound 20 4 10.
    Achieving equality in the Johnson bound requires a Steiner system S(9, 10, 20).
    Taking 5 successive derived designs yields S(4, 5, 15), which does not exist
    (Mendelsohn & Hung 1972, "On the Steiner systems S(3, 4, 14) and S(4, 5, 15)", Utilitas Math. 1, 5-95).
    Hence α(J(20, 10)) < 16796 and χ(J(20, 10)) ≥ 12.

  - For k = 12: χ(J(24, 12)) = 13 implies α(J(24, 12)) ≥ C(24, 12) / 13 = 208012 = johnsonBound 24 4 12.
    Achieving equality requires a Steiner system S(11, 12, 24).
    Taking 7 successive derived designs yields S(4, 5, 17), which does not exist
    (Östergård & Pottonen 2008, "There exists no Steiner system S(4, 5, 17)", J. Combin. Theory Ser. A 115(8), 1570-1573).
    Hence α(J(24, 12)) < 208012 and χ(J(24, 12)) ≥ 14.
-/

-- Insert inside `namespace Erdos835` of `FormalConjectures/ErdosProblems/835.lean`:

/--
The chromatic number of $J(20, 10)$ is at least $12$.
Follows from the non-existence of a Steiner system $S(4, 5, 15)$ (Mendelsohn–Hung 1972)
via 5-fold derivation from $S(9, 10, 20)$, which would be forced by equality
$\alpha(J(20, 10)) = \binom{20}{10}/11 = 16796$.
-/
@[category research solved, AMS 5]
theorem johnsonGraph_20_10_chromaticNumber : J(20, 10).chromaticNumber > 10 + 1 := by
  sorry

/--
The chromatic number of $J(24, 12)$ is at least $14$.
Follows from the non-existence of a Steiner system $S(4, 5, 17)$ (Östergård–Pottonen 2008)
via 7-fold derivation from $S(11, 12, 24)$, which would be forced by equality
$\alpha(J(24, 12)) = \binom{24}{12}/13 = 208012$.
-/
@[category research solved, AMS 5]
theorem johnsonGraph_24_12_chromaticNumber : J(24, 12).chromaticNumber > 12 + 1 := by
  sorry

/--
Combining the known cases $3 \le k \le 9$, Ma & Tang's composite theorem
(`johnson_chromaticNumber_composite`, covering $k \in \{11, 13, 14, 15\}$),
and the Steiner non-existence obstructions for $k = 10$ and $k = 12$ closes all $3 \le k \le 15$.
The smallest remaining open case is $k = 16$ ($J(32, 16)$).
-/
@[category research solved, AMS 5]
theorem johnsonGraph_2k_k_chromaticNumber_le_15 (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 15) :
    J(2 * k, k).chromaticNumber > k + 1 := by
  interval_cases k
  · exact johnsonGraph_2k_k_chromaticNumber_known_cases 3 (by omega) (by omega)
  · exact johnsonGraph_2k_k_chromaticNumber_known_cases 4 (by omega) (by omega)
  · exact johnsonGraph_2k_k_chromaticNumber_known_cases 5 (by omega) (by omega)
  · exact johnsonGraph_2k_k_chromaticNumber_known_cases 6 (by omega) (by omega)
  · exact johnsonGraph_2k_k_chromaticNumber_known_cases 7 (by omega) (by omega)
  · exact johnsonGraph_2k_k_chromaticNumber_known_cases 8 (by omega) (by omega)
  · exact johnsonGraph_18_9_chromaticNumber
  · exact johnsonGraph_20_10_chromaticNumber
  · exact johnson_chromaticNumber_composite 11 (by omega) (by decide)
  · exact johnsonGraph_24_12_chromaticNumber
  · exact johnson_chromaticNumber_composite 13 (by omega) (by decide)
  · exact johnson_chromaticNumber_composite 14 (by omega) (by decide)
  · exact johnson_chromaticNumber_composite 15 (by omega) (by decide)
