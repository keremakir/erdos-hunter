## Audit verdict

All three computational attacks failed to produce usable computational evidence:

- **DeepSeek:** `Exit Code: None`, no stdout, no stderr.
- **Nemotron:** `Exit Code: None`, no stdout, no stderr.
- **Gemma:** API failure.

Thus they proved or discovered **nothing computationally**. In particular, their repeated claim that \(k=10\) is the “smallest open case” was not verified—and is in fact falsified by the Johnson-bound calculation below.

### Main mathematical error

Both substantive agents misidentified \(k=10\) as an open frontier. Applying the exact `johnsonBound` from the Lean file gives

\[
\operatorname{johnsonBound}(20,4,10)=15920.
\]

Since

\[
\binom{20}{10}=184756,
\qquad
\left\lceil\frac{184756}{15920}\right\rceil=12,
\]

the formal lower-bound lemma implies

\[
\chi(J(20,10))\ge 12>11=k+1.
\]

Therefore `Property 10` is false. No coloring search is needed for \(k=10\).

For comparison, \(k=12\) gives

\[
\operatorname{johnsonBound}(24,4,12)=208012,
\]

and

\[
\binom{24}{12}=2704156=13\cdot208012,
\]

so the Johnson bound gives only

\[
\chi(J(24,12