# verification/ — exact-arithmetic scripts

These are the scripts of the **independent adversarial review** of
Theorems 1.2–1.3 and Corollary 1.4 of `main.tex` (the quantitative bound, the transcendence theorem, and the
unconditional corollary). They were written from scratch by the reviewer, not reused from the
author's own working code, and they are reproduced here unmodified.

**Remit.** The review covered §§1–5 and Appendices A–B of the paper. **§6
(Theorem 6.3, the finite effective measure for bounded partial quotients) was outside its remit**
and is not verified by anything in this directory.

## Ground rules observed

* Exact integer / `fractions.Fraction` arithmetic only. No floating-point value decides any
  inequality; floats appear only in printed ratios of exactly computed integers.
* Irrational slopes are pinned by a certified integer interval `[N/D, (N+1)/D]`; every floor or
  ceiling used to build a word is checked to agree at both endpoints, and the script raises rather
  than guessing if precision is exhausted.
* Approximation exponents are reported as the certified interval
  `[D/bitlen(H) - 1, D/(bitlen(H)-1) - 1]`, since `bitlen(H)-1 <= log2 H < bitlen(H)`.
* Shadows of height `H = 1` are excluded: the inequality of Theorem R is vacuous there.

## Files

| file | what it checks | corresponds to |
|---|---|---|
| `rev_core.py` | `Phi` built **only** from the parity-vector definition (`Phi(v) = 2 Phi(sigma v)` or `(2 Phi(sigma v) - 1)/3` according to `v_0`), plus certified Sturmian words, CF and convergents. Also re-checks the paper's closed form, the periodic-value formula and the isometry against it (300 / 200 / 300 exact random trials). | Props. 2.1, 2.2; App. B "Primitives" |
| `rev_main.py` | depth, exact height, and the certified `omega` interval at every convergent level for `c_gamma`, four slopes; direct check of `c_W <= 3 l max(2^l,3^k)` and of the Step-2 height bound at every level used; the depth identity `q_{k+1}+q_k-2`; plus an exhaustive sweep over all prefix lengths `l < 1400`. | §3 Steps 2–3; Prop. 2.4; App. B |
| `rev_boundary_controls.py` | noble slopes straddling `gamma*` (both sides); rational-target control; `sqrt(17)` in `Z_2` by bitwise Hensel lifting, worst exponent per dyadic height band against the Liouville cap. | Rem. 3.2; App. B "Boundary", "Controls" |
| `rev_collapse.py` | the parity dichotomy for `1c_gamma`; the witness `gamma = [0;2,1,4,1,8,1,16,...]` where `ice(1c_gamma) = 2` and the `1c_gamma` route collapses, against `c_gamma` on the same slope. | §4, Example 4.1 |
| `sign_check.py` | the two `Xi` conventions: `Phi(1c_beta) = -Xi_alpha` and `= +Xi_{alpha,0}`, mod `2^3000`, 1893 terms. | Rem. 3.3 |
| `rev_nguyen.py` | that `h(a_i) = o(i)` fails for the only admissible fixed-base coordinate, so the refined-Diophantine machinery of arXiv:2605.30606 does not apply directly. | §1.4 |
| `p1_ridout_gap.py`, `p1_ridout_gap2.py` | the quartic `X^4 - 3X^3 + 2X + 6`: Sturm real-root count, irreducibility over `Q`, Hensel root in `Z_2`. | footnote in §2.4 |
| `out_*.txt` | captured output of the corresponding runs | — |

## Reproducing

Python 3.9+ (uses `pow(a,-1,m)`), no third-party packages beyond the standard library
(`fractions`, `decimal`). From this directory:

```
python3 rev_core.py            # silent import; run the inline checks in rev_main.py
python3 rev_main.py
python3 rev_boundary_controls.py
python3 rev_collapse.py
python3 sign_check.py
python3 p1_ridout_gap2.py
```

Run times are minutes, dominated by big-integer `lcp` and `c_W` computations at the deepest levels.

## One caveat recorded by the reviewer

The first run of the quadratic control appeared to fail: for `sqrt(17)` the worst exponent at
`p/q = 3/11` is `1.89`, above the threshold `1`. This is **not** a violation. For a quadratic
irrational Liouville's inequality caps the exponent at `1 + log2(9)/log2 H`, so finite-height values
above `1` are forced and what must be observed is decay. Band by band the worst value stays under
the cap and the envelope decays toward `1`. The same caveat is why the paper's Lemma 3.1 is stated
as a *fixed* margin: for an algebraic target the excess over `1` is itself the vanishing slack,
whereas for `Phi(c_gamma)` it converges to a positive constant.
