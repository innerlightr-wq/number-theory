# Transcendence of the 3x+1 conjugacy map on Sturmian words

**Concept DOI:** [10.5281/zenodo.23210794](https://doi.org/10.5281/zenodo.23210794) ·
Elias De Jesús · Technical note, October 2026 · 20 pages

## Summary

Let `T` be the 3x+1 map on the 2-adic integers and `Φ: Z₂ → Z₂` the Bernstein–Lagarias
conjugacy map, which sends a parity vector to the unique 2-adic integer realising it. This
note proves that `Φ(s)` is **transcendental** for the characteristic Sturmian word of every
irrational slope below an explicit threshold, and for the two mechanical words at intercept 0
and all their shifts. The mechanism is a bridge: by the Bernstein–Lagarias isometry the 2-adic
approximation depth of a periodic shadow is *exactly* a longest common prefix, so a repetition
in the parity word is a Diophantine approximation with no loss. The repetition structure is
measured by the initial critical exponent `ice` of Berthé–Holton–Zamboni, against a height cost
`A(γ) = max(1, γ log₂3)`; when `ice > 2A(γ)` the approximants beat the Ridout threshold.

## Main results, with exact scope

- **Theorem 1.2 (quantitative).** For every irrational `γ ∈ (0,1)`,
  `ω₁⁽²⁾(Φ(c_γ)) ≥ ice(c_γ)/A(γ) − 1 = (1 + limsup_k q_{k+1}/q_k)/A(γ) − 1`.
- **Theorem 1.3 (criterion).** If `ice(c_γ) > 2A(γ)` then `Φ(c_γ)` is transcendental, and so
  are `Φ(1c_γ)`, `Φ(0c_γ)` and `Φ(σᵏ 1c_γ)` for every `k ≥ 0`.
- **Corollary 1.4 (unconditional range).** For **every irrational
  `γ < γ* = (3+√5)/(4 log₂3) = 0.8258977696818354644…`** the numbers `Φ(c_γ)`, `Φ(1c_γ)`,
  `Φ(0c_γ)` and `Φ` of every shift are transcendental — **including the resonance slope
  `γ = log₃2`, with no hypothesis on the partial quotients of `log₂3`**. The threshold is
  sufficient, not necessary: slopes above `γ*` with large partial quotients still satisfy the
  criterion.
- **Theorem 6.1 (Liouville alternative).** If the partial quotients of `γ` are unbounded then
  `ω₁⁽²⁾(Φ(c_γ)) = ∞`: a 2-adic Liouville number, a `U₁`-number in Mahler's classification.
- **Theorem 7.3 (effective measure).** For bounded partial quotients **and `γ ≤ log₃2`**,
  `Φ(c_γ)` has a finite *effective* irrationality measure.

## Non-claims (as stated in §1.4 of the paper)

Nothing here bears on the convergence of the 3x+1 map on the positive integers, nor on the
existence of divergent or cyclic orbits. It does not prove the Periodicity Conjecture, which
quantifies over an uncountable family of aperiodic parity vectors; the Sturmian words are a
measure-zero, countable-slope subfamily. It proves nothing for slopes `γ ≥ γ*` beyond what
Theorem 1.3 gives under its hypothesis. It says nothing about intercepts other than 0, and
nothing about approximation by **integers** — that is problem (2) of the irrationality paper
and remains open. No claim of priority is made over Cassidy.

## Epistemic tiers

- **T1** — proved here, or quoted from a cited source with hypotheses checked: Theorems
  1.2–1.3, Corollary 1.4, Propositions 2.1–2.10, Theorems 6.1 and 7.3, Propositions 5.1/5.3.
- **T2** — exact integer or 2-adic computation, precision stated: everything in Appendix B,
  Example 4.1, the complexity table of §1.6, the quartic witness in the footnote of §2.4.
  **No floating-point number decides any inequality anywhere in the paper.**
- **T3** — interpretation, flagged as such: the reading of eq. (5) as the reason the
  archimedean place is unavailable, and the discussion in §8.

## Layout

```
paper/         main.tex, refs.bib, main.pdf  (exactly as deposited)
verification/  the scripts Appendix B refers to, reproduced unmodified
INGREDIENTS.md every ingredient against its prior source (also .csv)
CHECKLIST.md   per-statement ledger: proof location, prior source, verification status
```

## Reproduction

Python 3.9+, standard library only (`fractions`, `decimal`). No third-party packages.
Measured on an Apple Silicon laptop; the whole suite is **11 s**.

```
cd verification
python3 rev_core.py               # primitives; silent, asserts only          0.0 s
python3 rev_main.py               # depth, heights, certified omega, 4 slopes 6.8 s
python3 rev_collapse.py           # the 1c_gamma parity collapse (§4)         0.3 s
python3 rev_boundary_controls.py  # noble slopes either side of gamma*        3.0 s
python3 sign_check.py             # Remark 3.3, the two Xi conventions        0.4 s
python3 rev_nguyen.py             # literature exclusion (Nguyen Thm A)       0.0 s
python3 p1_ridout_gap.py          # the quartic witness of the §2.4 footnote  0.7 s
```

`rev_main.py`, `rev_collapse.py` and `rev_boundary_controls.py` reproduce `out_main.txt`,
`out_collapse.txt` and `out_bc.txt` **byte for byte**.

These scripts are deliberately **self-contained** and are byte-identical to the ones the
paper's Appendix B describes as "reproduced here unmodified"; they do not import
[`lib/ntlib`](../../lib). The library carries the same primitives, independently tested
(`python3 lib/tests/test_ntlib.py`).

## Related work and credit

**Bernstein–Lagarias** (1996) defined the conjugacy map and proved the isometry on which
everything here rests.

**López–Stoll** are the origin of the explicit study of `Φ` on Sturmian words: their 2009
Theorem 1 is the closed 2-adic series whose term exponents `q_{j+1}+q_j−1` *are* the
approximation depths used throughout, with Corollary 2 the associated generalised continued
fraction, Lemma 11 the one-position formula and Lemma 12 the rational-slope shadow. From
López–Stoll 2021 this paper uses Lemma 43 (the term-size estimate) and cites Lemma 37; **it
does not rely on [LS21, Theorem 1]**.

**Berthé–Holton–Zamboni** (2006) supply the initial critical exponent, its formula, and the
floor `ice ≥ 1+φ` that makes Corollary 1.4 unconditional.

**Ridout** (1958), in the single-prime form of **Badziahin–Kristensen** (2018, Thm 1.3), is the
Diophantine input. **Schlickewei**'s p-adic Subspace Theorem appears only in Appendix A, where
Theorem R is re-derived; nothing depends on that derivation.

**Cassidy** first proposed transcendence of `Φ(s)` for every Sturmian word (September 2026,
§4.6 of his note), with a sketch via Schlickewei's p-adic Subspace Theorem, recorded there as
unaudited; the general claim remains open. He also proved an irrationality statement
independently, and **posted his note first**. The proof given here goes by a different route —
Ridout, with the Berthé–Holton–Zamboni bound on initial powers.

**Pham** (22 July 2026) obtained irrationality independently, by transporting Dubickas's
counting argument to rational 2-adic integers.

The irrationality input is the author's own
[*The 3x+1 conjugacy map sends every Sturmian word to an irrational 2-adic integer*](https://doi.org/10.5281/zenodo.23108370);
the critical-truncation question of §5 was first posed in
[*The Sturmian–Mahler edge of the accelerated Collatz realizer problem*](https://doi.org/10.5281/zenodo.20594173).

Neither Pham's nor Cassidy's note is refereed, and no comparative claim is made about either.

## License

Paper and documentation CC BY 4.0; code MIT. See the repository root.
