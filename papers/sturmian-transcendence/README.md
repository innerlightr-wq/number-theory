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

## Lean formalisation (stage 1 — logical skeleton)

Branch `lean-formalization`, directory [`lean/`](lean).  **Lean 4 + Mathlib, pinned**:
toolchain `leanprover/lean4:v4.34.0`, Mathlib `v4.34.0` (rev `5ed296525643`);
`lean-toolchain` and `lake-manifest.json` are committed.

### What is machine-checked

Everything in the import closure of `Sturmian.lean` compiles with **no `sorry`** and, per
[`AXIOM_AUDIT.txt`](lean/AXIOM_AUDIT.txt), depends on no axiom beyond the three standard
Lean ones (`propext`, `Classical.choice`, `Quot.sound`) plus the single named axiom below.

| result | statement | named axiom used |
|---|---|---|
| `Sturmian.H`, `finite_setOf_H_le`, `exists_H_gt_of_infinite` | the paper's height `H(r) = max(\|num\|, den)`; each height is attained finitely often, so an infinite set of rationals has unbounded height | none |
| `Sturmian.liouville_two_adic` | **the 2-adic Liouville inequality**: for `ξ ≠ r` rational with odd denominators, `\|ξ−r\|₂ ≥ (\|num ξ\| + den ξ)⁻¹ · H(r)⁻¹` | **none — proved** |
| `Sturmian.transcendental_of_approxExp` | infinitely many **distinct** rationals with `\|ξ−r\|₂ ≤ H(r)^(−μ)`, `μ > 2` ⟹ `ξ` transcendental over `ℚ` | Theorem R |
| `Sturmian.ne_rat_of_ApproxExp` | the same hypothesis at `μ > 1` already excludes every rational with odd denominator | none |
| `Sturmian.two_A_lt_one_add_phi` | **the arithmetic of Corollary 1.4**: `γ < γ*` ⟹ `2A(γ) < 1 + φ`, both branches of the `max` | none |
| `Sturmian.approx_of_depth_height` | **exponent bookkeeping**, pointwise: the paper's depth bound `\|ξ−r\|₂ ≤ 2^(−eℓ)` (eq. 20, *no floor and no O(1) loss*) and height bound `log₂ H(r) < A·ℓ + log₂(3ℓ) + log₂3` (eq. 22) give `\|ξ−r\|₂ ≤ H(r)^(−μ)` whenever `μ·B ≤ eℓ` | none |

### What is assumed

**One axiom, [`Sturmian/Axioms.lean`](lean/Sturmian/Axioms.lean):**

- `Sturmian.ridout_single_prime` — **Theorem R**, the single-prime form of Ridout's
  theorem, i.e. Bugeaud–Kekeç, *On Mahler's classification of p-adic numbers*, Bull.
  Austral. Math. Soc. **98** (2018), 203–211, **Theorem 1.3** (the paper's `BK18`,
  printed reference [7]).  Its statement was checked **verbatim against the source** and
  matches the paper's quotation with no hypothesis mismatch; the comparison table is in
  [`AXIOMS.md`](lean/AXIOMS.md).  Status: *external published theorem*.

**Not assumed, and not needed at stage 1:** the paper's Proposition 2.10 (irrationality,
the author's prior unrefereed result).  `Sturmian.ne_rat_of_ApproxExp` derives irrationality
from the proved Liouville inequality, for the skeleton's quantifier — infinitely many
*distinct rationals*, which is the form Theorem R's hypothesis takes.  The paper's §2.4
caution concerns the Koksma exponent `ω`, a different quantifier; see §3 of
[`AXIOMS.md`](lean/AXIOMS.md).  Also not yet declared, because stage 1 never consumes them:
BHZ's floor `ice(c_γ) ≥ 1+φ` (Prop 2.8) and the height bound (Prop 2.4).

### What is NOT formalised

Stages 2 and 3: `Φ` itself, the Bernstein–Lagarias isometry (Prop 2.1), the periodic-shadow
formula (Prop 2.2), the transfer identity (eq. 12), the height bound (Prop 2.4), the
Sturmian combinatorics, and `ice(c_γ) ≥ 1+φ` (Prop 2.8).  **Therefore the paper's Theorem
1.3 and Corollary 1.4 are not yet machine-checked** — only the logical skeleton into which
they fit.  Interfaces are recorded as `sorry` stubs in
[`lean/Stubs/TODO.lean`](lean/Stubs/TODO.lean), which **`Sturmian.lean` does not import**.

### Two discrepancies found while checking the axiom

1. **Erratum in the paper's bibliography.** `paper/refs.bib` gives
   `doi = {10.1017/S0004972718000345}` for `BK18`; that DOI is De Bondt–Sun in the same
   volume.  The correct DOI is `10.1017/S0004972718000515`.  Author, journal, volume,
   number and pages are correct.
2. **Attribution in this README.** The "Related work and credit" section above attributes
   Theorem R to *Badziahin–Kristensen*; the paper's `BK18` and printed reference [7] are
   *Bugeaud–Kekeç*.

Both are flagged for the author; no file outside `lean/` has been modified.

### Build

```
cd lean
lake exe cache get      # fetch the pinned Mathlib build
lake build              # the stage-1 import closure
lake env lean scripts/AxiomAudit.lean > AXIOM_AUDIT.txt
```

## License

Paper and documentation CC BY 4.0; code MIT. See the repository root.
