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

## Lean formalisation (stages 1–3)

Branch `lean-formalization`, directory [`lean/`](lean).  **Lean 4 + Mathlib, pinned**:
toolchain `leanprover/lean4:v4.34.0`, Mathlib `v4.34.0` (rev `5ed2965256430c3649e86755f9576b54eca72435`);
`lean-toolchain` and `lake-manifest.json` are committed.  2255 lines of Lean, 12 files,
**no `sorry`** anywhere in the import closure of `Sturmian.lean`.

### What is machine-checked

| result | statement | named axiom used |
|---|---|---|
| `Sturmian.H`, `finite_setOf_H_le` | the paper's `H(r) = max(\|num\|, den)`; each height is attained finitely often | none |
| `Sturmian.liouville_two_adic` | **the 2-adic Liouville inequality**: `\|ξ−r\|₂ ≥ (\|num ξ\|+den ξ)⁻¹·H(r)⁻¹` for `ξ ≠ r` with odd denominators | none |
| `Sturmian.two_A_lt_one_add_phi` | **the arithmetic of Corollary 1.4**: `γ < γ*` ⟹ `2A(γ) < 1+φ`, both branches of the `max` | none |
| `Sturmian.approx_of_depth_height` | **exponent bookkeeping**, pointwise, with the paper's exact error terms (eq. 7 has *no floor and no O(1) loss*; eq. 9 is `A·ℓ + log₂(3ℓ) + log₂3`) | none |
| `Sturmian.ones_succ`, `cw_succ`, `cw_cons_*_succ` | the recursions of the paper's `k_m(v)` and `c_m(v)`, **proved from the closed forms**, not substituted for them | none |
| **`Sturmian.isBL_PhiBL`** | **`Φ` EXISTS**: `PhiBL` is constructed as the 2-adic limit of `−c_m(v)·3^(−k_m(v))` — eq. (3) solved for `Φ(v)` — and satisfies the Bernstein–Lagarias recursion | none |
| **`Sturmian.IsBL.isometry`** | **Proposition 2.1**, the Bernstein–Lagarias isometry `\|Φ(v)−Φ(w)\|₂ = 2^(−lcp(v,w))`. The paper *cites* this; it is **proved here** from the recursion by induction on the `lcp` | none |
| `Sturmian.IsBL.injective` | `Φ` is injective (Prop. 2.1's last clause) | none |
| `Sturmian.IsBL.affinegen` | **the paper's eq. (3)**, `2^m Φ(σ^m v) = 3^{k_m(v)} Φ(v) + c_m(v)` | none |
| **`Sturmian.shadow_formula`** | **Proposition 2.2**, `Φ(w^∞) = c_w/(2^ℓ − 3^k)`, with `2^ℓ ≠ 3^k` (`two_pow_ne_three_pow`), **odd denominator** (`shadowRat_den_odd`) and `c_w > 0` (`cw_pos`) | none |
| **`Sturmian.IsBL.transfer`** | **the paper's eq. (12)**, `2Φ(c) = 3Φ(1c)+1 = Φ(0c)`, for every infinite word | none |
| `Sturmian.shadowRat_inj_of_word_ne`, `shadowSet_infinite` | Step 4: distinct periodic words give distinct shadows, so an injective family gives an infinite set of rationals | none |
| `Sturmian.transcendental_of_approxExp` | infinitely many **distinct** rationals with `\|ξ−r\|₂ ≤ H(r)^(−μ)`, `μ > 2` ⟹ `ξ` transcendental over `ℚ` | Theorem R |
| `Sturmian.ne_rat_of_ApproxExp` | the same hypothesis at `μ > 1` already excludes every rational with odd denominator | none |
| `Sturmian.transcendental_cons_true`, `..._false` | **Step 6**: transcendence transfers along eq. (12), via `isAlgebraic_affine` (proved) | none |
| **`Sturmian.ones_charWord`** | **the telescoping count**: the first `ℓ` letters of `c_γ` carry exactly `⌊(ℓ+1)γ⌋` ones | none |
| **`Sturmian.abs_ones_charWord_sub_lt_one`** | **balance for prefixes**, `\|k − γℓ\| < 1` — the paper's §2.2 bound, *proved* rather than quoted from Lothaire | none |
| **`Sturmian.shadow_height_bound`** | **Proposition 2.4** (the height of a shadow). **An axiom at stage 2; a theorem now**, from `H ≤ max(c_W,\|δ\|)`, `\|δ\| < max(2^ℓ,3^k)`, balance and the logarithm bookkeeping | `[DJirr, Lemma 10.4]` only |
| **`Sturmian.charWord_ne_per`** | **`c_γ` is aperiodic** for irrational `γ` — the paper's Step-4 "impossible, `γ` being irrational", and **the only place irrationality is used** | none |
| `Sturmian.transcendental_of_prefix_family` | **Steps 3–6** from the prefix family alone. Also derives `k_j ≥ 1`, the aperiodicity, the height bound, and the infinitude of the shadow set | Theorem R, `[DJirr 10.4]` |
| `Sturmian.transcendental_PhiBL_charWord`, `..._mechanical` | **Corollary 1.4** for the constructed `Φ`: `Φ(c_γ)`, `Φ(1c_γ)`, `Φ(0c_γ)` transcendental for irrational `γ < γ*` | all three |

`#print axioms` evidence: [`AXIOM_AUDIT.txt`](lean/AXIOM_AUDIT.txt) — **75 results audited,
0 `sorryAx`, 65 depending on no named axiom, 10 on the three below, and nothing else.**

### What is assumed

**Three axioms, all in [`Sturmian/Axioms.lean`](lean/Sturmian/Axioms.lean), each with the
paper's statement, the source, and a status label.  Full detail in
[`AXIOMS.md`](lean/AXIOMS.md).**

| axiom | source | status |
|---|---|---|
| `ridout_single_prime` | **Theorem R** — Bugeaud–Kekeç, Bull. Austral. Math. Soc. **98** (2018), 203–211, **Thm 1.3** (the paper's `BK18`, printed ref. [7]). Checked **verbatim against the source**; hypothesis table in `AXIOMS.md` shows an exact match | *external published theorem* |
| `bhz_prefix_family` | **Prop. 2.8** (`ice(c_γ) ≥ 1+φ`, Berthé–Holton–Zamboni, Acta Arith. **122** (2006), ref. [4]; **NOT CHECKED** directly) **combined with the paper's own Steps 1–2**. **Narrowed at stage 3 from six clauses to three**: only the lengths `ℓ_j ≥ 2`, their divergence, and the agreement of the first `⌈eℓ_j⌉` letters | *external theorem + paper's own extraction, **not yet formalized*** |
| `cw_le_three_mul_len_mul_max` | the numerator bound `c_W ≤ 3ℓ max(2^ℓ,3^k)` of **`[DJirr, Lemma 10.4]`** — all that is left of Proposition 2.4, which is now a theorem | *author's prior result, unrefereed, **NOT CHECKED***  |

**Not assumed, and not needed:** the existence of `Φ` (constructed); the isometry (proved);
the shadow formula (proved); the transfer identity (proved); Proposition 2.4 (proved);
balance (proved); aperiodicity of `c_γ` (proved); `k_j ≥ 1` (proved); injectivity of
`j ↦ W_j^∞` (**eliminated** — each shadow value is taken only finitely often, because the
`j`-th shadow is approached to depth `e ℓ_j → ∞`); and the paper's Proposition
2.10 — the author's prior unrefereed irrationality result — because
`Sturmian.ne_rat_of_ApproxExp` derives irrationality from the proved Liouville inequality
for the skeleton's quantifier (infinitely many *distinct rationals*).  The paper's §2.4
caution concerns the Koksma exponent `ω`, a different quantifier; see §4 of
[`AXIOMS.md`](lean/AXIOMS.md).

### What is still NOT formalised

Two things, and they are exactly the two non-Ridout axioms:

1. **`ice` itself and the paper's Steps 1–2** — the limsup of prefix powers, the
   primitive-root replacement, and the extraction of the prefix family from
   `ice(c_γ) > 2A(γ)`.  Until that is done, `bhz_prefix_family` bundles Berthé–Holton–
   Zamboni's floor (external, and expected to remain an axiom) with the paper's own
   extraction.
2. **`[DJirr, Lemma 10.4]`**, the numerator bound `c_W ≤ 3ℓ max(2^ℓ,3^k)` — the author's
   prior, unrefereed work, and all that Proposition 2.4 still takes on faith.

So **Theorem 1.3 and Corollary 1.4 are machine-checked modulo those two.**  Everything
between them and the conclusion is proved.  Remaining interfaces are recorded as `sorry`
stubs in [`lean/Stubs/TODO.lean`](lean/Stubs/TODO.lean), which **`Sturmian.lean` does not
import**.

### Two discrepancies found while checking the axioms

1. **Erratum in the paper's bibliography.** `paper/refs.bib` gives
   `doi = {10.1017/S0004972718000345}` for `BK18`; that DOI resolves (checked against
   Crossref) to De Bondt–Sun, *Classification of cubic homogeneous polynomial maps with
   Jacobian matrices of rank two*, same volume, pp. 89–101.  The correct DOI is
   **`10.1017/S0004972718000515`**.  Author, journal, volume, number and pages are correct.
2. **Attribution in this README.** The "Related work and credit" section above attributes
   Theorem R to *Badziahin–Kristensen*; the paper's `BK18` and printed reference [7] are
   *Bugeaud–Kekeç*.

Both are flagged for the author; no file outside `lean/` has been modified.

### Index conventions, recorded because they matter

* The paper indexes the letters of `c_γ` from `j = 1`; `Sturmian.Word` is indexed from `0`,
  so `charWord γ n` is the paper's `c_γ(n+1)`.
* `Sturmian.ApproxExp` quantifies over infinitely many **distinct elements of `ℚ`**; the
  paper's `ω` is the Koksma exponent, which quantifies over polynomials.  See the
  NORMALISATION NOTE in [`Sturmian/Basic.lean`](lean/Sturmian/Basic.lean).
* `c_m` and `k_m` read only the first `m` letters (`cw_congr`, `ones_congr`), which is why
  `cw ℓ (w^∞)` is the paper's `c_w`.

### Build

```
cd lean
lake exe cache get      # fetch the pinned Mathlib build
lake build              # 3216 jobs; 26 s here with the Mathlib build already present
lake env lean scripts/AxiomAudit.lean > AXIOM_AUDIT.txt
```

## License

Paper and documentation CC BY 4.0; code MIT. See the repository root.
