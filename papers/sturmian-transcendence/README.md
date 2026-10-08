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

## Lean formalisation (stages 1–5)

Branch `lean-formalization`, directory [`lean/`](lean).  **Lean 4 + Mathlib, pinned**:
toolchain `leanprover/lean4:v4.34.0`, Mathlib `v4.34.0` (rev `5ed2965256430c3649e86755f9576b54eca72435`);
`lean-toolchain` and `lake-manifest.json` are committed.  18 files, 3699 lines, **no `sorry`** anywhere
in the import closure of `Sturmian.lean`.  Tagged `sturmian-transcendence-lean-v1.1`.

> **ONE axiom: Ridout's theorem.**  Corollary 1.4 is machine-checked for every irrational
> `γ < γ*` depending on a single external result — Ridout's theorem in Bugeaud–Kekeç's
> single-prime form.  The Berthé–Holton–Zamboni floor `ice(c_γ) ≥ 1+φ`, an axiom through
> stage 4, is now the **theorem** `Sturmian.one_add_phi_le_ice`.  The constant `1+φ` is
> Berthé–Holton–Zamboni's (Acta Arith. **122** (2006), §4.2) and **no novelty is claimed**
> for the Lean proof: it is a formalisation of a known result along a route that fits
> inside Mathlib (Dirichlet's theorem, best-approximation records built from their
> definition, and the sharp inequality `max(x+1, 2+1/x) ≥ 1+φ`).  It is independent of
> their paper only because that paper was never accessible.
>
> **No irrationality result is used.**  The development does **not** depend on the author's
> Proposition 2.10 (`[DJirr, Thm 10.1, Cor 10.5]`), nor on Cassidy's irrationality result,
> nor on Pham's.  Irrationality enters only in proved form — the 2-adic Liouville
> inequality; the aperiodicity of `c_γ` from the *hypothesis* `Irrational γ` on the slope;
> and, for the headline slope, the irrationality of `log₃ 2` itself, proved here from
> `2^b ≠ 3^a` (Mathlib has no irrationality statement for logarithms).

### Dependency of each main theorem

**Every main theorem depends on Ridout's theorem and nothing else.**

| theorem | slopes | axioms |
|---|---|---|
| `transcendental_PhiBL_charWord`, `..._mechanical`, `..._shifts` | `0 < γ < γ*` | **Ridout only** |
| `transcendental_PhiBL_logThreeTwo`, `..._shifts` | `γ = log₃ 2` (headline) | **Ridout only** |
| `transcendental_PhiBL_charWord_tierA`, `..._mechanical_tierA` (the elementary route) | `0 < γ < γ_A = 0.7571…` | **Ridout only** |
| `one_add_phi_le_ice` (`ice(c_γ) ≥ 1+φ`), `two_lt_ice`, `twelve_fifths_le_ice` | every irrational `γ ∈ (0,1)` | **none** |

The `γ_A` row is subsumed by the first and is kept deliberately: it records that the
headline case never needed the constant `1+φ` at all, only `e > 2`, because `A(log₃2) = 1`.

Since v1.1 the hypothesis `γ < 1` is **gone** from these statements: `gammaStar_lt_one`
proves `γ* < 1`, so `γ < γ*` already gives it.  The hypotheses are exactly the paper's
`0 < γ`, `Irrational γ`, `γ < γ*`.

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
| **`Sturmian.abs_balance_prefix`** | **sharp prefix balance** `\|ℓ·k_m − m·k_ℓ\| < ℓ`, the form `[DJirr, Lemma 10.4]` uses — two floor estimates, no standard words | none |
| **`Sturmian.cw_le_of_balance`, `cw_le_prefix`** | **`[DJirr, Lemma 10.4]`**: `c_W ≤ 3ℓ·max(2^ℓ,3^k)`. Stated with the balance hypothesis the source's own proof uses; the source's real-power monotonicity step is replaced by an equivalent integer argument | none |
| **`Sturmian.shadow_height_bound`** | **Proposition 2.4** (the height of a shadow). **An axiom at stage 2; now depends on NO axiom** | none |
| **`Sturmian.ice`, `exists_prefix_power_of_lt_ice`** | the paper's **Definition 2.5** (limsup of prefix powers, in `ℝ≥0∞`) and its **Steps 1–2**: from `ice(c_γ) > e`, arbitrarily long prefixes repeating to power `≥ e`. **No primitive-root replacement needed** | none |
| **`Sturmian.charWord_ne_per`** | **`c_γ` is aperiodic** for irrational `γ` — the paper's Step-4 "impossible, `γ` being irrational", and **the only place irrationality is used** | none |
| `Sturmian.transcendental_of_prefix_family` | **Steps 3–6** from the prefix family alone. Also derives `k_j ≥ 1`, the aperiodicity, the height bound, and the infinitude of the shadow set | Theorem R |
| `Sturmian.transcendental_PhiBL_charWord`, `..._mechanical` | **Corollary 1.4** for the constructed `Φ`: `Φ(c_γ)`, `Φ(1c_γ)`, `Φ(0c_γ)` transcendental for irrational `γ < γ*` | Theorem R |
| **`Sturmian.per_eq_of_min`** | **the three-distance periodicity lemma**: if `q` minimises `‖jγ‖` over `1 ≤ j < Q`, the prefix of `c_γ` of length `Q+q−2` has period `q`. Proved from the two-floor form of `charWord`; no continued fractions | none |
| **`Sturmian.gap_le`** | **the gap lemma**: three consecutive best-approximation records `p < r < s` with `‖rγ‖ < 1/4` satisfy `s ≥ r+p` (Fibonacci-type growth). Proved from record-ness alone — Mathlib has Dirichlet but **not** the best-approximation property of convergents | none |
| **`Sturmian.one_add_phi_le_max`** | the sharp elementary inequality `max(x+1, 2+1/x) ≥ 1+φ` for `x > 0`, with **equality at `x = φ`** (`max_eq_one_add_phi_at_phi`) — so this route attains the constant and cannot beat it | none |
| **`Sturmian.one_add_phi_le_ice`** | **the paper's Proposition 2.8, PROVED**: `ice(c_γ) ≥ 1+φ` for every irrational `γ ∈ (0,1)`. Formerly the axiom `bhz_ice_floor`. Constant due to Berthé–Holton–Zamboni; **no novelty claimed** | none |
| `Sturmian.twelve_fifths_le_ice`, `two_lt_ice` | `ice(c_γ) ≥ 12/5 > 2`; the weaker constant, all the headline slope needs | none |
| **`Sturmian.irrational_logThreeTwo`, `A_logThreeTwo`** | `log₃ 2` is irrational (from `2^b ≠ 3^a`), and `A(log₃ 2) = 1` | none |
| **`Sturmian.transcendental_PhiBL_shifts`** | **Corollary 1.4 in full**: `Φ(σ^m c_γ)`, `Φ(σ^m 1c_γ)`, `Φ(σ^m 0c_γ)` transcendental for **every** `m ≥ 0` — "`Φ` of every shift of these words". Via the paper's eq. (3), `2^m Φ(σ^m v) = 3^{k_m(v)}Φ(v) + c_m(v)`, as a rational-affine relation | Theorem R |
| **`Sturmian.transcendental_PhiBL_logThreeTwo`**, `..._shifts` | **the headline case**: `Φ` of `c_{log₃2}`, `1c_{log₃2}`, `0c_{log₃2}` and every shift of them, transcendental, **on Ridout alone** | Theorem R |
| `Sturmian.gammaStar_lt_one` | `γ* < 1`, through the rational witness `4/3` between `(3+√5)/4` and `log₂3`; so `γ < 1` is redundant given `γ < γ*` | none |

`#print axioms` evidence: [`AXIOM_AUDIT.txt`](lean/AXIOM_AUDIT.txt) — **124 results audited,
0 `sorryAx`, 110 depending on no named axiom, 14 on Ridout's theorem, and nothing else.
`bhz_ice_floor` appears nowhere in the output: the axiom no longer exists.**  A
statement-by-statement review against the paper, with the scope limits, is in
[`STATEMENTS.md`](lean/STATEMENTS.md).

Every definition is audited against the paper's verbatim text, with a machine-checked sanity
lemma, in [`Sturmian/DefinitionAudit.lean`](lean/Sturmian/DefinitionAudit.lean): `charWord`
(checked letter by letter at `γ = 2/5`), `Φ` (`Φ(1^∞) = −1` derived twice, independently,
from the recursion and from Proposition 2.2), `H`, `lcp`, `A(γ)`, `γ*` and `ice`.
**No mismatch was found**; three conventions are flagged there and in `AXIOMS.md` §8.

### What is assumed

**One axiom, in [`Sturmian/Axioms.lean`](lean/Sturmian/Axioms.lean), with the paper's
statement, the source, and a status label.  Full detail in
[`AXIOMS.md`](lean/AXIOMS.md).**

| axiom | source | status |
|---|---|---|
| `ridout_single_prime` | **Theorem R** — Bugeaud–Kekeç, Bull. Austral. Math. Soc. **98** (2018), 203–211, **Thm 1.3** (the paper's `BK18`, printed ref. [7]). Checked **verbatim against the source**; hypothesis table in `AXIOMS.md` §1 shows an exact match | *external published theorem* |
**On the former BHZ axiom** (detail in `AXIOMS.md` §2). It asserted Proposition 2.8,
`ice(c_γ) ≥ 1+φ`, citing Berthé–Holton–Zamboni §4.2, Acta Arith. **122** (2006), printed
ref. [4]. The source was never retrieved — `doi:10.4064/aa122-4-1` returns HTTP 502, the
impan, EuDML and bibliotekanauki routes each serve an unrelated document, and no preprint
exists on arXiv or HAL — so the statement had to be proved rather than checked. It now is
(`Sturmian.one_add_phi_le_ice`), and **the inaccessibility no longer affects any result**:
nothing in the development depends on the BHZ paper's text.

**The paper's own route to Proposition 2.8, stated correctly** (this was described
incompletely before v1.1). The paper gives two routes: the direct citation of an
*unnumbered sentence* in BHZ §4.2 (after the proof of their Theorem 1.2), together with
`θ = (1+√5)/2` on their p. 3; **and** Proposition 2.6 — the exact formula
`ice(c_α) = 1 + limsup q_{k+1}/q_k`, also cited to BHZ §4.2 — combined with the paper's
**own Lemma 2.9**, an elementary four-line continued-fraction re-derivation which the paper
labels "it is not a new result". So the arithmetic half of the floor is proved in the paper
and only the formula is imported.

**The Lean proof follows neither route exactly, and claims no novelty.** It formalises
neither Proposition 2.6 (which equates `ice` with a continued-fraction limsup, and Mathlib
has no best-approximation property for convergents) nor Lemma 2.9 (whose proof is about the
convergent recursion, for the same reason). It proves their combination in one step, from
best-approximation *records* built from their definition. What remains unverified at the
source is the paper's *citations* — the §4.2 sentence, `θ` on p. 3, and the formula of
Proposition 2.6 — not the mathematics.

**Not assumed, and not needed:** the Berthé–Holton–Zamboni floor (**proved**, stage 5);
the existence of `Φ` (constructed); the isometry (proved);
the shadow formula (proved); the transfer identity (proved); Proposition 2.4 (proved,
axiom-free); `[DJirr, Lemma 10.4]` (proved); balance (proved); the sharp prefix balance
(proved); aperiodicity of `c_γ` (proved); `k_j ≥ 1` (proved); the paper's Steps 1–2
(proved); injectivity of `j ↦ W_j^∞` (**eliminated** — each shadow value is taken only
finitely often, because the `j`-th shadow is approached to depth `e ℓ_j → ∞`); the
primitive-root replacement and `[BHZ06, Prop. 3.2]` (**eliminated** — balance is proved
directly for prefixes); and the paper's Proposition
2.10 — the author's prior unrefereed irrationality result — because
`Sturmian.ne_rat_of_ApproxExp` derives irrationality from the proved Liouville inequality
for the skeleton's quantifier (infinitely many *distinct rationals*).  The paper's §2.4
caution concerns the Koksma exponent `ω`, a different quantifier; see §4 of
[`AXIOMS.md`](lean/AXIOMS.md).

### What is still NOT formalised

**Nothing of the paper's own argument, and exactly one external result.**  Theorem 1.3 and
Corollary 1.4 are machine-checked modulo **Ridout's theorem** and nothing else.  Ridout's
theorem is a result of another author and would be an axiom in any formalisation that does
not also formalise its proof.

`Φ` of **every shift** is covered as of v1.1 (`transcendental_PhiBL_shifts`), so
Corollary 1.4 is now formalised in full.  Theorem 1.2 (the `ω` bound), Proposition 2.6,
Theorem 6.1 and Theorem 7.3 are **not** formalised; `STATEMENTS.md` §5 lists them.

Two further things are deliberately *not* formalised:

* **the equality case of Proposition 2.8** — `ice(c_γ) = 1+φ` iff the partial quotients are
  eventually all `1`.  The axiom never asserted it and nothing uses it.  That the
  inequality is sharp is recorded instead, as `max_eq_one_add_phi_at_phi`: the elementary
  bound `max(x+1, 2+1/x) ≥ 1+φ` is an equality at `x = φ`, so this proof attains the
  constant in the limit and cannot improve it.
* **continued fractions.**  Mathlib has Dirichlet's theorem but not the
  best-approximation property of convergents, so the records of `Sturmian/Records.lean` are
  built from their definition.  The proofs are therefore continued-fraction-free, which is
  a convenience of the formalisation rather than a mathematical point.

The one item that is *not* closed to the same standard is the **BHZ source check**: that
axiom is `NOT CHECKED` because the source is paywalled, and the paper's Proposition 2.8 is
a deduction from an unnumbered sentence rather than a quotable theorem.  See `AXIOMS.md` §2
for the two specific things to verify.

Remaining interfaces are recorded as `sorry` stubs in
[`lean/Stubs/TODO.lean`](lean/Stubs/TODO.lean), which **`Sturmian.lean` does not import**.

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
lake build              # 3219 jobs; 24 s here with the Mathlib build already present
lake env lean scripts/AxiomAudit.lean > AXIOM_AUDIT.txt
```

## License

Paper and documentation CC BY 4.0; code MIT. See the repository root.
