# AXIOMS.md

Every axiom in this development, its exact quoted statement, source, and status.
`Sturmian/Axioms.lean` is the only file permitted to contain `axiom`.

**TWO axioms remain.**  Stage 1 declared one; stage 2 added two; stage 3 turned one of
those into a theorem and narrowed the other; stage 4 removed the remaining non-Ridout
non-BHZ axiom entirely and reduced the BHZ axiom to the floor alone.  `#print axioms`
evidence: [`AXIOM_AUDIT.txt`](AXIOM_AUDIT.txt).

| | axiom | status |
|---|---|---|
| §1 | `ridout_single_prime` | external published theorem, **source checked verbatim** |
| §2 | `bhz_ice_floor` | external (Berthé–Holton–Zamboni §4.2), **source NOT CHECKED — paywalled** |

**NO IRRATIONALITY RESULT IS USED.**  Neither axiom is an irrationality statement, and the
development depends on **none** of the three irrationality results in the literature — not
the author's Proposition 2.10 (`[DJirr, Theorem 10.1 and Corollary 10.5]`), not Cassidy's,
not Pham's.  Irrationality enters only in proved form: the 2-adic Liouville inequality
`Sturmian.liouville_two_adic`, whence `Sturmian.ne_rat_of_ApproxExp` (no rational with odd
denominator has the approximation property, already at `μ > 1`); and
`Sturmian.charWord_ne_per`, the aperiodicity of `c_γ`, which uses the **hypothesis**
`Irrational γ` on the slope — a hypothesis about `γ`, not an imported theorem about `Φ`.
See §5.

**Stage-4 summary.**  `[DJirr, Lemma 10.4]` is formalised, so Proposition 2.4
(`Sturmian.shadow_height_bound`) now depends on **no** axiom; and `ice` plus the paper's
Steps 1–2 are formalised, so the BHZ axiom is the floor alone.

---

## 1. `Sturmian.ridout_single_prime` — Theorem R

**Status: EXTERNAL PUBLISHED THEOREM.**  Not proved here and not expected to be.

**Paper's citation key:** `BK18`, used as `\cite[Theorem 1.3]{BK18}`, attributed there to
Ridout `\cite{Ridout58}`.

### As the paper states it

`paper/main.tex`, `\begin{theoremR}` (§2.4, printed p. 8), verbatim:

> Let $\xi$ be a $p$-adic number and $\varepsilon>0$. Suppose there is a sequence
> $(x_n/y_n)_{n\ge1}$ of rationals with $\gcd(x_n,y_n)=1$,
> $2\le|x_1,y_1|<|x_2,y_2|<\cdots$, and
> $$0<\Bigl|\xi-\frac{x_n}{y_n}\Bigr|_p<|x_n,y_n|^{-2-\varepsilon}\qquad(n=1,2,\dots),$$
> where $|x,y|:=\max(|x|,|y|)$ is the height of $x/y$. Then $\xi$ is transcendental.

### As the source states it

Yann Bugeaud and Gülcan Kekeç, *On Mahler's classification of p-adic numbers*,
**Bulletin of the Australian Mathematical Society 98 (2018), no. 2, 203–211**,
**Theorem 1.3** (printed pp. 2–3).  Checked against the author's own copy at
`irma.math.unistra.fr/~bugeaud/travaux/BuKe1.pdf`, verbatim:

> For coprime non-zero integers $x$, $y$, write $|x,y|$ for the maximum of $|x|$ and
> $|y|$, that is, for the height of the rational number $x/y$.
>
> **Theorem 1.3 (Ridout [11], 1958).** Let $\xi$ be a $p$-adic number and $\varepsilon$ a
> positive real number. Suppose that there exists a sequence $(x_n/y_n)_{n=1}^{\infty}$ of
> rational numbers with $\gcd(x_n,y_n)=1$ $(n=1,2,\dots)$ such that
> $2\le|x_1,y_1|<|x_2,y_2|<\cdots$ and
> $$0<\Bigl|\xi-\frac{x_n}{y_n}\Bigr|_p<|x_n,y_n|^{-2-\varepsilon}\quad(n=1,2,\dots).$$
> Then $\xi$ is transcendental.

### Hypothesis comparison — EXACT MATCH, no mismatch to report

| hypothesis | source | paper | Lean |
|---|---|---|---|
| `ξ` an arbitrary `p`-adic number, no condition on its minimal polynomial | ✓ | ✓ | `ξ : ℚ_[p]` |
| `ε > 0` | ✓ | ✓ | `hε : 0 < ε` |
| coprimality `gcd(xₙ,yₙ) = 1` | ✓ | ✓ | automatic — Lean's `Rat` is in lowest terms |
| `2 ≤ |x₁,y₁|` | ✓ | ✓ | `h2 : 2 ≤ H (x 0)` |
| heights strictly increasing | ✓ | ✓ | `hmono : StrictMono fun n => H (x n)` |
| strict lower bound `0 < |ξ − xₙ/yₙ|_p` | ✓ | ✓ | `hpos : ∀ n, 0 < ‖ξ - (x n : ℚ_[p])‖` |
| strict upper bound at exponent `−2−ε` | ✓ | ✓ | `hlt` |
| height `|x,y| = max(|x|,|y|)` | ✓ | ✓ | `Sturmian.H r = max r.num.natAbs r.den` |
| which absolute value | `|·|_p`, the `p`-adic one | same | `‖·‖` on `ℚ_[p]` |
| conclusion | `ξ` transcendental | same | `Transcendental ℚ ξ` |

**No hypothesis was weakened, strengthened, or dropped.**  Two conventions are recorded
rather than elided:

1. The source defines `|x,y|` only for coprime **non-zero** integers.  A rational with
   numerator `0` has height `1`, which `2 ≤ H (x 0)` together with strict monotonicity
   excludes, so the Lean statement never evaluates the height outside the source's range.
2. `Transcendental ℚ ξ` unfolds to `¬ IsAlgebraic ℚ ξ`.  Because every rational is
   algebraic over `ℚ`, this conclusion already excludes `ξ ∈ ℚ`.  The paper's separate
   irrationality input is needed for its `ω`-based route, not for the skeleton; see §3.

---

## 2. `Sturmian.bhz_ice_floor` — the Berthé–Holton–Zamboni floor

**Status: EXTERNAL.  SOURCE NOT CHECKED.**  Expected to remain an axiom.

**Lean:** `ENNReal.ofReal (1 + phi) ≤ ice (charWord γ)` for irrational `γ ∈ (0,1)`.

**As the paper states it** (Proposition 2.8, `{Floor; \cite[\S4.2]{BHZ06}}`), verbatim:

> For every irrational $\gamma$,
> $$\ice(c_\gamma)\;\ge\;1+\varphi=\varphi^{2}=\frac{3+\sqrt5}{2}=2.6180339887\ldots,$$
> with equality if and only if $a_k=1$ for all large $k$.

(The Lean axiom asserts only the inequality; the equality clause is not used.)

### Source comparison — COULD NOT BE DONE, and there is no theorem number to quote

The brief asked for a paper-versus-source comparison like the one done for Theorem R, and
to stop if they differ.  **Neither was possible, for two independent reasons.**

**(i) The source is inaccessible.**  Valérie Berthé, Charles Holton and Luca Q. Zamboni,
*Initial powers of Sturmian sequences*, Acta Arithmetica **122** (2006), no. 4, 315–347 —
the paper's printed reference **[4]** — is paywalled.  `doi:10.4064/aa122-4-1` returned
HTTP 502; the impan, EuDML and bibliotekanauki routes each served an unrelated document.
So the statement is taken **exactly as the paper quotes it**, and is marked **NOT CHECKED**.

**(ii) There is no numbered BHZ theorem to quote.**  The paper does not cite a numbered
result for the floor.  It says, verbatim:

> "This is `\cite[\S4.2]{BHZ06}`: in the sentence following the proof of their Theorem~1.2
>  they state that `\ice(\omega)\le3` if and only if all but finitely many `a_k` equal
>  `1`, in which case `\ice(\omega)=1+\theta`, where `\theta=(1+\sqrt5)/2` is the golden
>  mean fixed on `\cite[p.~3]{BHZ06}`.  Eventually-all-ones therefore gives
>  `\ice=1+\varphi`; otherwise `\ice>3>1+\varphi`."

So Proposition 2.8 is the paper's own **two-line deduction** from an *unnumbered sentence*
in BHZ §4.2, not a verbatim BHZ statement.  **The two things a reader must verify at the
source are:** (a) the sentence following the proof of BHZ **Theorem 1.2**, asserting
`ice(ω) ≤ 3` iff all but finitely many `a_k` equal 1, in which case `ice(ω) = 1+θ`; and
(b) that `θ = (1+√5)/2` on BHZ **p. 3**.  Until someone with access checks (a) and (b),
this axiom carries the paper's reading of the source and not the source itself.

### What stage 4 removed from this axiom

At stage 2 it asserted **six** clauses, at stage 3 **three**, and now the floor alone.
Everything the paper's Steps 1–2 and Step 4 add is proved:

* **the extraction** — `Sturmian.exists_prefix_power_of_lt_ice`, directly from the
  definition of `ice` as a limit superior (`Sturmian/Ice.lean`);
* **the primitive-root replacement is not needed at all.**  The paper performs it so that
  `\cite[Proposition 3.2]{BHZ06}` applies (giving a conjugate of a standard word, giving
  balance, giving the height bound), and so that minimal periods are distinct (giving Step
  4's distinctness).  Here balance for prefixes of `c_γ` is **proved** directly
  (`Sturmian.abs_balance_prefix`), and the distinctness was eliminated at stage 3 in favour
  of a finite-fibre argument.  So the extraction may take the prefix itself, and
  `\cite[Proposition 3.2]{BHZ06}` is **not used anywhere**;
* `k_j ≥ 1` for large `j` — from the telescoping count `Sturmian.ones_charWord`;
* `c_γ ≠ W_j^∞` — `Sturmian.charWord_ne_per`;
* injectivity of `j ↦ W_j^∞` — eliminated.

## 3. Axioms removed

**`shadow_height_bound` (stage 2) and `cw_le_three_mul_len_mul_max` (stage 3) are both
gone.**

Proposition 2.4 was an axiom at stage 2.  Stage 3 made it a theorem modulo the numerator
bound `c_W ≤ 3ℓ max(2^ℓ,3^k)` of `[DJirr, Lemma 10.4]`.  Stage 4 formalised that bound, so
**`Sturmian.shadow_height_bound` now depends on no axiom at all.**

`[DJirr, Lemma 10.4]` is `Sturmian.cw_le_of_balance` (from the balance hypothesis) and
`Sturmian.cw_le_prefix` (balance discharged for prefixes of `c_γ`), in
`Sturmian/Numerator.lean`.  Source: Elias De Jesús, *The 3x+1 Conjugacy Map Sends Every
Sturmian Word to an Irrational 2-adic Integer*, doi:10.5281/zenodo.23108370, p. 16 —
**retrieved and read**, md5 `5311cc475f7101d97158217097538a82`.  Its statement and proof are
quoted verbatim at the head of that file.  Two points recorded there:

* **the hypothesis is balance, as the source itself says.**  The sentence immediately
  before the lemma reads *"What Lemma 10.4 needs is balance of `w^∞`, which is what Theorem
  10.3 supplies."*  So `cw_le_of_balance` takes balance as its hypothesis rather than
  "cyclic permutation of a standard word", which is faithful to the source's own reading;
* **deviation in method.**  The source's middle step uses the real power `ρ = 3^{k/ℓ}` and
  monotonicity of `i ↦ ρ^{ℓ−1−i}2^i`.  The Lean proof is the same inequality rearranged to
  avoid real exponents: raising to the `ℓ`-th power turns it into
  `3^{(a−1)ℓ}2^{iℓ} ≤ (3^k)^{ℓ−i−1}(2^ℓ)^i ≤ M^{ℓ−1}`, pure integer arithmetic.  Same
  statement, same constant `3`.

## 4. What stages 3 and 4 proved

| was an axiom / hypothesis at stage 2 | now | where |
|---|---|---|
| **Proposition 2.4** (the height bound) | **THEOREM, axiom-free** | `Sturmian.shadow_height_bound`, from `H ≤ max(c_W,\|δ\|)`, `\|δ\| < max(2^ℓ,3^k)`, the balance bound and the logarithm bookkeeping — all proved — plus §3's numerator axiom |
| balance, `\|k − γℓ\| < 1` ("every Sturmian word is balanced", the paper's §2.2, citing Lothaire) | **THEOREM** for prefixes | `Sturmian.abs_ones_charWord_sub_lt_one`, from the telescoping count `Sturmian.ones_charWord`: `k_ℓ(c_γ) = ⌊(ℓ+1)γ⌋` exactly |
| `k_j ≥ 1` for large `j` (BHZ axiom clause) | **THEOREM** | inside `Sturmian.transcendental_of_prefix_family`, from `ones_charWord` and `ℓ_j → ∞` |
| `c_γ ≠ W_j^∞` (BHZ axiom clause) | **THEOREM** | `Sturmian.charWord_ne_per` — the aperiodicity of `c_γ`, and **the only place `Irrational γ` is used** |
| injectivity of `j ↦ W_j^∞` (BHZ axiom clause) | **ELIMINATED** | not needed: each shadow value is taken finitely often because the `j`-th shadow is approached to depth `e ℓ_j → ∞` |
| `0 < c_W` | **THEOREM** (already at stage 2) | `Sturmian.cw_pos` |
| **`[DJirr, Lemma 10.4]`**, `c_W ≤ 3ℓ max(2^ℓ,3^k)` | **THEOREM** (stage 4) | `Sturmian.cw_le_of_balance`, `Sturmian.cw_le_prefix` |
| **sharp prefix balance** `\|ℓk_m − mk_ℓ\| < ℓ` | **THEOREM** (stage 4) | `Sturmian.abs_balance_prefix`, two floor estimates |
| **`ice`** and the paper's **Steps 1–2** | **DEFINED and PROVED** (stage 4) | `Sturmian.ice`, `Sturmian.exists_prefix_power_of_lt_ice` |
| the **primitive-root replacement** and `\cite[Prop. 3.2]{BHZ06}` | **ELIMINATED** (stage 4) | not needed: balance is proved directly and distinctness was eliminated at stage 3 |

## 4a. Axioms the brief anticipated that turned out NOT to be needed

**`Φ`'s existence is NOT an axiom.**  The brief allowed falling back to an axiom for the
Bernstein–Lagarias map "only if blocked".  It was not needed: `Sturmian/Construct.lean`
**constructs** `Sturmian.PhiBL` as the `2`-adic limit of `−c_m(v)·3^(−k_m(v))` — which is
the paper's own eq. (3) solved for `Φ(v)` — and `Sturmian.isBL_PhiBL` proves it satisfies
the recursion.  So the interface `Sturmian.IsBL` is inhabited unconditionally.

**The isometry (Prop. 2.1) is NOT an axiom.**  The paper *cites* it (`\cite{BL96}`); per the
brief it is proved here anyway, `Sturmian.IsBL.isometry`, by induction on the `lcp` from
`IsBL` alone.  Likewise `Sturmian.IsBL.injective`, the periodic-shadow formula
`Sturmian.shadow_formula` (Prop. 2.2) with its odd denominator and `2^ℓ ≠ 3^k`, and the
transfer identity `Sturmian.IsBL.transfer` (eq. 12).

**Proposition 2.10 (irrationality) is NOT an axiom** — see §4.

## 5. No irrationality result is used — why Proposition 2.10 is not an axiom

The paper, §2.4, immediately after Theorem R:

> "Finally, the irrationality input, which Theorem R cannot supply: a rational $r$ has
> $\om(r)=\infty$, so $\om>1$ does not by itself exclude rationality."

and in Step 5:

> "It remains to exclude rationality, which Theorem R cannot do: a rational $r$ has
> $\om(r)=\infty$.  By Proposition~\ref{prop:irr}, $\PH(c_\gamma)\notin\Q$ …"

`Sturmian/Liouville.lean` proves, with no axiom,

```
theorem liouville_two_adic {ξ r : ℚ} (hξ : Odd ξ.den) (hr : Odd r.den) (hne : ξ ≠ r) :
    1 / ((|ξ.num| + (ξ.den : ℤ) : ℚ) * (H r : ℚ)) ≤ padicNorm 2 (ξ - r)
```

— the `p`-adic Liouville inequality, from `2^{v₂(n)} ∣ n ⟹ 2^{v₂(n)} ≤ |n|` for a nonzero
integer `n`, with the denominators cleared by `(ξ−r)·ξ.den·r.den = ξ.num·r.den − ξ.den·r.num`
and `padicNorm 2` of an odd integer equal to `1`.  From it,
`Sturmian.ne_rat_of_ApproxExp` concludes that **no rational with odd denominator admits
infinitely many distinct rational approximants of odd denominator at any exponent `μ > 1`**.

**NORMALISATION NOTE — the two statements are not in conflict, and the difference is a
quantifier, not a constant.**  The paper's `ω` is the `p`-adic Koksma exponent `w₁` in the
normalisation of Bugeaud's *Approximation by Algebraic Numbers* Ch. 9: its witnessing
family for a rational `ξ = a/b` is the set of integer multiples `k(bX − a)` of the minimal
polynomial, which is infinitely many **polynomials** but represents a single point of `ℚ`,
whence `ω(ξ) = ∞`.  `Sturmian.ApproxExp` asks instead for infinitely many **distinct
elements of `ℚ`** — which is the form Theorem R's hypothesis takes, its approximants being
coprime and of strictly increasing height.  Under that reading the Liouville inequality
forces irrationality already at `μ > 1`.

**Consequence, stated carefully.**  The stage-1 skeleton has **no dependence on the
unrefereed irrationality results** (neither the author's Prop 2.10, nor Pham's, nor
Cassidy's).  This is a statement about the skeleton, not a claim that the paper's §2.4
remark is wrong: the paper's route reaches Theorem R through `ω`, where its remark is the
correct caution.

---

## 6. Erratum found while checking Axiom R

`paper/refs.bib` gives, for `BK18`:

```
doi = {10.1017/S0004972718000345}
```

That DOI resolves (checked against Crossref) to a **different article in the same volume**:
De Bondt and Sun, *Classification of cubic homogeneous polynomial maps with Jacobian
matrices of rank two*, Bull. Austral. Math. Soc. **98** (2018), 89–101.

The correct DOI for Bugeaud–Kekeç is **`10.1017/S0004972718000515`** (Crossref: *ON
MAHLER'S CLASSIFICATION OF p-ADIC NUMBERS*, BUGEAUD, KEKEÇ, vol. 98, pp. 203–211).

Author, journal, volume, number and page range in `refs.bib` are all **correct**; only the
DOI string is wrong.  Since the paper is deposited (concept DOI 10.5281/zenodo.23210794),
this is an erratum for the author to decide about; **no file outside `lean/` was changed.**

## 7. A second, separate discrepancy — in the repository README, not the paper

`papers/sturmian-transcendence/README.md`, under "Related work and credit", says:

> "**Ridout** (1958), in the single-prime form of **Badziahin–Kristensen** (2018, Thm 1.3),
> is the Diophantine input."

The paper's own bibliography entry `BK18` and printed reference **[7]** are
**Bugeaud–Kekeç**, not Badziahin–Kristensen.  The initials coincide; the attribution in the
README does not match the paper.  **Flagged, not edited.**

---

## 8. Definition audit (stage 4, item 1)

`Sturmian/DefinitionAudit.lean` places each of `charWord`, `Φ`, `H`, `lcp`, `A(γ)`, `γ*` and
`ice` beside the paper's verbatim text with its page, and proves a machine-checked sanity
lemma for each.  **No mismatch was found.**  Three conventions needed an explicit note:

1. **Index shift.**  The paper indexes the letters of `c_γ` from `j = 1`; `Word` from `0`.
   So `charWord γ n` is the paper's `c_γ(n+1)`.  Checked at `γ = 2/5`, where the paper's
   word is `0,1,0,1,0,…`: the five letters are verified individually, and the telescoping
   count `ones 5 = ⌊6·(2/5)⌋ = 2` is cross-checked against the hand count.
2. **`IsBL` bundles eq. (2) with the parity fact.**  Unpacking `Φ(σv) = T(Φ(v))` by the
   first letter needs "`Φ(v)` is odd iff `v₀ = 1`" (the paper's §2.1, from `[BL96, §1]`) to
   know which branch of `T` applies.  That fact is then *derived* from `IsBL`
   (`IsBL.norm_cons_true`), so it is not assumed twice.  Sanity check: `Φ(1^∞) = −1` is
   derived twice independently — from the recursion, and from Proposition 2.2's rational —
   and the two agree.  Also `Φ(0^∞) = 0` and `Φ((10)^∞) = 1`.
3. **`log2three` is `logb 2 3`.**  `log2three = Real.log 3 / Real.log 2`, identified with
   `Real.logb 2 3` wherever both appear.  Sanity check: the paper's two closed forms for
   `γ*` agree, and `1+φ = φ² = (3+√5)/2`.
