# AXIOMS.md

Every axiom in this development, its exact quoted statement, source, and status.
`Sturmian/Axioms.lean` is the only file permitted to contain `axiom`.

**ONE axiom remains: Theorem R (Ridout).**  Stage 1 declared one; stage 2 added two;
stage 3 turned one of those into a theorem and narrowed the other; stage 4 removed the
remaining non-Ridout non-BHZ axiom entirely and reduced the BHZ axiom to the floor alone;
stage 5 proved a weaker floor outright (Tier A) and then **proved the floor itself**
(Tier B), so **`bhz_ice_floor` no longer exists**.  `#print axioms` evidence:
[`AXIOM_AUDIT.txt`](AXIOM_AUDIT.txt).

| | axiom | status |
|---|---|---|
| §1 | `ridout_single_prime` | external published theorem, **source checked verbatim** |

### Which main theorem depends on what

**Every main theorem depends on `ridout_single_prime` and nothing else.**

| theorem | slopes | axioms it depends on |
|---|---|---|
| `transcendental_charWord`, `transcendental_PhiBL_charWord`, `transcendental_PhiBL_mechanical` | `0 < γ < γ* = 0.8258…` | **`ridout_single_prime` only** |
| `transcendental_PhiBL_logThreeTwo` (headline, `γ = log₃ 2`) | one slope | **`ridout_single_prime` only** |
| `transcendental_charWord_tierA` and its two companions (the elementary route) | `0 < γ < γ_A = 6/(5 log₂ 3) = 0.7571…` | **`ridout_single_prime` only** |
| `one_add_phi_le_ice` (`ice(c_γ) ≥ 1+φ`), `two_lt_ice`, `twelve_fifths_le_ice` | every irrational `γ ∈ (0,1)` | **none** |

The Tier-A theorems at `γ_A` are now subsumed by the general ones, and are retained
deliberately: they record that the headline case never needed the constant `1 + φ` at all,
only `e > 2`, because `A(log₃ 2) = 1` (`Sturmian.A_logThreeTwo`).  `γ_A < γ*` is proved
(`Sturmian.gammaTierA_lt_gammaStar`).

**NO IRRATIONALITY RESULT IS USED.**  The one remaining axiom is not an irrationality
statement, and the development depends on **none** of the three irrationality results in
the literature — not
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

**Stage-5 summary.**  `ice(c_γ) ≥ 1 + φ` is **proved**, for every irrational `γ ∈ (0,1)`,
with no continued-fraction theory and no appeal to the Berthé–Holton–Zamboni paper — see
§9.  The axiom `bhz_ice_floor` was therefore deleted. The constant `1 + φ` is
Berthé–Holton–Zamboni's and **no novelty is claimed** for the Lean proof; it is a
formalisation of a known result by a route that fits inside Mathlib.  The irrationality of
the headline slope `log₃ 2` is also proved here (`Sturmian.irrational_logThreeTwo`;
Mathlib has no irrationality statement for logarithms).

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

## 2. `Sturmian.bhz_ice_floor` — REMOVED at stage 5 (Tier B)

**Status: PROVED.  The axiom has been deleted from `Sturmian/Axioms.lean`.**  Its content is
now the theorem `Sturmian.one_add_phi_le_ice` in `Sturmian/Floor.lean`:

```
ENNReal.ofReal (1 + phi) ≤ ice (charWord γ)      for irrational γ ∈ (0,1)
```

**As the paper states it** (Proposition 2.8, `{Floor; \cite[\S4.2]{BHZ06}}`), verbatim:

> For every irrational $\gamma$,
> $$\ice(c_\gamma)\;\ge\;1+\varphi=\varphi^{2}=\frac{3+\sqrt5}{2}=2.6180339887\ldots,$$
> with equality if and only if $a_k=1$ for all large $k$.

The Lean theorem is the inequality.  **The equality clause is not formalised** and is not
used anywhere.

### Attribution, stated plainly

The constant `1 + φ` is due to **Valérie Berthé, Charles Holton and Luca Q. Zamboni**,
*Initial powers of Sturmian sequences*, Acta Arithmetica **122** (2006), no. 4, 315–347,
§4.2 — the paper's printed reference **[4]**.  **No novelty is claimed for the Lean proof.**
It is a formalisation of a known result along a route that fits inside Mathlib, not a new
theorem, and it does not improve the constant: `1 + φ` is exactly what the sharp elementary
inequality `max(x + 1, 2 + 1/x) ≥ 1 + φ` gives, and that inequality is an equality at
`x = φ` (`Sturmian.max_eq_one_add_phi_at_phi`), so this route cannot do better.

**The proof is independent of the BHZ paper.**  That is a statement about the Lean
development, not a judgement about the source. The source was never accessible (see §9),
so the proof had to be built from scratch; `Sturmian/Floor.lean` and
`Sturmian/Records.lean` cite nothing but Dirichlet's theorem, which is in Mathlib.
Consequently the **NOT CHECKED** source status recorded through stage 4 no longer affects
any result: nothing in the development depends on the BHZ paper's text.

### Historical record: what the axiom asserted, and what the paper cited

At stage 2 the axiom asserted **six** clauses, at stage 3 **three**, at stage 4 the floor
alone, and at stage 5 nothing.  Everything the paper's Steps 1–2 and Step 4 add was proved
at stage 4:

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

It is also worth keeping on record that **the paper does not cite a numbered BHZ theorem**
for the floor.  It says, verbatim:

> "This is `\cite[\S4.2]{BHZ06}`: in the sentence following the proof of their Theorem~1.2
>  they state that `\ice(\omega)\le3` if and only if all but finitely many `a_k` equal
>  `1`, in which case `\ice(\omega)=1+\theta`, where `\theta=(1+\sqrt5)/2` is the golden
>  mean fixed on `\cite[p.~3]{BHZ06}`.  Eventually-all-ones therefore gives
>  `\ice=1+\varphi`; otherwise `\ice>3>1+\varphi`."

So Proposition 2.8 was the paper's own two-line **deduction** from an *unnumbered sentence*
in BHZ §4.2.  A reader who wants to verify the paper's citation (as opposed to the
mathematics, which is now machine-checked) must still check at the source: (a) the sentence
following the proof of BHZ **Theorem 1.2**, and (b) that `θ = (1+√5)/2` on BHZ **p. 3**.

## 3. Axioms removed

**`shadow_height_bound` (stage 2), `cw_le_three_mul_len_mul_max` (stage 3) and
`bhz_ice_floor` (stage 5) are all gone.**  `bhz_ice_floor` is §2 above; the other two:

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

## 4. What stages 3, 4 and 5 proved

| was an axiom / hypothesis at stage 2 | now | where |
|---|---|---|
| **the BHZ floor** `ice(c_γ) ≥ 1+φ` | **THEOREM** (stage 5) | `Sturmian.one_add_phi_le_ice` — records, the gap lemma `s ≥ r+p`, and `max(x+1,2+1/x) ≥ 1+φ`; constant due to Berthé–Holton–Zamboni, no novelty claimed |
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

---

## 9. Stage 5 — the floor, PROVED

**What is proved.**  `Sturmian.one_add_phi_le_ice`:

```
ENNReal.ofReal (1 + phi) ≤ ice (charWord γ)      for every irrational γ ∈ (0,1)
```

with `Sturmian.twelve_fifths_le_ice` and `Sturmian.two_lt_ice` (`ice(c_γ) > 2`) as
corollaries.  All three depend on **no** axiom beyond Lean's three.  This is the paper's
Proposition 2.8; the axiom `bhz_ice_floor` has been deleted.  Attribution and the
no-novelty statement are in §2.

**Why `2` was the number that mattered on the way.**  The chain needs an exponent `e` with
`e > 2` *and* `e > 2A(γ)`.  For the headline slope `A(log₃ 2) = 1`, so `e > 2` is the whole
requirement — which is why Tier A's weaker constant `12/5` already sufficed there, before
the full floor was available.  Both routes are kept; see §9c.

### 9a. How the floor is proved — no continued fractions

Mathlib has Dirichlet's theorem (`Real.exists_nat_abs_mul_sub_round_le`) but **not** the
best-approximation property of continued-fraction convergents, so the argument is built
from the definition of a *record* instead.

1. **`Sturmian/Rotation.lean` — the periodicity lemma.**  `per_eq_of_min`: if `q` minimises
   `‖jγ‖` over `1 ≤ j < Q`, then the prefix of `c_γ` of length `Q + q − 2` has period `q`.
   Proof: `⌊jγ + off(q)⌋ = ⌊jγ⌋` for every `1 ≤ j < Q`, because no `jγ` can cross an
   integer under a displacement smaller than its own distance to `ℤ`; the two-floor form of
   `charWord` then gives `c_γ(m+q) = c_γ(m)` for `m + 2 < Q`.
2. **`Sturmian/Records.lean` — records.**  `IsRecord γ q` says `q ≥ 1` beats every smaller
   positive index.  `exists_record_le` (least minimiser) and `exists_record_gt` (Dirichlet)
   give that records exist below every index and are unbounded with quality `→ 0`;
   `record_min_lt_nextRec` upgrades record-ness to the hypothesis `per_eq_of_min` wants —
   a record minimises up to the **next** record, not merely up to itself.  `IsRecord` is
   not decidable, so the successor is the predicate `IsNextRec`, never a function.
3. **The sign claim.**  `off_mul_off_next_neg`: consecutive records lie on **opposite
   sides** of the nearest integer.  Otherwise `r − p` would be a strictly better index than
   `p`, forcing a record strictly between `p` and `r`.
4. **The gap lemma.**  `gap_le`: for three consecutive records `p < r < s` with
   `‖rγ‖ < 1/4`, one has `s ≥ r + p` — Fibonacci-type growth.  Proof (`lt_nrm_add`): for
   `1 ≤ t < p`, the index `r + t` is strictly worse than `r`.  If `tγ` falls on `r`'s side,
   the displacements add, and `‖rγ‖ < 1/4` keeps the sum away from the far integer.  If it
   falls on `p`'s side, then `p − t` is an index below `p`, so record-ness of `p` forces
   `‖tγ‖ > 2‖pγ‖ > 2‖rγ‖`, and the cancellation still leaves more than `‖rγ‖`.
5. **The elementary inequality.**  `one_add_phi_le_max`: for `x > 0`,
   `max(x + 1, 2 + 1/x) ≥ 1 + φ`.  Proof: if `x ≥ φ` the first term already exceeds
   `1 + φ`; if `x < φ` then `1/x > 1/φ = φ − 1` (`one_div_phi`, from `φ² = φ + 1`), so the
   second does.  It is **sharp**: `max_eq_one_add_phi_at_phi` gives equality at `x = φ`.
6. **The quantitative form.**  `exists_long_period_eps`: with `x = r/p` for consecutive
   records, `per_eq_of_min` gives a prefix power `x + 1 − 2/p` at `p`, and `gap_le` plus
   `per_eq_of_min` give `2 + 1/x − 2/r` at `r`.  Both corrections are at most `2/p`, and
   `exists_record_gt` supplies records with `p > 2/ε`, so for every `ε > 0` the power
   `1 + φ − ε` is reached arbitrarily far out.
7. **`Sturmian/Floor.lean` — the limsup.**  `le_prefixPower` turns agreement into a prefix
   power (via `le_lcp_of_agree`, the converse of `eq_of_lt_lcp`);
   `le_ice_of_lt_one_add_phi` applies `Filter.le_limsup_of_frequently_le` at each
   `c < 1 + φ`; and `one_add_phi_le_ice` passes to the supremum, by contradiction through
   `ENNReal.ofReal_toReal` and a midpoint.

### 9b. Why the constant cannot be improved along this route

The two bounds the dichotomy balances meet exactly at `x = φ`, where both equal `1 + φ`
(`max_eq_one_add_phi_at_phi`).  So `1 + φ` is not an artefact of a lossy estimate — it is
the exact value of `min_{x>0} max(x + 1, 2 + 1/x)`, and this proof attains it in the limit.
A slope whose partial quotients are eventually all `1`, i.e. `γ` equivalent to `1/φ`,
realises it; the paper's Proposition 2.8 records exactly that as its equality case (not
formalised here).

### 9c. The elementary route is kept

`Sturmian/TierA.lean` retains the short proof at the weaker constant `12/5`: one record,
one dichotomy, no `ε` and no limsup.  It is now subsumed by the general theorem, and is
kept because it records how little the headline case actually needs — `γ_A = 6/(5 log₂3)`,
`2A(γ) < 12/5`, and `A(log₃ 2) = 1`.  It also contains `irrational_logThreeTwo`, proved
from `2^b ≠ 3^a` because Mathlib has no irrationality statement for logarithms.

### 9d. Numerical check before the proof

The identity the proof rests on, `L(q_n) = q_{n+1} + q_n − 2` for the length of the longest
`q_n`-periodic prefix, was checked first: exact on all named slopes and on 386 of 400 random
irrationals. The 14 exceptions are all at the terminal convergent of an exact rational,
where the word is genuinely periodic forever and `L` is capped by the computed length — i.e.
outside the irrationality hypothesis. Smallest maximal prefix power over all 386 usable
slopes: `4.371981`. The tight case is `γ = 1/φ` (all partial quotients `1`), approaching
`1 + φ = 2.618034` from below — which is exactly the sharpness recorded in §9b, and is why
`12/5` is provable at a fixed finite record while `1 + φ` needs the `ε`-argument.

### 9e. BHZ source search — still NOT CHECKED, and now immaterial

Three further attempts were made to reach Berthé–Holton–Zamboni, *Initial powers of Sturmian
sequences*, Acta Arith. **122** (2006), 315–347, beyond the stage-4 attempts recorded in §2:

| attempt | result |
|---|---|
| arXiv and HAL searched directly for the title and the three authors | no preprint version found |
| arXiv **1510.00279** followed as a secondary source | cites BHZ but does not restate the §4.2 sentence |
| arXiv **2103.08351** followed as a secondary source | likewise |

The source was never retrieved.  **This no longer affects any result**, because nothing in
the development depends on the BHZ paper's text: the floor is proved from Dirichlet's
theorem and the record machinery.  What remains unverified is the paper's *citation* —
items (a) and (b) in §2 — not its mathematics.
