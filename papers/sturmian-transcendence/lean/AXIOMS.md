# AXIOMS.md

Every axiom in this development, its exact quoted statement, source, and status.
`Sturmian/Axioms.lean` is the only file permitted to contain `axiom`.

**Stage 1 declares exactly one axiom.**

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

## 2. Axioms declared but NOT YET NEEDED at stage 1

**None.**  The brief anticipated declaring BHZ (`ice(c_γ) ≥ 1+φ`, paper Prop 2.8) and the
height bound (paper Prop 2.4) as labelled axioms.  Stage 1 does not reach the point where
either is consumed: its results are the abstract approximation lemma, the Liouville
inequality, the combination, the Corollary 1.4 arithmetic, and the pointwise exponent
bookkeeping — none of which mentions `ice` or a shadow height.  **They are therefore not
declared**, so that `#print axioms` cannot list an axiom that no reported theorem uses.
They will be added in stage 2/3 when first consumed, with the labels the brief specifies:

- **BHZ** — `ice(c_γ) ≥ 1 + φ`, paper Prop 2.8, `\cite[\S4.2]{BHZ06}`
  (Berthé–Holton–Zamboni, *Initial powers of Sturmian sequences*, Acta Arith. **122**
  (2006), 315–347) — status: *external published theorem*.
- **Height bound** — paper Prop 2.4, in the exact form
  `log₂ H(R_j) < A(γ)·ℓ_j + log₂(3ℓ_j) + log₂ 3` — status: *PROVED IN THE PAPER, NOT YET
  FORMALIZED — to be replaced by a proof in stage 3*.
- **Prop 2.10** (irrationality, `\cite[Theorem 10.1 and Corollary 10.5]{DJirr}`) —
  status: *author's prior result, unrefereed*.  **Stage 1 shows this is not needed for the
  skeleton**; see §3.

---

## 3. Why the paper's Proposition 2.10 is not an axiom here

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

## 4. Erratum found while checking Axiom R

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

## 5. A second, separate discrepancy — in the repository README, not the paper

`papers/sturmian-transcendence/README.md`, under "Related work and credit", says:

> "**Ridout** (1958), in the single-prime form of **Badziahin–Kristensen** (2018, Thm 1.3),
> is the Diophantine input."

The paper's own bibliography entry `BK18` and printed reference **[7]** are
**Bugeaud–Kekeç**, not Badziahin–Kristensen.  The initials coincide; the attribution in the
README does not match the paper.  **Flagged, not edited.**
