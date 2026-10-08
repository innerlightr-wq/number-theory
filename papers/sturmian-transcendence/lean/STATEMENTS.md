# STATEMENTS.md — final statement review

Read-only review of what the Lean development actually says, against the paper
(`papers/sturmian-transcendence/paper/main.tex`, concept DOI 10.5281/zenodo.23210794).
Every Lean statement below is copied verbatim from the source files; every paper passage is
copied verbatim from `main.tex`, with the printed number taken from `main.pdf`.

Toolchain `leanprover/lean4:v4.34.0`, Mathlib `v4.34.0`
(rev `5ed2965256430c3649e86755f9576b54eca72435`).  18 files, 3699 lines, **no `sorry`** in the import
closure of `Sturmian.lean`.  **One axiom** (`ridout_single_prime`); `#print axioms` evidence
in [`AXIOM_AUDIT.txt`](AXIOM_AUDIT.txt) — 124 results, 0 `sorryAx`, 110 depending on no named
axiom, 14 on Ridout.

**Revised at v1.1.**  Three things this review flagged are now fixed: the shifts are covered
(§3.6, formerly §5.4), `γ* < 1` is proved and `γ < 1` dropped (§4.2), and the description of
the paper's route to Proposition 2.8 is corrected (§6.1).  The changed entries say so.

---

## 0. Coverage at a glance

| paper | printed as | in Lean? |
|---|---|---|
| Proposition 2.1 (isometry) | Prop. 2.1 | **proved** — `IsBL.isometry` (the paper cites it) |
| Proposition 2.2 (periodic shadows) | Prop. 2.2 | **proved** — `shadow_formula` |
| Proposition 2.3 (`[BHZ06, Prop. 3.2]`) | Prop. 2.3 | **not needed** — see §4.9 |
| Proposition 2.4 (height of a shadow) | Prop. 2.4 | **proved** — `shadow_height_bound` |
| Definition 2.5 (`ice`) | Def. 2.5 | **formalised** — `prefixPower`, `ice` |
| Proposition 2.6 (the `ice` formula) | Prop. 2.6 | **not formalised**, and **not used** — see §5.2 |
| Proposition 2.8 (floor `ice ≥ 1+φ`) | Prop. 2.8 | **inequality proved** — `one_add_phi_le_ice`; **equality case not formalised** |
| Lemma 2.9 (re-derivation of 2.8) | Lem. 2.9 | **not formalised as stated**, and neither is Prop. 2.6; the Lean proof does their combination directly — §6.1 |
| Proposition 2.10 (irrationality) | Prop. 2.10 | **not used at all** — see §4.7 |
| Theorem R (Ridout, single prime) | Thm. R | **AXIOM** — §1 |
| Theorem 1.2 (quantitative, `ω` bound) | Thm. 1.2 | **not formalised** — see §5.1 |
| Theorem 1.3 (transcendence under (T)) | Thm. 1.3 | **conclusion fully proved** at `γ < γ*`, shifts included (§3.6); (T) itself is still not a stated Lean hypothesis — §5.3 |
| Corollary 1.4 (unconditional range) | Cor. 1.4 | **PROVED IN FULL** (v1.1): `Φ(c_γ)`, `Φ(1c_γ)`, `Φ(0c_γ)` and `Φ` of **every shift** — §3.3, §3.6 |
| Theorem 6.1 (Liouville alternative) | Thm. 6.1 | **not formalised** — §5.5 |
| Theorem 7.3 (finite effective measure) | Thm. 7.3 | **not formalised** — §5.6 |
| §5 (truncations), §4 (parity), §8 (scope) | — | **not formalised**; none of it is used |

---

## 1. The axiom

```lean
axiom ridout_single_prime {p : ℕ} [Fact p.Prime]
    (ξ : ℚ_[p]) (ε : ℝ) (hε : 0 < ε) (x : ℕ → ℚ)
    (h2 : 2 ≤ H (x 0))
    (hmono : StrictMono fun n => H (x n))
    (hpos : ∀ n, 0 < ‖ξ - (x n : ℚ_[p])‖)
    (hlt : ∀ n, ‖ξ - (x n : ℚ_[p])‖ < (H (x n) : ℝ) ^ (-2 - ε)) :
    Transcendental ℚ ξ
```

**Plain English.**  If a `p`-adic number is approximated by a sequence of rationals whose
heights strictly increase from at least `2`, each approximation being non-exact and better
than the `(−2−ε)` power of its height, then that number is not a root of any nonzero
rational polynomial.

**The paper** (`\begin{theoremR}`, §2.5, printed p. 8), verbatim:

> Let $\xi$ be a $p$-adic number and $\varepsilon>0$. Suppose there is a sequence
> $(x_n/y_n)_{n\ge1}$ of rationals with $\gcd(x_n,y_n)=1$,
> $2\le|x_1,y_1|<|x_2,y_2|<\cdots$, and
> $$0<\Bigl|\xi-\frac{x_n}{y_n}\Bigr|_p<|x_n,y_n|^{-2-\varepsilon}\qquad(n=1,2,\dots),$$
> where $|x,y|:=\max(|x|,|y|)$ is the height of $x/y$. Then $\xi$ is transcendental.

The source (Bugeaud–Kekeç, Bull. Austral. Math. Soc. **98** (2018), Thm 1.3) was checked
verbatim; the hypothesis-by-hypothesis table is `AXIOMS.md` §1, and it is an exact match.

**⚑ Misreadable 1 — which absolute value.**  `‖·‖` in the Lean statement is the norm on
`ℚ_[p]`, i.e. the paper's `|·|_p`.  It is **not** the real absolute value.  Nothing in the
Lean statement mentions an archimedean estimate, and nothing in the development uses one.

**⚑ Misreadable 2 — coprimality.**  The paper requires `gcd(x_n, y_n) = 1`.  Lean's `ℚ` is
always in lowest terms with positive denominator, so the hypothesis is automatic and does
not appear.  `H (x n) = max |num| den` is then exactly the paper's `|x_n, y_n|`.

**⚑ Misreadable 3 — the index base.**  The paper's sequence starts at `n = 1`; Lean's at
`n = 0`.  `h2 : 2 ≤ H (x 0)` is the paper's `2 ≤ |x_1, y_1|`.

**⚑ Misreadable 4 — strict monotonicity, not just distinctness.**  `hmono` is `StrictMono`
of the **height**, which is stronger than the approximants being distinct.  This is the
paper's `|x_1,y_1| < |x_2,y_2| < ⋯`, and the development discharges it (`pick`,
`strictMono_H_pick` in `Sturmian/Skeleton.lean`) from the infinitude of the shadow set plus
`finite_setOf_H_le`.

---

## 2. Definitions

### 2.1 `charWord` — the characteristic word `c_γ`

```lean
def Word : Type := ℕ → Bool

noncomputable def charWord (γ : ℝ) : Word :=
  fun n => decide (⌊((n : ℝ) + 2) * γ⌋ - ⌊((n : ℝ) + 1) * γ⌋ = 1)
```

**Plain English.**  The `n`-th letter of `charWord γ` is `true` exactly when the floor
function jumps between `(n+1)γ` and `(n+2)γ`.

**The paper** (§2.2), verbatim:

> For irrational $\gamma\in(0,1)$ the characteristic word is $c_\gamma(j)=\lfloor(j+1)\gamma\rfloor
> -\lfloor j\gamma\rfloor$ for $j\ge1$

**⚑ Misreadable 5 — INDEX SHIFT.**  The paper indexes letters from `j = 1`; `Word` from
`n = 0`.  So

> **`charWord γ n` is the paper's `c_γ(n+1)`.**

Every statement in the development is consistent with this one shift, and the shift is
checked letter by letter at `γ = 2/5` in `Sturmian/DefinitionAudit.lean`.  A reader
comparing a Lean index with a paper index must add 1.

**⚑ Misreadable 6 — `Bool`, not `{0,1}`.**  Letters are `Bool`.  `charWord γ n = true`
encodes the paper's `c_γ(n+1) = 1`.  The bridge is `Sturmian.charWord_true_iff` and the
counting function `ones` (the paper's `k_m`), where `true` contributes `1`.

### 2.2 `per` — periodisation, the paper's `W^∞`

```lean
def per (ℓ : ℕ) (W : Word) : Word := fun n => W (n % ℓ)
```

**Plain English.**  Repeat the first `ℓ` letters of `W` forever.

**⚑ Misreadable 7.**  In every main theorem the second argument is `charWord γ` itself, so
`per (ℓ j) (charWord γ)` is the infinite repetition of the **length-`ℓ j` prefix of `c_γ`** —
the paper's `W_k^∞` for `W_k` the length-`q_k` prefix.  `per ℓ W` ignores everything in `W`
beyond position `ℓ`.  At `ℓ = 0`, `n % 0 = n`, so `per 0 W = W`; the theorems always carry
`2 ≤ ℓ`.

### 2.3 `lcp` — longest common prefix

```lean
noncomputable def lcp (v w : Word) (h : v ≠ w) : ℕ :=
  Nat.find (p := fun n => v n ≠ w n) …
```

**Plain English.**  For two distinct words, the index of the first place they differ, which
equals the length of their longest common prefix.

**The paper** (§2.1), verbatim:

> for words $v,w\in\{0,1\}^{\N}$, $\lcp(v,w)$ is the length of their longest common prefix

**⚑ Misreadable 8.**  Lean's `lcp` takes a **proof** `v ≠ w` as an argument and so is
undefined on equal words (the paper's `lcp(v,v) = ∞`).  Every use supplies that proof from
`charWord_ne_per`, the proved aperiodicity of `c_γ`.  `prefixPower` handles the equal case
separately, by the value `⊤`.

### 2.4 `H` — height of a rational

```lean
def H (r : ℚ) : ℕ := max r.num.natAbs r.den
```

**The paper** (§2.2), verbatim:

> For $x=u/v\in\Q$ in lowest terms with $v>0$ we write $H(x)=\max(|u|,v)$.

Exact match.  `H r ≥ 1` always (`H_pos`), and `H r = 1` iff `r` is an integer in `{-1,0,1}`.

### 2.5 `IsBL` and `PhiBL` — the conjugacy map `Φ`

```lean
structure IsBL (Φ : Word → ℤ_[2]) : Prop where
  cons_false : ∀ c, Φ (cons false c) = 2 * Φ c
  cons_true  : ∀ c, 3 * Φ (cons true c) = 2 * Φ c - 1

noncomputable def PhiBL (v : Word) : ℤ_[2] := …   -- the 2-adic limit of −c_m(v)·3^(−k_m(v))
theorem isBL_PhiBL : IsBL PhiBL
```

**Plain English.**  `IsBL Φ` says `Φ` turns prefixing a `0` into doubling, and prefixing a
`1` into the inverse branch of the `3x+1` map.  `PhiBL` is an explicit map satisfying it, so
the interface is inhabited unconditionally.

**The paper** (§1.1), verbatim:

> Bernstein and Lagarias \cite[\S1]{BL96} proved that $T$ and $S$ are conjugate: there is a
> unique homeomorphism $\PH\colon\Zt\to\Zt$ with $\PH(0)=0$ and
> $$\PH\circ S\circ\PH^{-1}=T .$$

and

> $\PH(\sigma v)=T(\PH(v))$

**⚑ Misreadable 9 — `IsBL` is weaker than the paper's characterisation, and that is
deliberate.**  `IsBL` asserts only the two recursion clauses.  It does **not** assert that
`Φ` is a homeomorphism, that `Φ(0) = 0`, or that it is unique.  Consequences:

* The main theorems are stated **for every** `Φ` with `IsBL Φ`, which is *stronger* than a
  statement about one particular map.
* **No uniqueness theorem is stated.**  `∀ Φ Ψ, IsBL Φ → IsBL Ψ → Φ = Ψ` is not in the
  development (injectivity `IsBL.injective` and the isometry `IsBL.isometry` are).  Nothing
  needs it, precisely because of the universal quantification.
* **The bridge from the literature's `Φ` to `IsBL` is the paper's §2.1 unpacking, not a Lean
  proof.**  Bernstein–Lagarias's `Φ` is not independently defined in Lean, so "the `Φ` of
  `[BL96]` satisfies `IsBL`" is *not* machine-checked.  What is checked is that `IsBL`
  reproduces the paper's own consequences: `Sturmian/DefinitionAudit.lean` derives
  `Φ(1^∞) = −1` twice independently (from the recursion, and from Proposition 2.2's
  rational) and they agree, and also `Φ(0^∞) = 0`, `Φ((10)^∞) = 1`.
* Unpacking `Φ(σv) = T(Φ(v))` by the first letter needs "`Φ(v)` is odd iff `v₀ = 1`"
  (`[BL96, §1]`, the paper's §2.1) to know which branch of `T` applies.  That parity fact is
  **derived** from `IsBL` (`IsBL.norm_cons_true`), not assumed twice.

### 2.6 `A(γ)` and `γ*`

```lean
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2
noncomputable def log2three : ℝ := Real.log 3 / Real.log 2
noncomputable def A (γ : ℝ) : ℝ := max 1 (γ * log2three)
noncomputable def gammaStar : ℝ := (1 + phi) / (2 * log2three)
```

**The paper** (§1.2), verbatim:

> Put $\Av:=\max(1,\gamma\log_2 3),\qquad
> \gs:=\frac{1+\varphi}{2\log_2 3}=\frac{3+\sqrt5}{4\log_2 3}
> =0.8258977696818354644\ldots,$ where $\varphi=(1+\sqrt5)/2$

**⚑ Misreadable 10 — `log2three` is `logb 2 3`.**  `Real.log 3 / Real.log 2` is `Real.logb 2 3`;
the two are identified wherever both appear (`Sturmian/Height.lean`,
`Sturmian/DefinitionAudit.lean`).  Sanity-checked there: the paper's two closed forms for
`γ*` agree, and `1 + φ = φ² = (3+√5)/2`.

**⚑ Misreadable 11 — the decimal value of `γ*` is NOT verified in Lean.**  `0.8258977…`
appears only in prose.  What is proved is `γ_A < γ*` (`gammaTierA_lt_gammaStar`),
`2A(γ) < 1+φ` for `γ < γ*` (`two_A_lt_one_add_phi`), and `log₃2 < γ*`
(`logThreeTwo_lt_gammaStar`).  **`γ* < 1` is not proved** — see §4.2.

### 2.7 `prefixPower` and `ice`

```lean
noncomputable def prefixPower (ω : Word) (n : ℕ) : ℝ≥0∞ :=
  if h : ω = per n ω then ⊤ else ((lcp ω (per n ω) h : ℕ) : ℝ≥0∞) / ((n : ℕ) : ℝ≥0∞)

noncomputable def ice (ω : Word) : ℝ≥0∞ := limsup (prefixPower ω) atTop
```

**The paper** (Definition 2.5), verbatim:

> The \emph{prefix power} of a finite word $W$ in a sequence $\omega$ is the largest real $p$
> such that $W^{p}$ is a prefix of $\omega$; equivalently $\lcp(\omega,W^{\infty})/|W|$. The
> \emph{initial critical exponent} $\ice(\omega)$ is the limit superior of the prefix powers
> of the words $\omega[0,n)$ in $\omega$.

and the remark after it:

> Because the prefix power is defined as the largest \emph{real} such $p$, we have
> $\lcp(\omega,W^{\infty})=p\,|W|$ \emph{exactly}: no floor and no $O(1)$ is lost in passing
> between $\ice$ and approximation depth.

**⚑ Misreadable 12 — the value lives in `ℝ≥0∞`.**  The paper's `ice` can be `∞` (its Case L,
unbounded partial quotients), so the Lean version is `ENNReal`-valued and comparisons use
`ENNReal.ofReal`.  `prefixPower ω n = ⊤` **exactly** when `ω` is itself `n`-periodic, and
`prefixPower ω 0 = ⊤` (since `per 0 ω = ω`), so the `limsup` is taken over a sequence whose
first value is `⊤`.  That is harmless — a `limsup` at `atTop` ignores any finite prefix of
indices — but it means `ice ω = ⊤` cannot be read off from `prefixPower ω 0`.

### 2.8 Transcendence — over `ℚ`, inside which field

```lean
Transcendental ℚ ((Φ (charWord γ) : ℚ_[2]))
```

**Plain English.**  `Φ(c_γ)`, viewed inside the field `ℚ_[2]` of 2-adic numbers, is not a
root of any nonzero polynomial with rational coefficients.

* `Transcendental ℚ ξ` unfolds to `¬ IsAlgebraic ℚ ξ`, i.e. there is **no** nonzero
  `p ∈ ℚ[X]` with `p(ξ) = 0`.
* The ambient field is **`ℚ_[2]`** (`Padic 2`), with its unique `ℚ`-algebra structure
  (`ℚ_[2]` has characteristic `0`, so the embedding `ℚ ↪ ℚ_[2]` is the canonical one and
  there is no choice to make).
* `Φ` lands in **`ℤ_[2]`** (`PadicInt 2`), matching the paper's `Φ : ℤ₂ → ℤ₂`; the coercion
  `ℤ_[2] → ℚ_[2]` is the inclusion of the valuation ring, and it is injective, so nothing
  is lost.

**⚑ Misreadable 13 — transcendence already excludes rationality.**  Every rational is
algebraic over `ℚ`, so `Transcendental ℚ ξ` implies `ξ ∉ ℚ`.  The paper's separate
irrationality input (Proposition 2.10) is needed for its `ω`-based route, not for this one;
see §4.7.

---

## 3. The main theorems, verbatim

### 3.1 The engine — Steps 3–6 from a prefix family

```lean
theorem transcendental_of_prefix_family (h : IsBL Φ) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hirr : Irrational γ)
    {e : ℝ} (he2 : 2 < e) (heA : 2 * A γ < e)
    {ℓ : ℕ → ℕ} {W : ℕ → Word}
    (hℓ2 : ∀ j, 2 ≤ ℓ j)
    (hℓinf : Tendsto (fun j => (ℓ j : ℝ)) atTop atTop)
    (hagree : ∀ j (n : ℕ), (n : ℝ) < e * (ℓ j : ℝ) → charWord γ n = per (ℓ j) (W j) n) :
    Transcendental ℚ ((Φ (charWord γ) : ℚ_[2]))
```

**Plain English.**  If `c_γ` begins, for lengths `ℓ_j → ∞`, with an `e`-th power of a
length-`ℓ_j` word, and `e` beats both `2` and `2A(γ)`, then `Φ(c_γ)` is transcendental.

**⚑ Misreadable 14 — no distinctness hypothesis.**  The paper's Step 4 needs the periodic
approximants `W_j^∞` to be pairwise distinct, which is why it replaces each prefix by its
primitive root.  **The Lean statement has no such hypothesis.**  Distinctness is replaced by
a finite-fibre argument: each shadow value is taken only finitely often, because the `j`-th
shadow is approached to depth `e·ℓ_j → ∞`.  So `W` here is an arbitrary family — in every
application `W j = charWord γ`, i.e. the prefix itself, un-primitivised.

**⚑ Misreadable 15 — `hagree` is a strict inequality on the real line.**  It asks agreement
at every index `n` with `(n : ℝ) < e·ℓ_j`, which is the paper's "the first `⌈e ℓ_j⌉ letters
agree" with no floor lost — the Definition-2.5 remark quoted in §2.7.

### 3.2 Corollary 1.4, for an arbitrary `IsBL` map

```lean
theorem transcendental_charWord (h : IsBL Φ) {γ : ℝ}
    (hγ0 : 0 < γ) (hirr : Irrational γ) (hγs : γ < gammaStar) :
    Transcendental ℚ ((Φ (charWord γ) : ℚ_[2]))
```

### 3.3 Corollary 1.4, for the constructed map

```lean
theorem transcendental_PhiBL_charWord {γ : ℝ}
    (hγ0 : 0 < γ) (hirr : Irrational γ) (hγs : γ < gammaStar) :
    Transcendental ℚ ((PhiBL (charWord γ) : ℚ_[2]))

theorem transcendental_PhiBL_mechanical {γ : ℝ}
    (hγ0 : 0 < γ) (hirr : Irrational γ) (hγs : γ < gammaStar) :
    Transcendental ℚ ((PhiBL (cons true (charWord γ)) : ℚ_[2])) ∧
    Transcendental ℚ ((PhiBL (cons false (charWord γ)) : ℚ_[2]))
```

**⚑ Misreadable 13a — the hypotheses are now exactly the paper's.**  `γ < 1` was a
hypothesis through v1; since v1.1 `gammaStar_lt_one` is proved, so it is derived rather than
assumed.  The three hypotheses are `0 < γ`, `Irrational γ`, `γ < γ*`.  See §4.2.

**Plain English.**  For every irrational slope `γ` strictly between `0` and `γ*`, the three
2-adic integers `Φ(c_γ)`, `Φ(1c_γ)` and `Φ(0c_γ)` are transcendental over `ℚ`.

**The paper** (Corollary 1.4), verbatim:

> For every irrational $\gamma<\gs$ the numbers $\PH(c_\gamma)$, $\PH(1c_\gamma)$,
> $\PH(0c_\gamma)$ and $\PH$ of every shift of these words are transcendental. In particular
> they are transcendental at the resonance slope $\gamma=\beta=\log_3 2$, \emph{with no
> hypothesis on the partial quotients of $\log_2 3$}.

`cons true (charWord γ)` is the paper's `1c_γ` and `cons false (charWord γ)` is `0c_γ`; the
transfer is the paper's eq. (12), `2Φ(c) = 3Φ(1c) + 1 = Φ(0c)`, proved as `IsBL.transfer`.

### 3.4 The headline slope

```lean
noncomputable def logThreeTwo : ℝ := Real.log 2 / Real.log 3

theorem irrational_logThreeTwo : Irrational logThreeTwo
lemma   A_logThreeTwo : A logThreeTwo = 1

theorem transcendental_PhiBL_logThreeTwo :
    Transcendental ℚ ((PhiBL (charWord logThreeTwo) : ℚ_[2])) ∧
    Transcendental ℚ ((PhiBL (cons true (charWord logThreeTwo)) : ℚ_[2])) ∧
    Transcendental ℚ ((PhiBL (cons false (charWord logThreeTwo)) : ℚ_[2]))
```

**Plain English.**  At the resonance slope `β = log₃2` the three numbers are transcendental,
with no hypothesis at all beyond Ridout's theorem.

**⚑ Misreadable 16 — `log₃2` versus `log₂3`.**  `logThreeTwo = log 2 / log 3 = log₃ 2 ≈ 0.6309`
is the **slope**; `log2three = log 3 / log 2 = log₂ 3 ≈ 1.585` is the **height cost**.  They
are reciprocals, and `A(log₃2) = max(1, 1) = 1` is exactly that reciprocity
(`logThreeTwo_mul_log2three : logThreeTwo * log2three = 1`).

**⚑ Misreadable 17 — the irrationality of `log₃2` is proved here, from scratch.**  Mathlib
has no irrationality statement for logarithms, so `irrational_logThreeTwo` is proved from
`2^b ≠ 3^a` (`two_pow_ne_three_pow`).  It is **not** an axiom and **not** imported.

### 3.5 The floor, now a theorem

```lean
theorem one_add_phi_le_max {x : ℝ} (hx : 0 < x) : 1 + phi ≤ max (x + 1) (2 + 1 / x)
lemma   max_eq_one_add_phi_at_phi : max (phi + 1) (2 + 1 / phi) = 1 + phi

theorem one_add_phi_le_ice {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hirr : Irrational γ) :
    ENNReal.ofReal (1 + phi) ≤ ice (charWord γ)

theorem two_lt_ice {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hirr : Irrational γ) :
    2 < ice (charWord γ)
```

**Plain English.**  Every characteristic Sturmian word of irrational slope begins in
arbitrarily long `(1+φ−ε)`-th powers of its own prefixes.

**The paper** (Proposition 2.8), verbatim:

> For every irrational $\gamma$,
> $$\ice(c_\gamma)\;\ge\;1+\varphi=\varphi^{2}=\frac{3+\sqrt5}{2}=2.6180339887\ldots,$$
> with equality if and only if $a_k=1$ for all large $k$.

**⚑ Misreadable 18 — only the inequality.**  The Lean theorem is the inequality.  The
equality clause ("if and only if `a_k = 1` for all large `k`") is **not formalised** and is
not used; see §5.7.  What *is* recorded is that the elementary bound is sharp
(`max_eq_one_add_phi_at_phi`), so this proof attains `1+φ` in the limit and cannot improve it.

**⚑ Misreadable 19 — attribution.**  The constant `1+φ` is Berthé–Holton–Zamboni's
(Acta Arith. **122** (2006), §4.2).  **No novelty is claimed** for the Lean proof.  It is
independent of their paper only because that paper was never accessible; see §6.1 for a
correction about the paper's own route.

**⚑ Misreadable 20 — `0 < γ < 1` is carried, though the paper says only "irrational `γ`".**
Proposition 2.8 as printed quantifies over every irrational `γ`; the Lean theorem adds
`0 < γ` and `γ < 1`.  That is not a weakening of anything used, because `c_γ` is only
defined for `γ ∈ (0,1)` in both the paper (§2.2, "For irrational `γ ∈ (0,1)`") and Lean, but
a reader comparing the two statements side by side will see two extra hypotheses.

### 3.6 Every shift — Corollary 1.4 in full (new at v1.1)

```lean
lemma transcendental_affine {y : ℚ_[2]} (a b : ℚ) (ha : a ≠ 0)
    (hy : Transcendental ℚ y) : Transcendental ℚ ((a : ℚ_[2]) * y + (b : ℚ_[2]))

theorem IsBL.transcendental_shiftIter (h : IsBL Φ) {v : Word}
    (hv : Transcendental ℚ ((Φ v : ℚ_[2]))) (m : ℕ) :
    Transcendental ℚ ((Φ (shiftIter m v) : ℚ_[2]))

theorem transcendental_PhiBL_shifts {γ : ℝ}
    (hγ0 : 0 < γ) (hirr : Irrational γ) (hγs : γ < gammaStar) (m : ℕ) :
    Transcendental ℚ ((PhiBL (shiftIter m (charWord γ)) : ℚ_[2])) ∧
    Transcendental ℚ ((PhiBL (shiftIter m (cons true (charWord γ))) : ℚ_[2])) ∧
    Transcendental ℚ ((PhiBL (shiftIter m (cons false (charWord γ))) : ℚ_[2]))

theorem transcendental_PhiBL_shiftIter_mechanical {γ : ℝ}
    (hγ0 : 0 < γ) (hirr : Irrational γ) (hγs : γ < gammaStar) (k : ℕ) :
    Transcendental ℚ ((PhiBL (shiftIter k (cons true (charWord γ))) : ℚ_[2]))

theorem transcendental_PhiBL_logThreeTwo_shifts (m : ℕ) : …   -- the same at γ = log₃2
```

**Plain English.**  For every irrational slope below `γ*`, `Φ` of *every* shift of `c_γ`,
`1c_γ` and `0c_γ` is transcendental.

**The paper** — Theorem 1.3, verbatim:

> Then $\PH(c_\gamma)$ is transcendental, and so are $\PH(1c_\gamma)$, $\PH(0c_\gamma)$ and
> $\PH(\sigma^k 1c_\gamma)$ for every $k\ge0$.

and Corollary 1.4, verbatim:

> the numbers $\PH(c_\gamma)$, $\PH(1c_\gamma)$, $\PH(0c_\gamma)$ and $\PH$ of every shift
> of these words are transcendental

**How.**  `IsBL.affinegen` is the paper's eq. (3),
`2^m Φ(σ^m v) = 3^{k_m(v)} Φ(v) + c_m(v)`, a relation with rational coefficients whose
leading coefficient `3^{k_m(v)}/2^m` is never zero.  `transcendental_affine` (the forward
direction of the existing `isAlgebraic_affine`) then propagates transcendence.

**⚑ Misreadable 21 — "every shift of these words" is three families, and they overlap.**
`shiftIter 1 (cons true w) = w` and `shiftIter 1 (cons false w) = w` (both machine-checked),
so `σ(1c_γ) = σ(0c_γ) = c_γ` and the shift closure of the three words is
`{σ^m c_γ : m ≥ 0} ∪ {1c_γ, 0c_γ}`.  `transcendental_PhiBL_shifts` states all three families
anyway, so no reading of "every shift" is left out.  `m = 0` recovers §3.3 (also
machine-checked).

**⚑ Misreadable 22 — `shiftIter m v n = v (n + m)`, and the paper's `σ` is the same shift.**
No index shift beyond the one in §2.1: `shiftIter m (charWord γ)` is the paper's
`σ^m c_γ` with `c_γ` indexed from 1 as always.

---

## 4. Things a reader could misread — consolidated, plus four not yet listed

Misreadables 1–20 are at their statements above.  Four more are global.

### 4.1 The elementary route at `γ_A` is redundant, not a second result

`gammaTierA = 6/(5 log₂3) ≈ 0.7571` and `transcendental_charWord_tierA` and its two
companions are **subsumed** by §3.2–3.3 since Tier B.  They are retained because they
record that the headline case never needed the constant `1+φ` at all, only `e > 2`.  A
reader should not read the existence of two thresholds as two different ranges of validity:
the operative range is `γ < γ*`.

### 4.2 `γ* < 1` — RESOLVED at v1.1

Through v1 the main theorems carried both `γ < 1` and `γ < γ*`, because `γ* < 1` was not
proved; the hypothesis set was therefore *formally* slightly stronger than Corollary 1.4's.
Now proved:

```lean
lemma four_thirds_lt_log2three : (4 : ℝ) / 3 < log2three
lemma one_add_phi_lt_two_mul_log2three : 1 + phi < 2 * log2three
theorem gammaStar_lt_one : gammaStar < 1
lemma lt_one_of_lt_gammaStar {γ : ℝ} (hγ : γ < gammaStar) : γ < 1
```

The rational witness `4/3` is chosen to sit strictly between `(3+√5)/4 = 1.30901…` and
`log₂3 = 1.58496…`; `4/3 < log₂3` is `2^4 < 3^3`, and `(3+√5)/4 < 4/3` is `45 < 49`.  No
decimal expansion of either side is used.  `γ < 1` is dropped from
`transcendental_charWord`, `transcendental_PhiBL_charWord`,
`transcendental_PhiBL_mechanical`, `transcendental_PhiBL_shifts` and the three `tierA`
theorems, so their hypotheses are exactly `0 < γ`, `Irrational γ`, `γ < γ*`.

**⚑ Still carried where it is genuinely needed.**  `one_add_phi_le_ice`, `two_lt_ice`,
`twelve_fifths_le_ice`, `le_ice_of_lt_one_add_phi` and `transcendental_of_prefix_family`
keep `γ < 1`: none of them assumes `γ < γ*`, and `charWord_ne_per` needs `γ ∈ (0,1)`.

### 4.3 `ice` enters the main theorems only through a lower bound

`transcendental_charWord` does not mention `ice`.  It fixes `e` strictly between
`max(2A(γ), 2)` and `1+φ`, then uses `one_add_phi_le_ice` and
`exists_prefix_power_of_lt_ice`.  So the development never computes `ice(c_γ)`; it only ever
bounds it below.  Proposition 2.6, the exact formula, is not formalised and not needed
(§5.2).

### 4.4 No irrationality result of the literature is used

Neither Proposition 2.10 (the author's prior work), nor Cassidy's, nor Pham's.  Irrationality
enters only in proved form: the 2-adic Liouville inequality `liouville_two_adic`, whence
`ne_rat_of_ApproxExp`; the aperiodicity `charWord_ne_per`, which uses the **hypothesis**
`Irrational γ` on the slope and is the only place that hypothesis is used; and, for the
headline slope, `irrational_logThreeTwo`.  Detail and the normalisation note in `AXIOMS.md`
§5 — summarised: the paper's `ω` is Koksma's `w₁`, whose witnessing family for a rational is
infinitely many *polynomials* representing one point, while `ApproxExp` asks for infinitely
many *distinct rationals*.  Different quantifiers, no conflict.

---

## 5. Claims of the paper NOT covered

Listed so that scope is not inferred from the directory name.  None of these is used by
anything that *is* proved.

**5.1 Theorem 1.2 (quantitative form).**  `ω(Φ(c_γ)) ≥ ice(c_γ)/A(γ) − 1`.  **Not
formalised.**  The Koksma exponent `ω` is not defined in Lean at all; `ApproxExp` is a
different quantifier (§4.4).  Formalising Theorem 1.2 would need `ω` and the second equality
`ice = 1 + limsup q_{k+1}/q_k`, i.e. Proposition 2.6.

**5.2 Proposition 2.6 (the `ice` formula).**  `ice(c_α) = limsup (q_{k+1}+q_k−2)/q_k = 1 + limsup q_{k+1}/q_k`.
**Not formalised**, and deliberately: Mathlib has no best-approximation property for
continued-fraction convergents, so the development works with *records* instead and proves
only the lower bound it needs.  The `q_{k+1}+q_k−2` depth does appear, as `Q + q − 2` in
`per_eq_of_min`, but indexed by records rather than convergents.

**5.3 Theorem 1.3 under its own hypothesis (T).**  The paper's hypothesis is
`ice(c_γ) > 2A(γ)`.  **No Lean theorem is stated with that hypothesis.**  What is proved is
the `γ < γ*` instance (§3.2–3.3) and the engine (§3.1) with a hypothesis that is (T) unrolled
into a prefix family.  Note `A(γ) ≥ 1` always, so (T) implies `e > 2` automatically; a
statement with hypothesis `ENNReal.ofReal (2 * A γ) < ice (charWord γ)` is derivable from the
existing pieces and is **not** currently stated.

**5.4 The shifts — COVERED at v1.1, no longer a gap.**  Theorem 1.3's clause
`Φ(σ^k 1c_γ)` for every `k ≥ 0`, and Corollary 1.4's "`Φ` of every shift of these words",
are now `transcendental_PhiBL_shifts` and `transcendental_PhiBL_shiftIter_mechanical`
(§3.6), by the route this review identified: eq. (3) as a rational-affine relation.
**Corollary 1.4 is formalised in full.**

**5.5 Theorem 6.1 (the Liouville alternative).**  For irrational `γ` with unbounded partial
quotients, `ice = ∞` and the conclusion sharpens to a Liouville statement.  **Not
formalised.**  Needs Proposition 2.6 (§5.2) to see `ice = ∞` from unboundedness.

**5.6 Theorem 7.3 (finite effective measure).**  For `γ ∈ (0,β]` irrational with bounded
partial quotients, `Φ(c_γ)` has a finite effective irrationality measure, with explicit
constants (Lemmas 7.1, 7.2).  **Not formalised.**

**5.7 The equality case of Proposition 2.8.**  `ice(c_γ) = 1+φ` iff `a_k = 1` for all large
`k`.  **Not formalised**, never asserted even as an axiom, and used nowhere.

**5.8 Everything outside §§1–3 of the paper.**  §4 (the parity obstruction, Example 4.1),
§5 (truncations: Propositions 5.1, 5.3), §8 (scope, Questions 8.1–8.2), Appendix A
(Theorem R from Schlickewei), Appendix B (exact-arithmetic verification).  **None
formalised**, and the paper itself does not rest on Appendix A ("nothing depends on it").
Proposition 2.3 (`[BHZ06, Prop. 3.2]`) is **not used**: balance for prefixes of `c_γ` is
proved directly as `abs_balance_prefix`, so the primitive-root replacement is unnecessary.

---

## 6. Corrections this review found

### 6.1 The paper has its own re-derivation of the floor — Lemma 2.9  *(RESOLVED at v1.1)*

`AXIOMS.md` and the README said, through stage 4 and again at stage 5, that Proposition 2.8
rests on "the paper's own two-line deduction from an *unnumbered sentence* in BHZ §4.2".
**That was incomplete.**  Immediately after Proposition 2.8 the paper says, verbatim:

> For completeness we record the elementary re-derivation of the floor; it is not a new
> result.

> **Lemma 2.9 (Re-derivation of Proposition 2.8).** For every irrational
> $\gamma=[0;a_1,a_2,\dots]$ one has $\limsup_k q_{k+1}/q_k\ge\varphi$, with equality if and
> only if $a_k=1$ for all large $k$.

with a four-line continued-fraction proof (`q_{k+1}/q_k = a_{k+1} + q_{k−1}/q_k > a_{k+1}`;
if the limsup were `< φ < 2` then eventually `a_{k+1} = 1`, the ratios satisfy
`x_{k+1} = 1 + 1/x_k` and converge to `φ`, contradiction).

So the paper's route to the floor is **Proposition 2.6 (cited to BHZ) + Lemma 2.9
(elementary, in the paper)**, not a bare citation.  Three consequences, stated precisely:

* The description in `AXIOMS.md` §2 of what a reader must check at the BHZ source was about
  the *citation of Proposition 2.8*; the paper separately gives a self-contained proof of the
  arithmetic half.  The source-inaccessibility note stands, but it was never the only route
  even inside the paper.
* **The Lean proof is not a formalisation of Lemma 2.9.**  Lemma 2.9 is a statement about
  continued-fraction convergents and uses the recursion `q_{k+1} = a_{k+1} q_k + q_{k−1}`;
  Mathlib's missing best-approximation property is exactly what made that route unavailable.
  `one_add_phi_le_ice` instead proves the *combination* of Proposition 2.6's lower bound and
  Lemma 2.9 in one step, from records.
* **The claim "no novelty" is if anything strengthened**, since the paper already states the
  elementary argument and labels it "not a new result".

**Amended at v1.1.**  `AXIOMS.md` §2 (new subsection "The paper's own route, and how the
Lean proof relates to it") and §9, and the README's "What is assumed" section, now state the
two routes, say that the Lean proof follows neither exactly, keep the no-novelty statement,
and keep the note that the BHZ source was never accessible.  The reader-verification list is
extended from two items to three: the §4.2 sentence, `θ = (1+√5)/2` on p. 3, **and** the
formula of Proposition 2.6, which is also cited to BHZ §4.2.

### 6.2 Two errata already on record, unchanged

* `paper/refs.bib`, `BK18`: `doi = {10.1017/S0004972718000345}` resolves to De Bondt–Sun, a
  different article in the same volume.  Correct DOI: **`10.1017/S0004972718000515`**.
  Author, journal, volume, number and pages are all correct.  (`AXIOMS.md` §6.)
* `papers/sturmian-transcendence/README.md`, "Related work and credit", attributes the
  single-prime form of Ridout to **Badziahin–Kristensen**; the paper's `BK18` and printed
  ref. [7] are **Bugeaud–Kekeç**.  Flagged, not edited.  (`AXIOMS.md` §7.)

---

## 7. Verdict on item 3 of the review brief

* **Do the main theorems quantify over every irrational `γ < γ*`?**  Yes — `hγ0 : 0 < γ`,
  `hirr : Irrational γ`, `hγs : γ < gammaStar`, with no hypothesis on the partial quotients,
  and `γ` ranging over `ℝ`.  Since v1.1 these are **exactly** the paper's hypotheses:
  `γ* < 1` is proved (§4.2), so `γ < 1` is derived rather than assumed.
* **Do they cover `Φ(c_γ)`, `Φ(1c_γ)`, `Φ(0c_γ)`?**  Yes — §3.3, and at `γ = log₃2`
  specifically in §3.4.  Since v1.1, **every shift** of all three as well (§3.6), so
  Corollary 1.4 is formalised in full.
* **What of the paper is not covered?**  §5 above.  After v1.1 nothing inside
  Theorem 1.3 / Corollary 1.4 is missing; everything still uncovered is a separate theorem
  of the paper (1.2, 6.1, 7.3), an unused cited proposition (2.3, 2.6, 2.10), the equality
  half of Proposition 2.8, or material outside §§1–3.
