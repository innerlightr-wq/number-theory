/-
# Stage 4, item 1 — definition audit

Each definition is printed beside the paper's verbatim text, with the page or equation, and
followed by a machine-checked sanity lemma.  **No mismatch was found.**  Three conventions
needed an explicit note and have one; they are flagged ⚑ below.

Paper = `papers/sturmian-transcendence/paper/main.tex` / `main.pdf`, 20 pp,
concept DOI 10.5281/zenodo.23210794.  Printed page numbers are the PDF's.
-/
import Sturmian.Numerator
import Sturmian.Ice
import Sturmian.Construct

namespace Sturmian

/-! ## 1. `charWord` — the characteristic Sturmian word

**Paper, §2.2, p. 6:**

> "For irrational $\gamma\in(0,1)$ the characteristic word is
>  $c_\gamma(j)=\lfloor(j+1)\gamma\rfloor-\lfloor j\gamma\rfloor$ for $j\ge1$, and
>  $1c_\gamma$, $0c_\gamma$ are $1$, resp.\ $0$, followed by $c_\gamma$".

**Lean:** `charWord γ n = decide (⌊((n:ℝ)+2)*γ⌋ - ⌊((n:ℝ)+1)*γ⌋ = 1)`.

**⚑ CONVENTION 1 (index shift).**  The paper's letters are indexed from `j = 1`; `Word` is
indexed from `0`.  So `charWord γ n` is the paper's `c_γ(n+1)`, i.e. `n ↦ j = n+1`.  This is
recorded in `Sturmian/Word.lean` and is the only index convention in the development.

Sanity check at `γ = 2/5`: the paper's `c_γ(j)` for `j = 1,2,3,4,5` is
`0,1,0,1,0`, since `⌊jγ⌋ = 0,0,1,1,2,2` for `j = 1,…,6`.  So `charWord (2/5)` must begin
`0,1,0,1,0`. -/

example : charWord (2/5) 0 = false := by norm_num [charWord]
example : charWord (2/5) 1 = true := by norm_num [charWord]
example : charWord (2/5) 2 = false := by norm_num [charWord]
example : charWord (2/5) 3 = true := by norm_num [charWord]
example : charWord (2/5) 4 = false := by norm_num [charWord]

/-- Cross-check of the telescoping count against the hand count: the word above has two
ones among its first five letters, and `ones_charWord` predicts `⌊6·(2/5)⌋ = ⌊2.4⌋ = 2`. -/
example : ones 5 (charWord (2/5)) = 2 := by
  have h : ((ones 5 (charWord (2/5)) : ℤ)) = ⌊((5 : ℝ) + 1) * (2/5)⌋ :=
    ones_charWord (by norm_num) (by norm_num) 5
  have h2 : ⌊((5 : ℝ) + 1) * (2/5)⌋ = 2 := by norm_num
  rw [h2] at h
  omega

/-! ## 2. `Φ` — the Bernstein–Lagarias conjugacy map

**Paper, §1.1, pp. 1–2, eqs. (1)–(2):**

> "Bernstein and Lagarias [3, 1] proved that $T$ and $S$ are conjugate: there is a unique
>  homeomorphism $\PH:\Z_2\to\Z_2$ with $\PH(0)=0$ and $\PH\circ S\circ\PH^{-1}=T$. …
>  $\PH(v)$ is the unique $x\in\Zt$ whose parity vector is $v$, and (1) reads
>  $\PH(\sigma v)=T(\PH(v))$."

**Lean:** `IsBL Φ` (`Sturmian/BL.lean`) is eq. (2) unpacked by the first letter —
`Φ(0c) = 2Φ(c)` and `3Φ(1c) = 2Φ(c) − 1` — and `PhiBL` (`Sturmian/Construct.lean`) is a
constructed witness.

**⚑ CONVENTION 2.**  `IsBL` is eq. (2) *together with* the parity fact "`Φ(v)` is odd iff
`v₀ = 1`", which the paper quotes from `\cite[\S1]{BL96}` in §2.1.  Unpacking eq. (2) needs
that fact to know which branch of `T` applies.  It is then *derived* from `IsBL`
(`IsBL.norm_cons_true`), so it is not assumed twice.

Sanity check, two independent routes to the same value.  The all-ones word is fixed by the
shift, so eq. (2) forces `Φ(1^∞) = T(Φ(1^∞))`, i.e. `3x = 2x − 1`, i.e. `x = −1`; and
indeed `T(−1) = (3(−1)+1)/2 = −1` with `−1` odd.  Proposition 2.2 must agree: `ℓ = 1`,
`k = 1`, `c_W = 1`, `2^1 − 3^1 = −1`, so `c_W/(2^ℓ−3^k) = −1`. -/

/-- Route A — from the recursion (eq. (2)). -/
example {Φ : Word → ℤ_[2]} (h : IsBL Φ) : Φ (fun _ => true) = -1 := by
  have hfix : cons true (fun _ => true) = (fun _ => true : Word) := by
    funext n; cases n with
    | zero => rfl
    | succ m => rfl
  have h3 := h.cons_true (fun _ => true)
  rw [hfix] at h3
  linear_combination h3

/-- Route B — from Proposition 2.2's explicit rational. -/
example : shadowRat 1 (fun _ => true) = -1 := by
  have h1 : ones 1 (fun _ => true : Word) = 1 := by decide
  have h2 : cw 1 (fun _ => true : Word) = 1 := by decide
  rw [shadowRat, h1, h2]; norm_num

/-- `Φ(0^∞) = 0`, matching the paper's normalisation `Φ(0) = 0`. -/
example : shadowRat 1 (fun _ => false) = 0 := by
  have h1 : ones 1 (fun _ => false : Word) = 0 := by decide
  have h2 : cw 1 (fun _ => false : Word) = 0 := by decide
  rw [shadowRat, h1, h2]; norm_num

/-- `Φ((10)^∞) = 1`: the parity vector of `1` is `1,0,1,0,…` since `T(1) = 2`, `T(2) = 1`.
Proposition 2.2 gives `ℓ = 2`, `k = 1`, `c_W = 1`, `2² − 3 = 1`. -/
example : shadowRat 2 (fun n => n % 2 == 0) = 1 := by
  have h1 : ones 2 (fun n => n % 2 == 0 : Word) = 1 := by decide
  have h2 : cw 2 (fun n => n % 2 == 0 : Word) = 1 := by decide
  rw [shadowRat, h1, h2]; norm_num

/-! ## 3. `H` — the height

**Paper, §2.2, p. 6 and §2.4, p. 7:**

> "For $x=u/v\in\Q$ in lowest terms with $v>0$ we write $H(x)=\max(|u|,v)$."
> "For $\xi\in\Zt$ and $r\in\Q$ put $H(r)=\max(|\mathrm{num}|,\mathrm{den})$ as above".

**Lean:** `H r = max r.num.natAbs r.den`.  Lean's `Rat` is always in lowest terms with
`den > 0`, which is the paper's "in lowest terms with `v>0`". -/

example : H (3/4) = 4 := by norm_num [H]
example : H (-5/2) = 5 := by norm_num [H]
example : H 0 = 1 := by norm_num [H]
example : H (-1) = 1 := by norm_num [H]

/-! ## 4. `lcp` and the 2-adic exponent — indexing

**Paper, §2.1, p. 5:**

> "Throughout, $\vtwo$ is the $2$-adic valuation, $|x|_2=2^{-\vtwo(x)}$, and for words
>  $v,w\in\{0,1\}^{\N}$, $\lcp(v,w)$ is the length of their longest common prefix."

**Lean:** `lcp v w h = Nat.find (fun n => v n ≠ w n)` for `v ≠ w` — the least index of
disagreement, which is the length of the longest common prefix.  Proposition 2.1 is stated
in the paper's own equivalent form `|Φ(v)−Φ(w)|₂ = 2^{−lcp(v,w)}`, which fixes the
normalisation without committing to a valuation convention.

Sanity check: two words first differing at index `3` have `lcp = 3`, i.e. they agree on
exactly the three letters `0,1,2`. -/

example : lcp (fun _ => false) (fun n => n == 3) (by
    intro hh; have h3 := congrFun hh 3; simp at h3) = 3 := by
  rw [lcp, Nat.find_eq_iff]
  refine ⟨by simp, ?_⟩
  intro n hn
  simp only [not_not]
  interval_cases n <;> simp

/-! ## 5. `A(γ)` and `γ*`

**Paper, §1.2, p. 3:**

> "Put $\Av:=\max(1,\gamma\log_2 3),\qquad
>   \gs:=\frac{1+\varphi}{2\log_2 3}=\frac{3+\sqrt5}{4\log_2 3}
>   =0.8258977696818354644\ldots,$ where $\varphi=(1+\sqrt5)/2$".

**Lean:** `A γ = max 1 (γ * log2three)`, `gammaStar = (1 + phi)/(2 * log2three)`,
`phi = (1+√5)/2`, `log2three = Real.log 3 / Real.log 2`.

**⚑ CONVENTION 3.**  `log2three` is `log 3 / log 2`, which is `Real.logb 2 3`; the two are
identified wherever both appear (`max_lt_A_mul` in `Sturmian/Height.lean`).

Sanity check: the two closed forms the paper gives for `γ*` agree, and the paper's
`1+φ = φ² = (3+√5)/2` holds. -/

example : 1 + phi = (3 + Real.sqrt 5) / 2 := by rw [phi]; ring

example : 1 + phi = phi ^ 2 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [phi]; nlinarith [h5]

example : gammaStar = (3 + Real.sqrt 5) / (4 * log2three) := by
  rw [gammaStar, phi]; ring

/-! ## 6. `ice` — the initial critical exponent

**Paper, Definition 2.5, p. 7:**

> "The *prefix power* of a finite word $W$ in a sequence $\omega$ is the largest real $p$
>  such that $W^{p}$ is a prefix of $\omega$; equivalently $\lcp(\omega,W^{\infty})/|W|$.
>  The *initial critical exponent* $\ice(\omega)$ is the limit superior of the prefix powers
>  of the words $\omega[0,n)$ in $\omega$."

**Lean:** `prefixPower ω n = lcp(ω, per n ω)/n`, with the value `⊤` when `ω = per n ω`; and
`ice ω = limsup (prefixPower ω) atTop`, in `ℝ≥0∞`.

The `⊤` branch is forced: when `ω` is `n`-periodic the paper's "largest real `p` such that
`W^p` is a prefix" is unbounded, and `ℝ≥0∞` is what lets `ice = ∞` be a value (the paper's
Case L, `\S3` Step 1).

Sanity check: a periodic word has infinite prefix power at its period. -/

example (ℓ : ℕ) (W : Word) : prefixPower (per ℓ W) ℓ = ⊤ := by
  have h : per ℓ W = per ℓ (per ℓ W) := by funext n; simp [per]
  rw [prefixPower, dif_pos h]

end Sturmian
