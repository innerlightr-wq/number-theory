/-
# Axioms

The ONLY file in this development permitted to contain `axiom`.  Every axiom carries:
its statement as the paper states it, the original source with the exact theorem number,
and the paper's citation key.

STAGE 1 declares exactly one axiom: Theorem R.
STAGE 2 adds exactly two more, both named by the brief and both clearly labelled:
the Berthé–Holton–Zamboni prefix-power input and the paper's height bound (Prop. 2.4).
-/
import Sturmian.Basic
import Sturmian.Shadow
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Sturmian

/-! ## Axiom R — Ridout's theorem, single-prime form

**Paper's citation key:** `BK18`, used as `\cite[Theorem 1.3]{BK18}`.

**Paper's statement** (`paper/main.tex`, `\begin{theoremR}`, §2.4, printed p. 8), verbatim:

> `\begin{theoremR}[{\cite[Theorem 1.3]{BK18}, attributed there to Ridout \cite{Ridout58}}]`
> Let $\xi$ be a $p$-adic number and $\varepsilon>0$. Suppose there is a sequence
> $(x_n/y_n)_{n\ge1}$ of rationals with $\gcd(x_n,y_n)=1$,
> $2\le|x_1,y_1|<|x_2,y_2|<\cdots$, and
> \[ 0<\Bigl|\xi-\frac{x_n}{y_n}\Bigr|_p<|x_n,y_n|^{-2-\varepsilon}\qquad(n=1,2,\dots), \]
> where $|x,y|:=\max(|x|,|y|)$ is the height of $x/y$. Then $\xi$ is transcendental.
> `\end{theoremR}`

**Original source**, verified against the author's own copy of the article
(`irma.math.unistra.fr/~bugeaud/travaux/BuKe1.pdf`, printed pp. 2–3):

> Yann Bugeaud and Gülcan Kekeç, *On Mahler's classification of p-adic numbers*,
> Bull. Austral. Math. Soc. **98** (2018), no. 2, 203–211.
>
> "For coprime non-zero integers $x$, $y$, write $|x,y|$ for the maximum of $|x|$ and
> $|y|$, that is, for the height of the rational number $x/y$.
>
> **Theorem 1.3 (Ridout [11], 1958).** Let $\xi$ be a $p$-adic number and $\varepsilon$ a
> positive real number. Suppose that there exists a sequence $(x_n/y_n)_{n=1}^{\infty}$ of
> rational numbers with $\gcd(x_n,y_n)=1$ $(n=1,2,\dots)$ such that
> $2\le|x_1,y_1|<|x_2,y_2|<\cdots$ and
> $0<\bigl|\xi-\frac{x_n}{y_n}\bigr|_p<|x_n,y_n|^{-2-\varepsilon}$ $(n=1,2,\dots)$.
> Then $\xi$ is transcendental."

**Hypothesis comparison: EXACT MATCH.**  Every hypothesis of the source is present in the
paper's quotation and in the Lean statement below, with no weakening:

| hypothesis | source | paper | Lean below |
|---|---|---|---|
| `ξ` an arbitrary `p`-adic number, no condition on its minimal polynomial | yes | yes | `ξ : ℚ_[p]` |
| `ε > 0` | yes | yes | `hε : 0 < ε` |
| coprimality `gcd(xₙ,yₙ) = 1` | yes | yes | automatic: `Rat` is in lowest terms |
| `2 ≤ |x₁,y₁|` | yes | yes | `h2 : 2 ≤ H (x 0)` |
| heights strictly increasing | yes | yes | `hmono : StrictMono (H ∘ x)` |
| strict lower bound `0 < |ξ − xₙ/yₙ|_p` | yes | yes | `hpos` |
| strict upper bound, exponent `−2−ε` | yes | yes | `hlt` |
| height `|x,y| = max(|x|,|y|)` | yes | yes | `Sturmian.H` |
| conclusion: `ξ` transcendental | yes | yes | `Transcendental ℚ ξ` |

Two conventions recorded rather than elided.
*First*, the source defines `|x,y|` for coprime **non-zero** integers.  A rational with
`x = 0` has height `1`, which the hypothesis `2 ≤ H (x 0)` together with strict monotonicity
excludes, so the Lean statement never evaluates the height outside the source's range.
*Second*, `Transcendental ℚ ξ` unfolds to `¬ IsAlgebraic ℚ ξ`.  Since every rational is
algebraic over `ℚ`, this conclusion already excludes `ξ ∈ ℚ`; the paper's separate
irrationality input (its Proposition 2.10) is needed for its `ω`-based route, not for the
skeleton — see `Sturmian/Liouville.lean` and `AXIOMS.md`.

**Status:** external published theorem (Ridout 1958, in the single-prime form of
Bugeaud–Kekeç 2018, Theorem 1.3).  Not proved here and not expected to be.

**Erratum found while checking this axiom** (see `AXIOMS.md`): the paper's `refs.bib` gives
`doi = {10.1017/S0004972718000345}` for `BK18`.  That DOI resolves to a different article in
the same volume (De Bondt–Sun, *Classification of cubic homogeneous polynomial maps with
Jacobian matrices of rank two*, Bull. Austral. Math. Soc. **98** (2018), 89–101).  The
correct DOI is `10.1017/S0004972718000515`.  Author, journal, volume, number and pages in
`refs.bib` are all correct; only the DOI string is wrong.
-/
axiom ridout_single_prime {p : ℕ} [Fact p.Prime]
    (ξ : ℚ_[p]) (ε : ℝ) (hε : 0 < ε) (x : ℕ → ℚ)
    (h2 : 2 ≤ H (x 0))
    (hmono : StrictMono fun n => H (x n))
    (hpos : ∀ n, 0 < ‖ξ - (x n : ℚ_[p])‖)
    (hlt : ∀ n, ‖ξ - (x n : ℚ_[p])‖ < (H (x n) : ℝ) ^ (-2 - ε)) :
    Transcendental ℚ ξ

/-! ## Axiom BHZ — the prefix-power family of Steps 1–2

**Status: EXTERNAL PUBLISHED THEOREM (the floor) COMBINED WITH THE PAPER'S OWN STEPS 1–2
(the extraction), NOT YET FORMALIZED.**  To be discharged in stage 3.

**The external ingredient** is the paper's Proposition 2.8 (`{Floor; \cite[\S4.2]{BHZ06}}`),
verbatim:

> "For every irrational $\gamma$,
>  $$\ice(c_\gamma)\;\ge\;1+\varphi=\varphi^{2}=\frac{3+\sqrt5}{2}=2.6180339887\ldots,$$
>  with equality if and only if $a_k=1$ for all large $k$."

together with the paper's Definition 2.5 (`\cite[\S2]{BHZ06}`) of `ice` and its remark

> "Because the prefix power is defined as the largest *real* such $p$, we have
>  $\lcp(\omega,W^{\infty})=p\,|W|$ *exactly*: no floor and no $O(1)$ is lost".

**The paper's own part** is Step 1 ("fix a real `e` with `max(2A(γ),2) < e < ice(c_γ)`") and
Step 2 ("choose an infinite sequence `W_1, W_2, …` of **primitive** prefixes of `c_γ` with
`ℓ_j := |W_j| → ∞`, `ℓ_j ≥ 2`, and `lcp(c_γ, W_j^∞) ≥ e ℓ_j`").

**NARROWED AT STAGE 3.**  At stage 2 this axiom also asserted three further clauses of the
paper's Step 4.  All three are now **proved** and have been removed from it:

* `k_j ≥ 1` for large `j` — proved from the telescoping count
  `Sturmian.ones_charWord` (`k_ℓ(c_γ) = ⌊(ℓ+1)γ⌋`) together with `ℓ_j → ∞`;
* `c_γ ≠ W_j^∞` — proved as `Sturmian.charWord_ne_per`, the aperiodicity of `c_γ` for
  irrational `γ`, which is the one place irrationality is used;
* injectivity of `j ↦ W_j^∞` — no longer needed at all: the infinitude of the shadow set is
  derived instead from the fact that each shadow is approached to depth `e ℓ_j → ∞`, so each
  value is taken only finitely often (`transcendental_of_prefix_family`).

What remains is only: the lengths are at least `2`, they tend to infinity, and the first
`⌈e ℓ_j⌉` letters agree.

The depth is stated below as *agreement of the first `⌈e ℓ_j⌉` letters*, which is
`lcp ≥ e ℓ_j` without naming `lcp`, and so needs no side condition.  `ice` itself is **not**
formalized, which is exactly why this is an axiom rather than a theorem. -/
axiom bhz_prefix_family {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hirr : Irrational γ)
    {e : ℝ} (he2 : 2 < e) (heφ : e < 1 + phi) :
    ∃ (ℓ : ℕ → ℕ) (W : ℕ → Word),
      (∀ j, 2 ≤ ℓ j) ∧
      Filter.Tendsto (fun j => (ℓ j : ℝ)) Filter.atTop Filter.atTop ∧
      (∀ j (n : ℕ), (n : ℝ) < e * (ℓ j : ℝ) → charWord γ n = per (ℓ j) (W j) n)

/-! ## Axiom DJ10.4 — the numerator bound of the paper's Proposition 2.4

**Status: AUTHOR'S PRIOR RESULT, NOT YET FORMALIZED.**  Added at stage 3, where it replaced
the coarser `shadow_height_bound` axiom of stage 2: **Proposition 2.4 is now a theorem**
(`Sturmian.shadow_height_bound` in `Sturmian/Height.lean`), proved from the paper's own
four-line argument plus this one input.

The paper's Proposition 2.4 reads

> `\begin{proposition}[{Height of a shadow; \cite[Lemma 10.4]{DJirr}, resting on
> \cite[Lemma 43]{LS21}}]`
> Let $W$ be a conjugate of a standard word, $|W|=\ell$, with $k\ge1$ ones, and suppose
> $W$ is a factor of a Sturmian word of slope $\gamma$. Then
> $0<c_W\le3\ell\max(2^{\ell},3^{k})$ and
> $$\log_2 H\bigl(\PH(W^{\infty})\bigr)\;<\;\Av\,\ell+\log_2(3\ell)+\log_2 3 .$$

and its proof identifies exactly which part is external:

> "and $c_W\le3\ell\max(2^{\ell},3^{k})$ by \cite[Lemma 10.4]{DJirr}, whose input is that
>  $W^{\infty}$ is balanced, so that $|k_{i+1}(W)-(i+1)k/\ell|<1$."

**That numerator bound is all this axiom asserts.**  `0 < c_W` is **proved**
(`Sturmian.cw_pos`), the conclusion of Proposition 2.4 is **proved**
(`Sturmian.shadow_height_bound`), and the balance bound `|k − γℓ| < 1` the proof also needs
is **proved** for prefixes (`Sturmian.abs_ones_charWord_sub_lt_one`), by telescoping, rather
than quoted.

Source: `DJirr` = the author's *The 3x+1 conjugacy map sends every Sturmian word to an
irrational 2-adic integer*, doi:10.5281/zenodo.23108370, Lemma 10.4 — **unrefereed**, and
**NOT CHECKED** here.  Hypotheses are expressed as in stage 2: `|W| ≥ 2`, `k ≥ 1`, and
`c_γ` begins in `W²` (whence `W` is a conjugate of a standard word by the paper's
Proposition 2.3, and a factor of `c_γ`). -/
axiom cw_le_three_mul_len_mul_max {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (ℓ : ℕ) (W : Word)
    (hℓ : 2 ≤ ℓ) (hk : 1 ≤ ones ℓ W)
    (hpref : ∀ n : ℕ, (n : ℝ) < 2 * (ℓ : ℝ) → charWord γ n = per ℓ W n) :
    cw ℓ W ≤ 3 * (ℓ : ℤ) * max ((2 : ℤ) ^ ℓ) (3 ^ (ones ℓ W))

end Sturmian
