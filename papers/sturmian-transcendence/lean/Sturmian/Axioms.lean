/-
# Axioms

The ONLY file in this development permitted to contain `axiom`.  Every axiom carries:
its statement as the paper states it, the original source with the exact theorem number,
and the paper's citation key.

STAGE 1 declares exactly one axiom: Theorem R.
-/
import Sturmian.Basic

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

end Sturmian
