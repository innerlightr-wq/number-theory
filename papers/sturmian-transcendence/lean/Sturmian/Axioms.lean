/-
# Axioms

The ONLY file in this development permitted to contain `axiom`.  Every axiom carries:
its statement as the paper states it, the original source with the exact theorem number,
and the paper's citation key.

STAGE 1 declares exactly one axiom: Theorem R.
STAGE 2 added two more; STAGE 3 turned one into a theorem and narrowed the other;
STAGE 4 removed the numerator-bound axiom entirely; STAGE 5 proved the
Berthé–Holton–Zamboni floor and removed that axiom too.

**ONE axiom remains: Theorem R (Ridout).**
-/
import Sturmian.Basic
import Sturmian.Shadow
import Sturmian.Ice
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

/-! ## Axiom BHZ — REMOVED AT STAGE 5

**`bhz_ice_floor` no longer exists.**  It asserted the paper's Proposition 2.8
(`{Floor; \cite[\S4.2]{BHZ06}}`), verbatim:

> "For every irrational $\gamma$,
>  $$\ice(c_\gamma)\;\ge\;1+\varphi=\varphi^{2}=\frac{3+\sqrt5}{2}=2.6180339887\ldots,$$
>  with equality if and only if $a_k=1$ for all large $k$."

The inequality is now the theorem `Sturmian.one_add_phi_le_ice` in
`Sturmian/Floor.lean`.  (The equality clause was never asserted and is not used.)

**Attribution is unchanged.**  The constant `1 + φ` is Berthé–Holton–Zamboni's — Valérie
Berthé, Charles Holton, Luca Q. Zamboni, *Initial powers of Sturmian sequences*, Acta
Arith. **122** (2006), no. 4, 315–347, §4.2 — and **no novelty is claimed** for the Lean
proof, which is simply a route that could be carried out inside Mathlib: Dirichlet's
theorem, best-approximation records built from their definition (Mathlib has no
best-approximation property for continued-fraction convergents), the gap lemma
`s ≥ r + p` for consecutive records, and the sharp elementary inequality
`max(x + 1, 2 + 1/x) ≥ 1 + φ`.  The source paper remained inaccessible throughout and the
Lean proof does not depend on it; see `AXIOMS.md` §2 and §9.

Everything the paper's Steps 1–2 and Step 4 add was already proved at stage 4:

* the extraction itself — `Sturmian.exists_prefix_power_of_lt_ice`, directly from the
  definition of `ice` as a limit superior (`Sturmian/Ice.lean`);
* the **primitive-root replacement is not needed at all.**  The paper performs it so that
  `\cite[Proposition 3.2]{BHZ06}` applies, giving a conjugate of a standard word, giving
  balance, giving the height bound; and so that minimal periods are distinct, giving Step
  4's distinctness.  Here balance for prefixes of `c_γ` is proved directly
  (`Sturmian.abs_balance_prefix`) and the distinctness was eliminated at stage 3, so the
  extraction may take the prefix itself;
* `k_j ≥ 1` for large `j` — from the telescoping count `Sturmian.ones_charWord`;
* `c_γ ≠ W_j^∞` — `Sturmian.charWord_ne_per`;
* injectivity of `j ↦ W_j^∞` — eliminated (finite fibres).
-/

/-! ## Axioms removed at stage 4

**`cw_le_three_mul_len_mul_max` is gone.**  `[DJirr, Lemma 10.4]` is formalised in
`Sturmian/Numerator.lean` as `Sturmian.cw_le_of_balance` (from the balance hypothesis the
source's own proof uses) and `Sturmian.cw_le_prefix` (balance discharged for prefixes of
`c_γ`).  Proposition 2.4 (`Sturmian.shadow_height_bound`) therefore now depends on **no**
axiom.
-/

end Sturmian
