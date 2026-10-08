/-
# Basic definitions

Every definition here quotes the line of the paper it encodes.

Paper: Elias De Jesús, *Transcendence of the 3x+1 conjugacy map on Sturmian words*,
October 2026, 20 pp., concept DOI 10.5281/zenodo.23210794.
Source of record for this formalisation: `papers/sturmian-transcendence/paper/main.tex`.
-/
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Finite.Basic

namespace Sturmian

open scoped Classical

/-! ## Height

Paper, §2.4 (`\subsection{The normalisation of $\om$ and the threshold}`), first line:

> "For $\xi\in\Zt$ and $r\in\Q$ put $H(r)=\max(|\mathrm{num}|,\mathrm{den})$ as above"

`Rat` in Lean is always in lowest terms with `den > 0`, which is the paper's convention
(the paper's `num`/`den` are the numerator and denominator of `r` in lowest terms, the
denominator positive). So `H r = max r.num.natAbs r.den`.
-/

/-- The height of a rational, `H(r) = max(|num|, den)`, in the paper's normalisation. -/
def H (r : ℚ) : ℕ := max r.num.natAbs r.den

lemma H_pos (r : ℚ) : 0 < H r := lt_of_lt_of_le r.pos (le_max_right _ _)

lemma one_le_H (r : ℚ) : 1 ≤ H r := H_pos r

lemma H_num_le (r : ℚ) : r.num.natAbs ≤ H r := le_max_left _ _

lemma H_den_le (r : ℚ) : r.den ≤ H r := le_max_right _ _

/-- The height determines a rational up to the finitely many choices of `(num, den)`,
so each height is attained by only finitely many rationals.  This is the only
combinatorial input the skeleton needs. -/
lemma finite_setOf_H_le (N : ℕ) : {r : ℚ | H r ≤ N}.Finite := by
  have hinj : Set.InjOn (fun r : ℚ => (r.num, r.den)) {r : ℚ | H r ≤ N} := by
    intro a _ b _ hab
    exact Rat.ext (Prod.mk.injEq .. ▸ hab).1 (Prod.mk.injEq .. ▸ hab).2
  refine Set.Finite.of_finite_image (f := fun r : ℚ => (r.num, r.den)) ?_ hinj
  refine Set.Finite.subset ((Set.finite_Icc (-(N : ℤ)) (N : ℤ)).prod (Set.finite_Iic N)) ?_
  rintro ⟨x, y⟩ ⟨r, hr, hxy⟩
  have hn : r.num.natAbs ≤ N := le_trans (H_num_le r) hr
  have hd : r.den ≤ N := le_trans (H_den_le r) hr
  have habs : |r.num| ≤ (N : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hn
  obtain ⟨hlo, hhi⟩ := abs_le.mp habs
  have hx : x = r.num := ((Prod.mk.injEq ..).mp hxy.symm).1
  have hy : y = r.den := ((Prod.mk.injEq ..).mp hxy.symm).2
  subst hx; subst hy
  exact ⟨⟨hlo, hhi⟩, hd⟩

/-- An infinite set of rationals has unbounded height. -/
lemma exists_H_gt_of_infinite {S : Set ℚ} (hS : S.Infinite) (N : ℕ) :
    ∃ r ∈ S, N < H r := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  exact hS (Set.Finite.subset (finite_setOf_H_le N) (fun r hr => hcon r hr))

/-! ## The 2-adic Koksma exponent, in the paper's normalisation

Paper, §2.4, eq. (`eq:omdef`):

> "let $\om(\xi)$ be the supremum of the real $w$ for which
>  $|\xi-r|_2\le H(r)^{-(1+w)}$
>  holds for infinitely many $r\in\Q$."

We formalise the *predicate* rather than the supremum, since the skeleton needs only
the predicate form.  `ApproxExp ξ μ` says that `ξ` admits infinitely many **distinct**
rationals with **odd denominator** approximating it to exponent `μ`, i.e. the paper's
`|ξ − r|₂ ≤ H(r)^{−μ}` with `μ = 1 + w`.

NORMALISATION NOTE (see `AXIOMS.md`): the paper's `ω(ξ)` quantifies over rational
approximants in the Koksma sense, in which a *rational* `ξ` has `ω(ξ) = ∞` — the
witnessing family being the integer multiples `k(den·X − num)` of its minimal
polynomial, which are infinitely many *polynomials* but represent only one point of `ℚ`.
`ApproxExp` below quantifies over infinitely many **distinct elements of `ℚ`**, which is
the form Theorem R's hypothesis takes (its approximants are coprime and of strictly
increasing height).  Under that reading `Liouville.irrational_of_approxExp` shows a
rational `ξ` has no such family already for `μ > 1`; the two statements are not in
conflict because they quantify differently.  This is recorded rather than elided. -/
def ApproxExp (p : ℕ) [Fact p.Prime] (ξ : ℚ_[p]) (μ : ℝ) : Prop :=
  ∃ S : Set ℚ, S.Infinite ∧ (∀ r ∈ S, Odd r.den) ∧
    ∀ r ∈ S, ‖ξ - (r : ℚ_[p])‖ ≤ (H r : ℝ) ^ (-μ)

/-! ## The height cost `A(γ)` and the threshold `γ*`

Paper, §1.2 (`\subsection{Main results}`):

> "Put $\Av:=\max(1,\gamma\log_2 3),\qquad
>   \gs:=\frac{1+\varphi}{2\log_2 3}=\frac{3+\sqrt5}{4\log_2 3}
>   =0.8258977696818354644\ldots,$
>  where $\varphi=(1+\sqrt5)/2$"
-/

/-- The golden ratio `φ = (1+√5)/2`, as the paper defines it in §1.2. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

/-- `log₂ 3`, the base-2 logarithm of 3. -/
noncomputable def log2three : ℝ := Real.log 3 / Real.log 2

/-- The height cost `A(γ) = max(1, γ log₂ 3)` of the paper's §1.2. -/
noncomputable def A (γ : ℝ) : ℝ := max 1 (γ * log2three)

/-- The threshold `γ* = (1+φ)/(2 log₂ 3) = (3+√5)/(4 log₂ 3)` of the paper's §1.2. -/
noncomputable def gammaStar : ℝ := (1 + phi) / (2 * log2three)

end Sturmian
