/-
# The 2-adic core: the Bernstein–Lagarias recursion, the isometry, and eq. (3)

## What `IsBL` is, and why it is exactly the paper's eq. (2)

Paper, §1.1:

> "Identifying a word $v=v_0v_1v_2\cdots\in\{0,1\}^{\N}$ with the $2$-adic integer
>  $\sum_k v_k2^k$, the inverse $\PH^{-1}(x)=\sum_{k\ge0}(T^k(x)\bmod 2)2^k$ is the
>  *parity vector* of $x$, so $\PH(v)$ is the unique $x\in\Zt$ whose parity vector is $v$,
>  and (1) reads
>  $$\PH(\sigma v)=T(\PH(v)),\tag{2}$$
>  $\sigma$ being the shift on words."

with, from §1.1,
`T(x) = (3x+1)/2` for `x` odd and `T(x) = x/2` for `x` even, and, from §2.1,

> "We also use, from \cite[\S1]{BL96}, that $\PH(v)$ is odd if and only if $v_0=1$".

Unpacking eq. (2) on `v = cons b c` (so `σv = c`) with that parity fact gives exactly the
two equations of `IsBL`:

* `b = 0`: `Φ(v)` even, `T(Φ v) = Φ(v)/2 = Φ(c)`, i.e. `Φ(0c) = 2Φ(c)`;
* `b = 1`: `Φ(v)` odd, `T(Φ v) = (3Φ(v)+1)/2 = Φ(c)`, i.e. `3Φ(1c) = 2Φ(c) − 1`.

**These two equations are literally the paper's eq. (12)** (`2Φ(c) = 3Φ(1c)+1 = Φ(0c)`),
which the paper obtains as the `m = 1` case of eq. (3).  So `Sturmian.IsBL.transfer`
below is a restatement, recorded as such and not claimed as new work.

Nothing else about `Φ` is assumed in this file.  In particular the parity fact is *derived*
from `IsBL` (`IsBL.norm_cons_true`), not assumed twice.
-/
import Sturmian.Word
import Mathlib.NumberTheory.Padics.PadicIntegers

namespace Sturmian

open PadicInt

/-! ## Two norm facts in `ℤ_[2]` -/

lemma norm_sub_le_max (a b : ℤ_[2]) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  have h := PadicInt.nonarchimedean a (-b)
  simpa [sub_eq_add_neg] using h

/-- Ultrametric: a strictly smaller perturbation does not change the norm. -/
lemma norm_sub_eq_of_norm_lt {a b : ℤ_[2]} (hab : ‖a‖ < ‖b‖) : ‖a - b‖ = ‖b‖ := by
  refine le_antisymm ?_ ?_
  · have h := norm_sub_le_max a b
    rwa [max_eq_right (le_of_lt hab)] at h
  · have h : ‖b‖ ≤ max ‖a‖ ‖a - b‖ := by
      have := norm_sub_le_max a (a - b)
      simpa using this
    rcases max_cases ‖a‖ ‖a - b‖ with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he] at h; exact absurd (lt_of_lt_of_le hab h) (lt_irrefl _)
    · rwa [he] at h

lemma norm_two : ‖(2 : ℤ_[2])‖ = 1 / 2 := by
  have h : ((2 : ℕ) : ℤ_[2]) = (2 : ℤ_[2]) := by norm_cast
  have := PadicInt.norm_p (p := 2)
  rw [h] at this
  rw [this]; norm_num

lemma norm_three : ‖(3 : ℤ_[2])‖ = 1 := by
  have hdvd : ¬ ((2 : ℤ) ∣ (3 : ℤ)) := by decide
  have hiff := PadicInt.norm_int_lt_one_iff_dvd (p := 2) 3
  have hle : ‖((3 : ℤ) : ℤ_[2])‖ ≤ 1 := PadicInt.norm_le_one _
  have hnlt : ¬ (‖((3 : ℤ) : ℤ_[2])‖ < 1) := fun hh => hdvd (hiff.mp hh)
  have : ‖((3 : ℤ) : ℤ_[2])‖ = 1 := le_antisymm hle (not_lt.mp hnlt)
  simpa using this

/-! ## The interface -/

/-- `IsBL Φ` says that `Φ : Word → ℤ_[2]` satisfies the Bernstein–Lagarias recursion, i.e.
the paper's eq. (2) unpacked by the first letter — equivalently the paper's eq. (12). -/
structure IsBL (Φ : Word → ℤ_[2]) : Prop where
  /-- `Φ(0c) = 2Φ(c)`: eq. (2) at an even value. -/
  cons_false : ∀ c, Φ (cons false c) = 2 * Φ c
  /-- `3Φ(1c) = 2Φ(c) − 1`: eq. (2) at an odd value. -/
  cons_true : ∀ c, 3 * Φ (cons true c) = 2 * Φ c - 1

namespace IsBL

variable {Φ : Word → ℤ_[2]}

/-! ### Item 4 of the stage-2 brief — the transfer identity, eq. (12) -/

/-- **The paper's eq. (12)**, for every infinite word `c`:
`2Φ(c) = 3Φ(1c) + 1 = Φ(0c)`, equivalently `Φ(1c) = (2Φ(c) − 1)/3`.
This is a restatement of `IsBL` and is recorded as such. -/
theorem transfer (h : IsBL Φ) (c : Word) :
    2 * Φ c = 3 * Φ (cons true c) + 1 ∧ 2 * Φ c = Φ (cons false c) := by
  refine ⟨?_, (h.cons_false c).symm⟩
  linear_combination -(h.cons_true c)

/-! ### Parity, as a norm statement

Paper, §2.1: "$\PH(v)$ is odd if and only if $v_0=1$" (from `\cite[\S1]{BL96}`).  Here it
is *derived* from `IsBL`, in the equivalent norm form. -/

lemma norm_cons_false_le (h : IsBL Φ) (c : Word) : ‖Φ (cons false c)‖ ≤ 1 / 2 := by
  rw [h.cons_false c, norm_mul, norm_two]
  nlinarith [PadicInt.norm_le_one (Φ c), norm_nonneg (Φ c)]

lemma norm_cons_true (h : IsBL Φ) (c : Word) : ‖Φ (cons true c)‖ = 1 := by
  have h3 : ‖(3 : ℤ_[2]) * Φ (cons true c)‖ = ‖Φ (cons true c)‖ := by
    rw [norm_mul, norm_three, one_mul]
  have hlt : ‖(2 : ℤ_[2]) * Φ c‖ < ‖(1 : ℤ_[2])‖ := by
    rw [norm_one, norm_mul, norm_two]
    nlinarith [PadicInt.norm_le_one (Φ c), norm_nonneg (Φ c)]
  have hrhs : ‖2 * Φ c - 1‖ = 1 := by
    rw [norm_sub_eq_of_norm_lt hlt, norm_one]
  rw [← h3, h.cons_true c, hrhs]

/-! ### Item 2 of the stage-2 brief — the Bernstein–Lagarias isometry (Prop 2.1)

Paper, Proposition 2.1 (`\cite{BL96}`; also `\cite[eq.~(4), \S1]{LS21}`):

> "For all $v,w\in\{0,1\}^{\N}$,
>  $\vtwo(\PH(v)-\PH(w))=\lcp(v,w)$, equivalently $|\PH(x)-\PH(y)|_2=|x-y|_2$.
>  In particular $\PH$ is injective: distinct words have finite $\lcp$, hence distinct
>  values."

The paper **cites** it.  Per the brief it is **proved here anyway**, from `IsBL` alone, by
induction on the `lcp`.  It is stated in the equivalent `|·|₂` form the paper gives, which
avoids fixing a valuation convention. -/

private lemma isometry_aux (h : IsBL Φ) :
    ∀ n (v w : Word) (hne : v ≠ w), lcp v w hne = n →
      ‖Φ v - Φ w‖ = (2 : ℝ) ^ (-(n : ℤ)) := by
  intro n
  induction n with
  | zero =>
    intro v w hne hl
    have h0 : v 0 ≠ w 0 := by have hs := lcp_spec v w hne; rwa [hl] at hs
    have hv : v = cons (v 0) (shift v) := (cons_shift v).symm
    have hw : w = cons (w 0) (shift w) := (cons_shift w).symm
    have hgoal : ‖Φ v - Φ w‖ = 1 := by
      by_cases hv0 : v 0 = true
      · have hw0 : w 0 = false := by
          by_cases hh : w 0 = true
          · exact absurd (hv0.trans hh.symm) h0
          · simpa using hh
        have h1 : ‖Φ w‖ ≤ 1 / 2 := by rw [hw, hw0]; exact h.norm_cons_false_le _
        have h2 : ‖Φ v‖ = 1 := by rw [hv, hv0]; exact h.norm_cons_true _
        have hwv : ‖Φ w - Φ v‖ = 1 := by
          rw [norm_sub_eq_of_norm_lt (show ‖Φ w‖ < ‖Φ v‖ by rw [h2]; linarith), h2]
        rw [← norm_neg]; simpa using hwv
      · have hv0' : v 0 = false := by simpa using hv0
        have hw0 : w 0 = true := by
          by_cases hh : w 0 = true
          · exact hh
          · have hhf : w 0 = false := by simpa using hh
            exact absurd (hv0'.trans hhf.symm) h0
        have h1 : ‖Φ v‖ ≤ 1 / 2 := by rw [hv, hv0']; exact h.norm_cons_false_le _
        have h2 : ‖Φ w‖ = 1 := by rw [hw, hw0]; exact h.norm_cons_true _
        rw [norm_sub_eq_of_norm_lt (show ‖Φ v‖ < ‖Φ w‖ by rw [h2]; linarith), h2]
    rw [hgoal]; norm_num
  | succ n ih =>
    intro v w hne hl
    have h0 : v 0 = w 0 := eq_of_lt_lcp v w hne (by omega)
    have hs : shift v ≠ shift w := fun hss => hne (eq_of_shift_eq h0 hss)
    have hln : lcp (shift v) (shift w) hs = n := by
      have hsh := lcp_shift hne h0 hs; omega
    have ihn := ih (shift v) (shift w) hs hln
    have hv : v = cons (v 0) (shift v) := (cons_shift v).symm
    have hw : w = cons (w 0) (shift w) := (cons_shift w).symm
    have hstep : ‖Φ v - Φ w‖ = (1 / 2) * ‖Φ (shift v) - Φ (shift w)‖ := by
      by_cases hv0 : v 0 = true
      · have hw0 : w 0 = true := by rw [← h0]; exact hv0
        have e1 : 3 * Φ v = 2 * Φ (shift v) - 1 := by rw [hv, hv0]; exact h.cons_true _
        have e2 : 3 * Φ w = 2 * Φ (shift w) - 1 := by rw [hw, hw0]; exact h.cons_true _
        have key : (3 : ℤ_[2]) * (Φ v - Φ w) = 2 * (Φ (shift v) - Φ (shift w)) := by
          linear_combination e1 - e2
        have hl3 : ‖(3 : ℤ_[2]) * (Φ v - Φ w)‖ = ‖Φ v - Φ w‖ := by
          rw [norm_mul, norm_three, one_mul]
        rw [← hl3, key, norm_mul, norm_two]
      · have hv0' : v 0 = false := by simpa using hv0
        have hw0 : w 0 = false := by rw [← h0]; exact hv0'
        have e1 : Φ v = 2 * Φ (shift v) := by rw [hv, hv0']; exact h.cons_false _
        have e2 : Φ w = 2 * Φ (shift w) := by rw [hw, hw0]; exact h.cons_false _
        have key : Φ v - Φ w = 2 * (Φ (shift v) - Φ (shift w)) := by
          linear_combination e1 - e2
        rw [key, norm_mul, norm_two]
    rw [hstep, ihn]
    have hexp : (-((n + 1 : ℕ) : ℤ)) = -(n : ℤ) + (-1 : ℤ) := by push_cast; ring
    rw [hexp, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
    ring

/-- **Proposition 2.1 (Bernstein–Lagarias isometry), proved from `IsBL`.**
`|Φ(v) − Φ(w)|₂ = 2^(−lcp(v,w))`, the paper's equivalent form of
`v₂(Φ(v) − Φ(w)) = lcp(v,w)`. -/
theorem isometry (h : IsBL Φ) (v w : Word) (hne : v ≠ w) :
    ‖Φ v - Φ w‖ = (2 : ℝ) ^ (-(lcp v w hne : ℤ)) :=
  isometry_aux h _ v w hne rfl

/-- "In particular `Φ` is injective: distinct words have finite `lcp`, hence distinct
values." (Paper, Prop. 2.1.) -/
theorem injective (h : IsBL Φ) : Function.Injective Φ := by
  intro v w hvw
  by_contra hne
  have hiso := h.isometry v w hne
  rw [hvw, sub_self, norm_zero] at hiso
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(lcp v w hne : ℤ)) := by positivity
  linarith

/-! ### The paper's eq. (3)

Paper, §2.1:

> "iterating the latter and writing $c_m(v):=\sum_{i<m,\,v_i=1}3^{\,k_m(v)-k_{i+1}(v)}2^{i}
>  \in\Z$ gives
>  $$2^{m}\,\PH(\sigma^{m}v)=3^{\,k_m(v)}\,\PH(v)+c_m(v)\qquad(m\ge0),\tag{3}$$
>  a relation with rational coefficients." -/

lemma shiftIter_eq_cons (m : ℕ) (v : Word) :
    shiftIter m v = cons (v m) (shiftIter (m + 1) v) := by
  funext k
  cases k with
  | zero => simp [shiftIter]
  | succ j => simp only [shiftIter_apply, cons_succ]; congr 1; omega

/-- **The paper's eq. (3)**, proved from `IsBL` by induction on `m`. -/
theorem affinegen (h : IsBL Φ) (v : Word) : ∀ m : ℕ,
    (2 : ℤ_[2]) ^ m * Φ (shiftIter m v)
      = (3 : ℤ_[2]) ^ (ones m v) * Φ v + ((cw m v : ℤ) : ℤ_[2]) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have hc : shiftIter m v = cons (v m) (shiftIter (m + 1) v) := shiftIter_eq_cons m v
    by_cases hvm : v m = true
    · have estep : 3 * Φ (shiftIter m v) = 2 * Φ (shiftIter (m + 1) v) - 1 := by
        rw [hc, hvm]; exact h.cons_true _
      have hk : ones (m + 1) v = ones m v + 1 := by rw [ones_succ]; simp [hvm]
      have hcw : cw (m + 1) v = 3 * cw m v + 2 ^ m := by rw [cw_succ]; simp [hvm]
      rw [hk, hcw]
      push_cast
      rw [pow_succ, pow_succ]
      linear_combination (-((2 : ℤ_[2]) ^ m)) * estep + 3 * ih
    · have hvm' : v m = false := by simpa using hvm
      have estep : Φ (shiftIter m v) = 2 * Φ (shiftIter (m + 1) v) := by
        rw [hc, hvm']; exact h.cons_false _
      have hk : ones (m + 1) v = ones m v := by rw [ones_succ]; simp [hvm']
      have hcw : cw (m + 1) v = cw m v := by rw [cw_succ]; simp [hvm']
      rw [hk, hcw, pow_succ]
      linear_combination (-((2 : ℤ_[2]) ^ m)) * estep + ih

end IsBL

end Sturmian
