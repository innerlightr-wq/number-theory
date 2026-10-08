/-
# Stage 4 — the initial critical exponent, and the extraction of Steps 1–2

Paper, Definition 2.5 (`\cite[\S2]{BHZ06}`), verbatim:

> "The *prefix power* of a finite word $W$ in a sequence $\omega$ is the largest real $p$
>  such that $W^{p}$ is a prefix of $\omega$; equivalently $\lcp(\omega,W^{\infty})/|W|$.
>  The *initial critical exponent* $\ice(\omega)$ is the limit superior of the prefix powers
>  of the words $\omega[0,n)$ in $\omega$."

and the remark immediately after it:

> "Because the prefix power is defined as the largest *real* such $p$, we have
>  $\lcp(\omega,W^{\infty})=p\,|W|$ *exactly*: no floor and no $O(1)$ is lost in passing
>  between $\ice$ and approximation depth."

`prefixPower` and `ice` below are that definition.  Values lie in `ℝ≥0∞` because the prefix
power is `∞` exactly when `ω` is `n`-periodic, and `ice` is `∞` exactly when the partial
quotients of the slope are unbounded (the paper's Case L).

`exists_prefix_power_of_lt_ice` is the paper's **Steps 1–2**, proved: from `ice(c_γ) > e` it
produces, arbitrarily far out, lengths whose prefix repeats to power at least `e`.

**No primitive-root replacement is needed.**  The paper replaces each prefix by its
primitive root so that Berthé–Holton–Zamboni's Proposition 3.2 applies, giving a conjugate
of a standard word, giving balance, giving the height bound; and so that minimal periods
are distinct, giving Step 4's distinctness.  Neither is needed here: balance for prefixes
of `c_γ` is proved directly (`Sturmian.abs_balance_prefix`), and the distinctness was
eliminated at stage 3 in favour of the finite-fibre argument.  So the extraction can take
the prefix itself.
-/
import Sturmian.Word
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace Sturmian

open Filter ENNReal

open Classical in
/-- The prefix power of `ω[0,n)` in `ω`: `lcp(ω, (ω[0,n))^∞)/n`, with the value `∞` in the
degenerate case `ω = (ω[0,n))^∞`. -/
noncomputable def prefixPower (ω : Word) (n : ℕ) : ℝ≥0∞ :=
  if h : ω = per n ω then ⊤ else ((lcp ω (per n ω) h : ℕ) : ℝ≥0∞) / ((n : ℕ) : ℝ≥0∞)

/-- The paper's Definition 2.5: the **initial critical exponent**, the limit superior of the
prefix powers of the prefixes `ω[0,n)`. -/
noncomputable def ice (ω : Word) : ℝ≥0∞ := limsup (prefixPower ω) atTop

/-- A prefix power exceeding `e` means the first `⌈en⌉` letters of `ω` agree with the
periodisation of its length-`n` prefix.  This is the paper's "no floor and no `O(1)` is
lost". -/
lemma agree_of_lt_prefixPower {ω : Word} {n : ℕ} (hn : 0 < n) {e : ℝ} (he : 0 ≤ e)
    (h : ENNReal.ofReal e < prefixPower ω n) :
    ∀ m : ℕ, (m : ℝ) < e * (n : ℝ) → ω m = per n ω m := by
  intro m hm
  by_cases hp : ω = per n ω
  · exact congrFun hp m
  · have h : ENNReal.ofReal e
        < ((lcp ω (per n ω) hp : ℕ) : ℝ≥0∞) / ((n : ℕ) : ℝ≥0∞) := by
      simpa [prefixPower, hp] using h
    set L : ℕ := lcp ω (per n ω) hp with hLdef
    have hnne : ((n : ℕ) : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]; omega
    have hntop : ((n : ℕ) : ℝ≥0∞) ≠ ⊤ := by simp
    have hmul : ENNReal.ofReal e * ((n : ℕ) : ℝ≥0∞) < ((L : ℕ) : ℝ≥0∞) :=
      (ENNReal.lt_div_iff_mul_lt (Or.inl hnne) (Or.inl hntop)).mp h
    have hcast : ENNReal.ofReal e * ((n : ℕ) : ℝ≥0∞) = ENNReal.ofReal (e * (n : ℝ)) := by
      rw [ENNReal.ofReal_mul he, ENNReal.ofReal_natCast]
    have hLcast : ((L : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((L : ℝ)) := by
      rw [ENNReal.ofReal_natCast]
    rw [hcast, hLcast, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)] at hmul
    have hmL : m < L := by
      have : (m : ℝ) < (L : ℝ) := lt_trans hm hmul
      exact_mod_cast this
    exact eq_of_lt_lcp ω (per n ω) hp hmL

/-- **Steps 1–2 of the paper, proved.**  From `ice(ω) > e`, arbitrarily far out there are
lengths `n` whose length-`n` prefix repeats in `ω` to power at least `e`. -/
theorem exists_prefix_power_of_lt_ice {ω : Word} {e : ℝ} (he : 0 ≤ e)
    (hlt : ENNReal.ofReal e < ice ω) (N : ℕ) :
    ∃ n, N ≤ n ∧ 0 < n ∧ ∀ m : ℕ, (m : ℝ) < e * (n : ℝ) → ω m = per n ω m := by
  have hfreq : ∃ᶠ n in atTop, ENNReal.ofReal e < prefixPower ω n :=
    frequently_lt_of_lt_limsup (by isBoundedDefault) hlt
  obtain ⟨n, hn, hprop⟩ := frequently_atTop.mp hfreq (max N 1)
  refine ⟨n, le_trans (le_max_left N 1) hn, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_trans (le_max_right N 1) hn)
  · exact agree_of_lt_prefixPower (lt_of_lt_of_le zero_lt_one (le_trans (le_max_right N 1) hn))
      he hprop

end Sturmian
