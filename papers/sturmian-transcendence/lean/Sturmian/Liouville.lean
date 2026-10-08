/-
# The 2-adic Liouville inequality  (PROVED HERE — no axiom)

Stage 1, item 3 of the brief.  The paper records the need for an irrationality input
separately from Theorem R; this file shows that for the *skeleton* — in which the
approximants are **distinct elements of `ℚ`** — irrationality is already forced by the
exponent, so no appeal to the paper's Proposition 2.10 is needed here.

Paper, §2.4, immediately after Theorem R:

> "Finally, the irrationality input, which Theorem R cannot supply: a rational $r$ has
>  $\om(r)=\infty$, so $\om>1$ does not by itself exclude rationality."

See the NORMALISATION NOTE in `Sturmian/Basic.lean` for why that sentence and
`not_odd_den_rat_of_approxExp` below are consistent: the paper's `ω` is the Koksma
exponent, whose witnessing family for a rational is the set of integer multiples of its
minimal polynomial — infinitely many *polynomials* representing a single point of `ℚ` —
whereas `ApproxExp` asks for infinitely many *distinct rationals*.
-/
import Sturmian.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Sturmian

/-- For a nonzero integer `n`, the `p`-adic norm is at least `1/|n|`, because
`p ^ v_p(n)` divides `n`. -/
lemma one_div_abs_le_padicNorm_int {p : ℕ} [hp : Fact p.Prime] {n : ℤ} (hn : n ≠ 0) :
    1 / (|n| : ℚ) ≤ padicNorm p n := by
  have hp1 : 1 < p := hp.out.one_lt
  have hcast : ((n : ℚ) ≠ 0) := Int.cast_ne_zero.mpr hn
  have hval : padicNorm p (n : ℚ) = (p : ℚ) ^ (-(padicValRat p (n : ℚ))) :=
    padicNorm.eq_zpow_of_nonzero hcast
  have hint : padicValRat p (n : ℚ) = (padicValInt p n : ℤ) := by
    simp [padicValRat.of_int]
  set v : ℕ := padicValInt p n with hv
  have hdvd : (p : ℤ) ^ v ∣ n := padicValInt_dvd n
  have habs : ((p : ℤ) ^ v) ≤ |n| :=
    Int.le_of_dvd (abs_pos.mpr hn) ((dvd_abs _ _).mpr hdvd)
  have hpos : (0 : ℚ) < (p : ℚ) ^ v := by positivity
  have habsQ : ((p : ℚ) ^ v) ≤ (|n| : ℚ) := by exact_mod_cast habs
  have hnpos : (0 : ℚ) < (|n| : ℚ) := by exact_mod_cast abs_pos.mpr hn
  rw [hval, hint, zpow_neg, zpow_natCast, ← one_div]
  exact one_div_le_one_div_of_le hpos habsQ

/-- `padicNorm 2 m = 1` for an odd integer `m`. -/
lemma padicNorm_two_int_odd {m : ℤ} (hm : ¬ (2 : ℤ) ∣ m) : padicNorm 2 m = 1 :=
  (padicNorm.int_eq_one_iff m).mpr (by simpa using hm)

/-- **The 2-adic Liouville inequality.**  For `ξ ≠ r` rational, both with odd
denominator (equivalently: both in `ℤ₂`),
`|ξ − r|₂ ≥ c_ξ · H(r)⁻¹` with `c_ξ = (|num ξ| + den ξ)⁻¹`.

This is the `p`-adic Liouville inequality the paper refers to in §6 ("what Theorem R and
the $p$-adic Liouville inequality use"); it is proved here rather than assumed. -/
theorem liouville_two_adic {ξ r : ℚ} (hξ : Odd ξ.den) (hr : Odd r.den) (hne : ξ ≠ r) :
    1 / ((|ξ.num| + (ξ.den : ℤ) : ℚ) * (H r : ℚ)) ≤ padicNorm 2 (ξ - r) := by
  -- the integer numerator of the difference, cleared of denominators
  set n : ℤ := ξ.num * (r.den : ℤ) - (ξ.den : ℤ) * r.num with hn
  have hdξ : (ξ.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ξ.den_nz
  have hdr : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz
  have hξe : (ξ.num : ℚ) = ξ * (ξ.den : ℚ) := (div_eq_iff hdξ).mp (Rat.num_div_den ξ)
  have hre : (r.num : ℚ) = r * (r.den : ℚ) := (div_eq_iff hdr).mp (Rat.num_div_den r)
  have hkey : (ξ - r) * ((ξ.den : ℚ) * (r.den : ℚ)) = (n : ℚ) := by
    rw [hn]; push_cast
    linear_combination (-(r.den : ℚ)) * hξe + (ξ.den : ℚ) * hre
  have hnne : n ≠ 0 := by
    intro h0
    have : (ξ - r) * ((ξ.den : ℚ) * (r.den : ℚ)) = 0 := by rw [hkey, h0]; simp
    rcases mul_eq_zero.mp this with h | h
    · exact hne (sub_eq_zero.mp h)
    · exact (mul_ne_zero hdξ hdr) h
  -- the denominator product is odd, so it is a 2-adic unit
  have hdodd : Odd (ξ.den * r.den) := Nat.odd_mul.mpr ⟨hξ, hr⟩
  have hnat : ¬ (2 : ℕ) ∣ (ξ.den * r.den) := by
    obtain ⟨k, hk⟩ := hdodd; omega
  have hodd : ¬ (2 : ℤ) ∣ ((ξ.den : ℤ) * (r.den : ℤ)) := by
    have hcast : ((ξ.den : ℤ) * (r.den : ℤ)) = ((ξ.den * r.den : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, Int.natCast_dvd_natCast]
    exact hnat
  have hunit : padicNorm 2 (((ξ.den : ℤ) * (r.den : ℤ) : ℤ)) = 1 := padicNorm_two_int_odd hodd
  -- transport the integer bound
  have hmulnorm : padicNorm 2 (ξ - r) = padicNorm 2 (n : ℚ) := by
    have : padicNorm 2 ((ξ - r) * ((ξ.den : ℚ) * (r.den : ℚ)))
        = padicNorm 2 (ξ - r) * padicNorm 2 ((ξ.den : ℚ) * (r.den : ℚ)) := padicNorm.mul _ _
    rw [hkey] at this
    have hc : padicNorm 2 ((ξ.den : ℚ) * (r.den : ℚ)) = 1 := by
      have : (((ξ.den : ℤ) * (r.den : ℤ) : ℤ) : ℚ) = (ξ.den : ℚ) * (r.den : ℚ) := by push_cast; ring
      rw [← this]; exact hunit
    rw [hc, mul_one] at this
    exact this.symm
  have hge : 1 / (|n| : ℚ) ≤ padicNorm 2 (n : ℚ) := one_div_abs_le_padicNorm_int hnne
  -- and bound |n| by (|num ξ| + den ξ) · H(r)
  have hbound : (|n| : ℚ) ≤ ((|ξ.num| + (ξ.den : ℤ) : ℚ)) * (H r : ℚ) := by
    have h1 : |n| ≤ |ξ.num| * (r.den : ℤ) + (ξ.den : ℤ) * |r.num| := by
      calc |n| = |ξ.num * (r.den : ℤ) - (ξ.den : ℤ) * r.num| := by rw [hn]
        _ ≤ |ξ.num * (r.den : ℤ)| + |(ξ.den : ℤ) * r.num| := by
              simpa [sub_eq_add_neg, abs_neg] using
                abs_add_le (ξ.num * (r.den : ℤ)) (-((ξ.den : ℤ) * r.num))
        _ = |ξ.num| * (r.den : ℤ) + (ξ.den : ℤ) * |r.num| := by
              rw [abs_mul, abs_mul, Int.abs_natCast, Int.abs_natCast]
    have hrd : (r.den : ℤ) ≤ (H r : ℤ) := by exact_mod_cast H_den_le r
    have hrn : |r.num| ≤ (H r : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast H_num_le r
    have h2 : |ξ.num| * (r.den : ℤ) + (ξ.den : ℤ) * |r.num|
        ≤ (|ξ.num| + (ξ.den : ℤ)) * (H r : ℤ) := by
      have hx : (0 : ℤ) ≤ |ξ.num| := abs_nonneg _
      have hd : (0 : ℤ) ≤ (ξ.den : ℤ) := Int.natCast_nonneg _
      calc |ξ.num| * (r.den : ℤ) + (ξ.den : ℤ) * |r.num|
          ≤ |ξ.num| * (H r : ℤ) + (ξ.den : ℤ) * (H r : ℤ) := by
            exact add_le_add (mul_le_mul_of_nonneg_left hrd hx)
                             (mul_le_mul_of_nonneg_left hrn hd)
        _ = (|ξ.num| + (ξ.den : ℤ)) * (H r : ℤ) := by ring
    have := le_trans h1 h2
    exact_mod_cast this
  have hCpos : (0 : ℚ) < ((|ξ.num| + (ξ.den : ℤ) : ℚ)) * (H r : ℚ) := by
    have : (0 : ℚ) < (H r : ℚ) := by exact_mod_cast H_pos r
    have h2 : (0 : ℚ) < ((|ξ.num| + (ξ.den : ℤ) : ℚ)) := by
      have : (0 : ℤ) < |ξ.num| + (ξ.den : ℤ) := by
        have := abs_nonneg ξ.num
        have hd : (0 : ℤ) < (ξ.den : ℤ) := by exact_mod_cast ξ.pos
        linarith
      exact_mod_cast this
    positivity
  refine le_trans ?_ (le_trans hge (le_of_eq hmulnorm.symm))
  exact one_div_le_one_div_of_le (by exact_mod_cast abs_pos.mpr hnne) hbound

/-- The Liouville inequality in the form the skeleton uses: real-valued, and stated for
the `ℚ_[2]`-norm via the bridge `Padic.eq_padicNorm`. -/
theorem liouville_two_adic_real {ξ r : ℚ} (hξ : Odd ξ.den) (hr : Odd r.den) (hne : ξ ≠ r) :
    1 / (((|ξ.num| : ℝ) + (ξ.den : ℝ)) * (H r : ℝ))
      ≤ ‖((ξ : ℚ) : ℚ_[2]) - (r : ℚ_[2])‖ := by
  have hbridge : ‖((ξ : ℚ) : ℚ_[2]) - (r : ℚ_[2])‖ = ((padicNorm 2 (ξ - r) : ℚ) : ℝ) := by
    rw [show ((ξ : ℚ) : ℚ_[2]) - (r : ℚ_[2]) = (((ξ - r : ℚ)) : ℚ_[2]) by push_cast; ring]
    exact Padic.eq_padicNorm _
  rw [hbridge]
  have hQ := liouville_two_adic hξ hr hne
  have : ((1 / ((|ξ.num| + (ξ.den : ℤ) : ℚ) * (H r : ℚ)) : ℚ) : ℝ)
      ≤ ((padicNorm 2 (ξ - r) : ℚ) : ℝ) := by exact_mod_cast hQ
  refine le_trans (le_of_eq ?_) this
  push_cast
  ring

end Sturmian
