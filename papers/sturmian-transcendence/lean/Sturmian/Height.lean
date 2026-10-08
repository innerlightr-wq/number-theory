/-
# Stage 3, part 1 — the Sturmian balance facts, and the height bound (Prop. 2.4)

Paper, §2.2:

> "For irrational $\gamma\in(0,1)$ the characteristic word is
>  $c_\gamma(j)=\lfloor(j+1)\gamma\rfloor-\lfloor j\gamma\rfloor$ for $j\ge1$ …
>  Every Sturmian word is balanced, so any factor of length $\ell$ has $k$ ones with
>  $|k-\gamma\ell|<1$."

For a **prefix** of `c_γ` — the only case Proposition 2.4 is applied in — the balance bound
is not an external input: the letters of `c_γ` telescope, so the number of ones in the first
`ℓ` letters is exactly `⌊(ℓ+1)γ⌋`, whence `|k − γℓ| < 1`.  Both are proved below.

Paper, Proposition 2.4, with its four-line proof:

> "With $\delta=2^{\ell}-3^{k}$ and $g=\gcd(c_W,|\delta|)$ we have
>  $H=\max(c_W,|\delta|)/g\le\max(c_W,|\delta|)$. Since $2^{\ell}$ and $3^{k}$ are distinct
>  positive integers, $|\delta|<\max(2^{\ell},3^{k})$; and $c_W\le3\ell\max(2^{\ell},3^{k})$
>  by \cite[Lemma 10.4]{DJirr} … Hence
>  $\log_2 H\le\log_2(3\ell)+\max(\ell,k\log_2 3)$. Balance of the ambient Sturmian word
>  gives $|k-\gamma\ell|<1$, so $k\log_2 3<\gamma\ell\log_2 3+\log_2 3$ and therefore
>  $\max(\ell,k\log_2 3)<\Av\ell+\log_2 3$."

Every step of that is proved here; the remaining input `c_W ≤ 3ℓ max(2^ℓ,3^k)` is itself
proved in `Sturmian/Numerator.lean`, where Proposition 2.4 is then assembled.
-/
import Sturmian.Shadow
import Sturmian.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Ring

namespace Sturmian

/-! ## The letters of `c_γ` telescope -/

/-- The increment whose value is the `n`-th letter of `charWord γ`. -/
noncomputable def inc (γ : ℝ) (n : ℕ) : ℤ := ⌊((n : ℝ) + 2) * γ⌋ - ⌊((n : ℝ) + 1) * γ⌋

lemma charWord_true_iff (γ : ℝ) (n : ℕ) : charWord γ n = true ↔ inc γ n = 1 := by
  simp [charWord, inc]

lemma inc_nonneg {γ : ℝ} (hγ0 : 0 < γ) (n : ℕ) : 0 ≤ inc γ n := by
  have hle : ((n : ℝ) + 1) * γ ≤ ((n : ℝ) + 2) * γ := by nlinarith
  have := Int.floor_mono hle
  simp only [inc]; omega

lemma inc_le_one {γ : ℝ} (hγ1 : γ < 1) (n : ℕ) : inc γ n ≤ 1 := by
  have h1 : ((n : ℝ) + 1) * γ < (⌊((n : ℝ) + 1) * γ⌋ : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have h2 : ((n : ℝ) + 2) * γ < ((n : ℝ) + 1) * γ + 1 := by nlinarith
  have h3 : ((n : ℝ) + 2) * γ < ((⌊((n : ℝ) + 1) * γ⌋ + 2 : ℤ) : ℝ) := by push_cast; linarith
  have h4 : ⌊((n : ℝ) + 2) * γ⌋ < ⌊((n : ℝ) + 1) * γ⌋ + 2 := Int.floor_lt.mpr h3
  simp only [inc]; omega

lemma indicator_eq_inc {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (n : ℕ) :
    (if charWord γ n then (1 : ℤ) else 0) = inc γ n := by
  by_cases hc : charWord γ n = true
  · rw [if_pos hc, (charWord_true_iff γ n).mp hc]
  · have hc' : charWord γ n = false := by simpa using hc
    have hne : inc γ n ≠ 1 := fun hh => hc ((charWord_true_iff γ n).mpr hh)
    have h0 := inc_nonneg hγ0 n
    have h1 := inc_le_one hγ1 n
    have : inc γ n = 0 := by omega
    rw [hc']
    simp [this]

/-- **The number of ones in the first `ℓ` letters of `c_γ` is exactly `⌊(ℓ+1)γ⌋`.**
A telescoping sum; no external input. -/
lemma ones_charWord {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∀ ℓ : ℕ, ((ones ℓ (charWord γ) : ℤ)) = ⌊((ℓ : ℝ) + 1) * γ⌋ := by
  intro ℓ
  induction ℓ with
  | zero =>
    have hf : ⌊γ⌋ = 0 := by
      rw [Int.floor_eq_zero_iff]
      exact ⟨le_of_lt hγ0, hγ1⟩
    simp [hf]
  | succ m ih =>
    rw [ones_succ]
    push_cast
    rw [ih, indicator_eq_inc hγ0 hγ1 m, inc]
    have hr : ((m : ℝ) + 1 + 1) = ((m : ℝ) + 2) := by ring
    rw [hr]
    ring

/-- **Balance for a prefix**: `|k − γℓ| < 1`, the paper's §2.2 bound, proved for prefixes. -/
lemma abs_ones_charWord_sub_lt_one {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (ℓ : ℕ) :
    |((ones ℓ (charWord γ) : ℝ)) - (ℓ : ℝ) * γ| < 1 := by
  have hk : ((ones ℓ (charWord γ) : ℤ)) = ⌊((ℓ : ℝ) + 1) * γ⌋ := ones_charWord hγ0 hγ1 ℓ
  have hkR : ((ones ℓ (charWord γ) : ℝ)) = ((⌊((ℓ : ℝ) + 1) * γ⌋ : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hk
  rw [hkR, abs_lt]
  have hle : ((⌊((ℓ : ℝ) + 1) * γ⌋ : ℤ) : ℝ) ≤ ((ℓ : ℝ) + 1) * γ := Int.floor_le _
  have hgt : ((ℓ : ℝ) + 1) * γ < ((⌊((ℓ : ℝ) + 1) * γ⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  constructor <;> nlinarith

/-- **Sharp prefix balance.**  For `1 ≤ m ≤ ℓ`,
`|ℓ·k_m(c_γ) − m·k_ℓ(c_γ)| < ℓ`, i.e. `|k_m − m·k_ℓ/ℓ| < 1`.

This is the form of balance that `[DJirr, Lemma 10.4]` uses.  The source obtains it from
"`W` is a cyclic permutation of a standard word" via its Theorem 10.3; for a **prefix** of
`c_γ` it follows directly from the telescoping count and two floor estimates, with no
appeal to standard words.  Both directions are strict. -/
lemma abs_balance_prefix {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {m ℓ : ℕ}
    (hm1 : 1 ≤ m) (hmℓ : m ≤ ℓ) :
    |((ℓ : ℤ)) * ((ones m (charWord γ) : ℤ)) - ((m : ℤ)) * ((ones ℓ (charWord γ) : ℤ))|
      < ((ℓ : ℤ)) := by
  have hℓ1 : 1 ≤ ℓ := le_trans hm1 hmℓ
  set A : ℤ := ⌊((m : ℝ) + 1) * γ⌋ with hAdef
  set B : ℤ := ⌊((ℓ : ℝ) + 1) * γ⌋ with hBdef
  have hA : ((ones m (charWord γ) : ℤ)) = A := ones_charWord hγ0 hγ1 m
  have hB : ((ones ℓ (charWord γ) : ℤ)) = B := ones_charWord hγ0 hγ1 ℓ
  rw [hA, hB]
  -- the four floor estimates
  have hAle : ((A : ℝ)) ≤ ((m : ℝ) + 1) * γ := Int.floor_le _
  have hAgt : ((m : ℝ) + 1) * γ < ((A : ℝ)) + 1 := Int.lt_floor_add_one _
  have hBle : ((B : ℝ)) ≤ ((ℓ : ℝ) + 1) * γ := Int.floor_le _
  have hBgt : ((ℓ : ℝ) + 1) * γ < ((B : ℝ)) + 1 := Int.lt_floor_add_one _
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmℓR : ((m : ℝ)) ≤ ((ℓ : ℝ)) := by exact_mod_cast hmℓ
  have hℓR : (1 : ℝ) ≤ ((ℓ : ℝ)) := by exact_mod_cast hℓ1
  -- the real inequality, then transfer back to ℤ
  have hreal : |((ℓ : ℝ)) * ((A : ℝ)) - ((m : ℝ)) * ((B : ℝ))| < ((ℓ : ℝ)) := by
    rw [abs_lt]
    constructor
    · -- lower: ℓA − mB > γ(ℓ−m) − ℓ ≥ −ℓ
      nlinarith [mul_pos (lt_of_lt_of_le zero_lt_one hℓR) (sub_pos.mpr hγ1),
        mul_nonneg (sub_nonneg.mpr hmℓR) (le_of_lt hγ0)]
    · -- upper: ℓA − mB < γ(ℓ−m) + m ≤ ℓ
      nlinarith [mul_nonneg (sub_nonneg.mpr hmℓR) (le_of_lt hγ0),
        mul_nonneg (sub_nonneg.mpr hmℓR) (sub_nonneg.mpr (le_of_lt hγ1))]
  exact_mod_cast hreal

/-! ## The height bound -/

/-- `H(c/d) ≤ max(c, |d|)`: reduction to lowest terms only shrinks numerator and
denominator.  The paper's "`H = max(c_W,|δ|)/g ≤ max(c_W,|δ|)`". -/
lemma H_div_le {c d : ℤ} (hc : 0 < c) (hd : d ≠ 0) :
    ((H ((c : ℚ) / (d : ℚ)) : ℤ)) ≤ max c |d| := by
  set r : ℚ := (c : ℚ) / (d : ℚ) with hrdef
  have hnum : r.num ∣ c := by rw [hrdef, ← Rat.divInt_eq_div]; exact Rat.num_dvd c hd
  have hden : ((r.den : ℤ)) ∣ d := by rw [hrdef, ← Rat.divInt_eq_div]; exact Rat.den_dvd c d
  have h1 : |r.num| ≤ c := Int.le_of_dvd hc ((abs_dvd _ _).mpr hnum)
  have h2 : ((r.den : ℤ)) ≤ |d| := Int.le_of_dvd (abs_pos.mpr hd) ((dvd_abs _ _).mpr hden)
  have hH : ((H r : ℤ)) = max |r.num| ((r.den : ℤ)) := by
    rw [H, Nat.cast_max, Int.natCast_natAbs]
  rw [hH]
  exact max_le (le_trans h1 (le_max_left _ _)) (le_trans h2 (le_max_right _ _))

/-- "Since `2^ℓ` and `3^k` are distinct positive integers, `|δ| < max(2^ℓ, 3^k)`." -/
lemma abs_den_lt_max {ℓ k : ℕ} (hℓ : 1 ≤ ℓ) :
    |(2 : ℤ) ^ ℓ - 3 ^ k| < max ((2 : ℤ) ^ ℓ) (3 ^ k) := by
  have h2 : (2 : ℤ) ≤ 2 ^ ℓ := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) hℓ
  have h3 : (1 : ℤ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  rcases le_total ((3 : ℤ) ^ k) ((2 : ℤ) ^ ℓ) with hle | hle
  · rw [max_eq_left hle, abs_of_nonneg (by linarith)]; linarith
  · rw [max_eq_right hle, abs_of_nonpos (by linarith)]; linarith

/-- `log₂ max(2^ℓ, 3^k) = max(ℓ, k log₂ 3)`. -/
lemma logb_max_pow (ℓ k : ℕ) :
    Real.logb 2 (max ((2 : ℝ) ^ ℓ) ((3 : ℝ) ^ k))
      = max (ℓ : ℝ) ((k : ℝ) * Real.logb 2 3) := by
  have hb : (1 : ℝ) < 2 := by norm_num
  have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hl2 : Real.logb 2 (2 : ℝ) = 1 := by rw [Real.logb, div_self hlog2ne]
  have h2 : Real.logb 2 ((2 : ℝ) ^ ℓ) = (ℓ : ℝ) := by
    rw [Real.logb_pow, hl2]; ring
  have h3 : Real.logb 2 ((3 : ℝ) ^ k) = (k : ℝ) * Real.logb 2 3 := Real.logb_pow 2 3 k
  rcases le_total ((3 : ℝ) ^ k) ((2 : ℝ) ^ ℓ) with hle | hle
  · rw [max_eq_left hle, h2, max_eq_left]
    rw [← h2, ← h3]
    exact Real.logb_le_logb_of_le hb (by positivity) hle
  · rw [max_eq_right hle, h3, max_eq_right]
    rw [← h2, ← h3]
    exact Real.logb_le_logb_of_le hb (by positivity) hle

/-- "`max(ℓ, k log₂3) < A(γ)ℓ + log₂3`", from balance. -/
lemma max_lt_A_mul {γ : ℝ} (hγ0 : 0 < γ) (ℓ k : ℕ) (hℓ : 1 ≤ ℓ)
    (hbal : ((k : ℝ)) < (ℓ : ℝ) * γ + 1) :
    max (ℓ : ℝ) ((k : ℝ) * Real.logb 2 3) < A γ * (ℓ : ℝ) + Real.logb 2 3 := by
  have hlogpos : 0 < Real.logb 2 3 := by
    have h1 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [Real.logb]
    exact div_pos h1 h2
  have hℓR : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hA1 : (1 : ℝ) ≤ A γ := le_max_left _ _
  have hA2 : γ * log2three ≤ A γ := le_max_right _ _
  have hlogeq : Real.logb 2 3 = log2three := by rw [Real.logb, log2three]
  refine max_lt ?_ ?_
  · nlinarith
  · rw [hlogeq]
    nlinarith

end Sturmian
