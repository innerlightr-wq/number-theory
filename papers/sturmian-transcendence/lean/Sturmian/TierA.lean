/-
# Stage 5, Tier A — `ice(c_γ) > 2`, and the headline case on Ridout alone

`Sturmian.Records.exists_long_period` produces, arbitrarily far out, prefixes of `c_γ` that
repeat to power `12/5`.  Two consequences:

* `two_lt_ice`: the paper's `ice(c_γ) > 2` for **every** irrational `γ ∈ (0,1)`, with no
  appeal to `bhz_ice_floor`.
* `transcendental_charWord_tierA`: the paper's Corollary 1.4 for every `γ` below the
  Tier-A threshold `γ_A = 6/(5 log₂ 3) = 0.7571…`, depending on `ridout_single_prime`
  **only**.  The headline slope `γ = log₃ 2` lies in that range, because `A(log₃ 2) = 1`.

The Tier-A threshold is smaller than the paper's `γ* = (1+φ)/(2 log₂ 3) = 0.8258…`: the gap
is exactly `12/5` versus `1+φ = 2.618…`.  For `γ ∈ [γ_A, γ*)` the result still needs
`bhz_ice_floor`; see `Sturmian.Main.transcendental_charWord`.
-/
import Sturmian.Records
import Sturmian.Main

namespace Sturmian

open Filter ENNReal

/-! ## From agreement to a prefix power -/

/-- Converse of `eq_of_lt_lcp`: agreement on an initial segment bounds `lcp` from below. -/
lemma le_lcp_of_agree {v w : Word} (h : v ≠ w) {L : ℕ} (hagr : ∀ m, m < L → v m = w m) :
    L ≤ lcp v w h := by
  rw [lcp, Nat.le_find_iff]
  intro m hm
  simp only [ne_eq, not_not]
  exact hagr m hm

/-- A length-`q` prefix that agrees with the word out to `L ≥ c·q` has prefix power `≥ c`. -/
lemma le_prefixPower {ω : Word} {q L : ℕ} (hq : 0 < q) (hne : ω ≠ per q ω)
    (hagr : ∀ m, m < L → ω m = per q ω m) {c : ℝ} (hc0 : 0 ≤ c)
    (hcL : c * (q : ℝ) ≤ (L : ℝ)) :
    ENNReal.ofReal c ≤ prefixPower ω q := by
  have hqne : ((q : ℕ) : ℝ≥0∞) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hqtop : ((q : ℕ) : ℝ≥0∞) ≠ ⊤ := by simp
  rw [prefixPower, dif_neg hne, ENNReal.le_div_iff_mul_le (Or.inl hqne) (Or.inl hqtop)]
  have hstep : ENNReal.ofReal c * ((q : ℕ) : ℝ≥0∞) = ENNReal.ofReal (c * (q : ℝ)) := by
    rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_natCast]
  rw [hstep, show ((lcp ω (per q ω) hne : ℕ) : ℝ≥0∞)
      = ENNReal.ofReal ((lcp ω (per q ω) hne : ℝ)) from (ENNReal.ofReal_natCast _).symm,
    ENNReal.ofReal_le_ofReal_iff (by positivity)]
  refine le_trans hcL ?_
  exact_mod_cast le_lcp_of_agree hne hagr

/-! ## Tier A, in the paper's own language -/

/-- **Tier A.**  `ice(c_γ) ≥ 12/5` for every irrational `γ ∈ (0,1)`.  Unconditional: the
Berthé–Holton–Zamboni floor is not used. -/
theorem twelve_fifths_le_ice {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hirr : Irrational γ) :
    ENNReal.ofReal (12 / 5) ≤ ice (charWord γ) := by
  refine le_limsup_of_frequently_le ?_
  rw [frequently_atTop]
  intro N
  obtain ⟨q, L, hqN, hq2, hcL, hagr⟩ := exists_long_period hirr N
  refine ⟨q, hqN, ?_⟩
  exact le_prefixPower (by omega) (charWord_ne_per hγ0 hγ1 hirr (by omega) (charWord γ))
    hagr (by norm_num) hcL

/-- **The paper's `ice(c_γ) > 2`**, for every irrational `γ ∈ (0,1)`, proved. -/
theorem two_lt_ice {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hirr : Irrational γ) :
    2 < ice (charWord γ) := by
  refine lt_of_lt_of_le ?_ (twelve_fifths_le_ice hγ0 hγ1 hirr)
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).mpr (by norm_num)

/-! ## The Tier-A threshold -/

/-- `γ_A = 6/(5 log₂ 3) = 0.7571…`, the slope below which `2A(γ) < 12/5`. -/
noncomputable def gammaTierA : ℝ := 6 / (5 * log2three)

/-- `φ > 8/5`: enough to separate `12/5` from `1 + φ`. -/
lemma eight_fifths_lt_phi : (8 : ℝ) / 5 < phi := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have h : (11 : ℝ) / 5 < Real.sqrt 5 := by nlinarith [h5, hnn]
  rw [phi]; linarith

lemma gammaTierA_lt_gammaStar : gammaTierA < gammaStar := by
  have hl := log2three_pos
  rw [gammaTierA, gammaStar, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hl, eight_fifths_lt_phi]

lemma two_A_lt_twelve_fifths {γ : ℝ} (hγ : γ < gammaTierA) : 2 * A γ < 12 / 5 := by
  have hl := log2three_pos
  rw [gammaTierA, lt_div_iff₀ (by positivity)] at hγ
  rw [A]
  rcases max_cases (1 : ℝ) (γ * log2three) with ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [heq]; norm_num
  · rw [heq]; linarith

/-! ## Corollary 1.4 below `γ_A`, on Ridout alone -/

/-- **Corollary 1.4 for `γ < γ_A`, depending only on `ridout_single_prime`.**  No use of
`bhz_ice_floor`: the prefix family comes from `Sturmian.Records.exists_long_period`. -/
theorem transcendental_charWord_tierA (h : IsBL Φ) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hirr : Irrational γ) (hγA : γ < gammaTierA) :
    Transcendental ℚ ((Φ (charWord γ) : ℚ_[2])) := by
  choose ℓ L hℓN hℓ2 hLge hagr using fun j : ℕ => exists_long_period hirr (max j 2)
  refine transcendental_of_prefix_family h hγ0 hγ1 hirr (e := 12 / 5) (by norm_num)
    (two_A_lt_twelve_fifths hγA) (W := fun _ => charWord γ) hℓ2 ?_ ?_
  · refine tendsto_atTop_mono (fun j => ?_) tendsto_natCast_atTop_atTop
    exact_mod_cast le_trans (le_max_left j 2) (hℓN j)
  · intro j n hn
    refine hagr j n ?_
    have : (n : ℝ) < (L j : ℝ) := lt_of_lt_of_le hn (hLge j)
    exact_mod_cast this

/-- …and for the constructed Bernstein–Lagarias map. -/
theorem transcendental_PhiBL_charWord_tierA {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hirr : Irrational γ) (hγA : γ < gammaTierA) :
    Transcendental ℚ ((PhiBL (charWord γ) : ℚ_[2])) :=
  transcendental_charWord_tierA isBL_PhiBL hγ0 hγ1 hirr hγA

/-- …and for the two mechanical words at intercept `0` (paper eq. (12)). -/
theorem transcendental_PhiBL_mechanical_tierA {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hirr : Irrational γ) (hγA : γ < gammaTierA) :
    Transcendental ℚ ((PhiBL (cons true (charWord γ)) : ℚ_[2])) ∧
    Transcendental ℚ ((PhiBL (cons false (charWord γ)) : ℚ_[2])) :=
  ⟨transcendental_cons_true isBL_PhiBL
      (transcendental_PhiBL_charWord_tierA hγ0 hγ1 hirr hγA),
   transcendental_cons_false isBL_PhiBL
      (transcendental_PhiBL_charWord_tierA hγ0 hγ1 hirr hγA)⟩

/-! ## The headline slope `γ = log₃ 2`

Paper, §1.2: "the headline case is the slope `γ = log₃ 2`, for which `A(γ) = 1`."

Mathlib has no irrationality statement for logarithms, so `irrational_logThreeTwo` is proved
here, from `two_pow_ne_three_pow` (the same parity fact the shadow denominators use). -/

/-- `log₃ 2 = log 2 / log 3`. -/
noncomputable def logThreeTwo : ℝ := Real.log 2 / Real.log 3

lemma log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

lemma log_three_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)

lemma logThreeTwo_pos : 0 < logThreeTwo := div_pos log_two_pos log_three_pos

lemma logThreeTwo_lt_one : logThreeTwo < 1 := by
  rw [logThreeTwo, div_lt_one log_three_pos]
  exact Real.log_lt_log (by norm_num) (by norm_num)

/-- `log₃ 2 · log₂ 3 = 1`: this is why `A(log₃ 2) = 1`. -/
lemma logThreeTwo_mul_log2three : logThreeTwo * log2three = 1 := by
  rw [logThreeTwo, log2three]
  field_simp

/-- **`A(log₃ 2) = 1`**, the paper's reason the headline case only needs `e > 2`. -/
lemma A_logThreeTwo : A logThreeTwo = 1 := by
  rw [A, logThreeTwo_mul_log2three]; simp

/-- **`log₃ 2` is irrational**, from `2^b ≠ 3^a`. -/
theorem irrational_logThreeTwo : Irrational logThreeTwo := by
  rintro ⟨q, hq⟩
  have hl2 := log_two_pos
  have hl3 := log_three_pos
  have hqpos : 0 < q := by
    have h : (0 : ℝ) < (q : ℝ) := by rw [hq]; exact logThreeTwo_pos
    exact_mod_cast h
  have hnum : 0 < q.num := Rat.num_pos.mpr hqpos
  have hden : 0 < q.den := q.pos
  have hdenR : ((q.den : ℝ)) ≠ 0 := by positivity
  have heq : (q : ℝ) * Real.log 3 = Real.log 2 := by
    rw [hq, logThreeTwo]; field_simp
  have hcast : ((q.num : ℝ)) * Real.log 3 = ((q.den : ℝ)) * Real.log 2 := by
    rw [Rat.cast_def] at heq
    field_simp at heq
    linarith [heq]
  have hlog : Real.log ((3 : ℝ) ^ q.num.toNat) = Real.log ((2 : ℝ) ^ q.den) := by
    rw [Real.log_pow, Real.log_pow]
    have htn : ((q.num.toNat : ℕ) : ℝ) = ((q.num : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (le_of_lt hnum)
    rw [htn]
    push_cast
    linarith [hcast]
  have hpow : ((3 : ℝ) ^ q.num.toNat) = ((2 : ℝ) ^ q.den) := by
    have h3 : (0 : ℝ) < (3 : ℝ) ^ q.num.toNat := by positivity
    have h2 : (0 : ℝ) < (2 : ℝ) ^ q.den := by positivity
    have hc := congrArg Real.exp hlog
    rwa [Real.exp_log h3, Real.exp_log h2] at hc
  have hz : ((3 : ℤ) ^ q.num.toNat) = ((2 : ℤ) ^ q.den) := by exact_mod_cast hpow
  exact two_pow_ne_three_pow (ℓ := q.den) (k := q.num.toNat) (by omega) hz.symm

lemma logThreeTwo_lt_gammaTierA : logThreeTwo < gammaTierA := by
  have hl := log2three_pos
  rw [gammaTierA, lt_div_iff₀ (by positivity)]
  nlinarith [logThreeTwo_mul_log2three]

/-- **The headline case, on Ridout alone.**  `Φ(c_{log₃2})`, `Φ(1c_{log₃2})` and
`Φ(0c_{log₃2})` are all transcendental over `ℚ`, and the only cited external input is
`ridout_single_prime`. -/
theorem transcendental_PhiBL_logThreeTwo :
    Transcendental ℚ ((PhiBL (charWord logThreeTwo) : ℚ_[2])) ∧
    Transcendental ℚ ((PhiBL (cons true (charWord logThreeTwo)) : ℚ_[2])) ∧
    Transcendental ℚ ((PhiBL (cons false (charWord logThreeTwo)) : ℚ_[2])) := by
  have h := transcendental_PhiBL_charWord_tierA logThreeTwo_pos logThreeTwo_lt_one
    irrational_logThreeTwo logThreeTwo_lt_gammaTierA
  have h2 := transcendental_PhiBL_mechanical_tierA logThreeTwo_pos logThreeTwo_lt_one
    irrational_logThreeTwo logThreeTwo_lt_gammaTierA
  exact ⟨h, h2.1, h2.2⟩

end Sturmian
