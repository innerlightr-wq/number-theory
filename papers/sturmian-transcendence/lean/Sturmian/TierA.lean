/-
# Stage 5, Tier A — the elementary route, and the headline slope `γ = log₃ 2`

**Tier B superseded the need for this file's thresholds**, but not its content.  Since
`Sturmian/Floor.lean` proves `ice(c_γ) ≥ 1 + φ` outright, the general theorem
`Sturmian.transcendental_charWord` already covers every `γ < γ*` on Ridout's theorem alone.
What is kept here is the record of *how little* is actually needed:

* `γ_A = 6/(5 log₂ 3) = 0.7571…` is the slope below which `2A(γ) < 12/5`, and `12/5` is
  reached by the short route `Sturmian.exists_long_period` — no `ε`-argument, no limsup
  manipulation, just the dichotomy at one record.  So `transcendental_charWord_tierA` is a
  strictly more elementary proof of a strictly weaker statement, retained deliberately.
* The headline slope `γ = log₃ 2` lies below `γ_A`, because `A(log₃ 2) = 1`
  (`A_logThreeTwo`): the headline case never needed the constant `1 + φ` at all, only
  `e > 2`.
* `log₃ 2` is irrational (`irrational_logThreeTwo`), proved here from `2^b ≠ 3^a` because
  Mathlib has no irrationality statement for logarithms.
-/
import Sturmian.Records
import Sturmian.Main

namespace Sturmian

open Filter ENNReal

/-! ## The Tier-A threshold -/

/-- `γ_A = 6/(5 log₂ 3) = 0.7571…`, the slope below which `2A(γ) < 12/5`. -/
noncomputable def gammaTierA : ℝ := 6 / (5 * log2three)

lemma gammaTierA_lt_gammaStar : gammaTierA < gammaStar := by
  have hl := log2three_pos
  rw [gammaTierA, gammaStar, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hl, eight_fifths_lt_phi_aux]

lemma two_A_lt_twelve_fifths {γ : ℝ} (hγ : γ < gammaTierA) : 2 * A γ < 12 / 5 := by
  have hl := log2three_pos
  rw [gammaTierA, lt_div_iff₀ (by positivity)] at hγ
  rw [A]
  rcases max_cases (1 : ℝ) (γ * log2three) with ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [heq]; norm_num
  · rw [heq]; linarith

/-! ## Corollary 1.4 below `γ_A`, by the elementary route -/

/-- **Corollary 1.4 for `γ < γ_A`.**  Proved from `Sturmian.exists_long_period` directly,
without the `ε`-argument of `Sturmian/Floor.lean` and without any statement about `ice`.
Subsumed by `Sturmian.transcendental_charWord`, which now covers all `γ < γ*` on the same
single axiom; kept as the short route. -/
theorem transcendental_charWord_tierA (h : IsBL Φ) {γ : ℝ}
    (hγ0 : 0 < γ) (hirr : Irrational γ) (hγA : γ < gammaTierA) :
    Transcendental ℚ ((Φ (charWord γ) : ℚ_[2])) := by
  have hγ1 : γ < 1 := lt_one_of_lt_gammaStar (lt_trans hγA gammaTierA_lt_gammaStar)
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
    (hγ0 : 0 < γ) (hirr : Irrational γ) (hγA : γ < gammaTierA) :
    Transcendental ℚ ((PhiBL (charWord γ) : ℚ_[2])) :=
  transcendental_charWord_tierA isBL_PhiBL hγ0 hirr hγA

/-- …and for the two mechanical words at intercept `0` (paper eq. (12)). -/
theorem transcendental_PhiBL_mechanical_tierA {γ : ℝ}
    (hγ0 : 0 < γ) (hirr : Irrational γ) (hγA : γ < gammaTierA) :
    Transcendental ℚ ((PhiBL (cons true (charWord γ)) : ℚ_[2])) ∧
    Transcendental ℚ ((PhiBL (cons false (charWord γ)) : ℚ_[2])) :=
  ⟨transcendental_cons_true isBL_PhiBL
      (transcendental_PhiBL_charWord_tierA hγ0 hirr hγA),
   transcendental_cons_false isBL_PhiBL
      (transcendental_PhiBL_charWord_tierA hγ0 hirr hγA)⟩

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

lemma logThreeTwo_lt_gammaStar : logThreeTwo < gammaStar :=
  lt_trans logThreeTwo_lt_gammaTierA gammaTierA_lt_gammaStar

/-- **The headline case.**  `Φ(c_{log₃2})`, `Φ(1c_{log₃2})` and `Φ(0c_{log₃2})` are all
transcendental over `ℚ`, and the only cited external input is `ridout_single_prime`.

After stage 5 this needs no special threshold — `Sturmian.transcendental_PhiBL_charWord`
covers it via `logThreeTwo_lt_gammaStar`.  It is proved below by the elementary `12/5`
route, which is what first made the headline case axiom-light. -/
theorem transcendental_PhiBL_logThreeTwo :
    Transcendental ℚ ((PhiBL (charWord logThreeTwo) : ℚ_[2])) ∧
    Transcendental ℚ ((PhiBL (cons true (charWord logThreeTwo)) : ℚ_[2])) ∧
    Transcendental ℚ ((PhiBL (cons false (charWord logThreeTwo)) : ℚ_[2])) := by
  have h := transcendental_PhiBL_charWord_tierA logThreeTwo_pos
    irrational_logThreeTwo logThreeTwo_lt_gammaTierA
  have h2 := transcendental_PhiBL_mechanical_tierA logThreeTwo_pos
    irrational_logThreeTwo logThreeTwo_lt_gammaTierA
  exact ⟨h, h2.1, h2.2⟩

/-- **The headline case in full**, including every shift: Corollary 1.4 at the resonance
slope `γ = β = log₃ 2`, "with no hypothesis on the partial quotients of `log₂ 3`". -/
theorem transcendental_PhiBL_logThreeTwo_shifts (m : ℕ) :
    Transcendental ℚ ((PhiBL (shiftIter m (charWord logThreeTwo)) : ℚ_[2])) ∧
    Transcendental ℚ ((PhiBL (shiftIter m (cons true (charWord logThreeTwo))) : ℚ_[2])) ∧
    Transcendental ℚ ((PhiBL (shiftIter m (cons false (charWord logThreeTwo))) : ℚ_[2])) :=
  transcendental_PhiBL_shifts logThreeTwo_pos irrational_logThreeTwo
    logThreeTwo_lt_gammaStar m

end Sturmian
