/-
# Item 1 of the stage-2 brief — `Φ` exists

Paper, §1.1:

> "Bernstein and Lagarias [3, 1] proved that $T$ and $S$ are conjugate: there is a unique
>  homeomorphism $\PH:\Z_2\to\Z_2$ with $\PH(0)=0$ and $\PH\circ S\circ\PH^{-1}=T$."

This file **constructs** a map satisfying `IsBL` instead of assuming one, so that no
existence axiom is needed.  The construction is the paper's own eq. (3) solved for `Φ(v)`:
since `3` is a unit of `ℤ_[2]`, eq. (3) gives

  `Φ(v) ≡ −c_m(v) · 3^(−k_m(v))  (mod 2^m)`,

so `Φ(v)` is the `2`-adic limit of `approx v m := −c_m(v) · inv3 ^ k_m(v)`.  The
consecutive differences have norm at most `2^(−m)`, so the sequence is Cauchy and `ℤ_[2]`
is complete.
-/
import Sturmian.BL
import Mathlib.Analysis.SpecificLimits.Basic

namespace Sturmian

open Filter

/-! ## `3` is a unit of `ℤ_[2]` -/

lemma isUnit_three : IsUnit (3 : ℤ_[2]) := PadicInt.isUnit_iff.mpr norm_three

/-- The inverse of `3` in `ℤ_[2]`. -/
noncomputable def inv3 : ℤ_[2] := ↑(isUnit_three.unit⁻¹)

lemma three_mul_inv3 : (3 : ℤ_[2]) * inv3 = 1 := by
  have h : (isUnit_three.unit : ℤ_[2]) = 3 := isUnit_three.unit_spec
  calc (3 : ℤ_[2]) * inv3 = (isUnit_three.unit : ℤ_[2]) * ↑(isUnit_three.unit⁻¹) := by rw [h, inv3]
    _ = ((isUnit_three.unit * isUnit_three.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) := by push_cast; ring
    _ = 1 := by rw [mul_inv_cancel]; rfl

lemma norm_inv3 : ‖inv3‖ = 1 := by
  have h := three_mul_inv3
  have hn : ‖(3 : ℤ_[2])‖ * ‖inv3‖ = 1 := by rw [← norm_mul, h, norm_one]
  rw [norm_three, one_mul] at hn
  exact hn

lemma three_pow_mul_inv3_pow (k : ℕ) : (3 : ℤ_[2]) ^ k * inv3 ^ k = 1 := by
  rw [← mul_pow, three_mul_inv3, one_pow]

lemma norm_inv3_pow (k : ℕ) : ‖inv3 ^ k‖ = 1 := by
  rw [norm_pow, norm_inv3, one_pow]

/-! ## The approximating sequence -/

/-- `approx v m := −c_m(v) · inv3 ^ k_m(v)` — the paper's eq. (3) solved for `Φ(v)` modulo
`2^m`. -/
noncomputable def approx (v : Word) (m : ℕ) : ℤ_[2] :=
  -((cw m v : ℤ) : ℤ_[2]) * inv3 ^ (ones m v)

@[simp] lemma approx_zero (v : Word) : approx v 0 = 0 := by simp [approx]

/-- The consecutive differences are small: `‖approx v (m+1) − approx v m‖ ≤ 2^(−m)`. -/
lemma norm_approx_succ_sub (v : Word) (m : ℕ) :
    ‖approx v (m + 1) - approx v m‖ ≤ (1 / 2 : ℝ) ^ m := by
  by_cases hv : v m = true
  · have hk : ones (m + 1) v = ones m v + 1 := by rw [ones_succ]; simp [hv]
    have hc : cw (m + 1) v = 3 * cw m v + 2 ^ m := by rw [cw_succ]; simp [hv]
    have hstep : approx v (m + 1) - approx v m = -((2 : ℤ_[2]) ^ m) * inv3 ^ (ones m v + 1) := by
      rw [approx, approx, hk, hc]
      push_cast
      have h3 : (3 : ℤ_[2]) * inv3 ^ (ones m v + 1) = inv3 ^ (ones m v) := by
        rw [pow_succ]
        calc (3 : ℤ_[2]) * (inv3 ^ ones m v * inv3)
            = (3 * inv3) * inv3 ^ ones m v := by ring
          _ = inv3 ^ ones m v := by rw [three_mul_inv3, one_mul]
      linear_combination (-((cw m v : ℤ) : ℤ_[2])) * h3
    rw [hstep, norm_mul, norm_neg, norm_pow, norm_two, norm_inv3_pow, mul_one]
  · have hv' : v m = false := by simpa using hv
    have hk : ones (m + 1) v = ones m v := by rw [ones_succ]; simp [hv']
    have hc : cw (m + 1) v = cw m v := by rw [cw_succ]; simp [hv']
    have : approx v (m + 1) - approx v m = 0 := by rw [approx, approx, hk, hc]; ring
    rw [this, norm_zero]
    positivity

lemma cauchySeq_approx (v : Word) : CauchySeq (approx v) := by
  refine cauchySeq_of_le_geometric_two (C := 4) ?_
  intro n
  have h := norm_approx_succ_sub v n
  rw [dist_eq_norm]
  have hsym : ‖approx v n - approx v (n + 1)‖ = ‖approx v (n + 1) - approx v n‖ := by
    rw [← norm_neg]; ring_nf
  rw [hsym]
  calc ‖approx v (n + 1) - approx v n‖ ≤ (1 / 2 : ℝ) ^ n := h
    _ = 1 / 2 ^ n := by rw [div_pow, one_pow]
    _ ≤ 4 / 2 / 2 ^ n := by
        rw [show (4 : ℝ) / 2 = 2 by norm_num]
        have hp : (0 : ℝ) < 2 ^ n := by positivity
        rw [div_le_div_iff_of_pos_right hp]
        norm_num

/-! ## `Φ` -/

/-- The Bernstein–Lagarias conjugacy map, constructed as the `2`-adic limit of the
approximants of eq. (3). -/
noncomputable def PhiBL (v : Word) : ℤ_[2] := (cauchySeq_tendsto_of_complete (cauchySeq_approx v)).choose

lemma tendsto_approx (v : Word) : Tendsto (approx v) atTop (nhds (PhiBL v)) :=
  (cauchySeq_tendsto_of_complete (cauchySeq_approx v)).choose_spec

/-- `Φ(v) ≡ approx v m (mod 2^m)`, the content of eq. (3). -/
lemma norm_PhiBL_sub_approx (v : Word) (m : ℕ) :
    ‖PhiBL v - approx v m‖ ≤ (1 / 2 : ℝ) ^ m := by
  have hmono : ∀ n, m ≤ n → ‖approx v n - approx v m‖ ≤ (1 / 2 : ℝ) ^ m := by
    intro n
    induction n with
    | zero =>
      intro hle
      have hm : m = 0 := by omega
      subst hm; simp
    | succ k ih =>
      intro hn
      rcases Nat.lt_or_ge m (k + 1) with hlt | hge
      · have hmk : m ≤ k := by omega
        have h1 : ‖approx v (k + 1) - approx v k‖ ≤ (1 / 2 : ℝ) ^ k := norm_approx_succ_sub v k
        have h2 := ih hmk
        have hsp : approx v (k + 1) - approx v m
            = (approx v (k + 1) - approx v k) + (approx v k - approx v m) := by ring
        rw [hsp]
        refine le_trans (PadicInt.nonarchimedean _ _) (max_le ?_ h2)
        exact le_trans h1 (pow_le_pow_of_le_one (by norm_num) (by norm_num) hmk)
      · have hm : m = k + 1 := by omega
        subst hm; simp
  have hlim : Tendsto (fun n => ‖approx v n - approx v m‖) atTop
      (nhds ‖PhiBL v - approx v m‖) :=
    Filter.Tendsto.norm ((tendsto_approx v).sub_const (approx v m))
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop m] with n hn using hmono n hn

/-! ## `PhiBL` satisfies `IsBL` -/

lemma approx_cons_false (c : Word) (m : ℕ) :
    approx (cons false c) (m + 1) = 2 * approx c m := by
  rw [approx, approx, ones_cons_false_succ, cw_cons_false_succ]
  push_cast
  ring

lemma approx_cons_true (c : Word) (m : ℕ) :
    3 * approx (cons true c) (m + 1) = 2 * approx c m - 1 := by
  rw [approx, approx, ones_cons_true_succ, cw_cons_true_succ]
  push_cast
  have h3 : (3 : ℤ_[2]) * inv3 ^ (ones m c + 1) = inv3 ^ (ones m c) := by
    rw [pow_succ]
    calc (3 : ℤ_[2]) * (inv3 ^ ones m c * inv3)
        = (3 * inv3) * inv3 ^ ones m c := by ring
      _ = inv3 ^ ones m c := by rw [three_mul_inv3, one_mul]
  have hpow : (3 : ℤ_[2]) ^ (ones m c) * inv3 ^ (ones m c) = 1 := three_pow_mul_inv3_pow _
  linear_combination
    (-(2 * ((cw m c : ℤ) : ℤ_[2]) + (3 : ℤ_[2]) ^ (ones m c))) * h3 - hpow

/-- A limit characterisation: if `x` agrees with `approx v m` to within `2^(−m)` for every
`m`, then `x = PhiBL v`. -/
lemma eq_PhiBL_of_approx {x : ℤ_[2]} {v : Word}
    (h : ∀ m, ‖x - approx v m‖ ≤ (1 / 2 : ℝ) ^ m) : x = PhiBL v := by
  have hzero : ∀ m, ‖x - PhiBL v‖ ≤ (1 / 2 : ℝ) ^ m := by
    intro m
    have h1 := h m
    have h2 := norm_PhiBL_sub_approx v m
    have hsplit : x - PhiBL v = (x - approx v m) - (PhiBL v - approx v m) := by ring
    rw [hsplit]
    refine le_trans (norm_sub_le_max _ _) (max_le h1 h2)
  have hle0 : ‖x - PhiBL v‖ ≤ 0 := by
    refine ge_of_tendsto (f := fun m : ℕ => (1 / 2 : ℝ) ^ m)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)) ?_
    filter_upwards with m using hzero m
  have := le_antisymm hle0 (norm_nonneg _)
  rwa [norm_eq_zero, sub_eq_zero] at this

/-- **`PhiBL` satisfies the Bernstein–Lagarias recursion.**  Hence `IsBL` is not vacuous
and no existence axiom is needed for `Φ`. -/
theorem isBL_PhiBL : IsBL PhiBL := by
  constructor
  · intro c
    refine (eq_PhiBL_of_approx (x := 2 * PhiBL c) (v := cons false c) ?_).symm
    intro m
    cases m with
    | zero =>
      simp only [approx_zero, sub_zero, pow_zero]
      exact PadicInt.norm_le_one _
    | succ k =>
      rw [approx_cons_false]
      have h := norm_PhiBL_sub_approx c k
      have hre : (2 : ℤ_[2]) * PhiBL c - 2 * approx c k = 2 * (PhiBL c - approx c k) := by ring
      rw [hre, norm_mul, norm_two]
      calc (1 / 2 : ℝ) * ‖PhiBL c - approx c k‖
          ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k := mul_le_mul_of_nonneg_left h (by norm_num)
        _ = (1 / 2 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
  · intro c
    have key : inv3 * (2 * PhiBL c - 1) = PhiBL (cons true c) := by
      refine eq_PhiBL_of_approx (v := cons true c) ?_
      intro m
      cases m with
      | zero =>
        simp only [approx_zero, sub_zero, pow_zero]
        exact PadicInt.norm_le_one _
      | succ k =>
        have happ : approx (cons true c) (k + 1) = inv3 * (2 * approx c k - 1) := by
          have h3 := approx_cons_true c k
          calc approx (cons true c) (k + 1)
              = 1 * approx (cons true c) (k + 1) := by ring
            _ = (inv3 * 3) * approx (cons true c) (k + 1) := by
                  rw [show inv3 * (3 : ℤ_[2]) = 1 by rw [mul_comm]; exact three_mul_inv3]
            _ = inv3 * (3 * approx (cons true c) (k + 1)) := by ring
            _ = inv3 * (2 * approx c k - 1) := by rw [h3]
        rw [happ]
        have hre : inv3 * (2 * PhiBL c - 1) - inv3 * (2 * approx c k - 1)
            = inv3 * (2 * (PhiBL c - approx c k)) := by ring
        rw [hre, norm_mul, norm_inv3, one_mul, norm_mul, norm_two]
        have h := norm_PhiBL_sub_approx c k
        calc (1 / 2 : ℝ) * ‖PhiBL c - approx c k‖
            ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k := mul_le_mul_of_nonneg_left h (by norm_num)
          _ = (1 / 2 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
    rw [← key]
    linear_combination (2 * PhiBL c - 1) * three_mul_inv3

end Sturmian
