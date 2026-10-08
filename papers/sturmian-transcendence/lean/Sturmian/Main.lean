/-
# Assembly: the paper's Theorem 1.3 and Corollary 1.4, modulo stage 3

Everything here is **proved**, from: the stage-2 core (`Sturmian/BL.lean`,
`Sturmian/Shadow.lean`, `Sturmian/Construct.lean`), the stage-1 skeleton
(`Sturmian/Skeleton.lean`), and the three axioms of `Sturmian/Axioms.lean`.

The paper's proof of Theorem 1.3 runs in six steps (§3).  Their status here:

| step | content | status |
|---|---|---|
| 1 | choose `e` with `max(2A(γ),2) < e < ice(c_γ)` | inside Axiom BHZ (stage 3) |
| 2 | the primitive-prefix family, and the height bound | Axiom BHZ + Axiom 2.4 (stage 3) |
| 3 | depth ⟹ approximation exponent | **PROVED** (the isometry, `IsBL.isometry`) |
| 4 | the shadows are infinitely many and distinct | **PROVED** (`IsBL.injective`) |
| 5 | Theorem R applies | Axiom R (stage 1) |
| 6 | transfer along the shift orbit | **PROVED** (`IsBL.transfer`) |
-/
import Sturmian.Skeleton
import Sturmian.Shadow
import Sturmian.Construct
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Sturmian

open Filter

/-! ## The one analytic input: the paper's error term is sublinear

Paper, eq. (10): `1+w_j = eℓ_j/log₂H(R_j) > eℓ_j/(A ℓ_j + log₂(3ℓ_j) + log₂3) → e/A`.
The limit is exactly the statement that `log₂(3ℓ) + log₂3 = o(ℓ)`. -/

lemma tendsto_log_div_atTop : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
  simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero

/-- `(log₂(3ℓ) + log₂3)/ℓ → 0`: the paper's error term is sublinear in `ℓ`. -/
lemma tendsto_errorTerm :
    Tendsto (fun x : ℝ => (Real.logb 2 (3 * x) + Real.logb 2 3) / x) atTop (nhds 0) := by
  have hlog2 : Real.log 2 ≠ 0 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := tendsto_log_div_atTop
  have h2 : Tendsto (fun x : ℝ => (2 * Real.log 3) / x) atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
  have hsum : Tendsto (fun x : ℝ => (Real.log x / x + (2 * Real.log 3) / x) / Real.log 2)
      atTop (nhds 0) := by
    have := (h1.add h2).div_const (Real.log 2)
    simpa using this
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.logb, Real.logb, Real.log_mul (by norm_num) (ne_of_gt hx)]
  field_simp
  ring

/-! ## Transcendence transfers along an invertible `ℚ`-affine map

Paper, Step 6: "All three maps are `Q`-affine and invertible over `Q`, so the three values
are simultaneously algebraic or simultaneously transcendental." -/

open Polynomial in
/-- If `y` is algebraic over `ℚ` then so is `a y + b` for rationals `a ≠ 0`, `b`. -/
lemma isAlgebraic_affine {y : ℚ_[2]} (a b : ℚ) (ha : a ≠ 0) (hy : IsAlgebraic ℚ y) :
    IsAlgebraic ℚ ((a : ℚ_[2]) * y + (b : ℚ_[2])) := by
  obtain ⟨p, hp0, hpy⟩ := hy
  refine ⟨p.comp (C a⁻¹ * X - C (a⁻¹ * b)), ?_, ?_⟩
  · intro hz
    rcases (comp_eq_zero_iff).mp hz with hh | ⟨_, h2⟩
    · exact hp0 hh
    · have hc1 : (C a⁻¹ * X - C (a⁻¹ * b)).coeff 1 = a⁻¹ := by simp
      rw [h2] at hc1
      have h0 : (0 : ℚ) = a⁻¹ := by simpa using hc1
      exact ha (inv_eq_zero.mp h0.symm)
  · rw [aeval_comp]
    have ha' : ((a : ℚ_[2])) ≠ 0 := by exact_mod_cast ha
    have hinner : (aeval ((a : ℚ_[2]) * y + (b : ℚ_[2]))) (C a⁻¹ * X - C (a⁻¹ * b)) = y := by
      simp only [map_sub, map_mul, aeval_C, aeval_X, eq_ratCast]
      push_cast
      field_simp
      ring
    rw [hinner]
    exact hpy

/-- The contrapositive form used below. -/
lemma transcendental_of_affine {y : ℚ_[2]} (a b : ℚ) (ha : a ≠ 0)
    (h : Transcendental ℚ ((a : ℚ_[2]) * y + (b : ℚ_[2]))) : Transcendental ℚ y := by
  intro hy
  exact h (isAlgebraic_affine a b ha hy)

/-! ## The main theorem, with Steps 1–2 as hypotheses -/

variable {Φ : Word → ℤ_[2]}

/-- **Steps 3–6, proved.**  Given the prefix family of Steps 1–2 and the height bound,
`Φ(c)` is transcendental.  Every hypothesis is a displayed line of the paper. -/
theorem transcendental_of_prefix_family (h : IsBL Φ) (c : Word)
    {Aγ e : ℝ} (hA : 0 < Aγ) (he2 : 2 < e) (heA : 2 * Aγ < e)
    {ℓ : ℕ → ℕ} {W : ℕ → Word}
    (hℓ2 : ∀ j, 2 ≤ ℓ j)
    (hℓinf : Tendsto (fun j => (ℓ j : ℝ)) atTop atTop)
    (hinj : Function.Injective fun j => per (ℓ j) (W j))
    (hne : ∀ j, c ≠ per (ℓ j) (W j))
    (hagree : ∀ j (n : ℕ), (n : ℝ) < e * (ℓ j : ℝ) → c n = per (ℓ j) (W j) n)
    (hheight : ∀ j, Real.logb 2 (H (shadowRat (ℓ j) (W j)))
        < Aγ * (ℓ j : ℝ) + Real.logb 2 (3 * (ℓ j : ℝ)) + Real.logb 2 3) :
    Transcendental ℚ ((Φ c : ℚ_[2])) := by
  classical
  set R : ℕ → ℚ := fun j => shadowRat (ℓ j) (W j) with hRdef
  have hℓpos : ∀ j, (0 : ℝ) < (ℓ j : ℝ) := by
    intro j
    have : 0 < ℓ j := lt_of_lt_of_le (by norm_num) (hℓ2 j)
    exact_mod_cast this
  -- the exponent μ, strictly between 2 and e/A
  have heA' : 2 < e / Aγ := by rw [lt_div_iff₀ hA]; linarith
  set μ : ℝ := (2 + e / Aγ) / 2 with hμdef
  have hμ2 : 2 < μ := by rw [hμdef]; linarith
  have hμe : μ < e / Aγ := by rw [hμdef]; linarith
  have hμpos : (0 : ℝ) < μ := by linarith
  have hμA : μ * Aγ < e := by have := (lt_div_iff₀ hA).mp hμe; linarith
  -- the error term is eventually small enough
  set δ : ℝ := (e - μ * Aγ) / μ with hδdef
  have hδpos : 0 < δ := div_pos (by linarith) hμpos
  have hsmall : ∀ᶠ j in atTop,
      (Real.logb 2 (3 * (ℓ j : ℝ)) + Real.logb 2 3) / (ℓ j : ℝ) < δ :=
    (tendsto_errorTerm.comp hℓinf).eventually_lt_const hδpos
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hsmall
  -- Step 3: the depth bound, from agreement of the first ⌈eℓ⌉ letters
  have hdepth : ∀ j, e * (ℓ j : ℝ) ≤ ((lcp c (per (ℓ j) (W j)) (hne j) : ℕ) : ℝ) := by
    intro j
    by_contra hcon
    push_neg at hcon
    exact (lcp_spec c (per (ℓ j) (W j)) (hne j)) (hagree j _ hcon)
  -- Step 3: the approximation bound, via the isometry
  have happrox : ∀ j, ‖((Φ c : ℚ_[2])) - ((R j : ℚ) : ℚ_[2])‖
      ≤ (2 : ℝ) ^ (-(e * (ℓ j : ℝ))) := by
    intro j
    have hℓ1 : 1 ≤ ℓ j := le_trans (by norm_num) (hℓ2 j)
    have hsf := shadow_formula h hℓ1 (W j)
    have hdiff : ((Φ c : ℚ_[2])) - ((R j : ℚ) : ℚ_[2])
        = (((Φ c - Φ (per (ℓ j) (W j))) : ℤ_[2]) : ℚ_[2]) := by
      rw [hRdef, ← hsf, PadicInt.coe_sub]
    rw [hdiff, ← PadicInt.norm_def, h.isometry c (per (ℓ j) (W j)) (hne j)]
    have hzr : (2 : ℝ) ^ (-((lcp c (per (ℓ j) (W j)) (hne j) : ℕ) : ℤ))
        = (2 : ℝ) ^ (-(((lcp c (per (ℓ j) (W j)) (hne j) : ℕ) : ℝ))) := by
      rw [← Real.rpow_intCast]; push_cast; ring_nf
    rw [hzr]
    exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr (by linarith [hdepth j])
  -- Step 4: the shadows are pairwise distinct
  have hRinj : Function.Injective R := by
    intro i j hij
    by_contra hij'
    exact shadowRat_inj_of_word_ne h (le_trans (by norm_num) (hℓ2 i))
      (le_trans (by norm_num) (hℓ2 j)) (fun hw => hij' (hinj hw)) hij
  -- "no shadow has H = 1": discard the finitely many of height ≤ 1
  have hfinH : {j : ℕ | H (R j) ≤ 1}.Finite := by
    refine Set.Finite.of_finite_image (f := R) ?_ hRinj.injOn
    exact Set.Finite.subset (finite_setOf_H_le 1) (by rintro r ⟨j, hj, rfl⟩; exact hj)
  set T : Set ℕ := {j : ℕ | J ≤ j} \ {j : ℕ | H (R j) ≤ 1} with hTdef
  have hTinf : T.Infinite := by
    refine Set.Infinite.diff ?_ hfinH
    have hcompl : ((Set.Iio J : Set ℕ))ᶜ = {j : ℕ | J ≤ j} := by
      ext n; simp [Set.mem_Iio, not_lt]
    rw [← hcompl]
    exact (Set.finite_Iio J).infinite_compl
  -- Step 5: apply the stage-1 skeleton
  refine transcendental_of_approxExp hμ2 (R '' T) (hTinf.image hRinj.injOn) ?_
  rintro r ⟨j, hjT, rfl⟩
  obtain ⟨hjJ, hjH⟩ := hjT
  have hH1 : (1 : ℝ) < (H (R j) : ℝ) := by
    have h1 : 1 < H (R j) := by
      simp only [Set.mem_setOf_eq, not_le] at hjH; exact hjH
    exact_mod_cast h1
  have hsm := hJ j hjJ
  have hmul : Real.logb 2 (3 * (ℓ j : ℝ)) + Real.logb 2 3 < δ * (ℓ j : ℝ) := by
    rw [div_lt_iff₀ (hℓpos j)] at hsm; linarith
  have h1 : μ * (Real.logb 2 (3 * (ℓ j : ℝ)) + Real.logb 2 3) ≤ μ * (δ * (ℓ j : ℝ)) :=
    mul_le_mul_of_nonneg_left (le_of_lt hmul) (le_of_lt hμpos)
  have h2 : μ * (δ * (ℓ j : ℝ)) = (e - μ * Aγ) * (ℓ j : ℝ) := by
    rw [← mul_assoc, hδdef]; field_simp
  have hcomp : μ * (Aγ * (ℓ j : ℝ) + Real.logb 2 (3 * (ℓ j : ℝ)) + Real.logb 2 3)
      ≤ e * (ℓ j : ℝ) := by nlinarith [h1, h2]
  exact approx_of_depth_height hμpos hH1 (happrox j) (hheight j) hcomp

/-! ## The paper's Corollary 1.4, modulo stage 3 -/

/-- **The paper's Corollary 1.4** for the characteristic word, assembled from the three
axioms and everything proved in stages 1–2. -/
theorem transcendental_charWord (h : IsBL Φ) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hirr : Irrational γ) (hγs : γ < gammaStar) :
    Transcendental ℚ ((Φ (charWord γ) : ℚ_[2])) := by
  have hA : 0 < A γ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have h2A : 2 * A γ < 1 + phi := two_A_lt_one_add_phi hγs
  have h2φ : (2 : ℝ) < 1 + phi := by have := one_lt_phi; linarith
  have hmaxlt : max (2 * A γ) 2 < 1 + phi := max_lt h2A h2φ
  set e : ℝ := (max (2 * A γ) 2 + (1 + phi)) / 2 with hedef
  have he2 : 2 < e := by
    have hm : (2 : ℝ) ≤ max (2 * A γ) 2 := le_max_right _ _
    rw [hedef]; linarith
  have heA : 2 * A γ < e := by
    have hm : 2 * A γ ≤ max (2 * A γ) 2 := le_max_left _ _
    rw [hedef]; linarith
  have heφ : e < 1 + phi := by rw [hedef]; linarith
  obtain ⟨ℓ, W, hℓ2, hk, hℓinf, hinj, hne, hagree⟩ :=
    bhz_prefix_family hγ0 hγ1 hirr he2 heφ
  refine transcendental_of_prefix_family h (charWord γ) hA he2 heA hℓ2 hℓinf hinj hne hagree ?_
  intro j
  have hℓpos : (0 : ℝ) < (ℓ j : ℝ) := by
    have : 0 < ℓ j := lt_of_lt_of_le (by norm_num) (hℓ2 j)
    exact_mod_cast this
  refine shadow_height_bound hγ0 hγ1 (ℓ j) (W j) (hℓ2 j) (hk j) ?_
  intro n hn
  exact hagree j n (by nlinarith [hn, mul_pos (sub_pos.mpr he2) hℓpos])

/-! ## Step 6 — the transfer to `Φ(1c_γ)` and `Φ(0c_γ)`

Paper, eq. (12): `2Φ(c_γ) = 3Φ(1c_γ) + 1 = Φ(0c_γ)`. -/

/-- `((2 : ℤ_[2]) : ℚ_[2]) = 2`, to keep numerals from drifting across the coercion. -/
lemma coe_two_padicInt : (((2 : ℤ_[2])) : ℚ_[2]) = 2 := rfl

/-- `((3 : ℤ_[2]) : ℚ_[2]) = 3`. -/
lemma coe_three_padicInt : (((3 : ℤ_[2])) : ℚ_[2]) = 3 := rfl

/-- `Φ(0c)` is transcendental whenever `Φ(c)` is: `Φ(0c) = 2Φ(c)`. -/
theorem transcendental_cons_false (h : IsBL Φ) {c : Word}
    (hc : Transcendental ℚ ((Φ c : ℚ_[2]))) :
    Transcendental ℚ ((Φ (cons false c) : ℚ_[2])) := by
  refine transcendental_of_affine (y := ((Φ (cons false c) : ℚ_[2]))) (1 / 2) 0 (by norm_num) ?_
  have h2 : Φ (cons false c) = 2 * Φ c := h.cons_false c
  have hcg : ((Φ (cons false c) : ℚ_[2])) = (((2 : ℤ_[2]) * Φ c : ℤ_[2]) : ℚ_[2]) :=
    congrArg _ h2
  rw [PadicInt.coe_mul, coe_two_padicInt] at hcg
  have hrw : ((1 / 2 : ℚ) : ℚ_[2]) * ((Φ (cons false c) : ℚ_[2])) + ((0 : ℚ) : ℚ_[2])
      = ((Φ c : ℚ_[2])) := by
    push_cast
    linear_combination (1 / 2 : ℚ_[2]) * hcg
  rw [hrw]; exact hc

/-- `Φ(1c)` is transcendental whenever `Φ(c)` is: `3Φ(1c) = 2Φ(c) − 1`. -/
theorem transcendental_cons_true (h : IsBL Φ) {c : Word}
    (hc : Transcendental ℚ ((Φ c : ℚ_[2]))) :
    Transcendental ℚ ((Φ (cons true c) : ℚ_[2])) := by
  refine transcendental_of_affine (y := ((Φ (cons true c) : ℚ_[2]))) (3 / 2) (1 / 2)
    (by norm_num) ?_
  have h3 : (3 : ℤ_[2]) * Φ (cons true c) = 2 * Φ c - 1 := h.cons_true c
  have hcg : (((3 : ℤ_[2]) * Φ (cons true c) : ℤ_[2]) : ℚ_[2])
      = (((2 : ℤ_[2]) * Φ c - 1 : ℤ_[2]) : ℚ_[2]) := congrArg _ h3
  rw [PadicInt.coe_mul, PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_one,
    coe_two_padicInt, coe_three_padicInt] at hcg
  have hrw : ((3 / 2 : ℚ) : ℚ_[2]) * ((Φ (cons true c) : ℚ_[2])) + ((1 / 2 : ℚ) : ℚ_[2])
      = ((Φ c : ℚ_[2])) := by
    push_cast
    linear_combination (1 / 2 : ℚ_[2]) * hcg
  rw [hrw]; exact hc

/-! ## The unconditional statements for the constructed `Φ` -/

/-- Corollary 1.4 for the constructed Bernstein–Lagarias map, modulo the three axioms. -/
theorem transcendental_PhiBL_charWord {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hirr : Irrational γ) (hγs : γ < gammaStar) :
    Transcendental ℚ ((PhiBL (charWord γ) : ℚ_[2])) :=
  transcendental_charWord isBL_PhiBL hγ0 hγ1 hirr hγs

/-- …and for the two mechanical words at intercept `0`. -/
theorem transcendental_PhiBL_mechanical {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hirr : Irrational γ) (hγs : γ < gammaStar) :
    Transcendental ℚ ((PhiBL (cons true (charWord γ)) : ℚ_[2])) ∧
    Transcendental ℚ ((PhiBL (cons false (charWord γ)) : ℚ_[2])) :=
  ⟨transcendental_cons_true isBL_PhiBL (transcendental_PhiBL_charWord hγ0 hγ1 hirr hγs),
   transcendental_cons_false isBL_PhiBL (transcendental_PhiBL_charWord hγ0 hγ1 hirr hγs)⟩

end Sturmian
