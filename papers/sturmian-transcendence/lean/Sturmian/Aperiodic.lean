/-
# Stage 3, part 2 — `c_γ` is aperiodic for irrational `γ`

Paper, Step 4:

> "If $R_j=\PH(c_\gamma)$ then $\PH(W_j^{\infty})=\PH(c_\gamma)$, so by injectivity
>  (Proposition~\ref{prop:iso}) $c_\gamma=W_j^{\infty}$ would be periodic --- impossible,
>  $\gamma$ being irrational."

This file proves the "impossible" — the only place irrationality of `γ` is used in the
whole development.  The argument is the telescoping count of `Sturmian/Height.lean`: if
`c_γ = w^∞` with `|w| = ℓ` and `k` ones, then counting over `m` periods gives
`⌊(mℓ+1)γ⌋ = mk`, while balance gives `|mk − mℓγ| < 1` for every `m`; letting `m → ∞`
forces `γ = k/ℓ ∈ ℚ`.
-/
import Sturmian.Height

namespace Sturmian

/-- A periodic word is invariant under shifting by a multiple of its period. -/
lemma shiftIter_mul_per (ℓ : ℕ) (W : Word) :
    ∀ m, shiftIter (m * ℓ) (per ℓ W) = per ℓ W := by
  intro m
  induction m with
  | zero => simp
  | succ n ih =>
    have hassoc : (n + 1) * ℓ = n * ℓ + ℓ := by ring
    funext t
    have : shiftIter ((n + 1) * ℓ) (per ℓ W) t = shiftIter (n * ℓ) (per ℓ W) (t + ℓ) := by
      simp only [shiftIter_apply, hassoc]; congr 1; omega
    rw [this, ih]
    simp [per, Nat.add_mod_right]

/-- Counting ones over `m` periods multiplies by `m`. -/
lemma ones_mul_per (ℓ : ℕ) (W : Word) :
    ∀ m, ones (m * ℓ) (per ℓ W) = m * ones ℓ (per ℓ W) := by
  intro m
  induction m with
  | zero => simp
  | succ n ih =>
    have hassoc : (n + 1) * ℓ = n * ℓ + ℓ := by ring
    rw [hassoc, ones_add, ih, shiftIter_mul_per]
    ring

/-- **`c_γ` is aperiodic for irrational `γ`**: it is never a purely periodic word.
This is the paper's Step-4 "impossible, `γ` being irrational". -/
theorem charWord_ne_per {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hirr : Irrational γ)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (W : Word) : charWord γ ≠ per ℓ W := by
  intro hEq
  set k : ℕ := ones ℓ (per ℓ W) with hkdef
  -- counting over `m` periods, two ways
  have hcount : ∀ m : ℕ, ((m * k : ℕ) : ℤ) = ⌊((((m * ℓ : ℕ)) : ℝ) + 1) * γ⌋ := by
    intro m
    have h1 : ones (m * ℓ) (charWord γ) = m * k := by rw [hEq, hkdef]; exact ones_mul_per ℓ W m
    have h2 := ones_charWord hγ0 hγ1 (m * ℓ)
    rw [h1] at h2
    exact h2
  -- balance at every level `mℓ`
  have hbal : ∀ m : ℕ, |((m : ℝ)) * ((k : ℝ)) - ((m : ℝ)) * (ℓ : ℝ) * γ| < 1 := by
    intro m
    have h := abs_ones_charWord_sub_lt_one hγ0 hγ1 (m * ℓ)
    have h1 : ones (m * ℓ) (charWord γ) = m * k := by rw [hEq, hkdef]; exact ones_mul_per ℓ W m
    rw [h1] at h
    have hc : (((m * k : ℕ)) : ℝ) = ((m : ℝ)) * ((k : ℝ)) := by push_cast; ring
    have hc2 : (((m * ℓ : ℕ)) : ℝ) = ((m : ℝ)) * ((ℓ : ℝ)) := by push_cast; ring
    rw [hc, hc2] at h
    calc |((m : ℝ)) * ((k : ℝ)) - ((m : ℝ)) * (ℓ : ℝ) * γ|
        = |((m : ℝ)) * ((k : ℝ)) - ((m : ℝ)) * (ℓ : ℝ) * γ| := rfl
      _ < 1 := by
          have hre : ((m : ℝ)) * ((k : ℝ)) - ((m : ℝ)) * (ℓ : ℝ) * γ
              = ((m : ℝ)) * ((k : ℝ)) - ((m : ℝ)) * ((ℓ : ℝ)) * γ := by ring
          rw [hre]; exact h
  -- hence `k = ℓγ`
  have hzero : ((k : ℝ)) - (ℓ : ℝ) * γ = 0 := by
    by_contra hne
    have habs : 0 < |((k : ℝ)) - (ℓ : ℝ) * γ| := abs_pos.mpr hne
    obtain ⟨m, hm⟩ := exists_nat_gt (1 / |((k : ℝ)) - (ℓ : ℝ) * γ|)
    have hm0 : (0 : ℝ) < (m : ℝ) := by
      have : (0 : ℝ) < 1 / |((k : ℝ)) - (ℓ : ℝ) * γ| := by positivity
      linarith
    have hbm := hbal m
    have hfac : ((m : ℝ)) * ((k : ℝ)) - ((m : ℝ)) * (ℓ : ℝ) * γ
        = ((m : ℝ)) * (((k : ℝ)) - (ℓ : ℝ) * γ) := by ring
    rw [hfac, abs_mul, abs_of_pos hm0] at hbm
    have : 1 < (m : ℝ) * |((k : ℝ)) - (ℓ : ℝ) * γ| := by
      rw [div_lt_iff₀ habs] at hm; linarith
    linarith
  -- so `γ` is the rational `k/ℓ`
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hℓne : ((ℓ : ℝ)) ≠ 0 := ne_of_gt hℓR
  have hkR : (ℓ : ℝ) * γ = (k : ℝ) := by linarith
  have hγq : ((((k : ℚ)) / ((ℓ : ℚ)) : ℚ) : ℝ) = γ := by
    push_cast
    field_simp
    linarith [hkR]
  exact hirr ⟨((k : ℚ)) / ((ℓ : ℚ)), hγq⟩

end Sturmian
