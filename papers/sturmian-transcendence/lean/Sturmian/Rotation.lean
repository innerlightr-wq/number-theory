/-
# Stage 5, Step 2 — the periodicity lemma for `c_γ`

The engine of the lower bound on `ice(c_γ)`.  Paper, Proposition 2.6 (`\cite[\S4.2]{BHZ06}`)
asserts `ice(c_α) = 1 + limsup q_{k+1}/q_k`; the direction we need is the lower bound, and
it comes from a periodicity statement about prefixes of `c_γ`.

**No continued fractions are used.**  The hypothesis is stated directly in terms of the
rotation: if no index below `Q` approximates `γ` better than `q` does, then `c_γ` is
`q`-periodic on its first `Q + q − 2` letters.  Specialising `Q` to the next
best-approximation denominator recovers the paper's `q_{n+1} + q_n − 2`, which is what the
Step-1 numerics confirmed exactly (0 mismatches on every irrational slope tested).

The proof is a floor computation.  `c_γ(m) = ⌊(m+1)γ⌋ − ⌊mγ⌋` changes under `m ↦ m + q`
only if adding `qγ` moves one of two points across an integer; and `qγ` is within
`‖qγ‖` of an integer, which by hypothesis no index below `Q` can manage.
-/
import Sturmian.Word
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Sturmian

/-! ## Distance to the nearest integer

`nrmR x` is the distance from a real `x` to the nearest integer; `off γ q` is the signed
displacement of `qγ` from its nearest integer, and `nrm γ q = |off γ q| = ‖qγ‖`. -/

/-- Distance from a real to the nearest integer. -/
noncomputable def nrmR (x : ℝ) : ℝ := |x - (round x : ℝ)|

/-- The signed displacement of `qγ` from its nearest integer. -/
noncomputable def off (γ : ℝ) (q : ℕ) : ℝ :=
  ((q : ℝ)) * γ - (round (((q : ℝ)) * γ) : ℝ)

/-- `‖qγ‖`, the distance from `qγ` to the nearest integer. -/
noncomputable def nrm (γ : ℝ) (q : ℕ) : ℝ := |off γ q|

lemma nrm_eq_nrmR (γ : ℝ) (q : ℕ) : nrm γ q = nrmR (((q : ℝ)) * γ) := rfl

lemma nrm_nonneg (γ : ℝ) (j : ℕ) : 0 ≤ nrm γ j := abs_nonneg _

lemma nrm_le_half (γ : ℝ) (j : ℕ) : nrm γ j ≤ 1 / 2 := abs_sub_round _

lemma nrm_eq_min (γ : ℝ) (j : ℕ) :
    nrm γ j = min (Int.fract (((j : ℝ)) * γ)) (1 - Int.fract (((j : ℝ)) * γ)) :=
  abs_sub_round_eq_min _

lemma nrm_le_fract (γ : ℝ) (j : ℕ) : nrm γ j ≤ Int.fract (((j : ℝ)) * γ) := by
  rw [nrm_eq_min]; exact min_le_left _ _

lemma nrm_le_one_sub_fract (γ : ℝ) (j : ℕ) :
    nrm γ j ≤ 1 - Int.fract (((j : ℝ)) * γ) := by
  rw [nrm_eq_min]; exact min_le_right _ _

lemma exists_int_off (γ : ℝ) (q : ℕ) : ∃ p : ℤ, ((q : ℝ)) * γ = (p : ℝ) + off γ q :=
  ⟨round (((q : ℝ)) * γ), by rw [off]; ring⟩

lemma abs_off (γ : ℝ) (q : ℕ) : |off γ q| = nrm γ q := rfl

lemma off_le_nrm (γ : ℝ) (q : ℕ) : off γ q ≤ nrm γ q := le_abs_self _

lemma neg_nrm_le_off (γ : ℝ) (q : ℕ) : -nrm γ q ≤ off γ q := neg_abs_le _

/-! ## Irrationality: no nonzero multiple of `γ` is an integer -/

lemma mul_ne_int {γ : ℝ} (hirr : Irrational γ) {k : ℕ} (hk : 1 ≤ k) (z : ℤ) :
    (k : ℝ) * γ ≠ (z : ℝ) :=
  Irrational.ne_int (hirr.natCast_mul (by omega)) z

/-! ## The periodicity lemma -/

/-- Adding `off γ q` does not move `jγ` across an integer, for `1 ≤ j < Q`. -/
lemma floor_add_off {γ : ℝ} (hirr : Irrational γ) {q Q : ℕ} (hq : 1 ≤ q)
    (hmin : ∀ j, 1 ≤ j → j < Q → nrm γ q ≤ nrm γ j)
    {j : ℕ} (hj1 : 1 ≤ j) (hjQ : j < Q) :
    ⌊((j : ℝ)) * γ + off γ q⌋ = ⌊((j : ℝ)) * γ⌋ := by
  obtain ⟨p, hp⟩ := exists_int_off γ q
  set x : ℝ := ((j : ℝ)) * γ with hxdef
  set F : ℝ := Int.fract x with hFdef
  have hF : ((⌊x⌋ : ℤ) : ℝ) + F = x := Int.floor_add_fract x
  have hnj : nrm γ q ≤ nrm γ j := hmin j hj1 hjQ
  have hFlow : nrm γ q ≤ F := le_trans hnj (nrm_le_fract γ j)
  have hFhigh : nrm γ q ≤ 1 - F := le_trans hnj (nrm_le_one_sub_fract γ j)
  have hoffhi := off_le_nrm γ q
  have hofflo := neg_nrm_le_off γ q
  rw [Int.floor_eq_iff]
  refine ⟨by linarith, ?_⟩
  -- the upper bound is strict: equality would make `(j+q)γ` an integer
  have hne : F + off γ q ≠ 1 := by
    intro hEq
    have hsum : (((j + q : ℕ)) : ℝ) * γ = ((⌊x⌋ + 1 + p : ℤ) : ℝ) := by
      push_cast
      have hxq : ((q : ℝ)) * γ = (p : ℝ) + off γ q := hp
      push_cast at hF
      nlinarith [hF, hEq, hxq]
    exact mul_ne_int hirr (by omega) _ hsum
  have hle : F + off γ q ≤ 1 := by linarith
  have : F + off γ q < 1 := lt_of_le_of_ne hle hne
  linarith

/-- **The periodicity lemma.**  If no index `j` with `1 ≤ j < Q` approximates `γ` strictly
better than `q` does, then the letters of `c_γ` satisfy `c(m+q) = c(m)` for every
`m + 2 < Q`. -/
theorem charWord_add_eq {γ : ℝ} (hirr : Irrational γ) {q Q : ℕ} (hq : 1 ≤ q)
    (hmin : ∀ j, 1 ≤ j → j < Q → nrm γ q ≤ nrm γ j) :
    ∀ m : ℕ, m + 2 < Q → charWord γ (m + q) = charWord γ m := by
  intro m hm
  obtain ⟨p, hp⟩ := exists_int_off γ q
  have shift : ∀ j : ℕ, 1 ≤ j → j < Q →
      ⌊((((j + q : ℕ)) : ℝ)) * γ⌋ = ⌊((j : ℝ)) * γ⌋ + p := by
    intro j hj1 hjQ
    have hrw : ((((j + q : ℕ)) : ℝ)) * γ = (((j : ℝ)) * γ + off γ q) + (p : ℝ) := by
      push_cast
      nlinarith [hp]
    rw [hrw, Int.floor_add_intCast, floor_add_off hirr hq hmin hj1 hjQ]
  have e2 : ((m + q : ℕ) : ℝ) + 2 = (((m + 2 : ℕ) + q : ℕ) : ℝ) := by push_cast; ring
  have e1 : ((m + q : ℕ) : ℝ) + 1 = (((m + 1 : ℕ) + q : ℕ) : ℝ) := by push_cast; ring
  have d2 : ((m : ℝ) + 2) = (((m + 2 : ℕ)) : ℝ) := by push_cast; ring
  have d1 : ((m : ℝ) + 1) = (((m + 1 : ℕ)) : ℝ) := by push_cast; ring
  rw [charWord, charWord, e1, e2, shift (m + 2) (by omega) (by omega),
    shift (m + 1) (by omega) (by omega), d1, d2]
  simp only [add_sub_add_right_eq_sub]

/-- The prefix of `c_γ` of length `Q + q − 2` has period `q`. -/
theorem per_eq_of_min {γ : ℝ} (hirr : Irrational γ) {q Q : ℕ} (hq : 1 ≤ q) (hQ : 2 ≤ Q)
    (hmin : ∀ j, 1 ≤ j → j < Q → nrm γ q ≤ nrm γ j) :
    ∀ m : ℕ, m < Q + q - 2 → charWord γ m = per q (charWord γ) m := by
  have hstep : ∀ m : ℕ, m + 2 < Q → charWord γ (m + q) = charWord γ m :=
    charWord_add_eq hirr hq hmin
  -- induct on `m`, reducing by `q` until below `q`
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hmlt
    by_cases hmq : m < q
    · rw [per_apply_of_lt _ hmq]
    · have hmq' : q ≤ m := by omega
      obtain ⟨t, ht⟩ : ∃ t, m = t + q := ⟨m - q, by omega⟩
      have ht2 : t + 2 < Q := by omega
      have htlt : t < Q + q - 2 := by omega
      have htm : t < m := by omega
      rw [ht, hstep t ht2, ih t htm htlt]
      simp [per, Nat.add_mod_right]

end Sturmian
