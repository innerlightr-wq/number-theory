/-
# Item 3 of the stage-2 brief — the periodic-shadow formula (Proposition 2.2)

Paper, Proposition 2.2 (`{Periodic shadows; \cite[Theorem 1 and Lemma 12]{LS09}, restated as
\cite[Proposition 4.1]{DJirr}}`), verbatim:

> "Let $w$ be a finite word of length $\ell$ with $k\ge1$ ones. Then $2^{\ell}\ne3^{k}$ and
>  $$\PH(w^{\infty})=\frac{c_w}{2^{\ell}-3^{k}},\qquad
>    c_w=\sum_{i<\ell,\,w_i=1}3^{\,k-k_{i+1}(w)}2^{i}\in\Z_{>0},$$
>  and the denominator is **odd**."

Note that `c_w` is exactly `cw ℓ (w^∞)` in the notation of `Sturmian/Word.lean`, because
`c_m` reads only the first `m` letters (`cw_congr`) and `w^∞` agrees with `w` on `[0,ℓ)`.

Item 5 of the brief — the connection to stage 1 — is `shadowRat_den_odd` and
`shadowRat_injective` at the end of this file.
-/
import Sturmian.BL
import Mathlib.Data.Rat.Lemmas

namespace Sturmian

/-- `w^∞` for a finite word of length `ℓ` presented as `W : ℕ → Bool` read modulo `ℓ`. -/
def per (ℓ : ℕ) (W : Word) : Word := fun n => W (n % ℓ)

lemma per_apply_of_lt {ℓ : ℕ} (W : Word) {i : ℕ} (hi : i < ℓ) : per ℓ W i = W i := by
  simp [per, Nat.mod_eq_of_lt hi]

lemma shiftIter_per {ℓ : ℕ} (W : Word) : shiftIter ℓ (per ℓ W) = per ℓ W := by
  funext n; simp [shiftIter, per, Nat.add_mod_right]

/-- `k_ℓ(w^∞)` is the paper's `k`, the number of ones of `w`. -/
lemma ones_per {ℓ : ℕ} (W : Word) : ones ℓ (per ℓ W) = ones ℓ W :=
  ones_congr fun i hi => per_apply_of_lt W hi

/-- `c_ℓ(w^∞)` is the paper's `c_w`. -/
lemma cw_per {ℓ : ℕ} (W : Word) : cw ℓ (per ℓ W) = cw ℓ W :=
  cw_congr fun i hi => per_apply_of_lt W hi

/-! ## The denominator -/

/-- "Then `2^ℓ ≠ 3^k`": for `ℓ ≥ 1` the left side is even and the right side odd. -/
lemma two_pow_ne_three_pow {ℓ k : ℕ} (hℓ : 1 ≤ ℓ) : (2 : ℤ) ^ ℓ ≠ 3 ^ k := by
  intro hEq
  have h2 : (2 : ℤ) ∣ 2 ^ ℓ := dvd_pow_self 2 (by omega)
  have h3 : ¬ ((2 : ℤ) ∣ 3 ^ k) := by
    have hodd : Odd ((3 : ℤ) ^ k) := Odd.pow (by decide)
    obtain ⟨c, hc⟩ := hodd
    intro hd
    obtain ⟨e, he⟩ := hd
    omega
  exact h3 (hEq ▸ h2)

/-- "and the denominator is **odd**". -/
lemma den_odd {ℓ k : ℕ} (hℓ : 1 ≤ ℓ) : Odd ((2 : ℤ) ^ ℓ - 3 ^ k) := by
  have h2 : (2 : ℤ) ∣ 2 ^ ℓ := dvd_pow_self 2 (by omega)
  obtain ⟨a, ha⟩ := h2
  have h3 : Odd ((3 : ℤ) ^ k) := Odd.pow (by decide)
  obtain ⟨b, hb⟩ := h3
  exact ⟨a - b - 1, by rw [ha, hb]; ring⟩

lemma den_ne_zero {ℓ k : ℕ} (hℓ : 1 ≤ ℓ) : ((2 : ℤ) ^ ℓ - 3 ^ k) ≠ 0 :=
  sub_ne_zero.mpr (two_pow_ne_three_pow hℓ)

/-- "`c_w ∈ ℤ_{>0}`": every term is positive and there is at least one, since `k ≥ 1`. -/
lemma cw_pos {ℓ : ℕ} {v : Word} (hk : 1 ≤ ones ℓ v) : 0 < cw ℓ v := by
  classical
  have hterm : ∀ i ∈ Finset.range ℓ,
      (0 : ℤ) ≤ (if v i then (3 : ℤ) ^ (ones ℓ v - ones (i + 1) v) * 2 ^ i else 0) := by
    intro i _
    by_cases hv : v i = true
    · simp only [hv, if_true]; positivity
    · simp only [hv, Bool.false_eq_true, if_false]; exact le_refl 0
  -- some index carries a one
  have hnonempty : ((Finset.range ℓ).filter (fun i => v i = true)).Nonempty := by
    rw [← Finset.card_pos]
    unfold ones at hk
    omega
  obtain ⟨j, hjf⟩ := hnonempty
  rw [Finset.mem_filter] at hjf
  obtain ⟨hjmem, hjv⟩ := hjf
  have hjpos : (0 : ℤ) < (if v j then (3 : ℤ) ^ (ones ℓ v - ones (j + 1) v) * 2 ^ j else 0) := by
    simp only [hjv, if_true]; positivity
  calc (0 : ℤ) < (if v j then (3 : ℤ) ^ (ones ℓ v - ones (j + 1) v) * 2 ^ j else 0) := hjpos
    _ ≤ cw ℓ v := Finset.single_le_sum hterm hjmem

/-! ## Proposition 2.2 -/

variable {Φ : Word → ℤ_[2]}

/-- The algebraic core of Proposition 2.2, in `ℤ_[2]`:
`(2^ℓ − 3^k) · Φ(w^∞) = c_w`.  This is eq. (3) at `m = ℓ`, using `σ^ℓ(w^∞) = w^∞`. -/
theorem shadow_eq (h : IsBL Φ) (ℓ : ℕ) (W : Word) :
    (((2 : ℤ) ^ ℓ - 3 ^ (ones ℓ W) : ℤ) : ℤ_[2]) * Φ (per ℓ W)
      = ((cw ℓ W : ℤ) : ℤ_[2]) := by
  have key := h.affinegen (per ℓ W) ℓ
  rw [shiftIter_per, ones_per, cw_per] at key
  push_cast
  linear_combination key

/-- `Φ(w^∞)` as an explicit rational: the paper's `c_w / (2^ℓ − 3^k)`. -/
noncomputable def shadowRat (ℓ : ℕ) (W : Word) : ℚ :=
  (cw ℓ W : ℚ) / (((2 : ℤ) ^ ℓ - 3 ^ (ones ℓ W) : ℤ) : ℚ)

/-- **Proposition 2.2.**  `Φ(w^∞) = c_w / (2^ℓ − 3^k)`, as an identity in `ℚ_[2]`. -/
theorem shadow_formula (h : IsBL Φ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (W : Word) :
    ((Φ (per ℓ W) : ℚ_[2])) = ((shadowRat ℓ W : ℚ) : ℚ_[2]) := by
  have hd : ((2 : ℤ) ^ ℓ - 3 ^ (ones ℓ W) : ℤ) ≠ 0 := den_ne_zero hℓ
  have hdP : ((((2 : ℤ) ^ ℓ - 3 ^ (ones ℓ W) : ℤ) : ℚ_[2])) ≠ 0 := Int.cast_ne_zero.mpr hd
  have key := shadow_eq h ℓ W
  have keyQ : ((((2 : ℤ) ^ ℓ - 3 ^ (ones ℓ W) : ℤ) : ℚ_[2])) * ((Φ (per ℓ W) : ℚ_[2]))
      = (((cw ℓ W : ℤ) : ℚ_[2])) := by
    have hc := congrArg (fun z : ℤ_[2] => (z : ℚ_[2])) key
    simp only [PadicInt.coe_mul, PadicInt.coe_intCast] at hc
    exact hc
  rw [shadowRat, Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast, eq_div_iff hdP]
  linear_combination keyQ

/-- **The denominator is odd** — the last clause of Proposition 2.2, and exactly the
hypothesis `Sturmian.not_approxExp_of_rat` and `Sturmian.ne_rat_of_ApproxExp` consume. -/
theorem shadowRat_den_odd {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (W : Word) : Odd (shadowRat ℓ W).den := by
  have hdvd := Rat.den_dvd (cw ℓ W) (((2 : ℤ) ^ ℓ - 3 ^ (ones ℓ W) : ℤ))
  rw [Rat.divInt_eq_div] at hdvd
  have hden : ((shadowRat ℓ W).den : ℤ) ∣ ((2 : ℤ) ^ ℓ - 3 ^ (ones ℓ W) : ℤ) := by
    rw [shadowRat]; exact hdvd
  rw [Nat.odd_iff]
  by_contra hev
  have h2nat : 2 ∣ (shadowRat ℓ W).den := by omega
  have h2 : (2 : ℤ) ∣ ((shadowRat ℓ W).den : ℤ) := by
    exact_mod_cast Int.natCast_dvd_natCast.mpr h2nat
  have hbad : (2 : ℤ) ∣ ((2 : ℤ) ^ ℓ - 3 ^ (ones ℓ W) : ℤ) := dvd_trans h2 hden
  obtain ⟨c, hc⟩ := den_odd (k := ones ℓ W) hℓ
  obtain ⟨e, he⟩ := hbad
  omega

/-! ## Item 5 — the connection to stage 1

Paper, Step 4: "$R_j$ determines $W_j^{\infty}$ by injectivity … the $R_j$ take infinitely
many distinct values."  Here: distinct periodic words give distinct shadow rationals. -/

/-- Distinct periodic words have distinct shadow rationals.  This is the paper's Step 4
mechanism: the shadow determines `Φ(w^∞)`, which determines `w^∞` because `Φ` is injective
(Proposition 2.1). -/
theorem shadowRat_inj_of_word_ne (h : IsBL Φ) {ℓ₁ ℓ₂ : ℕ} (h₁ : 1 ≤ ℓ₁) (h₂ : 1 ≤ ℓ₂)
    {W₁ W₂ : Word} (hne : per ℓ₁ W₁ ≠ per ℓ₂ W₂) :
    shadowRat ℓ₁ W₁ ≠ shadowRat ℓ₂ W₂ := by
  intro hEq
  have e1 := shadow_formula h h₁ W₁
  have e2 := shadow_formula h h₂ W₂
  have : ((Φ (per ℓ₁ W₁) : ℚ_[2])) = ((Φ (per ℓ₂ W₂) : ℚ_[2])) := by
    rw [e1, e2, hEq]
  have hz : Φ (per ℓ₁ W₁) = Φ (per ℓ₂ W₂) := PadicInt.ext this
  exact hne (h.injective hz)

/-- The set of shadows of an injective family of periodic words is infinite, with odd
denominators — precisely what `Sturmian.transcendental_of_approxExp` and
`Sturmian.ne_rat_of_ApproxExp` consume. -/
theorem shadowSet_infinite (h : IsBL Φ) {ℓ : ℕ → ℕ} {W : ℕ → Word}
    (hℓ : ∀ j, 1 ≤ ℓ j) (hinj : Function.Injective fun j => per (ℓ j) (W j)) :
    (Set.range fun j => shadowRat (ℓ j) (W j)).Infinite := by
  apply Set.infinite_range_of_injective
  intro i j hij
  by_contra hne
  exact shadowRat_inj_of_word_ne h (hℓ i) (hℓ j) (fun hw => hne (hinj hw)) hij

end Sturmian
