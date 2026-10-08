/-
# Stage 4 — `[DJirr, Lemma 10.4]` formalised; the numerator-bound axiom removed

Source: Elias De Jesús, *The 3x+1 Conjugacy Map Sends Every Sturmian Word to an Irrational
2-adic Integer*, doi:10.5281/zenodo.23108370, 23 pp.  **Lemma 10.4** and its proof,
verbatim from p. 16:

> "What Lemma 10.4 needs is balance of `w^∞`, which is what Theorem 10.3 supplies.
>
>  **Lemma 10.4.** Let `W` be a cyclic permutation of a standard word, `|W| = ℓ`, with
>  `k ≥ 1` ones.  Then `0 < c_W ≤ 3 ℓ max(2^ℓ, 3^k)`.
>
>  *Proof.* Positivity is clear from (2).  By Theorem 10.3 the word `W^∞` is balanced, so
>  `|k_{i+1}(W) − (i+1)k/ℓ| < 1` and hence `k − k_{i+1}(W) < k(ℓ − 1 − i)/ℓ + 1`.  With
>  `ρ = 3^{k/ℓ}`,
>      `3^{k−k_{i+1}(W)} 2^i < 3 ρ^{ℓ−1−i} 2^i ≤ 3 max(ρ^{ℓ−1}, 2^{ℓ−1}) ≤ 3 max(3^k, 2^ℓ)`,
>  the middle step because `i ↦ ρ^{ℓ−1−i} 2^i` is monotone, so its maximum over
>  `0 ≤ i ≤ ℓ−1` is attained at an endpoint.  The sum (2) has at most `ℓ` terms.  □"

**Hypothesis, as the source itself identifies it.**  The sentence immediately before the
lemma says what the proof uses: *balance of `W^∞`*, in the form
`|k_{i+1}(W) − (i+1)k/ℓ| < 1`.  "Cyclic permutation of a standard word" is how the source
*obtains* that (its Theorem 10.3).  So `cw_le_of_balance` below takes the balance bound as
its hypothesis, and `cw_le_prefix` discharges it for prefixes of `c_γ` using
`Sturmian.abs_balance_prefix` — proved, with no appeal to standard words.

**Deviation in method, recorded.**  The source's middle step uses the real power
`ρ = 3^{k/ℓ}` and monotonicity of `i ↦ ρ^{ℓ−1−i}2^i`.  The proof below is the same
inequality rearranged to avoid real exponents: raising to the `ℓ`-th power turns
`3^{a−1}2^i ≤ max(2^ℓ,3^k)` into `3^{(a−1)ℓ}2^{iℓ} ≤ (3^k)^{ℓ−i−1}(2^ℓ)^i ≤ M^{ℓ−1}`,
which is integer arithmetic.  Same statement, same constant `3`.
-/
import Sturmian.Height

namespace Sturmian

/-- One term of `c_W` is at most `3·max(2^ℓ, 3^k)`. -/
lemma term_le_three_mul_max {ℓ i k a : ℕ} (hℓ : 1 ≤ ℓ) (hi : i < ℓ)
    (hkey : ((ℓ : ℤ)) * (((a : ℤ)) - 1) ≤ ((k : ℤ)) * (((ℓ : ℤ)) - ((i : ℤ)) - 1)) :
    ((3 : ℤ)) ^ a * 2 ^ i ≤ 3 * max ((2 : ℤ) ^ ℓ) (3 ^ k) := by
  set M : ℤ := max ((2 : ℤ) ^ ℓ) (3 ^ k) with hMdef
  have hM1 : (1 : ℤ) ≤ M := le_trans (one_le_pow₀ (by norm_num)) (le_max_left _ _)
  have hMpos : (0 : ℤ) < M := lt_of_lt_of_le zero_lt_one hM1
  have h2ℓ : ((2 : ℤ)) ^ ℓ ≤ M := le_max_left _ _
  have h3k : ((3 : ℤ)) ^ k ≤ M := le_max_right _ _
  cases a with
  | zero =>
    have hle : ((2 : ℤ)) ^ i ≤ ((2 : ℤ)) ^ ℓ :=
      pow_le_pow_right₀ (by norm_num) (le_of_lt hi)
    calc ((3 : ℤ)) ^ 0 * 2 ^ i = ((2 : ℤ)) ^ i := by ring
      _ ≤ M := le_trans hle h2ℓ
      _ ≤ 3 * M := by linarith
  | succ b =>
    -- the key exponent inequality, in `ℕ`
    have hib : i + 1 ≤ ℓ := hi
    have hnat : ℓ * b ≤ k * (ℓ - i - 1) := by
      have hZ : ((ℓ : ℤ)) * ((b : ℤ)) ≤ ((k : ℤ)) * (((ℓ : ℤ)) - ((i : ℤ)) - 1) := by
        push_cast at hkey ⊢; linarith
      have hsub : (((ℓ - i - 1 : ℕ)) : ℤ) = ((ℓ : ℤ)) - ((i : ℤ)) - 1 := by
        push_cast [Nat.cast_sub (by omega : i + 1 ≤ ℓ)]; omega
      rw [← Nat.cast_le (α := ℤ)]
      push_cast
      rw [hsub] at *
      linarith [hZ]
    -- raise to the ℓ-th power
    have hpow : (((3 : ℤ)) ^ b * 2 ^ i) ^ ℓ ≤ M ^ ℓ := by
      have e1 : (((3 : ℤ)) ^ b * 2 ^ i) ^ ℓ = ((3 : ℤ)) ^ (b * ℓ) * 2 ^ (i * ℓ) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]
      have e2 : ((3 : ℤ)) ^ (b * ℓ) ≤ ((3 : ℤ)) ^ (k * (ℓ - i - 1)) := by
        refine pow_le_pow_right₀ (by norm_num) ?_
        calc b * ℓ = ℓ * b := by ring
          _ ≤ k * (ℓ - i - 1) := hnat
      have e3 : ((3 : ℤ)) ^ (k * (ℓ - i - 1)) * 2 ^ (i * ℓ)
          = (((3 : ℤ)) ^ k) ^ (ℓ - i - 1) * (((2 : ℤ)) ^ ℓ) ^ i := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        ring
      have e4 : (((3 : ℤ)) ^ k) ^ (ℓ - i - 1) * (((2 : ℤ)) ^ ℓ) ^ i ≤ M ^ (ℓ - i - 1) * M ^ i := by
        refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
        · exact pow_le_pow_left₀ (by positivity) h3k _
        · exact pow_le_pow_left₀ (by positivity) h2ℓ _
      have e5 : M ^ (ℓ - i - 1) * M ^ i = M ^ (ℓ - 1) := by
        rw [← pow_add]
        congr 1
        omega
      have e6 : M ^ (ℓ - 1) ≤ M ^ ℓ := pow_le_pow_right₀ hM1 (by omega)
      calc (((3 : ℤ)) ^ b * 2 ^ i) ^ ℓ = ((3 : ℤ)) ^ (b * ℓ) * 2 ^ (i * ℓ) := e1
        _ ≤ ((3 : ℤ)) ^ (k * (ℓ - i - 1)) * 2 ^ (i * ℓ) := by
            exact mul_le_mul_of_nonneg_right e2 (by positivity)
        _ = (((3 : ℤ)) ^ k) ^ (ℓ - i - 1) * (((2 : ℤ)) ^ ℓ) ^ i := e3
        _ ≤ M ^ (ℓ - i - 1) * M ^ i := e4
        _ = M ^ (ℓ - 1) := e5
        _ ≤ M ^ ℓ := e6
    have hroot : ((3 : ℤ)) ^ b * 2 ^ i ≤ M :=
      le_of_pow_le_pow_left₀ (by omega) (le_of_lt hMpos) hpow
    calc ((3 : ℤ)) ^ (b + 1) * 2 ^ i = 3 * (((3 : ℤ)) ^ b * 2 ^ i) := by ring
      _ ≤ 3 * M := by linarith

/-- **`[DJirr, Lemma 10.4]`**, from the balance hypothesis the source's own proof uses. -/
theorem cw_le_of_balance {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (W : Word)
    (hbal : ∀ m, 1 ≤ m → m ≤ ℓ →
      |((ℓ : ℤ)) * ((ones m W : ℤ)) - ((m : ℤ)) * ((ones ℓ W : ℤ))| < ((ℓ : ℤ))) :
    cw ℓ W ≤ 3 * ((ℓ : ℤ)) * max ((2 : ℤ) ^ ℓ) (3 ^ (ones ℓ W)) := by
  classical
  set k : ℕ := ones ℓ W with hkdef
  set M : ℤ := max ((2 : ℤ) ^ ℓ) (3 ^ k) with hMdef
  have hterm : ∀ i ∈ Finset.range ℓ,
      (if W i then ((3 : ℤ)) ^ (k - ones (i + 1) W) * 2 ^ i else 0) ≤ 3 * M := by
    intro i hi
    have hiℓ : i < ℓ := Finset.mem_range.mp hi
    have hM1 : (1 : ℤ) ≤ M := le_trans (one_le_pow₀ (by norm_num)) (le_max_left _ _)
    by_cases hW : W i = true
    · rw [if_pos hW]
      -- the key exponent inequality from balance at `m = i + 1`
      have hmono : ones (i + 1) W ≤ k := by rw [hkdef]; exact ones_mono (by omega) W
      have hb := hbal (i + 1) (by omega) (by omega)
      rw [abs_lt] at hb
      have hcast : (((k - ones (i + 1) W : ℕ)) : ℤ) = ((k : ℤ)) - ((ones (i + 1) W : ℤ)) := by
        push_cast [Nat.cast_sub hmono]; ring
      have hkey : ((ℓ : ℤ)) * ((((k - ones (i + 1) W : ℕ)) : ℤ) - 1)
          ≤ ((k : ℤ)) * (((ℓ : ℤ)) - ((i : ℤ)) - 1) := by
        rw [hcast]
        have h1 := hb.1
        push_cast at h1 ⊢
        nlinarith [h1]
      exact term_le_three_mul_max hℓ hiℓ hkey
    · rw [if_neg hW]
      linarith [hM1]
  calc cw ℓ W = ∑ i ∈ Finset.range ℓ,
        (if W i then ((3 : ℤ)) ^ (k - ones (i + 1) W) * 2 ^ i else 0) := by rw [cw, hkdef]
    _ ≤ (Finset.range ℓ).card • (3 * M) := Finset.sum_le_card_nsmul _ _ _ hterm
    _ = 3 * ((ℓ : ℤ)) * M := by simp [Finset.card_range]; ring

/-- **The numerator bound for prefixes of `c_γ`** — the axiom
`Sturmian.cw_le_three_mul_len_mul_max` of stage 3, now a theorem.  The balance hypothesis
is discharged by `Sturmian.abs_balance_prefix`. -/
theorem cw_le_prefix {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (ℓ : ℕ) (W : Word)
    (hℓ : 1 ≤ ℓ) (hWchar : ∀ i, i < ℓ → W i = charWord γ i) :
    cw ℓ W ≤ 3 * ((ℓ : ℤ)) * max ((2 : ℤ) ^ ℓ) (3 ^ (ones ℓ W)) := by
  refine cw_le_of_balance hℓ W ?_
  intro m hm1 hmℓ
  have h1 : ones m W = ones m (charWord γ) :=
    ones_congr (fun i hi => hWchar i (lt_of_lt_of_le hi hmℓ))
  have h2 : ones ℓ W = ones ℓ (charWord γ) := ones_congr hWchar
  rw [h1, h2]
  exact abs_balance_prefix hγ0 hγ1 hm1 hmℓ

/-! ## Proposition 2.4, PROVED

The paper's four-line proof, formalised.  **Every input is now proved**: the numerator
bound is `cw_le_prefix` above, and the balance bound, `0 < c_W`, `|δ| < max(2^ℓ,3^k)`,
`H ≤ max(c_W,|δ|)` and the logarithm bookkeeping are all proved in
`Sturmian/Height.lean`. -/

/-- **Proposition 2.4 (height of a shadow).**  Was an axiom at stage 2, a theorem modulo
`[DJirr, Lemma 10.4]` at stage 3, and now **depends on no axiom at all**. -/
theorem shadow_height_bound {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (ℓ : ℕ) (W : Word)
    (hℓ : 2 ≤ ℓ) (hk : 1 ≤ ones ℓ W)
    (hpref : ∀ n : ℕ, (n : ℝ) < 2 * (ℓ : ℝ) → charWord γ n = per ℓ W n) :
    Real.logb 2 (H (shadowRat ℓ W))
      < A γ * (ℓ : ℝ) + Real.logb 2 (3 * (ℓ : ℝ)) + Real.logb 2 3 := by
  have hℓ1 : 1 ≤ ℓ := le_trans (by norm_num) hℓ
  have hℓR : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ1
  set k : ℕ := ones ℓ W with hkdef
  set c : ℤ := cw ℓ W with hcdef
  set d : ℤ := (2 : ℤ) ^ ℓ - 3 ^ k with hddef
  set M : ℤ := max ((2 : ℤ) ^ ℓ) (3 ^ k) with hMdef
  -- `W` agrees with the length-`ℓ` prefix of `c_γ`, so the balance bound applies
  have hWchar : ∀ i, i < ℓ → W i = charWord γ i := by
    intro i hi
    have hiR : (i : ℝ) < 2 * (ℓ : ℝ) := by
      have : (i : ℝ) < (ℓ : ℝ) := by exact_mod_cast hi
      linarith
    rw [← per_apply_of_lt W hi, ← hpref i hiR]
  have hones : k = ones ℓ (charWord γ) := by
    rw [hkdef]; exact ones_congr hWchar
  have hbal : ((k : ℝ)) < (ℓ : ℝ) * γ + 1 := by
    have h := abs_ones_charWord_sub_lt_one hγ0 hγ1 ℓ
    rw [abs_lt] at h
    rw [hones]
    linarith [h.2]
  -- the three size facts
  have hc : 0 < c := by rw [hcdef]; exact cw_pos hk
  have hd : d ≠ 0 := by rw [hddef]; exact den_ne_zero hℓ1
  have hHle : ((H (shadowRat ℓ W) : ℤ)) ≤ max c |d| := by
    rw [shadowRat]; exact H_div_le hc hd
  have hdlt : |d| < M := by rw [hddef, hMdef]; exact abs_den_lt_max hℓ1
  have hcle : c ≤ 3 * (ℓ : ℤ) * M := by
    rw [hcdef, hMdef, hkdef]
    exact cw_le_prefix hγ0 hγ1 ℓ W hℓ1 hWchar
  have hMpos : 0 < M := by
    rw [hMdef]; exact lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have h3ℓ : (1 : ℤ) ≤ 3 * (ℓ : ℤ) := by
    have : (1 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hℓ1
    linarith
  have hmaxle : max c |d| ≤ 3 * (ℓ : ℤ) * M := by
    refine max_le hcle (le_trans (le_of_lt hdlt) ?_)
    nlinarith
  -- pass to the reals and take logs
  have hHR : ((H (shadowRat ℓ W) : ℝ)) ≤ 3 * (ℓ : ℝ) * max ((2 : ℝ) ^ ℓ) ((3 : ℝ) ^ k) := by
    have hstep : ((H (shadowRat ℓ W) : ℤ)) ≤ 3 * (ℓ : ℤ) * M := le_trans hHle hmaxle
    have hcast : ((3 * (ℓ : ℤ) * M : ℤ) : ℝ) = 3 * (ℓ : ℝ) * max ((2 : ℝ) ^ ℓ) ((3 : ℝ) ^ k) := by
      rw [hMdef]; push_cast; ring
    calc ((H (shadowRat ℓ W) : ℝ)) ≤ ((3 * (ℓ : ℤ) * M : ℤ) : ℝ) := by exact_mod_cast hstep
      _ = _ := hcast
  have hHpos : (0 : ℝ) < ((H (shadowRat ℓ W) : ℝ)) := by
    have := H_pos (shadowRat ℓ W); exact_mod_cast this
  have hMRpos : (0 : ℝ) < max ((2 : ℝ) ^ ℓ) ((3 : ℝ) ^ k) :=
    lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hb : (1 : ℝ) < 2 := by norm_num
  calc Real.logb 2 (H (shadowRat ℓ W))
      ≤ Real.logb 2 (3 * (ℓ : ℝ) * max ((2 : ℝ) ^ ℓ) ((3 : ℝ) ^ k)) :=
        Real.logb_le_logb_of_le hb hHpos hHR
    _ = Real.logb 2 (3 * (ℓ : ℝ)) + max (ℓ : ℝ) ((k : ℝ) * Real.logb 2 3) := by
        rw [Real.logb_mul (by positivity) (ne_of_gt hMRpos), logb_max_pow]
    _ < Real.logb 2 (3 * (ℓ : ℝ)) + (A γ * (ℓ : ℝ) + Real.logb 2 3) := by
        have := max_lt_A_mul hγ0 ℓ k hℓ1 hbal; linarith
    _ = A γ * (ℓ : ℝ) + Real.logb 2 (3 * (ℓ : ℝ)) + Real.logb 2 3 := by ring

end Sturmian
