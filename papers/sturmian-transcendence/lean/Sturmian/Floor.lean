/-
# Stage 5, Tier B — the floor `ice(c_γ) ≥ 1 + φ`, PROVED

This file replaces the axiom `bhz_ice_floor`, which no longer exists.

Paper, Proposition 2.8 (`{Floor; \cite[\S4.2]{BHZ06}}`), verbatim:

> For every irrational $\gamma$,
> $$\ice(c_\gamma)\;\ge\;1+\varphi=\varphi^{2}=\frac{3+\sqrt5}{2}=2.6180339887\ldots,$$
> with equality if and only if $a_k=1$ for all large $k$.

`one_add_phi_le_ice` is the inequality.  (The equality clause is not formalised and is not
used anywhere.)

**Attribution.**  The constant `1 + φ` is due to Valérie Berthé, Charles Holton and
Luca Q. Zamboni, *Initial powers of Sturmian sequences*, Acta Arith. **122** (2006),
315–347, §4.2.  The proof here is independent of their paper — it uses Dirichlet's theorem
and the record machinery of `Sturmian/Records.lean`, nothing else — but **no novelty is
claimed**: this is a formalisation of a known result by a route convenient for Lean, not a
new theorem.

The mathematical content is `Sturmian.one_add_phi_le_max`: for `x > 0`,
`max(x + 1, 2 + 1/x) ≥ 1 + φ`, sharp at `x = φ`.  Its quantitative form over records is
`Sturmian.exists_long_period_eps`, and this file turns that into a statement about the
limit superior.
-/
import Sturmian.Records
import Sturmian.Ice
import Sturmian.Aperiodic

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

/-! ## The floor -/

/-- Every real strictly below `1 + φ` is a lower bound for `ice(c_γ)`. -/
theorem le_ice_of_lt_one_add_phi {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hirr : Irrational γ)
    {c : ℝ} (hc : c < 1 + phi) : ENNReal.ofReal c ≤ ice (charWord γ) := by
  by_cases h0 : 0 < c
  · refine le_limsup_of_frequently_le ?_
    rw [frequently_atTop]
    intro N
    obtain ⟨q, L, hqN, hq2, hcL, hagr⟩ :=
      exists_long_period_eps hirr N (ε := 1 + phi - c) (by linarith)
    refine ⟨q, hqN, le_prefixPower (by omega)
      (charWord_ne_per hγ0 hγ1 hirr (by omega) (charWord γ)) hagr (le_of_lt h0) ?_⟩
    linarith [hcL]
  · push_neg at h0
    rw [ENNReal.ofReal_eq_zero.mpr h0]
    simp

/-- **The paper's Proposition 2.8, proved.**  `ice(c_γ) ≥ 1 + φ` for every irrational
`γ ∈ (0,1)`.  Formerly the axiom `bhz_ice_floor`; the constant is
Berthé–Holton–Zamboni's, the proof is independent of their paper, and no novelty is
claimed for the result. -/
theorem one_add_phi_le_ice {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hirr : Irrational γ) :
    ENNReal.ofReal (1 + phi) ≤ ice (charWord γ) := by
  by_contra hcon
  push_neg at hcon
  have htop : ice (charWord γ) ≠ ⊤ := ne_top_of_lt hcon
  set t : ℝ := (ice (charWord γ)).toReal with ht
  have hte : ice (charWord γ) = ENNReal.ofReal t := (ENNReal.ofReal_toReal htop).symm
  have htnn : 0 ≤ t := ENNReal.toReal_nonneg
  have htlt : t < 1 + phi := by
    rw [hte] at hcon
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg htnn).mp hcon
  have h := le_ice_of_lt_one_add_phi hγ0 hγ1 hirr
    (show (t + (1 + phi)) / 2 < 1 + phi by linarith)
  rw [hte] at h
  have hle := (ENNReal.ofReal_le_ofReal_iff htnn).mp h
  linarith

/-! ## Two consequences used elsewhere -/

/-- `ice(c_γ) ≥ 12/5`: the weaker constant, which is all the headline slope needs. -/
theorem twelve_fifths_le_ice {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hirr : Irrational γ) :
    ENNReal.ofReal (12 / 5) ≤ ice (charWord γ) :=
  le_ice_of_lt_one_add_phi hγ0 hγ1 hirr (by linarith [eight_fifths_lt_phi_aux])

/-- **The paper's `ice(c_γ) > 2`**, for every irrational `γ ∈ (0,1)`. -/
theorem two_lt_ice {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hirr : Irrational γ) :
    2 < ice (charWord γ) := by
  refine lt_of_lt_of_le ?_ (twelve_fifths_le_ice hγ0 hγ1 hirr)
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).mpr (by norm_num)

end Sturmian
