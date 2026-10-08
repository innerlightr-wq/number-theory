/-
# Stage 1 — the logical skeleton

Items 2, 3 (conclusion), 4, 5 and 6 of the stage-1 brief.  The only axiom used is
`Sturmian.ridout_single_prime` (Axiom R); everything else is proved.
-/
import Sturmian.Axioms
import Sturmian.Liouville
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Sturmian

open Filter

/-! ## Choosing a strictly height-increasing family out of an infinite set -/

/-- From an infinite set of rationals, a sequence with strictly increasing heights,
the first of height at least `2`.  (Paper, Step 4: "Passing to a subsequence they are
pairwise distinct with $H(R_j)\to\infty$, only finitely many rationals having bounded
height. In particular no shadow has $H=1$, where \eqref{eq:omdef} would be vacuous.") -/
noncomputable def pick {S : Set ℚ} (hS : S.Infinite) : ℕ → ℚ
  | 0 => (exists_H_gt_of_infinite hS 1).choose
  | (n + 1) => (exists_H_gt_of_infinite hS (H (pick hS n))).choose

lemma pick_mem {S : Set ℚ} (hS : S.Infinite) : ∀ n, pick hS n ∈ S
  | 0 => (exists_H_gt_of_infinite hS 1).choose_spec.1
  | (n + 1) => (exists_H_gt_of_infinite hS (H (pick hS n))).choose_spec.1

lemma two_le_H_pick_zero {S : Set ℚ} (hS : S.Infinite) : 2 ≤ H (pick hS 0) :=
  (exists_H_gt_of_infinite hS 1).choose_spec.2

lemma H_pick_lt_succ {S : Set ℚ} (hS : S.Infinite) (n : ℕ) :
    H (pick hS n) < H (pick hS (n + 1)) :=
  (exists_H_gt_of_infinite hS (H (pick hS n))).choose_spec.2

lemma strictMono_H_pick {S : Set ℚ} (hS : S.Infinite) :
    StrictMono fun n => H (pick hS n) :=
  strictMono_nat_of_lt_succ (H_pick_lt_succ hS)

lemma two_le_H_pick {S : Set ℚ} (hS : S.Infinite) (n : ℕ) : 2 ≤ H (pick hS n) :=
  le_trans (two_le_H_pick_zero hS) ((strictMono_H_pick hS).monotone (Nat.zero_le n))

/-! ## Item 2 — the approximation lemma

Paper, Step 5: "By Steps 3 and 4 we have infinitely many pairwise distinct rationals
$R_j$, of strictly increasing height after passing to a subsequence, with odd
denominators, satisfying $|\PH(c_\gamma)-R_j|_2\le H(R_j)^{-(1+w_j)}$ and $w_j>1$.
… Choosing $\varepsilon>0$ with $1+w_j>2+\varepsilon$ for large $j$, Theorem R applies
and $\PH(c_\gamma)$ is *not* an algebraic irrational." -/

/-- At most one rational maps to a given element of `ℚ_[p]`. -/
lemma subsingleton_preimage {p : ℕ} [Fact p.Prime] (ξ : ℚ_[p]) :
    {q : ℚ | (q : ℚ_[p]) = ξ}.Subsingleton := by
  intro a ha b hb
  exact (Rat.cast_injective (α := ℚ_[p])) (by simpa [Set.mem_ofPred_eq] using ha.trans hb.symm)

/-- **Item 2.**  If `ξ` admits infinitely many *distinct* rationals approximating it to a
fixed exponent `μ > 2`, then `ξ` is transcendental over `ℚ` — in particular it is not an
algebraic irrational.  Odd denominators are carried through but not used here; they are
what the paper's Theorem R application and the Liouville inequality need. -/
theorem transcendental_of_approxExp {p : ℕ} [Fact p.Prime] {ξ : ℚ_[p]} {μ : ℝ} (hμ : 2 < μ)
    (S : Set ℚ) (hS : S.Infinite)
    (happ : ∀ r ∈ S, ‖ξ - (r : ℚ_[p])‖ ≤ (H r : ℝ) ^ (-μ)) :
    Transcendental ℚ ξ := by
  classical
  -- discard the at most one rational equal to ξ
  set T : Set ℚ := S \ {q : ℚ | (q : ℚ_[p]) = ξ} with hT
  have hTinf : T.Infinite := hS.sdiff ((subsingleton_preimage ξ).finite)
  set x : ℕ → ℚ := pick hTinf with hx
  have hxS : ∀ n, x n ∈ S := fun n => ((pick_mem hTinf n).1)
  have hxne : ∀ n, ((x n : ℚ) : ℚ_[p]) ≠ ξ := fun n => ((pick_mem hTinf n).2)
  have h2 : ∀ n, 2 ≤ H (x n) := two_le_H_pick hTinf
  have hH1 : ∀ n, (1 : ℝ) < (H (x n) : ℝ) := fun n => by
    have := h2 n; exact_mod_cast lt_of_lt_of_le one_lt_two (by exact_mod_cast this)
  -- the Ridout exponent
  set ε : ℝ := (μ - 2) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hlt2 : -μ < -2 - ε := by rw [hε]; linarith
  refine ridout_single_prime ξ ε hεpos x (h2 0) (strictMono_H_pick hTinf) ?_ ?_
  · intro n
    have : ξ - ((x n : ℚ) : ℚ_[p]) ≠ 0 := sub_ne_zero.mpr (fun h => hxne n h.symm)
    exact norm_pos_iff.mpr this
  · intro n
    calc ‖ξ - ((x n : ℚ) : ℚ_[p])‖ ≤ (H (x n) : ℝ) ^ (-μ) := happ _ (hxS n)
      _ < (H (x n) : ℝ) ^ (-2 - ε) :=
          Real.rpow_lt_rpow_left_iff (hH1 n) |>.mpr hlt2

/-! ## Item 3 (conclusion) — irrationality needs no extra input in the skeleton

With the Liouville inequality of `Sturmian/Liouville.lean`, the hypothesis of item 2
already forces irrationality at exponent `μ > 1`.  So the skeleton does not appeal to the
paper's Proposition 2.10. -/

/-- **Item 3, conclusion.**  No rational with odd denominator admits infinitely many
*distinct* rational approximants of odd denominator at any exponent `μ > 1`. -/
theorem not_approxExp_of_rat {q : ℚ} (hq : Odd q.den) {μ : ℝ} (hμ : 1 < μ)
    (S : Set ℚ) (hS : S.Infinite) (hodd : ∀ r ∈ S, Odd r.den)
    (happ : ∀ r ∈ S, ‖((q : ℚ) : ℚ_[2]) - (r : ℚ_[2])‖ ≤ (H r : ℝ) ^ (-μ)) : False := by
  classical
  set C : ℝ := (|q.num| : ℝ) + (q.den : ℝ) with hC
  have hCpos : 0 < C := by
    have h1 : (0 : ℝ) ≤ (|q.num| : ℝ) := by positivity
    have h2 : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.pos
    rw [hC]; linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (C ^ (1 / (μ - 1)))
  obtain ⟨r, hrS, hrH⟩ := exists_H_gt_of_infinite (hS.sdiff (Set.finite_singleton q)) (max N 1)
  have hrne : r ≠ q := fun h => hrS.2 (by simp [h])
  have hrmem : r ∈ S := hrS.1
  have hlow : 1 / (C * (H r : ℝ)) ≤ ‖((q : ℚ) : ℚ_[2]) - (r : ℚ_[2])‖ := by
    rw [hC]; exact liouville_two_adic_real hq (hodd r hrmem) (Ne.symm hrne)
  have hup := happ r hrmem
  have hHpos : (0 : ℝ) < (H r : ℝ) := by exact_mod_cast H_pos r
  have hH1 : (1 : ℝ) < (H r : ℝ) := by
    have : 1 < H r := lt_of_le_of_lt (le_max_right N 1) hrH
    exact_mod_cast this
  have hpowpos : (0 : ℝ) < (H r : ℝ) ^ μ := Real.rpow_pos_of_pos hHpos μ
  have hCH : (0 : ℝ) < C * (H r : ℝ) := by positivity
  have hrpow : (H r : ℝ) ^ (-μ) = ((H r : ℝ) ^ μ)⁻¹ := Real.rpow_neg (le_of_lt hHpos) μ
  have hchain : (C * (H r : ℝ))⁻¹ ≤ ((H r : ℝ) ^ μ)⁻¹ := by
    rw [← one_div, ← hrpow]; exact le_trans hlow hup
  have hmul : (H r : ℝ) ^ μ ≤ C * (H r : ℝ) := (inv_le_inv₀ hCH hpowpos).mp hchain
  have hsplit : (H r : ℝ) ^ μ = (H r : ℝ) * (H r : ℝ) ^ (μ - 1) := by
    have h := Real.rpow_one_add' (le_of_lt hHpos) (by linarith : (1 : ℝ) + (μ - 1) ≠ 0)
    rwa [show (1 : ℝ) + (μ - 1) = μ by ring] at h
  have hle : (H r : ℝ) ^ (μ - 1) ≤ C := by
    rw [hsplit] at hmul
    refine le_of_mul_le_mul_left ?_ hHpos
    calc (H r : ℝ) * (H r : ℝ) ^ (μ - 1) ≤ C * (H r : ℝ) := hmul
      _ = (H r : ℝ) * C := by ring
  have hgt : C < (H r : ℝ) ^ (μ - 1) := by
    have hNle : (N : ℝ) ≤ (H r : ℝ) := by
      have : N ≤ H r := le_trans (le_max_left N 1) (le_of_lt hrH)
      exact_mod_cast this
    have hbase : C ^ (1 / (μ - 1)) < (H r : ℝ) := lt_of_lt_of_le hN hNle
    have hz : (0 : ℝ) < μ - 1 := by linarith
    have hstep := Real.rpow_lt_rpow (Real.rpow_nonneg (le_of_lt hCpos) _) hbase hz
    rwa [← Real.rpow_mul (le_of_lt hCpos), one_div_mul_cancel (ne_of_gt hz),
      Real.rpow_one] at hstep
  linarith

/-! ## Item 5 — the arithmetic of Corollary 1.4

Paper, §1.2: `\Av:=\max(1,\gamma\log_2 3)`, `\gs:=\frac{1+\varphi}{2\log_2 3}`,
`\varphi=(1+\sqrt5)/2`; and the proof of Corollary 1.4 (paper, §3):
"$\Av=\max(1,\gamma\log_2 3)<(1+\varphi)/2$, i.e. $2\Av<1+\varphi\le\ice(c_\gamma)$". -/

lemma one_lt_phi : 1 < phi := by
  have h : (1 : ℝ) < Real.sqrt 5 := by
    have : (1 : ℝ) = Real.sqrt 1 := by simp
    rw [this]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [phi]; linarith

lemma log2three_pos : 0 < log2three := by
  rw [log2three]
  apply div_pos
  · exact Real.log_pos (by norm_num)
  · exact Real.log_pos (by norm_num)

/-- **Item 5.**  `γ < γ*` implies `2 A(γ) < 1 + φ`.  Both cases of the `max` are needed:
below `γ log₂ 3 = 1` the bound is `2 < 1 + φ`, which holds because `φ > 1`; above it the
bound is exactly the definition of `γ*`. -/
theorem two_A_lt_one_add_phi {γ : ℝ} (hγ : γ < gammaStar) : 2 * A γ < 1 + phi := by
  have hlog := log2three_pos
  have hφ := one_lt_phi
  have hc : (0 : ℝ) < 2 * log2three := by positivity
  simp only [gammaStar] at hγ
  have h1 : γ * (2 * log2three) < 1 + phi := by
    have h := mul_lt_mul_of_pos_right hγ hc
    rwa [div_mul_cancel₀ _ (ne_of_gt hc)] at h
  simp only [A]
  rcases max_cases (1 : ℝ) (γ * log2three) with ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [heq]; linarith
  · rw [heq]
    have hring : 2 * (γ * log2three) = γ * (2 * log2three) := by ring
    linarith

/-! ## Item 6 — exponent bookkeeping, with the paper's exact error terms

Paper, Step 2 eq. (`eq:depth`): `\lcp(c_\gamma,W_j^{\infty})\ge e\,\ell_j`, and the paper
notes explicitly "the relation \eqref{eq:depth} involves no floor and no $O(1)$ loss".
Paper, Step 2 eq. (`eq:hbound`):
`\log_2 H(R_j) < \Av\,\ell_j+\log_2(3\ell_j)+\log_2 3`.
Paper, Step 3 eq. (`eq:wj`):
`1+w_j=\frac{e\,\ell_j}{\log_2 H(R_j)} > \frac{e\,\ell_j}{\Av\,\ell_j+\log_2(3\ell_j)+\log_2 3}`.

NOTE ON THE BRIEF.  The brief's hypothesis was `v₂(ξ − r_k) ≥ e·ℓ_k − o(ℓ_k)`.  The paper
does not need the `−o(ℓ)`: its eq. (`eq:depth`) is exact.  The paper's form is used. -/

/-- The paper's height bound, as a named abbreviation: `B(A, ℓ) = A·ℓ + log₂(3ℓ) + log₂ 3`. -/
noncomputable def heightBound (Aγ ℓ : ℝ) : ℝ := Aγ * ℓ + Real.logb 2 (3 * ℓ) + Real.logb 2 3

/-- **Item 6, pointwise form.**  The depth bound `|ξ − r|₂ ≤ 2^(−eℓ)` of the paper's
Step 3 and the height bound `log₂ H(r) < B` of eq. (`eq:hbound`) give the approximation
`|ξ − r|₂ ≤ H(r)^(−μ)` as soon as `μ·B ≤ eℓ`.  No limit is taken, and no error term is
dropped. -/
theorem approx_of_depth_height {ξ : ℚ_[2]} {r : ℚ} {μ eℓ B : ℝ}
    (hμ : 0 < μ) (hH : (1 : ℝ) < (H r : ℝ))
    (hdepth : ‖ξ - (r : ℚ_[2])‖ ≤ (2 : ℝ) ^ (-eℓ))
    (hheight : Real.logb 2 (H r) < B)
    (hcomp : μ * B ≤ eℓ) :
    ‖ξ - (r : ℚ_[2])‖ ≤ (H r : ℝ) ^ (-μ) := by
  have hHpos : (0 : ℝ) < (H r : ℝ) := lt_trans zero_lt_one hH
  have hrewrite : (H r : ℝ) ^ (-μ) = (2 : ℝ) ^ (-(μ * Real.logb 2 (H r))) := by
    rw [show -(μ * Real.logb 2 (H r)) = Real.logb 2 (H r) * (-μ) by ring,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_logb (by norm_num) (by norm_num) hHpos]
  rw [hrewrite]
  refine le_trans hdepth
    ((Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr ?_)
  have hle : μ * Real.logb 2 (H r) ≤ μ * B :=
    mul_le_mul_of_nonneg_left (le_of_lt hheight) (le_of_lt hμ)
  linarith

/-! ## Item 4 — the combination

Hypothesis of item 2 at exponent `μ > 2` gives transcendence; and at exponent `μ > 1`
the Liouville inequality already gives irrationality, so no appeal to the paper's
Proposition 2.10 is made anywhere in the skeleton. -/

/-- **Item 4.**  `ApproxExp 2 ξ μ` with `μ > 2` implies `ξ` is transcendental over `ℚ`. -/
theorem transcendental_of_ApproxExp {ξ : ℚ_[2]} {μ : ℝ} (hμ : 2 < μ)
    (h : ApproxExp 2 ξ μ) : Transcendental ℚ ξ := by
  obtain ⟨S, hS, _, happ⟩ := h
  exact transcendental_of_approxExp hμ S hS happ

/-- **Item 3, as used.**  `ApproxExp 2 ξ μ` with `μ > 1` already excludes every rational
with odd denominator (equivalently, every rational in `ℤ₂`).  This is the step for which
the paper invokes its Proposition 2.10; the skeleton does not need it. -/
theorem ne_rat_of_ApproxExp {ξ : ℚ_[2]} {μ : ℝ} (hμ : 1 < μ) (h : ApproxExp 2 ξ μ)
    {q : ℚ} (hq : Odd q.den) : ξ ≠ (q : ℚ_[2]) := by
  intro hEq
  obtain ⟨S, hS, hodd, happ⟩ := h
  subst hEq
  exact not_approxExp_of_rat hq hμ S hS hodd happ

end Sturmian
