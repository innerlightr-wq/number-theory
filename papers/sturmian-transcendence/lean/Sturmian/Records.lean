/-
# Stage 5, Step 3 — best-approximation records, and `ice(c_γ) > 2`

Mathlib has the Dirichlet approximation theorem
(`Real.exists_nat_abs_mul_sub_round_le`) but **not** the best-approximation property of
continued-fraction convergents.  This file builds the small amount of that theory the
lower bound needs, directly from the definition of a *record* — an index `q` such that no
smaller index approximates `γ` better — with no continued fractions.

The key step is the **gap lemma**: between consecutive records `p < r` there is no new
record below `r + p`.  Equivalently, records grow at least like Fibonacci, which is what
makes `limsup r_{i+1}/r_i ≥ 3/2` and hence `ice(c_γ) ≥ 5/2 > 2`.
-/
import Sturmian.Rotation
import Mathlib.NumberTheory.DiophantineApproximation.Basic

namespace Sturmian

/-! ## Distance to `ℤ`: the arithmetic we need -/

lemma nrmR_add_int (x : ℝ) (z : ℤ) : nrmR (x + (z : ℝ)) = nrmR x := by
  rw [nrmR, nrmR, round_add_intCast]
  push_cast
  ring_nf

lemma nrmR_nonneg (x : ℝ) : 0 ≤ nrmR x := abs_nonneg _

/-- For `|x| ≤ 1`, the distance from `x` to `ℤ` is `min |x| (1 − |x|)`. -/
lemma nrmR_eq_min_abs {x : ℝ} (h : |x| ≤ 1) : nrmR x = min |x| (1 - |x|) := by
  rw [nrmR, abs_sub_round_eq_min]
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hfl : ⌊x⌋ = -1 := by
      rw [Int.floor_eq_iff]; push_cast; exact ⟨by linarith, by linarith⟩
    have hfr : Int.fract x = x + 1 := by rw [Int.fract, hfl]; push_cast; ring
    rw [hfr, abs_of_neg hx, min_comm]
    congr 1 <;> ring
  · subst hx; simp
  · rcases eq_or_lt_of_le hhi with heq | hlt
    · have hx1 : x = 1 := heq
      subst hx1
      norm_num [Int.fract]
    · have hfl : ⌊x⌋ = 0 := by rw [Int.floor_eq_zero_iff]; exact ⟨le_of_lt hx, hlt⟩
      have hfr : Int.fract x = x := by rw [Int.fract, hfl]; simp
      rw [hfr, abs_of_pos hx]

/-- A lower bound on the distance to `ℤ`. -/
lemma le_nrmR {x c : ℝ} (hx : |x| ≤ 1) (h1 : c ≤ |x|) (h2 : c ≤ 1 - |x|) : c ≤ nrmR x := by
  rw [nrmR_eq_min_abs hx]; exact le_min h1 h2

/-- If `|x| ≤ 1/2` then the distance to `ℤ` is `|x|`. -/
lemma nrmR_eq_abs {x : ℝ} (hx : |x| ≤ 1 / 2) : nrmR x = |x| := by
  have h1 : |x| ≤ 1 := by linarith
  rw [nrmR_eq_min_abs h1, min_eq_left (by linarith)]

/-! ## Transporting to `nrm γ` -/

lemma nrm_add (γ : ℝ) (a b : ℕ) : nrm γ (a + b) = nrmR (off γ a + off γ b) := by
  obtain ⟨pa, ha⟩ := exists_int_off γ a
  obtain ⟨pb, hb⟩ := exists_int_off γ b
  have hsum : (((a + b : ℕ)) : ℝ) * γ = (off γ a + off γ b) + ((pa + pb : ℤ) : ℝ) := by
    push_cast
    push_cast at ha hb
    linarith [ha, hb]
  rw [nrm_eq_nrmR, hsum, nrmR_add_int]

lemma nrm_sub (γ : ℝ) {a b : ℕ} (hba : b ≤ a) :
    nrm γ (a - b) = nrmR (off γ a - off γ b) := by
  obtain ⟨pa, ha⟩ := exists_int_off γ a
  obtain ⟨pb, hb⟩ := exists_int_off γ b
  have hsum : (((a - b : ℕ)) : ℝ) * γ = (off γ a - off γ b) + ((pa - pb : ℤ) : ℝ) := by
    rw [Nat.cast_sub hba]
    push_cast
    push_cast at ha hb
    linarith [ha, hb]
  rw [nrm_eq_nrmR, hsum, nrmR_add_int]

/-- `off γ j ≠ 0` for `j ≥ 1` and irrational `γ`. -/
lemma off_ne_zero {γ : ℝ} (hirr : Irrational γ) {j : ℕ} (hj : 1 ≤ j) : off γ j ≠ 0 := by
  intro h
  have : ((j : ℝ)) * γ = ((round (((j : ℝ)) * γ) : ℤ) : ℝ) := by
    rw [off] at h; linarith
  exact mul_ne_int hirr hj _ this

lemma nrm_pos {γ : ℝ} (hirr : Irrational γ) {j : ℕ} (hj : 1 ≤ j) : 0 < nrm γ j :=
  abs_pos.mpr (off_ne_zero hirr hj)

/-! ## Records

A *record* is an index that strictly beats every smaller positive index.  For `γ`
irrational these are exactly the continued-fraction denominators `q_n`, but nothing below
uses that: every statement is proved from the definition. -/

/-- `q` is a **record** for `γ`: `q ≥ 1` and `q` approximates `γ` strictly better than every
smaller positive index. -/
def IsRecord (γ : ℝ) (q : ℕ) : Prop :=
  1 ≤ q ∧ ∀ j, 1 ≤ j → j < q → nrm γ q < nrm γ j

lemma IsRecord.one_le {γ : ℝ} {q : ℕ} (h : IsRecord γ q) : 1 ≤ q := h.1

lemma IsRecord.lt {γ : ℝ} {q : ℕ} (h : IsRecord γ q) {j : ℕ} (hj1 : 1 ≤ j) (hjq : j < q) :
    nrm γ q < nrm γ j := h.2 j hj1 hjq

lemma isRecord_one (γ : ℝ) : IsRecord γ 1 := ⟨le_refl _, by omega⟩

/-- Below any index there is a record at least as good: take the least minimiser. -/
lemma exists_record_le (γ : ℝ) : ∀ Q : ℕ, 1 ≤ Q →
    ∃ q, 1 ≤ q ∧ q ≤ Q ∧ IsRecord γ q ∧ nrm γ q ≤ nrm γ Q := by
  intro Q
  induction Q using Nat.strong_induction_on with
  | _ Q ih =>
    intro hQ
    by_cases hrec : IsRecord γ Q
    · exact ⟨Q, hQ, le_refl _, hrec, le_refl _⟩
    · simp only [IsRecord, not_and, not_forall, not_lt] at hrec
      obtain ⟨j, hj1, hjQ, hjle⟩ := hrec hQ
      obtain ⟨q, hq1, hqj, hqr, hqle⟩ := ih j hjQ hj1
      exact ⟨q, hq1, le_of_lt (lt_of_le_of_lt hqj hjQ), hqr, le_trans hqle hjle⟩

/-- Records are unbounded, and their quality tends to `0`: this is the only place Dirichlet's
approximation theorem is used. -/
lemma exists_record_gt {γ : ℝ} (hirr : Irrational γ) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q, N < q ∧ IsRecord γ q ∧ nrm γ q < ε := by
  classical
  set M : ℕ := max N 1 with hM
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right N 1)
  -- the best approximation quality among the indices `1, …, M`
  obtain ⟨b, hbmem, hb⟩ :=
    Finset.exists_min_image (Finset.Icc 1 M) (nrm γ)
      ⟨1, Finset.mem_Icc.mpr ⟨le_refl _, hMpos⟩⟩
  have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hbmem).1
  have hbpos : 0 < nrm γ b := nrm_pos hirr hb1
  set ε' : ℝ := min ε (nrm γ b) with hε'
  have hε'pos : 0 < ε' := lt_min hε hbpos
  -- a Dirichlet index beating `ε'` must lie beyond `M`
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε')
  have hnpos : 0 < n + 1 := Nat.succ_pos n
  obtain ⟨k, hk0, hkn, hk⟩ := Real.exists_nat_abs_mul_sub_round_le γ hnpos
  have hksmall : nrm γ k < ε' := by
    have h1 : (1 : ℝ) / ((n : ℝ) + 1 + 1) < ε' := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hε'pos] at hn
      nlinarith [hε'pos, hn]
    refine lt_of_le_of_lt ?_ h1
    calc nrm γ k = |(k : ℝ) * γ - (round ((k : ℝ) * γ) : ℝ)| := by
          rw [nrm, off]
      _ ≤ 1 / (((n : ℕ) + 1 : ℕ) + 1) := by exact_mod_cast hk
      _ = 1 / ((n : ℝ) + 1 + 1) := by push_cast; ring
  obtain ⟨q, hq1, hqk, hqrec, hqle⟩ := exists_record_le γ k hk0
  have hqsmall : nrm γ q < ε' := lt_of_le_of_lt hqle hksmall
  refine ⟨q, ?_, hqrec, lt_of_lt_of_le hqsmall (min_le_left _ _)⟩
  -- if `q ≤ M` then `nrm γ b ≤ nrm γ q < ε' ≤ nrm γ b`
  by_contra hqN
  have hqM : q ≤ M := by omega
  have := hb q (Finset.mem_Icc.mpr ⟨hq1, hqM⟩)
  exact absurd (lt_of_le_of_lt this (lt_of_lt_of_le hqsmall (min_le_right _ _))) (lt_irrefl _)

/-! ## The next record

`nextRec` is deliberately *not* defined as a function: `IsRecord` is not decidable, and the
existential form is all that is used. -/

/-- `r` is the record immediately after `p`. -/
def IsNextRec (γ : ℝ) (p r : ℕ) : Prop :=
  p < r ∧ IsRecord γ r ∧ ∀ m, p < m → m < r → ¬ IsRecord γ m

lemma exists_isNextRec {γ : ℝ} (hirr : Irrational γ) (p : ℕ) : ∃ r, IsNextRec γ p r := by
  classical
  have hex : ∃ k, IsRecord γ (p + 1 + k) := by
    obtain ⟨q, hq, hqrec, -⟩ := exists_record_gt hirr p (ε := 1) zero_lt_one
    exact ⟨q - (p + 1), by rwa [show p + 1 + (q - (p + 1)) = q by omega]⟩
  refine ⟨p + 1 + Nat.find hex, by omega, Nat.find_spec hex, ?_⟩
  intro m h1 h2 hm
  have hle : Nat.find hex ≤ m - (p + 1) :=
    Nat.find_le (by rwa [show p + 1 + (m - (p + 1)) = m by omega])
  omega

/-- **A record minimises up to its successor.**  This is the hypothesis `per_eq_of_min` needs:
a record `p` beats every positive index below the *next* record, not merely below itself. -/
lemma record_min_lt_nextRec {γ : ℝ} {p r : ℕ} (hp : IsRecord γ p) (hnext : IsNextRec γ p r) :
    ∀ j, 1 ≤ j → j < r → nrm γ p ≤ nrm γ j := by
  obtain ⟨hpr, hrrec, hnone⟩ := hnext
  intro j hj1 hj
  rcases lt_trichotomy j p with hjp | hjp | hjp
  · exact le_of_lt (hp.lt hj1 hjp)
  · exact hjp ▸ le_refl _
  · by_contra hcon
    push_neg at hcon
    obtain ⟨m, hm1, hmj, hmrec, hmle⟩ := exists_record_le γ j hj1
    have hmp : p < m := by
      rcases lt_trichotomy m p with h | h | h
      · exact absurd (lt_of_le_of_lt (le_trans hmle (le_of_lt hcon)) (hp.lt hm1 h)) (lt_irrefl _)
      · exact absurd (lt_of_le_of_lt (h ▸ hmle) hcon) (lt_irrefl _)
      · exact h
    exact hnone m hmp (lt_of_le_of_lt hmj hj) hmrec

/-- A better index than a record `p` forces a record strictly beyond `p`. -/
lemma exists_record_gt_of_better {γ : ℝ} {p j : ℕ} (hp : IsRecord γ p) (hj1 : 1 ≤ j)
    (hbetter : nrm γ j < nrm γ p) : ∃ m, p < m ∧ m ≤ j ∧ IsRecord γ m := by
  obtain ⟨m, hm1, hmj, hmrec, hmle⟩ := exists_record_le γ j hj1
  refine ⟨m, ?_, hmj, hmrec⟩
  rcases lt_trichotomy m p with h | h | h
  · exact absurd (lt_of_le_of_lt (le_trans hmle (le_of_lt hbetter)) (hp.lt hm1 h)) (lt_irrefl _)
  · exact absurd (lt_of_le_of_lt (h ▸ hmle) hbetter) (lt_irrefl _)
  · exact h

/-! ## Consecutive records point to opposite sides of the nearest integer -/

theorem off_mul_off_next_neg {γ : ℝ} (hirr : Irrational γ) {p r : ℕ} (hp : IsRecord γ p)
    (hnext : IsNextRec γ p r) : off γ p * off γ r < 0 := by
  obtain ⟨hpr, hrrec, hnone⟩ := hnext
  have hp1 : 1 ≤ p := hp.1
  have hlt : nrm γ r < nrm γ p := hrrec.lt hp1 hpr
  have hune : off γ p ≠ 0 := off_ne_zero hirr hp1
  have hvne : off γ r ≠ 0 := off_ne_zero hirr hrrec.1
  rcases lt_trichotomy (off γ p * off γ r) 0 with h | h | h
  · exact h
  · exact absurd h (mul_ne_zero hune hvne)
  · exfalso
    have hup : |off γ p| = nrm γ p := abs_off γ p
    have hvp : |off γ r| = nrm γ r := abs_off γ r
    have habs : |off γ r - off γ p| = nrm γ p - nrm γ r := by
      rcases lt_trichotomy (off γ p) 0 with hu | hu | hu
      · have hv : off γ r < 0 := by
          by_contra hv; push_neg at hv; nlinarith
        rw [abs_of_neg hu] at hup
        rw [abs_of_neg hv] at hvp
        rw [abs_of_pos (by linarith)]; linarith
      · exact absurd hu hune
      · have hv : 0 < off γ r := by
          by_contra hv; push_neg at hv; nlinarith
        rw [abs_of_pos hu] at hup
        rw [abs_of_pos hv] at hvp
        rw [abs_of_neg (by linarith)]; linarith
    have hhalf : |off γ r - off γ p| ≤ 1 / 2 := by
      rw [habs]; linarith [nrm_le_half γ p, nrm_nonneg γ r]
    have hdiff : nrm γ (r - p) = nrm γ p - nrm γ r := by
      rw [nrm_sub γ (le_of_lt hpr), nrmR_eq_abs hhalf, habs]
    have hbetter : nrm γ (r - p) < nrm γ p := by
      rw [hdiff]; linarith [nrm_pos hirr hrrec.1]
    obtain ⟨m, hmp, hmj, hmrec⟩ := exists_record_gt_of_better hp (by omega) hbetter
    exact hnone m hmp (by omega) hmrec

/-! ## Elementary sign algebra -/

lemma lt_nrmR {x c : ℝ} (hx : |x| ≤ 1) (h1 : c < |x|) (h2 : c < 1 - |x|) : c < nrmR x := by
  rw [nrmR_eq_min_abs hx]; exact lt_min h1 h2

lemma mul_pos_of_mul_neg_mul_neg {a b c : ℝ} (hab : a * b < 0) (hbc : b * c < 0) :
    0 < a * c := by
  rcases lt_trichotomy b 0 with hb | hb | hb
  · have ha : 0 < a := by nlinarith
    have hc : 0 < c := by nlinarith
    exact mul_pos ha hc
  · rw [hb] at hab; simp at hab
  · have ha : a < 0 := by nlinarith
    have hc : c < 0 := by nlinarith
    exact mul_pos_of_neg_of_neg ha hc

lemma abs_add_of_mul_pos {a b : ℝ} (h : 0 < a * b) : |a + b| = |a| + |b| := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have hb : b < 0 := by nlinarith
    rw [abs_of_neg ha, abs_of_neg hb, abs_of_neg (by linarith)]; ring
  · rw [ha] at h; simp at h
  · have hb : 0 < b := by nlinarith
    rw [abs_of_pos ha, abs_of_pos hb, abs_of_pos (by linarith)]

lemma abs_add_of_mul_neg {a b : ℝ} (h : a * b < 0) (hlt : |a| < |b|) :
    |a + b| = |b| - |a| := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have hb : 0 < b := by nlinarith
    rw [abs_of_neg ha, abs_of_pos hb] at hlt ⊢
    rw [abs_of_pos (by linarith)]; ring
  · rw [ha] at h; simp at h
  · have hb : b < 0 := by nlinarith
    rw [abs_of_pos ha, abs_of_neg hb] at hlt ⊢
    rw [abs_of_neg (by linarith)]; ring

lemma abs_sub_of_mul_pos {a b : ℝ} (h : 0 < a * b) (hlt : |a| < |b|) :
    |a - b| = |b| - |a| := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have hb : b < 0 := by nlinarith
    rw [abs_of_neg ha, abs_of_neg hb] at hlt ⊢
    rw [abs_of_pos (by linarith)]; ring
  · rw [ha] at h; simp at h
  · have hb : 0 < b := by nlinarith
    rw [abs_of_pos ha, abs_of_pos hb] at hlt ⊢
    rw [abs_of_neg (by linarith)]; ring

/-! ## The gap lemma

Between a record `r` and the next record there is room at least the *previous* record `p`.
This is the Fibonacci-type growth of the record sequence, obtained here without continued
fractions. -/

/-- The heart of the gap lemma: for `1 ≤ t < p`, the index `r + t` is strictly worse than `r`. -/
theorem lt_nrm_add {γ : ℝ} (hirr : Irrational γ) {p r t : ℕ} (hp : IsRecord γ p)
    (hnext : IsNextRec γ p r) (hsmall : nrm γ r < 1 / 4) (ht1 : 1 ≤ t) (htp : t < p) :
    nrm γ r < nrm γ (r + t) := by
  obtain ⟨hpr, hrrec, hnone⟩ := hnext
  have hp1 : 1 ≤ p := hp.1
  have hθ : nrm γ r < nrm γ p := hrrec.lt hp1 hpr
  have hτ : nrm γ p < nrm γ t := hp.lt ht1 htp
  have hsign : off γ p * off γ r < 0 := off_mul_off_next_neg hirr hp ⟨hpr, hrrec, hnone⟩
  have hwne : off γ t ≠ 0 := off_ne_zero hirr ht1
  have hvne : off γ r ≠ 0 := off_ne_zero hirr hrrec.1
  have hθ0 : 0 < nrm γ r := nrm_pos hirr hrrec.1
  have hrt : nrm γ (r + t) = nrmR (off γ r + off γ t) := nrm_add γ r t
  have hvabs : |off γ r| = nrm γ r := abs_off γ r
  have hwabs : |off γ t| = nrm γ t := abs_off γ t
  have hzabs : |off γ p| = nrm γ p := abs_off γ p
  rcases lt_trichotomy (off γ r * off γ t) 0 with hcase | hcase | hcase
  -- Case B: `t` sits on the same side as `p`, forcing `‖tγ‖ > 2‖pγ‖ > 2‖rγ‖`
  · have hzt : 0 < off γ p * off γ t :=
      mul_pos_of_mul_neg_mul_neg hsign hcase
    have hltzw : |off γ p| < |off γ t| := by rw [hzabs, hwabs]; exact hτ
    have hdiff : |off γ p - off γ t| = nrm γ t - nrm γ p := by
      rw [abs_sub_of_mul_pos hzt hltzw, hwabs, hzabs]
    have hhalf : |off γ p - off γ t| ≤ 1 / 2 := by
      rw [hdiff]; linarith [nrm_le_half γ t, nrm_nonneg γ p]
    have hpt : nrm γ (p - t) = nrm γ t - nrm γ p := by
      rw [nrm_sub γ (le_of_lt htp), nrmR_eq_abs hhalf, hdiff]
    have htwo : 2 * nrm γ p < nrm γ t := by
      have := hp.lt (j := p - t) (by omega) (by omega)
      rw [hpt] at this; linarith
    have hltvw : |off γ r| < |off γ t| := by rw [hvabs, hwabs]; linarith
    have hsum : |off γ r + off γ t| = nrm γ t - nrm γ r := by
      rw [abs_add_of_mul_neg hcase hltvw, hwabs, hvabs]
    have hsumhalf : |off γ r + off γ t| ≤ 1 / 2 := by
      rw [hsum]; linarith [nrm_le_half γ t]
    rw [hrt, nrmR_eq_abs hsumhalf, hsum]
    linarith
  · exact absurd hcase (mul_ne_zero hvne hwne)
  -- Case A: `t` sits on the same side as `r`; the two displacements add
  · have hsum : |off γ r + off γ t| = nrm γ r + nrm γ t := by
      rw [abs_add_of_mul_pos hcase, hvabs, hwabs]
    rw [hrt]
    refine lt_nrmR (by rw [hsum]; linarith [nrm_le_half γ t]) ?_ ?_
    · rw [hsum]; linarith
    · rw [hsum]; linarith [nrm_le_half γ t]

/-- **The gap lemma.**  If `p`, `r`, `s` are three consecutive records and `‖rγ‖ < 1/4`, then
`s ≥ r + p`: the record sequence grows at least like the Fibonacci numbers. -/
theorem gap_le {γ : ℝ} (hirr : Irrational γ) {p r s : ℕ} (hp : IsRecord γ p)
    (hnext : IsNextRec γ p r) (hnext2 : IsNextRec γ r s) (hsmall : nrm γ r < 1 / 4) :
    r + p ≤ s := by
  by_contra hcon
  push_neg at hcon
  have hpr : p < r := hnext.1
  have hrs : r < s := hnext2.1
  have hsrec : IsRecord γ s := hnext2.2.1
  -- `s = r + t` with `1 ≤ t < p`
  have hworse : nrm γ r < nrm γ (r + (s - r)) :=
    lt_nrm_add hirr hp hnext hsmall (by omega) (by omega)
  rw [show r + (s - r) = s by omega] at hworse
  exact absurd (hsrec.lt (le_trans hp.1 (le_of_lt hpr)) hrs) (not_lt.mpr (le_of_lt hworse))

/-! ## Tier A: a prefix power above `12/5`

Combining the gap lemma with `per_eq_of_min` at two consecutive records gives a uniform
prefix power `12/5 = 2.4`.  The dichotomy is the `max(r/p, 2 + p/r)` one: if `r/p ≥ 3/2`
the record `p` already repeats to power `5/2 - 2/p`, and otherwise the record `r` repeats to
power `2 + p/r - 2/r > 8/3 - 2/r`.

(Pushing the same two inequalities to their common value gives `1 + φ = 2.618…`, the
Berthé–Holton–Zamboni floor; `12/5` is all the headline case needs and is what is proved
here.) -/

/-- **Tier A.**  Arbitrarily far out, `c_γ` begins with a `12/5`-th power of its own prefix. -/
theorem exists_long_period {γ : ℝ} (hirr : Irrational γ) (N : ℕ) :
    ∃ q L : ℕ, N ≤ q ∧ 2 ≤ q ∧ (12 / 5 : ℝ) * (q : ℝ) ≤ (L : ℝ) ∧
      ∀ m : ℕ, m < L → charWord γ m = per q (charWord γ) m := by
  obtain ⟨p, hpN, hprec, hpsmall⟩ :=
    exists_record_gt hirr (max N 20) (ε := 1 / 4) (by norm_num)
  obtain ⟨r, hnext⟩ := exists_isNextRec hirr p
  obtain ⟨s, hnext2⟩ := exists_isNextRec hirr r
  have hpr : p < r := hnext.1
  have hrrec : IsRecord γ r := hnext.2.1
  have hrs : r < s := hnext2.1
  have hp20 : 20 ≤ p := by omega
  have hpN' : N ≤ p := by omega
  have hrsmall : nrm γ r < 1 / 4 := lt_trans (hrrec.lt hprec.1 hpr) hpsmall
  have hgap : r + p ≤ s := gap_le hirr hprec hnext hnext2 hrsmall
  by_cases hdich : 3 * p ≤ 2 * r
  -- the record `p` repeats to power `(r + p - 2)/p ≥ 5/2 - 2/p ≥ 12/5`
  · refine ⟨p, r + p - 2, hpN', by omega, ?_, ?_⟩
    · have hnat : 12 * p ≤ 5 * (r + p - 2) := by omega
      have : (12 : ℝ) * (p : ℝ) ≤ 5 * ((r + p - 2 : ℕ) : ℝ) := by exact_mod_cast hnat
      linarith
    · exact per_eq_of_min hirr hprec.1 (by omega) (record_min_lt_nextRec hprec hnext)
  -- otherwise the record `r` repeats to power `(s + r - 2)/r ≥ 8/3 - 2/r ≥ 12/5`
  · push_neg at hdich
    refine ⟨r, 2 * r + p - 2, by omega, by omega, ?_, ?_⟩
    · have hnat : 12 * r ≤ 5 * (2 * r + p - 2) := by omega
      have : (12 : ℝ) * (r : ℝ) ≤ 5 * ((2 * r + p - 2 : ℕ) : ℝ) := by exact_mod_cast hnat
      linarith
    · intro m hm
      exact per_eq_of_min hirr hrrec.1 (by omega) (record_min_lt_nextRec hrrec hnext2) m
        (by omega)

end Sturmian