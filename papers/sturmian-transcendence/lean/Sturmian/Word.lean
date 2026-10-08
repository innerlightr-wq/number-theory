/-
# Infinite binary words, and the paper's `k_m`, `c_m`, `lcp`

Every definition quotes the paper line it encodes.  Paper, §2.1 (`\subsection{The conjugacy
map and the isometry}`), opening paragraph:

> "Throughout, $\vtwo$ is the $2$-adic valuation, $|x|_2=2^{-\vtwo(x)}$, and for words
>  $v,w\in\{0,1\}^{\N}$, $\lcp(v,w)$ is the length of their longest common prefix. For a
>  word $v$ and $m\ge0$ set $k_m(v):=\#\{i<m:v_i=1\}$."

and, after eq. (2):

> "iterating the latter and writing
>  $c_m(v):=\sum_{i<m,\,v_i=1}3^{\,k_m(v)-k_{i+1}(v)}2^{i}\in\Z$ gives" … eq. (3).
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Sturmian

/-! ## Words -/

/-- An infinite binary word `v = v₀v₁v₂⋯ ∈ {0,1}^ℕ`.  `true` is the letter `1`. -/
abbrev Word := ℕ → Bool

/-- The shift `σ` on words: `(σv)ᵢ = vᵢ₊₁`.  Paper, §1.1: "σ being the shift on words." -/
def shift (v : Word) : Word := fun n => v (n + 1)

/-- Prepending a letter: `cons b v = b v₀ v₁ ⋯`.  The paper's `1c` and `0c`. -/
def cons (b : Bool) (v : Word) : Word
  | 0 => b
  | (n + 1) => v n

@[simp] lemma cons_zero (b : Bool) (v : Word) : cons b v 0 = b := rfl
@[simp] lemma cons_succ (b : Bool) (v : Word) (n : ℕ) : cons b v (n + 1) = v n := rfl
@[simp] lemma shift_cons (b : Bool) (v : Word) : shift (cons b v) = v := rfl
@[simp] lemma shift_apply (v : Word) (n : ℕ) : shift v n = v (n + 1) := rfl

@[simp] lemma cons_shift (v : Word) : cons (v 0) (shift v) = v := by
  funext k
  cases k with
  | zero => rfl
  | succ m => rfl

lemma eq_of_shift_eq {v w : Word} (h0 : v 0 = w 0) (hs : shift v = shift w) : v = w := by
  funext n
  cases n with
  | zero => exact h0
  | succ m => exact congrFun hs m

/-- `σ^m v`. -/
def shiftIter (m : ℕ) (v : Word) : Word := fun n => v (n + m)

@[simp] lemma shiftIter_zero (v : Word) : shiftIter 0 v = v := rfl
@[simp] lemma shiftIter_apply (m : ℕ) (v : Word) (n : ℕ) : shiftIter m v n = v (n + m) := rfl

lemma shift_shiftIter (m : ℕ) (v : Word) : shift (shiftIter m v) = shiftIter (m + 1) v := by
  funext n; simp only [shift, shiftIter]; congr 1; omega

lemma shiftIter_zero_apply (m : ℕ) (v : Word) : shiftIter m v 0 = v m := by
  simp [shiftIter]

/-! ## The characteristic Sturmian word

Paper, §2.2: "For irrational $\gamma\in(0,1)$ the characteristic word is
$c_\gamma(j)=\lfloor(j+1)\gamma\rfloor-\lfloor j\gamma\rfloor$ for $j\ge1$".

**INDEX CONVENTION, recorded because it matters.**  The paper indexes the letters of
`c_γ` from `j = 1`.  `Sturmian.Word` is indexed from `0`.  So the `n`-th letter of
`charWord γ` is the paper's `c_γ(n+1)`. -/

/-- The characteristic Sturmian word of slope `γ`, in `0`-based indexing:
`charWord γ n = c_γ(n+1) = ⌊(n+2)γ⌋ − ⌊(n+1)γ⌋`. -/
noncomputable def charWord (γ : ℝ) : Word :=
  fun n => decide (⌊((n : ℝ) + 2) * γ⌋ - ⌊((n : ℝ) + 1) * γ⌋ = 1)

/-! ## `k_m(v)` — the paper's count of ones in the first `m` letters -/

/-- `k_m(v) := #{i < m : vᵢ = 1}`, the paper's §2.1 definition. -/
def ones (m : ℕ) (v : Word) : ℕ := ((Finset.range m).filter (fun i => v i = true)).card

@[simp] lemma ones_zero (v : Word) : ones 0 v = 0 := by simp [ones]

lemma ones_succ (m : ℕ) (v : Word) :
    ones (m + 1) v = ones m v + (if v m then 1 else 0) := by
  classical
  by_cases h : v m = true
  · simp [ones, Finset.range_add_one, Finset.filter_insert, h]
  · simp [ones, Finset.range_add_one, Finset.filter_insert, h]

lemma ones_mono {m n : ℕ} (h : m ≤ n) (v : Word) : ones m v ≤ ones n v := by
  classical
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨lt_of_lt_of_le hx.1 h, hx.2⟩

/-! ## `c_m(v)` — the paper's integer numerator -/

/-- `c_m(v) := Σ_{i<m, vᵢ=1} 3^{k_m(v) − k_{i+1}(v)} 2^i ∈ ℤ`, the paper's §2.1 definition
(the display just before eq. (3)). -/
def cw (m : ℕ) (v : Word) : ℤ :=
  ∑ i ∈ Finset.range m, (if v i then (3 : ℤ) ^ (ones m v - ones (i + 1) v) * 2 ^ i else 0)

@[simp] lemma cw_zero (v : Word) : cw 0 v = 0 := by simp [cw]

/-- The recursion satisfied by the paper's `c_m`.  Proved from the closed form, not
substituted for it. -/
lemma cw_succ (m : ℕ) (v : Word) :
    cw (m + 1) v = if v m then 3 * cw m v + 2 ^ m else cw m v := by
  classical
  rw [cw, Finset.sum_range_succ]
  by_cases h : v m = true
  · have hk : ones (m + 1) v = ones m v + 1 := by rw [ones_succ]; simp [h]
    have hmain : ∑ i ∈ Finset.range m,
        (if v i then (3 : ℤ) ^ (ones (m + 1) v - ones (i + 1) v) * 2 ^ i else 0)
        = 3 * cw m v := by
      rw [cw, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i + 1 ≤ m := by have := Finset.mem_range.mp hi; omega
      have hle : ones (i + 1) v ≤ ones m v := ones_mono hi' v
      by_cases hv : v i = true
      · simp only [hv, if_true, hk]
        rw [show ones m v + 1 - ones (i + 1) v = (ones m v - ones (i + 1) v) + 1 by omega]
        ring
      · simp only [hv, Bool.false_eq_true, if_false]; ring
    rw [hmain]
    simp [h]
  · have hk : ones (m + 1) v = ones m v := by rw [ones_succ]; simp [h]
    have hmain : ∑ i ∈ Finset.range m,
        (if v i then (3 : ℤ) ^ (ones (m + 1) v - ones (i + 1) v) * 2 ^ i else 0)
        = cw m v := by rw [cw, hk]
    rw [hmain]
    simp [h]

/-- `k_m` is additive along a cut: the ones in `[0,a+b)` are those in `[0,a)` plus those in
`[0,b)` of the shifted word. -/
lemma ones_add (v : Word) (a : ℕ) : ∀ b, ones (a + b) v = ones a v + ones b (shiftIter a v) := by
  intro b
  induction b with
  | zero => simp
  | succ m ih =>
    have hassoc : a + (m + 1) = (a + m) + 1 := by omega
    rw [hassoc, ones_succ, ih, ones_succ, shiftIter_apply]
    have hc : v (a + m) = v (m + a) := by rw [Nat.add_comm]
    rw [hc]
    omega

/-! ### How `k_m` and `c_m` behave under prepending a letter

These are the two identities the construction of `Φ` in `Sturmian/Construct.lean` needs. -/

lemma ones_cons_false_succ (c : Word) : ∀ m, ones (m + 1) (cons false c) = ones m c := by
  intro m
  induction m with
  | zero => simp [ones_succ]
  | succ m ih => rw [ones_succ, ih, cons_succ, ones_succ]

lemma ones_cons_true_succ (c : Word) : ∀ m, ones (m + 1) (cons true c) = ones m c + 1 := by
  intro m
  induction m with
  | zero => simp [ones_succ]
  | succ m ih => rw [ones_succ, ih, cons_succ, ones_succ]; omega

lemma cw_cons_false_succ (c : Word) : ∀ m, cw (m + 1) (cons false c) = 2 * cw m c := by
  intro m
  induction m with
  | zero => simp [cw_succ]
  | succ m ih =>
    rw [cw_succ, cons_succ, ih, cw_succ]
    by_cases hc : c m = true
    · simp only [hc, if_true]; ring
    · simp only [hc, Bool.false_eq_true, if_false]

lemma cw_cons_true_succ (c : Word) :
    ∀ m, cw (m + 1) (cons true c) = 2 * cw m c + (3 : ℤ) ^ (ones m c) := by
  intro m
  induction m with
  | zero => simp [cw_succ]
  | succ m ih =>
    rw [cw_succ, cons_succ, ih, cw_succ, ones_succ]
    by_cases hc : c m = true
    · simp only [hc, if_true]; ring
    · simp only [hc, Bool.false_eq_true, if_false]; ring

/-! ### Congruence: `k_m` and `c_m` only see the first `m` letters -/

lemma ones_congr {m : ℕ} {v w : Word} (hvw : ∀ i, i < m → v i = w i) :
    ones m v = ones m w := by
  classical
  unfold ones
  congr 1
  refine Finset.filter_congr ?_
  intro i hi
  rw [hvw i (Finset.mem_range.mp hi)]

lemma cw_congr {m : ℕ} {v w : Word} (hvw : ∀ i, i < m → v i = w i) :
    cw m v = cw m w := by
  classical
  unfold cw
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < m := Finset.mem_range.mp hi
  have h1 : ones m v = ones m w := ones_congr hvw
  have h2 : ones (i + 1) v = ones (i + 1) w :=
    ones_congr (fun j hj => hvw j (by omega))
  rw [hvw i hi', h1, h2]

/-! ## `lcp` — the length of the longest common prefix

Paper, §2.1: "for words $v,w\in\{0,1\}^{\N}$, $\lcp(v,w)$ is the length of their longest
common prefix."  For `v ≠ w` this is the least index at which they differ. -/

/-- `lcp(v, w)` for distinct words: the least index at which they differ, i.e. the length
of their longest common prefix. -/
noncomputable def lcp (v w : Word) (h : v ≠ w) : ℕ :=
  Nat.find (p := fun n => v n ≠ w n) (by
    rcases Function.ne_iff.mp h with ⟨n, hn⟩; exact ⟨n, hn⟩)

lemma lcp_spec (v w : Word) (h : v ≠ w) : v (lcp v w h) ≠ w (lcp v w h) :=
  Nat.find_spec (p := fun n => v n ≠ w n) _

lemma eq_of_lt_lcp (v w : Word) (h : v ≠ w) {n : ℕ} (hn : n < lcp v w h) : v n = w n := by
  have := Nat.find_min (p := fun n => v n ≠ w n) _ hn
  simpa using this

/-- If `v` and `w` agree at `0` then the shift drops the `lcp` by exactly one. -/
lemma lcp_shift {v w : Word} (h : v ≠ w) (h0 : v 0 = w 0) (hs : shift v ≠ shift w) :
    lcp v w h = lcp (shift v) (shift w) hs + 1 := by
  have hq := lcp_spec (shift v) (shift w) hs
  have hle : lcp v w h ≤ lcp (shift v) (shift w) hs + 1 := by
    refine Nat.find_le ?_
    simpa [shift] using hq
  have hne0 : lcp v w h ≠ 0 := by
    intro hz
    exact (lcp_spec v w h) (by rw [hz]; exact h0)
  obtain ⟨L', hL'⟩ : ∃ L', lcp v w h = L' + 1 := ⟨lcp v w h - 1, by omega⟩
  have hp : v (L' + 1) ≠ w (L' + 1) := by
    have hspec := lcp_spec v w h; rwa [hL'] at hspec
  have hge : lcp (shift v) (shift w) hs ≤ L' := Nat.find_le (by simpa [shift] using hp)
  omega

end Sturmian
