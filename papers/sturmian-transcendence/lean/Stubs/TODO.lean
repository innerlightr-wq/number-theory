/-
# TODO — stage 3

**This file is NOT imported by `Sturmian.lean` and nothing reported as proved depends on
it.**  Everything here is `sorry`.

STAGES 1 AND 2 ARE DONE.  In particular the following are **no longer** stubs and have
moved into the main development as PROVED results:

* `Φ` itself — constructed, `Sturmian.PhiBL` / `Sturmian.isBL_PhiBL`;
* the Bernstein–Lagarias isometry (Prop. 2.1) — `Sturmian.IsBL.isometry`;
* the periodic-shadow formula (Prop. 2.2) — `Sturmian.shadow_formula`;
* the transfer identity (eq. 12) — `Sturmian.IsBL.transfer`.

STAGE 3 IS DONE for the height bound and the Sturmian combinatorics.  No longer stubs:

* the telescoping count `k_ℓ(c_γ) = ⌊(ℓ+1)γ⌋` — `Sturmian.ones_charWord`;
* balance for prefixes — `Sturmian.abs_ones_charWord_sub_lt_one`;
* **Proposition 2.4** — `Sturmian.shadow_height_bound`, now a theorem;
* aperiodicity of `c_γ` — `Sturmian.charWord_ne_per`.

WHAT REMAINS, and it is exactly the two axioms of `Sturmian/Axioms.lean` that are still
there: the `ice` machinery behind the paper's Steps 1–2 (so that `bhz_prefix_family` can be
reduced to Berthé–Holton–Zamboni's floor alone), and `[DJirr, Lemma 10.4]`.
-/
import Sturmian

namespace Sturmian.Stubs

/-- STAGE 3 — the initial critical exponent of Definition 2.5: the prefix power of `W` in
`ω` is `lcp(ω, W^∞)/|W|`, and `ice ω` is the limsup of the prefix powers of the prefixes
`ω[0,n)`.  Needed to state the paper's Theorem 1.3 criterion `ice(c_γ) > 2A(γ)` directly,
rather than through `Sturmian.bhz_prefix_family`. -/
noncomputable def ice : Word → ℝ := sorry

/-- STAGE 3 — the paper's Proposition 2.6 (`\cite[\S4.2]{BHZ06}`): the `ice` formula
`ice(c_α) = 1 + limsup q_{k+1}/q_k`. -/
theorem ice_formula : True := sorry

/-- STAGE 3 — the paper's Proposition 2.8 (`\cite[\S4.2]{BHZ06}`): `ice(c_γ) ≥ 1 + φ`.
Discharging this plus Steps 1–2 replaces `Sturmian.bhz_prefix_family`. -/
theorem ice_floor : True := sorry

/-- STAGE 3 — the paper's Proposition 2.3 (`\cite[Proposition 3.2]{BHZ06}`): a Sturmian
sequence beginning in `W^r`, `r ≥ 2`, `|W| ≥ 2`, `W` primitive, has `W` a conjugate of a
standard word, hence `W^∞` balanced. -/
theorem conjugate_of_standard : True := sorry

/-- STAGE 3 — the paper's Proposition 2.4, the height of a shadow.  Discharging this
replaces `Sturmian.shadow_height_bound`.  The paper proves it in four lines from
`\cite[Lemma 10.4]{DJirr}` and balance. -/
theorem height_bound : True := sorry

/-- STAGE 3 — Steps 1–2: extraction of the primitive-prefix family from `ice(c_γ) > 2A(γ)`. -/
theorem prefix_family_extraction : True := sorry

end Sturmian.Stubs
