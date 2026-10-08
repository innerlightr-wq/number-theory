/-
# TODO — what is left

**This file is NOT imported by `Sturmian.lean` and nothing reported as proved depends on
it.**  Everything here is `sorry`.

STAGES 1–4 ARE DONE.  Theorem 1.3 and Corollary 1.4 are machine-checked modulo exactly
**two** axioms, both results of other authors: Ridout's theorem (in Bugeaud–Kekeç's
single-prime form, source checked verbatim) and the Berthé–Holton–Zamboni floor
`ice(c_γ) ≥ 1+φ`.  Everything of the paper's own argument is proved, including:

* `Φ` itself — constructed (`Sturmian.PhiBL`, `Sturmian.isBL_PhiBL`);
* the Bernstein–Lagarias isometry, Prop. 2.1 — `Sturmian.IsBL.isometry`;
* eq. (3) — `Sturmian.IsBL.affinegen`;
* the periodic-shadow formula, Prop. 2.2 — `Sturmian.shadow_formula`;
* the transfer identity, eq. (12) — `Sturmian.IsBL.transfer`;
* the telescoping count and balance — `Sturmian.ones_charWord`,
  `Sturmian.abs_ones_charWord_sub_lt_one`, `Sturmian.abs_balance_prefix`;
* `[DJirr, Lemma 10.4]` — `Sturmian.cw_le_of_balance`, `Sturmian.cw_le_prefix`;
* Prop. 2.4, the height of a shadow — `Sturmian.shadow_height_bound`, **axiom-free**;
* aperiodicity of `c_γ` — `Sturmian.charWord_ne_per`;
* `ice` and the paper's Steps 1–2 — `Sturmian.ice`,
  `Sturmian.exists_prefix_power_of_lt_ice`.

WHAT REMAINS is listed below.  None of it is needed for the main theorem; the first item is
the only one that would reduce the axiom count further.
-/
import Sturmian

namespace Sturmian.Stubs

/-- REMAINS, and the only thing that would reduce the axiom count — a formal proof of the
Berthé–Holton–Zamboni floor `ice(c_γ) ≥ 1 + φ` (the paper's Prop. 2.8, `[BHZ06, §4.2]`),
which would replace `Sturmian.bhz_ice_floor`.  This is someone else's theorem; formalising
it means formalising BHZ §4.2, including their `ice` formula (their Theorem 1.2 and the
sentence after its proof).  **Before that, the source itself needs checking: it is paywalled
and was NOT CHECKED here — see `AXIOMS.md` §2.** -/
theorem bhz_floor : True := sorry

/-- REMAINS (not needed) — the paper's Prop. 2.6, `[BHZ06, §4.2]`: the `ice` formula
`ice(c_α) = 1 + limsup q_{k+1}/q_k`.  Would let the paper's **Theorem 1.2** (the
quantitative form, `ω₁⁽²⁾ ≥ ice/A − 1`) be stated in continued-fraction terms. -/
theorem ice_formula : True := sorry

/-- REMAINS (not needed) — the paper's Prop. 2.3, `[BHZ06, Proposition 3.2]`: a Sturmian
sequence beginning in `W^r` with `r ≥ 2`, `|W| ≥ 2`, `W` primitive has `W` a conjugate of a
standard word.  **Eliminated from the development at stage 4**: balance for prefixes of
`c_γ` is proved directly, so no primitive-root replacement is performed and this is never
invoked. -/
theorem conjugate_of_standard : True := sorry

/-- REMAINS (not needed) — the paper's Theorems 6.1 and 7.3, the Liouville alternative and
the effective irrationality measure.  These are complements, not part of Theorem 1.3. -/
theorem complements : True := sorry

end Sturmian.Stubs
