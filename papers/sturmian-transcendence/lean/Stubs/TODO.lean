/-
# TODO — stages 2 and 3

**This file is NOT imported by `Sturmian.lean` and nothing reported as proved depends on
it.**  It records the shape of the statements the later stages must supply, so that the
stage-1 interfaces are visible.  Everything here is `sorry`.

STAGE 2 (the 2-adic core): Φ on infinite binary words; the Bernstein–Lagarias isometry
(paper Prop 2.1); the periodic-shadow formula (paper Prop 2.2); the transfer identity
(paper eq. (12)); and the fact that the periodic shadows are distinct rationals with odd
denominators, which is what `Sturmian.transcendental_of_approxExp` consumes.

STAGE 3 (deferred, DO NOT START): the height bound (paper Prop 2.4), the Sturmian
combinatorics, and `ice(c_γ) ≥ 1 + φ` (paper Prop 2.8).
-/
import Sturmian

namespace Sturmian.Stubs

/-- STAGE 2.1 — `Φ` on infinite binary words, valued in `ℤ_[2]` (paper §1.1, eq. (1)–(2)). -/
def Phi : (ℕ → Fin 2) → ℤ_[2] := sorry

/-- STAGE 2.2 — the Bernstein–Lagarias isometry (paper Prop 2.1):
`v₂(Φ(v) − Φ(w)) = lcp(v, w)`. -/
theorem bernstein_lagarias_isometry : True := sorry

/-- STAGE 2.3 — the periodic-shadow formula (paper Prop 2.2): `Φ(W^∞)` is rational with
denominator `2^ℓ − 3^k`. -/
theorem periodic_shadow : True := sorry

/-- STAGE 2.4 — the transfer identity (paper eq. (12)):
`2Φ(c) = 3Φ(1c) + 1 = Φ(0c)`. -/
theorem transfer_identity : True := sorry

/-- STAGE 3 — the height bound (paper Prop 2.4). -/
theorem height_bound : True := sorry

/-- STAGE 3 — the initial-critical-exponent floor (paper Prop 2.8, [BHZ06]). -/
theorem ice_floor : True := sorry

end Sturmian.Stubs
