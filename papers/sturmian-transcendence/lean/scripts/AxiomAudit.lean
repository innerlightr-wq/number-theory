import Sturmian

/-! `#print axioms` on every stage-1 result.  The permitted output is the three standard
Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) plus the single named axiom
`Sturmian.ridout_single_prime` declared in `Sturmian/Axioms.lean`. -/

-- the one declared axiom
#print axioms Sturmian.ridout_single_prime

-- Basic: height and finiteness
#print axioms Sturmian.H_pos
#print axioms Sturmian.finite_setOf_H_le
#print axioms Sturmian.exists_H_gt_of_infinite

-- Liouville (PROVED; must NOT list ridout_single_prime)
#print axioms Sturmian.one_div_abs_le_padicNorm_int
#print axioms Sturmian.padicNorm_two_int_odd
#print axioms Sturmian.liouville_two_adic
#print axioms Sturmian.liouville_two_adic_real

-- Skeleton
#print axioms Sturmian.subsingleton_preimage
#print axioms Sturmian.strictMono_H_pick
#print axioms Sturmian.two_le_H_pick
#print axioms Sturmian.transcendental_of_approxExp
#print axioms Sturmian.not_approxExp_of_rat
#print axioms Sturmian.transcendental_of_ApproxExp
#print axioms Sturmian.ne_rat_of_ApproxExp
#print axioms Sturmian.one_lt_phi
#print axioms Sturmian.log2three_pos
#print axioms Sturmian.two_A_lt_one_add_phi
#print axioms Sturmian.approx_of_depth_height
