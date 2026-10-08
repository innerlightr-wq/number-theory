import Sturmian

/-! `#print axioms` on every reported result of stages 1 and 2.  The permitted output is
the three standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) plus the three
named axioms declared in `Sturmian/Axioms.lean`:
`ridout_single_prime`, `bhz_prefix_family`, `cw_le_three_mul_len_mul_max`. -/

-- the three declared axioms
#print axioms Sturmian.ridout_single_prime
#print axioms Sturmian.bhz_prefix_family
#print axioms Sturmian.cw_le_three_mul_len_mul_max

-- STAGE 1: Basic
#print axioms Sturmian.H_pos
#print axioms Sturmian.finite_setOf_H_le
#print axioms Sturmian.exists_H_gt_of_infinite

-- STAGE 1: Liouville (PROVED; must NOT list any named axiom)
#print axioms Sturmian.one_div_abs_le_padicNorm_int
#print axioms Sturmian.padicNorm_two_int_odd
#print axioms Sturmian.liouville_two_adic
#print axioms Sturmian.liouville_two_adic_real

-- STAGE 1: Skeleton
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

-- STAGE 2: word combinatorics (PROVED)
#print axioms Sturmian.ones_succ
#print axioms Sturmian.cw_succ
#print axioms Sturmian.ones_cons_false_succ
#print axioms Sturmian.ones_cons_true_succ
#print axioms Sturmian.cw_cons_false_succ
#print axioms Sturmian.cw_cons_true_succ
#print axioms Sturmian.lcp_shift

-- STAGE 2: the 2-adic core (PROVED)
#print axioms Sturmian.norm_sub_eq_of_norm_lt
#print axioms Sturmian.norm_two
#print axioms Sturmian.norm_three
#print axioms Sturmian.IsBL.transfer
#print axioms Sturmian.IsBL.norm_cons_true
#print axioms Sturmian.IsBL.isometry
#print axioms Sturmian.IsBL.injective
#print axioms Sturmian.IsBL.affinegen

-- STAGE 2: the periodic shadow (PROVED)
#print axioms Sturmian.two_pow_ne_three_pow
#print axioms Sturmian.den_odd
#print axioms Sturmian.cw_pos
#print axioms Sturmian.shadow_eq
#print axioms Sturmian.shadow_formula
#print axioms Sturmian.shadowRat_den_odd
#print axioms Sturmian.shadowRat_inj_of_word_ne
#print axioms Sturmian.shadowSet_infinite

-- STAGE 2: the construction of Φ (PROVED — no existence axiom)
#print axioms Sturmian.isUnit_three
#print axioms Sturmian.three_mul_inv3
#print axioms Sturmian.norm_approx_succ_sub
#print axioms Sturmian.cauchySeq_approx
#print axioms Sturmian.norm_PhiBL_sub_approx
#print axioms Sturmian.approx_cons_false
#print axioms Sturmian.approx_cons_true
#print axioms Sturmian.isBL_PhiBL

-- STAGE 3: the Sturmian combinatorics (PROVED)
#print axioms Sturmian.inc_nonneg
#print axioms Sturmian.inc_le_one
#print axioms Sturmian.ones_charWord
#print axioms Sturmian.abs_ones_charWord_sub_lt_one
#print axioms Sturmian.H_div_le
#print axioms Sturmian.abs_den_lt_max
#print axioms Sturmian.logb_max_pow
#print axioms Sturmian.max_lt_A_mul
#print axioms Sturmian.ones_add
#print axioms Sturmian.shiftIter_mul_per
#print axioms Sturmian.ones_mul_per
#print axioms Sturmian.charWord_ne_per

-- STAGE 3: Proposition 2.4 -- an AXIOM at stage 2, a THEOREM now
#print axioms Sturmian.shadow_height_bound

-- STAGE 2: the assembly
#print axioms Sturmian.tendsto_errorTerm
#print axioms Sturmian.tendsto_two_rpow_neg
#print axioms Sturmian.isAlgebraic_affine
#print axioms Sturmian.transcendental_of_affine
#print axioms Sturmian.transcendental_cons_false
#print axioms Sturmian.transcendental_cons_true
#print axioms Sturmian.transcendental_of_prefix_family
#print axioms Sturmian.transcendental_charWord
#print axioms Sturmian.transcendental_PhiBL_charWord
#print axioms Sturmian.transcendental_PhiBL_mechanical
