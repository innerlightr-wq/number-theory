"""SIGN CHECK, exact. Two definitions in play:
 [P1] Prop 3.2 :  Xi_alpha        =  + sum_{j>=0} 3^{-(j+1)} 2^{floor(j*alpha)}       (no minus)
                  claim: Phi(1c_beta) = - Xi_alpha
 [P3] Thm 4.1  :  Xi_{alpha,b}    =  - sum_{i>=0} 3^{-i-1} 2^{floor(i*alpha + b)}     (minus built in)
Phi is computed from the parity-vector definition only (rev_core), independent of both."""
from decimal import Decimal, getcontext
import rev_core as R

L = 3000
Nlo,Nhi,D = R.pin_decimal(lambda: Decimal(3).ln()/Decimal(2).ln(), 500)   # alpha = log_2 3
Blo,Bhi,DB = R.pin_decimal(lambda: Decimal(2).ln()/Decimal(3).ln(), 500)  # beta  = log_3 2
M = 1 << L

def series_P1(L):
    """+ sum_j 3^{-(j+1)} 2^{floor(j*alpha)} mod 2^L, certified floors."""
    tot = 0; j = 0
    while True:
        lo = (j*Nlo)//D; hi = (j*Nhi)//D
        assert lo == hi, "precision exhausted at j=%d" % j
        if lo >= L: break
        tot = (tot + pow(pow(3, j+1, M), -1, M) * pow(2, lo, M)) % M
        j += 1
    return tot, j

A, nterms = series_P1(L)                    # [P1] Xi_alpha
P3 = (-A) % M                               # [P3] Xi_{alpha,0}
s  = R.one_c_gamma(Blo,Bhi,DB, L+60)        # 1c_beta, beta = log_3 2
PH = R.phi_mod(s, L)                        # Phi(1c_beta), from first principles

print("terms summed: %d ;  modulus 2^%d" % (nterms, L))
print()
print("  Phi(1c_beta) == - Xi_alpha        ([P1] Prop 3.2 convention) :", PH == P3)
print("  Phi(1c_beta) == + Xi_alpha                                   :", PH == A)
print()
print("  Phi(1c_beta) == + Xi_{alpha,0}    ([P3] Thm 4.1 convention)  :", PH == P3)
print("  Phi(1c_beta) == - Xi_{alpha,0}                               :", PH == A)
print()
print("  Xi_{alpha,0}^[P3] == - Xi_alpha^[P1] :", P3 == (-A) % M)
print()
print("  low 24 bits:  Phi(1c_beta) = %7d   Xi_alpha^[P1] = %7d   Xi_{alpha,0}^[P3] = %7d"
      % (PH % (1<<24), A % (1<<24), P3 % (1<<24)))
print("  v_2(Phi(1c_beta)) =", R.v2int(PH), " (expect 0: a 2-adic unit)")
