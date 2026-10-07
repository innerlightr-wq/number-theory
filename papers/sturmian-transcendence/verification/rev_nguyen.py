"""Does Nguyen (arXiv 2605.30606) Theorem A apply DIRECTLY to Phi(c_gamma)?
Theorem A needs xi = sum_{i>=0} a_i beta^{-i} with a_i in O_{K,S}, h(a_i) = o(i),
|beta|_v > 1 and Rdio(a) > log H(beta)/log|beta|_v.
The only coordinate with |beta|_2 > 1 is beta = 1/2, a_i = v_i * 3^{-k_{i+1}(v)}.
Check h(a_i) exactly."""
from fractions import Fraction
from decimal import Decimal
import rev_core as R
Nlo,Nhi,D = R.pin_decimal(lambda: Decimal(2).ln()/Decimal(3).ln(), 400)
s = R.c_gamma(Nlo,Nhi,D,4000)
k=0; rows=[]
for i in range(4000):
    if s[i]: k+=1
    if i+1 in (50,100,200,400,800,1600,3200):
        # a_i = v_i * 3^{-k_{i+1}};  h(a_i) = log H(a_i) = k_{i+1} * log 3  (num=1, den=3^k)
        rows.append((i+1,k))
print("Phi(v) = -sum_i a_i (1/2)^{-i} with a_i = v_i * 3^{-k_{i+1}(v)} :")
print("   i      k_{i+1}   H(a_i)=3^{k}   log2 H(a_i)   (log2 H)/i   -> must be o(1) for h(a_i)=o(i)")
for i,kk in rows:
    hb = (3**kk).bit_length()
    print("  %5d %8d      3^%-7d %12d %12.6f"%(i,kk,kk,hb,hb/i))
print()
print("  (log2 H(a_i))/i tends to gamma*log2 3 = %.6f, NOT to 0."%float(Fraction(Nlo,D)*Fraction(15850,10000)))
print("  => h(a_i) is LINEAR in i.  Nguyen Theorem A's hypothesis h(a_i)=o(i) FAILS.")
print("  Also: in the one-indexed coordinate Phi = -sum_j 3^{-j} 2^{n_j} the base is beta=3 with")
print("  |3|_2 = 1, NOT > 1, so that coordinate is inadmissible for Theorem A regardless of heights.")
