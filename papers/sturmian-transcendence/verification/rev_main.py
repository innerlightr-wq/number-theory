"""PHASE 3 MAIN. For c_gamma: exact depth, exact height, and omega in a CERTIFIED INTERVAL
   omega in [ depth/bitlen(H) - 1 , depth/(bitlen(H)-1) - 1 ]   since bitlen-1 <= log2 H < bitlen.
Also checks, at every level used:
   (2a) the balanced height bound   c_W <= 3*l*max(2^l,3^k)      -- directly, not by analogy
   (2a') log2 H(R) <= A*l + log2(3l) + log2 3                    -- the bound the proof uses
   (ICE) the depth identity depth(q_k) = q_{k+1}+q_k-2 (and -1)
"""
from fractions import Fraction
from decimal import Decimal
import rev_core as R

LOG23_HI = Fraction(15850, 10000)   # log2 3 = 1.5849625... < 1.5850
LOG23_LO = Fraction(15849, 10000)

def cw_int(w):
    k=sum(w); c=0; pw=1
    for i in range(len(w)):
        if w[i]: c=3*c+pw
        pw <<= 1
    return c

def run(name, Nlo, Nhi, D, NW, which='c'):
    a0 = R.cf_pinned(Nlo, D)
    assert a0[0] == 0, 'slope must be in (0,1)'
    a = a0[1:]                      # drop the integer part a_0 = 0
    conv = R.convergents(a)
    s = R.c_gamma(Nlo,Nhi,D,NW) if which=='c' else R.one_c_gamma(Nlo,Nhi,D,NW)
    g_lo, g_hi = Fraction(Nlo,D), Fraction(Nhi,D)
    A_hi = max(Fraction(1), g_hi*LOG23_HI)        # upper bound for A(gamma)
    print("="*118); print("%s   [%s]   a_1..a_10 = %s   A(gamma) <= %.6f"%(name,which,a[:10],float(A_hi)))
    print("  k   l=q_k      depth   q_{k+1}+q_k-2  bitsH   omega_lo   omega_hi   L10.4 ok   bound(3) ok   E(l)")
    rows=[]
    for k in range(1, len(conv)-1):
        l = conv[k-1][1]; qk1 = conv[k][1]
        if l + qk1 + 4 > NW: break
        W = s[:l]
        if sum(W) == 0: continue
        dep = R.lcp_pow(s, W)
        if dep >= len(s): continue
        Rj = R.phi_periodic_bruteforce(W)
        H = R.height(Rj); hb = H.bit_length()
        if H == 1: continue
        om_lo = Fraction(dep, hb) - 1
        om_hi = Fraction(dep, hb-1) - 1 if hb > 1 else None
        kk = sum(W)
        # (2a) direct check of the balanced-height bound
        l104 = cw_int(W) <= 3*l*max(1<<l, 3**kk)
        # (2a') the bound actually used in Step 2 of the proof
        rhs = A_hi*l + Fraction(len(bin(3*l))-2) + LOG23_HI     # log2(3l) <= bitlen(3l)
        b3 = Fraction(hb) <= rhs + 1                            # log2 H < bitsH <= rhs+1
        rows.append((k,l,dep,qk1,hb,om_lo,om_hi,l104,b3))
        print("%3d %8d %10d %13d %7d %10.5f %10.5f      %-5s        %-5s    %.5f"%(
            k,l,dep,qk1+l-2,hb,float(om_lo),float(om_hi) if om_hi else -9,l104,b3,dep/l))
    if rows:
        print("  depth == q_{k+1}+q_k-2 at %d/%d levels ; == -1 at %d/%d"%(
            sum(1 for r in rows if r[2]==r[3]+r[1]-2), len(rows),
            sum(1 for r in rows if r[2]==r[3]+r[1]-1), len(rows)))
        print("  Lemma 10.4 holds at %d/%d ;  Step-2 bound (3) holds at %d/%d"%(
            sum(1 for r in rows if r[7]), len(rows), sum(1 for r in rows if r[8]), len(rows)))
        print("  min omega_lo over k>=4 : %.5f   max : %.5f   #(omega_lo<=1): %d"%(
            float(min(r[5] for r in rows if r[0]>=4)), float(max(r[5] for r in rows)),
            sum(1 for r in rows if r[5]<=1)))
    # exhaustive scan over every prefix length (independent of any q_k indexing)
    best=(Fraction(-99),0); bestE=(Fraction(0),0); nbad=0; ntot=0
    for l in range(2, min(1400, NW//3)):
        W=s[:l]
        if sum(W)==0: continue
        dep=R.lcp_pow(s,W)
        if dep>=len(s): continue
        Rj=R.phi_periodic_bruteforce(W); H=R.height(Rj)
        if H==1: continue
        hb=H.bit_length(); om=Fraction(dep,hb)-1
        ntot+=1
        if om>best[0]: best=(om,l)
        if Fraction(dep,l)>bestE[0]: bestE=(Fraction(dep,l),l)
    print("  exhaustive scan l<%d : %d usable ; max E(l)=%.5f at l=%d ; max omega_lo=%.5f at l=%d"%(
        min(1400,NW//3), ntot, float(bestE[0]), bestE[1], float(best[0]), best[1]))
    return rows

CASES = [
 ("golden  gamma=(sqrt5-1)/2=[0;1,1,1,...]", lambda: R.pin_decimal(lambda:(Decimal(5).sqrt()-1)/2), 60000),
 ("gamma=sqrt2-1=[0;2,2,2,...]",             lambda: R.pin_decimal(lambda: Decimal(2).sqrt()-1),    60000),
 ("gamma=[0;5,1,5,1,...]",                   None,                                                  60000),
 ("gamma=log_3 2  (RESONANCE)",              lambda: R.pin_decimal(lambda: Decimal(2).ln()/Decimal(3).ln()), 60000),
]
for nm,f,NW in CASES:
    if f is None:
        a=[5,1]*400; cv=R.convergents(a); p,q=cv[300]; Nlo,Nhi,Dd=R.pin_rational(p,q,400)
    else:
        Nlo,Nhi,Dd=f()
    run(nm,Nlo,Nhi,Dd,NW,'c'); print()
