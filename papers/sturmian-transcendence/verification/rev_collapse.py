"""Where does the 1c_gamma route REALLY fail?
ice(1c_gamma) = 1 + limsup_{n ODD} q_{n+1}/q_n   (the even levels give E=1 exactly).
That limsup equals 1 -- i.e. ice(1c_gamma) = 2 and omega -> 1 -- iff a_{n+1}=1 for all large
odd n AND a_n -> infinity along odd n.  Family: gamma = [0; 2,1,4,1,8,1,16,1,...].
Contrast with [0;M,1,M,1,...] for FIXED M, where limsup_{n odd} q_{n+1}/q_n = 1 + 1/M > 1."""
from fractions import Fraction
import rev_core as R

def table(a, nm, NW=40000, which='1c'):
    cv=R.convergents(a); p,q=cv[min(40,len(cv)-1)]
    Nlo,Nhi,D=R.pin_rational(p,q,500)
    s=R.one_c_gamma(Nlo,Nhi,D,NW) if which=='1c' else R.c_gamma(Nlo,Nhi,D,NW)
    rows=[]
    for k in range(1,len(cv)-1):
        l=cv[k-1][1]; qk1=cv[k][1]
        if l+qk1+4>NW: break
        W=s[:l]
        if sum(W)==0: continue
        dep=R.lcp_pow(s,W)
        if dep>=len(s): continue
        Rj=R.phi_periodic_bruteforce(W); H=R.height(Rj)
        if H==1: continue
        hb=H.bit_length()
        rows.append((k,l,dep,Fraction(dep,l),Fraction(dep,hb)-1,Fraction(dep,max(hb-1,1))-1))
    if not rows: return None
    mx_lo=max(r[4] for r in rows); mx_hi=max(r[5] for r in rows)
    print("  %-34s [%s]  max omega_lo=%9.6f  max omega_hi=%9.6f   #levels=%d"%(nm,which,float(mx_lo),float(mx_hi),len(rows)))
    print("      (k,l,E=depth/l,omega_lo): %s"%("  ".join("(%d,%d,%.4f,%.4f)"%(r[0],r[1],float(r[3]),float(r[4])) for r in rows[:8])))
    return mx_lo, mx_hi

print("="*110)
print("A. [0;M,1,M,1,...] with FIXED M : the ORIGINAL's claimed collapse family")
print("="*110)
for M in (4,10,40,200,1000):
    a=[M,1]*120
    cv=R.convergents(a)
    # theoretical limsup over odd n of q_{n+1}/q_n
    ratios=[Fraction(cv[n][1],cv[n-1][1]) for n in range(1,60) if n%2==1]
    print("  M=%-5d  theoretical ice(1c) = 1 + limsup_{n odd} q_{n+1}/q_n = %.6f  => omega -> %.6f > 1"%(
        M, 1+float(max(ratios[-8:])), float(max(ratios[-8:]))))
    table(a, "[0;%d,1,%d,1,...]"%(M,M), 60000, '1c')
print()
print("="*110)
print("B. [0;2,1,4,1,8,1,16,...] : a_n -> infinity along ODD n, a_even = 1 -- the REAL failure family")
print("="*110)
a=[]
m=2
for i in range(26):
    a.append(m); a.append(1); m*=2
cv=R.convergents(a)
ratios=[(n,Fraction(cv[n][1],cv[n-1][1])) for n in range(1,22) if n%2==1]
print("  q_{n+1}/q_n at odd n :", ["%d:%.5f"%(n,float(r)) for n,r in ratios[:9]])
print("  => limsup_{n odd} q_{n+1}/q_n -> 1, so ice(1c_gamma) -> 2 and omega -> 1 : 1c-route FAILS")
print("  q_{k+1}/q_k over ALL k (limsup = infinity since a_k -> infinity):",
      ["%.4f"%float(Fraction(cv[k][1],cv[k-1][1])) for k in range(1,10)])
table(a, "[0;2,1,4,1,8,...]", 60000, '1c')
table(a, "[0;2,1,4,1,8,...]", 60000, 'c')
p,q=cv[30]; g=Fraction(p,q)
print("  gamma = %.8f  < gamma* = 0.82589777 : %s   => Theorem 1 applies via c_gamma"%(float(g), float(g)<0.82589777))
