"""PHASE 3, part 2:
 (i)  noble slopes straddling gamma* : omega must exceed 1 below and drop below 1 above;
 (ii) CONTROLS: a rational target and a quadratic irrational in Z_2 must stay at omega <= 1+o(1);
 (iii) the claimed '1c_gamma collapses to omega = 1' on [0;M,1,M,1,...] -- is it EXACTLY 1?
All exact. omega reported as the certified interval [dep/bitsH - 1, dep/(bitsH-1) - 1]."""
from fractions import Fraction
from decimal import Decimal, getcontext
from math import gcd, log2
import rev_core as R

getcontext().prec=60
PHI=(1+Decimal(5).sqrt())/2; L23=Decimal(3).ln()/Decimal(2).ln()
GSTAR=(1+PHI)/(2*L23)
print("gamma* = (3+sqrt5)/(4 log2 3) =", str(GSTAR)[:22])
print("(1+phi)/2 =", str((1+PHI)/2)[:22], "   log_3 2 =", str(1/L23)[:22])
print()
print("="*104); print("(i) NOBLE slopes (all-ones CF tail => ice = 1+phi EXACTLY: the worst case)"); print("="*104)
LOG23=Fraction(15850,10000)
def noble(head,reps=90): return head+[1]*reps
for head,nm in [([1],'[0;1,1,...]'),([1,4],'[0;1,4,1,1,...]'),([1,5],'[0;1,5,1,1,...]'),([1,8],'[0;1,8,1,1,...]')]:
    a=noble(head); cv=R.convergents(a); p,q=cv[60]
    Nlo,Nhi,D=R.pin_rational(p,q,400); NW=40000
    g=Fraction(p,q); A=max(Fraction(1),g*LOG23)
    s=R.c_gamma(Nlo,Nhi,D,NW)
    best=(Fraction(-99),0); rows=[]
    for k in range(1,len(cv)-1):
        l=cv[k-1][1]; qk1=cv[k][1]
        if l+qk1+4>NW: break
        W=s[:l]
        if sum(W)==0: continue
        dep=R.lcp_pow(s,W)
        if dep>=len(s): continue
        Rj=R.phi_periodic_bruteforce(W); H=R.height(Rj)
        if H==1: continue
        hb=H.bit_length(); rows.append((k,l,dep,hb,Fraction(dep,hb)-1,Fraction(dep,hb-1)-1))
        if rows[-1][4]>best[0]: best=(rows[-1][4],l)
    pred=float(1+PHI)/float(A)-1
    tail=rows[-3:]
    print("  %-18s gamma=%.8f  A<=%.6f  2A=%.5f  predicted limit (1+phi)/A-1 = %.6f"%(nm,float(g),float(A),2*float(A),pred))
    print("      last levels (k,l,depth,bitsH,omega_lo,omega_hi): %s"%
          ("  ".join("(%d,%d,%d,%d,%.5f,%.5f)"%(r[0],r[1],r[2],r[3],float(r[4]),float(r[5])) for r in tail)))
    print("      max omega_lo = %.6f   =>  %s"%(float(best[0]),
          "omega>1 : TRANSCENDENCE CERTIFIED" if best[0]>1 else "omega<=1 : METHOD GIVES NOTHING (expected above gamma*)"))
print()
print("="*104); print("(ii) CONTROLS"); print("="*104)
for W0 in ([1,1,0],[1,0,1,0,0],[1,1,0,1,0,0,1],[1,0,0,1,1,0,1,0,1]):
    s=(W0*(2500//len(W0)+2))[:2500]; tgt=R.phi_periodic_bruteforce(W0)
    best=(Fraction(-99),None); n=0
    for l in range(1,600):
        W=s[:l]
        if sum(W)==0: continue
        dep=R.lcp_pow(s,W)
        if dep>=len(s): continue
        Rj=R.phi_periodic_bruteforce(W)
        if Rj==tgt: continue
        H=R.height(Rj)
        if H==1: continue
        n+=1; om=Fraction(dep,H.bit_length()-1)-1 if H.bit_length()>1 else None   # UPPER bound on omega
        if om is not None and om>best[0]: best=(om,(l,dep,H))
    print("  rational target Phi(%s)=%-11s : %3d shadows, max omega_UPPER = %.5f at %s   %s"%(
        ''.join(map(str,W0)),str(tgt),n,float(best[0]),best[1],"OK (<=1+o(1))" if best[0]<=1.5 else "*** CHECK ***"))
def sqrt2adic(A,L):
    assert A%8==1
    r=1
    for m in range(3,L+1):
        if ((r*r-A)>>m)&1: r += 1<<(m-1)
    assert (r*r-A)%(1<<L)==0
    return r%(1<<L)
Lq=1400; Mq=1<<Lq; r17=sqrt2adic(17,Lq)
print("  quadratic target sqrt(17) in Z_2 : worst omega by dyadic height band (exhaustive, H<=1200)")
worst={}
for q in range(1,1201,2):
    iq=pow(q,-1,Mq)
    for p in range(-1200,1201):
        if p==0 or gcd(abs(p),q)!=1: continue
        H=max(abs(p),q)
        if H<2 or H>1200: continue
        d=(r17-p*iq)%Mq; v=Lq if d==0 else R.v2int(d)
        w=v/log2(H)-1; b=H.bit_length()-1
        if w>worst.get(b,(-99,))[0]: worst[b]=(w,p,q,v)
for b in sorted(worst):
    w,p,q,v=worst[b]; cap=1+log2(9)/ (b+1)
    print("     H in [2^%2d,2^%2d) : worst omega = %8.5f (p/q=%d/%d, v2=%d)   Liouville cap ~%.4f  %s"%(
        b,b+1,w,p,q,v,1+log2(9)/log2(2**b),"ok" if w<=1+log2(9)/log2(2**b)+1e-9 else "ABOVE"))
print()
print("="*104); print("(iii) the claimed '1c_gamma collapses to omega = 1' on [0;M,1,M,1,...]"); print("="*104)
for M in (4,10,40,200):
    a=[M,1]*200; cv=R.convergents(a); p,q=cv[150]
    Nlo,Nhi,D=R.pin_rational(p,q,400); NW=30000
    s1=R.one_c_gamma(Nlo,Nhi,D,NW)
    rows=[]
    for k in range(1,len(cv)-1):
        l=cv[k-1][1]; qk1=cv[k][1]
        if l+qk1+4>NW: break
        W=s1[:l]
        if sum(W)==0: continue
        dep=R.lcp_pow(s1,W)
        if dep>=len(s1): continue
        Rj=R.phi_periodic_bruteforce(W); H=R.height(Rj)
        if H==1: continue
        hb=H.bit_length()
        rows.append((k,l,dep,hb,Fraction(dep,hb)-1,Fraction(dep,hb-1)-1,Fraction(dep,l)))
    mx=max(r[4] for r in rows); mxhi=max(r[5] for r in rows)
    print("  M=%-4d  1c_gamma: max omega_lo=%.6f  max omega_hi=%.6f  (predicted limsup = 1/M-ish = %.6f)"%(
        M,float(mx),float(mxhi),1.0/M))
    print("          levels (k,l,depth,E=depth/l,omega_lo): %s"%
          ("  ".join("(%d,%d,%d,%.5f,%.5f)"%(r[0],r[1],r[2],float(r[6]),float(r[4])) for r in rows[:6])))
