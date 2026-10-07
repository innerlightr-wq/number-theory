"""Rigorous certificate: an algebraic xi in Z_2 whose minimal polynomial has NO real root.
- real root count by STURM's theorem in exact rational arithmetic;
- irreducibility over Q by complete search over integer quadratic factorisations
  (Gauss: a monic integer quartic reducible over Q factors into monic integer factors)
  plus the rational root test;
- the 2-adic root by Hensel lifting, verified exactly."""
from fractions import Fraction as F

def polydiv(a,b):
    a=a[:]; out=[F(0)]*(max(0,len(a)-len(b)+1))
    while len(a)>=len(b) and any(x!=0 for x in a):
        if a[-1]==0: a.pop(); continue
        q=a[-1]/b[-1]; d=len(a)-len(b); out[d]=q
        for i,bi in enumerate(b): a[i+d]-=q*bi
        while a and a[-1]==0: a.pop()
    return out,a
def deriv(c): return [F(i)*c[i] for i in range(1,len(c))]
def sturm_chain(c):
    c=[F(x) for x in c]; ch=[c, deriv(c)]
    while len(ch[-1])>1:
        _,r=polydiv(ch[-2],ch[-1])
        if not r or all(x==0 for x in r): break
        ch.append([-x for x in r])
    return ch
def signs_at(ch,x):
    s=[]
    for p in ch:
        v=sum(ci*x**i for i,ci in enumerate(p))
        s.append(0 if v==0 else (1 if v>0 else -1))
    return s
def sign_at_inf(ch,sgn):
    s=[]
    for p in ch:
        lead=p[-1]; d=len(p)-1
        v=lead*(sgn**d)
        s.append(0 if v==0 else (1 if v>0 else -1))
    return s
def varia(s):
    t=[x for x in s if x!=0]; return sum(1 for i in range(len(t)-1) if t[i]!=t[i+1])
def n_real_roots(c):
    ch=sturm_chain(c)
    return varia(sign_at_inf(ch,-1)) - varia(sign_at_inf(ch,1))

def rational_roots_none(c):
    a0,an=c[0],c[-1]
    for p in range(1,abs(a0)+1):
        if a0%p: continue
        for q in range(1,abs(an)+1):
            if an%q: continue
            for s in (1,-1):
                r=F(s*p,q)
                if sum(F(ci)*r**i for i,ci in enumerate(c))==0: return False
    return True

def no_quadratic_factor(c):
    """c monic quartic, low->high. Reducible into two integer quadratics?
    (x^2+Ax+B)(x^2+Cx+D): B*D=a0, A+C=a3, B+D+A*C=a2, A*D+C*B=a1."""
    a0,a1,a2,a3=c[0],c[1],c[2],c[3]
    for B in range(-abs(a0),abs(a0)+1):
        if B==0 or a0%B: continue
        D=a0//B
        for A in range(-40,41):
            C=a3-A
            if B+D+A*C==a2 and A*D+C*B==a1: return False
    return True

C=[6,2,0,-3,1]   # x^4 - 3x^3 + 2x + 6
nr=n_real_roots(C)
print("f(x) = x^4 - 3x^3 + 2x + 6")
print("  Sturm real-root count            :", nr, "  (0 => totally complex)")
print("  no rational root                 :", rational_roots_none(C))
print("  no integer quadratic factor      :", no_quadratic_factor(C))
print("  => irreducible over Q            :", nr==0 and rational_roots_none(C) and no_quadratic_factor(C))
L=800; M=1<<L
f  = lambda x: sum(ci*x**i for i,ci in enumerate(C))
fp = lambda x: sum(i*ci*x**(i-1) for i,ci in enumerate(C) if i>0)
a0h = next(a for a in (0,1) if f(a)%2==0 and fp(a)%2==1)
print("  Hensel seed a=%d : f(a) mod 2 = %d, f'(a) mod 2 = %d  -> simple root mod 2"%(a0h,f(a0h)%2,fp(a0h)%2))
r=a0h
for _ in range(14): r=(r-f(r)*pow(fp(r),-1,M))%M
print("  2-adic root r (mod 2^24)         :", r%(1<<24))
print("  f(r) = 0 mod 2^%d                : %s"%(L, f(r)%M==0))
print()
print("CONCLUSION: xi := r is an algebraic number of degree 4 lying in Z_2 whose minimal")
print("polynomial has NO real root. Ridout's theorem as classically stated ('let alpha be a")
print("REAL root of f') therefore does not literally apply to this xi.  The pure 2-adic")
print("statement must be obtained from the p-adic Subspace Theorem instead (see PHASE1.md).")
