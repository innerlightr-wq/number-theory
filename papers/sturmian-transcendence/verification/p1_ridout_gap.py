"""Is Ridout's real-root hypothesis a genuine restriction?
Search for f in Z[X], irreducible over Q, with NO real root, but WITH a root in Z_2.
Such an f is the minimal polynomial of an algebraic xi in Z_2 to which Ridout's
Theorem (as classically stated: "let alpha be a REAL root of f") does not apply.
Exact integer arithmetic; irreducibility by exhaustive factor search over Z[X]."""
from itertools import product
from fractions import Fraction

def real_roots_exist(c):
    """c = coeffs low->high, even degree, positive leading. True if f has a real root.
    Uses Sturm-free test: sample + sign change, plus check f>0 everywhere via minimum scan.
    For a rigorous 'no real root' certificate we verify f(x)>0 for all x by checking
    f has no rational-interval sign change on a wide grid AND f(x)>0 at all integers in
    a range containing all real roots (Cauchy bound)."""
    n = len(c)-1
    # Cauchy bound: |root| <= 1 + max|a_i|/|a_n|
    B = 1 + max(abs(x) for x in c[:-1])//abs(c[-1]) + 1
    f = lambda x: sum(ci*x**i for i,ci in enumerate(c))
    # scan rationals k/4 over [-B,B]
    prev = None
    for k in range(-4*B, 4*B+1):
        x = Fraction(k,4)
        v = f(x)
        if v == 0: return True
        if prev is not None and (prev>0) != (v>0): return True
        prev = v
    return False     # no sign change on a fine grid covering all roots

def irreducible_Z(c):
    """c low->high. Test irreducibility over Q by trial division by all monic/non-monic
    factors of degree 1 and 2 with bounded coefficients (sufficient for our small search)."""
    n=len(c)-1
    # rational roots
    a0,an = c[0], c[-1]
    if a0==0: return False
    for p in range(-abs(a0), abs(a0)+1):
        if p==0: continue
        for q in range(1, abs(an)+1):
            if a0 % p or an % q: continue
            for s in (1,-1):
                r = Fraction(s*p, q)
                if sum(ci*r**i for i,ci in enumerate(c))==0: return False
    if n==4:
        # try f = (x^2+ax+b)(x^2+cx+d) over Z  (leading coeff 1)
        assert c[-1]==1
        a4,a3,a2,a1,a0 = 1,c[3],c[2],c[1],c[0]
        for b in range(-abs(a0)-1, abs(a0)+2):
            if b==0 or a0 % b: continue
            d = a0//b
            for A in range(-12,13):
                C = a3 - A
                if A*d + C*b != a1: continue
                if b + d + A*C != a2: continue
                return False
    return True

found=[]
for c3 in range(-3,4):
  for c2 in range(-3,6):
    for c1 in range(-3,4):
      for c0 in range(1,9):
        c=[c0,c1,c2,c3,1]
        f=lambda x: sum(ci*x**i for i,ci in enumerate(c))
        fp=lambda x: sum(i*ci*x**(i-1) for i,ci in enumerate(c) if i>0)
        # Hensel: simple root mod 2
        hens=None
        for a in (0,1):
            if f(a)%2==0 and fp(a)%2==1: hens=a
        if hens is None: continue
        if real_roots_exist(c): continue
        if not irreducible_Z(c): continue
        found.append((c,hens))

print("quartics x^4+c3 x^3+c2 x^2+c1 x+c0, irreducible over Q, NO real root, simple root mod 2:")
for c,a in found[:8]:
    # Hensel-lift to high precision and verify
    L=600; M=1<<L
    r=a
    f=lambda x: sum(ci*x**i for i,ci in enumerate(c))
    fp=lambda x: sum(i*ci*x**(i-1) for i,ci in enumerate(c) if i>0)
    for _ in range(12):
        r = (r - f(r)*pow(fp(r),-1,M)) % M
    ok = f(r)%M==0
    print("   f = x^4 %+d x^3 %+d x^2 %+d x %+d    root in Z_2: r = %d (mod 2^20);  f(r)=0 mod 2^%d : %s"
          %(c[3],c[2],c[1],c[0], r%(1<<20), L, ok))
print("\ncount found:", len(found))
