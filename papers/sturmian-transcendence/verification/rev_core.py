"""INDEPENDENT implementation. Phi is built from FIRST PRINCIPLES:
Bernstein-Lagarias: T(x)=(3x+1)/2 for x odd, x/2 for x even; Phi(v) is the unique x in Z_2
whose parity vector is v.  Hence, with sigma the word shift,
        T(Phi(v)) = Phi(sigma v),
so inverting T on the branch selected by v_0:
        Phi(v) = 2*Phi(sigma v)             if v_0 = 0,
        Phi(v) = (2*Phi(sigma v) - 1)/3     if v_0 = 1.
Reading this backwards gives Phi(v) mod 2^L from L letters.  NOTHING is assumed about the
closed form -sum 3^{-k_{i+1}} 2^i or about c_w/(2^l-3^k); both are CHECKED against this.
Exact integer arithmetic only."""
from fractions import Fraction

def phi_mod(v, L):
    """Phi(v) mod 2^L, from the parity-vector definition only. Needs len(v) >= L."""
    assert len(v) >= L
    z = 0                                   # Phi(sigma^L v) mod 2^0
    for i in range(L-1, -1, -1):
        M = 1 << (L - i)
        z = (2*z) % M if v[i] == 0 else ((2*z - 1) * pow(3, -1, M)) % M
    return z

def v2int(n):
    if n == 0: return None
    c = 0
    while n % 2 == 0: n //= 2; c += 1
    return c

def v2frac(x):
    if x == 0: return None
    return v2int(x.numerator) - v2int(x.denominator)

def lcp_pow(s, u):
    """lcp(s, u^infty) without materialising u^infty."""
    l = len(u); i = 0
    while i < len(s) and s[i] == u[i % l]: i += 1
    return i

def phi_periodic_bruteforce(w, L=None):
    """Phi(w^infty) as an exact Fraction, found WITHOUT the c_w formula:
    Phi(w^infty) is the unique fixed point of the affine map obtained by composing the
    inverse-T branches along w.  Composing x -> 2x (letter 0) and x -> (2x-1)/3 (letter 1)
    over one period gives an affine map x -> a*x + b with a = 2^l/3^k; the fixed point is
    b/(1-a).  (This is read off the same recursion as phi_mod, not from any closed form.)"""
    l = len(w); k = sum(w)
    # compose along the period, from the deep end backwards: F(x) = a x + b
    a, b = Fraction(1), Fraction(0)
    for i in range(l-1, -1, -1):
        if w[i] == 0: a, b = 2*a, 2*b
        else:         a, b = Fraction(2,3)*a, Fraction(2,3)*b - Fraction(1,3)
    assert a == Fraction(1 << l, 3**k)
    return b / (1 - a)

def height(x):
    return max(abs(x.numerator), x.denominator)

# ---- certified Sturmian words ----
def pin_rational(num, den, Ddig=400):
    D = 10**Ddig; N = (num*D)//den
    return N, N+1, D

def pin_decimal(dec, Ddig=400):
    from decimal import getcontext
    getcontext().prec = Ddig + 60
    x = dec()
    ip,_,fr = str(+x).partition('.'); fr = (fr + '0'*Ddig)[:Ddig]
    N = int(ip+fr); return N, N+1, 10**Ddig

def c_gamma(Nlo, Nhi, D, NW):
    """characteristic word c_gamma(j) = floor((j+1)g) - floor(jg), j = 1,2,...  (j starts at 1)."""
    fl = [(j*Nlo)//D for j in range(NW+3)]
    fh = [(j*Nhi)//D for j in range(NW+3)]
    assert fl == fh, "slope precision exhausted"
    return [fl[j+1]-fl[j] for j in range(1, NW+1)]

def one_c_gamma(Nlo, Nhi, D, NW):
    """1c_gamma = 1 followed by c_gamma."""
    return [1] + c_gamma(Nlo, Nhi, D, NW-1)

def cf_pinned(N, D, maxt=3000):
    out=[]; alo,ahi=N,N+1; dlo,dhi=D,D
    for _ in range(maxt):
        q1,q2 = alo//dlo, ahi//dhi
        if q1 != q2: return out
        out.append(q1); alo -= q1*dlo; ahi -= q2*dhi
        if alo <= 0 or ahi <= 0: return out
        alo,dlo,ahi,dhi = dhi,ahi,dlo,alo
    return out

def convergents(a):
    """a = [a_1,a_2,...]; returns [(p_1,q_1),(p_2,q_2),...] for [0;a_1,a_2,...]."""
    pm,qm = 1,0; p0,q0 = 0,1; out=[]
    for ai in a:
        p1,q1 = ai*p0+pm, ai*q0+qm
        out.append((p1,q1)); pm,qm,p0,q0 = p0,q0,p1,q1
    return out
