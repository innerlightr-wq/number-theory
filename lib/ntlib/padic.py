"""Exact 2-adic arithmetic and the Bernstein-Lagarias conjugacy map.

Phi is built from the parity-vector definition only. With T(x)=(3x+1)/2 for x odd,
T(x)=x/2 for x even, and sigma the word shift, T(Phi(v)) = Phi(sigma v); inverting T on
the branch selected by v_0 gives

    Phi(v) = 2*Phi(sigma v)              if v_0 = 0,
    Phi(v) = (2*Phi(sigma v) - 1)/3      if v_0 = 1.

Nothing is assumed about the closed form -sum 3^{-k_{i+1}} 2^i or about c_w/(2^l - 3^k);
both are checked against this.  Exact integer arithmetic only.
"""
from fractions import Fraction

__all__ = ["phi_mod", "phi_periodic", "v2int", "v2frac", "height", "c_w"]


def phi_mod(v, L):
    """Phi(v) mod 2^L, from the parity-vector definition only.  Requires len(v) >= L."""
    if len(v) < L:
        raise ValueError("need at least L letters to determine Phi(v) mod 2^L")
    z = 0                                   # Phi(sigma^L v) mod 2^0
    for i in range(L - 1, -1, -1):
        M = 1 << (L - i)
        z = (2 * z) % M if v[i] == 0 else ((2 * z - 1) * pow(3, -1, M)) % M
    return z


def phi_periodic(w):
    """Phi(w^infty) as an exact Fraction, without using the c_w formula.

    Composing the inverse-T branches along one period gives an affine map x -> a*x + b
    with a = 2^l/3^k; Phi(w^infty) is its unique fixed point b/(1-a).
    """
    l, k = len(w), sum(w)
    a, b = Fraction(1), Fraction(0)
    for i in range(l - 1, -1, -1):
        if w[i] == 0:
            a, b = 2 * a, 2 * b
        else:
            a, b = Fraction(2, 3) * a, Fraction(2, 3) * b - Fraction(1, 3)
    assert a == Fraction(1 << l, 3 ** k)
    return b / (1 - a)


def c_w(w):
    """c_w = sum_{i<l, w_i=1} 3^{k-k_{i+1}(w)} 2^i, the numerator of the closed form."""
    k = sum(w)
    tot = kk = 0
    for i, wi in enumerate(w):
        if wi == 1:
            kk += 1
            tot += 3 ** (k - kk) * 2 ** i
    return tot


def v2int(n):
    """2-adic valuation of a nonzero integer; None for 0."""
    if n == 0:
        return None
    c = 0
    while n % 2 == 0:
        n //= 2
        c += 1
    return c


def v2frac(x):
    """2-adic valuation of a nonzero Fraction; None for 0."""
    if x == 0:
        return None
    return v2int(x.numerator) - v2int(x.denominator)


def height(x):
    """Weil height max(|num|, den) of a Fraction in lowest terms."""
    return max(abs(x.numerator), x.denominator)
