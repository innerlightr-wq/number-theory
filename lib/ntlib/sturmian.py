"""Sturmian / characteristic words with certified slope intervals.

A slope is carried as a pinned integer interval (Nlo, Nhi, D) with Nlo/D < gamma < Nhi/D.
Every floor used to build a word is computed at both endpoints and the two must agree;
otherwise the slope precision is exhausted and we raise rather than guess.
"""
__all__ = ["pin_rational", "pin_decimal", "c_gamma", "one_c_gamma", "lcp_pow",
           "prefix_power", "max_periodic_prefix"]


def pin_rational(num, den, Ddig=400):
    """Pin a rational slope to an integer interval of denominator 10^Ddig."""
    D = 10 ** Ddig
    N = (num * D) // den
    return N, N + 1, D


def pin_decimal(dec, Ddig=400):
    """Pin a slope given as a zero-argument callable returning a Decimal."""
    from decimal import getcontext
    getcontext().prec = Ddig + 60
    x = dec()
    ip, _, fr = str(+x).partition('.')
    fr = (fr + '0' * Ddig)[:Ddig]
    N = int(ip + fr)
    return N, N + 1, 10 ** Ddig


def c_gamma(Nlo, Nhi, D, NW):
    """Characteristic word c_gamma(j) = floor((j+1)g) - floor(jg), j = 1..NW."""
    fl = [(j * Nlo) // D for j in range(NW + 3)]
    fh = [(j * Nhi) // D for j in range(NW + 3)]
    if fl != fh:
        raise ValueError("slope precision exhausted; increase Ddig")
    return [fl[j + 1] - fl[j] for j in range(1, NW + 1)]


def one_c_gamma(Nlo, Nhi, D, NW):
    """1c_gamma = 1 followed by c_gamma."""
    return [1] + c_gamma(Nlo, Nhi, D, NW - 1)


def lcp_pow(s, u):
    """lcp(s, u^infty), without materialising u^infty."""
    l = len(u)
    i = 0
    while i < len(s) and s[i] == u[i % l]:
        i += 1
    return i


def prefix_power(s, u):
    """The prefix power of u in s: lcp(s, u^infty)/|u|."""
    return lcp_pow(s, u) / len(u)


def max_periodic_prefix(s, P):
    """Length of the longest P-periodic prefix of s.

    Equals max over words u of length P of lcp(s, u^infty), the maximum being attained
    at u = s[:P].
    """
    i = P
    while i < len(s) and s[i] == s[i - P]:
        i += 1
    return i
