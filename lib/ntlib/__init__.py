"""ntlib - exact arithmetic for 2-adic / Sturmian number theory.

Exact integer and Fraction arithmetic throughout.  No floating-point number decides any
inequality anywhere in this package.
"""
from .padic import phi_mod, phi_periodic, c_w, v2int, v2frac, height
from .sturmian import (pin_rational, pin_decimal, c_gamma, one_c_gamma, lcp_pow,
                       prefix_power, max_periodic_prefix)
from .cf import cf_pinned, convergents

__version__ = "0.1.0"
__all__ = ["phi_mod", "phi_periodic", "c_w", "v2int", "v2frac", "height",
           "pin_rational", "pin_decimal", "c_gamma", "one_c_gamma", "lcp_pow",
           "prefix_power", "max_periodic_prefix", "cf_pinned", "convergents"]
