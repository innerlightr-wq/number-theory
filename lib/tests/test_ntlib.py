"""Tests for ntlib: each reproduces a value stated in
papers/sturmian-transcendence (Transcendence of the 3x+1 conjugacy map on Sturmian words,
doi:10.5281/zenodo.23210794).  Exact arithmetic only.

Run:  python3 tests/test_ntlib.py     (no pytest required)
"""
import os, sys
from fractions import Fraction
from decimal import Decimal, getcontext
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from ntlib import (phi_mod, phi_periodic, c_w, v2int, v2frac, height, pin_decimal,
                   c_gamma, one_c_gamma, lcp_pow, max_periodic_prefix, cf_pinned,
                   convergents)

FAIL = []
def check(name, cond, detail=""):
    print(("  PASS  " if cond else "  FAIL  ") + name + ("" if cond else "   " + detail))
    if not cond:
        FAIL.append(name)

def log3_2(D=400):
    getcontext().prec = D + 60
    return pin_decimal(lambda: Decimal(2).ln() / Decimal(3).ln(), D)

print("ntlib tests")

# --- Prop 2.1 isometry: v2(Phi(v)-Phi(w)) = lcp(v,w) ------------------------------
Nlo, Nhi, D = log3_2()
c = c_gamma(Nlo, Nhi, D, 400)
L = 300
for cut in (37, 120, 211):
    w = c[:cut] + [1 - c[cut]] + c[cut + 1:]
    d = (phi_mod(c, L) - phi_mod(w, L)) % (1 << L)
    check("isometry: v2(Phi(c)-Phi(w)) = lcp = %d" % cut, v2int(d) == cut,
          "got %s" % v2int(d))

# --- Prop 2.4 periodic value: Phi(w^inf) = c_w/(2^l - 3^k) ------------------------
for w in ([1,0,1], [1,1,0,1,0], c[:19], c[:84]):
    lhs = phi_periodic(w)
    rhs = Fraction(c_w(w), 2 ** len(w) - 3 ** sum(w))
    check("periodic value, l=%d" % len(w), lhs == rhs)

# --- depth identity  lcp(c_gamma, W^inf) = q_{k+1} + q_k - 2  (Appendix B) --------
a = cf_pinned(Nlo, D)[1:]          # drop a_0 = 0
conv = convergents(a)   # conv[i] = p_{i+1}/q_{i+1} in the paper's Convention 2.6 indexing
c_long = c_gamma(Nlo, Nhi, D, 30000)
rows = []
for k in range(2, 10):
    q, q1 = conv[k][1], conv[k + 1][1]
    if q1 >= len(c_long) // 2:
        break
    dep = max_periodic_prefix(c_long, q)
    rows.append((q, q1, dep))
    check("depth law at q_%d=%d (%s)" % (k+1, q, "odd" if (k+1) % 2 else "even"),
          dep == q + q1 - 2, "got %d want %d" % (dep, q + q1 - 2))
check("depth law checked at >= 6 levels, both parities", len(rows) >= 6)

# --- Step-2 height bound (9):  log2 H < A*l + log2(3l) + log2 3 -------------------
import math
A = 1.0                                   # A(gamma) = 1 at gamma = log_3 2
ok = True
for q, q1, dep in rows:
    W = c_long[:q]
    R = phi_periodic(W)
    H = height(R)
    lh = (H.bit_length() - 1) + math.log2(H / (1 << (H.bit_length() - 1)))
    if not lh < A * q + math.log2(3 * q) + math.log2(3):
        ok = False
check("height bound (9) at every level used", ok)

# --- c_W <= 3 l max(2^l, 3^k)  (Prop 2.9 input) -----------------------------------
check("c_W <= 3 l max(2^l,3^k)",
      all(c_w(c_long[:q]) <= 3 * q * max(2 ** q, 3 ** sum(c_long[:q])) for q, _, _ in rows))

# --- Remark 3.3 sign check: Phi(1c_beta) = -Xi_alpha = +Xi_{alpha,0} ---------------
M = 600
one_c = one_c_gamma(Nlo, Nhi, D, 4000)
phi1c = phi_mod(one_c, M)
mod = 1 << M
# alpha = log_2 3 ; floor(j*alpha) via exact integer comparison: 2^m <= 3^j < 2^{m+1}
def fl_alpha(j):
    return 0 if j == 0 else (3 ** j).bit_length() - 1
inv3 = pow(3, -1, mod)
Xi = 0
for j in range(0, 2 * M):
    s = fl_alpha(j)
    if s >= M:
        break
    Xi = (Xi + pow(inv3, j + 1, mod) * pow(2, s, mod)) % mod
check("Remark 3.3: Phi(1c_beta) = -Xi_alpha  (mod 2^600)", phi1c == (-Xi) % mod)
check("Remark 3.3: opposite sign fails",        phi1c != Xi % mod)
check("Remark 3.3: v2(Phi(1c_beta)) = 0",       v2int(phi1c) == 0)

# --- eq (10) affine transfer: 2 Phi(c) = 3 Phi(1c) + 1 = Phi(0c) ------------------
zero_c = [0] + c_gamma(Nlo, Nhi, D, 3999)
phic, phi0c = phi_mod(c_long[:4000], M), phi_mod(zero_c, M)
check("2 Phi(c) = Phi(0c)        (mod 2^600)", (2 * phic) % mod == phi0c)
check("2 Phi(c) = 3 Phi(1c) + 1  (mod 2^600)", (2 * phic) % mod == (3 * phi1c + 1) % mod)

# --- gamma* and the ice floor ------------------------------------------------------
getcontext().prec = 60
import decimal
phi_g = (1 + Decimal(5).sqrt()) / 2
gs = (3 + Decimal(5).sqrt()) / (4 * (Decimal(3).ln() / Decimal(2).ln()))
check("gamma* = 0.8258977696818354644 (19 dp)", str(+gs)[:21] == "0.8258977696818354644",
      str(+gs)[:21])
check("ice floor 1+phi > 2", phi_g + 1 > 2)

print()
if FAIL:
    print("FAILED: %d" % len(FAIL)); sys.exit(1)
print("all tests passed")
