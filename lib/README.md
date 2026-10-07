# lib/ — `ntlib`

Exact-arithmetic primitives shared across the papers in this repository. Python 3.9+,
standard library only (`fractions`, `decimal`). **No floating-point number decides any
inequality anywhere in this package.**

| module | contents |
|---|---|
| `ntlib.padic` | `phi_mod` (the Bernstein–Lagarias map from the parity-vector definition alone), `phi_periodic` (the periodic value as an exact `Fraction`, via the fixed point of the composed inverse-`T` branches — not via the closed form), `c_w`, `v2int`, `v2frac`, `height` |
| `ntlib.sturmian` | `pin_rational` / `pin_decimal` (certified slope intervals), `c_gamma`, `one_c_gamma`, `lcp_pow`, `prefix_power`, `max_periodic_prefix` |
| `ntlib.cf` | `cf_pinned` (partial quotients certified by both endpoints; never guesses), `convergents` |

A slope is carried as a pinned interval `(Nlo, Nhi, D)` with `Nlo/D < γ < Nhi/D`. Every floor
is computed at both endpoints and the two must agree, or the call raises — precision is never
assumed.

## Tests

```
python3 tests/test_ntlib.py
```

23 checks, each reproducing a value stated in
[`papers/sturmian-transcendence`](../papers/sturmian-transcendence): the isometry, the periodic
value formula, the depth law `q_{k+1}+q_k−2` at both convergent parities, the Step-2 height
bound, `c_W ≤ 3ℓ·max(2^ℓ,3^k)`, the sign check of Remark 3.3, the affine transfer of eq. (10),
and `γ*` to 19 decimals. Runtime under a second; exit code 0 on success.

## Relation to the papers' own scripts

The verification scripts under `papers/*/verification/` are **self-contained and do not import
`ntlib`**. They are byte-identical to the scripts the deposited papers describe, and altering
them would falsify that description. `ntlib` carries the same primitives, packaged and tested
independently; the two implementations agree on every value the tests cover.
