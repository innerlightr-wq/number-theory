# number-theory

General number-theory work by Elias De Jesús — results whose interest is not specific to the
3x+1 problem. One self-contained folder per deposited paper, plus a small tested library of
exact-arithmetic primitives.

Collatz-specific work lives in its own repositories:
[eoc-divergence](https://github.com/innerlightr-wq/eoc-divergence),
[eoc-lean-verification](https://github.com/innerlightr-wq/eoc-lean-verification),
[periodicity-conjecture-bridge](https://github.com/innerlightr-wq/periodicity-conjecture-bridge).

## Index

| Title | DOI | Code | Scope | Status |
|---|---|---|---|---|
| Transcendence of the 3x+1 conjugacy map on Sturmian words | [10.5281/zenodo.23210794](https://doi.org/10.5281/zenodo.23210794) (concept) | [`papers/sturmian-transcendence`](papers/sturmian-transcendence) | 2-adic transcendence; Sturmian words; Ridout | deposited 2026-10-07 |
| The 3x+1 conjugacy map sends every Sturmian word to an irrational 2-adic integer | [10.5281/zenodo.23108370](https://doi.org/10.5281/zenodo.23108370) (version; concept [22920055](https://doi.org/10.5281/zenodo.22920055)) | with the deposit; primitives in [`lib/`](lib) | 2-adic irrationality; Sturmian words | deposited 2026-10-02 |
| A δ²–L³ Sensitivity Law for Finite-Window Weil Positivity, with a Function-Field Control of the Connes–van Suijlekom Pipeline | [10.5281/zenodo.23195177](https://doi.org/10.5281/zenodo.23195177) (version) | [github.com/innerlightr-wq/weil-window-control](https://github.com/innerlightr-wq/weil-window-control) | Weil positivity on finite windows; function-field control | deposited 2026-10-06 |
| Riemann Hypothesis: The Weil Enforcer in Audit Coordinates | [10.5281/zenodo.21115524](https://doi.org/10.5281/zenodo.21115524) (version) | — | Weil positivity, audit coordinates | deposited 2026-07-01 |
| The Partition Potential and the Laguerre Tower: An Exact Derivative–Response Witness | [10.5281/zenodo.21108392](https://doi.org/10.5281/zenodo.21108392) (version) | — | Laguerre tower; derivative-response witness | deposited 2026-07-01 |

Every DOI above was resolved against the Zenodo API and its title checked before listing.

> **Note on rows 3 and 4.** *A δ²–L³ Sensitivity Law…* (23195177) and *Riemann Hypothesis:
> The Weil Enforcer in Audit Coordinates* (21115524) are **two versions of a single Zenodo
> record**, concept DOI [10.5281/zenodo.21109955](https://doi.org/10.5281/zenodo.21109955),
> which has eight versions and now resolves to the δ²–L³ paper. The version DOIs above are
> stable and resolve to the stated titles; the concept DOI does **not** resolve to the Weil
> Enforcer. Cite the version DOI for either.

## Rules

- Only material **already published on Zenodo** goes here. Work in progress stays out.
- **One self-contained folder per paper**, under `papers/`, holding the deposited source and
  PDF, its verification scripts, and its own credit section.
- **Each folder keeps its own credit section.** Attribution is per paper, not repository-wide.
- The shared library in `lib/` holds only primitives that more than one paper uses, with tests
  that reproduce published values.

## Layout

```
lib/        exact-arithmetic primitives (ntlib) + tests
papers/     one folder per deposited paper
```

## Reproduction

Python 3.9+, standard library only. No third-party packages, no network access.

```
python3 lib/tests/test_ntlib.py          # 23 library tests                     <1 s
cd papers/sturmian-transcendence/verification && python3 rev_main.py   # Appendix B   7 s
```

The full verification suite of every paper in this repository runs in about 11 seconds.

## License

Dual-licensed.

- **Code** — **MIT**, see [`LICENSE`](LICENSE). Covers `lib/` and all `verification/` scripts.
- **Papers and documentation** — **CC BY 4.0**, see
  [`LICENSE-CC-BY-4.0`](LICENSE-CC-BY-4.0). Covers `papers/*/paper/`, every `README.md`, and
  the ingredient tables and checklists.

CC BY 4.0 requires attribution: if you use a paper, its figures or its data, please cite that
paper by its DOI.

## How to cite

Cite the individual paper by its DOI. For the repository as a whole see
[`CITATION.cff`](CITATION.cff).
