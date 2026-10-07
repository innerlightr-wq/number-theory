# CHECKLIST.md — every numbered statement: proof location, prior source, verification status

Numbering is that of the compiled `main.pdf` (18 pages). "Prior source" is authoritative: a
statement marked *inherited*, or marked as the author's **prior work [P1]**, must not be presented
as new in this paper. Verification refers to `verification/`, the independent review's scripts;
**§6 was outside the review's remit** and is marked accordingly.

Throughout, **[P1]** = De Jesús, *The 3x+1 conjugacy map sends every Sturmian word to an irrational
2-adic integer*, doi:10.5281/zenodo.23108370 (cited in the paper as `[DJirr]`), and **[6]** in
Cassidy's own numbering = `[Cassidy26]`, the file
`05-knowledge/results/collatz_procgen_20260922_transversality_foundry.md` of
`github.com/eliottcassidy2000/math`, September 2026, commit `6b805eed`.

| # | statement | proof location | prior source | verification |
|---|---|---|---|---|
| Q 1.1 | Periodicity Conjecture | — (open question, quoted) | **Lagarias \[Lagarias85, Rel. 2.31\]** | — |
| **Thm 1.2** | `omega_1^(2)(Phi(c_gamma)) >= ice(c_gamma)/A(gamma) - 1` | §3.2, from Steps 1–5 | **new in this paper** | trend confirmed at 4 slopes, `rev_main.py` |
| **Thm 1.3** | transcendence of `Phi(c_gamma)`, `Phi(1c_gamma)`, `Phi(0c_gamma)`, all shifts, under (T) | §3.1, Steps 1–6 | **new in this paper.** The *claim* for every Sturmian word was first proposed, with a sketch recorded there as unaudited, by **Cassidy \[6, §4.6\]** (September 2026). Our route — Ridout in the single-prime form, with BHZ — is different, and the general claim remains open | all inputs verified; `rev_main.py` |
| **Cor 1.4** | unconditional for `gamma < gamma* = (3+sqrt5)/(4 log_2 3)`, incl. `gamma = log_3 2` | §3.4 | **new in this paper**; answers **\[P1, §12 problem (3)\]** in this range | boundary both sides, `rev_boundary_controls.py` |
| Prop 2.1 | isometry `v_2(Phi(v)-Phi(w)) = lcp(v,w)`; injectivity | quoted | **\[BL96\]**; also recorded as **\[LS21, eq. (4), §1\]** (attributed there to \[BL96\]); restated \[P1, Prop. 2.2\] | re-derived from the parity-vector definition and checked, 300/300 exact trials |
| (2), (3) | `Phi(sigma v) = T(Phi(v))`; `Phi(v)` odd iff `v_0 = 1`; `2^m Phi(sigma^m v) = 3^{k_m} Phi(v) + c_m(v)` | §2.1 | **\[BL96, §1\]**; displayed as eq. (3) and Scheme 1 of \[LS21\] | affine case verified mod `2^400`, 3 slopes |
| Prop 2.2 | `Phi(w^inf) = c_w/(2^l - 3^k)`, odd denominator | quoted | **\[LS09, Thm 1 and Lemma 12\]** — the periodic approximants and their depths; restated \[P1, Prop. 4.1\] | formula checked 200/200; the 2009 series (eq. (4)) reproduced exactly mod `2^4000`, 3 slopes |
| (4) | the closed 2-adic series for `Phi(1c_beta)` | quoted | **\[LS09, Thm 1\]**; \[LS09, Cor. 2\] for the continued fraction | exact mod `2^4000`, 3/3 slopes (16/9/9 terms) |
| Prop 2.3 | prefix power `>= 2` ⟹ conjugate of a standard word ⟹ `W^inf` balanced | quoted | **\[BHZ06, Prop. 3.2\]**, with **\[Lothaire02, Ch. 2\]** | — (combinatorial input, used as quoted) |
| (5) | `3^{-(j+1)} 2^{floor(j alpha)} in (1/6, 1/3]`, with the distribution in that interval | §2.2 | **\[LS21, Lemma 43, §11\]**; \[LS21, Lemmas 41–42\] for the means | — |
| **Prop 2.4** | `c_W <= 3l max(2^l,3^k)`; `log_2 H(Phi(W^inf)) < A(gamma) l + log_2(3l) + log_2 3` | §2.2, proof reproduced | **author's prior work \[P1, Lemma 10.4\]** (the all-slopes extension by balance); its archimedean input is (5) = \[LS21, Lemma 43\]. *Not new here* | both the `c_W` bound and the height bound hold at **46/46** levels used, 4 slopes |
| Def 2.5 | `ice` = limsup of prefix powers; hence depth `= p·|W|` exactly | quoted | **\[BHZ06, §2\]** | — |
| Prop 2.6 | `ice(c_alpha) = 1 + limsup q_{k+1}/q_k` | quoted | **\[BHZ06, §4.2\]** (displayed chain in the proof of their Thm 1.2) | depth identity `q_{k+1}+q_k-2` at **46/46** levels, both parities; `-1` variant 0/46 |
| Rem 2.7 | the `c_gamma` depth `q_n+q_{n+1}-2` at odd `n` derived from the `1c_gamma` depth law via `c_gamma = sigma(1c_gamma)`; the even levels are *not* recovered this way | §2.3 | **re-derivation** from **author's prior work \[P1, Thm 8.3\]**; the limsup over all `k` stays **\[BHZ06, §4.2\]**. *Not new* | consistent with the 46/46 depth check above |
| Prop 2.8 | `ice(c_gamma) >= 1+phi`, equality iff `a_k = 1` eventually | quoted + 2 lines | **\[BHZ06, §4.2\]** (the sentence after their Thm 1.2, with `theta = (1+sqrt5)/2` fixed on their p. 3); Fibonacci case also in their Introduction; constant in \[BHZ06, Prop. 2.1(3)\]. Formula also from Cassaigne \[Cassaigne99\]; index formula Vandeth \[Vandeth00, Thm 16\]; Fibonacci repetitions \[MignosiPirillo92\] | — |
| Lemma 2.9 | `limsup q_{k+1}/q_k >= phi` | §2.3, proved | **re-derivation** of Prop 2.8; *not new*, labelled as such | checked on 7 CF patterns, minimum exactly `phi` at all-ones |
| Thm R | the 2-adic threshold (single-prime Ridout) | quoted | **\[BK18, Thm 1.3\]**, attributed there to **\[Ridout58\]** | — |
| footnote §2.4 | the several-primes form has a real-root hypothesis; witness `X^4-3X^3+2X+6` | footnote | caveat is ours; the formulation quoted is \[Ridout58\] as reproduced in arXiv:2603.10561, Thm 3 | Sturm count 0 real roots, irreducible, Hensel root mod `2^{800}`; `p1_ridout_gap2.py` |
| Prop 2.10 | `Phi(s) notin Q` for every mechanical word, every slope and intercept | quoted | **author's prior work \[P1, Thm 10.1, Cor. 10.5\]**. Prior partial coverage: **\[MY04, Thm 2.7(b)\]** below `beta`; irrationality also obtained independently by **\[Pham26, Thm 3, Cors. 4–5\]** (22 July 2026) and **\[Cassidy26, Thms R and S\]** (September 2026). **\[LS21, Thm 1\] cited as context only, relied on nowhere** | — |
| **Lemma 3.1** | fixed margin `delta = kappa/(2A) > 0`; slack `O(log log H / log H)` | §3.3, proved | **new in this paper** | contrast with the `sqrt(17)` control, `rev_boundary_controls.py` |
| Rem 3.2 | threshold arithmetic; `A(gamma)` correct across the range | §3.4 | **ours** | `bitsH` regimes both confirmed |
| Rem 3.3 | the two `Xi` conventions; `Xi_{alpha,0} = -Xi_alpha` | §3.4 | correction due to J. López; both conventions are \[P1, Prop. 3.2\] and \[DJedge, Thm 4.1\] | exact mod `2^3000`, 1893 terms; `sign_check.py` |
| (12) | `2 Phi(c_gamma) = 3 Phi(1c_gamma) + 1 = Phi(0c_gamma)` | §3.1 Step 6 | real normalisation (`alpha > beta`) is **\[LS21, Lemma 37\]**; the **2-adic form, every irrational slope, is author's prior work \[P1, Cor. 7.1, Cor. 8.8\]**. *New here: only the observation that, being Q-affine, it carries transcendence along the shift orbit* | exact mod `2^400`, 3 slopes |
| **§4, (13)** | `ice(1c_gamma) = 1 + limsup_{n odd} q_{n+1}/q_n`; the parity dichotomy and the obstruction | §4 | the **depth law at both convergent parities is author's prior work \[P1, Thms 5.3, 8.3\]**; depth *values* prefigured by the term exponents of \[LS09, Thm 1\]. **New in this paper: the parity obstruction drawn from it, and the witness** | prefix power `= 1` at every even level, 4 slopes; exhaustive sweep `l < 900` |
| **Ex 4.1** | witness `gamma = [0;2,1,4,1,8,...]`: `ice(1c_gamma) = 2`, `omega -> 1`, while `c_gamma` gives `omega >= 16.886` | §4 | **new in this paper**; witness supplied by the independent review | `rev_collapse.py` |
| **Thm 5.1** | unbounded partial quotients ⟹ `omega = infinity`, a 2-adic `U_1`-number | §5, proved | **new in this paper** (Theorem A\*; Case L of Thm 1.2); classification per \[Bugeaud04, Ch. 9\] | certified `omega >= 23.274` at one level for `log_3 2`; 1456 certified partial quotients, max 3308 |
| Lemma 6.1 | `v_2(R-R') <= log_2 H(R) + log_2 H(R') + 1` | §6, proved | **ours** (elementary) | **not reviewed** |
| Lemma 6.2 | abstract measure lemma; `mu > max(Theta, 1+g/(theta-1))` | §6, proved | **ours** | **not reviewed** |
| **Thm 6.3** | finite effective measure for `gamma <= log_3 2` with bounded partial quotients | §6, proved | **new in this paper** (Theorem B\*) | **not reviewed**; author's own numerics only |
| Rem 6.4 | why `gamma <= log_3 2` is needed (no lower bound on `h_k` when `A > 1`) | §6 | **ours** | — |
| §7.1, **Q 7.1** | general intercepts not covered; `ice = 2` attainable — open problem | §7.1 | obstruction is **\[BHZ06, Thm 1.1\]**; `ice >= 2` is **\[ADQZ2001, Thm 1\]** | — |
| §7.2, **Q 7.2** | extending the range toward all slopes by an S-unit/Subspace argument over `{inf,2,3}` — open problem | §7.2 | the route is **Cassidy's sketch \[6, §4.6\]**; the Subspace input is Thm S = \[Schlickewei76, Schlickewei77\]. Stated here as an open problem, not a result | — |
| §7.3 | integer target not obstructed; `2^l - 3^k = ±1` only in 3 cases. **\[P1, §12 problem (2)\]** remains open and is *not* answered by Thm 5.1 or Thm 6.3 | §7.3 | equivalence is **\[DJedge, Prop. 7.2\]**; Catalan/Mihăilescu | denominators checked large and odd at 11 levels |
| Rem 7.3 | the real series diverges at the resonance; \[LS09\]'s unproven remark on `F` | §7.4 | divergence from (5) = **\[LS21, Lemma 43\]**; the remark is **\[LS09, §4\]**, about the **real** `F(x) = Phi_R(m_x)` of \[LS09, Def. 26\], explicitly unproven | — |
| §8 | related work: López–Stoll; Pham; Cassidy; and the priority record | §8 | **\[LS09\], \[LS21\], \[Pham26\], \[Cassidy26\]**; characterisations of Pham and Cassidy reused in substance from **\[P1, §1\]** (irrationality only) | — |
| Thm S | `p`-adic subspace theorem | App. A, quoted | **\[Schlickewei76\], \[Schlickewei77\]**, in the formulation of **\[BG06, Thm 7.2.2\]** | — |
| Prop A.1 | Theorem R from Thm S | App. A, proved | **re-derivation** of Thm R = \[BK18, Thm 1.3\]; *not new*, labelled as such | — |

## New in this paper

1. **The transcendence theorem and its range** — Theorem 1.3 and Corollary 1.4, the latter
   unconditional for every irrational `gamma < gamma* = (3+sqrt5)/(4 log_2 3)`, the resonance slope
   `log_3 2` included. This answers **\[P1, §12 problem (3)\]** in that range.
2. **The quantitative bound** `omega >= ice(c_gamma)/A(gamma) - 1` — Theorem 1.2, obtained through
   `c_gamma`, with the full limsup; and the fixed-margin Lemma 3.1 that makes it usable.
3. **The parity obstruction and its witness** — §4 and Example 4.1: why the argument must run
   through `c_gamma` and not `1c_gamma`, with `gamma = [0;2,1,4,1,8,...]` showing the `1c_gamma`
   route collapses to `omega -> 1`.
4. **Theorem A\*** — Theorem 5.1: unbounded partial quotients give `omega = infinity` and a 2-adic
   `U_1`-number.
5. **Theorem B\*** — Theorem 6.3: a finite *effective* irrationality measure for `gamma <= log_3 2`
   with bounded partial quotients. §6 is unreviewed.

Also new, but minor: the observation that the transfer identity (12), being Q-affine, carries
transcendence along the shift orbit; and the several-primes real-root caveat in the §2.4 footnote.

## Author's prior work [P1] — quoted here, not new

- the **depth law at both convergent parities** → \[P1, Thm 8.3\] (with \[P1, Thm 5.3\]), used in §4
  and re-derived for `c_gamma` at odd levels in Remark 2.7;
- the **height bound** `c_W <= 3l·max(2^l,3^k)` for cyclic permutations of standard words →
  \[P1, Lemma 10.4\] = Proposition 2.4;
- the **transfer identities** → \[P1, Cor. 7.1, Cor. 8.8\] = equation (12);
- **irrationality** for every mechanical word, every slope and intercept → \[P1, Thm 10.1,
  Cor. 10.5\] = Proposition 2.10.

Lemma 2.9, Remark 2.7 and Proposition A.1 are re-derivations of inherited or prior statements, kept
only for self-containedness and labelled as such in the text.

## Priority on the transcendence claim

Cassidy \[6, §4.6\] (September 2026, commit `6b805eed`) first proposes transcendence of `Phi(s)`
for every Sturmian word `s`, with a sketch via Schlickewei's p-adic Subspace Theorem that the note
itself records as unaudited; its §6 keeps the claim a hypothesis candidate. This paper gives a
complete proof for characteristic words of every irrational slope `gamma < gamma*`, by a different
route — Ridout's theorem in the single-prime form \[BK18, Thm 1.3\] together with the
Berthé–Holton–Zamboni bound on initial powers. The general claim remains open and is recorded as
Question 7.2. The author suggested the same single-prime route independently on the same day, in
commit `a26b1cb` of the public repository `innerlightr-wq/eoc-divergence`; this is noted
parenthetically in §1.6 and nowhere else.

This is stated in §1.6 and, briefly, in §8 of the paper.

**Private records.** `prior-art/PRIORITY_TIMELINE.md` holds the full dated reconstruction, with
SHAs and UTC timestamps, including a section on a private repository. It is a **private working
record only**: nothing in `main.tex`, `refs.bib` or this checklist cites it, and the paper carries
no hour-level timestamps and no comparison of commit times.
