# Ingredient table

Every ingredient of *Transcendence of the 3x+1 conjugacy map on Sturmian words*
(doi:10.5281/zenodo.23210794) against its prior source. `inherited` = quoted from a cited
source with its hypotheses checked; `author prior work` = from the author's irrationality
paper, quoted and not re-claimed; `new here` = proved in this paper.

Machine-readable copy: [`INGREDIENTS.csv`](INGREDIENTS.csv).

| ingredient | where used | prior source | status |
|---|---|---|---|
| Conjugacy map Phi; isometry v2(Phi v - Phi w) = lcp(v,w) | Prop 2.1 | Bernstein-Lagarias 1996; also Lopez-Stoll 2021 eq. (4) Sec. 1 | inherited |
| Closed form Phi(v) = -sum 3^{-k_{i+1}} 2^i | Prop 2.2 | De Jesus, irrationality paper [P1] Prop 2.1 (doi:10.5281/zenodo.23108370) | author prior work |
| Periodic shadow Phi(w^inf) = c_w/(2^l - 3^k) | Prop 2.4 | Lopez-Stoll 2009 Thm 1 and Lemma 12; restated [P1] Prop 4.1 | inherited |
| Closed 2-adic series; term exponents q_{j+1}+q_j-1 | eq. (6) | Lopez-Stoll 2009 Thm 1; Cor. 2 (generalised continued fraction) | inherited |
| One-position formula for mechanical words | Sec. 2.2 | Lopez-Stoll 2009 Lemma 11; Lothaire 2002 Ch. 2 | inherited |
| Balanced periodic word <=> conjugate of a standard word | Sec. 2.2 | Lothaire 2002 Ch. 2 | inherited |
| Prefix power >= 2 implies conjugate of a standard word | Prop 2.7 | Berthe-Holton-Zamboni 2006 Prop 3.2 | inherited |
| Term-size estimate (1/3) 2^{-{j alpha}} in (1/6, 1/3] | eq. (5) | Lopez-Stoll 2021 Lemma 43 Sec. 11 (also Lemmas 41-42); elementary, re-derived inline here | inherited |
| Height of a shadow: log2 H < A(gamma) l + log2(3l) + log2 3 | Prop 2.9 | [P1] Lemma 10.4, resting on Lopez-Stoll 2021 Lemma 43 | author prior work |
| Initial critical exponent: definition and formula 1 + limsup q_{k+1}/q_k | Def 2.11 / Prop 2.12 | Berthe-Holton-Zamboni 2006 Sec. 2 and Sec. 4.2 | inherited |
| ice floor: ice(c_gamma) >= 1 + phi | Prop 2.14 | Berthe-Holton-Zamboni 2006 Sec. 4.2; re-derived as Lemma 2.15 | inherited |
| Depth law on 1c_gamma at both convergent parities | Sec. 4 | [P1] Thms 5.3 and 8.3 | author prior work |
| Affine transfer 2 Phi(c) = 3 Phi(1c) + 1 = Phi(0c) | eq. (10) | [P1] Cors 7.1 and 8.8; real form Lopez-Stoll 2021 Lemma 37 (equivalently Lemma 25) | author prior work |
| Irrationality: Phi(s) not in Q for every mechanical word | Prop 2.10 | [P1] Thm 10.1 and Cor 10.5; partial coverage Monks-Yazinski 2004 Thm 2.7(b); independent notes Pham 2026, Cassidy 2026 | author prior work |
| Ridout's theorem, single-prime form (Theorem R) | Sec. 2.4 | Badziahin-Kristensen 2018 Thm 1.3, attributed there to Ridout 1958 | inherited |
| p-adic Subspace Theorem (used only in Appendix A, nothing depends on it) | App. A | Schlickewei 1976/1977 | inherited |
| Transcendence of Phi(s) for every Sturmian s: the claim, first proposed | Sec. 9 | Cassidy 2026 Sec. 4.6, with a Subspace sketch recorded there as unaudited | prior proposal (credit) |
| Determinant identity P_N Q_{N+1} - P_{N+1} Q_N = +3^N 2^{S_N}; truncations subcritical | Props 5.1 and 5.3 | question posed in De Jesus, Sturmian-Mahler Edge (doi:10.5281/zenodo.20594173) | new here |
| Theorem 1.2 (quantitative), Theorem 1.3 (criterion ice > 2A), Corollary 1.4 | Sec. 1 and Sec. 3 | - | new here |

Counts: 11 inherited, 5 author prior work, 1 prior proposal, 2 new here.
