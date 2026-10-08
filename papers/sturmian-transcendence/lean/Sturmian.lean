/-
# Conditional Lean formalisation of
# "Transcendence of the 3x+1 conjugacy map on Sturmian words"

Paper: Elias De Jesús, October 2026, 20 pp., concept DOI 10.5281/zenodo.23210794.
Source of record: `papers/sturmian-transcendence/paper/main.tex` (and `main.pdf`).

STAGE 1 — the logical skeleton: `Basic`, `Liouville`, `Skeleton`.
STAGE 2 — the 2-adic core: `Word`, `BL`, `Shadow`, `Construct`, and the assembly in `Main`.
STAGE 3 — the Sturmian combinatorics: `Height` (the telescoping count, balance, sharp
prefix balance) and `Aperiodic` (`c_γ` is aperiodic for irrational `γ`).
STAGE 4 — `Numerator` (`[DJirr, Lemma 10.4]`, and Proposition 2.4 assembled with **no**
axiom), `Ice` (the initial critical exponent and the extraction of Steps 1–2), and
`DefinitionAudit` (every definition against the paper's verbatim text, with sanity lemmas).

**TWO axioms, both in `Axioms.lean`:** Theorem R (Ridout, in Bugeaud–Kekeç's single-prime
form) and the Berthé–Holton–Zamboni floor `ice(c_γ) ≥ 1+φ`.  See `AXIOMS.md` and
`AXIOM_AUDIT.txt`.
-/
import Sturmian.Basic
import Sturmian.Word
import Sturmian.Ice
import Sturmian.Axioms
import Sturmian.Liouville
import Sturmian.Skeleton
import Sturmian.BL
import Sturmian.Shadow
import Sturmian.Height
import Sturmian.Numerator
import Sturmian.Aperiodic
import Sturmian.Construct
import Sturmian.Main
import Sturmian.DefinitionAudit
