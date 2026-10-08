/-
# Conditional Lean formalisation of
# "Transcendence of the 3x+1 conjugacy map on Sturmian words"

Paper: Elias De Jesús, October 2026, 20 pp., concept DOI 10.5281/zenodo.23210794.
Source of record: `papers/sturmian-transcendence/paper/main.tex` (and `main.pdf`).

STAGE 1 — the logical skeleton: `Basic`, `Liouville`, `Skeleton`.
STAGE 2 — the 2-adic core: `Word`, `BL`, `Shadow`, `Construct`, and the assembly in `Main`.
STAGE 3 — the Sturmian combinatorics: `Height` (the telescoping count, balance, and
Proposition 2.4 as a THEOREM) and `Aperiodic` (`c_γ` is aperiodic for irrational `γ`).
What remains of stage 3 is in `Stubs/TODO.lean`, deliberately NOT imported here.

Three axioms, all in `Axioms.lean`: Theorem R (Ridout, in Bugeaud–Kekeç's single-prime
form), the Berthé–Holton–Zamboni prefix-power family (three clauses), and the numerator
bound of Proposition 2.4 (the author's prior Lemma 10.4).  See `AXIOMS.md` and
`AXIOM_AUDIT.txt`.
-/
import Sturmian.Basic
import Sturmian.Word
import Sturmian.Axioms
import Sturmian.Liouville
import Sturmian.Skeleton
import Sturmian.BL
import Sturmian.Shadow
import Sturmian.Height
import Sturmian.Aperiodic
import Sturmian.Construct
import Sturmian.Main
