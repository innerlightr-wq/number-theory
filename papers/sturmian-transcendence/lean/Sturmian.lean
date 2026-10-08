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

STAGE 5 — the BHZ floor, Tier A: `Rotation` (the three-distance periodicity lemma for
`c_γ`), `Records` (best-approximation records, Fibonacci-type growth, a prefix power of
`12/5`), and `TierA` (`ice(c_γ) > 2` unconditionally, the irrationality of `log₃ 2`, and
the headline case on Ridout alone).

**TWO axioms, both in `Axioms.lean`:** Theorem R (Ridout, in Bugeaud–Kekeç's single-prime
form) and the Berthé–Holton–Zamboni floor `ice(c_γ) ≥ 1+φ`.  After stage 5 the second one
is used **only** for slopes `γ ∈ [γ_A, γ*)`, where `γ_A = 6/(5 log₂ 3)`; for `γ < γ_A`, and
in particular for the headline slope `γ = log₃ 2`, the results depend on Ridout alone.
See `AXIOMS.md` and `AXIOM_AUDIT.txt`.
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
import Sturmian.Rotation
import Sturmian.Records
import Sturmian.TierA
