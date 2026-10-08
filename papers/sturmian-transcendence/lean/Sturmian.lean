/-
# Conditional Lean formalisation of
# "Transcendence of the 3x+1 conjugacy map on Sturmian words"

Paper: Elias De Jesús, October 2026, 20 pp., concept DOI 10.5281/zenodo.23210794.
Source of record: `papers/sturmian-transcendence/paper/main.tex` (and `main.pdf`).

STAGE 1 (this import closure): the logical skeleton.  One axiom, `ridout_single_prime`.
STAGE 2 and 3 are not part of this import closure; see `Stubs/TODO.lean`, which is
deliberately NOT imported here.
-/
import Sturmian.Basic
import Sturmian.Axioms
import Sturmian.Liouville
import Sturmian.Skeleton
