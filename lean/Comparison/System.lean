import Comparison.System.Spine
import Comparison.System.Geometry
import Comparison.System.Existence
import Comparison.System.Law
import Comparison.System.Completion
import Comparison.System.Table
import Comparison.System.Finite

/-!
# The proof system of physics without an outside observer

The finite geometry, walks, determinant, source reductions and numerical
formulas, in their dependency order from the five postulates.

* `Comparison.System.Spine`: P1 to P5 in their mathematical form (`System/Postulates.lean`); one
  name for each object of the model, with the ties to its other definitions (`System/Basic.lean`);
  the uniqueness theorem `System.uniqueness`: every system that satisfies P1 to P3 is the
  quaternionic plane, four complex amplitudes and five directions; the quaternionic plane and the
  two systems of every candidate system (`System/Spine/`).
* `Comparison.System.Geometry`: quaternionic structure, comparisons, distinctions,
  singlet, six directions and divisions.
* `Comparison.System.Existence`: reduced walks, first returns, the transmitting
  amplitude, spin, clocks and the last-step direction.
* `Comparison.System.Law`: the determinant and its factors, positivity, Schur
  calculus, source derivatives, poles, motion and finite cell equations.
* `Comparison.System.Completion`, `Comparison.System.Table`: crossings, couplings,
  mass formulas, positive sources, retained determinants, three pairings and table values.
* `Comparison.System.Finite`: the seventeen declarations `S3_1` to `S3_17`,
  with the equalities between definitions used in different layers.

The declaration names `prop_N`, `eq_N`, `row_X`, `table_VI`, `table_VII` and `S3_N`
are kept. `docs/ARTICLE_CONCORDANCE.md` gives each article number its theorem
and `docs/PROOFS.md` states the scope of the proofs. Statements about the model
are transported to candidate systems by the quaternionic isometry:
`System.uniqueness` makes every system that satisfies P1 to P3 the model up to one isometry that
carries the quaternionic structure to the quaternionic structure (`System.systems_isomorphic`).
-/
