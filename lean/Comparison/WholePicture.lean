import Comparison.WholePicture.Geometry
import Comparison.WholePicture.TheLaw
import Comparison.WholePicture.Spectra
import Comparison.WholePicture.Polar
import Comparison.WholePicture.Green
import Comparison.WholePicture.Cells
import Comparison.WholePicture.Connection
import Comparison.WholePicture.OneArc
import Comparison.WholePicture.Moment
import Comparison.WholePicture.MomentSubspaces
import Comparison.WholePicture.Circulation
import Comparison.WholePicture.Curvature
import Comparison.WholePicture.SecondVariation
import Comparison.WholePicture.TraceFive
import Comparison.WholePicture.Audit

/-!
# The whole picture in Lean

The seventeen finite statements of the whole picture of the theory.

* `Geometry`: statements 1 to 4. `TheLaw`: statements 5, 14, 16 and the law's own
  transformation (15). `Spectra`: spectra of symmetric matrices from finite data (a tool).
* `Cells`: statement 6. `Connection`: statement 8, for every unitary connection.
* `Polar`, `Green`: statement 11; `(5 − A)⁺` as the Moore–Penrose inverse.
* `Moment`, `MomentSubspaces`: statement 12, for every central weight and every two subspaces.
* `OneArc`: statement 13. `Curvature`, `SecondVariation`, `TraceFive`: statement 15.
* `Circulation`: statement 17.
* `Audit`: `#print axioms` for every new theorem and for the standing theorems cited.

`Connection`, `MomentSubspaces`, `Audit` and this root are files outside the module system
(they import `RuleAndLaw` and `ArticleStatements` files); the other files are modules.
-/
