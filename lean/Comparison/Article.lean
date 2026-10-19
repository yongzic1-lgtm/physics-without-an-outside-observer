import Comparison.Article.Numerics
import Comparison.Article.Clock
import Comparison.Article.Couplings
import Comparison.Article.QBase
import Comparison.Article.QCouplings
import Comparison.Article.QLeptonsQuarks
import Comparison.Article.RowsCouplings
import Comparison.Article.QNucleon
import Comparison.Article.QCosmos
import Comparison.Article.RowsExact
import Comparison.Article.Mixing
import Comparison.Article.QMix
import Comparison.Article.MixRows
import Comparison.Article.QKaon
import Comparison.Article.Kaons
import Comparison.Article.Deuteron
import Comparison.Article.QMisc
import Comparison.Article.Pieces
import Comparison.Article.RealModel
import Comparison.Article.Commutant2
import Comparison.Article.Summaries
import Comparison.Article.LocalForm
import Comparison.Article.Series
import Comparison.Article.Geometry2
import Comparison.Article.Geometry3
import Comparison.Article.Geometry4
import Comparison.Article.Marks
import Comparison.Article.Compositions
import Comparison.Article.Nuclei
import Comparison.Article.Splits
import Comparison.Article.FieldNumbers
import Comparison.Article.Whole
import Comparison.Article.Side
import Comparison.Article.Sources
import Comparison.Article.DimQ
import Comparison.Article.Holonomy
import Comparison.ArticleStatements.CommonClock
import Comparison.ArticleStatements.MeetingPhase
import Comparison.ArticleStatements.SectorSeries
import Comparison.JointCells.PlaneColour
import Comparison.JointCells.Patterns
import Comparison.JointCells.PairSign
import Comparison.RuleAndLaw.Bridges
import Comparison.RuleAndLaw.FactorsC
import Comparison.RuleAndLaw.FactorsA
import Comparison.RuleAndLaw.FactorsB
import Comparison.RuleAndLaw.Typical

/-!
# The article in Lean

The statements of *The Finite Geometry of Physics* (both editions) that were without a theorem or proved only in
part, and the closed forms and printed digits of the 157 rows of the whole table.

* `Numerics`: closed intervals carried through the operations that compose a row.
* `Clock`, `Couplings`: the clock at `{h, n}`, its overlap `h`, the repeated returns `N_h`, `N_con`, `N(1)`.
* `QBase`, `QCouplings`, `QLeptonsQuarks`, `RowsCouplings`, `QNucleon`, `QCosmos` (generated): the quantities of the law with
  closed intervals of twenty-six digits, and 119 rows to their printed digits; `RowsExact`: the twenty exact rows.
* `Mixing`, `QMix`, `MixRows`: the quark and lepton frames and the sixteen mixing rows; `QKaon`, `Kaons`: the light level
  and K⁰, K±.
* `Deuteron`, `QMisc`, `Summaries`, `Compositions`, `Nuclei`: Props. 124, 119, 68, 70, 118, 120, 121, 123, 125, 127,
  187, 50, 51, 97 and Eqs. (19), (39), (41), (50) as assembled statements.
* `Pieces` (Prop. 43), `RealModel` (Prop. 20), `Commutant2` (Props. 13, 15), `Geometry2` (Props. 9, 11, 16),
  `Geometry3` and `Side` (Props. 65, 91, 99), `Geometry4` (Props. 164, 165), `Whole` (Prop. 33), `Splits`
  (Props. 40, 38), `Holonomy` (Prop. 38), `DimQ` (Prop. 2), `Marks` (S109).
* `LocalForm` (Prop. 63, Eqs. (28), (30)), `Series` (Eqs. (47)–(49), Prop. 189), `Sources` (Eq. (31)),
  `FieldNumbers` (Eqs. (36), (38)).
* The cited files outside the former default build that join without a clash (`ArticleStatements`, `JointCells`,
  `RuleAndLaw`); `WholeExterior` (Prop. 33 on `Existence/Exterior.lean`) is built on its own.
-/
