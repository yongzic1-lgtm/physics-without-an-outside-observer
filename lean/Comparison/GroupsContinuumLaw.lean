import Comparison.GroupsContinuumLaw.Ward
import Comparison.GroupsContinuumLaw.Schur
import Comparison.GroupsContinuumLaw.RestPole
import Comparison.GroupsContinuumLaw.Symbol
import Comparison.GroupsContinuumLaw.Cone
import Comparison.GroupsContinuumLaw.Chart
import Comparison.GroupsContinuumLaw.Continuum
import Comparison.GroupsContinuumLaw.Rate
import Comparison.GroupsContinuumLaw.LogVertex
import Comparison.GroupsContinuumLaw.Phase48
import Comparison.GroupsContinuumLaw.ColourCoin
import Comparison.GroupsContinuumLaw.Grading
import Comparison.GroupsContinuumLaw.Hexagon
import Comparison.GroupsContinuumLaw.Spin5
import Comparison.GroupsContinuumLaw.Six
import Comparison.GroupsContinuumLaw.Spin6
import Comparison.GroupsContinuumLaw.Twistor
import Comparison.GroupsContinuumLaw.Planes
import Comparison.GroupsContinuumLaw.Centres
import Comparison.GroupsContinuumLaw.Euler
import Comparison.GroupsContinuumLaw.SignCover
import Comparison.GroupsContinuumLaw.SectorIntegral
import Comparison.GroupsContinuumLaw.Pencils
import Comparison.GroupsContinuumLaw.Coupling

/-!
# The groups, the continuum limit and the law

The root of the files in `Comparison/GroupsContinuumLaw/`.

* **The groups and the law.** `Spin5` (Prop. 6: `Sp(2) → SO(5)` onto, kernel `±1`), `Six` and `Spin6`
  (Prop. 17: `SU(4) → SO(6)` onto, kernel `±1`), `Twistor` (Prop. 8: `S⁴ = ℍP¹`, fibre `ℂP¹`),
  `Planes` (Prop. 21: `SO(6)` on `k`-planes, the real forms, the balanced directions of every type),
  `Centres` (Prop. 46: `Y`, `Q`, `S(U(3) × U(2)) ≅ (SU(3) × SU(2) × U(1))/ℤ₆`), `Euler` (Eq. 12,
  Prop. 52: every closed walk counted once, with its holonomy), `SignCover` (Prop. 114: the
  multiplicities `48`, `49`), `SectorIntegral` (Prop. 115 as an integral over the connections),
  `Pencils` (Eq. 38), `Coupling` (Prop. 194, R1 to R6).
* **The continuum limit**: `Chart`, `Schur`, `Symbol`, `RestPole`, `Cone`, assembled in
  `Continuum`.
* **The other holes**: `Ward`, `Rate`, `LogVertex`, `Phase48`, `ColourCoin`,
  `Grading`, `Hexagon`.
-/
