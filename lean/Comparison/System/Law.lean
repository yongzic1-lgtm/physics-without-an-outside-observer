import Comparison.System.Law.Euler
import Comparison.System.Law.Sign
import Comparison.System.Law.Determinant
import Comparison.System.Law.Return
import Comparison.System.Law.Closing
import Comparison.System.Law.Probability
import Comparison.System.Law.Source
import Comparison.System.Law.Sectors
import Comparison.System.Law.Meetings
import Comparison.System.Law.Equations
import Comparison.System.Law.TableVI
import Comparison.System.Law.Quarters
import Comparison.System.Law.Critical
import Comparison.System.Law.Motion
import Comparison.System.Law.Cells
import Comparison.System.Law.Germ
import Comparison.System.Law.Phases
import Comparison.System.Law.PhaseLaw
import Comparison.System.Law.LastDirectionJet
import Comparison.System.Law.LastDirection
import Comparison.System.Law.LocalForm

/-!
# The proof system: the law at its four points `u = i^d/4`

The layer root, in the order of the theory:

* the law (the SI section on the law): `prop_52` and `eq_12` (`Law/Euler.lean`), `prop_53` (`Law/Sign.lean`), `prop_54`
  (`Law/Determinant.lean`), `prop_55` (`Law/Return.lean`), `prop_57` (`Law/Closing.lean`, over every `RCLike`
  field), `prop_58` (`Law/Probability.lean`), `prop_110` (`Law/Source.lean`, over `ℂ`), `prop_115`
  (`Law/Sectors.lean`), `prop_131` (`Law/Meetings.lean`), `prop_114` (`Law/Germ.lean`); the determinant and return declarations
  `eq_13` to `eq_18`, `eq_20`, `eq_24`, `eq_25` (`Law/Equations.lean`) and Table VI (`Law/TableVI.lean`);
* breaking puts the variable at its four points `u = i^d/4`: `eq_19`, `eq_21`, `eq_22`, `eq_23`, Table VII (`Law/Quarters.lean`);
* the local form (the SI section on the local form): `prop_59` (`Law/Critical.lean`), `prop_60` and `eq_26` (`Law/Motion.lean`),
  `prop_61`, `eq_29` (`Law/LastDirection.lean`, `Law/LastDirectionJet.lean`), `eq_27`, `law_small_phases` (`Law/Phases.lean`),
  `prop_62` (`Law/PhaseLaw.lean`), `prop_63`, `eq_28`, `eq_30` (`Law/LocalForm.lean`), `prop_116`
  (`Law/Cells.lean`).

Every statement of this layer about the model holds in every candidate system: `System.uniqueness` makes every
system that satisfies P1 to P3 the model up to one isometry that carries the quaternionic structure to the quaternionic structure
(`System.systems_isomorphic`).
-/
