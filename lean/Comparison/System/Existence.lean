import Comparison.System.Existence.Ext.Exterior
import Comparison.System.Existence.Ext.Spin
import Comparison.System.Existence.Ext.Covariance
import Comparison.System.Existence.Ext.Turn
import Comparison.System.Existence.Ext.JointStep
import Comparison.System.Existence.Ext.EvenFour
import Comparison.System.Existence.Ext.Commutant
import Comparison.System.Existence.Defs
import Comparison.System.Existence.Line
import Comparison.System.Existence.LineWhole
import Comparison.System.Existence.ExcursionMoments
import Comparison.System.Existence.Excursion
import Comparison.System.Existence.ExcursionVisits
import Comparison.System.Existence.ExcursionWhole
import Comparison.System.Existence.Places
import Comparison.System.Existence.Holonomy4
import Comparison.System.Existence.PlacesWhole
import Comparison.System.Existence.Six
import Comparison.System.Existence.SixWhole
import Comparison.System.Existence.Matter
import Comparison.System.Existence.MatterWhole
import Comparison.System.Existence.Irreps
import Comparison.System.Existence.PairModel
import Comparison.System.Existence.PairPlanes
import Comparison.System.Existence.PairCentres
import Comparison.System.Existence.LastDirection
import Comparison.System.Existence.LastDirectionSpan
import Comparison.System.Existence.PairWhole
import Comparison.System.Existence.PairAlgebras
import Comparison.System.Existence.LastDirectionUnit
import Comparison.System.Existence.IrrepsWhole
import Comparison.System.Existence.Numbered

/-!
# The proof system, the existence layer

P4 and P5 (the spine, `System/Postulates.lean`), Definitions 17 to 30 (`Defs`), Propositions 24 to 51, 91, 97 and 99, in the theory's order:

* Book VI, a world line: `prop_24` (`LineWhole`, from `Line`), `prop_25` to `prop_28` (`Line`), `prop_29`
  (`ExcursionMoments`, `Excursion`), `prop_30`, `prop_31` (`ExcursionWhole`, from `Excursion`); the visits to the symmetric states of one excursion (`ExcursionVisits`);
* Book VII, both directions at every vertex: `prop_32`, `prop_34`, `prop_38`, `prop_39` (`PlacesWhole`, from `Places`
  and `Holonomy4`), `prop_33`, `prop_35` to `prop_37`, `prop_91` (`Places`, with the exterior algebra of the six in
  `Ext`);
* Book VIII, the six divisions completed: `prop_40` (`SixWhole`, from `Six` and `Geometry.RealForm`),
  `prop_41` to `prop_44`, `prop_97` (`Six`);
* Book IX, matter: `prop_45`, `prop_49` to `prop_51` (`Matter`), `prop_99` (`MatterWhole`); `prop_46` (`PairAlgebras`,
  from `PairWhole`: the pair `PairModel`, at every plane `PairPlanes`, the centres `PairCentres`); `prop_47` (`LastDirectionUnit`:
  the mass form `LastDirection`, the bases `LastDirectionSpan`); `prop_48` (`IrrepsWhole`: the three projectors `Matter`, what the ten keep
  `Irreps`).

Every statement of this layer about the model holds in every candidate system: `System.uniqueness` makes every
system that satisfies P1 to P3 the model up to one isometry that carries the quaternionic structure to the quaternionic structure
(`System.systems_isomorphic`).

The numbered theorems stand in `Comparison.System` as `prop_N` (`Numbered`), the
helpers in `Comparison.System.Existence`.
-/
