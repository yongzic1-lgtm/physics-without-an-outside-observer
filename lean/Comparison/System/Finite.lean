import Comparison.System.Finite.Geometry
import Comparison.System.Finite.Law
import Comparison.System.Finite.Excursion
import Comparison.System.Finite.Completion
import Comparison.System.Finite.Ties

/-!
# The geometry, law, returns and completions in seventeen statements

`S3_1` to `S3_4` (`Finite/Geometry.lean`), `S3_5` to `S3_8` (`Finite/Law.lean`), `S3_9` to
`S3_11` (`Finite/Excursion.lean`), `S3_12` to `S3_17` (`Finite/Completion.lean`), each the whole statement
as one Lean proposition, in the namespace `Comparison.System`; and the objects two layers define,
proved equal, with what P2 and P5 fix (`Finite/Ties.lean`).

Every statement of this layer about the model holds in every candidate system: `System.uniqueness`
makes every system that satisfies P1 to P3 the model up to one isometry that carries the quaternionic structure to
the quaternionic structure (`System.systems_isomorphic`).
-/
