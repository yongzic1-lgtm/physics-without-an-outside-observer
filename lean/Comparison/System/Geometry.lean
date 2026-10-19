import Comparison.System.Geometry.Definitions
import Comparison.System.Geometry.OneThing
import Comparison.System.Geometry.Lines
import Comparison.System.Geometry.TwoThings
import Comparison.System.Geometry.Kept
import Comparison.System.Geometry.KeptThree
import Comparison.System.Geometry.KeptFour
import Comparison.System.Geometry.KeptAll
import Comparison.System.Geometry.SixDirections
import Comparison.System.Geometry.RealModel
import Comparison.System.Geometry.Divisions
import Comparison.System.Geometry.RealForm
import Comparison.System.Geometry.DetExp
import Comparison.System.Geometry.RealFormGroup
import Comparison.System.Geometry.RealFormAll
import Comparison.System.Geometry.RealFormSU4
import Comparison.System.Geometry.OneModel

/-!
# The geometry of comparison: P1 to P3, Definitions 1 to 16, Propositions 1 to 23

The layer root, in the theory's order: the definitions; one system (Props. 1 to 3); the lines, sides,
rotations, overlap and sphere (Props. 4 to 8); two systems (Props. 9 to 14); the kept operators
(Prop. 15, whole in `KeptAll`); the six directions and the square root of the sign (Props. 16 to 19); the square root of the sign uses P1's
`i` (Prop. 20); divisions (Props. 21 and 22: the four types, Definition 15's real form in a basis,
`det e^A = e^{tr A}`, the groups of the real forms, every division, and the real form of the point `SU(4)`; Prop. 21 whole in `RealFormSU4`); one model
(Prop. 23).

Every statement of this layer about the model holds in every candidate system: `System.uniqueness` makes every
system that satisfies P1 to P3 the model up to one isometry that carries the quaternionic structure to the quaternionic structure
(`System.systems_isomorphic`).
-/
