import Comparison.System.Completion.Numbers
import Comparison.System.Completion.Ext.Planes
import Comparison.System.Completion.Ext.Idempotent
import Comparison.System.Table
import Comparison.System.Completion.Constants
import Comparison.System.Completion.Colour
import Comparison.System.Completion.Spectrum
import Comparison.System.Completion.Pairings
import Comparison.System.Completion.Composition
import Comparison.System.Completion.DividedSet
import Comparison.System.Completion.Classical
import Comparison.System.Completion.Remainders
import Comparison.System.Completion.Clock
import Comparison.System.Completion.QK0
import Comparison.System.Completion.Kaon
import Comparison.System.Completion.Bass
import Comparison.System.Completion.Whole
import Comparison.System.Completion.Families

/-!
# The proof system: the completions (SI Propositions 64 to 206; main-text Eqs. (31) to (50))

Layer root. The order inside the completions and the table: `Completion/Numbers` (the law's numbers, each tied to its law object,
and the outside inputs) → `Table/*` (the 157 rows) → the completions' propositions (`Constants`, `Colour`, `Spectrum`,
`Pairings`, `Composition`, `Support`, `Classical`, `Remainders`, `Clock`, `QK0`, `Kaon`, `Bass`) → `Whole` (the
numbered statements whose clauses come from two files) and `Families` (the three pairings beside `h` on the ten symmetric
states, row L04); `Ext/Neutral` (the kept algebra and its exterior representation, rows T01 and T02) is imported by
`Numbers`.

Every statement of this layer about the model holds in every candidate system: `System.uniqueness` makes every
system that satisfies P1 to P3 the model up to one isometry that carries the quaternionic structure to the quaternionic structure
(`System.systems_isomorphic`).
-/
