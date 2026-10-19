import Comparison.System.Table.Leptons
import Comparison.System.Table.Couplings
import Comparison.System.Table.Mixings
import Comparison.System.Table.Cosmos
import Comparison.System.Table.Neutrinos
import Comparison.System.Table.Hadrons
import Comparison.System.Table.Nuclei

/-!
# The proof system: the whole table (Table X, 157 rows)

Layer root. Each row `X` of Table X is `Comparison.System.row_X`: the row's value as a law-tied definition in
`Comparison.System.Table.Row` (built from the numbers of `Comparison.System.Completion.Num`), with its stated digits as
an interval with rational ends. The table's files import only `Completion/Numbers` (and the base); the completions'
proposition files import the table.

Every statement of this layer about the model holds in every candidate system: `System.uniqueness` makes every
system that satisfies P1 to P3 the model up to one isometry that carries the quaternionic structure to the quaternionic structure
(`System.systems_isomorphic`).
-/
