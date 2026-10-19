# Formal proofs

This is the Lean development accompanying *Physics Without an Outside Observer:
A Finite Geometry, Broken and Completed*. It constructs the finite geometry,
the directed step, the determinant and its returns, source reductions and the
formulas used to read physical quantities from them.

`Comparison.System` is the entry point. `Comparison.lean` and
`Comparison/Basic.lean` import it.

## Build every proof

The toolchain is `leanprover/lean4:v4.35.0`. Mathlib is `v4.35.0`; its exact
commit and all dependency commits are recorded in `lake-manifest.json`.

Run from this directory:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build Comparison.System
LEAN_NUM_THREADS=1 lake build
LEAN_NUM_THREADS=1 xargs lake build < verification/additional_roots.txt
```

The first build checks the common proof root and its dependencies. The second
checks all roots listed in `lakefile.toml`. The last command checks the remaining
source modules, including the independent exterior development and the audits.
Lake compiles each module in its own import environment. The matrix and exterior
libraries retain their declaration names and are read through their own roots.

The commands are collected in [verification/BUILD.md](verification/BUILD.md).

## Check the declarations

```sh
python tools/check_sources.py
lake env lean Comparison/System/Audit/Axioms.lean
```

The first command checks every indexed source file and every literal theorem
statement. It prints:

```text
Comparison source modules: 334
Theorem/lemma statements: 6863
Theorem aliases: 31
Source theorem declarations: 6894
Changed source files: 0
Changed indexed declarations: 0
Forbidden proof declarations/tactics: 0
Source and theorem index: PASS
```

The second command prints the axiom dependencies of the 2,456 declarations
defined within `Comparison.System`. The published compiled records give the
axioms of each checked declaration. The build record states the completed
import scope and the output of each executed command.

To read types and dependencies from a compiled import environment:

```sh
lake env lean --run tools/export_proofs.lean Comparison.System system_proofs.json
```

The output contains the elaborated types, constants used in each type and proof,
project dependency locations and axiom sets. Lean also generates auxiliary
theorems while elaborating definitions and tactics; the source index identifies
the 6,894 named declarations written in the development.

The two root lists cover every module in compatible import
environments. Read their complete theorem records with:

```sh
xargs -I ROOT lake env lean --run tools/export_proofs.lean ROOT matrix_proofs.json < verification/matrix_roots.txt
xargs -I ROOT lake env lean --run tools/export_proofs.lean ROOT exterior_proofs.json < verification/exterior_roots.txt
```

Each list is one comma-separated argument. The matrix environment contains 316
source modules and the exterior environment contains 55; their 37 common
modules are identified by module and declaration name in the index.

## Find a proof

[theorems.json](theorems.json) gives every theorem or lemma, each alias, its exact
source statement, file, line, module and source references. `source_context`
records the active variable declarations, typeclass hypotheses, open commands
and local notation; `source_scopes` records the enclosing namespaces and
sections. A theorem is identified by its module and name. `compiled` fields
give the type and dependencies read from its compiled environment.

The `compiled` fields are filled for the declarations exported so far;
`tools/export_proofs.lean` adds the others from a complete build.

[modules.json](modules.json) gives the imports, their topological order, the
additional roots and the locations of definitions. Each source dependency
precedes the module that imports it.

[../docs/ARTICLE_CONCORDANCE.md](../docs/ARTICLE_CONCORDANCE.md) follows every
numbered article result and every table address to the Supplemental Material,
program output and theorem. [../docs/PROOFS.md](../docs/PROOFS.md) states the
mathematical objects and hypotheses covered by the proofs. The strings
`prop_N`, `eq_N`, `row_X`, `table_VI`, `table_VII` and `S3_N` remain declaration
names; the concordance supplies the article numbering.

## Order of the proof layers

| Layer | Objects and results |
|---|---|
| `Comparison.System.Spine` | Candidate systems, the postulates, uniqueness, quaternionic dimension and equalities between definitions. |
| `Comparison.System.Geometry` | Distinctions, comparisons, the singlet, six directions and divisions. |
| `Comparison.System.Existence` | Reduced walks, the transmitting amplitude, returns, spin, clocks and the last-step direction. |
| `Comparison.System.Law` | The determinant, positivity, Schur calculus, poles, source derivatives, motion and finite cell equations. |
| `Comparison.System.Completion` | Crossings, couplings, mass formulas, the positive source, retained determinants and the three pairings. |
| `Comparison.System.Table` | Exact values and identities for the comparison rows. |
| `Comparison.System.Finite` | Seventeen collected statements and the ties between definitions used by the layers. |

The libraries in `Comparison/Elements`, `Existence`, `Colour`, `Mass`, `Law`,
`WholePicture`, `Article`, `ArticleStatements`, `JointCells`, `RuleAndLaw`,
`OneFormula`, `GroupsContinuumLaw` and `Formulas` supply these layers and the
independent developments. `Comparison/PauliDirac.lean` gives the explicit Pauli,
Dirac and quaternion matrices.

## Scope of the counts

| Source set | Modules | Theorem declarations, including aliases |
|---|---:|---:|
| `Comparison.System` and the files beneath `Comparison/System/` | 113 | 2456 |
| Its complete import closure | 282 | 6188 |
| Union of the configured library roots | 302 | 6616 |
| All `Comparison` source files | 334 | 6894 |

The 31 aliases give names to existing propositions.
