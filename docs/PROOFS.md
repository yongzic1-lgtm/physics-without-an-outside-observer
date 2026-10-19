# Proofs in the order of the article

The Lean development constructs the finite geometry, the directed step and its
determinant, then proves the identities used for returns, source derivatives,
mass formulas and finite field coefficients. The Supplemental Material gives
the physical derivations in the article's eight steps.

The complete result-by-result mapping is
[ARTICLE_CONCORDANCE.md](ARTICLE_CONCORDANCE.md), with its machine-readable
companion [article_concordance.json](article_concordance.json). It includes every
numbered main-text and appendix equation and every address in the two article
tables. Each entry identifies its Supplemental Material section, program and
printed result, then the relevant Lean declaration and its mathematical scope.

## Read a declaration

[../lean/theorems.json](../lean/theorems.json) contains all 6,894 source theorem
declarations: 6,863 explicit `theorem` or `lemma` statements and 31 aliases. Each
entry records the exact source statement, module, file and line. The alias
entries also give the aliased declaration and its source statement.

The `source_context` field records active variable declarations, typeclass
hypotheses, open commands and local notation. `source_scopes` gives the
enclosing namespaces and sections. Together these fields state the context of
each literal theorem header, including hypotheses declared before the theorem.

`source_references` lists names occurring in the proof text. The module imports
give their context. The `compiled` field gives the exact elaborated type, the
constants used by the type and proof, the locations of project dependencies and
the axiom set read from Lean's compiled environment.

The source index covers all 6,894 declarations, with their exact statements and
source context; the `compiled` records are filled for the declarations exported
so far.

[../lean/modules.json](../lean/modules.json) gives the imports and their
topological order, together with the locations of definitions. A declaration is
identified by its module and name. In the two independent libraries, for
example, `Comparison.half_mul_self` names the matrix half-step theorem in
`Comparison.Elements.Half` and the exterior half-step theorem in
`Comparison.Existence.Exterior`. Each theorem retains its statement and its
import environment.

Names such as `prop_57`, `eq_37` and `S3_12` are stable declaration names. Article
numbers are assigned by the concordance.

## Before the eight steps: postulates and geometry

| Result | Declaration | Mathematical scope and dependencies |
|---|---|---|
| Four complex amplitudes and five distinctions | `Comparison.System.uniqueness` | An arbitrary `CandidateSystem` satisfying the finite postulate definitions has complex dimension four, a five-dimensional distinction space, a Clifford frame and the quaternionic structure. The construction is in `System/Postulates.lean` and `Elements/OneModelGeneral.lean`. |
| One quaternionic plane | `Comparison.System.quaternionic_plane` | The associated real dimensions are eight for the carrier and four for the quaternions; the quaternionic dimension is two. |
| Equivalence of candidate systems | `Comparison.System.systems_isomorphic` | A linear isometry carries the quaternionic structure of one candidate system to that of another. |
| Singlet and comparison | `Comparison.System.prop_9`, `Comparison.System.prop_10`, `Comparison.System.prop_11` | The explicit singlet, sixteen pair states and comparison operator, including its swap-and-singlet expression. These use the Clifford model and its two-system basis. |
| Six directions and division | `Comparison.System.prop_16`, `Comparison.System.prop_17`, `Comparison.System.prop_18`, `Comparison.System.prop_19` | The six-dimensional construction, rotations, signs and half-step matrix identities. |

The generic trace crossing identity for arbitrary matrix channel operators is
derived in Supplemental Material S1, from the explicit comparison. Its
normalized colour reading is used in S7, after the signed returns and clock
weights.

The common entry point is `Comparison.System.Spine`. Equalities in
`System/Basic.lean` and `System/Finite/Ties.lean` identify the definitions used by
the supporting libraries.

## 1. One step (Supplemental Material S2)

| Result | Declaration | Mathematical scope and dependencies |
|---|---|---|
| Continuing walks and the directed state | `Comparison.System.prop_24`, `Comparison.System.prop_25`, `Comparison.System.prop_26` | Reduced words, vertices of a continuing line, eighty directed states and four continuations. |
| Each closed walk counted through its cyclic trace | `Comparison.System.eq_12`, `Comparison.System.prop_52` | Formal power-series coefficients of the logarithmic determinant and the sum over primitive cyclic histories with holonomy. The proofs use `System/Law/Euler.lean` and the walk libraries. |
| The global determinant | `Comparison.System.eq_13`, `Comparison.System.S3_5` | Exact finite determinant and grade factorization, with multiplicities one, ten and five. |
| The factor of one encounter | `Comparison.Law.pattern_factor` | For any subset of five channels and any commutative coefficient ring, `(1-u²) det(I-uK)` equals the signed-channel product times the quadratic grade factor. `Comparison.Law.singlet_factor` gives the singlet factor separately. |
| First returns | `Comparison.System.eq_18`, `Comparison.System.prop_55` | The unsigned and signed return series, their sums on the closed unit disk, normalization and mean return length. |

`Comparison.Law.pattern_factor` is the local polynomial identity used before the
product over the sixteen encounters. `Comparison.System.S3_5` collects the
local factors and their global determinant. The source parameter for the return
series is defined in these declarations; the concordance relates it to the
article's variable $u$.

## 2. Two steps (Supplemental Material S3)

| Result | Declaration | Mathematical scope and dependencies |
|---|---|---|
| The half-step carries the clock | `Comparison.Formulas.halfStep_carries_clock` | Conjugation of the clock generator into the plane generator. |
| A central kept rotation | `Comparison.Formulas.central_kept_iff_card` | The central-rotation criterion in the six-direction construction. |
| Quaternion clock triple | `Comparison.Formulas.quaternion_triple` | The three clock and plane generators satisfy the quaternion multiplication identities. |
| Null comparison and its conformal metric | `Comparison.GroupsContinuumLaw.normalized_ray_iff`, `Comparison.GroupsContinuumLaw.balanced_cone` | Normalized null rays are the product of the circle and three-sphere modulo their common sign. The tangent frame has signature (+---); the article chooses the opposite overall metric sign. |

The central rotation and its half-step use the Clifford matrices and singlet
already constructed. The normalized null rays carry the clock and three spatial
directions.

## 3. Any number of directions (Supplemental Material S4)

| Result | Declaration | Mathematical scope and dependencies |
|---|---|---|
| The transmitting amplitude | `Comparison.System.prop_28` | Every real five-channel matrix invariant under simultaneous permutations of rows and columns is a real linear combination of the identity and all-ones matrix. Orthogonality and transmission determine the reflection up to its overall sign. The theorem gives its entries, square, column norms, Clifford square and the orthogonal directed step. |
| Clifford composition and rotation | `Comparison.System.prop_33`, `Comparison.System.prop_34` | Creation and annihilation on arbitrary finite exterior algebras give the Clifford relations and orthogonal covariance. The real half-angle rotor gives its action on the Clifford generators, the sign after a full turn and the counts in a divided set. |
| Count and amplitude for a divided set | `Comparison.System.prop_42`, `Comparison.System.prop_44` | The count and amplitude weights and the step at each divided set in the finite model. |
| Signed determinant and four phase points | `Comparison.System.eq_15`, `Comparison.System.eq_16`, `Comparison.System.S3_7` | The signed adjacency square, signed determinant and renewal identities at the four points $u=i^d/4$. |
| Positivity of the connected finite kernel | `Comparison.System.S3_8` | For a unitary connection of any finite matrix size, the quadratic lower bound $(1-u)(1-4u)$ and positivity of the determinant for $0\leq u<1/4$. |

The division and clock libraries precede the signed determinant and its phase
readings. The positivity statement quantifies over the unitary connection.

## 4. The critical step (Supplemental Material S5)

| Result | Declaration | Mathematical scope and dependencies |
|---|---|---|
| A common pair clock | `Comparison.one_kron_line_singlet`, `Comparison.clock_turns_singlet` | The two actions agree on the singlet; equal unitary clock steps give the double-angle singlet rotation. |
| Exponential form of the clock | `Comparison.Formulas.one_kron_expIγ_singlet` | Equality of the two matrix-exponential actions on the singlet. |
| Green function of the finite germ | `Comparison.System.eq_20` | The explicit inverse on the complement of the constant mode, the four Penrose equations, uniqueness and the two resistance values. |
| Long-wavelength scalar operator | `Comparison.System.eq_24`, `Comparison.critical_operator` | The expansion for a $C^3$ function, with an $O(\varepsilon^3)$ remainder, and identification of the step Laplacian with an orthonormal four-frame. |
| Dispersion of one moving step | `Comparison.System.eq_25` | The exact matrix exponential and eigenphase relation, with an explicit sixth-order bound for the small-phase dispersion. |
| Cell geometry | `Comparison.System.S3_6` | The finite cells, integral and mod-two boundary identities, mod-two homology, circulation rank and circulation Gram spectrum. |

The continuum expansion starts from the finite operator and the five simplex
directions. The determinant and Green function appear before their Taylor
expansions.

| Result | Declaration | Mathematical scope and dependencies |
|---|---|---|
| Exact closing of a block | `Comparison.schur_det`, `Comparison.schur_inv` | The finite Schur determinant identity with an invertible eliminated block; the inverse identity also assumes that the retained Schur complement is invertible. |
| Source derivative of the reduced kernel | `Comparison.System.Law.schur_source_deriv` | Entrywise derivative $S_a=L K_a R$ for an affine source, over a nontrivially normed field with nonzero eliminated determinant. |
| Two-source derivative | `Comparison.System.Law.schur_source_mixed` | The mixed derivative $L(K_{ab}-K_aQK_b-K_bQK_a)R$ for the bilinear two-source family. |
| Residue at a simple zero | `Comparison.System.Law.residue_at_simple_zero` | For an entrywise differentiable matrix, a simple determinant zero and one-dimensional left and right kernels, the actual limit of the scaled inverse and the nonzero residue denominator. |
| Motion of a simple zero | `Comparison.System.Law.zero_shift_pencil` | A differentiable local zero branch of the affine pencil over ℝ or ℂ, with derivative $-l^\dagger S_a r/(l^\dagger S_\zeta r)$. The proof uses the implicit function theorem. |
| Closing collected in one proposition | `Comparison.System.prop_57` | Determinant, inverse, source derivatives, simple-zero residue and local zero branch with their stated hypotheses. |

The full positive-clock norm identity is proved in the Supplemental Material by
reconstructing the eliminated component and differentiating the Schur
complement. It identifies the residue denominator with the norm of the complete
state. The exact Schur calculus above supplies its finite matrix operations.

## 5. The plane (Supplemental Material S6)

| Result | Declaration | Mathematical scope and dependencies |
|---|---|---|
| Transport and curvature | `Comparison.System.prop_38` | Gauge conjugation of the finite curvature, square classification and the cubic-remainder expansion of the four-step holonomy. |
| One fermion family | `Comparison.System.prop_45` | The sixteen exterior occupations, their charges and the linear, cubic and mixed anomaly sums. |
| The plane and last-direction groups | `Comparison.System.prop_46` | The exterior rotation representation, kept Lie algebras, their centres and the group quotient by the cyclic centre of order six. |

## 6. The three directions outside the plane (Supplemental Material S7)

`Comparison.Formulas.finrank_su3` identifies the real dimension eight of the
traceless skew-Hermitian rotations of three complex lines. The construction in
`Formulas/SuThree.lean` exhibits the real coordinates, their injectivity and
their full range before taking the dimension.

| Result | Declaration | Mathematical scope and dependencies |
|---|---|---|
| Crossing moment | `Comparison.WholePicture.mixed_moment_central`, `Comparison.WholePicture.mixed_moment_central_subspaces` | Coordinate divided sets and invariant subspace projectors with two nonsinglet grade weights. The dependence is through the mixed trace and the clock variance. |
| The crossing coefficient | `Comparison.Formulas.crossing_g_sq` | The coefficient $1/72$ for two positive nonsinglet weights and its signed-return identities. |

The Supplemental Material extends the crossing trace identity to the completed
count operator, including the singlet weight. Its explicit trace calculation
gives the normalized coefficient for that full three-grade state.

The colour libraries construct the singlet sectors, tableaux, Gram forms and
projectors used in the composite formulas. Their declarations and source
dependencies are indexed by module in `theorems.json`.

## 7. The last direction (Supplemental Material S8)

| Result | Declaration | Mathematical scope and dependencies |
|---|---|---|
| Nucleon projector | `Comparison.Formulas.Nucleon.PN_idem`, `Comparison.Formulas.Nucleon.rank_PN`, `Comparison.Formulas.Nucleon.axial_Pp` | The spin and isospin doublets in the symmetric three-line space, their rank-four projector, and the axial current of the projected proton. |
| Weak displacement form | `Comparison.System.S3_4` | The explicit twelve-generator Gram form at the last direction, with three nonzero eigenvalues one-half, one-half and four-fifths. |
| Weak, scalar and radial top formulas | `Comparison.System.prop_68` | Algebraic identities for the weak return, scalar source susceptibility and radial top response. |
| The scalar chiral pencil | `Comparison.Article.pencil_det`, `Comparison.Article.pencil_zero` | The determinant and zero equation of the real two-by-two pencil, under the stated nonzero clock factors. |
| Three pairings beside the last direction | `Comparison.System.Completion.Families.pairing_response` | For every last direction, compression of the inverse rooted Gram form to the three orthonormal pairing states gives $40I_3-4J_3$. |
| Pairing spectrum | `Comparison.System.Completion.Families.response_spectrum`, `Comparison.System.Completion.Families.common_mode` | The eigenvalues $28,40,40$ and the common-mode return reading. |

The Supplemental Material proves the full matrix singular-value formulation of
the chiral pencil and the equal division of the normalized clock weight between
its two chiral components. These use positive clock forms and the full-state
normalization established at the critical step.

## 8. The whole (Supplemental Material S9)

| Result | Declaration | Mathematical scope and dependencies |
|---|---|---|
| Completion of the whole frame | `Comparison.System.prop_66`, `Comparison.System.prop_83` | The product of three mean returns gives the whole-frame amplitude and its two-end squared response. |
| Curvature with the last direction | `Comparison.System.Law.curvature_jet` | The finite first-jet decomposition into connection, coframe and torsion terms. |
| Four-spinor trace coefficient | `Comparison.System.Law.trace_four_form` | The ordinary matrix trace and oriented form-index contraction in the explicit Clifford basis. |
| Stationary action on the cells | `Comparison.System.prop_63`, `Comparison.System.eq_30` | Variations of the finite gauge and scalar cell action, its stationary equations, conservation and the finite mass shell. |
| Common proper-time scaling | `Comparison.Formulas.lapse_partials`, `Comparison.Formulas.lapse_zero_scales`, `Comparison.Formulas.lapse_rate`, `Comparison.Formulas.lapse_displacement` | The derivative and zero-scaling identities for $K(E,N)=K(E/N,1)$, including the normalized displacement at a simple zero. |
| Lapse through the reduced kernel | `Comparison.GroupsContinuumLaw.schur_lapse_jet`, `Comparison.GroupsContinuumLaw.on_shell_lapse_charge`, `Comparison.GroupsContinuumLaw.selfS_lapse` | The lapse jet survives Schur reduction; the on-shell algebra gives the energy charge, including the scalar self-energy expression. |
| Real nine-dimensional retained determinant | `Comparison.System.Completion.Neutral.retained_det` | The explicit real basis of the retained $\mathfrak{u}(3)$, its Gram form $G$, the coherent pullback $H=G/3$, and real determinant $3^{-9}$. |
| Complex six-dimensional off-diagonal determinant | `Comparison.System.Completion.Neutral.across_det` | The corresponding complex six-dimensional Gram determinant $3^{-6}$. |
| One positive source for three and twelve | `Comparison.System.Completion.Num.sourceC_deriv`, `Comparison.System.Completion.Num.sourceC_second` | The first two derivatives of the same connected source, using the mean three and variance twelve of the excess vector arrivals. |

The neutral determinant is taken on a real nine-dimensional space. Its proof
first constructs the retained algebra, then its exterior action, then both
Gram forms. The exponent is the dimension of that space.

The source proofs begin with the marked first-return generating function and its
geometric law. They compute the mean and variance before differentiating the
connected source. The Supplemental Material gives the positive occupation
weights of the exponential source.

The Supplemental Material then varies the common continuum action with respect
to the coframe, spin connection, gauge field and matter fields. These continuum
variations use the finite coefficients above. The finite cell stationarity
theorem states the cell action explicitly; the four-spinor trace theorem states
its own matrix and form-index normalization explicitly.

The unit instanton and its normalized integrated density are derived in the
Supplemental Material and recomputed by the article-results program. Their
article addresses are recorded in the concordance.

## One-variable readings, explorations and comparison rows

Part II of the Supplemental Material assigns each classical quantity its
reading or transformation of the variable $u$. `Comparison.Formulas` and
`Comparison.GroupsContinuumLaw` contain the determinant, clock, chart, crossing
and lapse identities used by those readings.

Part III places composite and many-body choices beside their mathematical
formulas. A theorem about a chosen nuclear or cosmological formula proves the
displayed formula under its stated inputs. Its index gives those inputs and the
exact conclusion. Part IV and the article concordance give every comparison
row its program output and theorem address.

The rows in `Comparison.System.Table` collect 157 named comparison formulas.
Their `row_X` names remain available when a present article row uses one of
those formulas. The article's two tables are mapped by their own addresses.

## Build and audit

The pinned configuration is in `lean/lean-toolchain`, `lean/lakefile.toml` and
`lean/lake-manifest.json`. Run from `lean/`:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build Comparison.System
LEAN_NUM_THREADS=1 lake build
LEAN_NUM_THREADS=1 xargs lake build < verification/additional_roots.txt
python tools/check_sources.py
lake env lean Comparison/System/Audit/Axioms.lean
```

[../lean/verification/BUILD.md](../lean/verification/BUILD.md) gives the
commands. The `Comparison.System` subtree contains 2,456 theorem
declarations; the complete import closure contains 6,188. The development
contains 6,894 declarations in 334 `Comparison` source modules.
