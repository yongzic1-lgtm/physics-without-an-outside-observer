import Comparison.System.Existence.Line
import Comparison.System.Existence.Excursion
import Comparison.System.Existence.Places
import Comparison.System.Existence.Six
import Comparison.System.Existence.Matter
import Comparison.System.Existence.PairWhole
import Comparison.System.Existence.LastDirectionUnit
import Comparison.System.Existence.IrrepsWhole
import Comparison.System.Existence.LineWhole
import Comparison.System.Existence.ExcursionWhole
import Comparison.System.Existence.PlacesWhole
import Comparison.System.Existence.MatterWhole
import Comparison.System.Existence.PairAlgebras
import Comparison.System.Existence.SixWhole

/-!
# The numbered theorems of the existence layer, in `Comparison.System`

The numbered theorems stand
in `Comparison.System`, one theorem per statement, the helpers in `Comparison.System.Existence`. Each `prop_N` below
is the theorem `Existence.prop_N_full` where the full statement is proved (Props. 24, 30, 31, 32, 34, 38, 39,
46, 99, 40), else `Existence.prop_N`, with its docstring.
-/

namespace Comparison.System

/-- **Proposition 24 (a walk is a reduced word).** `γ_sγ_t` is a number exactly when `s = t`; the step `s`
changes the two-spinor state to its own previous moment, `ℓ_t`, exactly when `s ≠ t`, so the words in which every step changes
that two-spinor state (P5 (b)) are the reduced words, the walks; a line's steps (P5 (a)) change the two-spinor state at each step
exactly when every first segment of them is a walk, and its two-spinor state at the moment `n` is the two-spinor state of the
word of its first `n` steps (P5 (c)); every word reduces to exactly one reduced word by removing pairs `tt`; there
are `5·4ⁿ⁻¹` walks of length `n ≥ 1` (here `n + 1`, `5·4ⁿ`).

Recognition: none (each walk has four continuations, Prop. 26). Uses Props. 4, 10, P5 (a), (b), (c). -/
alias prop_24 := Existence.prop_24_full

/-- **Proposition 25 (the vertices of a line).** The two-spinor state between two moments of a line is `r = ±e_S`, with
`S = T_{t_k} △ ⋯ △ T_{t_{j+1}}` the parities of the steps between them; the two moments are at one vertex exactly
when `S = ∅`; the sets compose, `S(j,k) △ S(k,l) = S(j,l)`; they are exactly the sixteen even sets of lines, so
fixing a moment labels the vertices by the sixteen sets, and another moment adds one set to every label; a step along
`s` takes `x` to `x ⊕ g_s`, `g_s = T_s`; the five steps lead from each vertex to five vertices, as the Clebsch graph
(five neighbours, none in common for two neighbours, two otherwise); the adjacency `A` has the eigenvalue
`5 − 2|U|` on the character `χ_U(x) = (−1)^{|U ∩ x|}`.

Recognition: the vertices are positions relative to one another only; there is no origin. Uses Props. 10, 12, 14. -/
alias prop_25 := Existence.prop_25

/-- **Proposition 26 (eighty states and four continuations).** The state of a line is its two-spinor state and its last-step direction,
`(x, t)`: eighty states; the step is `B(x′, s; x, t) = [s ≠ t][x′ = x ⊕ g_s]` and the undo
`R(x, t) = (x ⊕ g_t, t)`, `R² = 1`; every state has four continuations and four predecessors, `320` arcs; `B + R`
takes each state to its five neighbours, `(B + R)(x′, s; x, t) = [x′ = x ⊕ g_s]`; the two-spinor states and their steps are the cells of `ℝP⁴`, the symmetric states of the five-cube with the whole flip
identified: 16 two-spinor states, 40 links, 40 squares (Prop. 38), 20 cubes and 5 four-cells, with Euler number 1 and one
class in each dimension mod 2 (SI Prop. 116, `Comparison.System.prop_116`, `System/Law/Cells.lean`).

Recognition: none. Uses Props. 24, 25. -/
alias prop_26 := Existence.prop_26

/-- **Proposition 27 (what a line holds).** With `h` the last-step direction and `k′` the step before it (`h ≠ k′`):
`r_{k,k} = Ω`, `r_{k,k−1} = ℓ_h = e_{T_h}`, `r_{k,k−2} = ±e_{h k′}`; on P1's real six
`γ_h ⊗ γ_h = θ_{T_h} = −θ_{\{h,n\}}` and `γ_hγ_{k′} ⊗ γ_hγ_{k′} = θ_{\{h,k′\}}`; the divided sets of the three two-spinor states
are `{}`, `{h, n}`, `F = {h, k′}`, their counterparts `{n}`, `{h}`, `C` (the three lines outside `F`), and these are the six
divisions of Prop. 22 with the singlet fixed, each once: they divide `0, 4, 2, 5, 1, 3` lines.

Recognition: the line holds its own time `{h, n}`, its own direction `{h}`, its clock plane `F` and the three lines
outside it. Uses Props. 10, 22, 24, Definitions 18, 29. -/
alias prop_27 := Existence.prop_27

/-- **Proposition 28 (the coin).** A real `X = aI + b𝟏𝟏ᵀ` with `XᵀX = I` and `X ≠ ±I` is `±σ₅`,
`σ₅ = (2/5)𝟏𝟏ᵀ − I`; a real matrix that no relabelling of the five directions changes is of that form, so `±σ₅` are the
only orthogonal involutions besides `±1` that no relabelling changes; `(σ₅)_{tt} = −3/5`, `(σ₅)_{st} = 2/5`,
`σ₅² = I`; the step from the last-step direction `t` is the line `γ(x_t)`, `x_t = (2/5)𝟏 − e_t` the column of `σ₅`, of length one,
`γ(x_t)² = 1`; on the eighty states `U = (2/5)B − (3/5)R` and `UᵀU = I`.

Recognition: the radar echo of one step, `(3/5)² + 4(2/5)² = 1 = v² + 1/γ²` with `v = 3/5`, `γ = 5/4`. Uses
Props. 4, 26, P1, P2 (a), P3 (b). -/
alias prop_28 := Existence.prop_28

/-- **Proposition 29 (the excursion).** With `f_n` the excursions among the walks of length `n`, divided by `5·4ⁿ⁻¹`:
`F(z) = Σ f_n zⁿ = z⁴(1 + z)/(16 − 8z − 3z² − 3z³)` (for `|z| ≤ 1`); `F(1) = 1`, `Eℓ = F′(1) = Σ n f_n = 16`,
`Var ℓ = 156`; the excursions of length `4, …, 8` number `20, 120, 300, 1200, 4740`; with `P` and `Q` the symmetric and
the vector states an excursion meets, `E P = 10`, `E Q = 5`, `Var P = 84`, `Var Q = 12`, `Cov(P, Q) = 30`,
`Var P − Cov²/Var Q = 9`; an excursion of `ℓ` steps has `ℓ = 1 + P + Q`; and the derivatives of B.29's `F(z, x, y)` at
`(1, 1, 1)` are these moments.

Recognition: a walk comes back to the vertex of its start with chance one, in sixteen steps on average; an excursion
meets one of each of the fifteen two-spinor states other than the singlet on average. Uses Props. 24 to 26, P2 (a). -/
alias prop_29 := Existence.prop_29

/-- **Proposition 30 (the signed excursion).** `A₋ = Σ_t γ_t ⊗ 1` on the sixteen two-spinor states has `A₋² = 5`; at the end of an
excursion the two-spinor state is `σ_w Ω`, `σ_w = ±1`; `Φ(z) = Σ_n zⁿ Σ_{excursions w, |w| = n} σ_w/(5·4ⁿ⁻¹) = −z⁴/(16 + 3z²)`; the
signed counts of the lengths `4, …, 8` are `−20, 0, 60, 0, −180`; no excursion is shorter than four, and the twenty
shortest excursions are the words `tsts` and come back with `−1`; `Φ(1) = −1/19`, `Φ(i) = −1/13`; an excursion keeps its sign
with chance `9/19` and reverses it with chance `10/19`, `a = (F(1) − Φ(1))/8 = 5/38`; and
`b = Var P/(2(Var P + Var Q)) = 7/16`.

Recognition: the sign `−1` of `tsts` is spin one half; the lean `10/19` toward reversal is attraction. Uses
Props. 4, 10, 24, 29. -/
alias prop_30 := Existence.prop_30_full

/-- **Proposition 31 (the transitions of one excursion).** An excursion that begins at a moment whose last-step direction is `h` can be in
`80 − 5 − 1 = 74` states (the five `(∅, t)` end it; `(T_h, h)` is reached only from the start's vertex, by the
undo); they are exactly the states its steps reach, within four steps and for every number of steps from four on; the
uniform law on them is the stationary law of the steps watched on them (each state takes in and gives out the total
weight one); `M = 4·74 = 296` continuations, `C_h = 60` along `h` and `C_j = 59` along each other line;
`c_L = 15/74`, `σ = 75/74`, `η = 295/296`, `σ + 4η = 5`, `η/σ = 59/60`, `σ − 1 = 4(1 − η) = 1/74`; `34` of the `74`
leave `h` undivided, `R_ud = 17/37`.

Recognition: existing tilts a line toward its own direction by one part in `296`. Uses Props. 24, 26. -/
alias prop_31 := Existence.prop_31_full

/-- **Proposition 32 (closed facts).** A gauge transformation takes `U_xy ↦ g_xU_xyg_y⁻¹`; the holonomy of a closed walk
at `x₀` turns by the gauge at its own vertex, `hol ↦ g_{x₀} hol g_{x₀}⁻¹`, so its trace is a fact (for every group of
invertible matrices over every commutative ring); the transport of an open walk from `x` to `y ≠ x` can be gauge-transformed
into every rotation, and only the constants are facts of it.

Recognition: Einstein's point coincidences and the gauge principle, with Wilson's closed loops. Uses P4,
Definition 24. -/
alias prop_32 := Existence.prop_32_full

/-- **Proposition 33 (the vertical step).** On the exterior algebra of `n` directions (the sixty-four sets at `n = 6`):
`ι(v)ε(w) + ε(w)ι(v) = ⟨v, w⟩`, `ε(v)ε(w) + ε(w)ε(v) = 0 = ι(v)ι(w) + ι(w)ι(v)`; `J(v) = ε(v) + ι(v)` has
`J(v)J(w) + J(w)J(v) = 2⟨v, w⟩` and `J(v)² = |v|²`; `J_a f_S = (−1)^{#\{s ∈ S : s < a\}} f_{S △ \{a\}}`;
`J_{s₁} ⋯ J_{s_r} f_∅ = f_{\{s₁,…,s_r\}}` (`s₁ < ⋯ < s_r`); `Λ(O) J(v) Λ(O)⁻¹ = J(Ov)` for every rotation `O`
(`Λ(O)⁻¹ = Λ(Oᵀ)`); and the step of the proof: the whole `w = J₀⋯J₅` turns adding into removing,
`w ε_a = −ι_a w`.

Recognition: dividing a direction and undividing it are one operation. Uses Definitions 13, 26, P3 (b). -/
alias prop_33 := Existence.prop_33

/-- **Proposition 34 (spin one half).** `J_aJ_bJ_aJ_b = −1` (`a ≠ b`): the loop `f_∅ → f_b → f_{ab} → f_a → f_∅`
comes back with `−1`; `R_ab(ϑ) = e^{ϑJ_aJ_b/2} = cos(ϑ/2) + J_aJ_b sin(ϑ/2)`, `R_ab(ϑ) J(v) R_ab(ϑ)⁻¹ = J(O_ϑ v)`
for every `v` (`O_ϑ` the rotation of the plane `(a, b)` by `ϑ`), and `R_ab(2π) = −1` while `O_{2π} = 1`; with the square
root of the sign of a division `D`, `f_x = i^{[x ∈ D]} J_x` has `f_xf_y + f_yf_x = 2θ_D(x)δ_xy` and
`(f_xf_y)² = −θ_D(x)θ_D(y)` (`x ≠ y`): `−1` on the `C(k,2) + C(6−k,2)` planes within a side and `+1` on the
`k(6−k)` planes across (`k = |D|`); and these are the division's kept and moved rotations: a rotation is kept exactly when its
plane lies within one side.

Recognition: spin one half, four quarter turns around a plane come back with `−1`; a loop across the division is a
boost and never closes. Uses Props. 21, 33, Definition 14. -/
alias prop_34 := Existence.prop_34_full

/-- **Proposition 35 (the phase of the whole).** `w = J₀J₁⋯J₅` has `w² = −1`; with the square root of the sign of `D`,
`f₀f₁⋯f₅ = i^{|D|} w`; `Λ(q_D) f_{\{0,…,5\}} = det(q_D) f_{\{0,…,5\}} = i^{|D|} f_{\{0,…,5\}}`;
`Λ(iI) f_S = i^{|S|} f_S`, `z_S = i^{|S|}`; `z_S² = det θ_S = (−1)^{|S|}`; `z_S = 1, i, −1, i, −1, −i` on the six
divided sets `{}, {n}, {h,n}, {h}, F, C` of a line; and `z_{S △ \{n\}} = ±i z_S`.

Recognition: the four phases `1, i, −1, −i`; counterparts differ by a quarter turn. Uses Props. 19, 27, 33, 34. -/
alias prop_35 := Existence.prop_35

/-- **Proposition 36 (the parallel rotation).** `T_ab = ε_aι_b − ε_bι_a = Σ_k Π_kJ_aJ_bΠ_k` (`a ≠ b`); `NT_ab = T_abN`;
`T_abT_bc − T_bcT_ab = T_ac` (`a, b, c` distinct) and `T_abT_cd = T_cdT_ab` (`{a,b} ∩ {c,d} = ∅`);
`J_aJ_b = T_ab + ε_aε_b + ι_aι_b` (`a ≠ b`); `e^{ϑT_ab} = Λ(e^{ϑ(E_ab − E_ba)})`.

Recognition: the parallel rotation is already inside the vertical square; the fifteen rotations of the six act on every
division at once. Uses Props. 17, 33, Definition 26. -/
alias prop_36 := Existence.prop_36

/-- **Proposition 37 (one step joins the two).** `𝒯 = J(a)Λ(U)` is gauge-transformed like one transport,
`Λ(g_x)𝒯_{xy}Λ(g_y)⁻¹ = J(g_xa)Λ(g_xU_{xy}g_y⁻¹)`, for every connection of P4 with values in the rotations of the six;
`𝒯_{xy}⁻¹ = J(U_{yx}a)Λ(U_{yx})` for a unit direction; on the four amplitudes the even words of the step are all the
operators (an isomorphism of real algebras from the even Clifford algebra of the six), with `J_nJ_t ↦ −iγ_t`,
`J_sJ_t ↦ γ_sγ_t`, `w ↦ −i`; so a step of one system along `t` is `γ_t = i J_nJ_t`, two vertical steps; the vertical
steps on the sixty-four sets are a faithful representation of the Clifford algebra of the six.

Recognition: the four amplitudes are the spinor of the six; the quantum `i` is the whole `w`. Uses Props. 4, 5, 33,
P4, Definitions 24, 26. -/
alias prop_37 := Existence.prop_37

/-- **Proposition 38 (curvature).** The curvature `F_st(x) = hol(x; tsts) − 1` turns under a gauge transformation by
the gauge at its vertex, `F_st(x) ↦ g_xF_st(x)g_x⁻¹`; every closed walk of four steps is a square `tsts`; ten
squares pass through each vertex and there are forty in all, which with the sixteen vertices build the cells of `ℝP⁴`
(SI Prop. 116, `Comparison.System.prop_116`); for `U_{xy} = e^{a_{xy}}` near one, with `a = (a₁, …, a₄)` the rotations
of the four steps in order, `hol = exp(Σ aᵢ + ½ Σ_{i>j}[aᵢ, aⱼ]) + O(‖a‖³)` uniformly for small rotations, that is
`log hol = Σ aᵢ + ½ Σ_{i>j}[aᵢ, aⱼ] + O(a³)`.

Recognition: the curvature is the force, `F = dA + A ∧ A` when the vertices are many and the rotations small. Uses
Props. 25, 32, Definition 25. -/
alias prop_38 := Existence.prop_38_full

/-- **Proposition 39 (kept and moved: the mass form).** `M_D(X, X) = ‖[X, P_D]‖² ≥ 0`, zero exactly when `X` is kept;
`M_D = 2` on every unit moved rotation `E_ab − E_ba` (`a ∈ D`, `b ∉ D`); between neighbouring vertices
`DP_D = U_{xy}P_D(y)U_{xy}⁻¹ − P_D(x) ↦ g_x(DP_D)g_x⁻¹`; near one, `U = e^A`,
`DP_D = (P_D(y) − P_D(x)) + (AP_D(y) + P_D(y)Aᵀ) + O(‖A‖²)`, which along the rotations `Aᵀ = −A` is
`(P_D(y) − P_D(x)) + [A, P_D(y)] + O(‖A‖²)`, and for `U = 1 + A` exactly `(P_D(y) − P_D(x)) + [A, P_D(y)] − AP_D(y)A`; with `q_D = 1 + (i − 1)P_D`,
`Dq_D = (i − 1)DP_D` and `‖Dq_D‖² = 2‖DP_D‖²`; along a rotation `X`, `‖Dq_D‖² = 2M_D(X, X)`.

Recognition: the kept rotations are massless gauge fields and the moved rotations massive (Englert, Brout, Higgs). Uses
Prop. 21, Definitions 15, 27. -/
alias prop_39 := Existence.prop_39_full

/-- **Proposition 91 (the common clock).** Phases `q_{xy} = q_{yx}⁻¹` in `U(1)` on the forty links of the sixteen
vertices have a common phase, `z_x = q_{xy}z_y` on every link, exactly when the product of `q` around every closed walk
is one (the vertices being connected); the flat sign `q ≡ −1` closes every square with `(−1)⁴ = +1` and the closed
walk `12345` with `(−1)⁵ = −1`, so it has no common phase; the centre of the kept rotations, in a basis (the sixty-four coordinate sets `D`), has dimension `0, 0, 1, 0`
at the types `0|6, 1|5, 2|4, 3|3` (and their complements), at `2|4` the rotation of the two-direction part, which at the
plane `F = \{h, k\}` is the action of the plane's rotation `γ_hγ_k` on the six.

Recognition: the common time of electromagnetism; the field is the obstruction to it, which the Aharonov–Bohm phase
measures; the flat sign is the loop of `ℝP⁴`. Uses Props. 17, 25, 38, Definition 28. -/
alias prop_91 := Existence.prop_91

/-- **Proposition 40 (the table of the six).** For every last-step direction `h` and plane `{h, k}`, the six divisions a line holds,
`{}`, `{n}`, `{h, n}`, `{h}`, `F = {h, k}`, `C`, have: the types `0¦6, 1¦5, 2¦4, 1¦5, 2¦4, 3¦3`; the time-like
part (the smaller part, where `θ_S = −1`): none, the singlet, the singlet and `h`, the last-step direction, the plane, none; the loops
`−1/+1`: `15/0, 10/5, 7/8, 10/5, 7/8, 6/9` (a loop `(f_xf_y)²` is `−1` within a side, `+1` across); the phases
`z_S = 1, i, −1, i, −1, −i`; kept/moved of the fifteen `15/0, 10/5, 7/8, 10/5, 7/8, 6/9` and of the ten
`10/0, 10/0, 6/4, 6/4, 4/6, 4/6`, counterparts keeping the same ten; a centre of the kept rotations of dimension
`0, 0, 1, 0, 1, 0`, the clocks `E_{n h} − E_{h n}` at `{h, n}` and `E_{h k} − E_{k h}` at `F` (the rotations of `iγ_h`
and `γ_hγ_k`, Prop. 41); every moved unit rotation has `M_S = 2`; for every connection the curvature splits as
`A = A_k + A_m`, `F_k = F(A_k) + (A_m ∧ A_m)_k`, `F_m = D_{A_k}A_m` (the derivatives of the parts are the parts of
the derivative, `keptPart_hasFDerivAt`, `movedPart_hasFDerivAt`); the rows divide the lines `∅`, all five, all but
`h`, `{h}`, `{h, k}`, `C`, and the real form of each row (Definition 15) is the real span of fifteen generators,
`{X : tr X = 0, X†h_D + h_DX = 0}` for the even line sets `D` (`h_D` Hermitian, `h_D² = 1`, trace zero for
`|D| = 2, 4`) and `{X : tr X = 0, XC_D = C_DX}` for the odd ones (`C_D² = −1, −1, +1` at `|D| = 1, 5, 3`); the
balanced directions of each row are the `v ≠ 0` with `|v off S| = |v on S|`, and two of them span one line exactly
when their normalized representatives agree up to sign: the balanced lines are `(S^{5−k} × S^{k−1})/ℤ₂`, `k = |S|`.
The real forms as groups (`SU(4)`, `SU*(4)`, `SU(2,2)`, `SL(4, ℝ)`) are in the geometry layer.

Recognition: `{}` the universality of gravity; `{n}` the sign of time of every pair and the sphere of lines; `{h}`
the ten rotations split at the last-step direction, `6 + 4`, spin connection and co-frame; `{h, n}` the line's own clock; `F` the common
time and light; `C` two times and no clock, colour; the real forms `su(4)`, `sl(2, ℍ)`, `su(2,2)`, `sl(4, ℝ)` and the
balanced directions `S⁴`, `(S¹ × S³)/ℤ₂`, `(S² × S²)/ℤ₂`. Uses Props. 21, 22, 27, 34, 35, 39, Definitions 15, 28. -/
alias prop_40 := Existence.prop_40_full

/-- **Proposition 41 (the clock of a line, and its mass).** `iγ_h` is the clock of `{h, n}`: it is kept, it
commutes with every rotation `{h, n}` keeps, it turns the plane `(n, h)` of the six (as `−2(E_{n h} − E_{h n})`), whose
unit rotation is a clock and spans the centre of the kept rotations; at `{h}` it is moved;
`e^{iaγ_h} = cos a + i sin a γ_h`, `(e^{iaγ_h} ⊗ e^{iaγ_h})Ω = cos 2a Ω + sin 2a iℓ_h`, `e^{i(π/2)γ_h} = iγ_h`;
`γ_hγ_k` (the plane's rotation, `±γ_hγ_k`) is the clock of `F = {h, k}`: kept, commuting with every rotation `F` keeps, its
unit rotation spans the centre; and it is moved at `{h}` and at `{k}`.

Recognition: the line's own time and its rest mass are one rotation, de Broglie's internal clock, `E = mc²`; the plane's
clock is the common time, the conformal time translation of `SU(2,2)`. Uses Props. 17, 21, 40, Definition 28. -/
alias prop_41 := Existence.prop_41

/-- **Proposition 42 (count and amplitude).** For every divided set `S` of the six, read with the singlet undivided as the
division of the lines `D = divLines S` (`|D| ≡ |S|` mod 2): the rotations `S` keeps are exactly those that commute with
`γ_D` (`|S|` even) or with the antilinear `C_S = γ_DΘ` (`|S|` odd); for `S` even the kept form
`h_S = i^{r(r−1)/2}γ_D` is Hermitian and `⟨v, h_S v⟩` is real, a count; for `S` odd, `⟨C_S v, w⟩` is linear in `v`
and in `w`, an amplitude, `C_S² = s_r`, `⟨C_S v, w⟩ = s_r ⟨C_S w, v⟩` (antisymmetric where `C² = −1`, `r = 1, 5`;
symmetric where `C² = +1`, `r = 3`), and `⟨C_S v, C_S u⟩ = ⟨u, v⟩`, so `|⟨C_S v, w⟩|²` is a chance between two
states; `z_S = det q_S`, `z_S² = det θ_S`, `+1` for `S` even and `−1` for `S` odd; and a counterpart has the other parity.

Recognition: a count is a probability, an amplitude a transition amplitude; matter is counted, its counterpart with `n` added is a
quantum amplitude. Uses Props. 7, 19, 35, the Lemma of the divisions (the section on divisions), Definition 29. -/
alias prop_42 := Existence.prop_42

/-- **Proposition 43 (where each piece sits).** An excursion closes the two-spinor state of a line to itself, the singlet, whose
divided set is `{}`, with the counterpart `{n}`; a step along `t` makes `ℓ_t`, divided set `{t, n}`, counterpart `{t}`; for every last-step direction `h`
and plane `{h, k}` of a line (Prop. 27: `r_{k,k} = Ω`, `r_{k,k−1} = ℓ_h`, `r_{k,k−2} = ±e_{hk}`), the three two-spinor states
have the divided sets `{}`, `{h, n}`, `{h, k}` and the counterparts `{n}`, `{h}`, `C` (the three lines outside the plane); every
symmetric state `e_{ab}` has the divided set `{a, b}` and the counterpart `{a, b}'`, the three lines outside it; every divided set is
even (a count, Prop. 42) and its counterpart with `n` added odd (an amplitude).

Recognition: `{}` carries gravity, the proton and the cosmos; `{n}` sizes and moments; `{t, n}` the step; `{t}`
colour per vertex and `α_s`; `{h, n}` the clock and the weak contact; `{h}` the Higgs; `F` the electric plane and
light; `C` the strong force; `{a, b}` the leptons and `{a, b}'` the quarks. Uses Props. 27, 42, Definition 29. -/
alias prop_43 := Existence.prop_43

/-- **Proposition 44 (the step at each divided set).** On the five directions, with `q_S` the square root of the sign of the divided set:
`G_S = q_S†q_S = 1` (`S` even), `G_S = q_Sᵀq_S = θ_S` (`S` odd); `L_S = 𝟏ᵀG_S𝟏 = 5` (`S` even), `5 − 2k` (`S` odd,
`k` lines in `S`), never `0`; the coin at `S`, `σ_S = (2/L_S)𝟏𝟏ᵀG_S − I`, has `σ_S² = I` and `σ_∅ = σ₅`, Prop. 28's
coin; the reflection is `1 − 2/|L_S|` and the weight of a step `w_S = z_S/L_S`; at an even divided set `|w_S| = 1/5`; a symmetric
state continues once to a vector state and three times to symmetric states when its last-step direction is in the plane, twice and twice when
it is not; of the `200` departures from the fifty symmetric states `80` reach a vector state, `120` a plane and `12` each
plane: transmission `2|w_S| = 2/5 = 80/200`, reflection `1 − 2|w_S| = 3/5 = 120/200`, `s = 12/200 = 3/50` per plane; at
`{t}`: `L = 3`, `w = i/3`, reflection `1/3`; at `{n}`: `L = 5`, reflection `3/5`; at the counterpart of a plane named by its three
outside lines `L = −1`, `w = i`, named `{n, a, b}` `L = 1`, `w = −i`; `w² = −1` either way.

Recognition: the reflection `3/5` of the counted step gives `f = (3/5)²/10`, the reflection `1/3` of the coherent one
`α_s² = (1/3)²/8`. Uses Props. 19, 28, 29, 35, 42. -/
alias prop_44 := Existence.prop_44

/-- **Proposition 97 (the reflections are radar steps).** `tanh log 2 = 3/5`, `tanh(log 2/2) = 1/3`,
`tanh(log 2/4) = 3 − 2√2 = tan²(π/8)`, `cosh log 2 = 5/4`; the reflection at every even divided set is `tanh log 2` and at a
line alone `tanh(log 2/2)` (Prop. 44); `tan²(π/8)` is the half phase of the line factor at the last-step direction's phase
(Prop. 51).

Recognition: the reflection of a counted step is the speed of one radar step of rapidity `log 2` (`v = 3/5`, `γ = 5/4`);
the reflection of a step carried as an amplitude halves that rapidity, and the half phase of the line factor quarters it.
Uses Props. 44, 51. -/
alias prop_97 := Existence.prop_97

/-- **Proposition 45 (one generation, seen from the plane).** For every plane `F = {h, k}`: each two-spinor state `e_S`
meets the plane in `N_F = |S ∩ F|` lines and the outside in `N_C = |S ∩ C|`, `N_F + N_C = |S| ∈ {0, 2, 4}`; the
classes `(N_F, N_C) = (0,0), (2,0), (1,1), (0,2), (1,3), (2,2)` hold `1, 1, 6, 3, 2, 3` two-spinor states, with
`Y = N_F/2 − N_C/3 = 0, 1, 1/6, −2/3, −1/2, 1/3`; `Y = Σ_{x ∈ S} y_x` with `y = ½` on the plane and `−⅓` outside,
`Σ_x y_x = 0`; the values of `Y` occur `1, 6, 3, 1, 3, 2` times; `Σ Y = Σ Y³ = 0`, the colour and the doublet sums of
`Y` vanish, as many two-spinor states in triplets as in antitriplets, eight in doublets; `Σ Y⁵ = 5/9`;
`Q = N_k − N_C/3 = T₃ + Y`, `T₃ = (N_k − N_h)/2`, with the charges `0` twice, `2/3, −1/3, −2/3, 1/3` three times,
`±1` once; the last-step direction's vector state is neutral; the ten symmetric states meet `F` in two lines once, in one line six times, in
none three times.

Recognition: with the line charges `(0, 1, −⅓, −⅓, −⅓)` the sixteen two-spinor states are `ν^c` (`Y = 0`), `e^c` (`1`),
`u^c` (`−2/3`, three), `Q` (`1/6`, six), `d^c` (`1/3`, three) and `L` (`−1/2`, two): one generation with its
right-handed neutrino; the vanishing sums are the absence of anomalies; the eight two-spinor states meeting the plane in one
line are the weak doublets, parity broken at the plane. Uses Props. 10, 25. -/
alias prop_45 := Existence.prop_45

/-- **Proposition 46 (the rotations of a pair, and what each keeps).** The ten lines of a pair on `H ⊗ H ⊗ ℂ²`,
`Γ_a = γ_a ⊗ 1 ⊗ σ_x`, `Γ_{5+a} = 1 ⊗ γ_a ⊗ σ_y`, anticommute, `Γ_xΓ_y + Γ_yΓ_x = 2δ_xy`; the two-spinor states are
`σ_z = +1`, on which the rotations `½Γ_xΓ_y` act as `γ_aγ_b ⊗ 1`, `1 ⊗ γ_aγ_b` and `iγ_a ⊗ γ_b` (times `½`); they are
`so(10)`: `M ↦ ρ(M) = ¼ Σ M_xy Γ_xΓ_y` keeps the commutator and is injective on the antisymmetric `M`, dimension
45; `−i Σ_t Γ_tΓ_{5+t} = (L − 1) ⊗ σ_z` and `e^{−iπL/4} = −iP` (as an operator, and on each two-spinor state); the rotations
keeping the comparison are `u(5)`: `Z ↦ ρ([[Re Z, −Im Z], [Im Z, Re Z]])` is an injective real-linear map of Lie
algebras from the anti-Hermitian `5 × 5` matrices onto them, 25 (keeping `L ⊗ 1` likewise), with centre
`ℝ·i(L − 1) ⊗ σ_z`, the rotation `ρ(J) = ½ i(L − 1) ⊗ σ_z` of the complex structure; keeping also the singlet `Ω ⊗ e₊`:
`tr Z = 0`, `su(5)`, 24; keeping also the plane count `N_F = Σ_{t ∈ F}(1 − (γ_t ⊗ γ_t) ⊗ σ_z)/2`: `Z` in
`s(u(3) ⊕ u(2))`, 12, with centre `ℝ·ρ(iY)`; keeping also the last-step direction's two-spinor state `ℓ_h ⊗ e₊`: `Z` in `su(3) ⊕ u(1)`, 9,
with centre `ℝ·ρ(iQ)` — at every plane `F = {h, k}` with the last-step direction `h` (`Z` read after a relabelling `π` with
`π 3 = h`, `π 4 = k`; `Y = ½` on `F`, `−⅓` on `C`; `Q = 0` on `h`, `1` on `k`, `−⅓` on `C`);
`(A, B, z) ↦ (z²A, z̄³B)` maps `SU(3) × SU(2) × U(1)` onto `S(U(3) × U(2))`, with kernel the six images of the sixth
roots of unity, cyclic, and `(SU(3) × SU(2) × U(1))/ℤ₆ ≃ S(U(3) × U(2))`; and on the sixteen, at every plane,
`Tr Y = Tr Y³ = 0` and the colour and the doublet sums of `Y` vanish (`Tr YT_c² = Tr YT₃² = 0`).

Recognition: the gauge group of the standard model, `S(U(2) × U(3)) = (SU(3) × SU(2) × U(1))/ℤ₆`, twelve
generators, held by `SU(5)`; `Y` the hypercharge, `Q` the electric charge. Uses Props. 4, 10, 11, 45. -/
alias prop_46 := Existence.prop_46_full

/-- **Proposition 47 (the last-step direction).** The mass form of the division of a real line is `M_h(X, Y) = 2⟨Xh, Yh⟩`, on
`ℂ⁵ = ℝ¹⁰` `M_v(X, Y) = 2 Re⟨Xv, Yv⟩` for anti-Hermitian `X`, `Y`, so `M_v(X, X) = 2|Xv|²`, and `½M_v` is the
Gram `Re⟨Xv, Yv⟩`; for every plane `F = {h, k}` and every unit vector `v`
of `F`: thirteen rotations that span `u(3) ⊕ u(2)` (the anti-Hermitian matrices with no entry across `F`), orthonormal
for `Re tr(X†Y)`, on which `½M_v(X_i, X_j) = Re⟨X_iv, X_jv⟩ = diag(1, 0, ½, ½, 0, …, 0)`: three of thirteen move
the last-step direction, `w_h = 3/13`, `χ_h = w_h(1 − w_h) = 30/169`; and twelve orthonormal rotations that span `s(u(3) ⊕ u(2))`, on
which the form has `det(x − G) = x⁹(x − ½)²(x − 4/5)`: `½M_v = 4/5, ½, ½, 0⁹`; `(½)/(4/5) = 5/8`,
`sin²θ = 1 − 5/8 = 3/8`.

Recognition: the last-step direction moves `W⁺`, `W⁻` and `Z` (`½, ½, 4/5`); nine stay massless, the photon and the eight colour
rotations; the last-step direction's length is the Higgs scalar; at the source `M_W²/M_Z² = 5/8`, `sin²θ_W = 3/8`. Uses Props. 21, 39,
46, Definition 27. -/
alias prop_47 := Existence.prop_47

/-- **Proposition 48 (singlet, symmetric and vector states).** A two-spinor state disagrees on `N = 0`, `2` or `4` lines, `1 + 10 + 5` two-spinor states,
and none on six (an even set of five lines has at most four); the comparison is `L = 6 − 2N = 6, 2, −2` on them;
`Π₀ = E/4`, `Π_F = (1 + P)/2`, `Π_L = (1 − P)/2 − E/4` are one on the singlet, the symmetric states and the vector states
respectively and zero on the others, `Π₀ + Π_F + Π_L = 1`, and they span the operators the ten keep: an operator on
two systems commutes with the ten rotations `γ_aγ_b ⊗ 1 + 1 ⊗ γ_aγ_b` exactly when it is `c₀Π₀ + c₁Π_F + c₂Π_L`;
cumulatively `Q₁ = 0`, `Q₂ = Π_F`, `Q₃ = Π_F + Π_L`, `Q_n` one on the two-spinor states with `0 < N ≤ 2(n − 1)`.

Recognition: three families and no fourth, the electron at no distinction, the muon reaching the symmetric states, the tau
reaching the vector states. Uses Props. 10, 11, 13. -/
alias prop_48 := Existence.prop_48

/-- **Proposition 99 (the three pairings of the four lines beside the last-step direction).** For every last-step direction `h`: the four lines
beside it pair in exactly three ways; for every plane `{h, k}` and the three lines `c` outside it, with
`K_c = γ_kγ_c` on the last-step direction's side `Q(h)H` (`Q(h) = (1 + γ_h)/2`): `K_c² = −1`, `K_cK_d = −K_dK_c`, each `K_c` keeps
the side (it commutes with `γ_h`), and every operator of the side is `½ tr(X) Q − ½ Σ_c tr(K_cX) K_cQ`, a
combination of `Q` and the three `K_cQ`; for each pairing `{a, b | c, d}` of the four lines,
`(γ_aγ_b)(γ_cγ_d) = ±γ_h`, so on the side `γ_aγ_b = ∓γ_cγ_d`; the pairing vectors, `+1` on the pair of `k` and `−1`
on the other, are orthogonal on the four lines (`Σ_x χ_cχ_{c'} = 4δ`) and sum to `3` at `k` and `−1` at each
outside line, `(3, −1, −1, −1)`; `G_Θ = (5I − 𝖩₃)/4` on `X = (1, −P, −E)`; the singlet, the symmetric and the vector states `Π₀ = E/4`,
`Π_F = (1 + P)/2`, `Π_L = (1 − P)/2 − E/4` are `(1/4) Σ_i (B₃)_{ij} X_i`, so `B₃` changes one basis of the space
into the other and `B₃ᵀG_ΘB₃ = diag(1, 10, 5)` is the Gram matrix of the three projectors; `3(1 + 10 + 5) = 48`.

Recognition: the three families, each one of the three ways the four lines beside the last-step direction split into two symmetric states; on
the last-step direction's doublet the same three are the three rotations of spin. Uses Props. 4, 5, 13, 48. -/
alias prop_99 := Existence.prop_99_full

/-- **Proposition 49 (one plane at its two signs).** For every plane `{a, b}`: at the plane itself (even, a count)
`z = −1`, `L = 5`, `w = −1/5`, `w² = 1/25`; at its counterpart `{a, b}'`, the three lines outside it (odd, an amplitude),
`z = −i`, `L = −1`, `w = i`, `w² = −1`; `Φ(z) = −z²Ψ(z²/16)` with `Ψ(v) = v/(1 + 3v)`; `Ψ(w²) = 1/28` at the plane and
`1/2` at its counterpart with `n` added; the sign `z²` each puts on the clock is `+1`, `−1`; on both signs each two-spinor state of the singlet, the symmetric or the vector states weighs
`|L/6|^{−1/2} = √3`.

Recognition: the charged leptons sit at the plane and the quarks at its counterpart with `n` added, one mass operator for both. Uses
Props. 10, 30, 44. -/
alias prop_49 := Existence.prop_49

/-- **Proposition 50 (the complex weight).** For every plane `{a, b}`: the plane whose one end counts an excursion at `{}`,
`b = Var P/(2(Var P + Var Q)) = 7/16` (Prop. 30), and whose other end carries the three outside lines,
`w_C = i` (Prop. 44), has `b + w_C = 7/16 + i`, of angle `arg(7 + 16i) = arctan(16/7) = 1.15839…`; with the other
orientation of the square root of the sign (`C` named `{n, a, b}`, `w = −i`), `b + w = 7/16 − i`, of angle `−arg(7 + 16i)`.

Recognition: the phase of quark mixing and its sign; the orientation `q` is the one that calls matter matter. Uses
Props. 30, 44. -/
alias prop_50 := Existence.prop_50

/-- **Proposition 51 (the line factor at the last-step direction's phase).** The factor of the law on the vector states,
`1 + 3u + 4u²` at `u = z/4`: `2` at `z = 1` (`u_∅ = 1/4`) and `(3/4)(1 + i)` at the last-step direction's phase `z = i`
(`u_{\{t\}} = i/4`), of phase `π/4`, half phase `π/8`; `tan²(π/8) = 3 − 2√2 = 0.171573…`; at every even divided set
the factor is real and positive.

Recognition: the ratio of the two light neutral masses `ρ_ν = tan²(π/8)`. Uses Props. 35, 44. -/
alias prop_51 := Existence.prop_51

end Comparison.System
