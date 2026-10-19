module

public import Comparison.Law.LongZero
public import Comparison.Law.Source
public import Comparison.Colour.Proton
public import Comparison.Existence.Moments

/-!
# The law, VIII: the rows as compositions

The composition of a number from its pieces on their divided sets, by the one rule, at the
address of Proposition 110, is the law. Each retained row is written here as such a composition:
each piece is defined as the rule's value at its divided set (`Rule.lean`: `z_S`, `L_S` from the transported
matrix's minors, `w_S`, `u_S`, the power, `Φ(z_S)`, `Ψ(w_S²)`, `e_S`, `t_S`, `N(S)`) or is one of
Proposition 108's reading-free counts, and the row is proved equal to the book's value.

**The pieces at their divided sets** (`piece_*`): `a = (1 − Φ(z_{}))/8 = 5/38`, `E_U = 1/t_{} = 5/2`,
`b = [12w/(1 − w) + 4w/(1 + 3w)]/8 at w_{} = 1/5: 7/16`, `2/|Φ(z_{})| = 38`, the long mark
`1/|Φ(z_{h,n})| = 19`, the clock's rate `ν = e_{h,n}²/(E_P Eℓ) = 9/4000`, the plane meeting
`f = e_{t,n}²/N(C) = 9/250`, `Φ(z_C) = −1/13`, `e_{t} = 1/3` with power `1/2`, `Ψ(w_{a,b}²) = 1/28`,
`Ψ(w_{a,b,n}²) = 1/2`, `ε_S = (1 + z_S²)/2`, `u_{h} = i/4`, `e_{t,n}/t_{t,n} = 3/2`; the clock
`M_Q` at `{h, n}` with the marks `(0, 1, 2, 3, 19)/4`, its mean gap `2` and spread `61/16`.

**The addresses** (Proposition 110): `address_volume`: the exterior volume `V_B(a)` is the
principal minor of `diag(a sgn L)` on the word `B`, the coefficient of the several-vertices member
`det(I + diag(j)M)` on `B` (`det_one_add_diagonal_mul`); `address_gramTerm`: `E_U = 1/t_{}` is the
k-times member `det(I − J₃/5)⁻¹` on the word of the three pairings; the available transitions count `6M + C_h` is
the first-order coefficient, the zero's angle `1836/320` against one transition's `1/320`.

**The rows** (`row_*`), each proved equal to the book's closed form:
* `row_e`: the unit, one transition per stationary cycle, the zero's angle `1/320`.
* `row_p`: `m_p/m_e = L(Ω)M + C_h + (1/L(Ω)) log E_U + V_{B_L}(a) + V'_{B_h̄}(a)/Eℓ =
  protonPole`, in `(1836.152673412, 1836.1526734121)`; `piece_opened`: `V'_{B_h̄}(a)/Eℓ = −b a⁶`.
* `row_n`: `m_n/m_p = E_U^{Σ_contrasts a^{2Δ_F} + N_F c_L b a⁶} = (5/2)^{5a⁴ + 4a¹⁰ + 10c_Lba⁶}`.
* `row_Lam`: `m_Λ/m_n = E_U^{C_h/320} = (5/2)^{3/16}` (the first order of the available transitions along `h`).
* `row_Delta`: `m_Δ/m_p = 3b = Var P/(4Eℓ) = 21/16`.
* `row_pi0`: `m_π⁰²/(m_e m_p) = (2/|Φ(z_{})|)·h_{h,n} = 38 [M_Q(ν)M_Q(−ν)]^{−3/2}`; `blk_square`: the
  two-end block `[[0, x], [y, 0]]` squares to `xy`.
* `row_pipm`: `m_π±² = m_π⁰² + πα m_p²/(Eℓ(1 − αbΦ(z_C)))`, `alpha_identity`:
  `1/α = 3700/27 − (37/120)h/(297 + N_h)` for `α = c_Lf/(1 − νh/(M + 1 + N_h))`; `piece_Nh`: the
  repeated return `p_k = −Φ(4u_{h}^k)` (odd `k`), `p₁ = 1/13`.
* `row_rho`: `Re s_ρ/m_p² = L(Ω) log x_c`, `x_c = (√313 − 11)/6` the pole of the first return's
  plane-visit function at the record point.
* `massOp`, `row_mu`, `row_tau`, `row_p_quark`, `row_q_quark`: **one mass operator on the symmetric
  and the vector states at the two signs of a plane**,
  `R(Π, S) = e_{t}^{−n_Π/2} exp[−Ψ(w_S²) L_Π (n_Π − ε_S)/4] · clock_Π(z_S²ν)`:
  `m_μ/m_e = R(F, {a,b}) = 3⁵e^{−9/56}M_Q(ν)^{1/6}`, `m_τ/m_μ = R(L, {a,b}) = 3^{5/2}e^{1/14 + 2ν}`,
  `p = R(F, {a,b,n}) = 3⁵e^{−5/2}M_Q(−ν)^{1/6}`, `q = R(L, {a,b,n}) = 3^{5/2}e^{5/4 − 5ν/2}`;
  `row_quarks`: `m_s/m_d = p`, `m_b/m_s = qη`, `m_u/m_d = R_ud = 17/37`, `κ = (3/2)^{8/5}`.

**M1 to M7, written as compositions**:
* M1, the bound state's own terms: `row_p` composes the available transitions count (the zero's angle, `row_e`), the
  Gram-determinant term `(1/L(Ω)) log E_U` (`address_gramTerm`: the k-times member on the three pairings,
  `E_U = 1/t_{}`) and the volumes (`address_volume`: coefficients of the several-vertices member on
  `B_L` and `B_h̄`, with `a = (1 − Φ(z_{}))/8`).
* M2, a meson's squared mass: `row_pi0` (`2/|Φ(z_{})|` at `{}`, the clock overlap at `{h, n}`, the
  two-end block `blk_square`); a meson of two levels is `Composite.lean`'s `compositeDelta`.
* M3, a transition read in the singlet: the transition's weight is `L(Ω) = 1 + 5 det σ[∅, ∅] = 6`
  (`piece_LOmega`), the transported matrix's minor at the singlet.
* M4, the typical weight: `row_Lam` takes the first order `C_h/320` (`availableTransitions_along_rate`).
* M5, the electron: `row_e`, one transition per stationary cycle.
* M6, the clock's marks: `clock_moments`, `piece_h`: marks `(0, 1, 2, 3, 1/|Φ(z_{h,n})|)/4`, rate
  `ν = e_{h,n}²/(E_P Eℓ)`, tilt `z_S²ν` at each end.
* M7, the meeting as a coefficient: `piece_f`, `piece_alphas_sq` (`e_S²/N` with the ends' divided set and
  the contraction's), and Proposition 110's two-ends member (`sourceZ_ends`,
  `logSource_first_order`).

**Missing pieces** (pieces that are neither the rule's value at a divided set nor one of
Proposition 108's counts), each as what is missing and what fills it:
* e. Missing: the bound state that carries one available transition per stationary cycle at `{}` (M5).
  Filled by: a proposition landing a colourless line at here with one continuation of the 296 as
  its count.
* Λ. Missing: why the available transitions weight enters by its first order `C_h/320` (the law's exact zero
  under the same weight is another number; M4). Filled by: a proposition that a bound state's
  weight enters a mass by its first order.
* Δ. Missing: the factor `3` of `3b` on the aligned last-step directions. Filled by: a proposition that
  attaches the count of the three lines outside a plane (`N3`) to the three aligned last-step directions at `F`.
* π⁰. Missing: the two ends `m_e`, `m_p` of the two-end block and the exponent `−3/2` of the clock
  overlap (M2). Filled by: a proposition giving the meson's squared mass as the two-end
  coefficient of the doubled law with these ends, the three pairings each read with the power `1/2`.
* π±. Missing: the factor `π` of the plane contact `πα m_p²/Eℓ`; its other pieces are the rule's
  values (`N_h` at `{h}`, the clock `h` at `{h, n}`, `f` at `{t, n}` on `N(C)`, `b` at `{}`, `Φ` at
  `C`). Filled by: a proposition giving the contact per mean excursion from the plane's rotation.
* ρ. Missing: the transfer `e^{−Q²λ_p²/L(Ω)}` per visit to the symmetric states and the extent `λ_p = 1/m_p`.
  Filled by: a divided set for the extent of a visit to the symmetric states.
* μ, τ, quarks. Missing: the factor `1/4` in `Ψ L (n − ε)/4` and the power `1/6` of the plane clock
  Filled by: a proposition reading `1/6` as `1/L(Ω)` (a count) and `1/4` as `|u_S|` (the
  rule's value at every divided set).
-/

@[expose] public section

namespace Comparison

open Matrix Complex

namespace Law

/-! ## The pieces the rule gives at a divided set -/

/-- The reversal `a_S = (1 − Φ(z_S))/8`. -/
noncomputable def aS (S : Finset (Fin 6)) : ℂ := (1 - PhiS S) / 8

/-- The mean inverse transmission `E_U(S) = 1/t_S`. -/
noncomputable def EUS (S : Finset (Fin 6)) : ℝ := 1 / tS S

/-- The rooted response `b(w_S) = [12w/(1 − w) + 4w/(1 + 3w)]/8`. -/
noncomputable def bS (S : Finset (Fin 6)) : ℂ :=
  (12 * wS S / (1 - wS S) + 4 * wS S / (1 + 3 * wS S)) / 8

/-- The long mark `1/|Φ(z_S)|`. -/
noncomputable def longMark (S : Finset (Fin 6)) : ℝ := 1 / ‖PhiS S‖

/-- The signed return at both closed ends, `2/|Φ(z_S)|`. -/
noncomputable def endsReturn (S : Finset (Fin 6)) : ℝ := 2 / ‖PhiS S‖

/-- The meeting of two ends with the reflection of `S` on `N` vertices, `e_S²/N` (Proposition 64). -/
noncomputable def meetS (S : Finset (Fin 6)) (N : ℕ) : ℝ := eS S ^ 2 / N

/-- The clock's rate at a divided set, `ν_S = e_S²/(E_P Eℓ)` with the counts `E_P = 10`, `Eℓ = 16`. -/
noncomputable def nuS (S : Finset (Fin 6)) : ℝ := eS S ^ 2 / (10 * 16)

/-- The record's term `ε_S = (1 + z_S²)/2`: one common component removed at an even divided set. -/
noncomputable def epsRec (S : Finset (Fin 6)) : ℝ := (1 + (signS S : ℝ)) / 2

theorem norm_real_c (r : ℝ) : ‖(r : ℂ)‖ = |r| := Complex.norm_real r

theorem PhiS_here : PhiS sHere = -1 / 19 := table_here.2.2.2.2.2.2.2.1

theorem piece_a_here : aS sHere = 5 / 38 := by
  rw [aS, PhiS_here]
  norm_num

theorem piece_EU_here : EUS sHere = 5 / 2 := by
  rw [EUS, table_here.2.2.2.2.2.2.1]
  norm_num

theorem piece_b_here : bS sHere = 7 / 16 := by
  rw [bS, table_here.2.2.1]
  norm_num

theorem piece_38 : endsReturn sHere = 38 := by
  rw [endsReturn, PhiS_here, show (-1 / 19 : ℂ) = ((-1 / 19 : ℝ) : ℂ) by push_cast; ring,
    norm_real_c]
  norm_num [abs_of_neg]

theorem piece_longMark_hn : longMark sLastDirectionSinglet = 19 := by
  have h := (table_lineSinglet sLastDirectionSinglet (Or.inr (Or.inl rfl))).2.2.2.2.2.2.2.1
  rw [longMark, h, show (-1 / 19 : ℂ) = ((-1 / 19 : ℝ) : ℂ) by push_cast; ring, norm_real_c]
  norm_num [abs_of_neg]

theorem eS_hn : eS sLastDirectionSinglet = 3 / 5 :=
  (table_lineSinglet sLastDirectionSinglet (Or.inr (Or.inl rfl))).2.2.2.2.2.1

theorem piece_nu_hn : nuS sLastDirectionSinglet = 9 / 4000 := by
  rw [nuS, eS_hn]
  norm_num

/-- **The plane meeting `f = e_{t,n}²/N(C) = 9/250`**, `N(C) = 10` (Proposition 64). -/
theorem piece_f : meetS sLineSinglet (NS sC) = 9 / 250 := by
  rw [meetS, (table_lineSinglet sLineSinglet (Or.inl rfl)).2.2.2.2.2.1, table_C.2.2.2.2.2.2.2.2.2]
  norm_num

/-- **The colour meeting `α_s² = e_{t}²/N(F) = 1/72`**, `N(F) = 8` (Proposition 64). -/
theorem piece_alphas_sq : meetS sLine (NS sF) = 1 / 72 := by
  rw [meetS, (table_line sLine (Or.inl rfl)).2.2.2.2.2.1,
    (table_lineSinglet sF (Or.inr (Or.inr (Or.inr rfl)))).2.2.2.2.2.2.2.2.2]
  norm_num

theorem piece_PhiC : PhiS sC = -1 / 13 := table_C.2.2.2.2.2.2.2.1

theorem piece_e_line : eS sLine = 1 / 3 := (table_line sLine (Or.inl rfl)).2.2.2.2.2.1

theorem piece_Psi_plane : PsiS sPlane = 1 / 28 :=
  (table_lineSinglet sPlane (Or.inr (Or.inr (Or.inl rfl)))).2.2.2.2.2.2.2.2.1

theorem piece_Psi_planeSinglet : PsiS sPlaneSinglet = 1 / 2 :=
  (table_planeSinglet sPlaneSinglet (Or.inl rfl)).2.2.2.2.2.2.2.2.1

theorem piece_eps : epsRec sPlane = 1 ∧ epsRec sPlaneSinglet = 0 := by
  constructor
  · rw [epsRec, show signS sPlane = 1 by decide]
    norm_num
  · rw [epsRec, show signS sPlaneSinglet = -1 by decide]
    norm_num

theorem piece_u_lastDirection : uS sLastDirection = I / 4 := (table_line sLastDirection (Or.inr rfl)).2.2.2.1

/-- `κ`'s base, the ratio of reflection to transmission at `{t, n}`: `e/t = 3/2`. -/
theorem piece_kappa_base : eS sLineSinglet / tS sLineSinglet = 3 / 2 := by
  rw [(table_lineSinglet sLineSinglet (Or.inl rfl)).2.2.2.2.2.1,
    (table_lineSinglet sLineSinglet (Or.inl rfl)).2.2.2.2.2.2.1]
  norm_num

/-! ## The clock at `{h, n}` -/

/-- The marks of the clock at a divided set: the four quick marks and the long mark `1/|Φ(z_S)|`. -/
noncomputable def clockMarks (S : Finset (Fin 6)) : Fin 5 → ℝ :=
  ![0, 1 / 4, 2 / 4, 3 / 4, longMark S / 4]

/-- The ten pairs of marks. -/
def gapList : Fin 10 → Fin 5 × Fin 5 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

/-- The ten gaps of the clock's marks. -/
noncomputable def clockGap (S : Finset (Fin 6)) (i : Fin 10) : ℝ :=
  clockMarks S (gapList i).2 - clockMarks S (gapList i).1

/-- **The clock** `M_Q(x) = (1/10) Σ_gaps e^{−xD}` at the divided set `S`. -/
noncomputable def clockMQ (S : Finset (Fin 6)) (x : ℝ) : ℝ :=
  (1 / 10) * ∑ i, Real.exp (-(x * clockGap S i))

/-- **The clock's overlap of the two signs** `h_S = [M_Q(z_S²ν_S) M_Q(z_{S'}²ν_S)]^{−3/2}`,
`S'` the counterpart. -/
noncomputable def hOv (S : Finset (Fin 6)) : ℝ :=
  (clockMQ S ((signS S : ℝ) * nuS S) * clockMQ S ((signS (twin S) : ℝ) * nuS S)) ^ (-(3 / 2 : ℝ))

theorem clockGap_hn : ∀ i : Fin 10, clockGap sLastDirectionSinglet i =
    ![1 / 4, 2 / 4, 3 / 4, 19 / 4, 1 / 4, 2 / 4, 18 / 4, 1 / 4, 17 / 4, 16 / 4] i := by
  intro i
  fin_cases i <;> simp [clockGap, clockMarks, gapList, piece_longMark_hn] <;> norm_num

/-- **The clock's mean gap `E_D = 2` and spread `Var D = 61/16`** at `{h, n}`. -/
theorem clock_moments :
    (1 / 10) * ∑ i, clockGap sLastDirectionSinglet i = 2 ∧
      (1 / 10) * ∑ i, clockGap sLastDirectionSinglet i ^ 2 - 2 ^ 2 = 61 / 16 := by
  simp only [clockGap_hn, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num

/-- **`h = [M_Q(ν)M_Q(−ν)]^{−3/2}`** at `{h, n}` with its counterpart `{h}`. -/
theorem piece_h : hOv sLastDirectionSinglet =
    (clockMQ sLastDirectionSinglet (9 / 4000) * clockMQ sLastDirectionSinglet (-(9 / 4000))) ^ (-(3 / 2 : ℝ)) := by
  rw [hOv, piece_nu_hn, show signS sLastDirectionSinglet = 1 by decide,
    show twin sLastDirectionSinglet = sLastDirection by decide, show signS sLastDirection = -1 by decide]
  norm_num

/-! ## The addresses -/

/-- **The exterior volume is a principal minor:** `V_B(a) = det diag(a sgn L)[B, B]`, the coefficient
of the several-vertices member on the word `B`. -/
theorem address_volume (B : Finset (Fin 16)) (a : ℝ) :
    volume B a =
      ((diagonal fun k => a * (sgnL k : ℝ)).submatrix (Subtype.val : B → Fin 16) Subtype.val).det := by
  rw [submatrix_diagonal _ _ Subtype.val_injective, det_diagonal, volume]
  rw [← Finset.prod_coe_sort B (fun k => a * (sgnL k : ℝ))]
  rfl

/-- **The Gram-determinant term's address:** `E_U = 1/t_{} = det(I − J₃/5)⁻¹`, the k-times member on the word of
the three pairings. -/
theorem address_gramTerm :
    EUS sHere = sourceZ 1 1 ((1 / 5 : ℝ) • (Matrix.of fun _ _ => (1 : ℝ)) : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [sourceZ_times, piece_EU_here, Matrix.det_fin_three]
  simp
  norm_num

/-! ## The rows -/

/-- **The unit:** the bound state that carries one available transition per stationary cycle turns the zero at
`1/320` per unit phase (`one_transition_angle_rate`); the proton's available transitions at `1836/320`. -/
theorem row_e (h : Fin 5) (a₀ s₀ : State) (h₀ : Continues a₀ s₀) :
    piU ⬝ᵥ (hadPow lawP (oneTransitionX a₀ s₀) 1 *ᵥ 1) = 1 / 320 ∧
      piU ⬝ᵥ (hadPow lawP (availableTransitionsLawX h (transitionX h)) 1 *ᵥ 1) = 1836 / 320 :=
  ⟨one_transition_angle_rate a₀ s₀ h₀, availableTransitions_angle_rate h⟩

/-- The comparison at the singlet, `L(Ω) = 6 = 1 + 5 det σ[∅, ∅]`. -/
theorem piece_LOmega : (Lvalue 0 : ℚ) = 6 ∧ 5 * minor coin (disagreeSet 0) (disagreeSet 0) = 5 := by
  constructor
  · rw [Lvalue]
    simp [disagreeSet]
  · rw [minor_coin_relation]
    simp [Lvalue, disagreeSet]
    norm_num

/-- **The proton composed:** `L(Ω)M + C_h + (1/L(Ω)) log E_U({}) + V_{B_L}(a) + V'_{B_h̄}(a)/Eℓ`. -/
noncomputable def rowP : ℝ :=
  6 * 296 + 60 + (1 / 6) * Real.log (EUS sHere) + volume BL (aS sHere).re +
    (-(7 * (aS sHere).re ^ 6)) / 16

/-- The opened seven-volume over the mean excursion is `−b a⁶`: `|B_h̄|/Eℓ = 7/16 = b({})`. -/
theorem piece_opened : (-(7 * (aS sHere).re ^ 6)) / 16 = -((bS sHere).re * (aS sHere).re ^ 6) := by
  rw [piece_b_here]
  norm_num
  ring

/-- **Row p:** the composition is the book's `6M + C_h + (1/6)log(5/2) − a⁵ − ba⁶`. -/
theorem row_p : rowP = protonPole ∧ (1836.152673412 : ℝ) < rowP ∧ rowP < 1836.1526734121 := by
  have e : rowP = protonPole := by
    rw [rowP, protonPole, piece_EU_here, volume_BL, piece_a_here]
    simp only [Complex.div_ofNat_re, Complex.re_ofNat]
    ring
  refine ⟨e, ?_, ?_⟩
  · rw [e]
    exact protonPole_bounds.1
  · rw [e]
    exact protonPole_bounds.2

/-! ### The plane contrasts on the sixteen vertices (the Petersen graph)

`Existence/Planes.lean` proves the spectrum `0, 2⁵, 5⁴` of the plane Laplacian (`planeLap_charpoly`,
`contrast_sum`); that file cannot be imported beside `Colour/BoundStates.lean` (both name `planeRel`), so
the spectral content is re-proved here on the sixteen vertices from the transition table. -/

/-- The ten plane meetings joined by the steps along their outside lines, on the sixteen vertices. -/
def petAdj16 : Matrix (Fin 16) (Fin 16) ℤ :=
  Matrix.of fun U V =>
    if (disagreeSet U).card = 2 ∧ (disagreeSet V).card = 2 ∧ ∃ t, U = transition t V then 1 else 0

/-- The indicator of the ten symmetric states. -/
def planeInd16 : Matrix (Fin 16) (Fin 16) ℤ :=
  diagonal fun U => if (disagreeSet U).card = 2 then 1 else 0

/-- **The Laplacian of the plane contrasts** `Δ_F = 3 − A_F` on the ten symmetric states. -/
def petLap16 : Matrix (Fin 16) (Fin 16) ℤ := (3 : ℤ) • planeInd16 - petAdj16

/-- `6P₂ = −Δ(Δ − 5)` and `15P₅ = Δ(Δ − 2)`: the spectral projectors of the contrasts. -/
def petP2num : Matrix (Fin 16) (Fin 16) ℤ := -(petLap16 * (petLap16 - (5 : ℤ) • 1))

def petP5num : Matrix (Fin 16) (Fin 16) ℤ := petLap16 * (petLap16 - (2 : ℤ) • 1)

/-- **The plane contrasts:** `Δ(Δ − 2)(Δ − 5) = 0`, `Δ·6P₂ = 2·6P₂`, `Δ·15P₅ = 5·15P₅`, with
`Tr 6P₂ = 30` and `Tr 15P₅ = 60`: five contrasts at `2`, four at `5`, over ten symmetric states. -/
theorem petersen_spectrum :
    petLap16 * (petLap16 - (2 : ℤ) • 1) * (petLap16 - (5 : ℤ) • 1) = 0 ∧
      petLap16 * petP2num = (2 : ℤ) • petP2num ∧ petLap16 * petP5num = (5 : ℤ) • petP5num ∧
      petP2num.trace = 30 ∧ petP5num.trace = 60 ∧ planeInd16.trace = 10 := by
  decide +kernel

/-- The heat trace of the plane contrasts, `Σ_contrasts x^{Δ_F} = Tr P₂ x² + Tr P₅ x⁵`. -/
noncomputable def heatContrasts (x : ℝ) : ℝ :=
  ((petP2num.trace : ℝ) / 6) * x ^ 2 + ((petP5num.trace : ℝ) / 15) * x ^ 5

theorem heatContrasts_eq (x : ℝ) : heatContrasts x = 5 * x ^ 2 + 4 * x ^ 5 := by
  rw [heatContrasts, petersen_spectrum.2.2.2.1, petersen_spectrum.2.2.2.2.1]
  norm_num

/-- The neutron's exponent: the heat trace of the plane contrasts at `a²` and the opened volume on the ten
symmetric states with the last-step direction's share `c_L`. -/
noncomputable def kappaN : ℝ :=
  heatContrasts ((aS sHere).re ^ 2) +
    (planeInd16.trace : ℝ) * (15 / 74) * (bS sHere).re * (aS sHere).re ^ 6

/-- **Row n:** `m_n/m_p = E_U^{κ_n}`. -/
noncomputable def rowN : ℝ := (EUS sHere) ^ kappaN

theorem row_n : rowN = (5 / 2 : ℝ) ^ (5 * (5 / 38 : ℝ) ^ 4 + 4 * (5 / 38) ^ 10 +
    10 * (15 / 74) * (7 / 16) * (5 / 38) ^ 6) := by
  rw [rowN, kappaN, heatContrasts_eq, petersen_spectrum.2.2.2.2.2, piece_EU_here, piece_a_here,
    piece_b_here]
  congr 1
  simp only [Complex.div_ofNat_re, Complex.re_ofNat, Int.cast_ofNat]
  ring

/-- **Row Λ:** `m_Λ/m_n = E_U^{C_h/320}`, the first order of the weight on the 60 available transitions. -/
noncomputable def rowLam : ℝ := (EUS sHere) ^ ((60 : ℝ) / 320)

theorem row_Lam : rowLam = (5 / 2 : ℝ) ^ (3 / 16 : ℝ) ∧
    piU ⬝ᵥ (hadPow lawP (availableTransitionsAlongX 0) 1 *ᵥ 1) = 60 / 320 := by
  refine ⟨?_, ?_⟩
  · rw [rowLam, piece_EU_here]
    congr 1
    norm_num
  · rw [availableTransitions_along_rate]
    norm_num

/-- **Row Δ:** `m_Δ/m_p = 3b`. -/
noncomputable def rowDelta : ℝ := 3 * (bS sHere).re

theorem row_Delta : rowDelta = 21 / 16 ∧ rowDelta = 84 / (4 * 16) := by
  rw [rowDelta, piece_b_here]
  norm_num

/-- The two-end block squares to the product of its ends: `[[0, x], [y, 0]]² = xy`. -/
theorem blk_square (x y : ℝ) : (!![0, x; y, 0] : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 = (x * y) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **Row π⁰:** `m_π⁰²/(m_e m_p) = (2/|Φ(z_{})|) h_{h,n}`. -/
noncomputable def rowPi0 : ℝ := endsReturn sHere * hOv sLastDirectionSinglet

theorem row_pi0 : rowPi0 = 38 *
    (clockMQ sLastDirectionSinglet (9 / 4000) * clockMQ sLastDirectionSinglet (-(9 / 4000))) ^ (-(3 / 2 : ℝ)) := by
  rw [rowPi0, piece_38, piece_h]

/-- The electric coupling with the clock `h` and the repeated return `N`:
`α = c_L f/(1 − νh/(M + 1 + N))`. -/
noncomputable def alphaOf (h N : ℝ) : ℝ :=
  (15 / 74) * meetS sLineSinglet (NS sC) / (1 - nuS sLastDirectionSinglet * h / (296 + 1 + N))

/-- **`1/α = 3700/27 − (37/120)h/(297 + N)`** (Proposition 65). -/
theorem alpha_identity (h N : ℝ) (hN : 297 + N ≠ 0) :
    1 / alphaOf h N = 3700 / 27 - (37 / 120) * h / (297 + N) := by
  rw [alphaOf, piece_f, piece_nu_hn]
  have : (296 + 1 + N) = 297 + N := by ring
  rw [this]
  field_simp
  ring

/-- **The repeated return's terms at the last-step direction `{h}`:** `p_k = −Φ(4u_{h}^k)` for odd `k`, with
`4u_{h}^k = 4(i/4)^k`; `p₁ = 1/13`. -/
theorem piece_Nh (k : ℕ) (hk : Odd k) :
    repReturn k = -Phi (4 * uS sLastDirection ^ k) ∧ repR 1 = 1 / 13 := by
  refine ⟨?_, repR_one⟩
  rw [repReturn, if_pos hk, Phi, piece_u_lastDirection, zPow]
  ring

/-- **Row π±:** `m_π±² = m_π⁰² + πα m_p²/(Eℓ(1 − α b Φ(z_C)))`. -/
noncomputable def rowPipm (mpi0sq mp α : ℝ) : ℝ :=
  mpi0sq + Real.pi * α * mp ^ 2 / (16 * (1 - α * (bS sHere).re * (PhiS sC).re))

theorem row_pipm (mpi0sq mp α : ℝ) :
    rowPipm mpi0sq mp α = mpi0sq + Real.pi * α * mp ^ 2 / (16 * (1 + α * (7 / 16) * (1 / 13))) := by
  rw [rowPipm, piece_b_here, piece_PhiC]
  norm_num

/-- **Row ρ:** `Re s_ρ/m_p² = L(Ω) log x_c`. -/
noncomputable def rowRho : ℝ := 6 * Real.log xc

theorem row_rho : rowRho = 6 * Real.log ((Real.sqrt 313 - 11) / 6) ∧
    16 - 11 * xc - 3 * xc ^ 2 = 0 ∧ 1 < xc := by
  refine ⟨rfl, ?_, xc_gt_one⟩
  rw [GP_denominator]
  ring

/-! ## One mass operator on the symmetric and the vector states at the two signs of a plane -/

/-- The symmetric and the vector states: the symmetric states (`L = 2`, ten two-spinor states) and the vector states (`L = −2`, five). -/
inductive States
  | symmetric
  | vector

/-- The comparison on the singlet, the symmetric or the vector states. -/
def statesL : States → ℝ
  | .symmetric => 2
  | .vector => -2

/-- The two-spinor states of the singlet, the symmetric or the vector states. -/
def statesN : States → ℝ
  | .symmetric => 10
  | .vector => 5

/-- The clock read on the singlet, the symmetric or the vector states at the plane's sign `S`: the plane clock `M_Q(z_S²ν)^{1/6}`, the line clock
`exp[(n − ε_S) z_S²ν/2]`. -/
noncomputable def clockOn (P : States) (S : Finset (Fin 6)) : ℝ :=
  match P with
  | .symmetric => clockMQ sLastDirectionSinglet ((signS S : ℝ) * nuS sLastDirectionSinglet) ^ (1 / 6 : ℝ)
  | .vector => Real.exp ((statesN .vector - epsRec S) * ((signS S : ℝ) * nuS sLastDirectionSinglet) / 2)

/-- **The one mass operator** `exp Tr(Π H_S)` on the projector `Π` at the plane's sign `S`:
`e_{t}^{−n/2} exp[−Ψ(w_S²) L (n − ε_S)/4] · clock`. -/
noncomputable def massOp (P : States) (S : Finset (Fin 6)) : ℝ :=
  eS sLine ^ (-(statesN P) / 2) * Real.exp (-((PsiS S).re * statesL P * (statesN P - epsRec S) / 4)) *
    clockOn P S

/-- **`m_μ/m_e = 3⁵ e^{−9/56} M_Q(ν)^{1/6}`.** -/
theorem row_mu : massOp .symmetric sPlane =
    3 ^ (5 : ℝ) * Real.exp (-(9 / 56)) * clockMQ sLastDirectionSinglet (9 / 4000) ^ (1 / 6 : ℝ) := by
  rw [massOp, clockOn, piece_e_line, piece_Psi_plane, piece_eps.1, piece_nu_hn,
    show signS sPlane = 1 by decide]
  simp only [statesN, statesL]
  rw [show (1 / 3 : ℝ) ^ (-(10 : ℝ) / 2) = 3 ^ (5 : ℝ) by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    norm_num]
  norm_num

/-- **`m_τ/m_μ = 3^{5/2} e^{1/14 + 2ν}`.** -/
theorem row_tau : massOp .vector sPlane = 3 ^ (5 / 2 : ℝ) * Real.exp (1 / 14 + 2 * (9 / 4000)) := by
  rw [massOp, clockOn, piece_e_line, piece_Psi_plane, piece_eps.1, piece_nu_hn,
    show signS sPlane = 1 by decide]
  simp only [statesN, statesL]
  rw [show (1 / 3 : ℝ) ^ (-(5 : ℝ) / 2) = 3 ^ (5 / 2 : ℝ) by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    norm_num]
  rw [mul_assoc, ← Real.exp_add]
  norm_num

/-- **`p = 3⁵ e^{−5/2} M_Q(−ν)^{1/6}`.** -/
theorem row_p_quark : massOp .symmetric sPlaneSinglet =
    3 ^ (5 : ℝ) * Real.exp (-(5 / 2)) * clockMQ sLastDirectionSinglet (-(9 / 4000)) ^ (1 / 6 : ℝ) := by
  rw [massOp, clockOn, piece_e_line, piece_Psi_planeSinglet, piece_eps.2, piece_nu_hn,
    show signS sPlaneSinglet = -1 by decide]
  simp only [statesN, statesL]
  rw [show (1 / 3 : ℝ) ^ (-(10 : ℝ) / 2) = 3 ^ (5 : ℝ) by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    norm_num]
  norm_num

/-- **`q = 3^{5/2} e^{5/4 − 5ν/2}`.** -/
theorem row_q_quark : massOp .vector sPlaneSinglet =
    3 ^ (5 / 2 : ℝ) * Real.exp (5 / 4 - 5 * (9 / 4000) / 2) := by
  rw [massOp, clockOn, piece_e_line, piece_Psi_planeSinglet, piece_eps.2, piece_nu_hn,
    show signS sPlaneSinglet = -1 by decide]
  simp only [statesN, statesL]
  rw [show (1 / 3 : ℝ) ^ (-(5 : ℝ) / 2) = 3 ^ (5 / 2 : ℝ) by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    norm_num]
  rw [mul_assoc, ← Real.exp_add]
  norm_num

/-- **The quark ratios:** `m_s/m_d = p`, `m_b/m_s = qη`, `m_u/m_d = R_ud = 17/37`,
`κ = (e/t)_{t,n}^{Eℓ/E_P} = (3/2)^{8/5}`. -/
theorem row_quarks :
    massOp .vector sPlaneSinglet * (295 / 296) =
        3 ^ (5 / 2 : ℝ) * Real.exp (5 / 4 - 5 * (9 / 4000) / 2) * (295 / 296) ∧
      (34 : ℚ) / 74 = 17 / 37 ∧
      (eS sLineSinglet / tS sLineSinglet) ^ ((16 : ℝ) / 10) = (3 / 2 : ℝ) ^ (8 / 5 : ℝ) := by
  refine ⟨by rw [row_q_quark], by norm_num, ?_⟩
  rw [piece_kappa_base]
  norm_num

end Law

end Comparison

end
