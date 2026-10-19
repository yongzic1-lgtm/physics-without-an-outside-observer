import Comparison.System.Postulates
import Comparison.Article
import Comparison.GroupsContinuumLaw
import Comparison.Formulas
import Comparison.System.Completion.Ext.Neutral

set_option linter.style.longLine false

/-!
# The proof system, the completions, part 0: the numbers of the law that compose the constants

The SI table of the numbers of the law that compose the rows, each
number **defined as the law's own object** and proved equal to its value:

* the grade factors `k_N ≡ k_N(−1/4)` of the law `det(I − uB) = (1 − u²)²⁴k₀k₂¹⁰k₄⁵` (`kN`, Eq. (21));
* the rule's transmission and reflection at the divided sets (Prop. 200): `t = t@{}`, `e = e@{}`, `t_line = t@{t}`,
  `e_line = e@{t}`;
* the counts of the six: `k_C` (the lines of `C`), `N₂` (the symmetric states);
* the excursion (Prop. 29): `Eℓ`, `Var ℓ` as sums over the counts of the excursions, `E P`, `E Q`, `Var P`, `Var Q`, `Cov`
  from the excursion's generating function in the plane and arrivals at the vector states (E's Prop. 29 ties it to the excursions' counts);
  `F(1, x, 1) = x²/(4 − 3x)`: the arrivals `K = Q − 2` beyond the two compulsory ones have `G(x) = 1/(4 − 3x)`,
  `E K = 3`, `Var K = 12`, and the connected source `C(j) = a¹¹ log G(e^j)` of the one positive volume has
  `C′(0) = 3a¹¹`, `C″(0) = 12a¹¹` (the one source of rows F01 and F03);
* the available transitions of a last-step direction (Prop. 31): `M`, `C_h`, `C_j`, `c_L`, `σ`, `η`, `R_ud`, `E_H`;
* the signed returns (Prop. 30): `Φ(z) = Σ_n φ(n)zⁿ`, `Φ(1) = −1/19`, `Φ(i) = −1/13`; `a = (F(1) − Φ(1))/8`,
  `b = b(w@{})`, `χ_A`, `w_h`, `χ_h`;
* the plane meeting and the clock (Props. 64, 206, 72): `f`, `ν`, `h`, `N_h`, the contact `x`, the coupling `α`;
* the weak retained excursion `W_W`, `G_Fm_p²`, gravity's amplitude `W`, the colour coupling `α_s`;
* `x_c`, `κ`, `L(Ω)`, `E_U`, the available transition sum;
* the proton's pole (Prop. 82) and the neutron's exponent (Prop. 120) as compositions of these;
* the heavy neutral exponent: `det(G⁻¹H) = 3⁻⁹` on the kept algebra `k = {diag(0, −Tr A, A) : A ∈ u(3)}` of real
  dimension nine, and `det_ℂ(G_off⁻¹H_off) = 3⁻⁶` on `Hom_ℂ(F, C)` (`Ext/Neutral.lean`; rows T01, T02).

The outside inputs (the unit `m_e c²`, `ħ`, `ħc`, the megaparsec, the Julian year) are named and marked as such.
-/

namespace Comparison.System.Completion.Num

open Real Complex Matrix Comparison Comparison.Law

/-! ## The grade factors at the point `u = −1/4` (Eq. (21)) -/

/-- `k_N ≡ k_N(−1/4)`, the grade factor of the law at the point `u = −1/4`. -/
noncomputable def k (N : ℕ) : ℝ := WholePicture.kN N (-1 / 4)

theorem k_zero : k 0 = 5 / 2 := by simpa [k, kR_eq_kN] using WholePicture.grade_factors_plane_quarter.1
theorem k_two : k 2 = 3 / 2 := by simpa [k, kR_eq_kN] using WholePicture.grade_factors_plane_quarter.2.1
theorem k_four : k 4 = 1 / 2 := by simpa [k, kR_eq_kN] using WholePicture.grade_factors_plane_quarter.2.2

/-! ## Transmission and reflection at the divided sets (Prop. 200) -/

/-- The transmission at an even divided set, `t = t@{}`. -/
noncomputable def t : ℝ := tS sHere
/-- The reflection at an even divided set, `e = e@{}`. -/
noncomputable def e : ℝ := eS sHere
/-- The transmission at a line, `t_line = t@{t}`. -/
noncomputable def tLine : ℝ := tS sLine
/-- The reflection at a line, `e_line = e@{t}`. -/
noncomputable def eLine : ℝ := eS sLine

theorem t_eq : t = 2 / 5 := table_here.2.2.2.2.2.2.1
theorem e_eq : e = 3 / 5 := table_here.2.2.2.2.2.1
theorem tLine_eq : tLine = 2 / 3 := (table_line sLine (Or.inl rfl)).2.2.2.2.2.2.1
theorem eLine_eq : eLine = 1 / 3 := (table_line sLine (Or.inl rfl)).2.2.2.2.2.1

/-! ## The counts of the six -/

/-- `k_C`, the lines of the divided set `C` outside the plane `hk`. -/
def kC : ℕ := linesIn sC
/-- `N₂`, the symmetric states among the sixteen. -/
def N2 : ℕ := (Finset.univ.filter fun U : Fin 16 => (disagreeSet U).card = 2).card

theorem kC_eq : kC = 3 := by decide
theorem N2_eq : N2 = 10 := by decide

/-! ## The excursion (Prop. 29) -/

/-- `Eℓ`, the mean length of one excursion: `Σ_n n f(n)` over the counts of the excursions. -/
noncomputable def El : ℝ := ∑' n : ℕ, (n : ℝ) * excursionLaw n
/-- `Var ℓ`. -/
noncomputable def VarEll : ℝ := (∑' n : ℕ, (n : ℝ) ^ 2 * excursionLaw n) - El ^ 2

theorem El_eq : El = 16 := excursion_mean.tsum_eq
theorem VarEll_eq : VarEll = 156 := by
  rw [VarEll, El]
  exact excursion_variance

/-- `E P`, the mean number of visits to the symmetric states of one excursion, from `F(1, 1, y)`; it is the mean over the excursions
`Existence.excursionMean Existence.fP` (`System.num_moments_eq`, from E's Prop. 29). -/
noncomputable def EP : ℝ := deriv (fun y => excursionF 1 1 y) 1
/-- `E Q`, the mean number of arrivals at the vector states, from `F(1, x, 1)`; the mean over the excursions
`Existence.excursionMean Existence.fQ` (`System.num_moments_eq`). -/
noncomputable def EQ : ℝ := deriv (fun x => excursionF 1 x 1) 1
/-- `Var P`, `Var Q`, `Cov(P, Q)`: the derivatives of the excursion's generating function; they are the moments over the
excursions `Existence.varP`, `Existence.varQ`, `Existence.covPQ` (`System.num_moments_eq`). -/
noncomputable def VarP : ℝ := Article.varP
noncomputable def VarQ : ℝ := Article.varQ
noncomputable def Cov : ℝ := Article.covPQ

theorem EP_eq : EP = 10 := Comparison.EP_eq
theorem EQ_eq : EQ = 5 := Comparison.EQ_eq
theorem VarP_eq : VarP = 84 := Article.moments_values.1
theorem VarQ_eq : VarQ = 12 := Article.moments_values.2.1
theorem Cov_eq : Cov = 30 := Article.moments_values.2.2

/-! ## The arrivals at the vector states beyond the two compulsory ones (rows F01, F03) -/

/-- **`F(1, x, 1) = x²/(4 − 3x)`**: the first return with its arrivals at the vector states marked by `x`, at `z = y = 1`. -/
theorem excursionF_vector (x : ℝ) : excursionF 1 x 1 = x ^ 2 / (4 - 3 * x) := by
  rw [Comparison.excursionF_x, show (8 : ℝ) - 6 * x = 2 * (4 - 3 * x) by ring]
  exact mul_div_mul_left _ _ two_ne_zero

/-- `G(x) = 1/(4 − 3x)`: the generating function of the arrivals `K = Q − 2` at the vector states beyond the two
compulsory ones of every return. -/
noncomputable def GK (x : ℝ) : ℝ := 1 / (4 - 3 * x)

/-- **Every return has two compulsory arrivals at the vector states:** `F(1, x, 1) = x²G(x)`. -/
theorem excursionF_eq_GK (x : ℝ) : excursionF 1 x 1 = x ^ 2 * GK x := by
  rw [excursionF_vector, GK, mul_one_div]

/-- **The law of `K`:** `Pr(K = k) = (1/4)(3/4)ᵏ`, and `Σ_k Pr(K = k)xᵏ = G(x)` for `|x| < 4/3`. -/
theorem GK_law (x : ℝ) (hx : |x| < 4 / 3) :
    HasSum (fun k : ℕ => (1 / 4 : ℝ) * (3 / 4) ^ k * x ^ k) (GK x) := by
  have hr : |3 / 4 * x| < 1 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]
    linarith
  have h := (hasSum_geometric_of_abs_lt_one hr).mul_left (1 / 4)
  convert h using 1
  · funext k
    rw [mul_pow]
    ring
  · rw [GK, show (1 : ℝ) - 3 / 4 * x = (4 - 3 * x) / 4 by ring, inv_div, ← mul_div_assoc]
    norm_num

theorem GK_hasDerivAt (x : ℝ) (hx : 4 - 3 * x ≠ 0) : HasDerivAt GK (3 / (4 - 3 * x) ^ 2) x := by
  have hD : HasDerivAt (fun y : ℝ => 4 - 3 * y) (-(3 * 1)) x :=
    ((hasDerivAt_id x).const_mul 3).const_sub 4
  have h := (hasDerivAt_const x (1 : ℝ)).div hD hx
  show HasDerivAt (fun y : ℝ => 1 / (4 - 3 * y)) _ x
  convert h using 1
  ring

theorem GK_second : HasDerivAt (fun x : ℝ => 3 / (4 - 3 * x) ^ 2) 18 1 := by
  have h1 : HasDerivAt (fun x : ℝ => 4 - 3 * x) (-3) 1 :=
    (((hasDerivAt_id (1 : ℝ)).const_mul 3).const_sub 4).congr_deriv (by norm_num)
  have hD : HasDerivAt (fun x : ℝ => (4 - 3 * x) ^ 2) (-6) 1 :=
    (h1.pow 2).congr_deriv (by norm_num)
  refine ((hasDerivAt_const (1 : ℝ) (3 : ℝ)).div hD (by norm_num)).congr_deriv ?_
  norm_num

/-- `E K = G′(1)`. -/
noncomputable def EK : ℝ := deriv GK 1
/-- `Var K = G″(1) + G′(1) − G′(1)²`. -/
noncomputable def VarK : ℝ := deriv (deriv GK) 1 + deriv GK 1 - deriv GK 1 ^ 2

/-- **`E K = 3`.** -/
theorem EK_eq : EK = 3 := by
  rw [EK, (GK_hasDerivAt 1 (by norm_num)).deriv]
  norm_num

open Filter Topology in
theorem GK_deriv_deriv : deriv (deriv GK) 1 = 18 := by
  refine Comparison.deriv_deriv_of ?_ GK_second
  have hc : ContinuousAt (fun x : ℝ => 4 - 3 * x) 1 := by fun_prop
  filter_upwards [hc.eventually_ne (by norm_num : (4 - 3 * 1 : ℝ) ≠ 0)] with x hx
  exact GK_hasDerivAt x hx

/-- **`Var K = 18 + 3 − 9 = 12`.** -/
theorem VarK_eq : VarK = 12 := by
  rw [VarK, GK_deriv_deriv, (GK_hasDerivAt 1 (by norm_num)).deriv]
  norm_num

/-- **`K = Q − 2`:** `E K = E Q − 2` and `Var K = Var Q`, with `E Q = 5`, `Var Q = 12` from `F` (`EQ_eq`, `VarQ_eq`). -/
theorem EK_eq_EQ : EK = EQ - 2 := by rw [EK_eq, EQ_eq]; norm_num

theorem VarK_eq_VarQ : VarK = VarQ := by rw [VarK_eq, VarQ_eq]

/-! ## The available transitions of the last-step direction `h = 0` (Prop. 31) -/

/-- `M`, the continuations of the available transitions of a last-step direction. -/
def M : ℕ := ∑ j, alongCount 0 j
/-- `C_h`, those along the last-step direction. -/
def Ch : ℕ := alongCount 0 0
/-- `C_j`, those along another line. -/
def Cj : ℕ := alongCount 0 1
/-- The states of the available transitions that leave the last-step direction undivided. -/
def Nup : ℕ := ((excursionStates 0).filter fun s => (0 : Fin 5) ∉ disagreeSet s.1).card
/-- The states of the available transitions. -/
def Nlife : ℕ := (excursionStates 0).card

theorem M_eq : M = 296 := availableTransitions_total 0
theorem Ch_eq : Ch = 60 := (availableTransitions_along 0).1
theorem Cj_eq : Cj = 59 := (availableTransitions_along 0).2 1 (by decide)
theorem Nup_eq : Nup = 34 := availableTransitions_up 0
theorem Nlife_eq : Nlife = 74 := card_excursionStates 0

/-- `c_L = C_h/M`, `σ = 5C_h/M`, `η = 5C_j/M`, `R_ud = 34/74`. -/
noncomputable def cL : ℝ := (Ch : ℝ) / M
noncomputable def sigma : ℝ := 5 * (Ch : ℝ) / M
noncomputable def eta : ℝ := 5 * (Cj : ℝ) / M
noncomputable def Rud : ℝ := (Nup : ℝ) / Nlife

theorem cL_eq : cL = 15 / 74 := by rw [cL, Ch_eq, M_eq]; norm_num
theorem sigma_eq : sigma = 75 / 74 := by rw [sigma, Ch_eq, M_eq]; norm_num
theorem eta_eq : eta = 295 / 296 := by rw [eta, Cj_eq, M_eq]; norm_num
theorem Rud_eq : Rud = 17 / 37 := by rw [Rud, Nup_eq, Nlife_eq]; norm_num

/-- `E_H`, the available transitions along the last-step direction per excursion of the stationary walk (Prop. 71). -/
noncomputable def EH : ℝ :=
  ∑' n : ℕ, (∑ s ∈ (excursionStates 0).filter (fun s => s.2 ≠ 0), (stateCount n s : ℝ)) / (5 * 4 ^ n) / 4

theorem EH_eq : EH = 3 := (steps_along_lastDirection 0).tsum_eq

/-- The available transition sum `Σ_transitions (L(Ω) + [along h])` of the last-step direction `h = 0` (Prop. 78). -/
def transitionSum : ℕ :=
  ∑ p ∈ Finset.univ.filter (fun p : State × State => inExcursion 0 p.1 = true ∧ Continues p.1 p.2),
    (6 + if p.2.2 = 0 then 1 else 0)

theorem transitionSum_eq : transitionSum = 1836 := transition_inventory 0

/-! ## The comparison at the singlet and the pairings' Gram-determinant term -/

/-- `L(Ω) = ⟨Ω, LΩ⟩`, the comparison at the singlet. -/
noncomputable def LOmega : ℝ := (star Ω ⬝ᵥ (L *ᵥ Ω)).re

theorem LOmega_eq : LOmega = 6 := by
  rw [LOmega, Comparison.Formulas.LOmega_inner]; norm_num

/-- `E_U = 1/t@{}`, the ratio of the two levels of the pairings' Gram (Prop. 80). -/
noncomputable def EU : ℝ := EUS sHere

theorem EU_eq : EU = 5 / 2 := piece_EU_here

/-! ## The signed returns and the odd-point counts (Props. 30, 42) -/

/-- `Φ(z) = Σ_n φ(n) zⁿ`, the signed excursion. -/
noncomputable def Phi (z : ℂ) : ℂ := ∑' n : ℕ, (signedLaw n : ℂ) * z ^ n

theorem Phi_closed (z : ℂ) (hz : ‖z‖ ≤ 1) : Phi z = -z ^ 4 / (16 + 3 * z ^ 2) :=
  (signed_gf z hz).tsum_eq

/-- **The rule's `Φ` is the signed excursion** on the closed unit disc (Prop. 200 against Prop. 30). -/
theorem rulePhi_eq (z : ℂ) (hz : ‖z‖ ≤ 1) : Law.Phi z = Phi z := by
  rw [Phi_closed z hz, Law.Phi]

theorem Phi_one : Phi 1 = -1 / 19 := by
  rw [Phi_closed 1 (by simp)]; norm_num

theorem Phi_I : Phi I = -1 / 13 := by
  rw [Phi_closed I (by simp)]
  rw [show I ^ 4 = 1 by rw [pow_succ, pow_succ, pow_succ, pow_one]; simp, I_sq]
  norm_num

/-- `F(z) = Σ_n f(n) zⁿ`, the first return. -/
noncomputable def F (z : ℂ) : ℂ := ∑' n : ℕ, (excursionLaw n : ℂ) * z ^ n

theorem F_closed (z : ℂ) (hz : ‖z‖ ≤ 1) : F z = excursionGF z := (excursion_gf_eq z hz).tsum_eq

/-- The first return on the real line. -/
noncomputable def Fr (z : ℝ) : ℝ := ∑' n : ℕ, excursionLaw n * z ^ n

theorem Fr_closed (z : ℝ) (hz : |z| ≤ 1) :
    Fr z = z ^ 4 * (1 + z) / (16 - 8 * z - 3 * z ^ 2 - 3 * z ^ 3) := by
  have hc := excursion_gf (z : ℂ) (by rw [Complex.norm_real]; exact hz)
  have hr : HasSum (fun n => ((excursionLaw n * z ^ n : ℝ) : ℂ))
      (((z ^ 4 * (1 + z) / (16 - 8 * z - 3 * z ^ 2 - 3 * z ^ 3) : ℝ)) : ℂ) := by
    convert hc using 1
    · funext n; push_cast; ring
    · push_cast; ring
  exact (Complex.hasSum_ofReal.mp hr).tsum_eq

/-- `a = (F(1) − Φ(1))/8`, the reversal per continuation. -/
noncomputable def a : ℝ := ((∑' n : ℕ, excursionLaw n) - (∑' n : ℕ, signedLaw n)) / 8

theorem a_eq : a = 5 / 38 := a_value.1

/-- `b = b(w@{})`, the rooted response at here. -/
noncomputable def b : ℝ := (bS sHere).re

theorem b_eq : b = 7 / 16 := by rw [b, piece_b_here]; norm_num

/-- `χ_A = 1/(1 + Φ(i))`, `w_h = 1/(4χ_A)`, `χ_h = w_h(1 − w_h)`. -/
noncomputable def chiA : ℝ := (1 / (1 + Phi I)).re
noncomputable def wh : ℝ := 1 / (4 * chiA)
noncomputable def chih : ℝ := wh * (1 - wh)

theorem chiA_eq : chiA = 13 / 12 := by rw [chiA, Phi_I]; norm_num
theorem wh_eq : wh = 3 / 13 := by rw [wh, chiA_eq]; norm_num
theorem chih_eq : chih = 30 / 169 := by rw [chih, wh_eq]; norm_num

/-! ## The plane meeting and the clock (Props. 64, 206, 72) -/

/-- `f = e@{t,n}²/N(C)`, the plane meeting. -/
noncomputable def f : ℝ := meetS sLineSinglet (NS sC)
/-- `ν = e@{h,n}²/(E_P Eℓ)`, the plane meeting per mean excursion. -/
noncomputable def nu : ℝ := nuS sLastDirectionSinglet

theorem f_eq : f = 9 / 250 := piece_f
theorem nu_eq : nu = 9 / 4000 := piece_nu_hn

/-- `M_Q(x) = (1/10)Σ_D e^{−xD}`, the clock at `{h, n}` with its ten gaps. -/
noncomputable def MQ (x : ℝ) : ℝ := clockMQ sLastDirectionSinglet x

/-- `h = [M_Q(ν)M_Q(−ν)]^{−3/2}`, the overlap of the clock's two signs (Prop. 206). -/
noncomputable def h : ℝ := hOv sLastDirectionSinglet

theorem h_closed : h = (MQ (9 / 4000) * MQ (-(9 / 4000))) ^ (-(3 / 2 : ℝ)) := piece_h

theorem h_eq_q : h = Article.qH := Article.hOv_eq

theorem h_pos : 0 < h := by rw [h_eq_q]; exact Article.qH_pos

theorem h_le_one : h ≤ 1 := by rw [h_eq_q]; exact Article.qH_le_one

/-- `N(h) = Σ_k hᵏ p_k`, the repeated return at `u = i/4` (Prop. 72), and `N_h` at the clock. -/
noncomputable def Nof (y : ℝ) : ℝ := Article.NhOf y
noncomputable def Nh : ℝ := Nof h

theorem Nh_eq_q : Nh = Article.qNh := by rw [Nh, Nof, h_eq_q]; rfl

/-- `N_con = Σ_k p^con_k`, the conjugate-pair returns (Prop. 119). -/
noncomputable def Ncon : ℝ := Article.qNcon

/-- The contact `x = νh/(M + 1 + N_h)` (Eq. (32)). -/
noncomputable def x : ℝ := nu * h / ((M : ℝ) + 1 + Nh)

/-- The electric coupling `α = c_L f/(1 − x)` (Prop. 65). -/
noncomputable def alpha : ℝ := cL * f / (1 - x)

theorem x_eq_q : x = Article.qX := by
  rw [x, nu_eq, h_eq_q, Nh_eq_q, M_eq, Article.qX]; norm_num

theorem alpha_eq_q : alpha = Article.qAlpha := by
  rw [alpha, x_eq_q, cL_eq, f_eq, Article.qAlpha]; norm_num

/-! ## The weak excursion, gravity's amplitude, the colour coupling -/

/-- The weak retained excursion `W_W = F(h)h⁻⁴(1 − 2b + 2bh)` (Prop. 68). -/
noncomputable def WW : ℝ := Fr h / h ^ 4 * (1 - 2 * b + 2 * b * h)

/-- `G_F m_p² = (1 − 1/N₂) W_W/M²` (Prop. 68). -/
noncomputable def GFmp2 : ℝ := (1 - 1 / (N2 : ℝ)) * WW / (M : ℝ) ^ 2

/-- Gravity's amplitude `W = t^{k_C Eℓ} η^{k_C E_H}` (Props. 66, 83). -/
noncomputable def W : ℝ := t ^ ((kC : ℝ) * El) * eta ^ ((kC : ℝ) * EH)

/-- The colour coupling `α_s = k₄/(k₂(k_C² − 1)^{1/2})` (Prop. 64, Table VIII). -/
noncomputable def alphaS : ℝ := k 4 / (k 2 * √((kC : ℝ) ^ 2 - 1))

theorem WW_eq_q : WW = Article.qWW := by
  have hh : |h| ≤ 1 := by rw [abs_of_pos h_pos]; exact h_le_one
  rw [WW, Fr_closed h hh, b_eq, h_eq_q, Article.qWW, Article.qFh]
  norm_num

theorem GFmp2_eq_q : GFmp2 = Article.qGFmp2 := by
  rw [GFmp2, WW_eq_q, N2_eq, M_eq, Article.qGFmp2]; norm_num

theorem W_closed : W = (2 / 5) ^ 48 * (295 / 296) ^ 9 := by
  rw [W, t_eq, El_eq, eta_eq, EH_eq, kC_eq]
  rw [show ((3 : ℕ) : ℝ) * 16 = ((48 : ℕ) : ℝ) by norm_num,
    show ((3 : ℕ) : ℝ) * 3 = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]

theorem W_eq_q : W = Article.qW := by
  rw [W_closed, Article.qW]; norm_num

theorem alphaS_eq_q : alphaS = Article.qAlphaS := by
  rw [alphaS, k_four, k_two, kC_eq, Article.qAlphaS]
  have h8 : √((((3 : ℕ) : ℝ)) ^ 2 - 1) = 2 * √2 := by
    rw [show ((((3 : ℕ) : ℝ)) ^ 2 - 1) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have h72 : √((1 : ℝ) / 72) = 1 / (6 * √2) := by
    rw [show (1 : ℝ) / 72 = 1 / (6 ^ 2 * 2) by norm_num, Real.sqrt_div (by norm_num),
      Real.sqrt_one, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [h8, h72]
  field_simp
  ring

/-- `α_s² = 1/72`. -/
theorem alphaS_sq : alphaS ^ 2 = 1 / 72 := by
  rw [alphaS_eq_q, Article.qAlphaS, Real.sq_sqrt (by norm_num)]

/-! ## The visits to the symmetric states, the up factor -/

/-- `x_c`, the pole of one excursion's visits to the symmetric states `G_P = F(1, 1, x)` (Prop. 84). -/
noncomputable def xc : ℝ := Comparison.xc

theorem xc_root : 16 - 11 * xc - 3 * xc ^ 2 = 0 := by
  rw [xc, GP_denominator]; ring

/-- `κ = (e@{t,n}/t@{t,n})^{Eℓ/E_P}`, the up factor per visit to the symmetric states (Prop. 69). -/
noncomputable def kappa : ℝ := (eS sLineSinglet / tS sLineSinglet) ^ (El / EP)

theorem kappa_eq : kappa = (3 / 2) ^ (8 / 5 : ℝ) := by
  rw [kappa, piece_kappa_base, El_eq, EP_eq]; norm_num

theorem kappa_eq_q : kappa = Article.qKap := by rw [kappa_eq, Article.qKap]

/-! ## The proton's pole and the neutron's exponent (Props. 82, 120) -/

/-- **The proton's pole** (Prop. 82): the available transition sum, the closed Gram-determinant term `log E_U/L(Ω)` and the two exterior
volumes, the five vector states' `V_{B_L}(a)` and the opened seven-volume's `V′_{B_h̄}(a)/Eℓ`. -/
noncomputable def protonPole : ℝ :=
  (transitionSum : ℝ) + Real.log EU / LOmega + volume BL a +
    deriv (fun y : ℝ => volume (Bhbar 0) y) a / El

theorem protonPole_closed :
    protonPole = 6 * 296 + 60 + (1 / 6) * Real.log (5 / 2) - (5 / 38) ^ 5 - (7 / 16) * (5 / 38) ^ 6 := by
  rw [protonPole, transitionSum_eq, EU_eq, LOmega_eq, volume_BL, a_eq,
    (deriv_volume_Bhbar 0 (5 / 38)).1.deriv, El_eq]
  push_cast
  ring

theorem protonPole_eq_q : protonPole = Article.qRp := by
  rw [protonPole_closed, Article.qRp, Article.qLog52]
  norm_num

theorem protonPole_pos : 0 < protonPole := by
  rw [protonPole_eq_q]; exact lt_of_lt_of_le (by norm_num) Article.qRp_bnd.1

/-- **The neutron's exponent** (Prop. 120): the plane contrasts' heat trace at `a²` and the opened volume on the ten
symmetric states with the last-step direction's share. -/
noncomputable def neutronExponent : ℝ :=
  heatContrasts (a ^ 2) + (N2 : ℝ) * cL * b * a ^ 6

theorem neutronExponent_closed :
    neutronExponent = 5 * (5 / 38 : ℝ) ^ 4 + 4 * (5 / 38) ^ 10 + 10 * (15 / 74) * (7 / 16) * (5 / 38) ^ 6 := by
  rw [neutronExponent, a_eq, N2_eq, cL_eq, b_eq, heatContrasts_eq]
  push_cast
  ring

/-! ## Outside inputs -/

/-- The electron's rest energy `m_e c² = 0.51099895069 MeV` (CODATA 2022): the unit of the rows that carry a
unit. Outside input. -/
noncomputable def me : ℝ := 51099895069 / 100000000000

/-- `ħ` [MeV s] and `ħc` [MeV fm] from the SI `h`, `c`, `e`. Outside inputs. -/
noncomputable def hbar : ℝ := (44173801 / 10681177560000000000000000000) / (2 * π)
noncomputable def hc : ℝ := (6621486190496429 / 5340588780000) / (2 * π)

/-- The Julian year [s] and the megaparsec [fm]. Outside inputs. -/
def year : ℝ := 31557600
def Mpc : ℝ := 30856775814913673000000000000000000000

theorem me_eq_q : me = Article.qMe := by rw [me, Article.qMe]
theorem hbar_eq_q : hbar = Article.qHbar := by rw [hbar, Article.qHbar]
theorem hc_eq_q : hc = Article.qHc := by rw [hc, Article.qHc]

/-- The proton's mass `m_p = m_e (m_p/m_e)` [MeV]. -/
noncomputable def mp : ℝ := me * protonPole

theorem mp_eq_q : mp = Article.qMp := by rw [mp, protonPole_eq_q, me_eq_q, Article.qMp]

/-- `G_F` [GeV⁻²], the electroweak scale `v = (√2 G_F)^{−1/2}` [GeV], the Planck mass `M_Pl = m_p/W` [GeV]. -/
noncomputable def GF : ℝ := GFmp2 / (mp / 1000) ^ 2
noncomputable def v : ℝ := (√2 * GF) ^ (-(1 / 2 : ℝ))
noncomputable def MPl : ℝ := (mp / 1000) / W

theorem GF_eq_q : GF = Article.qGF := by rw [GF, GFmp2_eq_q, mp_eq_q, Article.qGF]
theorem v_eq_q : v = Article.qV := by rw [v, GF_eq_q, Article.qV]
theorem MPl_eq_q : MPl = Article.qMpl := by rw [MPl, mp_eq_q, W_eq_q, Article.qMpl]

/-- The weak angles: `ŝ² = 3N_h` and `s² = 3N_h/(1 + f)` (Prop. 119). -/
noncomputable def sw2 : ℝ := 3 * Nh
noncomputable def s2 : ℝ := sw2 / (1 + f)

theorem sw2_eq_q : sw2 = Article.qSw := by rw [sw2, Nh_eq_q, Article.qSw]
theorem s2_eq_q : s2 = Article.qOsw := by rw [s2, sw2_eq_q, f_eq, Article.qOsw]; norm_num

/-- The proton's length `λ_p = ħc/m_p` [fm]. -/
noncomputable def lp : ℝ := hc / mp

theorem lp_eq_q : lp = Article.qLp := by rw [lp, hc_eq_q, mp_eq_q, Article.qLp]

/-! ## The stationary state and the neutral poles (Props. 70, 123, 127) -/

/-- `τ = 2π/(Eℓ m_p/m_e)`, the electron's angle per proton step; `s = e@{t,n}/N₂`, one arrival at a symmetric state. -/
noncomputable def tau : ℝ := 2 * π / (El * protonPole)
noncomputable def s : ℝ := eS sLineSinglet / (N2 : ℝ)

theorem s_eq : s = 3 / 50 := by
  rw [s, (table_lineSinglet sLineSinglet (Or.inl rfl)).2.2.2.2.2.1, N2_eq]; norm_num

theorem tau_eq_q : tau = Article.qTau := by
  rw [tau, El_eq, protonPole_eq_q, Article.qTau]

/-- The scalar tilt `n_s = 1 − t/Eℓ`. -/
noncomputable def ns : ℝ := 1 - t / El

theorem ns_eq : ns = 39 / 40 := by rw [ns, t_eq, El_eq]; norm_num

/-- The de Sitter radius `ℓ = λ_p/(W²(τs³)^{1/2})` [Mpc]. -/
noncomputable def ell : ℝ := lp / (W ^ 2 * √(tau * s ^ 3)) / Mpc

theorem ell_eq_q : ell = Article.qEll := by
  rw [ell, lp_eq_q, W_eq_q, tau_eq_q, s_eq, Mpc, Article.qEll]; norm_num

/-- The pivot `k_* = 0.05 Mpc⁻¹`. Outside input (the convention of the measured amplitude). -/
noncomputable def kstar : ℝ := 1 / 20

/-! ## One source for the 3 and the 12 (rows F01, F03) -/

/-- The eleven states of positive comparison value, `dim E₆(L) + dim E₂(L) = 11`: the exponent of the one positive
volume `a¹¹`. -/
theorem positive_states :
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' L) 6) +
      Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' L) 2) = 11 :=
  WholePicture.twentyfour_eleven.2

/-- **The connected source of the one positive volume**, `C(j) = a¹¹ log G(e^j)`: the reversal `a` once on each of the
eleven states of positive comparison value, with the connected return of the arrivals at the vector states beyond the
two compulsory ones. -/
noncomputable def sourceC (j : ℝ) : ℝ := a ^ 11 * Real.log (GK (Real.exp j))

/-- `C(j) = −a¹¹ log(4 − 3e^j)`. -/
theorem sourceC_eq (j : ℝ) : sourceC j = -(a ^ 11 * Real.log (4 - 3 * Real.exp j)) := by
  rw [sourceC, GK, one_div, Real.log_inv]
  ring

theorem sourceC_hasDerivAt (j : ℝ) (hj : 4 - 3 * Real.exp j ≠ 0) :
    HasDerivAt sourceC (a ^ 11 * (3 * Real.exp j / (4 - 3 * Real.exp j))) j := by
  have hf : HasDerivAt (fun y : ℝ => 4 - 3 * Real.exp y) (-(3 * Real.exp j)) j :=
    ((Real.hasDerivAt_exp j).const_mul 3).const_sub 4
  have hl := ((hf.log hj).const_mul (a ^ 11)).neg
  have e : sourceC = fun y : ℝ => -(a ^ 11 * Real.log (4 - 3 * Real.exp y)) := funext sourceC_eq
  rw [e]
  convert hl using 1
  ring

/-- **`C′(0) = a¹¹E K = 3a¹¹`**, the baryons per photon. -/
theorem sourceC_deriv : deriv sourceC 0 = a ^ 11 * EK := by
  rw [(sourceC_hasDerivAt 0 (by norm_num)).deriv, EK_eq]
  norm_num

theorem sourceC_second_hasDerivAt :
    HasDerivAt (fun j : ℝ => a ^ 11 * (3 * Real.exp j / (4 - 3 * Real.exp j))) (a ^ 11 * 12) 0 := by
  have hN : HasDerivAt (fun j : ℝ => 3 * Real.exp j) (3 * Real.exp 0) 0 := (Real.hasDerivAt_exp 0).const_mul 3
  have hD : HasDerivAt (fun j : ℝ => 4 - 3 * Real.exp j) (-(3 * Real.exp 0)) 0 :=
    ((Real.hasDerivAt_exp 0).const_mul 3).const_sub 4
  have h := (hN.div hD (by norm_num)).const_mul (a ^ 11)
  convert h using 1
  norm_num

open Filter Topology in
/-- **`C″(0) = a¹¹Var K = 12a¹¹`**, the coefficient of the primordial amplitude. -/
theorem sourceC_second : deriv (deriv sourceC) 0 = a ^ 11 * VarK := by
  have hc : ContinuousAt (fun j : ℝ => 4 - 3 * Real.exp j) 0 := by fun_prop
  have hev : ∀ᶠ j in 𝓝 (0 : ℝ),
      HasDerivAt sourceC (a ^ 11 * (3 * Real.exp j / (4 - 3 * Real.exp j))) j := by
    filter_upwards [hc.eventually_ne (by norm_num : (4 - 3 * Real.exp 0 : ℝ) ≠ 0)] with j hj
    exact sourceC_hasDerivAt j hj
  rw [Comparison.deriv_deriv_of hev sourceC_second_hasDerivAt, VarK_eq]

/-! ## The heavy neutral exponent (rows T01, T02) -/

/-- **The heavy neutral exponent** `det(G⁻¹H)`: the coherent comparison `D_coh = |L|/L(Ω)` pulled back by the exterior
representation to the kept algebra `k = {diag(0, −Tr A, A) : A ∈ u(3)}`, over its nine real coordinates
(`Ext/Neutral.lean`). -/
noncomputable def neutralR : ℝ := ((Neutral.keptG⁻¹ * Neutral.keptH).det : ℝ)

/-- `det_ℂ(G_off⁻¹H_off)` on `Hom_ℂ(F, C)`, the six complex rotations across the split. -/
noncomputable def neutralOff : ℝ := ((Neutral.acrossG⁻¹ * Neutral.acrossH).det : ℝ)

/-- **`det(G⁻¹H) = e_line^{dim k} = 3⁻⁹`**, with `dim_ℝ k = 9` (`Neutral.finrank_kept`). -/
theorem neutralR_eq : neutralR = eLine ^ Module.finrank ℝ Neutral.kept ∧ neutralR = (1 / 3) ^ 9 := by
  have h : neutralR = (1 / 3) ^ 9 := by
    rw [neutralR, Neutral.retained_det.2]
    norm_num
  exact ⟨by rw [h, eLine_eq, Neutral.finrank_kept], h⟩

/-- **`det_ℂ(G_off⁻¹H_off) = e_line^{dim_ℂ Hom(F, C)} = 3⁻⁶`.** -/
theorem neutralOff_eq :
    neutralOff = eLine ^ Module.finrank ℂ (Matrix (Fin 3) (Fin 2) ℂ) ∧ neutralOff = (1 / 3) ^ 6 := by
  have h : neutralOff = (1 / 3) ^ 6 := by
    rw [neutralOff, Neutral.across_det.2]
    norm_num
  exact ⟨by rw [h, eLine_eq, Neutral.finrank_hom], h⟩

/-- The heavy neutral pole `X_R = M_R/m_p = e_line⁹/W` and the half phase `ρ_ν = tan²(π/8)` (Props. 118, 123). -/
noncomputable def XR : ℝ := eLine ^ 9 / W
noncomputable def rhoNu : ℝ := Real.tan (π / 8) ^ 2

theorem XR_eq_q : XR = Article.qXR := by rw [XR, eLine_eq, W_eq_q, Article.qXR]; norm_num

theorem rhoNu_eq_q : rhoNu = Article.qRho := by
  rw [rhoNu, ArticleStatements.Radar.tan_sq_pi_div_eight, Article.qRho]

/-- The Dirac couplings `δ = σ(v/m_p)(0, ρ_ν^{1/2}, 1)/√2` and the light seesaw root
`x(δ) = 2δ²/(X_R + (X_R² + 4δ²)^{1/2})`, the light zero of `det [[x, δ], [δ, X_R + x]]` (Prop. 123). -/
noncomputable def delta3 : ℝ := sigma * v / (mp / 1000) / √2
noncomputable def delta2 : ℝ := delta3 * √rhoNu
noncomputable def seesaw (d : ℝ) : ℝ := 2 * d * d / (XR + √(XR * XR + 4 * d * d))

/-- The neutrino masses `m_i = x(δ_i) m_p` [eV]. -/
noncomputable def mnu2 : ℝ := seesaw delta2 * mp * 1000000
noncomputable def mnu3 : ℝ := seesaw delta3 * mp * 1000000

theorem delta3_eq_q : delta3 = Article.qY3 := by
  rw [delta3, sigma_eq, v_eq_q, mp_eq_q, Article.qY3, Article.qYfac]

theorem delta2_eq_q : delta2 = Article.qY2 := by
  rw [delta2, delta3_eq_q, rhoNu_eq_q, Article.qY2, Article.qY3]

theorem mnu2_eq_q : mnu2 = Article.qM2 := by
  rw [mnu2, seesaw, delta2_eq_q, XR_eq_q, mp_eq_q, Article.qM2]

theorem mnu3_eq_q : mnu3 = Article.qM3 := by
  rw [mnu3, seesaw, delta3_eq_q, XR_eq_q, mp_eq_q, Article.qM3]

end Comparison.System.Completion.Num
