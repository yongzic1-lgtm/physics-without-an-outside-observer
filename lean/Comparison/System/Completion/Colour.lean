import Comparison.System.Completion.Numbers
import Comparison.System.Table.Leptons
import Comparison.System.Table.Couplings
import Comparison.System.Table.Hadrons

set_option linter.style.longLine false

/-!
# The proof system, the completions, part 2: the totally antisymmetric colour state, the proton's pole and gravity (SI Props. 75 to 84)

The colour lines are the three lines `C` outside the plane `hk`; a meson closes a line with
its conjugate, a baryon three lines by `ε_abc`; a transition is one of the `M = 296` continuations of the available transitions of `h`; the
exterior volume of a set `B` of two-spinor states is `V_B(a) = Π_{e_S ∈ B} a sgn L(e_S)`.
-/

namespace Comparison.System

open Real Complex Matrix Kronecker Comparison Comparison.Law Comparison.System.Completion

/-- **The two-spinor state of the plane `{h, k}`:** `(γ_u ⊗ γ_u)e_{hk} = −e_{hk}` exactly for the two lines `u` of the plane and
`+e_{hk}` for the three others, `e_{hk} = (γ_hγ_k ⊗ 1)Ω`. -/
theorem Completion.Comp.planeRel_eigen (h k u : Fin 5) (hk : h ≠ k) :
    (γ u ⊗ₖ γ u) *ᵥ planeRel h k = (if u = h ∨ u = k then -1 else 1 : ℂ) • planeRel h k := by
  have hΩ : ((1 : Matrix Four Four ℂ) ⊗ₖ γ u) *ᵥ Ω = (γ u ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω :=
    (meson_either_end u).symm
  have hsplit : (γ u ⊗ₖ γ u) * ((γ h * γ k) ⊗ₖ (1 : Matrix Four Four ℂ)) =
      ((γ u * (γ h * γ k)) ⊗ₖ (1 : Matrix Four Four ℂ)) * ((1 : Matrix Four Four ℂ) ⊗ₖ γ u) := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
  have hc : γ u * (γ h * γ k) * γ u = (if u = h ∨ u = k then -1 else 1 : ℂ) • (γ h * γ k) := by
    by_cases hu : u = h
    · rw [hu, ite_eq_left (Or.inl rfl : h = h ∨ h = k)]
      have e : γ h * (γ h * γ k) * γ h = γ k * γ h := by
        rw [← Matrix.mul_assoc (γ h) (γ h) (γ k), γ_mul_self, Matrix.one_mul]
      rw [e, γ_anticomm (Ne.symm hk), neg_one_smul]
    · by_cases hu' : u = k
      · rw [hu', ite_eq_left (Or.inr rfl : k = h ∨ k = k)]
        have e : γ k * (γ h * γ k) * γ k = γ k * γ h := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, γ_mul_self, Matrix.mul_one]
        rw [e, γ_anticomm (Ne.symm hk), neg_one_smul]
      · have hnot : ¬(u = h ∨ u = k) := by tauto
        rw [ite_eq_right hnot, one_smul]
        calc γ u * (γ h * γ k) * γ u = (γ u * γ h) * (γ k * γ u) := by simp only [Matrix.mul_assoc]
          _ = (γ h * γ u) * (γ u * γ k) := by rw [γ_anticomm hu, γ_anticomm (Ne.symm hu'), neg_mul_neg]
          _ = γ h * (γ u * γ u) * γ k := by simp only [Matrix.mul_assoc]
          _ = γ h * γ k := by rw [γ_mul_self, Matrix.mul_one]
  rw [planeRel, Matrix.mulVec_mulVec, hsplit, ← Matrix.mulVec_mulVec, hΩ, Matrix.mulVec_mulVec,
    ← Matrix.mul_kronecker_mul, Matrix.mul_one, hc, Matrix.smul_kronecker, Matrix.smul_mulVec]

/-- **Proposition 75 (where the two bound states land).** For every line `c`, `(γ_c ⊗ 1)Ω = (1 ⊗ γ_c)Ω`; for every plane
`{h, k}`, `Σ_{c outside} (γ_c ⊗ γ_c)Ω = 3Ω` and `LΩ = 6Ω`: a line closes with its conjugate at the singlet. For three
different lines `ε^{abc}γ_aγ_bγ_c = 6γ_{c₁}γ_{c₂}γ_{c₃}`; in an orientation with `γ_hγ_kγ_{c₁}γ_{c₂}γ_{c₃} = 1`,
`γ_{c₁}γ_{c₂}γ_{c₃} = −γ_hγ_k`, and `(γ_{c₁}γ_{c₂}γ_{c₃} ⊗ 1)Ω = −sgn·e_{hk}` with `Le_{hk} = 2e_{hk}`, where
`e_{hk} = (γ_hγ_k ⊗ 1)Ω` is the two-spinor state of the plane `{h, k}`: `(γ_u ⊗ γ_u)e_{hk} = −e_{hk}` exactly for `u ∈ {h, k}`.
Three lines close at the plane `hk`. Recognition: the meson (a quark and its antiquark closed at the singlet) and the baryon (three
colours making the plane of the last-step direction). -/
theorem prop_75 :
    (∀ c : Fin 5, (γ c ⊗ₖ 1) *ᵥ Ω = (1 ⊗ₖ γ c) *ᵥ Ω) ∧
    (∀ h k : Fin 5, h ≠ k → ∑ c ∈ outside h k, (γ c ⊗ₖ γ c) *ᵥ Ω = (3 : ℂ) • Ω) ∧
    L *ᵥ Ω = (6 : ℂ) • Ω ∧
    (∀ c : Fin 3 → Fin 5, Function.Injective c →
      ∑ a, ∑ b, ∑ d, (levi3 a b d : ℂ) • (γ (c a) * γ (c b) * γ (c d)) = (6 : ℂ) • (γ (c 0) * γ (c 1) * γ (c 2))) ∧
    (∀ h k c₁ c₂ c₃ : Fin 5, [h, k, c₁, c₂, c₃].Nodup → orderSign [h, k, c₁, c₂, c₃] = 1 →
      γ c₁ * γ c₂ * γ c₃ = -(γ h * γ k)) ∧
    (∀ h k c₁ c₂ c₃ : Fin 5, [h, k, c₁, c₂, c₃].Nodup →
      ((γ c₁ * γ c₂ * γ c₃) ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω =
        -((orderSign [h, k, c₁, c₂, c₃] : ℂ) • planeRel h k)) ∧
    (∀ h k : Fin 5, h ≠ k → L *ᵥ planeRel h k = (2 : ℂ) • planeRel h k) ∧
    (∀ h k u : Fin 5, h ≠ k →
      (γ u ⊗ₖ γ u) *ᵥ planeRel h k = (if u = h ∨ u = k then -1 else 1 : ℂ) • planeRel h k) :=
  ⟨meson_either_end, meson_lands_on_singlet, L_singlet, eps_lines, colour_product_oriented, baryon_lands_on_plane,
    L_planeRel, fun h k u hk => Completion.Comp.planeRel_eigen h k u hk⟩

/-- **Proposition 77 (the available transitions are a closed level of the law).** For the last-step direction `h`, every rotation `w` on the steps and
every `u`: the six closed states `D` have `B_DD[w]² = 0` and `det(1 − uB_DD[w]) = 1`, and
`det(I − uB[w]) = det S_h(u)` with `S_h = 1 − uB_AA − u²B_ADB_DA − u³B_ADB_DDB_DA` on `h`'s seventy-four states; the
steps by blocks are `276, 20, 20, 4`: the `320` steps of a stationary cycle are `296` transitions and `24` hidden steps,
`40/37` steps per transition; at `u = 1/4` the watched walk `W` is stochastic with the uniform stationary law, and its
only harmonic vectors on either side are the constants. -/
theorem prop_77 (h : Fin 5) {R : Type*} [CommRing R] (w : State → State → R) (u : R) :
    blockDD h w * blockDD h w = 0 ∧ (1 - u • blockDD h w).det = 1 ∧
    (1 - u • stepT w).det =
      (1 - u • (stepT w).toBlock (InAvailableTransitions h) (InAvailableTransitions h) -
        u ^ 2 • ((stepT w).toBlock (InAvailableTransitions h) (fun s => ¬InAvailableTransitions h s) *
          (stepT w).toBlock (fun s => ¬InAvailableTransitions h s) (InAvailableTransitions h)) -
        u ^ 3 • ((stepT w).toBlock (InAvailableTransitions h) (fun s => ¬InAvailableTransitions h s) * blockDD h w *
          (stepT w).toBlock (fun s => ¬InAvailableTransitions h s) (InAvailableTransitions h))).det ∧
    (Finset.univ.filter fun p : State × State =>
      inExcursion h p.1 = true ∧ inExcursion h p.2 = true ∧ Continues p.1 p.2).card = 276 ∧
    (Finset.univ.filter fun p : State × State =>
      inExcursion h p.1 = true ∧ inExcursion h p.2 = false ∧ Continues p.1 p.2).card = 20 ∧
    (Finset.univ.filter fun p : State × State =>
      inExcursion h p.1 = false ∧ inExcursion h p.2 = true ∧ Continues p.1 p.2).card = 20 ∧
    (Finset.univ.filter fun p : State × State =>
      inExcursion h p.1 = false ∧ inExcursion h p.2 = false ∧ Continues p.1 p.2).card = 4 ∧
    (276 + 20 : ℕ) = 296 ∧ (20 + 4 : ℕ) = 24 ∧ (320 : ℚ) / 296 = 40 / 37 ∧
    watchedW h *ᵥ (1 : {s // InAvailableTransitions h s} → ℚ) = 1 ∧ (1 : {s // InAvailableTransitions h s} → ℚ) ᵥ* watchedW h = 1 ∧
    (∀ v : {s // InAvailableTransitions h s} → ℝ, watchedR h *ᵥ v = v → ∃ c : ℝ, v = c • (1 : {s // InAvailableTransitions h s} → ℝ)) ∧
    (∀ v : {s // InAvailableTransitions h s} → ℝ, v ᵥ* watchedR h = v → ∃ c : ℝ, v = c • (1 : {s // InAvailableTransitions h s} → ℝ)) :=
  ⟨blockDD_sq h w, det_closed h w u, det_availableTransitions h w u, (availableTransitions_counts h).1, (availableTransitions_counts h).2.1,
    (availableTransitions_counts h).2.2.1, (availableTransitions_counts h).2.2.2, by norm_num, by norm_num, by norm_num, watched_rows h,
    watched_cols h, watched_kernel_right h, watched_kernel_left h⟩

open Filter Topology Asymptotics in
/-- **Proposition 78 (the inventory of the closed available transitions).** The transition along `t` weighs
`⟨Ω, (L + γ_h ⊗ γ_t)Ω⟩ = 6 + δ_th`; `Σ_transitions (L(Ω) + [along h]) = Σ_t C_t(6 + δ_th) = (M/5)Tr R_h(L(Ω) + P_h)
= 6M + C_h = 1836`; per transition `6 + c_L = 6 + 15/74`; per excursion `6·74/5 + E_H = 91.8`, twenty excursions a cycle; and on the
watched walk the weight `e^{sX}` on the transitions moves the largest eigenvalue at `d log ρ/ds = 1836/296` at `s = 0`. -/
theorem prop_78 (h : Fin 5) :
    (∀ t : Fin 5, star Ω ⬝ᵥ ((L + γ h ⊗ₖ γ t) *ᵥ Ω) = 6 + if t = h then 1 else 0) ∧
    ∑ p ∈ Finset.univ.filter (fun p : State × State => inExcursion h p.1 = true ∧ Continues p.1 p.2),
      (6 + if p.2.2 = h then 1 else 0) = 1836 ∧
    ∑ t, (alongCount h t : ℚ) * (6 + if t = h then 1 else 0) = 1836 ∧
    (296 / 5 : ℚ) * (availableTransitionsDiag h * weightX h).trace = 1836 ∧
    6 * (Num.M : ℝ) + Num.Ch = 1836 ∧ (1836 : ℝ) / Num.M = 6 + Num.cL ∧
    6 * (74 / 5 : ℝ) + Num.EH = 459 / 5 ∧ (320 : ℝ) / Num.El = 20 ∧ 20 * (459 / 5 : ℝ) = 1836 ∧
    HasDerivAt (fun s => Real.log (perronRoot (watchedS h) s)) (1836 / 296) 0 := by
  refine ⟨fun t => transition_weight h t, transition_inventory h, inventory_by_lines h, inventory_trace h, ?_, ?_, ?_, ?_,
    by norm_num, (inventory_velocity h).2.1⟩
  · rw [Num.M_eq, Num.Ch_eq]; norm_num
  · rw [Num.M_eq, Num.cL_eq]; norm_num
  · rw [Num.EH_eq]; norm_num
  · rw [Num.El_eq]; norm_num

/-- **Proposition 79 (a pole carries the inverse of its count, a source the count itself).** For `S(ζ, j) = cζ − jm`
with `c ≠ 0`: the zero `ζ₀ = jm/c`, the residue `1/c`, `dζ₀/dj = m/c`, `−∂_jS = m`. On the five directions with the available transitions
as the count per step a rest pole on `h` sits at `1/σ` and on another line at `1/η`, `(σ + 4η)/5 = 1`,
`σ − 1 = 4(1 − η) = 1/74`, `1/η = 296/295`; for `X = L(Ω)1 + P_h` the source `(M/5)Tr R_hX = 1836`, the pole
`(M/5)Tr R_h⁻¹X = 1834.49…`, every line alike `(300/5)Tr X = 1860`; with the record `(T_h, h)` every line is asked
sixty times. -/
theorem prop_79 :
    (∀ c j m ζ : ℝ, c ≠ 0 → c * (j * m / c) - j * m = 0 ∧
      (ζ ≠ j * m / c → (ζ - j * m / c) / (c * ζ - j * m) = 1 / c) ∧
      HasDerivAt (fun j' : ℝ => j' * m / c) (m / c) j ∧ HasDerivAt (fun j' : ℝ => -(c * ζ - j' * m)) m j) ∧
    1 / Num.sigma = 74 / 75 ∧ 1 / Num.eta = 296 / 295 ∧ (Num.sigma + 4 * Num.eta) / 5 = 1 ∧
    Num.sigma - 1 = 4 * (1 - Num.eta) ∧ Num.sigma - 1 = 1 / 74 ∧
    (∀ h : Fin 5,
      (296 / 5 : ℚ) * ∑ t, (if t = h then σc else ηc) * (6 + if t = h then 1 else 0) = 1836 ∧
      (296 / 5 : ℚ) * ∑ t, (if t = h then σc else ηc)⁻¹ * (6 + if t = h then 1 else 0) = 40588112 / 22125 ∧
      (300 / 5 : ℚ) * ∑ t, ((6 : ℚ) + if t = h then 1 else 0) = 1860) ∧
    (∀ h j : Fin 5, (Finset.univ.filter fun s : State =>
      (inExcursion h s = true ∨ s = (lastDirectionRel h, h)) ∧ s.2 ≠ j).card = 60) := by
  refine ⟨fun c j m ζ hc => pole_of_count c j m ζ hc, ?_, ?_, ?_, ?_, ?_, three_readings, record_count⟩ <;>
    simp only [Num.sigma_eq, Num.eta_eq] <;> norm_num

/-- **Proposition 80 (the closed Gram-determinant term).** The three pairings `1, −P, −E` of four ends have the Gram
`G = (5·1 − J₃)/4`, levels `1/2` on `(1, 1, 1)` and `5/4` twice, ratio `5/2 = E_U`; `F₀ = (4/5)G = 1 − J₃/5`,
`det F₀ = 2/5 = t`; `h_p = −(1/L(Ω)) log det F₀ = (1/6)log(5/2) = (1/3)artanh(3/7) = Σ_iρ_i log((5/12)/ρ_i)` with
`ρ = G/Tr G = (1/6, 5/12, 5/12)`; a weight `t` on every step moves the zero by `log(1/t)` exactly:
`h_p = log(1/t)/L(Ω)`. -/
theorem prop_80 :
    (∀ i j : Fin 3, ((pairing i)ᴴ * pairing j).trace / 16 = (gram3 i j : ℂ)) ∧
    (gram3 *ᵥ ![1, 1, 1] = (1 / 2 : ℚ) • ![1, 1, 1] ∧ gram3 *ᵥ ![1, -1, 0] = (5 / 4 : ℚ) • ![1, -1, 0] ∧
      gram3 *ᵥ ![1, 0, -1] = (5 / 4 : ℚ) • ![1, 0, -1] ∧ (5 / 4 : ℚ) / (1 / 2) = 5 / 2) ∧
    Num.EU = 5 / 2 ∧
    ((4 / 5 : ℚ) • gram3).det = 2 / 5 ∧ (4 / 5 : ℚ) • gram3 = 1 - (1 / 5 : ℚ) • Matrix.of (fun _ _ => 1) ∧
    Num.t = 2 / 5 ∧ (gram3.trace = 3 ∧ (1 / 2 : ℚ) / 3 = 1 / 6 ∧ (5 / 4 : ℚ) / 3 = 5 / 12) ∧
    -(1 / Num.LOmega) * Real.log Num.t = (1 / 6) * Real.log (5 / 2) ∧
    (1 / 6) * Real.log (5 / 2) = (1 / 3) * ((1 / 2) * Real.log ((1 + 3 / 7) / (1 - 3 / 7))) ∧
    (1 / 6) * Real.log (5 / 2) = (1 / 6) * Real.log ((5 / 12) / (1 / 6)) +
      (5 / 12) * Real.log ((5 / 12) / (5 / 12)) + (5 / 12) * Real.log ((5 / 12) / (5 / 12)) ∧
    Real.log (1 / Num.t) / Num.LOmega = (1 / 6) * Real.log (5 / 2) := by
  have hf := gramTerm_forms
  refine ⟨pairing_gram, gram_levels, Num.EU_eq, det_F0.1, det_F0.2, Num.t_eq, trace_gram, ?_, hf.2.1, hf.2.2, ?_⟩
  · rw [Num.LOmega_eq, Num.t_eq, hf.1]
  · rw [Num.LOmega_eq, Num.t_eq, show (1 : ℝ) / (2 / 5) = 5 / 2 by norm_num]; ring

/-- **Proposition 81 (the signed-volume terms).** The five vector states `B_L` (`L = −2`): `V_{B_L}(a) = −a⁵`; the
seven nonempty even sets of the four lines other than `h`, `B_h̄` (six symmetric states and one vector state):
`V_{B_h̄}(a) = −a⁷` and `−V′_{B_h̄}(a)/Eℓ = (7/16)a⁶ = ba⁶`, `7/16 = Var P/(2(Var P + Var Q))`, for every `a` and `h`;
`dim B_h̄/Eℓ = (2^{d−2} − 1)/2^{d−1}` at `d = 5`. -/
theorem prop_81 :
    (BL.card = 5 ∧ ∏ k ∈ BL, sgnL k = -1) ∧ (∀ a : ℝ, volume BL a = -a ^ 5) ∧
    (∀ h : Fin 5, (Bhbar h).card = 7 ∧ ∏ k ∈ Bhbar h, sgnL k = -1) ∧
    (∀ (h : Fin 5) (a : ℝ), volume (Bhbar h) a = -a ^ 7) ∧
    (∀ (h : Fin 5) (a : ℝ), HasDerivAt (fun x : ℝ => volume (Bhbar h) x) (-(7 * a ^ 6)) a ∧
      -(-(7 * a ^ 6)) / Num.El = Num.b * a ^ 6) ∧
    Num.b = Num.VarP / (2 * (Num.VarP + Num.VarQ)) ∧
    (∀ h : Fin 5, ((Bhbar h).card : ℝ) / Num.El = (2 ^ (Fintype.card (Fin 5) - 2) - 1) / 2 ^ (Fintype.card (Fin 5) - 1)) := by
  refine ⟨card_BL, fun a => volume_BL a, card_Bhbar, fun h a => volume_Bhbar h a,
    fun h a => ⟨(deriv_volume_Bhbar h a).1, ?_⟩, ?_, fun h => ?_⟩
  · rw [Num.El_eq, Num.b_eq]; ring
  · rw [Num.b_eq, Num.VarP_eq, Num.VarQ_eq]; norm_num
  · rw [(card_Bhbar h).1, Num.El_eq]; norm_num

/-- **Proposition 82 (the proton's pole).** `m_p/m_e = Σ_transitions(L(Ω) + [along h]) + log E_U/L(Ω) + V_{B_L}(a) +
V′_{B_h̄}(a)/Eℓ = 6M + C_h + (1/6)log(5/2) − a⁵ − ba⁶ = 1836.15267341`: the four terms `1836`, `0.1527151220`,
`−3.943956·10⁻⁵`, `−2.270369·10⁻⁶`; the available transitions count `1836` is the ratio of two zeros' angles of the law, the
available transitions weight's `1836/320` against one transition's `1/320`.

Recognition: the proton/electron mass ratio. The theorem proves the four terms and their sum; the sum as one pole (Prop. 82 (iv):
the Gram-determinant term and the signed-volume terms enter once for the bound state) is the theory's composition, and one
operator of the law whose zero is the whole sum is the statement that completes it. -/
theorem prop_82 (a₀ s₀ : State) (h₀ : Continues a₀ s₀) :
    Num.protonPole = (Num.transitionSum : ℝ) + Real.log Num.EU / Num.LOmega + volume BL Num.a +
      deriv (fun y : ℝ => volume (Bhbar 0) y) Num.a / Num.El ∧
    Num.protonPole = 6 * (Num.M : ℝ) + Num.Ch + Real.log Num.EU / Num.LOmega - Num.a ^ 5 - Num.b * Num.a ^ 6 ∧
    Num.protonPole = 6 * 296 + 60 + (1 / 6) * Real.log (5 / 2) - (5 / 38) ^ 5 - (7 / 16) * (5 / 38) ^ 6 ∧
    ((1836.152673405 : ℝ) < Num.protonPole ∧ Num.protonPole < 1836.152673415) ∧
    (Num.transitionSum : ℝ) = 1836 ∧
    ((0.152715121 : ℝ) < Real.log Num.EU / Num.LOmega ∧ Real.log Num.EU / Num.LOmega < 0.152715123) ∧
    volume BL Num.a = -(3125 / 79235168) ∧
    deriv (fun y : ℝ => volume (Bhbar 0) y) Num.a / Num.El = -(109375 / 48174982144) ∧
    piU ⬝ᵥ (hadPow ((1 / 4 : ℝ) • B ℝ) (availableTransitionsLawX 0 (transitionX 0)) 1 *ᵥ 1) = 1836 / 320 ∧
    piU ⬝ᵥ (hadPow ((1 / 4 : ℝ) • B ℝ) (oneTransitionX a₀ s₀) 1 *ᵥ 1) = 1 / 320 ∧ (1836 / 320 : ℝ) / (1 / 320) = 1836 := by
  have hlog := log_five_halves
  refine ⟨rfl, ?_, Num.protonPole_closed, row_B12.2, by rw [Num.transitionSum_eq]; norm_num, ?_, ?_, ?_,
    availableTransitions_angle_rate 0, one_transition_angle_rate a₀ s₀ h₀, by norm_num⟩
  · rw [Num.protonPole_closed, Num.M_eq, Num.Ch_eq, Num.EU_eq, Num.LOmega_eq, Num.a_eq, Num.b_eq]
    push_cast
    ring
  · rw [Num.EU_eq, Num.LOmega_eq]
    constructor <;> nlinarith [hlog.1, hlog.2]
  · rw [volume_BL, Num.a_eq]; norm_num
  · rw [(deriv_volume_Bhbar 0 Num.a).1.deriv, Num.a_eq, Num.El_eq]; norm_num

/-- **Proposition 83 (gravity hung on the proton's pole).** `W = m_p/M_Pl = Π_{c∈C} t^{Eℓ}η^{E_H} = (t¹⁶η³)³ =
(2/5)⁴⁸(295/296)⁹` (the 3 × 3 diagonal minor on the lines of `C`), `α_G = W² = 5.90615249·10⁻³⁹`;
`−log W = 3Eℓ log E_U + 3E_H log(1/η) = 48 log(5/2) + 9 log(296/295) = L(Ω)·3Eℓ·h_p + 9 log(296/295)
= 288(m_p/m_e − 6M − C_h + a⁵ + ba⁶) + 9 log(296/295)` with `288 = L(Ω)·k_CEℓ`; `α_G = W²`, `W = m_p/M_Pl`,
`M_Pl = m_p/W = 1.22088981·10¹⁹ GeV`.

Recognition: `α_G = Gm_p²/ħc`, `M_Pl` the Planck mass; the three excursions on the lines of `C` and the source carried
to gravity as the numerator of the pole are the theory's composition. -/
theorem prop_83 :
    Num.W = (2 / 5) ^ 48 * (295 / 296) ^ 9 ∧
    (∏ _c ∈ sC, (Num.t ^ Num.El * Num.eta ^ Num.EH)) = Num.W ∧ sC.card = Num.kC ∧
    -Real.log Num.W = (Num.kC : ℝ) * Num.El * Real.log Num.EU + (Num.kC : ℝ) * Num.EH * Real.log (1 / Num.eta) ∧
    (Num.kC : ℝ) * Num.El * Real.log Num.EU + (Num.kC : ℝ) * Num.EH * Real.log (1 / Num.eta) =
      48 * Real.log (5 / 2) + 9 * Real.log (296 / 295) ∧
    (Num.kC : ℝ) * Num.El * Real.log Num.EU =
      Num.LOmega * ((Num.kC : ℝ) * Num.El) * (Real.log Num.EU / Num.LOmega) ∧
    Num.LOmega * ((Num.kC : ℝ) * Num.El) = 288 ∧
    -Real.log Num.W = Num.LOmega * ((Num.kC : ℝ) * Num.El) *
        (Num.protonPole - (6 * (Num.M : ℝ) + Num.Ch) + Num.a ^ 5 + Num.b * Num.a ^ 6) +
      (Num.kC : ℝ) * Num.EH * Real.log (1 / Num.eta) ∧
    Table.Row.D04 = Num.W ^ 2 * 10 ^ 39 ∧ Num.W = (Num.mp / 1000) / Num.MPl ∧
    ((1.220889811885 : ℝ) < Table.Row.D05 ∧ Table.Row.D05 < 1.220889811895) := by
  have ht : (0 : ℝ) < Num.t := by rw [Num.t_eq]; norm_num
  have he : (0 : ℝ) < Num.eta := by rw [Num.eta_eq]; norm_num
  have hW3 : Num.W = (Num.t ^ Num.El * Num.eta ^ Num.EH) ^ 3 := by
    rw [Num.W, Num.El_eq, Num.EH_eq, Num.kC_eq, Num.t_eq, Num.eta_eq]
    rw [show ((3 : ℕ) : ℝ) * 16 = ((48 : ℕ) : ℝ) by norm_num, show ((3 : ℕ) : ℝ) * 3 = ((9 : ℕ) : ℝ) by norm_num,
      show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num]
    simp only [Real.rpow_natCast]
    ring
  have hsC : sC.card = 3 := (Comparison.RuleAndLaw.gravity_three_excursions).2.1
  have hlogW : Real.log Num.W = (Num.kC : ℝ) * Num.El * Real.log Num.t + (Num.kC : ℝ) * Num.EH * Real.log Num.eta := by
    rw [Num.W, Real.log_mul (Real.rpow_pos_of_pos ht _).ne' (Real.rpow_pos_of_pos he _).ne', Real.log_rpow ht,
      Real.log_rpow he]
  have hEU : Real.log Num.EU = -Real.log Num.t := by
    rw [Num.EU_eq, Num.t_eq, ← Real.log_inv]; norm_num
  have hneg : -Real.log Num.W =
      (Num.kC : ℝ) * Num.El * Real.log Num.EU + (Num.kC : ℝ) * Num.EH * Real.log (1 / Num.eta) := by
    rw [hlogW, hEU, one_div, Real.log_inv]; ring
  have hlaw : Num.protonPole = 6 * (Num.M : ℝ) + Num.Ch + Real.log Num.EU / Num.LOmega - Num.a ^ 5 -
      Num.b * Num.a ^ 6 := by
    rw [Num.protonPole_closed, Num.M_eq, Num.Ch_eq, Num.EU_eq, Num.LOmega_eq, Num.a_eq, Num.b_eq]
    push_cast
    ring
  have hm : Num.mp ≠ 0 := by
    rw [Num.mp_eq_q]; exact (lt_of_lt_of_le (by norm_num) Article.qMp_bnd.1).ne'
  refine ⟨Num.W_closed, ?_, by rw [hsC, Num.kC_eq], hneg, ?_, by rw [Num.LOmega_eq]; ring,
    by rw [Num.LOmega_eq, Num.kC_eq, Num.El_eq]; norm_num, ?_, rfl, ?_, row_D05.2⟩
  · rw [Finset.prod_const, hsC, ← hW3]
  · rw [Num.kC_eq, Num.El_eq, Num.EH_eq, Num.EU_eq, Num.eta_eq]; norm_num
  · rw [show Num.protonPole - (6 * (Num.M : ℝ) + Num.Ch) + Num.a ^ 5 + Num.b * Num.a ^ 6 =
      Real.log Num.EU / Num.LOmega by rw [hlaw]; ring, hneg, Num.LOmega_eq]
    ring
  · rw [Num.MPl, div_div_cancel₀ (div_ne_zero hm (by norm_num))]

/-- **Proposition 84 (the visits to the symmetric states of one excursion, and the vector pole).** `G_P(x) = F(1, 1, x) =
x(1 + x)/(16 − 11x − 3x²)`, `G_P(1) = 1`, `G_P′(1) = E_P = 10`, its pole `x_c = (√313 − 11)/6 > 1`; with each visit to the
symmetric states carrying `e^{−Q²λ²/6}` (the transfer `1/(d − 2) = 1/3` of the law's critical zero, so the divisor `6 = 2k_C`),
`r_π² = 10λ²` and the pole stands at `−Q² = 6 log x_c/λ²`: `s_V = 6m_p² log x_c = 0.576409 GeV²`.

Recognition: the pion's charge radius and the ρ pole; the extent `λ_p` of a visit to the symmetric states is the theory's. -/
theorem prop_84 :
    (∀ y : ℝ, GP y = excursionF 1 1 y) ∧ GP 1 = 1 ∧ HasDerivAt GP 10 1 ∧
    (∀ x : ℝ, 16 - 11 * x - 3 * x ^ 2 = -3 * (x - Num.xc) * (x - xc')) ∧ 1 < Num.xc ∧
    HasDerivAt (fun x : ℝ => Real.log ((5 - 1) * Comparison.RuleAndLaw.uRoot 5 (5 - x))) (1 / 3) 0 ∧
    (∀ lam : ℝ, HasDerivAt (fun q : ℝ => GP (Real.exp (-(q * lam ^ 2) / 6))) (10 * (-(lam ^ 2) / 6)) 0 ∧
      -6 * (10 * (-(lam ^ 2) / 6)) = 10 * lam ^ 2) ∧
    (∀ lam q : ℝ, lam ≠ 0 → (Real.exp (-(q * lam ^ 2) / 6) = Num.xc ↔ -q = 6 * Real.log Num.xc / lam ^ 2)) ∧
    ((0.5764085554935 : ℝ) < Table.Row.J07 ∧ Table.Row.J07 < 0.5764085554945) :=
  ⟨GP_eq, GP_one, GP_deriv, GP_denominator, xc_gt_one, Comparison.RuleAndLaw.transfer_five, pion_radius,
    fun lam q hl => vector_pole lam q hl, row_J07.2⟩

end Comparison.System
