import Comparison.Law.Rows

/-!
# Book XXIV in Lean, part B

Propositions 205 to 210 (Book XXIV): the three lines outside the plane, the clock's
overlap, the pion's two ends, the factor `π`, the transfer as the law's response at its critical zero
with any number of lines, and the mass operator's `1/4` and `1/6`. Built on `Comparison.Law.Rule` and `Comparison.Law.Rows`.

* **Prop. 205.** `delta_three`: `m_Δ/m_p = k_C b(w@{}) = |u@{}| Var P/Eℓ = 21/16 = rowDelta`;
  `gravity_three_excursions`: `W = ∏_{c ∈ C} t^{Eℓ}η^{E_H} = (2/5)⁴⁸(295/296)⁹`, with `t@{t,n} = 2/5`.
* **Prop. 206.** `bhattacharyya`: the clock's gap law tilted by `+ν` and by `−ν` has the amplitude
  overlap `Σ_D (p_ν p_{−ν})^{1/2} = [M_Q(ν)M_Q(−ν)]^{−1/2}`; `clock_overlap`: the clock's overlap `h`
  of `Law/Rows.lean` is that overlap taken on the `k_C = 3` lines of `C`, `[M_Q(ν)M_Q(−ν)]^{−k_C s@{h}}`.
* **Prop. 207.** `exchange_block`: `T = [[0, m_e], [m_p, 0]]` has `T² = m_e m_p` and
  `det(1 − T) = 1 − m_e m_p`; `exchange_series`: `det(1 − T)⁻¹ = Σ_k (m_e m_p)^k`; `pion_ends`:
  `2/|Φ@{}| = 38`, the root read at the counterpart `{n}` of `{}`.
* **Prop. 208.** `plane_phase`: `z@F = −1`, `arg z@F = π`; `plane_clock_half_turn`:
  `(γ_hγ_k)² = −1` and `cos π + sin π·γ_hγ_k = −1`; `charge_square`: `α arg(z@F)/|u@{}| = 4πα`;
  `row_pipm_arg`: the charged pion's `π` is `arg z@F`.
* **Prop. 209.** `uRoot_root`, `uRoot_at_d`: with `d` lines the singlet factor `1 + (d − 1)u² − uλ`
  has the root `u_c(λ)`, `1/(d − 1)` at `λ = d`; `transfer_rate`: **`d/dx log((d − 1)u_c(d − x)) =
  1/(d − 2)` at `x = 0`**: a momentum lowering the step's eigenvalue by `x = ε²Q²/2` moves the zero by
  `ε²Q²/(2(d − 2))`, the divisor `2k_C = 2(d − 2)`; `transfer_five`: at five lines `1/3 = 1/k_C`;
  `rho_rule`: `Re s_ρ/m_p² = 2k_C log x_c = rowRho`.
* **Prop. 210.** `massOpRule`: the mass operator with its `1/4` written as `|u_S|` and its `1/6` as
  `1/(1 + L@{})` and the line clock's mean gap `E_D`; `massOpRule_eq`: it is `massOp` on the symmetric
  and on the vector states at every divided set.
-/

open Comparison Comparison.Law Matrix

namespace Comparison.RuleAndLaw

theorem kC_val : ((LZ sHere - LZ sC) / 2 : ℤ) = 3 := by decide

theorem uS_norm' (S : Finset (Fin 6)) : ‖uS S‖ = 1 / 4 := by
  rw [uS, norm_div, zS, norm_pow, Complex.norm_I, one_pow]
  norm_num

/-! ## Proposition 205: the three lines outside the plane -/

/-- **The Δ, the three last-step directions aligned: `k_C b(w@{}) = |u@{}| Var P/Eℓ = 21/16`.** -/
theorem delta_three :
    (((LZ sHere - LZ sC) / 2 : ℤ) : ℝ) * (bS sHere).re = 21 / 16 ∧
      ‖uS sHere‖ * 84 / 16 = 21 / 16 ∧
      (((LZ sHere - LZ sC) / 2 : ℤ) : ℝ) * (bS sHere).re = rowDelta := by
  rw [kC_val]
  refine ⟨?_, ?_, ?_⟩
  · rw [piece_b_here]
    norm_num
  · rw [uS_norm']
    norm_num
  · rw [rowDelta]
    norm_num

/-- **Gravity's three excursions:** the address on the word `C` takes the per-line excursion `t^{Eℓ}η^{E_H}`
once on each of the three lines, `W = (2/5)⁴⁸(295/296)⁹`, with `t = t@{t,n} = 2/5`. -/
theorem gravity_three_excursions :
    tS sLineSinglet = 2 / 5 ∧ sC.card = 3 ∧
      ∏ _c ∈ sC, ((2 / 5 : ℝ) ^ 16 * (295 / 296) ^ 3) = (2 / 5 : ℝ) ^ 48 * (295 / 296) ^ 9 := by
  refine ⟨(table_lineSinglet sLineSinglet (Or.inl rfl)).2.2.2.2.2.2.1, by decide, ?_⟩
  rw [Finset.prod_const, show sC.card = 3 by decide]
  ring

/-! ## Proposition 206: the clock's overlap -/

theorem clockMQ_pos (x : ℝ) : 0 < clockMQ sLastDirectionSinglet x := by
  unfold clockMQ
  apply mul_pos (by norm_num)
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

/-- The clock's gap law tilted at `x`, `p_x(D) = e^{−xD}/(10 M_Q(x))`. -/
noncomputable def tiltLaw (x : ℝ) (i : Fin 10) : ℝ :=
  Real.exp (-(x * clockGap sLastDirectionSinglet i)) / (10 * clockMQ sLastDirectionSinglet x)

theorem tiltLaw_mul (x : ℝ) (i : Fin 10) :
    tiltLaw x i * tiltLaw (-x) i = 1 / (100 * (clockMQ sLastDirectionSinglet x * clockMQ sLastDirectionSinglet (-x))) := by
  have hM := clockMQ_pos x
  have hM' := clockMQ_pos (-x)
  simp only [tiltLaw]
  rw [div_mul_div_comm, ← Real.exp_add]
  have e0 : -(x * clockGap sLastDirectionSinglet i) + -(-x * clockGap sLastDirectionSinglet i) = 0 := by ring
  rw [e0, Real.exp_zero]
  field_simp
  ring

theorem sqrt_hundredth (P : ℝ) (hP : 0 < P) :
    Real.sqrt (1 / (100 * P)) = 1 / (10 * Real.sqrt P) := by
  rw [show (1 : ℝ) / (100 * P) = (1 / (10 * Real.sqrt P)) ^ 2 by
    rw [div_pow, mul_pow, Real.sq_sqrt hP.le]
    norm_num]
  exact Real.sqrt_sq (by positivity)

/-- **The amplitude overlap of the clock's two signs** (Bhattacharyya): the gap law tilted by `+ν`
and by `−ν` overlap as `Σ_D (p_ν(D) p_{−ν}(D))^{1/2} = [M_Q(ν) M_Q(−ν)]^{−1/2}`, for every `x`. -/
theorem bhattacharyya (x : ℝ) :
    ∑ i, Real.sqrt (tiltLaw x i * tiltLaw (-x) i) =
      (clockMQ sLastDirectionSinglet x * clockMQ sLastDirectionSinglet (-x)) ^ (-(1 / 2 : ℝ)) := by
  have hP : 0 < clockMQ sLastDirectionSinglet x * clockMQ sLastDirectionSinglet (-x) :=
    mul_pos (clockMQ_pos x) (clockMQ_pos (-x))
  simp only [tiltLaw_mul, sqrt_hundredth _ hP, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [Real.rpow_neg hP.le, ← Real.sqrt_eq_rpow]
  have hs : 0 < Real.sqrt (clockMQ sLastDirectionSinglet x * clockMQ sLastDirectionSinglet (-x)) := Real.sqrt_pos.mpr hP
  field_simp
  norm_num

/-- **The clock's overlap is the amplitude overlap of the two signs on the three lines of `C`:**
`h = (Σ_D (p_ν p_{−ν})^{1/2})^{k_C} = [M_Q(ν)M_Q(−ν)]^{−k_C s@{h}}`, `k_C = 3`, `s@{h} = 1/2`. -/
theorem clock_overlap :
    hOv sLastDirectionSinglet = (∑ i, Real.sqrt (tiltLaw (9 / 4000) i * tiltLaw (-(9 / 4000)) i)) ^ 3 ∧
      hOv sLastDirectionSinglet = (clockMQ sLastDirectionSinglet (9 / 4000) * clockMQ sLastDirectionSinglet (-(9 / 4000))) ^
        (-(((((LZ sHere - LZ sC) / 2 : ℤ) : ℝ)) * powS sLastDirection)) := by
  have hP : 0 < clockMQ sLastDirectionSinglet (9 / 4000) * clockMQ sLastDirectionSinglet (-(9 / 4000)) :=
    mul_pos (clockMQ_pos _) (clockMQ_pos _)
  have hp : powS sLastDirection = 1 / 2 := (table_line sLastDirection (Or.inr rfl)).2.2.2.2.1
  refine ⟨?_, ?_⟩
  · rw [piece_h, bhattacharyya, ← Real.rpow_natCast, ← Real.rpow_mul hP.le]
    norm_num
  · rw [piece_h, hp, kC_val]
    norm_num

/-! ## Proposition 207: the two ends of the pion's block -/

/-- **The exchange block** `T = [[0, m_e], [m_p, 0]]`: `T² = m_e m_p`, `det(1 − T) = 1 − m_e m_p`. -/
theorem exchange_block (me mp : ℝ) :
    (!![0, me; mp, 0] : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 = (me * mp) • 1 ∧
      (1 - !![0, me; mp, 0] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 - me * mp := by
  refine ⟨blk_square me mp, ?_⟩
  rw [Matrix.det_fin_two]
  simp

/-- **The closed walks of the exchange block** `e → p → e` weigh `(m_e m_p)^k`, and their sum is
`det(1 − T)⁻¹`. -/
theorem exchange_series (x : ℝ) (hx : |x| < 1) : HasSum (fun k : ℕ => x ^ k) (1 - x)⁻¹ :=
  hasSum_geometric_of_abs_lt_one hx

/-- **The pion's two closed ends:** each carries the signed return `1/|Φ@{}| = 19`, together `38`,
and the root is read at the counterpart `{n}` of `{}`, the power `s@{n} = 1/2`. -/
theorem pion_ends :
    endsReturn sHere = 38 ∧ twin sHere = sSinglet ∧ powS sSinglet = 1 / 2 ∧
      rowPi0 = endsReturn sHere * hOv sLastDirectionSinglet := by
  refine ⟨piece_38, by decide, table_singlet.2.2.2.2.1, rfl⟩

/-! ## Proposition 208: the factor `π` of the plane contact -/

/-- **`z@F = −1`, `arg z@F = π`.** -/
theorem plane_phase : zS sF = -1 ∧ Complex.arg (zS sF) = Real.pi := by
  have h : zS sF = -1 := (table_lineSinglet sF (Or.inr (Or.inr (Or.inr rfl)))).1
  exact ⟨h, by rw [h, Complex.arg_neg_one]⟩

/-- **The plane's clock returns its divided set's phase after a half turn:** `(γ_hγ_k)² = −1`, so
`cos θ + sin θ γ_hγ_k` is `−1` at `θ = π`. -/
theorem plane_clock_half_turn :
    (γ 0 * γ 1) * (γ 0 * γ 1) = -1 ∧
      (Real.cos Real.pi : ℂ) • (1 : Matrix Four Four ℂ) + (Real.sin Real.pi : ℂ) • (γ 0 * γ 1) = -1 := by
  refine ⟨?_, ?_⟩
  · have h1 : γ 1 * γ 0 = -(γ 0 * γ 1) := γ_anticomm (by decide)
    calc (γ 0 * γ 1) * (γ 0 * γ 1) = γ 0 * (γ 1 * γ 0) * γ 1 := by noncomm_ring
      _ = γ 0 * (-(γ 0 * γ 1)) * γ 1 := by rw [h1]
      _ = -((γ 0 * γ 0) * (γ 1 * γ 1)) := by noncomm_ring
      _ = -1 := by rw [γ_mul_self, γ_mul_self, one_mul]
  · rw [Real.cos_pi, Real.sin_pi]
    simp

/-- **`e² = 4πα`:** the phase `arg z@F` over one step's weight `|u@{}|`. -/
theorem charge_square (α : ℝ) : α * Complex.arg (zS sF) / ‖uS sHere‖ = 4 * Real.pi * α := by
  rw [plane_phase.2, uS_norm']
  ring

/-- **The charged pion with `π = arg z@F`.** -/
theorem row_pipm_arg (mpi0sq mp α : ℝ) :
    mpi0sq + Complex.arg (zS sF) * α * mp ^ 2 / (16 * (1 - α * (bS sHere).re * (PhiS sC).re)) =
      rowPipm mpi0sq mp α := by
  rw [plane_phase.2, rowPipm]

/-! ## Proposition 209: the transfer, the law's response at its critical zero -/

/-- The root of the singlet factor `1 + (d − 1)u² − uλ` that is `1/(d − 1)` at `λ = d`. -/
noncomputable def uRoot (d lam : ℝ) : ℝ :=
  (lam - Real.sqrt (lam ^ 2 - 4 * (d - 1))) / (2 * (d - 1))

/-- **`u_c(λ)` is a root of the singlet factor with `d` lines.** -/
theorem uRoot_root (d lam : ℝ) (hd : 1 < d) (hD : 4 * (d - 1) ≤ lam ^ 2) :
    1 + (d - 1) * uRoot d lam ^ 2 - uRoot d lam * lam = 0 := by
  have hd1 : d - 1 ≠ 0 := by linarith
  have hs : Real.sqrt (lam ^ 2 - 4 * (d - 1)) ^ 2 = lam ^ 2 - 4 * (d - 1) :=
    Real.sq_sqrt (by linarith)
  have hu : 2 * (d - 1) * uRoot d lam = lam - Real.sqrt (lam ^ 2 - 4 * (d - 1)) := by
    rw [uRoot]
    field_simp
  have key : 4 * (d - 1) * (1 + (d - 1) * uRoot d lam ^ 2 - uRoot d lam * lam) = 0 := by
    have e : 4 * (d - 1) * (1 + (d - 1) * uRoot d lam ^ 2 - uRoot d lam * lam) =
        4 * (d - 1) + (2 * (d - 1) * uRoot d lam) ^ 2 - 2 * (2 * (d - 1) * uRoot d lam) * lam := by
      ring
    rw [e, hu]
    linear_combination hs
  have h4 : (4 : ℝ) * (d - 1) ≠ 0 := by
    have : (0 : ℝ) < d - 1 := by linarith
    positivity
  exact (mul_eq_zero.mp key).resolve_left h4

/-- **At `λ = d` the root is `1/(d − 1)`**, the weight of one of the `d − 1` continuations. -/
theorem uRoot_at_d (d : ℝ) (hd : 2 < d) : uRoot d d = 1 / (d - 1) := by
  have hsq : Real.sqrt (d ^ 2 - 4 * (d - 1)) = d - 2 := by
    rw [show d ^ 2 - 4 * (d - 1) = (d - 2) ^ 2 by ring, Real.sqrt_sq (by linarith)]
  have hd1 : d - 1 ≠ 0 := by linarith
  rw [uRoot, hsq]
  field_simp
  ring

/-- **The transfer with `d` lines.** A momentum on the steps lowers the step's eigenvalue from `d`
by `x = ε²Q²/2` (Proposition 59); the critical zero moves by
`d/dx log((d − 1) u_c(d − x)) = 1/(d − 2)` at `x = 0`: the divisor of `ε²Q²` is `2(d − 2) = 2k_C`,
the law's response `λ − 2(d − 1)u` at its zero, not `L(Ω) = 1 + d`. -/
theorem transfer_rate (d : ℝ) (hd : 2 < d) :
    HasDerivAt (fun x : ℝ => Real.log ((d - 1) * uRoot d (d - x))) (1 / (d - 2)) 0 := by
  have hd1 : d - 1 ≠ 0 := by linarith
  have hd2 : d - 2 ≠ 0 := by linarith
  have hpos : 0 < d - 2 := by linarith
  have hfun : (fun x : ℝ => Real.log ((d - 1) * uRoot d (d - x))) =
      fun x : ℝ => Real.log (((d - x) - Real.sqrt ((d - x) ^ 2 - 4 * (d - 1))) / 2) := by
    funext x
    congr 1
    rw [uRoot]
    field_simp
  rw [hfun]
  -- the radicand
  have hg : HasDerivAt (fun x : ℝ => (d - x) ^ 2 - 4 * (d - 1)) (-(2 * d)) 0 := by
    have h := (((hasDerivAt_id' (0 : ℝ)).const_sub d).pow 2).sub_const (4 * (d - 1))
    convert h using 1
    simp
  have hg0 : (d - 0) ^ 2 - 4 * (d - 1) = (d - 2) ^ 2 := by ring
  have hne : (d - 0) ^ 2 - 4 * (d - 1) ≠ 0 := by
    rw [hg0]
    positivity
  -- its root
  have hs : HasDerivAt (fun x : ℝ => Real.sqrt ((d - x) ^ 2 - 4 * (d - 1)))
      (-(2 * d) / (2 * (d - 2))) 0 := by
    have h := hg.sqrt hne
    have hv : Real.sqrt ((d - 0) ^ 2 - 4 * (d - 1)) = d - 2 := by
      rw [hg0, Real.sqrt_sq hpos.le]
    rw [hv] at h
    exact h
  -- the root of the factor, times `d − 1`
  have hv : HasDerivAt (fun x : ℝ => ((d - x) - Real.sqrt ((d - x) ^ 2 - 4 * (d - 1))) / 2)
      ((-1 - (-(2 * d) / (2 * (d - 2)))) / 2) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).const_sub d).sub hs).div_const 2
  have hv0 : ((d - 0) - Real.sqrt ((d - 0) ^ 2 - 4 * (d - 1))) / 2 = 1 := by
    rw [hg0, Real.sqrt_sq hpos.le]
    ring
  have hlog := hv.log (by rw [hv0]; norm_num)
  convert hlog using 1
  rw [hv0]
  field_simp
  ring

/-- **At five lines the transfer's divisor is `6 = 2k_C`:** `d/dx log(4u_c(5 − x)) = 1/3`. -/
theorem transfer_five :
    HasDerivAt (fun x : ℝ => Real.log ((5 - 1) * uRoot 5 (5 - x))) (1 / 3) 0 := by
  have h := transfer_rate 5 (by norm_num)
  norm_num at h ⊢
  exact h

/-- **The ρ:** the pole of one excursion's visits to the symmetric states at the transfer `e^{−ε²Q²/(2k_C)}` stands at
`Re s/m_p² = 2k_C log x_c`, `rowRho`. -/
theorem rho_rule : 2 * ((((LZ sHere - LZ sC) / 2 : ℤ) : ℝ)) * Real.log xc = rowRho := by
  rw [kC_val, rowRho]
  norm_num

/-! ## Proposition 210: the mass operator's `1/4` and `1/6` -/

/-- The clock's mean gap `E_D = (1/10) Σ D = 2` at `{h, n}`. -/
noncomputable def clockMeanGap : ℝ := (1 / 10) * ∑ i, clockGap sLastDirectionSinglet i

theorem clockMeanGap_eq : clockMeanGap = 2 := clock_moments.1

/-- The clock on the singlet, the symmetric or the vector states with its exponents written as rule values: the plane clock's `1/6` is
`1/(1 + L@{}) = 1/L(Ω)`, the line clock's `1/2` is `|u_S| E_D`. -/
noncomputable def clockRule (P : States) (S : Finset (Fin 6)) : ℝ :=
  match P with
  | .symmetric => clockMQ sLastDirectionSinglet ((signS S : ℝ) * nuS sLastDirectionSinglet) ^ (1 / (1 + (LZ sHere : ℝ)))
  | .vector => Real.exp ((statesN .vector - epsRec S) * (‖uS S‖ * ((signS S : ℝ) * nuS sLastDirectionSinglet) *
      clockMeanGap))

/-- **The one mass operator with every factor a rule value:** `e@{t}^{−n s@{t}}`, the association
taken over one step's weight `|u_S|`, and the clock read per `L(Ω)` or per `|u_S| E_D`. -/
noncomputable def massOpRule (P : States) (S : Finset (Fin 6)) : ℝ :=
  eS sLine ^ (-(statesN P) * powS sLine) *
    Real.exp (-(‖uS S‖ * ((PsiS S).re * statesL P * (statesN P - epsRec S)))) * clockRule P S

/-- **The mass operator's `1/4` is `|u_S|` and its `1/6` is `1/L(Ω)`:** `massOpRule = massOp`
on the symmetric and on the vector states at every divided set. -/
theorem massOpRule_eq (P : States) (S : Finset (Fin 6)) : massOpRule P S = massOp P S := by
  have hp : powS sLine = 1 / 2 := (table_line sLine (Or.inl rfl)).2.2.2.2.1
  have hL : (LZ sHere : ℝ) = 5 := by
    rw [show LZ sHere = 5 by decide]
    norm_num
  cases P with
  | symmetric =>
    simp only [massOpRule, massOp, clockRule, clockOn, uS_norm', hp, hL]
    congr 2
    · ring_nf
    · congr 1
      ring
    · norm_num
  | vector =>
    simp only [massOpRule, massOp, clockRule, clockOn, uS_norm', hp, clockMeanGap_eq]
    congr 2
    · ring_nf
    · congr 1
      ring
    · ring

end Comparison.RuleAndLaw

#print axioms Comparison.RuleAndLaw.delta_three
#print axioms Comparison.RuleAndLaw.gravity_three_excursions
#print axioms Comparison.RuleAndLaw.bhattacharyya
#print axioms Comparison.RuleAndLaw.clock_overlap
#print axioms Comparison.RuleAndLaw.exchange_block
#print axioms Comparison.RuleAndLaw.exchange_series
#print axioms Comparison.RuleAndLaw.pion_ends
#print axioms Comparison.RuleAndLaw.plane_phase
#print axioms Comparison.RuleAndLaw.plane_clock_half_turn
#print axioms Comparison.RuleAndLaw.charge_square
#print axioms Comparison.RuleAndLaw.row_pipm_arg
#print axioms Comparison.RuleAndLaw.uRoot_root
#print axioms Comparison.RuleAndLaw.uRoot_at_d
#print axioms Comparison.RuleAndLaw.transfer_rate
#print axioms Comparison.RuleAndLaw.transfer_five
#print axioms Comparison.RuleAndLaw.rho_rule
#print axioms Comparison.RuleAndLaw.massOpRule_eq
#print axioms Comparison.RuleAndLaw.kC_val
#print axioms Comparison.RuleAndLaw.uS_norm'
#print axioms Comparison.RuleAndLaw.clockMQ_pos
#print axioms Comparison.RuleAndLaw.tiltLaw_mul
#print axioms Comparison.RuleAndLaw.sqrt_hundredth
#print axioms Comparison.RuleAndLaw.clockMeanGap_eq
