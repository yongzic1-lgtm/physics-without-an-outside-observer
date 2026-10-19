import Comparison.Article.QNucleon

/-!
# The stationary state, the proton's lifetime and the neutrinos

Propositions 118, 123, 127: `Λℓ_P² = 3W⁶τs³`, `ℓ`, `A_s = 12a¹¹(k_*ℓ)^{-1/40}`, `η_B`, `N_eff`, the de Sitter
rows, `τ(p → e⁺π⁰)`, the seesaw `m_i = 2δ_i² m_p/[X_R + (X_R² + 4δ_i²)^{1/2}]`, and the two coloured
statistics.
-/

namespace Comparison.Article

open Real

/-- `τ = 2π/(Eℓ m_p/m_e)`. -/
noncomputable def qTau : ℝ :=
  (((2 : ℝ) * π) / ((16 : ℝ) * qRp))

theorem qTau_bnd : Bnd qTau (2.1387060421777813153309657e-4 : ℝ) (2.138706042177781315337774e-4 : ℝ) := by
  unfold qTau
  have h1 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 bnd_pi (by norm_num) (by norm_num)
  have h3 : Bnd (((2 : ℝ) * π)) (6.28318530717958647692 : ℝ) (6.28318530717958647694 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (16 : ℝ) (16 : ℝ) (16 : ℝ) := Bnd.const _
  have h5 := Bnd.mul h4 qRp_bnd (by norm_num) (by norm_num)
  have h6 : Bnd (((16 : ℝ) * qRp)) (2.937844277459282857833595e4 : ℝ) (2.9378442774592828578335956e4 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.div h3 h6 (by norm_num) (by norm_num)
  have h8 : Bnd ((((2 : ℝ) * π) / ((16 : ℝ) * qRp))) (2.1387060421777813153309657e-4 : ℝ) (2.138706042177781315337774e-4 : ℝ) := h7.weak (by norm_num) (by norm_num)
  exact h8

/-- **`Λℓ_P² = 3W⁶τs³`.** -/
noncomputable def qLam : ℝ :=
  ((((3 : ℝ) * (qW ^ 6)) * qTau) * ((27 : ℝ) / 125000))

theorem qLam_bnd : Bnd qLam (2.8552232430080306423749802e-122 : ℝ) (2.85522324300803064238407e-122 : ℝ) := by
  unfold qLam
  have h1 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h2 := Bnd.pow qW_bnd (by norm_num) 6
  have h3 : Bnd ((qW ^ 6)) (2.0602217515872419118974667e-115 : ℝ) (2.0602217515872419118974668e-115 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.mul h1 h3 (by norm_num) (by norm_num)
  have h5 : Bnd (((3 : ℝ) * (qW ^ 6))) (6.1806652547617257356924001e-115 : ℝ) (6.1806652547617257356924004e-115 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.mul h5 qTau_bnd (by norm_num) (by norm_num)
  have h7 : Bnd ((((3 : ℝ) * (qW ^ 6)) * qTau)) (1.3218626125037178899884168e-118 : ℝ) (1.321862612503717889992625e-118 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 : Bnd ((27 : ℝ) / 125000) ((27 : ℝ) / 125000) ((27 : ℝ) / 125000) := Bnd.const _
  have h9 := Bnd.mul h7 h8 (by norm_num) (by norm_num)
  have h10 : Bnd (((((3 : ℝ) * (qW ^ 6)) * qTau) * ((27 : ℝ) / 125000))) (2.8552232430080306423749802e-122 : ℝ) (2.85522324300803064238407e-122 : ℝ) := h9.weak (by norm_num) (by norm_num)
  exact h10

/-- The de Sitter radius `ℓ = λ_p/(W²(τs³)^{1/2})` in Mpc. -/
noncomputable def qEll : ℝ :=
  ((qLp / ((qW ^ 2) * (√(qTau * ((27 : ℝ) / 125000))))) / (30856775814913673000000000000000000000 : ℝ))

theorem qEll_bnd : Bnd qEll (5.3690821330510157757928664e3 : ℝ) (5.3690821330510157758185056e3 : ℝ) := by
  unfold qEll
  have h1 := Bnd.pow qW_bnd (by norm_num) 2
  have h2 : Bnd ((qW ^ 2)) (5.9061524937714610760366769e-39 : ℝ) (5.906152493771461076036677e-39 : ℝ) := h1.weak (by norm_num) (by norm_num)
  have h3 : Bnd ((27 : ℝ) / 125000) ((27 : ℝ) / 125000) ((27 : ℝ) / 125000) := Bnd.const _
  have h4 := Bnd.mul qTau_bnd h3 (by norm_num) (by norm_num)
  have h5 : Bnd ((qTau * ((27 : ℝ) / 125000))) (4.6196050511040076411148859e-8 : ℝ) (4.6196050511040076411295919e-8 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 : Bnd ((√(qTau * ((27 : ℝ) / 125000)))) (2.1493266506289842311123962e-4 : ℝ) (2.1493266506289842311158174e-4 : ℝ) := Bnd.sqrt h5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h7 := Bnd.mul h2 h6 (by norm_num) (by norm_num)
  have h8 : Bnd (((qW ^ 2) * (√(qTau * ((27 : ℝ) / 125000))))) (1.2694250957541837085290709e-42 : ℝ) (1.2694250957541837085310917e-42 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 := Bnd.div qLp_bnd h8 (by norm_num) (by norm_num)
  have h10 : Bnd ((qLp / ((qW ^ 2) * (√(qTau * ((27 : ℝ) / 125000)))))) (1.6567256371141369899836889e41 : ℝ) (1.6567256371141369899916003e41 : ℝ) := h9.weak (by norm_num) (by norm_num)
  have h11 : Bnd (30856775814913673000000000000000000000 : ℝ) (30856775814913673000000000000000000000 : ℝ) (30856775814913673000000000000000000000 : ℝ) := Bnd.const _
  have h12 := Bnd.div h10 h11 (by norm_num) (by norm_num)
  have h13 : Bnd (((qLp / ((qW ^ 2) * (√(qTau * ((27 : ℝ) / 125000))))) / (30856775814913673000000000000000000000 : ℝ))) (5.3690821330510157757928664e3 : ℝ) (5.3690821330510157758185056e3 : ℝ) := h12.weak (by norm_num) (by norm_num)
  exact h13

/-- `(k_* ℓ)^{-1/40}` with `k_* = 0.05` Mpc⁻¹. -/
noncomputable def qKl : ℝ :=
  ((((1 : ℝ) / 20) * qEll) ^ (-((1 : ℝ) / 40)))

theorem qKl_bnd : Bnd qKl (8.6951734307032663433038883e-1 : ℝ) (8.6951734307032663433049272e-1 : ℝ) := by
  unfold qKl
  have h1 : Bnd ((1 : ℝ) / 20) ((1 : ℝ) / 20) ((1 : ℝ) / 20) := Bnd.const _
  have h2 := Bnd.mul h1 qEll_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((((1 : ℝ) / 20) * qEll)) (2.6845410665255078878964332e2 : ℝ) (2.6845410665255078879092528e2 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (((((1 : ℝ) / 20) * qEll) ^ (-((1 : ℝ) / 40)))) ((1.1500633172754553299682432 : ℝ))⁻¹ ((1.1500633172754553299681058 : ℝ))⁻¹ := Bnd.rpow_neg' (p := 1) (q := 40) h3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h5 : Bnd (((((1 : ℝ) / 20) * qEll) ^ (-((1 : ℝ) / 40)))) (8.6951734307032663433038883e-1 : ℝ) (8.6951734307032663433049272e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- **`A_s = 12a¹¹(k_*ℓ)^{n_s − 1}`.** -/
noncomputable def qAs : ℝ :=
  (((146484375 : ℝ) / 59643012555888128) * qKl)

theorem qAs_bnd : Bnd qAs (2.1355511583517922000876015e-9 : ℝ) (2.1355511583517922000878567e-9 : ℝ) := by
  unfold qAs
  have h1 : Bnd ((146484375 : ℝ) / 59643012555888128) ((146484375 : ℝ) / 59643012555888128) ((146484375 : ℝ) / 59643012555888128) := Bnd.const _
  have h2 := Bnd.mul h1 qKl_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((((146484375 : ℝ) / 59643012555888128) * qKl)) (2.1355511583517922000876015e-9 : ℝ) (2.1355511583517922000878567e-9 : ℝ) := h2.weak (by norm_num) (by norm_num)
  exact h3

/-- **The proton's partial lifetime `72²ħ/(3²⁴W⁴m_p)`** in years. -/
noncomputable def qExcursion : ℝ :=
  ((((5184 : ℝ) * qHbar) / (((282429536481 : ℝ) * (qW ^ 4)) * qMp)) / (31557600 : ℝ))

theorem qExcursion_bnd : Bnd qExcursion (1.1697109894562755791671021e37 : ℝ) (1.1697109894562755791708259e37 : ℝ) := by
  unfold qExcursion
  have h1 : Bnd (5184 : ℝ) (5184 : ℝ) (5184 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qHbar_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((5184 : ℝ) * qHbar)) (3.4121707848334996578733184e-18 : ℝ) (3.4121707848334996578841798e-18 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (282429536481 : ℝ) (282429536481 : ℝ) (282429536481 : ℝ) := Bnd.const _
  have h5 := Bnd.pow qW_bnd (by norm_num) 4
  have h6 : Bnd ((qW ^ 4)) (3.4882637279682848564568115e-77 : ℝ) (3.4882637279682848564568116e-77 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.mul h4 h6 (by norm_num) (by norm_num)
  have h8 : Bnd (((282429536481 : ℝ) * (qW ^ 4))) (9.8518870781356776787766889e-66 : ℝ) (9.8518870781356776787766893e-66 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 := Bnd.mul h8 qMp_bnd (by norm_num) (by norm_num)
  have h10 : Bnd ((((282429536481 : ℝ) * (qW ^ 4)) * qMp)) (9.2437506735341992036457435e-63 : ℝ) (9.2437506735341992036457456e-63 : ℝ) := h9.weak (by norm_num) (by norm_num)
  have h11 := Bnd.div h3 h10 (by norm_num) (by norm_num)
  have h12 : Bnd ((((5184 : ℝ) * qHbar) / (((282429536481 : ℝ) * (qW ^ 4)) * qMp))) (3.6913271520865362217123744e44 : ℝ) (3.6913271520865362217241253e44 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 : Bnd (31557600 : ℝ) (31557600 : ℝ) (31557600 : ℝ) := Bnd.const _
  have h14 := Bnd.div h12 h13 (by norm_num) (by norm_num)
  have h15 : Bnd (((((5184 : ℝ) * qHbar) / (((282429536481 : ℝ) * (qW ^ 4)) * qMp)) / (31557600 : ℝ))) (1.1697109894562755791671021e37 : ℝ) (1.1697109894562755791708259e37 : ℝ) := h14.weak (by norm_num) (by norm_num)
  exact h15

/-- Row D06, cosmological constant `Lambdaell_P^2` [`10^{-122}`]. -/
noncomputable def rowD06 : ℝ :=
  (qLam * (100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))

theorem rowD06_bnd : Bnd rowD06 (2.8552232430080306423749802 : ℝ) (2.85522324300803064238407 : ℝ) := by
  unfold rowD06
  have h1 : Bnd (100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) (100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) (100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := Bnd.const _
  have h2 := Bnd.mul qLam_bnd h1 (by norm_num) (by norm_num)
  have h3 : Bnd ((qLam * (100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) (2.8552232430080306423749802 : ℝ) (2.85522324300803064238407 : ℝ) := h2.weak (by norm_num) (by norm_num)
  exact h3

/-- **Row D06 to its printed digits, `2.85522324301`.** -/
theorem rowD06_digits : (2.855223243005 : ℝ) < rowD06 ∧ rowD06 < (2.855223243015 : ℝ) :=
  rowD06_bnd.strict (by norm_num) (by norm_num)

/-- Row F01, baryons per photon `eta_B` [`10^{-10}`]. -/
noncomputable def rowF01 : ℝ :=
  ((1430511474609375 : ℝ) / 232980517796438)

theorem rowF01_bnd : Bnd rowF01 ((1430511474609375 : ℝ) / 232980517796438) ((1430511474609375 : ℝ) / 232980517796438) := by
  unfold rowF01
  have h1 : Bnd ((1430511474609375 : ℝ) / 232980517796438) ((1430511474609375 : ℝ) / 232980517796438) ((1430511474609375 : ℝ) / 232980517796438) := Bnd.const _
  exact h1

/-- **Row F01 to its printed digits, `6.14004762346`.** -/
theorem rowF01_digits : (6.140047623455 : ℝ) < rowF01 ∧ rowF01 < (6.140047623465 : ℝ) :=
  rowF01_bnd.strict (by norm_num) (by norm_num)

/-- Row F03, primordial amplitude `ln(10^{10}A_s)`. -/
noncomputable def rowF03 : ℝ :=
  (Real.log ((10000000000 : ℝ) * qAs))

theorem rowF03_bnd : Bnd rowF03 (3.06130986015342677059156 : ℝ) (3.06130986015342677059169 : ℝ) := by
  unfold rowF03
  have h1 : Bnd (10000000000 : ℝ) (10000000000 : ℝ) (10000000000 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qAs_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((10000000000 : ℝ) * qAs)) (2.1355511583517922000876015e1 : ℝ) (2.1355511583517922000878567e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd ((Real.log ((10000000000 : ℝ) * qAs))) (3.06130986015342677059156 : ℝ) (3.06130986015342677059169 : ℝ) := Bnd.log h3 (by norm_num) (le_trans (exp_le_split (3.06130986015342677059156 : ℝ) ((7.6532746503835669264789e-1 : ℝ)) (2.1496982104150574521489252 : ℝ) (2.1355511583517922000875914e1 : ℝ) 4 (by norm_num) (exp_le' ((7.6532746503835669264789e-1 : ℝ)) (((76532746503835669264789 : ℝ) / 100000000000000000000000)) (2.1496982104150574521489252 : ℝ) 27 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (by norm_num)) (by norm_num)) (le_trans (by norm_num) (exp_ge_split (3.06130986015342677059169 : ℝ) ((7.653274650383566926479225e-1 : ℝ)) (2.149698210415057452148995 : ℝ) (2.1355511583517922000878687e1 : ℝ) 4 (by norm_num) (by norm_num) (exp_ge' ((7.653274650383566926479225e-1 : ℝ)) (((306130986015342677059169 : ℝ) / 400000000000000000000000)) (2.149698210415057452148995 : ℝ) 27 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (by norm_num)))
  exact h4

/-- **Row F03 to its printed digits, `3.06130986015`.** -/
theorem rowF03_digits : (3.061309860145 : ℝ) < rowF03 ∧ rowF03 < (3.061309860155 : ℝ) :=
  rowF03_bnd.strict (by norm_num) (by norm_num)

/-- Row F04, effective neutrinos `N_{rm eff}`. -/
noncomputable def rowF04 : ℝ :=
  (((885 : ℝ) / 296) * (((75 : ℝ) / 74) ^ (4 / 3 : ℝ)))

theorem rowF04_bnd : Bnd rowF04 (3.0438572736176182031827459 : ℝ) (3.0438572736176182031827463 : ℝ) := by
  unfold rowF04
  have h1 : Bnd ((885 : ℝ) / 296) ((885 : ℝ) / 296) ((885 : ℝ) / 296) := Bnd.const _
  have h2 : Bnd ((75 : ℝ) / 74) ((75 : ℝ) / 74) ((75 : ℝ) / 74) := Bnd.const _
  have h3 : Bnd ((((75 : ℝ) / 74) ^ (4 / 3 : ℝ))) (1.0180584779557231504430427 : ℝ) (1.0180584779557231504430428 : ℝ) := Bnd.rpow' (p := 4) (q := 3) h2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h4 := Bnd.mul h1 h3 (by norm_num) (by norm_num)
  have h5 : Bnd ((((885 : ℝ) / 296) * (((75 : ℝ) / 74) ^ (4 / 3 : ℝ)))) (3.0438572736176182031827459 : ℝ) (3.0438572736176182031827463 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- **Row F04 to its printed digits, `3.04385727362`.** -/
theorem rowF04_digits : (3.043857273615 : ℝ) < rowF04 ∧ rowF04 < (3.043857273625 : ℝ) :=
  rowF04_bnd.strict (by norm_num) (by norm_num)

/-- Row K06, proton partial lifetime `tau/B(epi)` [yr]. -/
noncomputable def rowK06 : ℝ :=
  qExcursion

theorem rowK06_bnd : Bnd rowK06 (1.1697109894562755791671021e37 : ℝ) (1.1697109894562755791708259e37 : ℝ) := by
  unfold rowK06
  exact qExcursion_bnd

/-- **Row K06 to its printed digits, `1.16971098946e37`.** -/
theorem rowK06_digits : (1.169710989455e37 : ℝ) < rowK06 ∧ rowK06 < (1.169710989465e37 : ℝ) :=
  rowK06_bnd.strict (by norm_num) (by norm_num)

/-- Row L12, proton partial lifetime [yr]. -/
noncomputable def rowL12 : ℝ :=
  qExcursion

theorem rowL12_bnd : Bnd rowL12 (1.1697109894562755791671021e37 : ℝ) (1.1697109894562755791708259e37 : ℝ) := by
  unfold rowL12
  exact qExcursion_bnd

/-- **Row L12 to its printed digits, `1.16971098946e37`.** -/
theorem rowL12_digits : (1.169710989455e37 : ℝ) < rowL12 ∧ rowL12 < (1.169710989465e37 : ℝ) :=
  rowL12_bnd.strict (by norm_num) (by norm_num)

/-- Row L10, de Sitter horizon entropy. -/
noncomputable def rowL10 : ℝ :=
  (((3 : ℝ) * π) / qLam)

theorem rowL10_bnd : Bnd rowL10 (3.3008900385807315480483496e122 : ℝ) (3.3008900385807315480693653e122 : ℝ) := by
  unfold rowL10
  have h1 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 bnd_pi (by norm_num) (by norm_num)
  have h3 : Bnd (((3 : ℝ) * π)) (9.42477796076937971538 : ℝ) (9.42477796076937971541 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.div h3 qLam_bnd (by norm_num) (by norm_num)
  have h5 : Bnd ((((3 : ℝ) * π) / qLam)) (3.3008900385807315480483496e122 : ℝ) (3.3008900385807315480693653e122 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- **Row L10 to its printed digits, `3.30089003858e122`.** -/
theorem rowL10_digits : (3.300890038575e122 : ℝ) < rowL10 ∧ rowL10 < (3.300890038585e122 : ℝ) :=
  rowL10_bnd.strict (by norm_num) (by norm_num)

/-- Row L11, tensor-to-scalar ratio in the de Sitter convention. -/
noncomputable def rowL11 : ℝ :=
  (((16 : ℝ) * qLam) / (((3 : ℝ) * π) * ((146484375 : ℝ) / 59643012555888128)))

theorem rowL11_bnd : Bnd rowL11 (1.9735911754997033931517327e-113 : ℝ) (1.9735911754997033931642981e-113 : ℝ) := by
  unfold rowL11
  have h1 : Bnd (16 : ℝ) (16 : ℝ) (16 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qLam_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((16 : ℝ) * qLam)) (4.5683571888128490277999683e-121 : ℝ) (4.568357188812849027814512e-121 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h5 := Bnd.mul h4 bnd_pi (by norm_num) (by norm_num)
  have h6 : Bnd (((3 : ℝ) * π)) (9.42477796076937971538 : ℝ) (9.42477796076937971541 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 : Bnd ((146484375 : ℝ) / 59643012555888128) ((146484375 : ℝ) / 59643012555888128) ((146484375 : ℝ) / 59643012555888128) := Bnd.const _
  have h8 := Bnd.mul h6 h7 (by norm_num) (by norm_num)
  have h9 : Bnd ((((3 : ℝ) * π) * ((146484375 : ℝ) / 59643012555888128))) (2.3147434207878254654954571e-8 : ℝ) (2.3147434207878254655028252e-8 : ℝ) := h8.weak (by norm_num) (by norm_num)
  have h10 := Bnd.div h3 h9 (by norm_num) (by norm_num)
  have h11 : Bnd ((((16 : ℝ) * qLam) / (((3 : ℝ) * π) * ((146484375 : ℝ) / 59643012555888128)))) (1.9735911754997033931517327e-113 : ℝ) (1.9735911754997033931642981e-113 : ℝ) := h10.weak (by norm_num) (by norm_num)
  exact h11

/-- **Row L11 to its printed digits, `1.9735911755e-113`.** -/
theorem rowL11_digits : (1.97359117545e-113 : ℝ) < rowL11 ∧ rowL11 < (1.97359117555e-113 : ℝ) :=
  rowL11_bnd.strict (by norm_num) (by norm_num)

/-- Row L18, second-order light-bending coefficient. -/
noncomputable def rowL18 : ℝ :=
  (((15 : ℝ) * π) / (4 : ℝ))

theorem rowL18_bnd : Bnd rowL18 (1.1780972450961724644225e1 : ℝ) (1.17809724509617246442625e1 : ℝ) := by
  unfold rowL18
  have h1 : Bnd (15 : ℝ) (15 : ℝ) (15 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 bnd_pi (by norm_num) (by norm_num)
  have h3 : Bnd (((15 : ℝ) * π)) (4.71238898038468985769e1 : ℝ) (4.712388980384689857705e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (4 : ℝ) (4 : ℝ) (4 : ℝ) := Bnd.const _
  have h5 := Bnd.div h3 h4 (by norm_num) (by norm_num)
  have h6 : Bnd ((((15 : ℝ) * π) / (4 : ℝ))) (1.1780972450961724644225e1 : ℝ) (1.17809724509617246442625e1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  exact h6

/-- **Row L18 to its printed digits, `11.780972451`.** -/
theorem rowL18_digits : (1.17809724505e1 : ℝ) < rowL18 ∧ rowL18 < (1.17809724515e1 : ℝ) :=
  rowL18_bnd.strict (by norm_num) (by norm_num)

/-- Row S08, primordial amplitude, second construction [`10^{-9}`]. -/
noncomputable def rowS08 : ℝ :=
  ((((191581231380566414401 : ℝ) / 79228162514264337593543950336) * qKl) * (1000000000 : ℝ))

theorem rowS08_bnd : Bnd rowS08 (2.1025756246988530771769464 : ℝ) (2.1025756246988530771771978 : ℝ) := by
  unfold rowS08
  have h1 : Bnd ((191581231380566414401 : ℝ) / 79228162514264337593543950336) ((191581231380566414401 : ℝ) / 79228162514264337593543950336) ((191581231380566414401 : ℝ) / 79228162514264337593543950336) := Bnd.const _
  have h2 := Bnd.mul h1 qKl_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((((191581231380566414401 : ℝ) / 79228162514264337593543950336) * qKl)) (2.1025756246988530771769464e-9 : ℝ) (2.1025756246988530771771978e-9 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (1000000000 : ℝ) (1000000000 : ℝ) (1000000000 : ℝ) := Bnd.const _
  have h5 := Bnd.mul h3 h4 (by norm_num) (by norm_num)
  have h6 : Bnd (((((191581231380566414401 : ℝ) / 79228162514264337593543950336) * qKl) * (1000000000 : ℝ))) (2.1025756246988530771769464 : ℝ) (2.1025756246988530771771978 : ℝ) := h5.weak (by norm_num) (by norm_num)
  exact h6

/-- **Row S08 to its printed digits, `2.1025756247`.** -/
theorem rowS08_digits : (2.10257562465 : ℝ) < rowS08 ∧ rowS08 < (2.10257562475 : ℝ) :=
  rowS08_bnd.strict (by norm_num) (by norm_num)

/-- Row T03, de Sitter radius [Mpc]. -/
noncomputable def rowT03 : ℝ :=
  qEll

theorem rowT03_bnd : Bnd rowT03 (5.3690821330510157757928664e3 : ℝ) (5.3690821330510157758185056e3 : ℝ) := by
  unfold rowT03
  exact qEll_bnd

/-- **Row T03 to its printed digits, `5369.08213305`.** -/
theorem rowT03_digits : (5.369082133045e3 : ℝ) < rowT03 ∧ rowT03 < (5.369082133055e3 : ℝ) :=
  rowT03_bnd.strict (by norm_num) (by norm_num)

/-- Row T04, de Sitter temperature [eV]. -/
noncomputable def rowT04 : ℝ :=
  ((qHc * (1000000 : ℝ)) / ((((2 : ℝ) * π) * qEll) * (30856775814913673000000000000000000000 : ℝ)))

theorem rowT04_bnd : Bnd rowT04 (1.8956406324586983949171018e-34 : ℝ) (1.8956406324586983949382224e-34 : ℝ) := by
  unfold rowT04
  have h1 : Bnd (1000000 : ℝ) (1000000 : ℝ) (1000000 : ℝ) := Bnd.const _
  have h2 := Bnd.mul qHc_bnd h1 (by norm_num) (by norm_num)
  have h3 : Bnd ((qHc * (1000000 : ℝ))) (1.9732698045930246589043233e8 : ℝ) (1.9732698045930246589106045e8 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h5 := Bnd.mul h4 bnd_pi (by norm_num) (by norm_num)
  have h6 : Bnd (((2 : ℝ) * π)) (6.28318530717958647692 : ℝ) (6.28318530717958647694 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.mul h6 qEll_bnd (by norm_num) (by norm_num)
  have h8 : Bnd ((((2 : ℝ) * π) * qEll)) (3.3734937971426575948455695e4 : ℝ) (3.3734937971426575948724173e4 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 : Bnd (30856775814913673000000000000000000000 : ℝ) (30856775814913673000000000000000000000 : ℝ) (30856775814913673000000000000000000000 : ℝ) := Bnd.const _
  have h10 := Bnd.mul h8 h9 (by norm_num) (by norm_num)
  have h11 : Bnd (((((2 : ℝ) * π) * qEll) * (30856775814913673000000000000000000000 : ℝ))) (1.040951418114328493784309e42 : ℝ) (1.0409514181143284937925934e42 : ℝ) := h10.weak (by norm_num) (by norm_num)
  have h12 := Bnd.div h3 h11 (by norm_num) (by norm_num)
  have h13 : Bnd (((qHc * (1000000 : ℝ)) / ((((2 : ℝ) * π) * qEll) * (30856775814913673000000000000000000000 : ℝ)))) (1.8956406324586983949171018e-34 : ℝ) (1.8956406324586983949382224e-34 : ℝ) := h12.weak (by norm_num) (by norm_num)
  exact h13

/-- **Row T04 to its printed digits, `1.89564063246e-34`.** -/
theorem rowT04_digits : (1.895640632455e-34 : ℝ) < rowT04 ∧ rowT04 < (1.895640632465e-34 : ℝ) :=
  rowT04_bnd.strict (by norm_num) (by norm_num)

/-- Row S09, cold/baryon count, second construction. -/
noncomputable def rowS09 : ℝ :=
  ((37 : ℝ) / 7)

theorem rowS09_bnd : Bnd rowS09 ((37 : ℝ) / 7) ((37 : ℝ) / 7) := by
  unfold rowS09
  have h1 : Bnd ((37 : ℝ) / 7) ((37 : ℝ) / 7) ((37 : ℝ) / 7) := Bnd.const _
  exact h1

/-- **Row S09 to its printed digits, `5.28571428571`.** -/
theorem rowS09_digits : (5.285714285705 : ℝ) < rowS09 ∧ rowS09 < (5.285714285715 : ℝ) :=
  rowS09_bnd.strict (by norm_num) (by norm_num)

/-- Row T07, deuteron D-state share. -/
noncomputable def rowT07 : ℝ :=
  ((2 : ℝ) / 51)

theorem rowT07_bnd : Bnd rowT07 ((2 : ℝ) / 51) ((2 : ℝ) / 51) := by
  unfold rowT07
  have h1 : Bnd ((2 : ℝ) / 51) ((2 : ℝ) / 51) ((2 : ℝ) / 51) := Bnd.const _
  exact h1

/-- **Row T07 to its printed digits, `0.0392156862745`.** -/
theorem rowT07_digits : (3.921568627445e-2 : ℝ) < rowT07 ∧ rowT07 < (3.921568627455e-2 : ℝ) :=
  rowT07_bnd.strict (by norm_num) (by norm_num)

/-- The half phase `ρ_ν = 3 − 2√2 = tan²(π/8)`. -/
noncomputable def qRho : ℝ :=
  ((3 : ℝ) - ((2 : ℝ) * (√(2 : ℝ))))

theorem qRho_bnd : Bnd qRho (1.715728752538099023966224e-1 : ℝ) (1.715728752538099023966226e-1 : ℝ) := by
  unfold qRho
  have h1 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h2 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h3 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h4 : Bnd ((√(2 : ℝ))) (1.4142135623730950488016887 : ℝ) (1.4142135623730950488016888 : ℝ) := Bnd.sqrt h3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h5 := Bnd.mul h2 h4 (by norm_num) (by norm_num)
  have h6 : Bnd (((2 : ℝ) * (√(2 : ℝ)))) (2.8284271247461900976033774 : ℝ) (2.8284271247461900976033776 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.sub h1 h6
  have h8 : Bnd (((3 : ℝ) - ((2 : ℝ) * (√(2 : ℝ))))) (1.715728752538099023966224e-1 : ℝ) (1.715728752538099023966226e-1 : ℝ) := h7.weak (by norm_num) (by norm_num)
  exact h8

/-- Row L03, light-limit neutrino splitting ratio. -/
noncomputable def rowL03 : ℝ :=
  ((1 : ℝ) / (qRho ^ 2))

theorem rowL03_bnd : Bnd rowL03 (3.3970562748477140585620244e1 : ℝ) (3.3970562748477140585620326e1 : ℝ) := by
  unfold rowL03
  have h1 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h2 := Bnd.pow qRho_bnd (by norm_num) 2
  have h3 : Bnd ((qRho ^ 2)) (2.9437251522859414379735257e-2 : ℝ) (2.9437251522859414379735327e-2 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.div h1 h3 (by norm_num) (by norm_num)
  have h5 : Bnd (((1 : ℝ) / (qRho ^ 2))) (3.3970562748477140585620244e1 : ℝ) (3.3970562748477140585620326e1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- **Row L03 to its printed digits, `33.9705627485`.** -/
theorem rowL03_digits : (3.397056274845e1 : ℝ) < rowL03 ∧ rowL03 < (3.397056274855e1 : ℝ) :=
  rowL03_bnd.strict (by norm_num) (by norm_num)

/-- `X_R = M_R/m_p = e_line⁹/W`. -/
noncomputable def qXR : ℝ :=
  (((1 : ℝ) / 19683) / qW)

theorem qXR_bnd : Bnd qXR (6.6108359403957651719544778e14 : ℝ) (6.6108359403957651719544779e14 : ℝ) := by
  unfold qXR
  have h1 : Bnd ((1 : ℝ) / 19683) ((1 : ℝ) / 19683) ((1 : ℝ) / 19683) := Bnd.const _
  have h2 := Bnd.div h1 qW_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((((1 : ℝ) / 19683) / qW)) (6.6108359403957651719544778e14 : ℝ) (6.6108359403957651719544779e14 : ℝ) := h2.weak (by norm_num) (by norm_num)
  exact h3

/-- `σ v/(√2 m_p)`, the Dirac coupling's scale. -/
noncomputable def qYfac : ℝ :=
  (((((75 : ℝ) / 74) * qV) / (qMp / (1000 : ℝ))) / (√(2 : ℝ)))

theorem qYfac_bnd : Bnd qYfac (1.8806519544566795269917247e2 : ℝ) (1.8806519544566795269917385e2 : ℝ) := by
  unfold qYfac
  have h1 : Bnd ((75 : ℝ) / 74) ((75 : ℝ) / 74) ((75 : ℝ) / 74) := Bnd.const _
  have h2 := Bnd.mul h1 qV_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((((75 : ℝ) / 74) * qV)) (2.4954692639480171213181249e2 : ℝ) (2.4954692639480171213181423e2 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (1000 : ℝ) (1000 : ℝ) (1000 : ℝ) := Bnd.const _
  have h5 := Bnd.div qMp_bnd h4 (by norm_num) (by norm_num)
  have h6 : Bnd ((qMp / (1000 : ℝ))) (9.3827208942019672472054469e-1 : ℝ) (9.3827208942019672472054485e-1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.div h3 h6 (by norm_num) (by norm_num)
  have h8 : Bnd (((((75 : ℝ) / 74) * qV) / (qMp / (1000 : ℝ)))) (2.6596435000961044612864485e2 : ℝ) (2.6596435000961044612864676e2 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h10 : Bnd ((√(2 : ℝ))) (1.4142135623730950488016887 : ℝ) (1.4142135623730950488016888 : ℝ) := Bnd.sqrt h9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11 := Bnd.div h8 h10 (by norm_num) (by norm_num)
  have h12 : Bnd ((((((75 : ℝ) / 74) * qV) / (qMp / (1000 : ℝ))) / (√(2 : ℝ)))) (1.8806519544566795269917247e2 : ℝ) (1.8806519544566795269917385e2 : ℝ) := h11.weak (by norm_num) (by norm_num)
  exact h12

/-- `δ₂ = σ v ρ_ν^{1/2}/(√2 m_p)`. -/
noncomputable def qY2 : ℝ :=
  (qYfac * (√qRho))

theorem qY2_bnd : Bnd qY2 (7.7899154563942493429472321e1 : ℝ) (7.7899154563942493429472941e1 : ℝ) := by
  unfold qY2
  have h1 : Bnd ((√qRho)) (4.1421356237309504880168854e-1 : ℝ) (4.1421356237309504880168879e-1 : ℝ) := Bnd.sqrt qRho_bnd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := Bnd.mul qYfac_bnd h1 (by norm_num) (by norm_num)
  have h3 : Bnd ((qYfac * (√qRho))) (7.7899154563942493429472321e1 : ℝ) (7.7899154563942493429472941e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  exact h3

/-- `δ₃ = σ v/(√2 m_p)`. -/
noncomputable def qY3 : ℝ :=
  qYfac

theorem qY3_bnd : Bnd qY3 (1.8806519544566795269917247e2 : ℝ) (1.8806519544566795269917385e2 : ℝ) := by
  unfold qY3
  exact qYfac_bnd

/-- **The middle neutrino** `m₂ = 2δ₂² m_p/[X_R + (X_R² + 4δ₂²)^{1/2}]` in eV. -/
noncomputable def qM2 : ℝ :=
  ((((((2 : ℝ) * qY2) * qY2) / (qXR + (√((qXR * qXR) + (((4 : ℝ) * qY2) * qY2))))) * qMp) * (1000000 : ℝ))

theorem qM2_bnd : Bnd qM2 (8.6126719736524727057604685e-3 : ℝ) (8.6126719736524727057606099e-3 : ℝ) := by
  unfold qM2
  have h1 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qY2_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((2 : ℝ) * qY2)) (1.5579830912788498685894464e2 : ℝ) (1.5579830912788498685894589e2 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.mul h3 qY2_bnd (by norm_num) (by norm_num)
  have h5 : Bnd ((((2 : ℝ) * qY2) * qY2)) (1.2136556563554005207288081e4 : ℝ) (1.2136556563554005207288276e4 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.mul qXR_bnd qXR_bnd (by norm_num) (by norm_num)
  have h7 : Bnd ((qXR * qXR)) (4.3703151830828360845270513e29 : ℝ) (4.3703151830828360845270516e29 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 : Bnd (4 : ℝ) (4 : ℝ) (4 : ℝ) := Bnd.const _
  have h9 := Bnd.mul h8 qY2_bnd (by norm_num) (by norm_num)
  have h10 : Bnd (((4 : ℝ) * qY2)) (3.1159661825576997371788928e2 : ℝ) (3.1159661825576997371789177e2 : ℝ) := h9.weak (by norm_num) (by norm_num)
  have h11 := Bnd.mul h10 qY2_bnd (by norm_num) (by norm_num)
  have h12 : Bnd ((((4 : ℝ) * qY2) * qY2)) (2.4273113127108010414576163e4 : ℝ) (2.4273113127108010414576551e4 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 := Bnd.add h7 h12
  have h14 : Bnd (((qXR * qXR) + (((4 : ℝ) * qY2) * qY2))) (4.3703151830828360845270515e29 : ℝ) (4.3703151830828360845270519e29 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 : Bnd ((√((qXR * qXR) + (((4 : ℝ) * qY2) * qY2)))) (6.6108359403957651719544778e14 : ℝ) (6.6108359403957651719544782e14 : ℝ) := Bnd.sqrt h14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h16 := Bnd.add qXR_bnd h15
  have h17 : Bnd ((qXR + (√((qXR * qXR) + (((4 : ℝ) * qY2) * qY2))))) (1.3221671880791530343908955e15 : ℝ) (1.3221671880791530343908957e15 : ℝ) := h16.weak (by norm_num) (by norm_num)
  have h18 := Bnd.div h5 h17 (by norm_num) (by norm_num)
  have h19 : Bnd (((((2 : ℝ) * qY2) * qY2) / (qXR + (√((qXR * qXR) + (((4 : ℝ) * qY2) * qY2)))))) (9.1792903900345744469962265e-12 : ℝ) (9.1792903900345744469963755e-12 : ℝ) := h18.weak (by norm_num) (by norm_num)
  have h20 := Bnd.mul h19 qMp_bnd (by norm_num) (by norm_num)
  have h21 : Bnd ((((((2 : ℝ) * qY2) * qY2) / (qXR + (√((qXR * qXR) + (((4 : ℝ) * qY2) * qY2))))) * qMp)) (8.6126719736524727057604685e-9 : ℝ) (8.6126719736524727057606099e-9 : ℝ) := h20.weak (by norm_num) (by norm_num)
  have h22 : Bnd (1000000 : ℝ) (1000000 : ℝ) (1000000 : ℝ) := Bnd.const _
  have h23 := Bnd.mul h21 h22 (by norm_num) (by norm_num)
  have h24 : Bnd (((((((2 : ℝ) * qY2) * qY2) / (qXR + (√((qXR * qXR) + (((4 : ℝ) * qY2) * qY2))))) * qMp) * (1000000 : ℝ))) (8.6126719736524727057604685e-3 : ℝ) (8.6126719736524727057606099e-3 : ℝ) := h23.weak (by norm_num) (by norm_num)
  exact h24

/-- **The heaviest light neutrino** `m₃` in eV. -/
noncomputable def qM3 : ℝ :=
  ((((((2 : ℝ) * qY3) * qY3) / (qXR + (√((qXR * qXR) + (((4 : ℝ) * qY3) * qY3))))) * qMp) * (1000000 : ℝ))

theorem qM3_bnd : Bnd qM3 (5.0198330947777375808569645e-2 : ℝ) (5.0198330947777375808570397e-2 : ℝ) := by
  unfold qM3
  have h1 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qY3_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((2 : ℝ) * qY3)) (3.7613039089133590539834494e2 : ℝ) (3.761303908913359053983477e2 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.mul h3 qY3_bnd (by norm_num) (by norm_num)
  have h5 : Bnd ((((2 : ℝ) * qY3) * qY3)) (7.0737035476034572115722435e4 : ℝ) (7.0737035476034572115723474e4 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.mul qXR_bnd qXR_bnd (by norm_num) (by norm_num)
  have h7 : Bnd ((qXR * qXR)) (4.3703151830828360845270513e29 : ℝ) (4.3703151830828360845270516e29 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 : Bnd (4 : ℝ) (4 : ℝ) (4 : ℝ) := Bnd.const _
  have h9 := Bnd.mul h8 qY3_bnd (by norm_num) (by norm_num)
  have h10 : Bnd (((4 : ℝ) * qY3)) (7.5226078178267181079668988e2 : ℝ) (7.522607817826718107966954e2 : ℝ) := h9.weak (by norm_num) (by norm_num)
  have h11 := Bnd.mul h10 qY3_bnd (by norm_num) (by norm_num)
  have h12 : Bnd ((((4 : ℝ) * qY3) * qY3)) (1.4147407095206914423144487e5 : ℝ) (1.4147407095206914423144695e5 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 := Bnd.add h7 h12
  have h14 : Bnd (((qXR * qXR) + (((4 : ℝ) * qY3) * qY3))) (4.3703151830828360845270527e29 : ℝ) (4.3703151830828360845270531e29 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 : Bnd ((√((qXR * qXR) + (((4 : ℝ) * qY3) * qY3)))) (6.6108359403957651719544787e14 : ℝ) (6.6108359403957651719544791e14 : ℝ) := Bnd.sqrt h14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h16 := Bnd.add qXR_bnd h15
  have h17 : Bnd ((qXR + (√((qXR * qXR) + (((4 : ℝ) * qY3) * qY3))))) (1.3221671880791530343908956e15 : ℝ) (1.3221671880791530343908957e15 : ℝ) := h16.weak (by norm_num) (by norm_num)
  have h18 := Bnd.div h5 h17 (by norm_num) (by norm_num)
  have h19 : Bnd (((((2 : ℝ) * qY3) * qY3) / (qXR + (√((qXR * qXR) + (((4 : ℝ) * qY3) * qY3)))))) (5.3500825095199548596739801e-11 : ℝ) (5.3500825095199548596740592e-11 : ℝ) := h18.weak (by norm_num) (by norm_num)
  have h20 := Bnd.mul h19 qMp_bnd (by norm_num) (by norm_num)
  have h21 : Bnd ((((((2 : ℝ) * qY3) * qY3) / (qXR + (√((qXR * qXR) + (((4 : ℝ) * qY3) * qY3))))) * qMp)) (5.0198330947777375808569645e-8 : ℝ) (5.0198330947777375808570397e-8 : ℝ) := h20.weak (by norm_num) (by norm_num)
  have h22 : Bnd (1000000 : ℝ) (1000000 : ℝ) (1000000 : ℝ) := Bnd.const _
  have h23 := Bnd.mul h21 h22 (by norm_num) (by norm_num)
  have h24 : Bnd (((((((2 : ℝ) * qY3) * qY3) / (qXR + (√((qXR * qXR) + (((4 : ℝ) * qY3) * qY3))))) * qMp) * (1000000 : ℝ))) (5.0198330947777375808569645e-2 : ℝ) (5.0198330947777375808570397e-2 : ℝ) := h23.weak (by norm_num) (by norm_num)
  exact h24

/-- Row E01, solar splitting `Delta m^2_{21}` [`10^{-5}`,eV`^2`]. -/
noncomputable def rowE01 : ℝ :=
  ((qM2 * qM2) * (100000 : ℝ))

theorem rowE01_bnd : Bnd rowE01 (7.4178118525738779501527046 : ℝ) (7.4178118525738779501529482 : ℝ) := by
  unfold rowE01
  have h1 := Bnd.mul qM2_bnd qM2_bnd (by norm_num) (by norm_num)
  have h2 : Bnd ((qM2 * qM2)) (7.4178118525738779501527046e-5 : ℝ) (7.4178118525738779501529482e-5 : ℝ) := h1.weak (by norm_num) (by norm_num)
  have h3 : Bnd (100000 : ℝ) (100000 : ℝ) (100000 : ℝ) := Bnd.const _
  have h4 := Bnd.mul h2 h3 (by norm_num) (by norm_num)
  have h5 : Bnd (((qM2 * qM2) * (100000 : ℝ))) (7.4178118525738779501527046 : ℝ) (7.4178118525738779501529482 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- **Row E01 to its printed digits, `7.41781185257`.** -/
theorem rowE01_digits : (7.417811852565 : ℝ) < rowE01 ∧ rowE01 < (7.417811852575 : ℝ) :=
  rowE01_bnd.strict (by norm_num) (by norm_num)

/-- Row E02, splitting `Delta m^2_{31}` [`10^{-3}`,eV`^2`]. -/
noncomputable def rowE02 : ℝ :=
  ((qM3 * qM3) * (1000 : ℝ))

theorem rowE02_bnd : Bnd rowE02 (2.5198724299425838530271458 : ℝ) (2.5198724299425838530272214 : ℝ) := by
  unfold rowE02
  have h1 := Bnd.mul qM3_bnd qM3_bnd (by norm_num) (by norm_num)
  have h2 : Bnd ((qM3 * qM3)) (2.5198724299425838530271458e-3 : ℝ) (2.5198724299425838530272214e-3 : ℝ) := h1.weak (by norm_num) (by norm_num)
  have h3 : Bnd (1000 : ℝ) (1000 : ℝ) (1000 : ℝ) := Bnd.const _
  have h4 := Bnd.mul h2 h3 (by norm_num) (by norm_num)
  have h5 : Bnd (((qM3 * qM3) * (1000 : ℝ))) (2.5198724299425838530271458 : ℝ) (2.5198724299425838530272214 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- **Row E02 to its printed digits, `2.51987242994`.** -/
theorem rowE02_digits : (2.519872429935 : ℝ) < rowE02 ∧ rowE02 < (2.519872429945 : ℝ) :=
  rowE02_bnd.strict (by norm_num) (by norm_num)

/-- Row E03, splitting `Delta m^2_{32}` [`10^{-3}`,eV`^2`]. -/
noncomputable def rowE03 : ℝ :=
  (((qM3 * qM3) - (qM2 * qM2)) * (1000 : ℝ))

theorem rowE03_bnd : Bnd rowE03 (2.4456943114168450735256163 : ℝ) (2.4456943114168450735256944 : ℝ) := by
  unfold rowE03
  have h1 := Bnd.mul qM3_bnd qM3_bnd (by norm_num) (by norm_num)
  have h2 : Bnd ((qM3 * qM3)) (2.5198724299425838530271458e-3 : ℝ) (2.5198724299425838530272214e-3 : ℝ) := h1.weak (by norm_num) (by norm_num)
  have h3 := Bnd.mul qM2_bnd qM2_bnd (by norm_num) (by norm_num)
  have h4 : Bnd ((qM2 * qM2)) (7.4178118525738779501527046e-5 : ℝ) (7.4178118525738779501529482e-5 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 := Bnd.sub h2 h4
  have h6 : Bnd (((qM3 * qM3) - (qM2 * qM2))) (2.4456943114168450735256163e-3 : ℝ) (2.4456943114168450735256944e-3 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 : Bnd (1000 : ℝ) (1000 : ℝ) (1000 : ℝ) := Bnd.const _
  have h8 := Bnd.mul h6 h7 (by norm_num) (by norm_num)
  have h9 : Bnd ((((qM3 * qM3) - (qM2 * qM2)) * (1000 : ℝ))) (2.4456943114168450735256163 : ℝ) (2.4456943114168450735256944 : ℝ) := h8.weak (by norm_num) (by norm_num)
  exact h9

/-- **Row E03 to its printed digits, `2.44569431142`.** -/
theorem rowE03_digits : (2.445694311415 : ℝ) < rowE03 ∧ rowE03 < (2.445694311425 : ℝ) :=
  rowE03_bnd.strict (by norm_num) (by norm_num)

/-- Row E04, neutrino mass ratio `m_2/m_3`. -/
noncomputable def rowE04 : ℝ :=
  (qM2 / qM3)

theorem rowE04_bnd : Bnd rowE04 (1.7157287525380990239661981e-1 : ℝ) (1.7157287525380990239662521e-1 : ℝ) := by
  unfold rowE04
  have h1 := Bnd.div qM2_bnd qM3_bnd (by norm_num) (by norm_num)
  have h2 : Bnd ((qM2 / qM3)) (1.7157287525380990239661981e-1 : ℝ) (1.7157287525380990239662521e-1 : ℝ) := h1.weak (by norm_num) (by norm_num)
  exact h2

/-- **Row E04 to its printed digits, `0.171572875254`.** -/
theorem rowE04_digits : (1.715728752535e-1 : ℝ) < rowE04 ∧ rowE04 < (1.715728752545e-1 : ℝ) :=
  rowE04_bnd.strict (by norm_num) (by norm_num)

/-- Row E05, splitting ratio `Delta m^2_{31}/Delta m^2_{21}`. -/
noncomputable def rowE05 : ℝ :=
  ((qM3 / qM2) ^ 2)

theorem rowE05_bnd : Bnd rowE05 (3.3970562748477140585619212e1 : ℝ) (3.3970562748477140585621348e1 : ℝ) := by
  unfold rowE05
  have h1 := Bnd.div qM3_bnd qM2_bnd (by norm_num) (by norm_num)
  have h2 : Bnd ((qM3 / qM2)) (5.8284271247461900976032872 : ℝ) (5.8284271247461900976034703 : ℝ) := h1.weak (by norm_num) (by norm_num)
  have h3 := Bnd.pow h2 (by norm_num) 2
  have h4 : Bnd (((qM3 / qM2) ^ 2)) (3.3970562748477140585619212e1 : ℝ) (3.3970562748477140585621348e1 : ℝ) := h3.weak (by norm_num) (by norm_num)
  exact h4

/-- **Row E05 to its printed digits, `33.9705627485`.** -/
theorem rowE05_digits : (3.397056274845e1 : ℝ) < rowE05 ∧ rowE05 < (3.397056274855e1 : ℝ) :=
  rowE05_bnd.strict (by norm_num) (by norm_num)

/-- Row E06, heaviest light neutrino `m_3` [meV]. -/
noncomputable def rowE06 : ℝ :=
  (qM3 * (1000 : ℝ))

theorem rowE06_bnd : Bnd rowE06 (5.0198330947777375808569645e1 : ℝ) (5.0198330947777375808570397e1 : ℝ) := by
  unfold rowE06
  have h1 : Bnd (1000 : ℝ) (1000 : ℝ) (1000 : ℝ) := Bnd.const _
  have h2 := Bnd.mul qM3_bnd h1 (by norm_num) (by norm_num)
  have h3 : Bnd ((qM3 * (1000 : ℝ))) (5.0198330947777375808569645e1 : ℝ) (5.0198330947777375808570397e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  exact h3

/-- **Row E06 to its printed digits, `50.1983309478`.** -/
theorem rowE06_digits : (5.019833094775e1 : ℝ) < rowE06 ∧ rowE06 < (5.019833094785e1 : ℝ) :=
  rowE06_bnd.strict (by norm_num) (by norm_num)

/-- Row K02, neutrino mass sum [eV]. -/
noncomputable def rowK02 : ℝ :=
  (qM2 + qM3)

theorem rowK02_bnd : Bnd rowK02 (5.8811002921429848514330113e-2 : ℝ) (5.8811002921429848514331007e-2 : ℝ) := by
  unfold rowK02
  have h1 := Bnd.add qM2_bnd qM3_bnd
  have h2 : Bnd ((qM2 + qM3)) (5.8811002921429848514330113e-2 : ℝ) (5.8811002921429848514331007e-2 : ℝ) := h1.weak (by norm_num) (by norm_num)
  exact h2

/-- **Row K02 to its printed digits, `0.0588110029214`.** -/
theorem rowK02_digits : (5.881100292135e-2 : ℝ) < rowK02 ∧ rowK02 < (5.881100292145e-2 : ℝ) :=
  rowK02_bnd.strict (by norm_num) (by norm_num)

/-- Row K03, neutrino mass sum [eV]. -/
noncomputable def rowK03 : ℝ :=
  (qM2 + qM3)

theorem rowK03_bnd : Bnd rowK03 (5.8811002921429848514330113e-2 : ℝ) (5.8811002921429848514331007e-2 : ℝ) := by
  unfold rowK03
  have h1 := Bnd.add qM2_bnd qM3_bnd
  have h2 : Bnd ((qM2 + qM3)) (5.8811002921429848514330113e-2 : ℝ) (5.8811002921429848514331007e-2 : ℝ) := h1.weak (by norm_num) (by norm_num)
  exact h2

/-- **Row K03 to its printed digits, `0.0588110029214`.** -/
theorem rowK03_digits : (5.881100292135e-2 : ℝ) < rowK03 ∧ rowK03 < (5.881100292145e-2 : ℝ) :=
  rowK03_bnd.strict (by norm_num) (by norm_num)

/-- `Σ_q S_q⁻¹ = 1/R_ud + 1 + 1/p`. -/
noncomputable def qInvSum : ℝ :=
  ((((37 : ℝ) / 17) + (1 : ℝ)) + ((1 : ℝ) / qP))

theorem qInvSum_bnd : Bnd qInvSum (3.2265666414213359426234209 : ℝ) (3.2265666414213359426234211 : ℝ) := by
  unfold qInvSum
  have h1 : Bnd ((37 : ℝ) / 17) ((37 : ℝ) / 17) ((37 : ℝ) / 17) := Bnd.const _
  have h2 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h3 := Bnd.add h1 h2
  have h4 : Bnd ((((37 : ℝ) / 17) + (1 : ℝ))) (3.1764705882352941176470588 : ℝ) (3.1764705882352941176470589 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h6 := Bnd.div h5 qP_bnd (by norm_num) (by norm_num)
  have h7 : Bnd (((1 : ℝ) / qP)) (5.0096053186041824976362159e-2 : ℝ) (5.009605318604182497636218e-2 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 := Bnd.add h4 h7
  have h9 : Bnd (((((37 : ℝ) / 17) + (1 : ℝ)) + ((1 : ℝ) / qP))) (3.2265666414213359426234209 : ℝ) (3.2265666414213359426234211 : ℝ) := h8.weak (by norm_num) (by norm_num)
  exact h9

/-- The trace of the light colour matrix. -/
noncomputable def qTrM : ℝ :=
  (((54 : ℝ) / 37) + ((((54 : ℝ) / 37) + ((4 : ℝ) * qP)) / (3 : ℝ)))

theorem qTrM_bnd : Bnd qTrM (2.8561482470983763705566105e1 : ℝ) (2.8561482470983763705566118e1 : ℝ) := by
  unfold qTrM
  have h1 : Bnd ((54 : ℝ) / 37) ((54 : ℝ) / 37) ((54 : ℝ) / 37) := Bnd.const _
  have h2 : Bnd ((54 : ℝ) / 37) ((54 : ℝ) / 37) ((54 : ℝ) / 37) := Bnd.const _
  have h3 : Bnd (4 : ℝ) (4 : ℝ) (4 : ℝ) := Bnd.const _
  have h4 := Bnd.mul h3 qP_bnd (by norm_num) (by norm_num)
  have h5 : Bnd (((4 : ℝ) * qP)) (7.984660957511345327886048e1 : ℝ) (7.9846609575113453278860512e1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.add h2 h5
  have h7 : Bnd ((((54 : ℝ) / 37) + ((4 : ℝ) * qP))) (8.1306069034572912738319939e1 : ℝ) (8.1306069034572912738319972e1 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h9 := Bnd.div h7 h8 (by norm_num) (by norm_num)
  have h10 : Bnd (((((54 : ℝ) / 37) + ((4 : ℝ) * qP)) / (3 : ℝ))) (2.7102023011524304246106646e1 : ℝ) (2.7102023011524304246106658e1 : ℝ) := h9.weak (by norm_num) (by norm_num)
  have h11 := Bnd.add h1 h10
  have h12 : Bnd ((((54 : ℝ) / 37) + ((((54 : ℝ) / 37) + ((4 : ℝ) * qP)) / (3 : ℝ)))) (2.8561482470983763705566105e1 : ℝ) (2.8561482470983763705566118e1 : ℝ) := h11.weak (by norm_num) (by norm_num)
  exact h12

/-- The determinant of the light colour matrix. -/
noncomputable def qDetM : ℝ :=
  (((((54 : ℝ) / 37) * (((54 : ℝ) / 37) + ((4 : ℝ) * qP))) - ((400 : ℝ) / 1369)) / (3 : ℝ))

theorem qDetM_bnd : Bnd qDetM (3.9456909162667806099625816e1 : ℝ) (3.945690916266780609962584e1 : ℝ) := by
  unfold qDetM
  have h1 : Bnd ((54 : ℝ) / 37) ((54 : ℝ) / 37) ((54 : ℝ) / 37) := Bnd.const _
  have h2 : Bnd ((54 : ℝ) / 37) ((54 : ℝ) / 37) ((54 : ℝ) / 37) := Bnd.const _
  have h3 : Bnd (4 : ℝ) (4 : ℝ) (4 : ℝ) := Bnd.const _
  have h4 := Bnd.mul h3 qP_bnd (by norm_num) (by norm_num)
  have h5 : Bnd (((4 : ℝ) * qP)) (7.984660957511345327886048e1 : ℝ) (7.9846609575113453278860512e1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.add h2 h5
  have h7 : Bnd ((((54 : ℝ) / 37) + ((4 : ℝ) * qP))) (8.1306069034572912738319939e1 : ℝ) (8.1306069034572912738319972e1 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 := Bnd.mul h1 h7 (by norm_num) (by norm_num)
  have h9 : Bnd ((((54 : ℝ) / 37) * (((54 : ℝ) / 37) + ((4 : ℝ) * qP)))) (1.1866291156397127805052099e2 : ℝ) (1.1866291156397127805052105e2 : ℝ) := h8.weak (by norm_num) (by norm_num)
  have h10 : Bnd ((400 : ℝ) / 1369) ((400 : ℝ) / 1369) ((400 : ℝ) / 1369) := Bnd.const _
  have h11 := Bnd.sub h9 h10
  have h12 : Bnd (((((54 : ℝ) / 37) * (((54 : ℝ) / 37) + ((4 : ℝ) * qP))) - ((400 : ℝ) / 1369))) (1.1837072748800341829887745e2 : ℝ) (1.1837072748800341829887752e2 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h14 := Bnd.div h12 h13 (by norm_num) (by norm_num)
  have h15 : Bnd ((((((54 : ℝ) / 37) * (((54 : ℝ) / 37) + ((4 : ℝ) * qP))) - ((400 : ℝ) / 1369)) / (3 : ℝ))) (3.9456909162667806099625816e1 : ℝ) (3.945690916266780609962584e1 : ℝ) := h14.weak (by norm_num) (by norm_num)
  exact h15

/-- Its lower eigenvalue `λ_min`. -/
noncomputable def qLow : ℝ :=
  ((qTrM - (√((qTrM * qTrM) - ((4 : ℝ) * qDetM)))) / (2 : ℝ))

theorem qLow_bnd : Bnd qLow (1.4556618566961937110173275 : ℝ) (1.455661856696193711017343 : ℝ) := by
  unfold qLow
  have h1 := Bnd.mul qTrM_bnd qTrM_bnd (by norm_num) (by norm_num)
  have h2 : Bnd ((qTrM * qTrM)) (8.1575828094031280056326488e2 : ℝ) (8.1575828094031280056326564e2 : ℝ) := h1.weak (by norm_num) (by norm_num)
  have h3 : Bnd (4 : ℝ) (4 : ℝ) (4 : ℝ) := Bnd.const _
  have h4 := Bnd.mul h3 qDetM_bnd (by norm_num) (by norm_num)
  have h5 : Bnd (((4 : ℝ) * qDetM)) (1.5782763665067122439850326e2 : ℝ) (1.5782763665067122439850336e2 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.sub h2 h5
  have h7 : Bnd (((qTrM * qTrM) - ((4 : ℝ) * qDetM))) (6.5793064428964157616476152e2 : ℝ) (6.5793064428964157616476238e2 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 : Bnd ((√((qTrM * qTrM) - ((4 : ℝ) * qDetM)))) (2.5650158757591376283531432e1 : ℝ) (2.565015875759137628353145e1 : ℝ) := Bnd.sqrt h7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h9 := Bnd.sub qTrM_bnd h8
  have h10 : Bnd ((qTrM - (√((qTrM * qTrM) - ((4 : ℝ) * qDetM))))) (2.911323713392387422034655 : ℝ) (2.911323713392387422034686 : ℝ) := h9.weak (by norm_num) (by norm_num)
  have h11 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h12 := Bnd.div h10 h11 (by norm_num) (by norm_num)
  have h13 : Bnd (((qTrM - (√((qTrM * qTrM) - ((4 : ℝ) * qDetM)))) / (2 : ℝ))) (1.4556618566961937110173275 : ℝ) (1.455661856696193711017343 : ℝ) := h12.weak (by norm_num) (by norm_num)
  exact h13

/-- Row I08, topological curvature `chi/(F_pi^2m_{pi^0}^2)`. -/
noncomputable def rowI08 : ℝ :=
  ((1 : ℝ) / (qLow * qInvSum))

theorem rowI08_bnd : Bnd rowI08 (2.1291137192716519140968207e-1 : ℝ) (2.1291137192716519140968437e-1 : ℝ) := by
  unfold rowI08
  have h1 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h2 := Bnd.mul qLow_bnd qInvSum_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((qLow * qInvSum)) (4.6967899880053837601745528 : ℝ) (4.6967899880053837601746032 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.div h1 h3 (by norm_num) (by norm_num)
  have h5 : Bnd (((1 : ℝ) / (qLow * qInvSum))) (2.1291137192716519140968207e-1 : ℝ) (2.1291137192716519140968437e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- **Row I08 to its printed digits, `0.212911371927`.** -/
theorem rowI08_digits : (2.129113719265e-1 : ℝ) < rowI08 ∧ rowI08 < (2.129113719275e-1 : ℝ) :=
  rowI08_bnd.strict (by norm_num) (by norm_num)

/-- Row I09, fourth strong cumulant `b_2`. -/
noncomputable def rowI09 : ℝ :=
  (-((((((37 : ℝ) / 17) ^ 3) + (1 : ℝ)) + (((1 : ℝ) / qP) ^ 3)) / ((12 : ℝ) * (qInvSum ^ 3))))

theorem rowI09_bnd : Bnd rowI09 (-2.8058473098757368519129973e-2 : ℝ) (-2.8058473098757368519129961e-2 : ℝ) := by
  unfold rowI09
  have h1 : Bnd ((37 : ℝ) / 17) ((37 : ℝ) / 17) ((37 : ℝ) / 17) := Bnd.const _
  have h2 := Bnd.pow h1 (by norm_num) 3
  have h3 : Bnd ((((37 : ℝ) / 17) ^ 3)) (1.0309993893751272135151638e1 : ℝ) (1.0309993893751272135151639e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h5 := Bnd.add h3 h4
  have h6 : Bnd (((((37 : ℝ) / 17) ^ 3) + (1 : ℝ))) (1.1309993893751272135151638e1 : ℝ) (1.1309993893751272135151639e1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h8 := Bnd.div h7 qP_bnd (by norm_num) (by norm_num)
  have h9 : Bnd (((1 : ℝ) / qP)) (5.0096053186041824976362159e-2 : ℝ) (5.009605318604182497636218e-2 : ℝ) := h8.weak (by norm_num) (by norm_num)
  have h10 := Bnd.pow h9 (by norm_num) 3
  have h11 : Bnd ((((1 : ℝ) / qP) ^ 3)) (1.2572178371370330765506683e-4 : ℝ) (1.25721783713703307655067e-4 : ℝ) := h10.weak (by norm_num) (by norm_num)
  have h12 := Bnd.add h6 h11
  have h13 : Bnd ((((((37 : ℝ) / 17) ^ 3) + (1 : ℝ)) + (((1 : ℝ) / qP) ^ 3))) (1.1310119615534985838459293e1 : ℝ) (1.1310119615534985838459295e1 : ℝ) := h12.weak (by norm_num) (by norm_num)
  have h14 : Bnd (12 : ℝ) (12 : ℝ) (12 : ℝ) := Bnd.const _
  have h15 := Bnd.pow qInvSum_bnd (by norm_num) 3
  have h16 : Bnd ((qInvSum ^ 3)) (3.3590921524628150789486313e1 : ℝ) (3.359092152462815078948632e1 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.mul h14 h16 (by norm_num) (by norm_num)
  have h18 : Bnd (((12 : ℝ) * (qInvSum ^ 3))) (4.0309105829553780947383575e2 : ℝ) (4.0309105829553780947383584e2 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 := Bnd.div h13 h18 (by norm_num) (by norm_num)
  have h20 : Bnd (((((((37 : ℝ) / 17) ^ 3) + (1 : ℝ)) + (((1 : ℝ) / qP) ^ 3)) / ((12 : ℝ) * (qInvSum ^ 3)))) (2.8058473098757368519129961e-2 : ℝ) (2.8058473098757368519129973e-2 : ℝ) := h19.weak (by norm_num) (by norm_num)
  have h21 := Bnd.neg h20
  have h22 : Bnd ((-((((((37 : ℝ) / 17) ^ 3) + (1 : ℝ)) + (((1 : ℝ) / qP) ^ 3)) / ((12 : ℝ) * (qInvSum ^ 3))))) (-2.8058473098757368519129973e-2 : ℝ) (-2.8058473098757368519129961e-2 : ℝ) := h21.weak (by norm_num) (by norm_num)
  exact h22

/-- **Row I09 to its printed digits, `-0.0280584730988`.** -/
theorem rowI09_digits : (-2.805847309885e-2 : ℝ) < rowI09 ∧ rowI09 < (-2.805847309875e-2 : ℝ) :=
  rowI09_bnd.strict (by norm_num) (by norm_num)

end Comparison.Article
