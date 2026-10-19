import Comparison.Article.QCouplings

/-!
# The lepton and quark rows

`L(n, L, P) = 3^{n/2} exp[−Ψ_P L (n − ε_P)/4 + c_n(P)]` (Proposition 69): `m_μ/m_e`, `m_τ/m_μ`, `p`, `q`,
`κ = (3/2)^{8/5}`, and the rows B01 to B14 and L01, L05, L17.
-/

namespace Comparison.Article

open Real

/-- **`m_μ/m_e = 3⁵ e^{−9/56} M_Q(ν)^{1/6}`.** -/
noncomputable def qRmu : ℝ :=
  (((243 : ℝ) * (Real.exp (-((9 : ℝ) / 56)))) * (qMQp ^ (1 / 6 : ℝ)))

theorem qRmu_bnd : Bnd qRmu (2.0676828394547607776342051e2 : ℝ) (2.0676828394547607776342054e2 : ℝ) := by
  unfold qRmu
  have h1 : Bnd (243 : ℝ) (243 : ℝ) (243 : ℝ) := Bnd.const _
  have h2 : Bnd (-((9 : ℝ) / 56)) (-((9 : ℝ) / 56)) (-((9 : ℝ) / 56)) := Bnd.const _
  have h3 : Bnd ((Real.exp (-((9 : ℝ) / 56)))) (8.5153533216310634395799501e-1 : ℝ) (8.5153533216310634395799502e-1 : ℝ) := Bnd.exp h2 (exp_ge' (-((9 : ℝ) / 56)) (((9 : ℝ) / 56)) (8.5153533216310634395799501e-1 : ℝ) 19 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' (-((9 : ℝ) / 56)) (((9 : ℝ) / 56)) (8.5153533216310634395799502e-1 : ℝ) 19 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h4 := Bnd.mul h1 h3 (by norm_num) (by norm_num)
  have h5 : Bnd (((243 : ℝ) * (Real.exp (-((9 : ℝ) / 56))))) (2.0692308571563484158179278e2 : ℝ) (2.0692308571563484158179279e2 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 : Bnd ((qMQp ^ (1 / 6 : ℝ))) (9.9925188738789880129746819e-1 : ℝ) (9.9925188738789880129746822e-1 : ℝ) := Bnd.rpow' (p := 1) (q := 6) qMQp_bnd (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h7 := Bnd.mul h5 h6 (by norm_num) (by norm_num)
  have h8 : Bnd ((((243 : ℝ) * (Real.exp (-((9 : ℝ) / 56)))) * (qMQp ^ (1 / 6 : ℝ)))) (2.0676828394547607776342051e2 : ℝ) (2.0676828394547607776342054e2 : ℝ) := h7.weak (by norm_num) (by norm_num)
  exact h8

/-- **`m_τ/m_μ = 3^{5/2} e^{1/14 + 2ν}`.** -/
noncomputable def qRtau : ℝ :=
  (((3 : ℝ) ^ (5 / 2 : ℝ)) * (Real.exp ((1063 : ℝ) / 14000)))

theorem qRtau_bnd : Bnd qRtau (1.6818160641058324346829661e1 : ℝ) (1.6818160641058324346829665e1 : ℝ) := by
  unfold qRtau
  have h1 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h2 : Bnd (((3 : ℝ) ^ (5 / 2 : ℝ))) (1.5588457268119895641747017e1 : ℝ) (1.5588457268119895641747018e1 : ℝ) := Bnd.rpow' (p := 5) (q := 2) h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 : Bnd ((1063 : ℝ) / 14000) ((1063 : ℝ) / 14000) ((1063 : ℝ) / 14000) := Bnd.const _
  have h4 : Bnd ((Real.exp ((1063 : ℝ) / 14000))) (1.078885508154376952836635 : ℝ) (1.0788855081543769528366351 : ℝ) := Bnd.exp h3 (exp_ge' ((1063 : ℝ) / 14000) (((1063 : ℝ) / 14000)) (1.078885508154376952836635 : ℝ) 16 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' ((1063 : ℝ) / 14000) (((1063 : ℝ) / 14000)) (1.0788855081543769528366351 : ℝ) 16 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h5 := Bnd.mul h2 h4 (by norm_num) (by norm_num)
  have h6 : Bnd ((((3 : ℝ) ^ (5 / 2 : ℝ)) * (Real.exp ((1063 : ℝ) / 14000)))) (1.6818160641058324346829661e1 : ℝ) (1.6818160641058324346829665e1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  exact h6

/-- **`p = m_s/m_d = 3⁵ e^{−5/2} M_Q(−ν)^{1/6}`.** -/
noncomputable def qP : ℝ :=
  (((243 : ℝ) * (Real.exp (-((5 : ℝ) / 2)))) * (qMQm ^ (1 / 6 : ℝ)))

theorem qP_bnd : Bnd qP (1.996165239377836331971512e1 : ℝ) (1.9961652393778363319715128e1 : ℝ) := by
  unfold qP
  have h1 : Bnd (243 : ℝ) (243 : ℝ) (243 : ℝ) := Bnd.const _
  have h2 : Bnd (-((5 : ℝ) / 2)) (-((5 : ℝ) / 2)) (-((5 : ℝ) / 2)) := Bnd.const _
  have h3 : Bnd ((Real.exp (-((5 : ℝ) / 2)))) (8.2084998623898795169528669e-2 : ℝ) (8.2084998623898795169528676e-2 : ℝ) := Bnd.exp h2 (exp_ge_split (-((5 : ℝ) / 2)) ((-6.25e-1 : ℝ)) (5.352614285189902419566225e-1 : ℝ) (8.2084998623898795169528669e-2 : ℝ) 4 (by norm_num) (by norm_num) (exp_ge' ((-6.25e-1 : ℝ)) (((5 : ℝ) / 8)) (5.352614285189902419566225e-1 : ℝ) 26 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (by norm_num)) (exp_le_split (-((5 : ℝ) / 2)) ((-6.25e-1 : ℝ)) (5.3526142851899024195662251e-1 : ℝ) (8.2084998623898795169528676e-2 : ℝ) 4 (by norm_num) (exp_le' ((-6.25e-1 : ℝ)) (((5 : ℝ) / 8)) (5.3526142851899024195662251e-1 : ℝ) 26 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  have h4 := Bnd.mul h1 h3 (by norm_num) (by norm_num)
  have h5 : Bnd (((243 : ℝ) * (Real.exp (-((5 : ℝ) / 2))))) (1.9946654665607407226195466e1 : ℝ) (1.9946654665607407226195469e1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 : Bnd ((qMQm ^ (1 / 6 : ℝ))) (1.0007518919048022426342718 : ℝ) (1.000751891904802242634272 : ℝ) := Bnd.rpow' (p := 1) (q := 6) qMQm_bnd (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h7 := Bnd.mul h5 h6 (by norm_num) (by norm_num)
  have h8 : Bnd ((((243 : ℝ) * (Real.exp (-((5 : ℝ) / 2)))) * (qMQm ^ (1 / 6 : ℝ)))) (1.996165239377836331971512e1 : ℝ) (1.9961652393778363319715128e1 : ℝ) := h7.weak (by norm_num) (by norm_num)
  exact h8

/-- **`q = 3^{5/2} e^{5/4 − 5ν/2}`.** -/
noncomputable def qQ : ℝ :=
  (((3 : ℝ) ^ (5 / 2 : ℝ)) * (Real.exp ((1991 : ℝ) / 1600)))

theorem qQ_bnd : Bnd qQ (5.4103870226173303763729782e1 : ℝ) (5.4103870226173303763729793e1 : ℝ) := by
  unfold qQ
  have h1 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h2 : Bnd (((3 : ℝ) ^ (5 / 2 : ℝ))) (1.5588457268119895641747017e1 : ℝ) (1.5588457268119895641747018e1 : ℝ) := Bnd.rpow' (p := 5) (q := 2) h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 : Bnd ((1991 : ℝ) / 1600) ((1991 : ℝ) / 1600) ((1991 : ℝ) / 1600) := Bnd.const _
  have h4 : Bnd ((Real.exp ((1991 : ℝ) / 1600))) (3.4707648932535261692388875 : ℝ) (3.4707648932535261692388879 : ℝ) := Bnd.exp h3 (exp_ge_split ((1991 : ℝ) / 1600) ((6.221875e-1 : ℝ)) (1.8629988978132880713072827 : ℝ) (3.4707648932535261692388875 : ℝ) 2 (by norm_num) (by norm_num) (exp_ge' ((6.221875e-1 : ℝ)) (((1991 : ℝ) / 3200)) (1.8629988978132880713072827 : ℝ) 26 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (by norm_num)) (exp_le_split ((1991 : ℝ) / 1600) ((6.221875e-1 : ℝ)) (1.8629988978132880713072828 : ℝ) (3.4707648932535261692388879 : ℝ) 2 (by norm_num) (exp_le' ((6.221875e-1 : ℝ)) (((1991 : ℝ) / 3200)) (1.8629988978132880713072828 : ℝ) 26 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  have h5 := Bnd.mul h2 h4 (by norm_num) (by norm_num)
  have h6 : Bnd ((((3 : ℝ) ^ (5 / 2 : ℝ)) * (Real.exp ((1991 : ℝ) / 1600)))) (5.4103870226173303763729782e1 : ℝ) (5.4103870226173303763729793e1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  exact h6

/-- **`κ = (e/t)^{Eℓ/E_P} = (3/2)^{8/5}`.** -/
noncomputable def qKap : ℝ :=
  (((3 : ℝ) / 2) ^ (8 / 5 : ℝ))

theorem qKap_bnd : Bnd qKap (1.9131367509386862492998217 : ℝ) (1.9131367509386862492998218 : ℝ) := by
  unfold qKap
  have h1 : Bnd ((3 : ℝ) / 2) ((3 : ℝ) / 2) ((3 : ℝ) / 2) := Bnd.const _
  have h2 : Bnd ((((3 : ℝ) / 2) ^ (8 / 5 : ℝ))) (1.9131367509386862492998217 : ℝ) (1.9131367509386862492998218 : ℝ) := Bnd.rpow' (p := 8) (q := 5) h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h2

/-- The Koide statistic `Σ m_l/(Σ √m_l)²` of `1, m_μ/m_e, m_τ/m_e`. -/
noncomputable def qKoide : ℝ :=
  ((((1 : ℝ) + qRmu) + (qRmu * qRtau)) / ((((1 : ℝ) + (√qRmu)) + (√(qRmu * qRtau))) ^ 2))

theorem qKoide_bnd : Bnd qKoide (6.6666725976109061536212319e-1 : ℝ) (6.6666725976109061536212375e-1 : ℝ) := by
  unfold qKoide
  have h1 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h2 := Bnd.add h1 qRmu_bnd
  have h3 : Bnd (((1 : ℝ) + qRmu)) (2.0776828394547607776342051e2 : ℝ) (2.0776828394547607776342054e2 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.mul qRmu_bnd qRtau_bnd (by norm_num) (by norm_num)
  have h5 : Bnd ((qRmu * qRtau)) (3.4774622148709775861540239e3 : ℝ) (3.4774622148709775861540253e3 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.add h3 h5
  have h7 : Bnd ((((1 : ℝ) + qRmu) + (qRmu * qRtau))) (3.6852304988164536639174444e3 : ℝ) (3.6852304988164536639174459e3 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h9 : Bnd ((√qRmu)) (1.4379439625572203700813309e1 : ℝ) (1.4379439625572203700813311e1 : ℝ) := Bnd.sqrt qRmu_bnd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h10 := Bnd.add h8 h9
  have h11 : Bnd (((1 : ℝ) + (√qRmu))) (1.5379439625572203700813309e1 : ℝ) (1.5379439625572203700813311e1 : ℝ) := h10.weak (by norm_num) (by norm_num)
  have h12 := Bnd.mul qRmu_bnd qRtau_bnd (by norm_num) (by norm_num)
  have h13 : Bnd ((qRmu * qRtau)) (3.4774622148709775861540239e3 : ℝ) (3.4774622148709775861540253e3 : ℝ) := h12.weak (by norm_num) (by norm_num)
  have h14 : Bnd ((√(qRmu * qRtau))) (5.8970011148642134084556469e1 : ℝ) (5.8970011148642134084556482e1 : ℝ) := Bnd.sqrt h13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h15 := Bnd.add h11 h14
  have h16 : Bnd ((((1 : ℝ) + (√qRmu)) + (√(qRmu * qRtau)))) (7.4349450774214337785369778e1 : ℝ) (7.4349450774214337785369793e1 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.pow h16 (by norm_num) 2
  have h18 : Bnd (((((1 : ℝ) + (√qRmu)) + (√(qRmu * qRtau))) ^ 2)) (5.5278408304273209923207629e3 : ℝ) (5.5278408304273209923207652e3 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 := Bnd.div h7 h18 (by norm_num) (by norm_num)
  have h20 : Bnd (((((1 : ℝ) + qRmu) + (qRmu * qRtau)) / ((((1 : ℝ) + (√qRmu)) + (√(qRmu * qRtau))) ^ 2))) (6.6666725976109061536212319e-1 : ℝ) (6.6666725976109061536212375e-1 : ℝ) := h19.weak (by norm_num) (by norm_num)
  exact h20

/-- Row B01, muon/electron. -/
noncomputable def rowB01 : ℝ :=
  qRmu

theorem rowB01_bnd : Bnd rowB01 (2.0676828394547607776342051e2 : ℝ) (2.0676828394547607776342054e2 : ℝ) := by
  unfold rowB01
  exact qRmu_bnd

/-- **Row B01 to its printed digits, `206.768283945`.** -/
theorem rowB01_digits : (2.067682839445e2 : ℝ) < rowB01 ∧ rowB01 < (2.067682839455e2 : ℝ) :=
  rowB01_bnd.strict (by norm_num) (by norm_num)

/-- Row B02, tau/muon. -/
noncomputable def rowB02 : ℝ :=
  qRtau

theorem rowB02_bnd : Bnd rowB02 (1.6818160641058324346829661e1 : ℝ) (1.6818160641058324346829665e1 : ℝ) := by
  unfold rowB02
  exact qRtau_bnd

/-- **Row B02 to its printed digits, `16.8181606411`.** -/
theorem rowB02_digits : (1.681816064105e1 : ℝ) < rowB02 ∧ rowB02 < (1.681816064115e1 : ℝ) :=
  rowB02_bnd.strict (by norm_num) (by norm_num)

/-- Row B03, Koide statistic. -/
noncomputable def rowB03 : ℝ :=
  qKoide

theorem rowB03_bnd : Bnd rowB03 (6.6666725976109061536212319e-1 : ℝ) (6.6666725976109061536212375e-1 : ℝ) := by
  unfold rowB03
  exact qKoide_bnd

/-- **Row B03 to its printed digits, `0.666667259761`.** -/
theorem rowB03_digits : (6.666672597605e-1 : ℝ) < rowB03 ∧ rowB03 < (6.666672597615e-1 : ℝ) :=
  rowB03_bnd.strict (by norm_num) (by norm_num)

/-- Row B04, strange/down. -/
noncomputable def rowB04 : ℝ :=
  qP

theorem rowB04_bnd : Bnd rowB04 (1.996165239377836331971512e1 : ℝ) (1.9961652393778363319715128e1 : ℝ) := by
  unfold rowB04
  exact qP_bnd

/-- **Row B04 to its printed digits, `19.9616523938`.** -/
theorem rowB04_digits : (1.996165239375e1 : ℝ) < rowB04 ∧ rowB04 < (1.996165239385e1 : ℝ) :=
  rowB04_bnd.strict (by norm_num) (by norm_num)

/-- Row B05, bottom/strange. -/
noncomputable def rowB05 : ℝ :=
  (qQ * ((295 : ℝ) / 296))

theorem rowB05_bnd : Bnd rowB05 (5.3921086880814610169933397e1 : ℝ) (5.3921086880814610169933409e1 : ℝ) := by
  unfold rowB05
  have h1 : Bnd ((295 : ℝ) / 296) ((295 : ℝ) / 296) ((295 : ℝ) / 296) := Bnd.const _
  have h2 := Bnd.mul qQ_bnd h1 (by norm_num) (by norm_num)
  have h3 : Bnd ((qQ * ((295 : ℝ) / 296))) (5.3921086880814610169933397e1 : ℝ) (5.3921086880814610169933409e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  exact h3

/-- **Row B05 to its printed digits, `53.9210868808`.** -/
theorem rowB05_digits : (5.392108688075e1 : ℝ) < rowB05 ∧ rowB05 < (5.392108688085e1 : ℝ) :=
  rowB05_bnd.strict (by norm_num) (by norm_num)

/-- Row B06, down statistic `m_b^2m_d/m_s^3`. -/
noncomputable def rowB06 : ℝ :=
  (((qQ * ((295 : ℝ) / 296)) ^ 2) / qP)

theorem rowB06_bnd : Bnd rowB06 (1.4565345358456198422356883e2 : ℝ) (1.4565345358456198422356897e2 : ℝ) := by
  unfold rowB06
  have h1 : Bnd ((295 : ℝ) / 296) ((295 : ℝ) / 296) ((295 : ℝ) / 296) := Bnd.const _
  have h2 := Bnd.mul qQ_bnd h1 (by norm_num) (by norm_num)
  have h3 : Bnd ((qQ * ((295 : ℝ) / 296))) (5.3921086880814610169933397e1 : ℝ) (5.3921086880814610169933409e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.pow h3 (by norm_num) 2
  have h5 : Bnd (((qQ * ((295 : ℝ) / 296)) ^ 2)) (2.9074836104083574658932841e3 : ℝ) (2.9074836104083574658932855e3 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.div h5 qP_bnd (by norm_num) (by norm_num)
  have h7 : Bnd ((((qQ * ((295 : ℝ) / 296)) ^ 2) / qP)) (1.4565345358456198422356883e2 : ℝ) (1.4565345358456198422356897e2 : ℝ) := h6.weak (by norm_num) (by norm_num)
  exact h7

/-- **Row B06 to its printed digits, `145.653453585`.** -/
theorem rowB06_digits : (1.456534535845e2 : ℝ) < rowB06 ∧ rowB06 < (1.456534535855e2 : ℝ) :=
  rowB06_bnd.strict (by norm_num) (by norm_num)

/-- Row B07, up statistic `m_t^2m_u/m_c^3`. -/
noncomputable def rowB07 : ℝ :=
  (((qQ * ((295 : ℝ) / 296)) ^ 2) / qP)

theorem rowB07_bnd : Bnd rowB07 (1.4565345358456198422356883e2 : ℝ) (1.4565345358456198422356897e2 : ℝ) := by
  unfold rowB07
  have h1 : Bnd ((295 : ℝ) / 296) ((295 : ℝ) / 296) ((295 : ℝ) / 296) := Bnd.const _
  have h2 := Bnd.mul qQ_bnd h1 (by norm_num) (by norm_num)
  have h3 : Bnd ((qQ * ((295 : ℝ) / 296))) (5.3921086880814610169933397e1 : ℝ) (5.3921086880814610169933409e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.pow h3 (by norm_num) 2
  have h5 : Bnd (((qQ * ((295 : ℝ) / 296)) ^ 2)) (2.9074836104083574658932841e3 : ℝ) (2.9074836104083574658932855e3 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.div h5 qP_bnd (by norm_num) (by norm_num)
  have h7 : Bnd ((((qQ * ((295 : ℝ) / 296)) ^ 2) / qP)) (1.4565345358456198422356883e2 : ℝ) (1.4565345358456198422356897e2 : ℝ) := h6.weak (by norm_num) (by norm_num)
  exact h7

/-- **Row B07 to its printed digits, `145.653453585`.** -/
theorem rowB07_digits : (1.456534535845e2 : ℝ) < rowB07 ∧ rowB07 < (1.456534535855e2 : ℝ) :=
  rowB07_bnd.strict (by norm_num) (by norm_num)

/-- Row B08, lepton/quark plane quotient. -/
noncomputable def rowB08 : ℝ :=
  (qRmu / qP)

theorem rowB08_bnd : Bnd rowB08 (1.0358274949719167594315449e1 : ℝ) (1.0358274949719167594315456e1 : ℝ) := by
  unfold rowB08
  have h1 := Bnd.div qRmu_bnd qP_bnd (by norm_num) (by norm_num)
  have h2 : Bnd ((qRmu / qP)) (1.0358274949719167594315449e1 : ℝ) (1.0358274949719167594315456e1 : ℝ) := h1.weak (by norm_num) (by norm_num)
  exact h2

/-- **Row B08 to its printed digits, `10.3582749497`.** -/
theorem rowB08_digits : (1.035827494965e1 : ℝ) < rowB08 ∧ rowB08 < (1.035827494975e1 : ℝ) :=
  rowB08_bnd.strict (by norm_num) (by norm_num)

/-- Row B09, up/down `m_u/m_d`. -/
noncomputable def rowB09 : ℝ :=
  ((17 : ℝ) / 37)

theorem rowB09_bnd : Bnd rowB09 ((17 : ℝ) / 37) ((17 : ℝ) / 37) := by
  unfold rowB09
  have h1 : Bnd ((17 : ℝ) / 37) ((17 : ℝ) / 37) ((17 : ℝ) / 37) := Bnd.const _
  exact h1

/-- **Row B09 to its printed digits, `0.459459459459`.** -/
theorem rowB09_digits : (4.594594594585e-1 : ℝ) < rowB09 ∧ rowB09 < (4.594594594595e-1 : ℝ) :=
  rowB09_bnd.strict (by norm_num) (by norm_num)

/-- Row B10, up factor per visit to the symmetric states, `kappa`. -/
noncomputable def rowB10 : ℝ :=
  qKap

theorem rowB10_bnd : Bnd rowB10 (1.9131367509386862492998217 : ℝ) (1.9131367509386862492998218 : ℝ) := by
  unfold rowB10
  exact qKap_bnd

/-- **Row B10 to its printed digits, `1.91313675094`.** -/
theorem rowB10_digits : (1.913136750935 : ℝ) < rowB10 ∧ rowB10 < (1.913136750945 : ℝ) :=
  rowB10_bnd.strict (by norm_num) (by norm_num)

/-- Row B11, charm/strange. -/
noncomputable def rowB11 : ℝ :=
  (((17 : ℝ) / 37) * (qKap ^ 5))

theorem rowB11_bnd : Bnd rowB11 (1.1775443412162162162162159e1 : ℝ) (1.1775443412162162162162164e1 : ℝ) := by
  unfold rowB11
  have h1 : Bnd ((17 : ℝ) / 37) ((17 : ℝ) / 37) ((17 : ℝ) / 37) := Bnd.const _
  have h2 := Bnd.pow qKap_bnd (by norm_num) 5
  have h3 : Bnd ((qKap ^ 5)) (2.5628906249999999999999994e1 : ℝ) (2.5628906250000000000000002e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.mul h1 h3 (by norm_num) (by norm_num)
  have h5 : Bnd ((((17 : ℝ) / 37) * (qKap ^ 5))) (1.1775443412162162162162159e1 : ℝ) (1.1775443412162162162162164e1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- **Row B11 to its printed digits, `11.7754434122`.** -/
theorem rowB11_digits : (1.177544341215e1 : ℝ) < rowB11 ∧ rowB11 < (1.177544341225e1 : ℝ) :=
  rowB11_bnd.strict (by norm_num) (by norm_num)

/-- Row B12, proton/electron `m_p/m_e`. -/
noncomputable def rowB12 : ℝ :=
  qRp

theorem rowB12_bnd : Bnd rowB12 (1.8361526734120517861459969e3 : ℝ) (1.8361526734120517861459972e3 : ℝ) := by
  unfold rowB12
  exact qRp_bnd

/-- **Row B12 to its printed digits, `1836.15267341`.** -/
theorem rowB12_digits : (1.836152673405e3 : ℝ) < rowB12 ∧ rowB12 < (1.836152673415e3 : ℝ) :=
  rowB12_bnd.strict (by norm_num) (by norm_num)

/-- Row B13, neutron/proton `m_n/m_p`. -/
noncomputable def rowB13 : ℝ :=
  qRn

theorem rowB13_bnd : Bnd rowB13 (1.0013784195646195665100965 : ℝ) (1.0013784195646195665100966 : ℝ) := by
  unfold rowB13
  exact qRn_bnd

/-- **Row B13 to its printed digits, `1.00137841956`.** -/
theorem rowB13_digits : (1.001378419555 : ℝ) < rowB13 ∧ rowB13 < (1.001378419565 : ℝ) :=
  rowB13_bnd.strict (by norm_num) (by norm_num)

/-- Row B14, neutron/electron `m_n/m_e`. -/
noncomputable def rowB14 : ℝ :=
  (qRp * qRn)

theorem rowB14_bnd : Bnd rowB14 (1.8386836621807114796652719e3 : ℝ) (1.8386836621807114796652725e3 : ℝ) := by
  unfold rowB14
  have h1 := Bnd.mul qRp_bnd qRn_bnd (by norm_num) (by norm_num)
  have h2 : Bnd ((qRp * qRn)) (1.8386836621807114796652719e3 : ℝ) (1.8386836621807114796652725e3 : ℝ) := h1.weak (by norm_num) (by norm_num)
  exact h2

/-- **Row B14 to its printed digits, `1838.68366218`.** -/
theorem rowB14_digits : (1.838683662175e3 : ℝ) < rowB14 ∧ rowB14 < (1.838683662185e3 : ℝ) :=
  rowB14_bnd.strict (by norm_num) (by norm_num)

/-- Row J01, `m_p/m_e`. -/
noncomputable def rowJ01 : ℝ :=
  qRp

theorem rowJ01_bnd : Bnd rowJ01 (1.8361526734120517861459969e3 : ℝ) (1.8361526734120517861459972e3 : ℝ) := by
  unfold rowJ01
  exact qRp_bnd

/-- **Row J01 to its printed digits, `1836.15267341`.** -/
theorem rowJ01_digits : (1.836152673405e3 : ℝ) < rowJ01 ∧ rowJ01 < (1.836152673415e3 : ℝ) :=
  rowJ01_bnd.strict (by norm_num) (by norm_num)

/-- Row J02, `m_n/m_p`. -/
noncomputable def rowJ02 : ℝ :=
  qRn

theorem rowJ02_bnd : Bnd rowJ02 (1.0013784195646195665100965 : ℝ) (1.0013784195646195665100966 : ℝ) := by
  unfold rowJ02
  exact qRn_bnd

/-- **Row J02 to its printed digits, `1.00137841956`.** -/
theorem rowJ02_digits : (1.001378419555 : ℝ) < rowJ02 ∧ rowJ02 < (1.001378419565 : ℝ) :=
  rowJ02_bnd.strict (by norm_num) (by norm_num)

/-- Row L01, `tau` pole mass [MeV]. -/
noncomputable def rowL01 : ℝ :=
  ((qMe * qRmu) * qRtau)

theorem rowL01_bnd : Bnd rowL01 (1.7769795428631928602592152e3 : ℝ) (1.7769795428631928602592161e3 : ℝ) := by
  unfold rowL01
  have h1 := Bnd.mul qMe_bnd qRmu_bnd (by norm_num) (by norm_num)
  have h2 : Bnd ((qMe * qRmu)) (1.0565837613211024890960472e2 : ℝ) (1.0565837613211024890960474e2 : ℝ) := h1.weak (by norm_num) (by norm_num)
  have h3 := Bnd.mul h2 qRtau_bnd (by norm_num) (by norm_num)
  have h4 : Bnd (((qMe * qRmu) * qRtau)) (1.7769795428631928602592152e3 : ℝ) (1.7769795428631928602592161e3 : ℝ) := h3.weak (by norm_num) (by norm_num)
  exact h4

/-- **Row L01 to its printed digits, `1776.97954286`.** -/
theorem rowL01_digits : (1.776979542855e3 : ℝ) < rowL01 ∧ rowL01 < (1.776979542865e3 : ℝ) :=
  rowL01_bnd.strict (by norm_num) (by norm_num)

/-- Row L05, forbidden charged-lepton threshold [MeV]. -/
noncomputable def rowL05 : ℝ :=
  (((3 : ℝ) ^ (5 / 2 : ℝ)) * qMe)

theorem rowL05_bnd : Bnd rowL05 (7.9656853068851706620450298 : ℝ) (7.9656853068851706620450304 : ℝ) := by
  unfold rowL05
  have h1 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h2 : Bnd (((3 : ℝ) ^ (5 / 2 : ℝ))) (1.5588457268119895641747017e1 : ℝ) (1.5588457268119895641747018e1 : ℝ) := Bnd.rpow' (p := 5) (q := 2) h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 := Bnd.mul h2 qMe_bnd (by norm_num) (by norm_num)
  have h4 : Bnd ((((3 : ℝ) ^ (5 / 2 : ℝ)) * qMe)) (7.9656853068851706620450298 : ℝ) (7.9656853068851706620450304 : ℝ) := h3.weak (by norm_num) (by norm_num)
  exact h4

/-- **Row L05 to its printed digits, `7.96568530689`.** -/
theorem rowL05_digits : (7.965685306885 : ℝ) < rowL05 ∧ rowL05 < (7.965685306895 : ℝ) :=
  rowL05_bnd.strict (by norm_num) (by norm_num)

/-- Row L17, Koide discrimination. -/
noncomputable def rowL17 : ℝ :=
  qKoide

theorem rowL17_bnd : Bnd rowL17 (6.6666725976109061536212319e-1 : ℝ) (6.6666725976109061536212375e-1 : ℝ) := by
  unfold rowL17
  exact qKoide_bnd

/-- **Row L17 to its printed digits, `0.666667259761`.** -/
theorem rowL17_digits : (6.666672597605e-1 : ℝ) < rowL17 ∧ rowL17 < (6.666672597615e-1 : ℝ) :=
  rowL17_bnd.strict (by norm_num) (by norm_num)

end Comparison.Article
