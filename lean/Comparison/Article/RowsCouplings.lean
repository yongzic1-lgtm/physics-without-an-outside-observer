import Comparison.Article.QLeptonsQuarks

/-!
# The rows of the couplings and of the last-step direction

D01 to D17, L14, L15, L19, L20, S07, S16, and the Planck sequence T01, T02.
-/

namespace Comparison.Article

open Real

/-- Row D01, strong coupling `alpha_s(M_Z)`. -/
noncomputable def rowD01 : ℝ :=
  qAlphaS

theorem rowD01_bnd : Bnd rowD01 (1.1785113019775792073347406e-1 : ℝ) (1.1785113019775792073347407e-1 : ℝ) := by
  unfold rowD01
  exact qAlphaS_bnd

/-- **Row D01 to its printed digits, `0.117851130198`.** -/
theorem rowD01_digits : (1.178511301975e-1 : ℝ) < rowD01 ∧ rowD01 < (1.178511301985e-1 : ℝ) :=
  rowD01_bnd.strict (by norm_num) (by norm_num)

/-- Row D02, inverse electric coupling `1/alpha`. -/
noncomputable def rowD02 : ℝ :=
  (((1 : ℝ) - qX) / ((27 : ℝ) / 3700))

theorem rowD02_bnd : Bnd rowD02 (1.3703599917709572158181338e2 : ℝ) (1.3703599917709572158181463e2 : ℝ) := by
  unfold rowD02
  have h1 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h2 := Bnd.sub h1 qX_bnd
  have h3 : Bnd (((1 : ℝ) - qX)) (9.9999242642745526559701657e-1 : ℝ) (9.9999242642745526559702567e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd ((27 : ℝ) / 3700) ((27 : ℝ) / 3700) ((27 : ℝ) / 3700) := Bnd.const _
  have h5 := Bnd.div h3 h4 (by norm_num) (by norm_num)
  have h6 : Bnd ((((1 : ℝ) - qX) / ((27 : ℝ) / 3700))) (1.3703599917709572158181338e2 : ℝ) (1.3703599917709572158181463e2 : ℝ) := h5.weak (by norm_num) (by norm_num)
  exact h6

/-- **Row D02 to its printed digits, `137.035999177`.** -/
theorem rowD02_digits : (1.370359991765e2 : ℝ) < rowD02 ∧ rowD02 < (1.370359991775e2 : ℝ) :=
  rowD02_bnd.strict (by norm_num) (by norm_num)

/-- Row D03, Fermi coefficient `G_F` [`10^{-5}`,GeV`^{-2}`]. -/
noncomputable def rowD03 : ℝ :=
  (qGF * (100000 : ℝ))

theorem rowD03_bnd : Bnd rowD03 (1.1663788587064412272608604 : ℝ) (1.1663788587064412272608763 : ℝ) := by
  unfold rowD03
  have h1 : Bnd (100000 : ℝ) (100000 : ℝ) (100000 : ℝ) := Bnd.const _
  have h2 := Bnd.mul qGF_bnd h1 (by norm_num) (by norm_num)
  have h3 : Bnd ((qGF * (100000 : ℝ))) (1.1663788587064412272608604 : ℝ) (1.1663788587064412272608763 : ℝ) := h2.weak (by norm_num) (by norm_num)
  exact h3

/-- **Row D03 to its printed digits, `1.16637885871`.** -/
theorem rowD03_digits : (1.166378858705 : ℝ) < rowD03 ∧ rowD03 < (1.166378858715 : ℝ) :=
  rowD03_bnd.strict (by norm_num) (by norm_num)

/-- Row D04, gravitational coupling `Gm_p^2/hbar c` [`10^{-39}`]. -/
noncomputable def rowD04 : ℝ :=
  ((qW ^ 2) * (1000000000000000000000000000000000000000 : ℝ))

theorem rowD04_bnd : Bnd rowD04 (5.9061524937714610760366769 : ℝ) (5.906152493771461076036677 : ℝ) := by
  unfold rowD04
  have h1 := Bnd.pow qW_bnd (by norm_num) 2
  have h2 : Bnd ((qW ^ 2)) (5.9061524937714610760366769e-39 : ℝ) (5.906152493771461076036677e-39 : ℝ) := h1.weak (by norm_num) (by norm_num)
  have h3 : Bnd (1000000000000000000000000000000000000000 : ℝ) (1000000000000000000000000000000000000000 : ℝ) (1000000000000000000000000000000000000000 : ℝ) := Bnd.const _
  have h4 := Bnd.mul h2 h3 (by norm_num) (by norm_num)
  have h5 : Bnd (((qW ^ 2) * (1000000000000000000000000000000000000000 : ℝ))) (5.9061524937714610760366769 : ℝ) (5.906152493771461076036677 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- **Row D04 to its printed digits, `5.90615249377`.** -/
theorem rowD04_digits : (5.906152493765 : ℝ) < rowD04 ∧ rowD04 < (5.906152493775 : ℝ) :=
  rowD04_bnd.strict (by norm_num) (by norm_num)

/-- The Planck mass `M_Pl = m_p/W` in GeV. -/
noncomputable def qMpl : ℝ :=
  ((qMp / (1000 : ℝ)) / qW)

theorem qMpl_bnd : Bnd qMpl (1.2208898118854217646727213e19 : ℝ) (1.2208898118854217646727216e19 : ℝ) := by
  unfold qMpl
  have h1 : Bnd (1000 : ℝ) (1000 : ℝ) (1000 : ℝ) := Bnd.const _
  have h2 := Bnd.div qMp_bnd h1 (by norm_num) (by norm_num)
  have h3 : Bnd ((qMp / (1000 : ℝ))) (9.3827208942019672472054469e-1 : ℝ) (9.3827208942019672472054485e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.div h3 qW_bnd (by norm_num) (by norm_num)
  have h5 : Bnd (((qMp / (1000 : ℝ)) / qW)) (1.2208898118854217646727213e19 : ℝ) (1.2208898118854217646727216e19 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- Row D05, Planck mass, `m_p` over the square root of the gravitational coupling [`10^{19}`,GeV]. -/
noncomputable def rowD05 : ℝ :=
  (qMpl / (10000000000000000000 : ℝ))

theorem rowD05_bnd : Bnd rowD05 (1.2208898118854217646727213 : ℝ) (1.2208898118854217646727216 : ℝ) := by
  unfold rowD05
  have h1 : Bnd (10000000000000000000 : ℝ) (10000000000000000000 : ℝ) (10000000000000000000 : ℝ) := Bnd.const _
  have h2 := Bnd.div qMpl_bnd h1 (by norm_num) (by norm_num)
  have h3 : Bnd ((qMpl / (10000000000000000000 : ℝ))) (1.2208898118854217646727213 : ℝ) (1.2208898118854217646727216 : ℝ) := h2.weak (by norm_num) (by norm_num)
  exact h3

/-- **Row D05 to its printed digits, `1.22088981189`.** -/
theorem rowD05_digits : (1.220889811885 : ℝ) < rowD05 ∧ rowD05 < (1.220889811895 : ℝ) :=
  rowD05_bnd.strict (by norm_num) (by norm_num)

/-- Row D08, `overline{rm MS}` weak angle `3N_h`. -/
noncomputable def rowD08 : ℝ :=
  qSw

theorem rowD08_bnd : Bnd rowD08 (2.31257521689421775544e-1 : ℝ) (2.312575216894228455378e-1 : ℝ) := by
  unfold rowD08
  exact qSw_bnd

/-- **Row D08 to its printed digits, `0.231257521689`.** -/
theorem rowD08_digits : (2.312575216885e-1 : ℝ) < rowD08 ∧ rowD08 < (2.312575216895e-1 : ℝ) :=
  rowD08_bnd.strict (by norm_num) (by norm_num)

/-- Row D09, effective weak angle `3N_{rm con}`. -/
noncomputable def rowD09 : ℝ :=
  ((3 : ℝ) * qNcon)

theorem rowD09_bnd : Bnd rowD09 (2.3155023393785275754769e-1 : ℝ) (2.3155023393785382754149e-1 : ℝ) := by
  unfold rowD09
  have h1 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qNcon_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((3 : ℝ) * qNcon)) (2.3155023393785275754769e-1 : ℝ) (2.3155023393785382754149e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  exact h3

/-- **Row D09 to its printed digits, `0.231550233938`.** -/
theorem rowD09_digits : (2.315502339375e-1 : ℝ) < rowD09 ∧ rowD09 < (2.315502339385e-1 : ℝ) :=
  rowD09_bnd.strict (by norm_num) (by norm_num)

/-- Row D10, on-shell weak angle `3N_h/(1+f)`. -/
noncomputable def rowD10 : ℝ :=
  qOsw

theorem rowD10_bnd : Bnd rowD10 (2.232215460322604011042471e-1 : ℝ) (2.2322154603226143391679537e-1 : ℝ) := by
  unfold rowD10
  exact qOsw_bnd

/-- **Row D10 to its printed digits, `0.223221546032`.** -/
theorem rowD10_digits : (2.232215460315e-1 : ℝ) < rowD10 ∧ rowD10 < (2.232215460325e-1 : ℝ) :=
  rowD10_bnd.strict (by norm_num) (by norm_num)

/-- Row D11, `W` mass [GeV]. -/
noncomputable def rowD11 : ℝ :=
  qMw

theorem rowD11_bnd : Bnd rowD11 (8.036625104033244980113877e1 : ℝ) (8.0366251040332635722550764e1 : ℝ) := by
  unfold rowD11
  exact qMw_bnd

/-- **Row D11 to its printed digits, `80.3662510403`.** -/
theorem rowD11_digits : (8.036625104025e1 : ℝ) < rowD11 ∧ rowD11 < (8.036625104035e1 : ℝ) :=
  rowD11_bnd.strict (by norm_num) (by norm_num)

/-- Row D12, `Z` mass [GeV]. -/
noncomputable def rowD12 : ℝ :=
  qMz

theorem rowD12_bnd : Bnd rowD12 (9.1185361518345607148409049e1 : ℝ) (9.1185361518345878719530501e1 : ℝ) := by
  unfold rowD12
  exact qMz_bnd

/-- **Row D12 to its printed digits, `91.1853615183`.** -/
theorem rowD12_digits : (9.118536151825e1 : ℝ) < rowD12 ∧ rowD12 < (9.118536151835e1 : ℝ) :=
  rowD12_bnd.strict (by norm_num) (by norm_num)

/-- Row D13, `W/Z` mass ratio. -/
noncomputable def rowD13 : ℝ :=
  (qMw / qMz)

theorem rowD13_bnd : Bnd rowD13 (8.8135035823884191125868615e-1 : ℝ) (8.8135035823884657506338125e-1 : ℝ) := by
  unfold rowD13
  have h1 := Bnd.div qMw_bnd qMz_bnd (by norm_num) (by norm_num)
  have h2 : Bnd ((qMw / qMz)) (8.8135035823884191125868615e-1 : ℝ) (8.8135035823884657506338125e-1 : ℝ) := h1.weak (by norm_num) (by norm_num)
  exact h2

/-- **Row D13 to its printed digits, `0.881350358239`.** -/
theorem rowD13_digits : (8.813503582385e-1 : ℝ) < rowD13 ∧ rowD13 < (8.813503582395e-1 : ℝ) :=
  rowD13_bnd.strict (by norm_num) (by norm_num)

/-- Row D15, electroweak scale `v=(sqrt2G_F)^{-1/2}` [GeV]. -/
noncomputable def rowD15 : ℝ :=
  qV

theorem rowD15_bnd : Bnd rowD15 (2.4621963404287102263672166e2 : ℝ) (2.4621963404287102263672337e2 : ℝ) := by
  unfold rowD15
  exact qV_bnd

/-- **Row D15 to its printed digits, `246.219634043`.** -/
theorem rowD15_digits : (2.462196340425e2 : ℝ) < rowD15 ∧ rowD15 < (2.462196340435e2 : ℝ) :=
  rowD15_bnd.strict (by norm_num) (by norm_num)

/-- Row D16, scalar mass `m_H` [GeV]. -/
noncomputable def rowD16 : ℝ :=
  qMh

theorem rowD16_bnd : Bnd rowD16 (1.2513477159340231894515854e2 : ℝ) (1.2513477159340231894535915e2 : ℝ) := by
  unfold rowD16
  exact qMh_bnd

/-- **Row D16 to its printed digits, `125.134771593`.** -/
theorem rowD16_digits : (1.251347715925e2 : ℝ) < rowD16 ∧ rowD16 < (1.251347715935e2 : ℝ) :=
  rowD16_bnd.strict (by norm_num) (by norm_num)

/-- Row D17, top mass [GeV]. -/
noncomputable def rowD17 : ℝ :=
  qMt

theorem rowD17_bnd : Bnd rowD17 (1.7264661361444158874927995e2 : ℝ) (1.7264661361444158874928116e2 : ℝ) := by
  unfold rowD17
  exact qMt_bnd

/-- **Row D17 to its printed digits, `172.646613614`.** -/
theorem rowD17_digits : (1.726466136135e2 : ℝ) < rowD17 ∧ rowD17 < (1.726466136145e2 : ℝ) :=
  rowD17_bnd.strict (by norm_num) (by norm_num)

/-- Row L15, `W` pole mass test [GeV]. -/
noncomputable def rowL15 : ℝ :=
  qMw

theorem rowL15_bnd : Bnd rowL15 (8.036625104033244980113877e1 : ℝ) (8.0366251040332635722550764e1 : ℝ) := by
  unfold rowL15
  exact qMw_bnd

/-- **Row L15 to its printed digits, `80.3662510403`.** -/
theorem rowL15_digits : (8.036625104025e1 : ℝ) < rowL15 ∧ rowL15 < (8.036625104035e1 : ℝ) :=
  rowL15_bnd.strict (by norm_num) (by norm_num)

/-- Row L19, clock-independent lower bound on `1/alpha`. -/
noncomputable def rowL19 : ℝ :=
  (((1 : ℝ) - (((9 : ℝ) / 4000) / ((297 : ℝ) + N1))) / ((27 : ℝ) / 3700))

theorem rowL19_bnd : Bnd rowL19 (1.3703599914705592448465173e2 : ℝ) (1.3703599914705592448465348e2 : ℝ) := by
  unfold rowL19
  have h1 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h2 : Bnd ((9 : ℝ) / 4000) ((9 : ℝ) / 4000) ((9 : ℝ) / 4000) := Bnd.const _
  have h3 : Bnd (297 : ℝ) (297 : ℝ) (297 : ℝ) := Bnd.const _
  have h4 := Bnd.add h3 N1_bnd
  have h5 : Bnd (((297 : ℝ) + N1)) (2.970770880771192245e2 : ℝ) (2.97077088077119225e2 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.div h2 h5 (by norm_num) (by norm_num)
  have h7 : Bnd ((((9 : ℝ) / 4000) / ((297 : ℝ) + N1))) (7.5737917540645714475804665e-6 : ℝ) (7.5737917540645714603276492e-6 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 := Bnd.sub h1 h7
  have h9 : Bnd (((1 : ℝ) - (((9 : ℝ) / 4000) / ((297 : ℝ) + N1)))) (9.9999242620824593542853967e-1 : ℝ) (9.9999242620824593542855242e-1 : ℝ) := h8.weak (by norm_num) (by norm_num)
  have h10 : Bnd ((27 : ℝ) / 3700) ((27 : ℝ) / 3700) ((27 : ℝ) / 3700) := Bnd.const _
  have h11 := Bnd.div h9 h10 (by norm_num) (by norm_num)
  have h12 : Bnd ((((1 : ℝ) - (((9 : ℝ) / 4000) / ((297 : ℝ) + N1))) / ((27 : ℝ) / 3700))) (1.3703599914705592448465173e2 : ℝ) (1.3703599914705592448465348e2 : ℝ) := h11.weak (by norm_num) (by norm_num)
  exact h12

/-- **Row L19 to its printed digits, `137.035999147`.** -/
theorem rowL19_digits : (1.370359991465e2 : ℝ) < rowL19 ∧ rowL19 < (1.370359991475e2 : ℝ) :=
  rowL19_bnd.strict (by norm_num) (by norm_num)

/-- Row L20, clock-independent upper bound on the `overline{rm MS}` weak angle. -/
noncomputable def rowL20 : ℝ :=
  ((3 : ℝ) * N1)

theorem rowL20_bnd : Bnd rowL20 (2.312642313576735e-1 : ℝ) (2.31264231357675e-1 : ℝ) := by
  unfold rowL20
  have h1 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 N1_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((3 : ℝ) * N1)) (2.312642313576735e-1 : ℝ) (2.31264231357675e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  exact h3

/-- **Row L20 to its printed digits, `0.231264231358`.** -/
theorem rowL20_digits : (2.312642313575e-1 : ℝ) < rowL20 ∧ rowL20 < (2.312642313585e-1 : ℝ) :=
  rowL20_bnd.strict (by norm_num) (by norm_num)

/-- Row S07, top mass, second construction [GeV]. -/
noncomputable def rowS07 : ℝ :=
  (((qMp * qMp) / ((10 : ℝ) * qMe)) / (1000 : ℝ))

theorem rowS07_bnd : Bnd rowS07 (1.7228108053768059266180018e2 : ℝ) (1.7228108053768059266180025e2 : ℝ) := by
  unfold rowS07
  have h1 := Bnd.mul qMp_bnd qMp_bnd (by norm_num) (by norm_num)
  have h2 : Bnd ((qMp * qMp)) (8.803545137849416385655721e5 : ℝ) (8.8035451378494163856557241e5 : ℝ) := h1.weak (by norm_num) (by norm_num)
  have h3 : Bnd (10 : ℝ) (10 : ℝ) (10 : ℝ) := Bnd.const _
  have h4 := Bnd.mul h3 qMe_bnd (by norm_num) (by norm_num)
  have h5 : Bnd (((10 : ℝ) * qMe)) (5.1099895069 : ℝ) (5.1099895069 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.div h2 h5 (by norm_num) (by norm_num)
  have h7 : Bnd (((qMp * qMp) / ((10 : ℝ) * qMe))) (1.7228108053768059266180018e5 : ℝ) (1.7228108053768059266180025e5 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 : Bnd (1000 : ℝ) (1000 : ℝ) (1000 : ℝ) := Bnd.const _
  have h9 := Bnd.div h7 h8 (by norm_num) (by norm_num)
  have h10 : Bnd ((((qMp * qMp) / ((10 : ℝ) * qMe)) / (1000 : ℝ))) (1.7228108053768059266180018e2 : ℝ) (1.7228108053768059266180025e2 : ℝ) := h9.weak (by norm_num) (by norm_num)
  exact h10

/-- **Row S07 to its printed digits, `172.281080538`.** -/
theorem rowS07_digits : (1.722810805375e2 : ℝ) < rowS07 ∧ rowS07 < (1.722810805385e2 : ℝ) :=
  rowS07_bnd.strict (by norm_num) (by norm_num)

/-- Row S16, five-flavour one-loop scale marker [MeV]. -/
noncomputable def rowS16 : ℝ :=
  ((qMz * (1000 : ℝ)) * (Real.exp (-(((2 : ℝ) * π) / (((23 : ℝ) / 3) * qAlphaS)))))

theorem rowS16_bnd : Bnd rowS16 (8.7057777826485077468966488e1 : ℝ) (8.7057777826485336749115074e1 : ℝ) := by
  unfold rowS16
  have h1 : Bnd (1000 : ℝ) (1000 : ℝ) (1000 : ℝ) := Bnd.const _
  have h2 := Bnd.mul qMz_bnd h1 (by norm_num) (by norm_num)
  have h3 : Bnd ((qMz * (1000 : ℝ))) (9.1185361518345607148409049e4 : ℝ) (9.1185361518345878719530501e4 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h5 := Bnd.mul h4 bnd_pi (by norm_num) (by norm_num)
  have h6 : Bnd (((2 : ℝ) * π)) (6.28318530717958647692 : ℝ) (6.28318530717958647694 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 : Bnd ((23 : ℝ) / 3) ((23 : ℝ) / 3) ((23 : ℝ) / 3) := Bnd.const _
  have h8 := Bnd.mul h7 qAlphaS_bnd (by norm_num) (by norm_num)
  have h9 : Bnd ((((23 : ℝ) / 3) * qAlphaS)) (9.0352533151614405895663446e-1 : ℝ) (9.0352533151614405895663454e-1 : ℝ) := h8.weak (by norm_num) (by norm_num)
  have h10 := Bnd.div h6 h9 (by norm_num) (by norm_num)
  have h11 : Bnd ((((2 : ℝ) * π) / (((23 : ℝ) / 3) * qAlphaS))) (6.9540776423348341257581357 : ℝ) (6.954077642334834125780272 : ℝ) := h10.weak (by norm_num) (by norm_num)
  have h12 := Bnd.neg h11
  have h13 : Bnd ((-(((2 : ℝ) * π) / (((23 : ℝ) / 3) * qAlphaS)))) (-6.954077642334834125780272 : ℝ) (-6.9540776423348341257581357 : ℝ) := h12.weak (by norm_num) (by norm_num)
  have h14 : Bnd ((Real.exp (-(((2 : ℝ) * π) / (((23 : ℝ) / 3) * qAlphaS))))) (9.5473414127957259874303165e-4 : ℝ) (9.5473414127957259876416606e-4 : ℝ) := Bnd.exp h13 (exp_ge_split (-6.954077642334834125780272 : ℝ) ((-8.69259705291854265722534e-1 : ℝ)) (4.1926181169116941877775819e-1 : ℝ) (9.5473414127957259874303165e-4 : ℝ) 8 (by norm_num) (by norm_num) (exp_ge' ((-8.69259705291854265722534e-1 : ℝ)) (((434629852645927132861267 : ℝ) / 500000000000000000000000)) (4.1926181169116941877775819e-1 : ℝ) 28 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (by norm_num)) (exp_le_split (-6.9540776423348341257581357 : ℝ) ((-8.692597052918542657197669625e-1 : ℝ)) (4.1926181169116941877891831e-1 : ℝ) (9.5473414127957259876416606e-4 : ℝ) 8 (by norm_num) (exp_le' ((-8.692597052918542657197669625e-1 : ℝ)) (((69540776423348341257581357 : ℝ) / 80000000000000000000000000)) (4.1926181169116941877891831e-1 : ℝ) 28 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  have h15 := Bnd.mul h3 h14 (by norm_num) (by norm_num)
  have h16 : Bnd (((qMz * (1000 : ℝ)) * (Real.exp (-(((2 : ℝ) * π) / (((23 : ℝ) / 3) * qAlphaS)))))) (8.7057777826485077468966488e1 : ℝ) (8.7057777826485336749115074e1 : ℝ) := h15.weak (by norm_num) (by norm_num)
  exact h16

/-- **Row S16 to its printed digits, `87.0577778265`.** -/
theorem rowS16_digits : (8.705777782645e1 : ℝ) < rowS16 ∧ rowS16 < (8.705777782655e1 : ℝ) :=
  rowS16_bnd.strict (by norm_num) (by norm_num)

/-- The heavy neutral threshold `M_R = M_Pl 3⁻⁹` in GeV. -/
noncomputable def qMR : ℝ :=
  (qMpl * (((1 : ℝ) / 3) ^ 9))

theorem qMR_bnd : Bnd qMR (6.2027628506092656844623344e14 : ℝ) (6.2027628506092656844623362e14 : ℝ) := by
  unfold qMR
  have h1 : Bnd ((1 : ℝ) / 3) ((1 : ℝ) / 3) ((1 : ℝ) / 3) := Bnd.const _
  have h2 := Bnd.pow h1 (by norm_num) 9
  have h3 : Bnd ((((1 : ℝ) / 3) ^ 9)) (5.080526342529086013310979e-5 : ℝ) (5.0805263425290860133109791e-5 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.mul qMpl_bnd h3 (by norm_num) (by norm_num)
  have h5 : Bnd ((qMpl * (((1 : ℝ) / 3) ^ 9))) (6.2027628506092656844623344e14 : ℝ) (6.2027628506092656844623362e14 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- The plane-changing threshold `M_off = M_Pl 3⁻⁶` in GeV. -/
noncomputable def qMoff : ℝ :=
  (qMpl * (((1 : ℝ) / 3) ^ 6))

theorem qMoff_bnd : Bnd qMoff (1.6747459696645017348048302e16 : ℝ) (1.6747459696645017348048309e16 : ℝ) := by
  unfold qMoff
  have h1 : Bnd ((1 : ℝ) / 3) ((1 : ℝ) / 3) ((1 : ℝ) / 3) := Bnd.const _
  have h2 := Bnd.pow h1 (by norm_num) 6
  have h3 : Bnd ((((1 : ℝ) / 3) ^ 6)) (1.3717421124828532235939643e-3 : ℝ) (1.3717421124828532235939644e-3 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.mul qMpl_bnd h3 (by norm_num) (by norm_num)
  have h5 : Bnd ((qMpl * (((1 : ℝ) / 3) ^ 6))) (1.6747459696645017348048302e16 : ℝ) (1.6747459696645017348048309e16 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- Row T01, heavy neutral threshold `M_R` [GeV]. -/
noncomputable def rowT01 : ℝ :=
  qMR

theorem rowT01_bnd : Bnd rowT01 (6.2027628506092656844623344e14 : ℝ) (6.2027628506092656844623362e14 : ℝ) := by
  unfold rowT01
  exact qMR_bnd

/-- **Row T01 to its printed digits, `6.20276285061e14`.** -/
theorem rowT01_digits : (6.202762850605e14 : ℝ) < rowT01 ∧ rowT01 < (6.202762850615e14 : ℝ) :=
  rowT01_bnd.strict (by norm_num) (by norm_num)

/-- Row T02, heavy plane-changing threshold `M_{rm off}` [GeV]. -/
noncomputable def rowT02 : ℝ :=
  qMoff

theorem rowT02_bnd : Bnd rowT02 (1.6747459696645017348048302e16 : ℝ) (1.6747459696645017348048309e16 : ℝ) := by
  unfold rowT02
  exact qMoff_bnd

/-- **Row T02 to its printed digits, `1.67474596966e16`.** -/
theorem rowT02_digits : (1.674745969655e16 : ℝ) < rowT02 ∧ rowT02 < (1.674745969665e16 : ℝ) :=
  rowT02_bnd.strict (by norm_num) (by norm_num)

end Comparison.Article
