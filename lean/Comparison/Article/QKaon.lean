import Comparison.Article.QCosmos

/-!
# The kaons' numbers

The eigen-factors of the level operator `R = D^{1/2} G D^{1/2}`, `G₁₂ = (8/15)^{1/2}`, at the light level
`(R_ud, 1)`, at K⁰'s `(1, p)` and at K±'s `(R_ud, p)`; the light level's target `m_π⁰²/(6m_p²)`; its shift at the
two ends of an interval `[sdLo, sdHi]` of relative width `2·10⁻¹⁷`, below and above the target; and the two
kaons at every light level in that interval.
-/

namespace Comparison.Article

open Real

/-- The light level's upper eigen-factor `eigenPlus(R_ud, 1, 8/15)`. -/
noncomputable def qMuP : ℝ :=
  (((((17 : ℝ) / 37) + (1 : ℝ)) + (√((26128 : ℝ) / 20535))) / (2 : ℝ))

theorem qMuP_bnd : Bnd qMuP (1.2937253538590397817339699 : ℝ) (1.29372535385903978173397 : ℝ) := by
  unfold qMuP
  have h1 : Bnd ((17 : ℝ) / 37) ((17 : ℝ) / 37) ((17 : ℝ) / 37) := Bnd.const _
  have h2 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h3 := Bnd.add h1 h2
  have h4 : Bnd ((((17 : ℝ) / 37) + (1 : ℝ))) (1.4594594594594594594594594 : ℝ) (1.4594594594594594594594595 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 : Bnd ((26128 : ℝ) / 20535) ((26128 : ℝ) / 20535) ((26128 : ℝ) / 20535) := Bnd.const _
  have h6 : Bnd ((√((26128 : ℝ) / 20535))) (1.1279912482586201040084804 : ℝ) (1.1279912482586201040084805 : ℝ) := Bnd.sqrt h5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h7 := Bnd.add h4 h6
  have h8 : Bnd (((((17 : ℝ) / 37) + (1 : ℝ)) + (√((26128 : ℝ) / 20535)))) (2.5874507077180795634679398 : ℝ) (2.58745070771807956346794 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h10 := Bnd.div h8 h9 (by norm_num) (by norm_num)
  have h11 : Bnd ((((((17 : ℝ) / 37) + (1 : ℝ)) + (√((26128 : ℝ) / 20535))) / (2 : ℝ))) (1.2937253538590397817339699 : ℝ) (1.29372535385903978173397 : ℝ) := h10.weak (by norm_num) (by norm_num)
  exact h11

/-- The light level's lower eigen-factor `eigenMinus(R_ud, 1, 8/15)`. -/
noncomputable def qMuM : ℝ :=
  (((((17 : ℝ) / 37) + (1 : ℝ)) - (√((26128 : ℝ) / 20535))) / (2 : ℝ))

theorem qMuM_bnd : Bnd qMuM (1.6573410560041967772548945e-1 : ℝ) (1.6573410560041967772548955e-1 : ℝ) := by
  unfold qMuM
  have h1 : Bnd ((17 : ℝ) / 37) ((17 : ℝ) / 37) ((17 : ℝ) / 37) := Bnd.const _
  have h2 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h3 := Bnd.add h1 h2
  have h4 : Bnd ((((17 : ℝ) / 37) + (1 : ℝ))) (1.4594594594594594594594594 : ℝ) (1.4594594594594594594594595 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 : Bnd ((26128 : ℝ) / 20535) ((26128 : ℝ) / 20535) ((26128 : ℝ) / 20535) := Bnd.const _
  have h6 : Bnd ((√((26128 : ℝ) / 20535))) (1.1279912482586201040084804 : ℝ) (1.1279912482586201040084805 : ℝ) := Bnd.sqrt h5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h7 := Bnd.sub h4 h6
  have h8 : Bnd (((((17 : ℝ) / 37) + (1 : ℝ)) - (√((26128 : ℝ) / 20535)))) (3.314682112008393554509789e-1 : ℝ) (3.314682112008393554509791e-1 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h10 := Bnd.div h8 h9 (by norm_num) (by norm_num)
  have h11 : Bnd ((((((17 : ℝ) / 37) + (1 : ℝ)) - (√((26128 : ℝ) / 20535))) / (2 : ℝ))) (1.6573410560041967772548945e-1 : ℝ) (1.6573410560041967772548955e-1 : ℝ) := h10.weak (by norm_num) (by norm_num)
  exact h11

/-- `discR(1, p, 8/15)`. -/
noncomputable def qDiscP : ℝ :=
  (√(((qP - (1 : ℝ)) ^ 2) + (((32 : ℝ) / 15) * qP)))

theorem qDiscP_bnd : Bnd qDiscP (2.0053157355951237941524956e1 : ℝ) (2.0053157355951237941524966e1 : ℝ) := by
  unfold qDiscP
  have h1 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h2 := Bnd.sub qP_bnd h1
  have h3 : Bnd ((qP - (1 : ℝ))) (1.896165239377836331971512e1 : ℝ) (1.8961652393778363319715128e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.pow h3 (by norm_num) 2
  have h5 : Bnd (((qP - (1 : ℝ)) ^ 2)) (3.595442615024807358574051e2 : ℝ) (3.5954426150248073585740542e2 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 : Bnd ((32 : ℝ) / 15) ((32 : ℝ) / 15) ((32 : ℝ) / 15) := Bnd.const _
  have h7 := Bnd.mul h6 qP_bnd (by norm_num) (by norm_num)
  have h8 : Bnd ((((32 : ℝ) / 15) * qP)) (4.2584858440060508415392256e1 : ℝ) (4.2584858440060508415392274e1 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 := Bnd.add h5 h8
  have h10 : Bnd ((((qP - (1 : ℝ)) ^ 2) + (((32 : ℝ) / 15) * qP))) (4.0212911994254124427279735e2 : ℝ) (4.021291199425412442727977e2 : ℝ) := h9.weak (by norm_num) (by norm_num)
  have h11 : Bnd ((√(((qP - (1 : ℝ)) ^ 2) + (((32 : ℝ) / 15) * qP)))) (2.0053157355951237941524956e1 : ℝ) (2.0053157355951237941524966e1 : ℝ) := Bnd.sqrt h10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h11

/-- `eigenPlus(1, p, 8/15)`, the K⁰ level's upper eigen-factor. -/
noncomputable def qNuP : ℝ :=
  ((((1 : ℝ) + qP) + qDiscP) / (2 : ℝ))

theorem qNuP_bnd : Bnd qNuP (2.0507404874864800630620038e1 : ℝ) (2.0507404874864800630620047e1 : ℝ) := by
  unfold qNuP
  have h1 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h2 := Bnd.add h1 qP_bnd
  have h3 : Bnd (((1 : ℝ) + qP)) (2.096165239377836331971512e1 : ℝ) (2.0961652393778363319715128e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.add h3 qDiscP_bnd
  have h5 : Bnd ((((1 : ℝ) + qP) + qDiscP)) (4.1014809749729601261240076e1 : ℝ) (4.1014809749729601261240094e1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h7 := Bnd.div h5 h6 (by norm_num) (by norm_num)
  have h8 : Bnd (((((1 : ℝ) + qP) + qDiscP) / (2 : ℝ))) (2.0507404874864800630620038e1 : ℝ) (2.0507404874864800630620047e1 : ℝ) := h7.weak (by norm_num) (by norm_num)
  exact h8

/-- `eigenMinus(1, p, 8/15)`. -/
noncomputable def qNuM : ℝ :=
  ((((1 : ℝ) + qP) - qDiscP) / (2 : ℝ))

theorem qNuM_bnd : Bnd qNuM (4.54247518913562689095077e-1 : ℝ) (4.54247518913562689095086e-1 : ℝ) := by
  unfold qNuM
  have h1 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h2 := Bnd.add h1 qP_bnd
  have h3 : Bnd (((1 : ℝ) + qP)) (2.096165239377836331971512e1 : ℝ) (2.0961652393778363319715128e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.sub h3 qDiscP_bnd
  have h5 : Bnd ((((1 : ℝ) + qP) - qDiscP)) (9.08495037827125378190154e-1 : ℝ) (9.08495037827125378190172e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h7 := Bnd.div h5 h6 (by norm_num) (by norm_num)
  have h8 : Bnd (((((1 : ℝ) + qP) - qDiscP) / (2 : ℝ))) (4.54247518913562689095077e-1 : ℝ) (4.54247518913562689095086e-1 : ℝ) := h7.weak (by norm_num) (by norm_num)
  exact h8

/-- `discR(R_ud, p, 8/15)`. -/
noncomputable def qDiscK : ℝ :=
  (√(((qP - ((17 : ℝ) / 37)) ^ 2) + (((544 : ℝ) / 555) * qP)))

theorem qDiscK_bnd : Bnd qDiscK (1.9997538480708718934782487e1 : ℝ) (1.9997538480708718934782497e1 : ℝ) := by
  unfold qDiscK
  have h1 : Bnd ((17 : ℝ) / 37) ((17 : ℝ) / 37) ((17 : ℝ) / 37) := Bnd.const _
  have h2 := Bnd.sub qP_bnd h1
  have h3 : Bnd ((qP - ((17 : ℝ) / 37))) (1.950219293431890386025566e1 : ℝ) (1.9502192934318903860255669e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.pow h3 (by norm_num) 2
  have h5 : Bnd (((qP - ((17 : ℝ) / 37)) ^ 2)) (3.8033552924739817757630821e2 : ℝ) (3.8033552924739817757630857e2 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 : Bnd ((544 : ℝ) / 555) ((544 : ℝ) / 555) ((544 : ℝ) / 555) := Bnd.const _
  have h7 := Bnd.mul h6 qP_bnd (by norm_num) (by norm_num)
  have h8 : Bnd ((((544 : ℝ) / 555) * qP)) (1.9566016040027801163828874e1 : ℝ) (1.9566016040027801163828883e1 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 := Bnd.add h5 h8
  have h10 : Bnd ((((qP - ((17 : ℝ) / 37)) ^ 2) + (((544 : ℝ) / 555) * qP))) (3.9990154528742597874013708e2 : ℝ) (3.9990154528742597874013746e2 : ℝ) := h9.weak (by norm_num) (by norm_num)
  have h11 : Bnd ((√(((qP - ((17 : ℝ) / 37)) ^ 2) + (((544 : ℝ) / 555) * qP)))) (1.9997538480708718934782487e1 : ℝ) (1.9997538480708718934782497e1 : ℝ) := Bnd.sqrt h10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h11

/-- `eigenPlus(R_ud, p, 8/15)`, the K± level's upper eigen-factor. -/
noncomputable def qKapP : ℝ :=
  (((((17 : ℝ) / 37) + qP) + qDiscK) / (2 : ℝ))

theorem qKapP_bnd : Bnd qKapP (2.0209325166973270856978533e1 : ℝ) (2.0209325166973270856978543e1 : ℝ) := by
  unfold qKapP
  have h1 : Bnd ((17 : ℝ) / 37) ((17 : ℝ) / 37) ((17 : ℝ) / 37) := Bnd.const _
  have h2 := Bnd.add h1 qP_bnd
  have h3 : Bnd ((((17 : ℝ) / 37) + qP)) (2.0421111853237822779174579e1 : ℝ) (2.0421111853237822779174588e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.add h3 qDiscK_bnd
  have h5 : Bnd (((((17 : ℝ) / 37) + qP) + qDiscK)) (4.0418650333946541713957066e1 : ℝ) (4.0418650333946541713957085e1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h7 := Bnd.div h5 h6 (by norm_num) (by norm_num)
  have h8 : Bnd ((((((17 : ℝ) / 37) + qP) + qDiscK) / (2 : ℝ))) (2.0209325166973270856978533e1 : ℝ) (2.0209325166973270856978543e1 : ℝ) := h7.weak (by norm_num) (by norm_num)
  exact h8

/-- `eigenMinus(R_ud, p, 8/15)`. -/
noncomputable def qKapM : ℝ :=
  (((((17 : ℝ) / 37) + qP) - qDiscK) / (2 : ℝ))

theorem qKapM_bnd : Bnd qKapM (2.11786686264551922196041e-1 : ℝ) (2.117866862645519221960505e-1 : ℝ) := by
  unfold qKapM
  have h1 : Bnd ((17 : ℝ) / 37) ((17 : ℝ) / 37) ((17 : ℝ) / 37) := Bnd.const _
  have h2 := Bnd.add h1 qP_bnd
  have h3 : Bnd ((((17 : ℝ) / 37) + qP)) (2.0421111853237822779174579e1 : ℝ) (2.0421111853237822779174588e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.sub h3 qDiscK_bnd
  have h5 : Bnd (((((17 : ℝ) / 37) + qP) - qDiscK)) (4.23573372529103844392082e-1 : ℝ) (4.23573372529103844392101e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h7 := Bnd.div h5 h6 (by norm_num) (by norm_num)
  have h8 : Bnd ((((((17 : ℝ) / 37) + qP) - qDiscK) / (2 : ℝ))) (2.11786686264551922196041e-1 : ℝ) (2.117866862645519221960505e-1 : ℝ) := h7.weak (by norm_num) (by norm_num)
  exact h8

/-- The light level's target `m_π⁰²/(6 m_p²)`. -/
noncomputable def qTarget : ℝ :=
  ((qPi0 ^ 2) / ((6 : ℝ) * (qMp ^ 2)))

theorem qTarget_bnd : Bnd qTarget (3.4491412782790906922827891e-3 : ℝ) (3.4491412782790906922827939e-3 : ℝ) := by
  unfold qTarget
  have h1 := Bnd.pow qPi0_bnd (by norm_num) 2
  have h2 : Bnd ((qPi0 ^ 2)) (1.8218802558089765826623941e4 : ℝ) (1.8218802558089765826623959e4 : ℝ) := h1.weak (by norm_num) (by norm_num)
  have h3 : Bnd (6 : ℝ) (6 : ℝ) (6 : ℝ) := Bnd.const _
  have h4 := Bnd.pow qMp_bnd (by norm_num) 2
  have h5 : Bnd ((qMp ^ 2)) (8.803545137849416385655721e5 : ℝ) (8.8035451378494163856557241e5 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.mul h3 h5 (by norm_num) (by norm_num)
  have h7 : Bnd (((6 : ℝ) * (qMp ^ 2))) (5.2821270827096498313934326e6 : ℝ) (5.2821270827096498313934345e6 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 := Bnd.div h2 h7 (by norm_num) (by norm_num)
  have h9 : Bnd (((qPi0 ^ 2) / ((6 : ℝ) * (qMp ^ 2)))) (3.4491412782790906922827891e-3 : ℝ) (3.4491412782790906922827939e-3 : ℝ) := h8.weak (by norm_num) (by norm_num)
  exact h9

/-- The light level's shift at the left end `l` of the root's interval. -/
theorem light_level_at_l  :
    Bnd ((Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((59279081753726513400927 : ℝ) / 5000000000000000000000000) * qMuP)))))))))) + (Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((59279081753726513400927 : ℝ) / 5000000000000000000000000) * qMuM))))))))))) (3.449141278279090657905891e-3 : ℝ) (3.449141278279090657906292e-3 : ℝ) := by
  have h1 : Bnd (4 : ℝ) (4 : ℝ) (4 : ℝ) := Bnd.const _
  have h2 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h3 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h4 : Bnd (9 : ℝ) (9 : ℝ) (9 : ℝ) := Bnd.const _
  have h5 : Bnd (16 : ℝ) (16 : ℝ) (16 : ℝ) := Bnd.const _
  have h6 : Bnd ((59279081753726513400927 : ℝ) / 5000000000000000000000000) ((59279081753726513400927 : ℝ) / 5000000000000000000000000) ((59279081753726513400927 : ℝ) / 5000000000000000000000000) := Bnd.const _
  have h7 := Bnd.mul h6 qMuP_bnd (by norm_num) (by norm_num)
  have h8 : Bnd ((((59279081753726513400927 : ℝ) / 5000000000000000000000000) * qMuP)) (1.5338170203655756413236979e-2 : ℝ) (1.5338170203655756413236981e-2 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 := Bnd.neg h8
  have h10 : Bnd ((-(((59279081753726513400927 : ℝ) / 5000000000000000000000000) * qMuP))) (-1.5338170203655756413236981e-2 : ℝ) (-1.5338170203655756413236979e-2 : ℝ) := h9.weak (by norm_num) (by norm_num)
  have h11 : Bnd ((Real.exp (-(((59279081753726513400927 : ℝ) / 5000000000000000000000000) * qMuP)))) (9.8477886041972522717948124e-1 : ℝ) (9.8477886041972522717948125e-1 : ℝ) := Bnd.exp h10 (exp_ge' (-1.5338170203655756413236981e-2 : ℝ) (((15338170203655756413236981 : ℝ) / 1000000000000000000000000000)) (9.8477886041972522717948124e-1 : ℝ) 13 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' (-1.5338170203655756413236979e-2 : ℝ) (((15338170203655756413236979 : ℝ) / 1000000000000000000000000000)) (9.8477886041972522717948125e-1 : ℝ) 13 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h12 := Bnd.mul h5 h11 (by norm_num) (by norm_num)
  have h13 : Bnd (((16 : ℝ) * (Real.exp (-(((59279081753726513400927 : ℝ) / 5000000000000000000000000) * qMuP))))) (1.5756461766715603634871699e1 : ℝ) (1.57564617667156036348717e1 : ℝ) := h12.weak (by norm_num) (by norm_num)
  have h14 := Bnd.add h4 h13
  have h15 : Bnd (((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((59279081753726513400927 : ℝ) / 5000000000000000000000000) * qMuP)))))) (2.4756461766715603634871699e1 : ℝ) (2.47564617667156036348717e1 : ℝ) := h14.weak (by norm_num) (by norm_num)
  have h16 : Bnd ((√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((59279081753726513400927 : ℝ) / 5000000000000000000000000) * qMuP))))))) (4.9755865751402219606491358 : ℝ) (4.975586575140221960649136 : ℝ) := Bnd.sqrt h15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h17 := Bnd.add h3 h16
  have h18 : Bnd (((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((59279081753726513400927 : ℝ) / 5000000000000000000000000) * qMuP)))))))) (7.9755865751402219606491358 : ℝ) (7.975586575140221960649136 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 := Bnd.div h2 h18 (by norm_num) (by norm_num)
  have h20 : Bnd (((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((59279081753726513400927 : ℝ) / 5000000000000000000000000) * qMuP))))))))) (2.5076525483830475557265111e-1 : ℝ) (2.5076525483830475557265113e-1 : ℝ) := h19.weak (by norm_num) (by norm_num)
  have h21 := Bnd.mul h1 h20 (by norm_num) (by norm_num)
  have h22 : Bnd (((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((59279081753726513400927 : ℝ) / 5000000000000000000000000) * qMuP)))))))))) (1.0030610193532190222906044 : ℝ) (1.0030610193532190222906046 : ℝ) := h21.weak (by norm_num) (by norm_num)
  have h23 : Bnd ((Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((59279081753726513400927 : ℝ) / 5000000000000000000000000) * qMuP))))))))))) (3.05634397200376537519296e-3 : ℝ) (3.05634397200376537519316e-3 : ℝ) := Bnd.log h22 (by norm_num) (le_trans (exp_le' (3.05634397200376537519296e-3 : ℝ) (((4775537456255883398739 : ℝ) / 1562500000000000000000000)) (1.0030610193532190222906044 : ℝ) 10 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (by norm_num)) (le_trans (by norm_num) (exp_ge' (3.05634397200376537519316e-3 : ℝ) (((76408599300094134379829 : ℝ) / 25000000000000000000000000)) (1.0030610193532190222906046 : ℝ) 10 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])))
  have h24 : Bnd (4 : ℝ) (4 : ℝ) (4 : ℝ) := Bnd.const _
  have h25 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h26 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h27 : Bnd (9 : ℝ) (9 : ℝ) (9 : ℝ) := Bnd.const _
  have h28 : Bnd (16 : ℝ) (16 : ℝ) (16 : ℝ) := Bnd.const _
  have h29 : Bnd ((59279081753726513400927 : ℝ) / 5000000000000000000000000) ((59279081753726513400927 : ℝ) / 5000000000000000000000000) ((59279081753726513400927 : ℝ) / 5000000000000000000000000) := Bnd.const _
  have h30 := Bnd.mul h29 qMuM_bnd (by norm_num) (by norm_num)
  have h31 : Bnd ((((59279081753726513400927 : ℝ) / 5000000000000000000000000) * qMuM)) (1.9649131190536042551417115e-3 : ℝ) (1.9649131190536042551417128e-3 : ℝ) := h30.weak (by norm_num) (by norm_num)
  have h32 := Bnd.neg h31
  have h33 : Bnd ((-(((59279081753726513400927 : ℝ) / 5000000000000000000000000) * qMuM))) (-1.9649131190536042551417128e-3 : ℝ) (-1.9649131190536042551417115e-3 : ℝ) := h32.weak (by norm_num) (by norm_num)
  have h34 : Bnd ((Real.exp (-(((59279081753726513400927 : ℝ) / 5000000000000000000000000) * qMuM)))) (9.9803701605896650566245823e-1 : ℝ) (9.9803701605896650566245824e-1 : ℝ) := Bnd.exp h33 (exp_ge' (-1.9649131190536042551417128e-3 : ℝ) (((2456141398817005318927141 : ℝ) / 1250000000000000000000000000)) (9.9803701605896650566245823e-1 : ℝ) 10 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' (-1.9649131190536042551417115e-3 : ℝ) (((3929826238107208510283423 : ℝ) / 2000000000000000000000000000)) (9.9803701605896650566245824e-1 : ℝ) 10 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h35 := Bnd.mul h28 h34 (by norm_num) (by norm_num)
  have h36 : Bnd (((16 : ℝ) * (Real.exp (-(((59279081753726513400927 : ℝ) / 5000000000000000000000000) * qMuM))))) (1.5968592256943464090599331e1 : ℝ) (1.5968592256943464090599332e1 : ℝ) := h35.weak (by norm_num) (by norm_num)
  have h37 := Bnd.add h27 h36
  have h38 : Bnd (((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((59279081753726513400927 : ℝ) / 5000000000000000000000000) * qMuM)))))) (2.4968592256943464090599331e1 : ℝ) (2.4968592256943464090599332e1 : ℝ) := h37.weak (by norm_num) (by norm_num)
  have h39 : Bnd ((√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((59279081753726513400927 : ℝ) / 5000000000000000000000000) * qMuM))))))) (4.9968582386278944836262412 : ℝ) (4.9968582386278944836262414 : ℝ) := Bnd.sqrt h38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h40 := Bnd.add h26 h39
  have h41 : Bnd (((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((59279081753726513400927 : ℝ) / 5000000000000000000000000) * qMuM)))))))) (7.9968582386278944836262412 : ℝ) (7.9968582386278944836262414 : ℝ) := h40.weak (by norm_num) (by norm_num)
  have h42 := Bnd.div h25 h41 (by norm_num) (by norm_num)
  have h43 : Bnd (((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((59279081753726513400927 : ℝ) / 5000000000000000000000000) * qMuM))))))))) (2.5009821861530974761874942e-1 : ℝ) (2.5009821861530974761874944e-1 : ℝ) := h42.weak (by norm_num) (by norm_num)
  have h44 := Bnd.mul h24 h43 (by norm_num) (by norm_num)
  have h45 : Bnd (((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((59279081753726513400927 : ℝ) / 5000000000000000000000000) * qMuM)))))))))) (1.0003928744612389904749976 : ℝ) (1.0003928744612389904749978 : ℝ) := h44.weak (by norm_num) (by norm_num)
  have h46 : Bnd ((Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((59279081753726513400927 : ℝ) / 5000000000000000000000000) * qMuM))))))))))) (3.92797306275325282712931e-4 : ℝ) (3.92797306275325282713132e-4 : ℝ) := Bnd.log h45 (by norm_num) (le_trans (exp_le' (3.92797306275325282712931e-4 : ℝ) (((392797306275325282712931 : ℝ) / 1000000000000000000000000000)) (1.0003928744612389904749976 : ℝ) 8 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (by norm_num)) (le_trans (by norm_num) (exp_ge' (3.92797306275325282713132e-4 : ℝ) (((98199326568831320678283 : ℝ) / 250000000000000000000000000)) (1.0003928744612389904749978 : ℝ) 8 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])))
  have h47 := Bnd.add h23 h46
  have h48 : Bnd (((Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((59279081753726513400927 : ℝ) / 5000000000000000000000000) * qMuP)))))))))) + (Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((59279081753726513400927 : ℝ) / 5000000000000000000000000) * qMuM)))))))))))) (3.449141278279090657905891e-3 : ℝ) (3.449141278279090657906292e-3 : ℝ) := h47.weak (by norm_num) (by norm_num)
  exact h48

/-- The light level's shift at the right end `u`. -/
theorem light_level_at_u  :
    Bnd ((Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((118558163507453029173019 : ℝ) / 10000000000000000000000000) * qMuP)))))))))) + (Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((118558163507453029173019 : ℝ) / 10000000000000000000000000) * qMuM))))))))))) (3.449141278279090726659386e-3 : ℝ) (3.449141278279090726659697e-3 : ℝ) := by
  have h1 : Bnd (4 : ℝ) (4 : ℝ) (4 : ℝ) := Bnd.const _
  have h2 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h3 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h4 : Bnd (9 : ℝ) (9 : ℝ) (9 : ℝ) := Bnd.const _
  have h5 : Bnd (16 : ℝ) (16 : ℝ) (16 : ℝ) := Bnd.const _
  have h6 : Bnd ((118558163507453029173019 : ℝ) / 10000000000000000000000000) ((118558163507453029173019 : ℝ) / 10000000000000000000000000) ((118558163507453029173019 : ℝ) / 10000000000000000000000000) := Bnd.const _
  have h7 := Bnd.mul h6 qMuP_bnd (by norm_num) (by norm_num)
  have h8 : Bnd ((((118558163507453029173019 : ℝ) / 10000000000000000000000000) * qMuP)) (1.5338170203655756720000606e-2 : ℝ) (1.5338170203655756720000609e-2 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 := Bnd.neg h8
  have h10 : Bnd ((-(((118558163507453029173019 : ℝ) / 10000000000000000000000000) * qMuP))) (-1.5338170203655756720000609e-2 : ℝ) (-1.5338170203655756720000606e-2 : ℝ) := h9.weak (by norm_num) (by norm_num)
  have h11 : Bnd ((Real.exp (-(((118558163507453029173019 : ℝ) / 10000000000000000000000000) * qMuP)))) (9.847788604197252268773869e-1 : ℝ) (9.8477886041972522687738692e-1 : ℝ) := Bnd.exp h10 (exp_ge' (-1.5338170203655756720000609e-2 : ℝ) (((15338170203655756720000609 : ℝ) / 1000000000000000000000000000)) (9.847788604197252268773869e-1 : ℝ) 13 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' (-1.5338170203655756720000606e-2 : ℝ) (((7669085101827878360000303 : ℝ) / 500000000000000000000000000)) (9.8477886041972522687738692e-1 : ℝ) 13 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h12 := Bnd.mul h5 h11 (by norm_num) (by norm_num)
  have h13 : Bnd (((16 : ℝ) * (Real.exp (-(((118558163507453029173019 : ℝ) / 10000000000000000000000000) * qMuP))))) (1.575646176671560363003819e1 : ℝ) (1.5756461766715603630038191e1 : ℝ) := h12.weak (by norm_num) (by norm_num)
  have h14 := Bnd.add h4 h13
  have h15 : Bnd (((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((118558163507453029173019 : ℝ) / 10000000000000000000000000) * qMuP)))))) (2.475646176671560363003819e1 : ℝ) (2.4756461766715603630038191e1 : ℝ) := h14.weak (by norm_num) (by norm_num)
  have h16 : Bnd ((√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((118558163507453029173019 : ℝ) / 10000000000000000000000000) * qMuP))))))) (4.9755865751402219601634132 : ℝ) (4.9755865751402219601634134 : ℝ) := Bnd.sqrt h15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h17 := Bnd.add h3 h16
  have h18 : Bnd (((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((118558163507453029173019 : ℝ) / 10000000000000000000000000) * qMuP)))))))) (7.9755865751402219601634132 : ℝ) (7.9755865751402219601634134 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 := Bnd.div h2 h18 (by norm_num) (by norm_num)
  have h20 : Bnd (((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((118558163507453029173019 : ℝ) / 10000000000000000000000000) * qMuP))))))))) (2.5076525483830475558792301e-1 : ℝ) (2.5076525483830475558792303e-1 : ℝ) := h19.weak (by norm_num) (by norm_num)
  have h21 := Bnd.mul h1 h20 (by norm_num) (by norm_num)
  have h22 : Bnd (((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((118558163507453029173019 : ℝ) / 10000000000000000000000000) * qMuP)))))))))) (1.003061019353219022351692 : ℝ) (1.0030610193532190223516922 : ℝ) := h21.weak (by norm_num) (by norm_num)
  have h23 : Bnd ((Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((118558163507453029173019 : ℝ) / 10000000000000000000000000) * qMuP))))))))))) (3.05634397200376543609414e-3 : ℝ) (3.05634397200376543609435e-3 : ℝ) := Bnd.log h22 (by norm_num) (le_trans (exp_le' (3.05634397200376543609414e-3 : ℝ) (((152817198600188271804707 : ℝ) / 50000000000000000000000000)) (1.003061019353219022351692 : ℝ) 10 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (by norm_num)) (le_trans (by norm_num) (exp_ge' (3.05634397200376543609435e-3 : ℝ) (((61126879440075308721887 : ℝ) / 20000000000000000000000000)) (1.0030610193532190223516922 : ℝ) 10 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])))
  have h24 : Bnd (4 : ℝ) (4 : ℝ) (4 : ℝ) := Bnd.const _
  have h25 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h26 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h27 : Bnd (9 : ℝ) (9 : ℝ) (9 : ℝ) := Bnd.const _
  have h28 : Bnd (16 : ℝ) (16 : ℝ) (16 : ℝ) := Bnd.const _
  have h29 : Bnd ((118558163507453029173019 : ℝ) / 10000000000000000000000000) ((118558163507453029173019 : ℝ) / 10000000000000000000000000) ((118558163507453029173019 : ℝ) / 10000000000000000000000000) := Bnd.const _
  have h30 := Bnd.mul h29 qMuM_bnd (by norm_num) (by norm_num)
  have h31 : Bnd ((((118558163507453029173019 : ℝ) / 10000000000000000000000000) * qMuM)) (1.9649131190536042944400025e-3 : ℝ) (1.9649131190536042944400038e-3 : ℝ) := h30.weak (by norm_num) (by norm_num)
  have h32 := Bnd.neg h31
  have h33 : Bnd ((-(((118558163507453029173019 : ℝ) / 10000000000000000000000000) * qMuM))) (-1.9649131190536042944400038e-3 : ℝ) (-1.9649131190536042944400025e-3 : ℝ) := h32.weak (by norm_num) (by norm_num)
  have h34 : Bnd ((Real.exp (-(((118558163507453029173019 : ℝ) / 10000000000000000000000000) * qMuM)))) (9.9803701605896650562323708e-1 : ℝ) (9.980370160589665056232371e-1 : ℝ) := Bnd.exp h33 (exp_ge' (-1.9649131190536042944400038e-3 : ℝ) (((9824565595268021472200019 : ℝ) / 5000000000000000000000000000)) (9.9803701605896650562323708e-1 : ℝ) 10 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' (-1.9649131190536042944400025e-3 : ℝ) (((785965247621441717776001 : ℝ) / 400000000000000000000000000)) (9.980370160589665056232371e-1 : ℝ) 10 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h35 := Bnd.mul h28 h34 (by norm_num) (by norm_num)
  have h36 : Bnd (((16 : ℝ) * (Real.exp (-(((118558163507453029173019 : ℝ) / 10000000000000000000000000) * qMuM))))) (1.5968592256943464089971793e1 : ℝ) (1.5968592256943464089971794e1 : ℝ) := h35.weak (by norm_num) (by norm_num)
  have h37 := Bnd.add h27 h36
  have h38 : Bnd (((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((118558163507453029173019 : ℝ) / 10000000000000000000000000) * qMuM)))))) (2.4968592256943464089971793e1 : ℝ) (2.4968592256943464089971794e1 : ℝ) := h37.weak (by norm_num) (by norm_num)
  have h39 : Bnd ((√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((118558163507453029173019 : ℝ) / 10000000000000000000000000) * qMuM))))))) (4.996858238627894483563448 : ℝ) (4.9968582386278944835634482 : ℝ) := Bnd.sqrt h38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h40 := Bnd.add h26 h39
  have h41 : Bnd (((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((118558163507453029173019 : ℝ) / 10000000000000000000000000) * qMuM)))))))) (7.996858238627894483563448 : ℝ) (7.9968582386278944835634482 : ℝ) := h40.weak (by norm_num) (by norm_num)
  have h42 := Bnd.div h25 h41 (by norm_num) (by norm_num)
  have h43 : Bnd (((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((118558163507453029173019 : ℝ) / 10000000000000000000000000) * qMuM))))))))) (2.5009821861530974762071325e-1 : ℝ) (2.5009821861530974762071327e-1 : ℝ) := h42.weak (by norm_num) (by norm_num)
  have h44 := Bnd.mul h24 h43 (by norm_num) (by norm_num)
  have h45 : Bnd (((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((118558163507453029173019 : ℝ) / 10000000000000000000000000) * qMuM)))))))))) (1.000392874461238990482853 : ℝ) (1.0003928744612389904828531 : ℝ) := h44.weak (by norm_num) (by norm_num)
  have h46 : Bnd ((Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((118558163507453029173019 : ℝ) / 10000000000000000000000000) * qMuM))))))))))) (3.92797306275325290565246e-4 : ℝ) (3.92797306275325290565347e-4 : ℝ) := Bnd.log h45 (by norm_num) (le_trans (exp_le' (3.92797306275325290565246e-4 : ℝ) (((196398653137662645282623 : ℝ) / 500000000000000000000000000)) (1.000392874461238990482853 : ℝ) 8 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (by norm_num)) (le_trans (by norm_num) (exp_ge' (3.92797306275325290565347e-4 : ℝ) (((392797306275325290565347 : ℝ) / 1000000000000000000000000000)) (1.0003928744612389904828531 : ℝ) 8 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])))
  have h47 := Bnd.add h23 h46
  have h48 : Bnd (((Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((118558163507453029173019 : ℝ) / 10000000000000000000000000) * qMuP)))))))))) + (Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(((118558163507453029173019 : ℝ) / 10000000000000000000000000) * qMuM)))))))))))) (3.449141278279090726659386e-3 : ℝ) (3.449141278279090726659697e-3 : ℝ) := h47.weak (by norm_num) (by norm_num)
  exact h48

/-- The ends of the light level's interval. -/
noncomputable def sdLo : ℝ := (1.18558163507453026801854e-2 : ℝ)

noncomputable def sdHi : ℝ := (1.18558163507453029173019e-2 : ℝ)

/-- **K⁰ at any light level in `[sdLo, sdHi]`.** -/
theorem J08_of_root (Sd : ℝ) (hSd : Bnd Sd (1.18558163507453026801854e-2 : ℝ) (1.18558163507453029173019e-2 : ℝ)) :
    Bnd (qMp * (√((6 : ℝ) * ((Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qNuP)))))))))) + (Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qNuM)))))))))))))) (4.9761358445093629212535783e2 : ℝ) (4.9761358445093629680365343e2 : ℝ) := by
  have h1 : Bnd (6 : ℝ) (6 : ℝ) (6 : ℝ) := Bnd.const _
  have h2 : Bnd (4 : ℝ) (4 : ℝ) (4 : ℝ) := Bnd.const _
  have h3 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h4 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h5 : Bnd (9 : ℝ) (9 : ℝ) (9 : ℝ) := Bnd.const _
  have h6 : Bnd (16 : ℝ) (16 : ℝ) (16 : ℝ) := Bnd.const _
  have h7 := Bnd.mul hSd qNuP_bnd (by norm_num) (by norm_num)
  have h8 : Bnd ((Sd * qNuP)) (2.4313202602677603117287923e-1 : ℝ) (2.4313202602677603603552341e-1 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 := Bnd.neg h8
  have h10 : Bnd ((-(Sd * qNuP))) (-2.4313202602677603603552341e-1 : ℝ) (-2.4313202602677603117287923e-1 : ℝ) := h9.weak (by norm_num) (by norm_num)
  have h11 : Bnd ((Real.exp (-(Sd * qNuP)))) (7.841679763546468489956323e-1 : ℝ) (7.8416797635464685280876216e-1 : ℝ) := Bnd.exp h10 (exp_ge' (-2.4313202602677603603552341e-1 : ℝ) (((24313202602677603603552341 : ℝ) / 100000000000000000000000000)) (7.841679763546468489956323e-1 : ℝ) 20 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' (-2.4313202602677603117287923e-1 : ℝ) (((24313202602677603117287923 : ℝ) / 100000000000000000000000000)) (7.8416797635464685280876216e-1 : ℝ) 20 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h12 := Bnd.mul h6 h11 (by norm_num) (by norm_num)
  have h13 : Bnd (((16 : ℝ) * (Real.exp (-(Sd * qNuP))))) (1.2546687621674349583930116e1 : ℝ) (1.2546687621674349644940195e1 : ℝ) := h12.weak (by norm_num) (by norm_num)
  have h14 := Bnd.add h5 h13
  have h15 : Bnd (((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qNuP)))))) (2.1546687621674349583930116e1 : ℝ) (2.1546687621674349644940195e1 : ℝ) := h14.weak (by norm_num) (by norm_num)
  have h16 : Bnd ((√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qNuP))))))) (4.6418409733288310470542681 : ℝ) (4.6418409733288310536260228 : ℝ) := Bnd.sqrt h15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h17 := Bnd.add h4 h16
  have h18 : Bnd (((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qNuP)))))))) (7.6418409733288310470542681 : ℝ) (7.6418409733288310536260228 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 := Bnd.div h3 h18 (by norm_num) (by norm_num)
  have h20 : Bnd (((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qNuP))))))))) (2.6171704004052156948380287e-1 : ℝ) (2.6171704004052156970887171e-1 : ℝ) := h19.weak (by norm_num) (by norm_num)
  have h21 := Bnd.mul h2 h20 (by norm_num) (by norm_num)
  have h22 : Bnd (((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qNuP)))))))))) (1.0468681601620862779352114 : ℝ) (1.0468681601620862788354869 : ℝ) := h21.weak (by norm_num) (by norm_num)
  have h23 : Bnd ((Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qNuP))))))))))) (4.58030024334356989812505e-2 : ℝ) (4.58030024334356998412209e-2 : ℝ) := Bnd.log h22 (by norm_num) (le_trans (exp_le' (4.58030024334356989812505e-2 : ℝ) (((91606004866871397962501 : ℝ) / 2000000000000000000000000)) (1.0468681601620862779352114 : ℝ) 15 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (by norm_num)) (le_trans (by norm_num) (exp_ge' (4.58030024334356998412209e-2 : ℝ) (((458030024334356998412209 : ℝ) / 10000000000000000000000000)) (1.0468681601620862788354869 : ℝ) 15 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])))
  have h24 : Bnd (4 : ℝ) (4 : ℝ) (4 : ℝ) := Bnd.const _
  have h25 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h26 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h27 : Bnd (9 : ℝ) (9 : ℝ) (9 : ℝ) := Bnd.const _
  have h28 : Bnd (16 : ℝ) (16 : ℝ) (16 : ℝ) := Bnd.const _
  have h29 := Bnd.mul hSd qNuM_bnd (by norm_num) (by norm_num)
  have h30 : Bnd ((Sd * qNuM)) (5.385475162020902659437227e-3 : ℝ) (5.3854751620209027671469156e-3 : ℝ) := h29.weak (by norm_num) (by norm_num)
  have h31 := Bnd.neg h30
  have h32 : Bnd ((-(Sd * qNuM))) (-5.3854751620209027671469156e-3 : ℝ) (-5.385475162020902659437227e-3 : ℝ) := h31.weak (by norm_num) (by norm_num)
  have h33 : Bnd ((Real.exp (-(Sd * qNuM)))) (9.9462900051155452356950246e-1 : ℝ) (9.9462900051155452367663365e-1 : ℝ) := Bnd.exp h32 (exp_ge' (-5.3854751620209027671469156e-3 : ℝ) (((13463687905052256917867289 : ℝ) / 2500000000000000000000000000)) (9.9462900051155452356950246e-1 : ℝ) 11 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' (-5.385475162020902659437227e-3 : ℝ) (((5385475162020902659437227 : ℝ) / 1000000000000000000000000000)) (9.9462900051155452367663365e-1 : ℝ) 11 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h34 := Bnd.mul h28 h33 (by norm_num) (by norm_num)
  have h35 : Bnd (((16 : ℝ) * (Real.exp (-(Sd * qNuM))))) (1.5914064008184872377112039e1 : ℝ) (1.5914064008184872378826139e1 : ℝ) := h34.weak (by norm_num) (by norm_num)
  have h36 := Bnd.add h27 h35
  have h37 : Bnd (((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qNuM)))))) (2.4914064008184872377112039e1 : ℝ) (2.4914064008184872378826139e1 : ℝ) := h36.weak (by norm_num) (by norm_num)
  have h38 : Bnd ((√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qNuM))))))) (4.991399003103726266671821 : ℝ) (4.9913990031037262668435265 : ℝ) := Bnd.sqrt h37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h39 := Bnd.add h26 h38
  have h40 : Bnd (((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qNuM)))))))) (7.991399003103726266671821 : ℝ) (7.9913990031037262668435265 : ℝ) := h39.weak (by norm_num) (by norm_num)
  have h41 := Bnd.div h25 h40 (by norm_num) (by norm_num)
  have h42 : Bnd (((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qNuM))))))))) (2.50269070437258021068072e-1 : ℝ) (2.5026907043725802107344937e-1 : ℝ) := h41.weak (by norm_num) (by norm_num)
  have h43 := Bnd.mul h24 h42 (by norm_num) (by norm_num)
  have h44 : Bnd (((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qNuM)))))))))) (1.001076281749032084272288 : ℝ) (1.0010762817490320842937975 : ℝ) := h43.weak (by norm_num) (by norm_num)
  have h45 : Bnd ((Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qNuM))))))))))) (1.07570297307720698294755e-3 : ℝ) (1.07570297307720700443394e-3 : ℝ) := Bnd.log h44 (by norm_num) (le_trans (exp_le' (1.07570297307720698294755e-3 : ℝ) (((21514059461544139658951 : ℝ) / 20000000000000000000000000)) (1.001076281749032084272288 : ℝ) 9 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (by norm_num)) (le_trans (by norm_num) (exp_ge' (1.07570297307720700443394e-3 : ℝ) (((53785148653860350221697 : ℝ) / 50000000000000000000000000)) (1.0010762817490320842937975 : ℝ) 9 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])))
  have h46 := Bnd.add h23 h45
  have h47 : Bnd (((Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qNuP)))))))))) + (Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qNuM)))))))))))) (4.687870540651290596419805e-2 : ℝ) (4.687870540651290684565484e-2 : ℝ) := h46.weak (by norm_num) (by norm_num)
  have h48 := Bnd.mul h1 h47 (by norm_num) (by norm_num)
  have h49 : Bnd (((6 : ℝ) * ((Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qNuP)))))))))) + (Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qNuM))))))))))))) (2.812722324390774357851883e-1 : ℝ) (2.8127223243907744107392904e-1 : ℝ) := h48.weak (by norm_num) (by norm_num)
  have h50 : Bnd ((√((6 : ℝ) * ((Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qNuP)))))))))) + (Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qNuM)))))))))))))) (5.3035104642027193400553772e-1 : ℝ) (5.3035104642027193899161325e-1 : ℝ) := Bnd.sqrt h49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h51 := Bnd.mul qMp_bnd h50 (by norm_num) (by norm_num)
  have h52 : Bnd ((qMp * (√((6 : ℝ) * ((Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qNuP)))))))))) + (Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qNuM))))))))))))))) (4.9761358445093629212535783e2 : ℝ) (4.9761358445093629680365343e2 : ℝ) := h51.weak (by norm_num) (by norm_num)
  exact h52

/-- **K± at any light level in `[sdLo, sdHi]`.** -/
theorem J09_of_root (Sd : ℝ) (hSd : Bnd Sd (1.18558163507453026801854e-2 : ℝ) (1.18558163507453029173019e-2 : ℝ)) :
    Bnd (√((((6 : ℝ) * (qMp ^ 2)) * ((Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qKapP)))))))))) + (Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qKapM)))))))))))) + (((48 : ℝ) / 25) * qElec))) (4.9366503266830768281279382e2 : ℝ) (4.9366503266830768740888688e2 : ℝ) := by
  have h1 : Bnd (6 : ℝ) (6 : ℝ) (6 : ℝ) := Bnd.const _
  have h2 := Bnd.pow qMp_bnd (by norm_num) 2
  have h3 : Bnd ((qMp ^ 2)) (8.803545137849416385655721e5 : ℝ) (8.8035451378494163856557241e5 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.mul h1 h3 (by norm_num) (by norm_num)
  have h5 : Bnd (((6 : ℝ) * (qMp ^ 2))) (5.2821270827096498313934326e6 : ℝ) (5.2821270827096498313934345e6 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 : Bnd (4 : ℝ) (4 : ℝ) (4 : ℝ) := Bnd.const _
  have h7 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h8 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h9 : Bnd (9 : ℝ) (9 : ℝ) (9 : ℝ) := Bnd.const _
  have h10 : Bnd (16 : ℝ) (16 : ℝ) (16 : ℝ) := Bnd.const _
  have h11 := Bnd.mul hSd qKapP_bnd (by norm_num) (by norm_num)
  have h12 : Bnd ((Sd * qKapP)) (2.3959804775213024885082803e-1 : ℝ) (2.3959804775213025364279261e-1 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 := Bnd.neg h12
  have h14 : Bnd ((-(Sd * qKapP))) (-2.3959804775213025364279261e-1 : ℝ) (-2.3959804775213024885082803e-1 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 : Bnd ((Real.exp (-(Sd * qKapP)))) (7.8694411145806602772536115e-1 : ℝ) (7.8694411145806603149636946e-1 : ℝ) := Bnd.exp h14 (exp_ge' (-2.3959804775213025364279261e-1 : ℝ) (((23959804775213025364279261 : ℝ) / 100000000000000000000000000)) (7.8694411145806602772536115e-1 : ℝ) 20 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' (-2.3959804775213024885082803e-1 : ℝ) (((23959804775213024885082803 : ℝ) / 100000000000000000000000000)) (7.8694411145806603149636946e-1 : ℝ) 20 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h16 := Bnd.mul h10 h15 (by norm_num) (by norm_num)
  have h17 : Bnd (((16 : ℝ) * (Real.exp (-(Sd * qKapP))))) (1.2591105783329056443605778e1 : ℝ) (1.2591105783329056503941912e1 : ℝ) := h16.weak (by norm_num) (by norm_num)
  have h18 := Bnd.add h9 h17
  have h19 : Bnd (((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qKapP)))))) (2.1591105783329056443605778e1 : ℝ) (2.1591105783329056503941912e1 : ℝ) := h18.weak (by norm_num) (by norm_num)
  have h20 : Bnd ((√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qKapP))))))) (4.6466230515643354092558285 : ℝ) (4.6466230515643354157483 : ℝ) := Bnd.sqrt h19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h21 := Bnd.add h8 h20
  have h22 : Bnd (((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qKapP)))))))) (7.6466230515643354092558285 : ℝ) (7.6466230515643354157483 : ℝ) := h21.weak (by norm_num) (by norm_num)
  have h23 := Bnd.div h7 h22 (by norm_num) (by norm_num)
  have h24 : Bnd (((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qKapP))))))))) (2.6155336630473013914048274e-1 : ℝ) (2.6155336630473013936255827e-1 : ℝ) := h23.weak (by norm_num) (by norm_num)
  have h25 := Bnd.mul h6 h24 (by norm_num) (by norm_num)
  have h26 : Bnd (((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qKapP)))))))))) (1.0462134652189205565619309 : ℝ) (1.0462134652189205574502331 : ℝ) := h25.weak (by norm_num) (by norm_num)
  have h27 : Bnd ((Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qKapP))))))))))) (4.5177422468872395453758e-2 : ℝ) (4.51774224688723963028221e-2 : ℝ) := Bnd.log h26 (by norm_num) (le_trans (exp_le' (4.5177422468872395453758e-2 : ℝ) (((22588711234436197726879 : ℝ) / 500000000000000000000000)) (1.0462134652189205565619309 : ℝ) 15 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (by norm_num)) (le_trans (by norm_num) (exp_ge' (4.51774224688723963028221e-2 : ℝ) (((451774224688723963028221 : ℝ) / 10000000000000000000000000)) (1.0462134652189205574502331 : ℝ) 15 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])))
  have h28 : Bnd (4 : ℝ) (4 : ℝ) (4 : ℝ) := Bnd.const _
  have h29 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h30 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h31 : Bnd (9 : ℝ) (9 : ℝ) (9 : ℝ) := Bnd.const _
  have h32 : Bnd (16 : ℝ) (16 : ℝ) (16 : ℝ) := Bnd.const _
  have h33 := Bnd.mul hSd qKapM_bnd (by norm_num) (by norm_num)
  have h34 : Bnd ((Sd * qKapM)) (2.5109040578854402894963057e-3 : ℝ) (2.5109040578854403397145363e-3 : ℝ) := h33.weak (by norm_num) (by norm_num)
  have h35 := Bnd.neg h34
  have h36 : Bnd ((-(Sd * qKapM))) (-2.5109040578854403397145363e-3 : ℝ) (-2.5109040578854402894963057e-3 : ℝ) := h35.weak (by norm_num) (by norm_num)
  have h37 : Bnd ((Real.exp (-(Sd * qKapM)))) (9.9749224562497318082297519e-1 : ℝ) (9.9749224562497318087306749e-1 : ℝ) := Bnd.exp h36 (exp_ge' (-2.5109040578854403397145363e-3 : ℝ) (((25109040578854403397145363 : ℝ) / 10000000000000000000000000000)) (9.9749224562497318082297519e-1 : ℝ) 10 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' (-2.5109040578854402894963057e-3 : ℝ) (((25109040578854402894963057 : ℝ) / 10000000000000000000000000000)) (9.9749224562497318087306749e-1 : ℝ) 10 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h38 := Bnd.mul h32 h37 (by norm_num) (by norm_num)
  have h39 : Bnd (((16 : ℝ) * (Real.exp (-(Sd * qKapM))))) (1.5959875929999570893167603e1 : ℝ) (1.595987592999957089396908e1 : ℝ) := h38.weak (by norm_num) (by norm_num)
  have h40 := Bnd.add h31 h39
  have h41 : Bnd (((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qKapM)))))) (2.4959875929999570893167603e1 : ℝ) (2.495987592999957089396908e1 : ℝ) := h40.weak (by norm_num) (by norm_num)
  have h42 : Bnd ((√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qKapM))))))) (4.99598598176571857493982 : ℝ) (4.9959859817657185750200322 : ℝ) := Bnd.sqrt h41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h43 := Bnd.add h30 h42
  have h44 : Bnd (((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qKapM)))))))) (7.99598598176571857493982 : ℝ) (7.9959859817657185750200322 : ℝ) := h43.weak (by norm_num) (by norm_num)
  have h45 := Bnd.div h29 h44 (by norm_num) (by norm_num)
  have h46 : Bnd (((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qKapM))))))))) (2.5012550104025429478392239e-1 : ℝ) (2.5012550104025429478643155e-1 : ℝ) := h45.weak (by norm_num) (by norm_num)
  have h47 := Bnd.mul h28 h46 (by norm_num) (by norm_num)
  have h48 : Bnd (((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qKapM)))))))))) (1.0005020041610171791356895 : ℝ) (1.0005020041610171791457262 : ℝ) := h47.weak (by norm_num) (by norm_num)
  have h49 : Bnd ((Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qKapM))))))))))) (5.01878199082187132927393e-4 : ℝ) (5.01878199082187142959058e-4 : ℝ) := Bnd.log h48 (by norm_num) (le_trans (exp_le' (5.01878199082187132927393e-4 : ℝ) (((501878199082187132927393 : ℝ) / 1000000000000000000000000000)) (1.0005020041610171791356895 : ℝ) 8 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (by norm_num)) (le_trans (by norm_num) (exp_ge' (5.01878199082187142959058e-4 : ℝ) (((250939099541093571479529 : ℝ) / 500000000000000000000000000)) (1.0005020041610171791457262 : ℝ) 8 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])))
  have h50 := Bnd.add h27 h49
  have h51 : Bnd (((Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qKapP)))))))))) + (Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qKapM)))))))))))) (4.5679300667954582586685393e-2 : ℝ) (4.5679300667954583445781158e-2 : ℝ) := h50.weak (by norm_num) (by norm_num)
  have h52 := Bnd.mul h5 h51 (by norm_num) (by norm_num)
  have h53 : Bnd ((((6 : ℝ) * (qMp ^ 2)) * ((Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qKapP)))))))))) + (Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qKapM))))))))))))) (2.412838711774398982443204e5 : ℝ) (2.4128387117743990278217351e5 : ℝ) := h52.weak (by norm_num) (by norm_num)
  have h54 : Bnd ((48 : ℝ) / 25) ((48 : ℝ) / 25) ((48 : ℝ) / 25) := Bnd.const _
  have h55 := Bnd.mul h54 qElec_bnd (by norm_num) (by norm_num)
  have h56 : Bnd ((((48 : ℝ) / 25) * qElec)) (2.4212933019613934455621964e3 : ℝ) (2.4212933019613934455699272e3 : ℝ) := h55.weak (by norm_num) (by norm_num)
  have h57 := Bnd.add h53 h56
  have h58 : Bnd (((((6 : ℝ) * (qMp ^ 2)) * ((Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qKapP)))))))))) + (Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qKapM)))))))))))) + (((48 : ℝ) / 25) * qElec))) (2.4370516447940129168988259e5 : ℝ) (2.4370516447940129622774344e5 : ℝ) := h57.weak (by norm_num) (by norm_num)
  have h59 : Bnd ((√((((6 : ℝ) * (qMp ^ 2)) * ((Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qKapP)))))))))) + (Real.log ((4 : ℝ) * ((2 : ℝ) / ((3 : ℝ) + (√((9 : ℝ) + ((16 : ℝ) * (Real.exp (-(Sd * qKapM)))))))))))) + (((48 : ℝ) / 25) * qElec)))) (4.9366503266830768281279382e2 : ℝ) (4.9366503266830768740888688e2 : ℝ) := Bnd.sqrt h58 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h59

end Comparison.Article
