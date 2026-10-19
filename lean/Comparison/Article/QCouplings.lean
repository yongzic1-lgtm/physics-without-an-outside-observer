import Comparison.Article.QBase

/-!
# The couplings and the last-step direction

`x = νh/(M + 1 + N_h)`, `α = c_L f/(1 − x)`, `α_s = (1/72)^{1/2}`, `W_W = F(h)h⁻⁴(1 − 2b + 2bh)`,
`G_F m_p² = (9/10)W_W/M²`, `v = (√2 G_F)^{-1/2}`, the weak angles, `M_W`, `M_Z`, `m_H`, `m_t`.
-/

namespace Comparison.Article

open Real

/-- **The contact** `x = νh/(M + 1 + N_h)`. -/
noncomputable def qX : ℝ :=
  ((((9 : ℝ) / 4000) * qH) / ((297 : ℝ) + qNh))

theorem qX_bnd : Bnd qX (7.5735725447344029743347837e-6 : ℝ) (7.5735725447344029834274633e-6 : ℝ) := by
  unfold qX
  have h1 : Bnd ((9 : ℝ) / 4000) ((9 : ℝ) / 4000) ((9 : ℝ) / 4000) := Bnd.const _
  have h2 := Bnd.mul h1 qH_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((((9 : ℝ) / 4000) * qH)) (2.2499348609917944612340766e-3 : ℝ) (2.2499348609917944612340781e-3 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (297 : ℝ) (297 : ℝ) (297 : ℝ) := Bnd.const _
  have h5 := Bnd.add h4 qNh_bnd
  have h6 : Bnd (((297 : ℝ) + qNh)) (2.97077085840563140591848e2 : ℝ) (2.970770858405631409485126e2 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.div h3 h6 (by norm_num) (by norm_num)
  have h8 : Bnd (((((9 : ℝ) / 4000) * qH) / ((297 : ℝ) + qNh))) (7.5735725447344029743347837e-6 : ℝ) (7.5735725447344029834274633e-6 : ℝ) := h7.weak (by norm_num) (by norm_num)
  exact h8

/-- **The electric coupling** `α = c_L f/(1 − x)`. -/
noncomputable def qAlpha : ℝ :=
  (((27 : ℝ) / 3700) / ((1 : ℝ) - qX))

theorem qAlpha_bnd : Bnd qAlpha (7.29735256432632772636425e-3 : ℝ) (7.2973525643263277263643165e-3 : ℝ) := by
  unfold qAlpha
  have h1 : Bnd ((27 : ℝ) / 3700) ((27 : ℝ) / 3700) ((27 : ℝ) / 3700) := Bnd.const _
  have h2 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h3 := Bnd.sub h2 qX_bnd
  have h4 : Bnd (((1 : ℝ) - qX)) (9.9999242642745526559701657e-1 : ℝ) (9.9999242642745526559702567e-1 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 := Bnd.div h1 h4 (by norm_num) (by norm_num)
  have h6 : Bnd ((((27 : ℝ) / 3700) / ((1 : ℝ) - qX))) (7.29735256432632772636425e-3 : ℝ) (7.2973525643263277263643165e-3 : ℝ) := h5.weak (by norm_num) (by norm_num)
  exact h6

/-- **The strong coupling** `α_s = (1/72)^{1/2}`. -/
noncomputable def qAlphaS : ℝ :=
  (√((1 : ℝ) / 72))

theorem qAlphaS_bnd : Bnd qAlphaS (1.1785113019775792073347406e-1 : ℝ) (1.1785113019775792073347407e-1 : ℝ) := by
  unfold qAlphaS
  have h1 : Bnd ((1 : ℝ) / 72) ((1 : ℝ) / 72) ((1 : ℝ) / 72) := Bnd.const _
  have h2 : Bnd ((√((1 : ℝ) / 72))) (1.1785113019775792073347406e-1 : ℝ) (1.1785113019775792073347407e-1 : ℝ) := Bnd.sqrt h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h2

/-- The first return at the clock's overlap, `F(h) = h⁴(1 + h)/(16 − 8h − 3h² − 3h³)`. -/
noncomputable def qFh : ℝ :=
  (((qH ^ 4) * ((1 : ℝ) + qH)) / ((((16 : ℝ) - ((8 : ℝ) * qH)) - ((3 : ℝ) * (qH ^ 2))) - ((3 : ℝ) * (qH ^ 3))))

theorem qFh_bnd : Bnd qFh (9.9953695516919611005256889e-1 : ℝ) (9.9953695516919611005257884e-1 : ℝ) := by
  unfold qFh
  have h1 := Bnd.pow qH_bnd (by norm_num) 4
  have h2 : Bnd ((qH ^ 4)) (9.9988420234749652018301492e-1 : ℝ) (9.9988420234749652018301737e-1 : ℝ) := h1.weak (by norm_num) (by norm_num)
  have h3 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h4 := Bnd.add h3 qH_bnd
  have h5 : Bnd (((1 : ℝ) + qH)) (1.9999710493296864272151451 : ℝ) (1.9999710493296864272151458 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.mul h2 h5 (by norm_num) (by norm_num)
  have h7 : Bnd (((qH ^ 4) * ((1 : ℝ) + qH))) (1.9997394573770991282950853 : ℝ) (1.999739457377099128295091 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 : Bnd (16 : ℝ) (16 : ℝ) (16 : ℝ) := Bnd.const _
  have h9 : Bnd (8 : ℝ) (8 : ℝ) (8 : ℝ) := Bnd.const _
  have h10 := Bnd.mul h9 qH_bnd (by norm_num) (by norm_num)
  have h11 : Bnd (((8 : ℝ) * qH)) (7.9997683946374914177211615 : ℝ) (7.9997683946374914177211664 : ℝ) := h10.weak (by norm_num) (by norm_num)
  have h12 := Bnd.sub h8 h11
  have h13 : Bnd (((16 : ℝ) - ((8 : ℝ) * qH))) (8.0002316053625085822788336 : ℝ) (8.0002316053625085822788385 : ℝ) := h12.weak (by norm_num) (by norm_num)
  have h14 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h15 := Bnd.pow qH_bnd (by norm_num) 2
  have h16 : Bnd ((qH ^ 2)) (9.999420994975141660354749e-1 : ℝ) (9.9994209949751416603547613e-1 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.mul h14 h16 (by norm_num) (by norm_num)
  have h18 : Bnd (((3 : ℝ) * (qH ^ 2))) (2.9998262984925424981064247 : ℝ) (2.9998262984925424981064284 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 := Bnd.sub h13 h18
  have h20 : Bnd ((((16 : ℝ) - ((8 : ℝ) * qH)) - ((3 : ℝ) * (qH ^ 2)))) (5.0004053068699660841724052 : ℝ) (5.0004053068699660841724138 : ℝ) := h19.weak (by norm_num) (by norm_num)
  have h21 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h22 := Bnd.pow qH_bnd (by norm_num) 3
  have h23 : Bnd ((qH ^ 3)) (9.9991315050345895170820068e-1 : ℝ) (9.9991315050345895170820252e-1 : ℝ) := h22.weak (by norm_num) (by norm_num)
  have h24 := Bnd.mul h21 h23 (by norm_num) (by norm_num)
  have h25 : Bnd (((3 : ℝ) * (qH ^ 3))) (2.999739451510376855124602 : ℝ) (2.9997394515103768551246076 : ℝ) := h24.weak (by norm_num) (by norm_num)
  have h26 := Bnd.sub h20 h25
  have h27 : Bnd (((((16 : ℝ) - ((8 : ℝ) * qH)) - ((3 : ℝ) * (qH ^ 2))) - ((3 : ℝ) * (qH ^ 3)))) (2.0006658553595892290477976 : ℝ) (2.0006658553595892290478118 : ℝ) := h26.weak (by norm_num) (by norm_num)
  have h28 := Bnd.div h7 h27 (by norm_num) (by norm_num)
  have h29 : Bnd ((((qH ^ 4) * ((1 : ℝ) + qH)) / ((((16 : ℝ) - ((8 : ℝ) * qH)) - ((3 : ℝ) * (qH ^ 2))) - ((3 : ℝ) * (qH ^ 3))))) (9.9953695516919611005256889e-1 : ℝ) (9.9953695516919611005257884e-1 : ℝ) := h28.weak (by norm_num) (by norm_num)
  exact h29

/-- **The weak contact's retained excursion** `W_W = F(h) h⁻⁴ (1 − 2b + 2bh)`. -/
noncomputable def qWW : ℝ :=
  ((qFh / (qH ^ 4)) * (((1 : ℝ) - ((7 : ℝ) / 8)) + (((7 : ℝ) / 8) * qH)))

theorem qWW_bnd : Bnd qWW (9.9962738956753779363446632e-1 : ℝ) (9.9962738956753779363447928e-1 : ℝ) := by
  unfold qWW
  have h1 := Bnd.pow qH_bnd (by norm_num) 4
  have h2 : Bnd ((qH ^ 4)) (9.9988420234749652018301492e-1 : ℝ) (9.9988420234749652018301737e-1 : ℝ) := h1.weak (by norm_num) (by norm_num)
  have h3 := Bnd.div qFh_bnd h2 (by norm_num) (by norm_num)
  have h4 : Bnd ((qFh / (qH ^ 4))) (9.9965271260663469411455847e-1 : ℝ) (9.9965271260663469411457088e-1 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h6 : Bnd ((7 : ℝ) / 8) ((7 : ℝ) / 8) ((7 : ℝ) / 8) := Bnd.const _
  have h7 := Bnd.sub h5 h6
  have h8 : Bnd (((1 : ℝ) - ((7 : ℝ) / 8))) (1.25e-1 : ℝ) (1.25e-1 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 : Bnd ((7 : ℝ) / 8) ((7 : ℝ) / 8) ((7 : ℝ) / 8) := Bnd.const _
  have h10 := Bnd.mul h9 qH_bnd (by norm_num) (by norm_num)
  have h11 : Bnd ((((7 : ℝ) / 8) * qH)) (8.7497466816347562381325204e-1 : ℝ) (8.7497466816347562381325258e-1 : ℝ) := h10.weak (by norm_num) (by norm_num)
  have h12 := Bnd.add h8 h11
  have h13 : Bnd ((((1 : ℝ) - ((7 : ℝ) / 8)) + (((7 : ℝ) / 8) * qH))) (9.9997466816347562381325204e-1 : ℝ) (9.9997466816347562381325258e-1 : ℝ) := h12.weak (by norm_num) (by norm_num)
  have h14 := Bnd.mul h4 h13 (by norm_num) (by norm_num)
  have h15 : Bnd (((qFh / (qH ^ 4)) * (((1 : ℝ) - ((7 : ℝ) / 8)) + (((7 : ℝ) / 8) * qH)))) (9.9962738956753779363446632e-1 : ℝ) (9.9962738956753779363447928e-1 : ℝ) := h14.weak (by norm_num) (by norm_num)
  exact h15

/-- **`G_F m_p² = (1 − 1/N₂) W_W/M²`.** -/
noncomputable def qGFmp2 : ℝ :=
  ((((9 : ℝ) / 10) * qWW) / (87616 : ℝ))

theorem qGFmp2_bnd : Bnd qGFmp2 (1.0268268930455442091296334e-5 : ℝ) (1.0268268930455442091296469e-5 : ℝ) := by
  unfold qGFmp2
  have h1 : Bnd ((9 : ℝ) / 10) ((9 : ℝ) / 10) ((9 : ℝ) / 10) := Bnd.const _
  have h2 := Bnd.mul h1 qWW_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((((9 : ℝ) / 10) * qWW)) (8.9966465061078401427101968e-1 : ℝ) (8.9966465061078401427103136e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (87616 : ℝ) (87616 : ℝ) (87616 : ℝ) := Bnd.const _
  have h5 := Bnd.div h3 h4 (by norm_num) (by norm_num)
  have h6 : Bnd (((((9 : ℝ) / 10) * qWW) / (87616 : ℝ))) (1.0268268930455442091296334e-5 : ℝ) (1.0268268930455442091296469e-5 : ℝ) := h5.weak (by norm_num) (by norm_num)
  exact h6

/-- `G_F` in GeV⁻². -/
noncomputable def qGF : ℝ :=
  (qGFmp2 / ((qMp / (1000 : ℝ)) ^ 2))

theorem qGF_bnd : Bnd qGF (1.1663788587064412272608604e-5 : ℝ) (1.1663788587064412272608763e-5 : ℝ) := by
  unfold qGF
  have h1 : Bnd (1000 : ℝ) (1000 : ℝ) (1000 : ℝ) := Bnd.const _
  have h2 := Bnd.div qMp_bnd h1 (by norm_num) (by norm_num)
  have h3 : Bnd ((qMp / (1000 : ℝ))) (9.3827208942019672472054469e-1 : ℝ) (9.3827208942019672472054485e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.pow h3 (by norm_num) 2
  have h5 : Bnd (((qMp / (1000 : ℝ)) ^ 2)) (8.803545137849416385655721e-1 : ℝ) (8.8035451378494163856557241e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.div qGFmp2_bnd h5 (by norm_num) (by norm_num)
  have h7 : Bnd ((qGFmp2 / ((qMp / (1000 : ℝ)) ^ 2))) (1.1663788587064412272608604e-5 : ℝ) (1.1663788587064412272608763e-5 : ℝ) := h6.weak (by norm_num) (by norm_num)
  exact h7

/-- **The electroweak scale** `v = (√2 G_F)^{-1/2}` in GeV. -/
noncomputable def qV : ℝ :=
  (((√(2 : ℝ)) * qGF) ^ (-((1 : ℝ) / 2)))

theorem qV_bnd : Bnd qV (2.4621963404287102263672166e2 : ℝ) (2.4621963404287102263672337e2 : ℝ) := by
  unfold qV
  have h1 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h2 : Bnd ((√(2 : ℝ))) (1.4142135623730950488016887 : ℝ) (1.4142135623730950488016888 : ℝ) := Bnd.sqrt h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 := Bnd.mul h2 qGF_bnd (by norm_num) (by norm_num)
  have h4 : Bnd (((√(2 : ℝ)) * qGF)) (1.6495088008479011375585705e-5 : ℝ) (1.6495088008479011375585932e-5 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 : Bnd ((((√(2 : ℝ)) * qGF) ^ (-((1 : ℝ) / 2)))) ((4.0614145329526523689848247e-3 : ℝ))⁻¹ ((4.0614145329526523689847966e-3 : ℝ))⁻¹ := Bnd.rpow_neg' (p := 1) (q := 2) h4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h6 : Bnd ((((√(2 : ℝ)) * qGF) ^ (-((1 : ℝ) / 2)))) (2.4621963404287102263672166e2 : ℝ) (2.4621963404287102263672337e2 : ℝ) := h5.weak (by norm_num) (by norm_num)
  exact h6

/-- **The MS-bar weak angle** `ŝ² = 3N_h`. -/
noncomputable def qSw : ℝ :=
  ((3 : ℝ) * qNh)

theorem qSw_bnd : Bnd qSw (2.31257521689421775544e-1 : ℝ) (2.312575216894228455378e-1 : ℝ) := by
  unfold qSw
  have h1 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qNh_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((3 : ℝ) * qNh)) (2.31257521689421775544e-1 : ℝ) (2.312575216894228455378e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  exact h3

/-- **The on-shell weak angle** `s² = 3N_h/(1 + f)`. -/
noncomputable def qOsw : ℝ :=
  (qSw / ((259 : ℝ) / 250))

theorem qOsw_bnd : Bnd qOsw (2.232215460322604011042471e-1 : ℝ) (2.2322154603226143391679537e-1 : ℝ) := by
  unfold qOsw
  have h1 : Bnd ((259 : ℝ) / 250) ((259 : ℝ) / 250) ((259 : ℝ) / 250) := Bnd.const _
  have h2 := Bnd.div qSw_bnd h1 (by norm_num) (by norm_num)
  have h3 : Bnd ((qSw / ((259 : ℝ) / 250))) (2.232215460322604011042471e-1 : ℝ) (2.2322154603226143391679537e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  exact h3

/-- **The W mass** `M_W = v [πα/((1 − f)s²)]^{1/2}` in GeV. -/
noncomputable def qMw : ℝ :=
  (qV * (√((π * qAlpha) / (((241 : ℝ) / 250) * qOsw))))

theorem qMw_bnd : Bnd qMw (8.036625104033244980113877e1 : ℝ) (8.0366251040332635722550764e1 : ℝ) := by
  unfold qMw
  have h1 := Bnd.mul bnd_pi qAlpha_bnd (by norm_num) (by norm_num)
  have h2 : Bnd ((π * qAlpha)) (2.2925309206742230280714532e-2 : ℝ) (2.2925309206742230280787715e-2 : ℝ) := h1.weak (by norm_num) (by norm_num)
  have h3 : Bnd ((241 : ℝ) / 250) ((241 : ℝ) / 250) ((241 : ℝ) / 250) := Bnd.const _
  have h4 := Bnd.mul h3 qOsw_bnd (by norm_num) (by norm_num)
  have h5 : Bnd ((((241 : ℝ) / 250) * qOsw)) (2.151855703750990266644942e-1 : ℝ) (2.1518557037510002229579074e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.div h2 h5 (by norm_num) (by norm_num)
  have h7 : Bnd (((π * qAlpha) / (((241 : ℝ) / 250) * qOsw))) (1.0653739080543389881701131e-1 : ℝ) (1.0653739080543439174984848e-1 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 : Bnd ((√((π * qAlpha) / (((241 : ℝ) / 250) * qOsw)))) (3.2640065993412742917350736e-1 : ℝ) (3.2640065993412818427742975e-1 : ℝ) := Bnd.sqrt h7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h9 := Bnd.mul qV_bnd h8 (by norm_num) (by norm_num)
  have h10 : Bnd ((qV * (√((π * qAlpha) / (((241 : ℝ) / 250) * qOsw))))) (8.036625104033244980113877e1 : ℝ) (8.0366251040332635722550764e1 : ℝ) := h9.weak (by norm_num) (by norm_num)
  exact h10

/-- **The Z mass** `M_Z = M_W/(1 − s²)^{1/2}` in GeV. -/
noncomputable def qMz : ℝ :=
  (qMw / (√((1 : ℝ) - qOsw)))

theorem qMz_bnd : Bnd qMz (9.1185361518345607148409049e1 : ℝ) (9.1185361518345878719530501e1 : ℝ) := by
  unfold qMz
  have h1 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h2 := Bnd.sub h1 qOsw_bnd
  have h3 : Bnd (((1 : ℝ) - qOsw)) (7.7677845396773856608320463e-1 : ℝ) (7.767784539677395988957529e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd ((√((1 : ℝ) - qOsw))) (8.8135035823884395019792923e-1 : ℝ) (8.8135035823884453612413816e-1 : ℝ) := Bnd.sqrt h3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h5 := Bnd.div qMw_bnd h4 (by norm_num) (by norm_num)
  have h6 : Bnd ((qMw / (√((1 : ℝ) - qOsw)))) (9.1185361518345607148409049e1 : ℝ) (9.1185361518345878719530501e1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  exact h6

/-- **The scalar mass** `m_H = v (2πα/χ_h)^{1/2}` in GeV. -/
noncomputable def qMh : ℝ :=
  (qV * (√((((2 : ℝ) * π) * qAlpha) / ((30 : ℝ) / 169))))

theorem qMh_bnd : Bnd qMh (1.2513477159340231894515854e2 : ℝ) (1.2513477159340231894535915e2 : ℝ) := by
  unfold qMh
  have h1 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 bnd_pi (by norm_num) (by norm_num)
  have h3 : Bnd (((2 : ℝ) * π)) (6.28318530717958647692 : ℝ) (6.28318530717958647694 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.mul h3 qAlpha_bnd (by norm_num) (by norm_num)
  have h5 : Bnd ((((2 : ℝ) * π) * qAlpha)) (4.5850618413484460561429064e-2 : ℝ) (4.585061841348446056157543e-2 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 : Bnd ((30 : ℝ) / 169) ((30 : ℝ) / 169) ((30 : ℝ) / 169) := Bnd.const _
  have h7 := Bnd.div h5 h6 (by norm_num) (by norm_num)
  have h8 : Bnd (((((2 : ℝ) * π) * qAlpha) / ((30 : ℝ) / 169))) (2.5829181706262912782938372e-1 : ℝ) (2.5829181706262912783020826e-1 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 : Bnd ((√((((2 : ℝ) * π) * qAlpha) / ((30 : ℝ) / 169)))) (5.0822417992715491008719549e-1 : ℝ) (5.0822417992715491008800669e-1 : ℝ) := Bnd.sqrt h8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h10 := Bnd.mul qV_bnd h9 (by norm_num) (by norm_num)
  have h11 : Bnd ((qV * (√((((2 : ℝ) * π) * qAlpha) / ((30 : ℝ) / 169))))) (1.2513477159340231894515854e2 : ℝ) (1.2513477159340231894535915e2 : ℝ) := h10.weak (by norm_num) (by norm_num)
  exact h11

/-- **The top mass** `m_t = v (η/2σ)^{1/2}` in GeV. -/
noncomputable def qMt : ℝ :=
  (qV * (√((59 : ℝ) / 120)))

theorem qMt_bnd : Bnd qMt (1.7264661361444158874927995e2 : ℝ) (1.7264661361444158874928116e2 : ℝ) := by
  unfold qMt
  have h1 : Bnd ((59 : ℝ) / 120) ((59 : ℝ) / 120) ((59 : ℝ) / 120) := Bnd.const _
  have h2 : Bnd ((√((59 : ℝ) / 120))) (7.0118946559875431906849879e-1 : ℝ) (7.011894655987543190684988e-1 : ℝ) := Bnd.sqrt h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 := Bnd.mul qV_bnd h2 (by norm_num) (by norm_num)
  have h4 : Bnd ((qV * (√((59 : ℝ) / 120)))) (1.7264661361444158874927995e2 : ℝ) (1.7264661361444158874928116e2 : ℝ) := h3.weak (by norm_num) (by norm_num)
  exact h4

end Comparison.Article
