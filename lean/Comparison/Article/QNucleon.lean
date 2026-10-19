import Comparison.Article.RowsCouplings

/-!
# The nucleon at rest, the pions, the deuteron and the nuclei

Propositions 70, 120, 121, 124, 125: `ε₂ = α²/(1 + α/N₂)`, `S_μ = 1 − ε₂/(Eℓ² b)`, `μ_p`, `μ_n`, `g_A`,
`m_π⁰² = 38 h m_e m_p`, `Δ_el`, `m_π±`, `f_π`, `B_d`, `m_d`, `μ_d`, the incidence polynomial `B(A, Z)`, the
cluster nuclei with their Thomas–Fermi atomic term, and the bulk coefficients.
-/

namespace Comparison.Article

open Real

/-- The proton's length `λ_p = ħ/m_p c` in fm. -/
noncomputable def qLp : ℝ :=
  (qHc / qMp)

theorem qLp_bnd : Bnd qLp (2.1030891005320243593703339e-1 : ℝ) (2.1030891005320243593770288e-1 : ℝ) := by
  unfold qLp
  have h1 := Bnd.div qHc_bnd qMp_bnd (by norm_num) (by norm_num)
  have h2 : Bnd ((qHc / qMp)) (2.1030891005320243593703339e-1 : ℝ) (2.1030891005320243593770288e-1 : ℝ) := h1.weak (by norm_num) (by norm_num)
  exact h2

/-- **`ε₂ = α²/(1 + α/N₂)`.** -/
noncomputable def qEps2 : ℝ :=
  ((qAlpha ^ 2) / ((1 : ℝ) + (qAlpha / (10 : ℝ))))

theorem qEps2_bnd : Bnd qEps2 (5.321252339367591947007307e-5 : ℝ) (5.3212523393675919470074046e-5 : ℝ) := by
  unfold qEps2
  have h1 := Bnd.pow qAlpha_bnd (by norm_num) 2
  have h2 : Bnd ((qAlpha ^ 2)) (5.325135444808003103748339e-5 : ℝ) (5.3251354448080031037484361e-5 : ℝ) := h1.weak (by norm_num) (by norm_num)
  have h3 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h4 : Bnd (10 : ℝ) (10 : ℝ) (10 : ℝ) := Bnd.const _
  have h5 := Bnd.div qAlpha_bnd h4 (by norm_num) (by norm_num)
  have h6 : Bnd ((qAlpha / (10 : ℝ))) (7.29735256432632772636425e-4 : ℝ) (7.2973525643263277263643165e-4 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.add h3 h6
  have h8 : Bnd (((1 : ℝ) + (qAlpha / (10 : ℝ)))) (1.0007297352564326327726364 : ℝ) (1.0007297352564326327726365 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 := Bnd.div h2 h8 (by norm_num) (by norm_num)
  have h10 : Bnd (((qAlpha ^ 2) / ((1 : ℝ) + (qAlpha / (10 : ℝ))))) (5.321252339367591947007307e-5 : ℝ) (5.3212523393675919470074046e-5 : ℝ) := h9.weak (by norm_num) (by norm_num)
  exact h10

/-- **`S_μ = 1 − ε₂/(Eℓ² b)`.** -/
noncomputable def qSmu : ℝ :=
  ((1 : ℝ) - (qEps2 / (112 : ℝ)))

theorem qSmu_bnd : Bnd qSmu (9.999995248881839850364333e-1 : ℝ) (9.9999952488818398503643331e-1 : ℝ) := by
  unfold qSmu
  have h1 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h2 : Bnd (112 : ℝ) (112 : ℝ) (112 : ℝ) := Bnd.const _
  have h3 := Bnd.div qEps2_bnd h2 (by norm_num) (by norm_num)
  have h4 : Bnd ((qEps2 / (112 : ℝ))) (4.7511181601496356669708098e-7 : ℝ) (4.751118160149635666970897e-7 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 := Bnd.sub h1 h4
  have h6 : Bnd (((1 : ℝ) - (qEps2 / (112 : ℝ)))) (9.999995248881839850364333e-1 : ℝ) (9.9999952488818398503643331e-1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  exact h6

/-- **`μ_p = [(Var ℓ/2N₂) S_μ]^{1/2}`** in nuclear magnetons. -/
noncomputable def qMup : ℝ :=
  (√(((39 : ℝ) / 5) * qSmu))

theorem qMup_bnd : Bnd qMup (2.7928473452961647834347469 : ℝ) (2.7928473452961647834347471 : ℝ) := by
  unfold qMup
  have h1 : Bnd ((39 : ℝ) / 5) ((39 : ℝ) / 5) ((39 : ℝ) / 5) := Bnd.const _
  have h2 := Bnd.mul h1 qSmu_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((((39 : ℝ) / 5) * qSmu)) (7.7999962941278350832841797 : ℝ) (7.7999962941278350832841799 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd ((√(((39 : ℝ) / 5) * qSmu))) (2.7928473452961647834347469 : ℝ) (2.7928473452961647834347471 : ℝ) := Bnd.sqrt h3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h4

/-- **`μ_n = −(4(1 + E_P)/23) S_μ^{1/2}`** in nuclear magnetons. -/
noncomputable def qMun : ℝ :=
  (-(((44 : ℝ) / 23) * (√qSmu)))

theorem qMun_bnd : Bnd qMun (-1.9130430238060350499434417 : ℝ) (-1.9130430238060350499434416 : ℝ) := by
  unfold qMun
  have h1 : Bnd ((44 : ℝ) / 23) ((44 : ℝ) / 23) ((44 : ℝ) / 23) := Bnd.const _
  have h2 : Bnd ((√qSmu)) (9.9999976244406377610679904e-1 : ℝ) (9.9999976244406377610679905e-1 : ℝ) := Bnd.sqrt qSmu_bnd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 := Bnd.mul h1 h2 (by norm_num) (by norm_num)
  have h4 : Bnd ((((44 : ℝ) / 23) * (√qSmu))) (1.9130430238060350499434416 : ℝ) (1.9130430238060350499434417 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 := Bnd.neg h4
  have h6 : Bnd ((-(((44 : ℝ) / 23) * (√qSmu)))) (-1.9130430238060350499434417 : ℝ) (-1.9130430238060350499434416 : ℝ) := h5.weak (by norm_num) (by norm_num)
  exact h6

/-- **`g_A = (5/3)(2/5)^{2b/3} = (5/3)(2/5)^{7/24}`.** -/
noncomputable def qGA : ℝ :=
  (((5 : ℝ) / 3) * (((2 : ℝ) / 5) ^ (7 / 24 : ℝ)))

theorem qGA_bnd : Bnd qGA (1.2758009281154655816747105 : ℝ) (1.2758009281154655816747106 : ℝ) := by
  unfold qGA
  have h1 : Bnd ((5 : ℝ) / 3) ((5 : ℝ) / 3) ((5 : ℝ) / 3) := Bnd.const _
  have h2 : Bnd ((2 : ℝ) / 5) ((2 : ℝ) / 5) ((2 : ℝ) / 5) := Bnd.const _
  have h3 : Bnd ((((2 : ℝ) / 5) ^ (7 / 24 : ℝ))) (7.6548055686927934900482631e-1 : ℝ) (7.6548055686927934900482632e-1 : ℝ) := Bnd.rpow' (p := 7) (q := 24) h2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h4 := Bnd.mul h1 h3 (by norm_num) (by norm_num)
  have h5 : Bnd ((((5 : ℝ) / 3) * (((2 : ℝ) / 5) ^ (7 / 24 : ℝ)))) (1.2758009281154655816747105 : ℝ) (1.2758009281154655816747106 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- **`m_π⁰ = (38 h m_e m_p)^{1/2}`** in MeV. -/
noncomputable def qPi0 : ℝ :=
  (√((((38 : ℝ) * qH) * qMe) * qMp))

theorem qPi0_bnd : Bnd qPi0 (1.349770445597686281871865e2 : ℝ) (1.3497704455976862818718656e2 : ℝ) := by
  unfold qPi0
  have h1 : Bnd (38 : ℝ) (38 : ℝ) (38 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qH_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((38 : ℝ) * qH)) (3.7998899874528084234175517e1 : ℝ) (3.7998899874528084234175541e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.mul h3 qMe_bnd (by norm_num) (by norm_num)
  have h5 : Bnd ((((38 : ℝ) * qH) * qMe)) (1.9417397963258223702599621e1 : ℝ) (1.9417397963258223702599634e1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.mul h5 qMp_bnd (by norm_num) (by norm_num)
  have h7 : Bnd (((((38 : ℝ) * qH) * qMe) * qMp)) (1.8218802558089765826623942e4 : ℝ) (1.8218802558089765826623958e4 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 : Bnd ((√((((38 : ℝ) * qH) * qMe) * qMp))) (1.349770445597686281871865e2 : ℝ) (1.3497704455976862818718656e2 : ℝ) := Bnd.sqrt h7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h8

/-- **The plane contact `Δ_el = πα m_p²/(Eℓ(1 − αbΦ(i)))`**, `Φ(i) = −1/13`, in MeV². -/
noncomputable def qElec : ℝ :=
  (((π * qAlpha) * (qMp ^ 2)) / ((16 : ℝ) * ((1 : ℝ) + ((qAlpha * ((7 : ℝ) / 16)) * ((1 : ℝ) / 13)))))

theorem qElec_bnd : Bnd qElec (1.2610902614382257528969773e3 : ℝ) (1.2610902614382257529010037e3 : ℝ) := by
  unfold qElec
  have h1 := Bnd.mul bnd_pi qAlpha_bnd (by norm_num) (by norm_num)
  have h2 : Bnd ((π * qAlpha)) (2.2925309206742230280714532e-2 : ℝ) (2.2925309206742230280787715e-2 : ℝ) := h1.weak (by norm_num) (by norm_num)
  have h3 := Bnd.pow qMp_bnd (by norm_num) 2
  have h4 : Bnd ((qMp ^ 2)) (8.803545137849416385655721e5 : ℝ) (8.8035451378494163856557241e5 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 := Bnd.mul h2 h4 (by norm_num) (by norm_num)
  have h6 : Bnd (((π * qAlpha) * (qMp ^ 2))) (2.0182399440071002228674937e4 : ℝ) (2.0182399440071002228739372e4 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 : Bnd (16 : ℝ) (16 : ℝ) (16 : ℝ) := Bnd.const _
  have h8 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h9 : Bnd ((7 : ℝ) / 16) ((7 : ℝ) / 16) ((7 : ℝ) / 16) := Bnd.const _
  have h10 := Bnd.mul qAlpha_bnd h9 (by norm_num) (by norm_num)
  have h11 : Bnd ((qAlpha * ((7 : ℝ) / 16))) (3.1925917468927683802843593e-3 : ℝ) (3.1925917468927683802843885e-3 : ℝ) := h10.weak (by norm_num) (by norm_num)
  have h12 : Bnd ((1 : ℝ) / 13) ((1 : ℝ) / 13) ((1 : ℝ) / 13) := Bnd.const _
  have h13 := Bnd.mul h11 h12 (by norm_num) (by norm_num)
  have h14 : Bnd (((qAlpha * ((7 : ℝ) / 16)) * ((1 : ℝ) / 13))) (2.455839805302129523295661e-4 : ℝ) (2.4558398053021295232956835e-4 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 := Bnd.add h8 h14
  have h16 : Bnd (((1 : ℝ) + ((qAlpha * ((7 : ℝ) / 16)) * ((1 : ℝ) / 13)))) (1.0002455839805302129523295 : ℝ) (1.0002455839805302129523296 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.mul h7 h16 (by norm_num) (by norm_num)
  have h18 : Bnd (((16 : ℝ) * ((1 : ℝ) + ((qAlpha * ((7 : ℝ) / 16)) * ((1 : ℝ) / 13))))) (1.6003929343688483407237272e1 : ℝ) (1.6003929343688483407237274e1 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 := Bnd.div h6 h18 (by norm_num) (by norm_num)
  have h20 : Bnd ((((π * qAlpha) * (qMp ^ 2)) / ((16 : ℝ) * ((1 : ℝ) + ((qAlpha * ((7 : ℝ) / 16)) * ((1 : ℝ) / 13)))))) (1.2610902614382257528969773e3 : ℝ) (1.2610902614382257529010037e3 : ℝ) := h19.weak (by norm_num) (by norm_num)
  exact h20

/-- **`m_π± = (m_π⁰² + Δ_el)^{1/2}`** in MeV. -/
noncomputable def qPip : ℝ :=
  (√((qPi0 ^ 2) + qElec))

theorem qPip_bnd : Bnd qPip (1.3957038661380855965663077e2 : ℝ) (1.3957038661380855965664527e2 : ℝ) := by
  unfold qPip
  have h1 := Bnd.pow qPi0_bnd (by norm_num) 2
  have h2 : Bnd ((qPi0 ^ 2)) (1.8218802558089765826623941e4 : ℝ) (1.8218802558089765826623959e4 : ℝ) := h1.weak (by norm_num) (by norm_num)
  have h3 := Bnd.add h2 qElec_bnd
  have h4 : Bnd (((qPi0 ^ 2) + qElec)) (1.9479892819527991579520918e4 : ℝ) (1.9479892819527991579524963e4 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 : Bnd ((√((qPi0 ^ 2) + qElec))) (1.3957038661380855965663077e2 : ℝ) (1.3957038661380855965664527e2 : ℝ) := Bnd.sqrt h4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h5

/-- **`f_π = η m_p (2k_C)^{1/2}/(2π μ_p)`** in MeV. -/
noncomputable def qFpi : ℝ :=
  (((((295 : ℝ) / 296) * qMp) * (√(6 : ℝ))) / (((2 : ℝ) * π) * qMup))

theorem qFpi_bnd : Bnd qFpi (1.3052919547815715965795752e2 : ℝ) (1.3052919547815715965837307e2 : ℝ) := by
  unfold qFpi
  have h1 : Bnd ((295 : ℝ) / 296) ((295 : ℝ) / 296) ((295 : ℝ) / 296) := Bnd.const _
  have h2 := Bnd.mul h1 qMp_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((((295 : ℝ) / 296) * qMp)) (9.3510225128026362767756987e2 : ℝ) (9.3510225128026362767757004e2 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (6 : ℝ) (6 : ℝ) (6 : ℝ) := Bnd.const _
  have h5 : Bnd ((√(6 : ℝ))) (2.449489742783178098197284 : ℝ) (2.4494897427831780981972841 : ℝ) := Bnd.sqrt h4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h6 := Bnd.mul h3 h5 (by norm_num) (by norm_num)
  have h7 : Bnd (((((295 : ℝ) / 296) * qMp) * (√(6 : ℝ)))) (2.2905233729644637258295903e3 : ℝ) (2.2905233729644637258295909e3 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h9 := Bnd.mul h8 bnd_pi (by norm_num) (by norm_num)
  have h10 : Bnd (((2 : ℝ) * π)) (6.28318530717958647692 : ℝ) (6.28318530717958647694 : ℝ) := h9.weak (by norm_num) (by norm_num)
  have h11 := Bnd.mul h10 qMup_bnd (by norm_num) (by norm_num)
  have h12 : Bnd ((((2 : ℝ) * π) * qMup)) (1.7547977405160375746045151e1 : ℝ) (1.754797740516037574610101e1 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 := Bnd.div h7 h12 (by norm_num) (by norm_num)
  have h14 : Bnd ((((((295 : ℝ) / 296) * qMp) * (√(6 : ℝ))) / (((2 : ℝ) * π) * qMup))) (1.3052919547815715965795752e2 : ℝ) (1.3052919547815715965837307e2 : ℝ) := h13.weak (by norm_num) (by norm_num)
  exact h14

/-- **The deuteron's binding `B_d = m_p χ_A^{1/2} a³ [1 − (1 + t/Eℓ) ε₂]`** in MeV. -/
noncomputable def qBd : ℝ :=
  (((qMp * (√((13 : ℝ) / 12))) * ((125 : ℝ) / 54872)) * ((1 : ℝ) - (((41 : ℝ) / 40) * qEps2)))

theorem qBd_bnd : Bnd qBd (2.2245664630991941695357564 : ℝ) (2.2245664630991941695357572 : ℝ) := by
  unfold qBd
  have h1 : Bnd ((13 : ℝ) / 12) ((13 : ℝ) / 12) ((13 : ℝ) / 12) := Bnd.const _
  have h2 : Bnd ((√((13 : ℝ) / 12))) (1.0408329997330663676411488 : ℝ) (1.0408329997330663676411489 : ℝ) := Bnd.sqrt h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 := Bnd.mul qMp_bnd h2 (by norm_num) (by norm_num)
  have h4 : Bnd ((qMp * (√((13 : ℝ) / 12)))) (9.7658455339703524061119674e2 : ℝ) (9.7658455339703524061119701e2 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 : Bnd ((125 : ℝ) / 54872) ((125 : ℝ) / 54872) ((125 : ℝ) / 54872) := Bnd.const _
  have h6 := Bnd.mul h4 h5 (by norm_num) (by norm_num)
  have h7 : Bnd (((qMp * (√((13 : ℝ) / 12))) * ((125 : ℝ) / 54872))) (2.2246878038822970745808352 : ℝ) (2.2246878038822970745808359 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h9 : Bnd ((41 : ℝ) / 40) ((41 : ℝ) / 40) ((41 : ℝ) / 40) := Bnd.const _
  have h10 := Bnd.mul h9 qEps2_bnd (by norm_num) (by norm_num)
  have h11 : Bnd ((((41 : ℝ) / 40) * qEps2)) (5.4542836478517817456824896e-5 : ℝ) (5.4542836478517817456825898e-5 : ℝ) := h10.weak (by norm_num) (by norm_num)
  have h12 := Bnd.sub h8 h11
  have h13 : Bnd (((1 : ℝ) - (((41 : ℝ) / 40) * qEps2))) (9.9994545716352148218254317e-1 : ℝ) (9.9994545716352148218254318e-1 : ℝ) := h12.weak (by norm_num) (by norm_num)
  have h14 := Bnd.mul h7 h13 (by norm_num) (by norm_num)
  have h15 : Bnd ((((qMp * (√((13 : ℝ) / 12))) * ((125 : ℝ) / 54872)) * ((1 : ℝ) - (((41 : ℝ) / 40) * qEps2)))) (2.2245664630991941695357564 : ℝ) (2.2245664630991941695357572 : ℝ) := h14.weak (by norm_num) (by norm_num)
  exact h15

/-- The deuteron's mass `m_p + m_n − B_d` in MeV. -/
noncomputable def qMd : ℝ :=
  ((qMp + qMn) - qBd)

theorem qMd_bnd : Bnd qMd (1.8756129449822875338176001e3 : ℝ) (1.8756129449822875338176007e3 : ℝ) := by
  unfold qMd
  have h1 := Bnd.add qMp_bnd qMn_bnd
  have h2 : Bnd ((qMp + qMn)) (1.8778375114453867279871359e3 : ℝ) (1.8778375114453867279871364e3 : ℝ) := h1.weak (by norm_num) (by norm_num)
  have h3 := Bnd.sub h2 qBd_bnd
  have h4 : Bnd (((qMp + qMn) - qBd)) (1.8756129449822875338176001e3 : ℝ) (1.8756129449822875338176007e3 : ℝ) := h3.weak (by norm_num) (by norm_num)
  exact h4

/-- `μ_S = μ_p + μ_n`. -/
noncomputable def qMus : ℝ :=
  (qMup + qMun)

theorem qMus_bnd : Bnd qMus (8.798043214901297334913052e-1 : ℝ) (8.798043214901297334913055e-1 : ℝ) := by
  unfold qMus
  have h1 := Bnd.add qMup_bnd qMun_bnd
  have h2 : Bnd ((qMup + qMun)) (8.798043214901297334913052e-1 : ℝ) (8.798043214901297334913055e-1 : ℝ) := h1.weak (by norm_num) (by norm_num)
  exact h2

/-- `g_l = m_n/(m_p + m_n)`. -/
noncomputable def qGl : ℝ :=
  (qMn / (qMp + qMn))

theorem qGl_bnd : Bnd qGl (5.0034436754967094835973278e-1 : ℝ) (5.0034436754967094835973306e-1 : ℝ) := by
  unfold qGl
  have h1 := Bnd.add qMp_bnd qMn_bnd
  have h2 : Bnd ((qMp + qMn)) (1.8778375114453867279871359e3 : ℝ) (1.8778375114453867279871364e3 : ℝ) := h1.weak (by norm_num) (by norm_num)
  have h3 := Bnd.div qMn_bnd h2 (by norm_num) (by norm_num)
  have h4 : Bnd ((qMn / (qMp + qMn))) (5.0034436754967094835973278e-1 : ℝ) (5.0034436754967094835973306e-1 : ℝ) := h3.weak (by norm_num) (by norm_num)
  exact h4

/-- `u_B = B_d/m_p`. -/
noncomputable def qUB : ℝ :=
  (qBd / qMp)

theorem qUB_bnd : Bnd qUB (2.3709182956447743881740958e-3 : ℝ) (2.3709182956447743881740971e-3 : ℝ) := by
  unfold qUB
  have h1 := Bnd.div qBd_bnd qMp_bnd (by norm_num) (by norm_num)
  have h2 : Bnd ((qBd / qMp)) (2.3709182956447743881740958e-3 : ℝ) (2.3709182956447743881740971e-3 : ℝ) := h1.weak (by norm_num) (by norm_num)
  exact h2

/-- **The deuteron's moment `μ_d = (16μ_S + g_l)/17 − u_B(μ_S − g_l)/(20 + 13u_B)`.** -/
noncomputable def qMud : ℝ :=
  (((((16 : ℝ) * qMus) + qGl) / (17 : ℝ)) - ((qUB * (qMus - qGl)) / ((20 : ℝ) + ((13 : ℝ) * qUB))))

theorem qMud_bnd : Bnd qMud (8.57438233518712951668911e-1 : ℝ) (8.5743823351871295166891143e-1 : ℝ) := by
  unfold qMud
  have h1 : Bnd (16 : ℝ) (16 : ℝ) (16 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qMus_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((16 : ℝ) * qMus)) (1.4076869143842075735860883e1 : ℝ) (1.4076869143842075735860888e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.add h3 qGl_bnd
  have h5 : Bnd ((((16 : ℝ) * qMus) + qGl)) (1.4577213511391746684220615e1 : ℝ) (1.4577213511391746684220622e1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 : Bnd (17 : ℝ) (17 : ℝ) (17 : ℝ) := Bnd.const _
  have h7 := Bnd.div h5 h6 (by norm_num) (by norm_num)
  have h8 : Bnd (((((16 : ℝ) * qMus) + qGl) / (17 : ℝ))) (8.5748314772892627554238911e-1 : ℝ) (8.5748314772892627554238953e-1 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 := Bnd.sub qMus_bnd qGl_bnd
  have h10 : Bnd ((qMus - qGl)) (3.7945995394045878513157214e-1 : ℝ) (3.7945995394045878513157272e-1 : ℝ) := h9.weak (by norm_num) (by norm_num)
  have h11 := Bnd.mul qUB_bnd h10 (by norm_num) (by norm_num)
  have h12 : Bnd ((qUB * (qMus - qGl))) (8.9966854726195713400044825e-4 : ℝ) (8.9966854726195713400045013e-4 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 : Bnd (20 : ℝ) (20 : ℝ) (20 : ℝ) := Bnd.const _
  have h14 : Bnd (13 : ℝ) (13 : ℝ) (13 : ℝ) := Bnd.const _
  have h15 := Bnd.mul h14 qUB_bnd (by norm_num) (by norm_num)
  have h16 : Bnd (((13 : ℝ) * qUB)) (3.0821937843382067046263245e-2 : ℝ) (3.0821937843382067046263263e-2 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.add h13 h16
  have h18 : Bnd (((20 : ℝ) + ((13 : ℝ) * qUB))) (2.0030821937843382067046263e1 : ℝ) (2.0030821937843382067046264e1 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 := Bnd.div h12 h18 (by norm_num) (by norm_num)
  have h20 : Bnd (((qUB * (qMus - qGl)) / ((20 : ℝ) + ((13 : ℝ) * qUB)))) (4.4914210213323873478102334e-5 : ℝ) (4.4914210213323873478102432e-5 : ℝ) := h19.weak (by norm_num) (by norm_num)
  have h21 := Bnd.sub h8 h20
  have h22 : Bnd ((((((16 : ℝ) * qMus) + qGl) / (17 : ℝ)) - ((qUB * (qMus - qGl)) / ((20 : ℝ) + ((13 : ℝ) * qUB))))) (8.57438233518712951668911e-1 : ℝ) (8.5743823351871295166891143e-1 : ℝ) := h21.weak (by norm_num) (by norm_num)
  exact h22

/-- The Coulomb pair `α m_p/(Var P − Cov²/Var Q) = α m_p/9` in MeV. -/
noncomputable def qCoul : ℝ :=
  ((qAlpha * qMp) / (9 : ℝ))

theorem qCoul_bnd : Bnd qCoul (7.6076691530736600446393288e-1 : ℝ) (7.6076691530736600446393997e-1 : ℝ) := by
  unfold qCoul
  have h1 := Bnd.mul qAlpha_bnd qMp_bnd (by norm_num) (by norm_num)
  have h2 : Bnd ((qAlpha * qMp)) (6.846902237766294040175396 : ℝ) (6.8469022377662940401754597 : ℝ) := h1.weak (by norm_num) (by norm_num)
  have h3 : Bnd (9 : ℝ) (9 : ℝ) (9 : ℝ) := Bnd.const _
  have h4 := Bnd.div h2 h3 (by norm_num) (by norm_num)
  have h5 : Bnd (((qAlpha * qMp) / (9 : ℝ))) (7.6076691530736600446393288e-1 : ℝ) (7.6076691530736600446393997e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- **The triton `B(3, 1) = B_d [3 + τ₃]`** in MeV. -/
noncomputable def qBt : ℝ :=
  (qBd * ((61 : ℝ) / 16))

theorem qBt_bnd : Bnd qBt (8.4811596405656777713550712 : ℝ) (8.4811596405656777713550744 : ℝ) := by
  unfold qBt
  have h1 : Bnd ((61 : ℝ) / 16) ((61 : ℝ) / 16) ((61 : ℝ) / 16) := Bnd.const _
  have h2 := Bnd.mul qBd_bnd h1 (by norm_num) (by norm_num)
  have h3 : Bnd ((qBd * ((61 : ℝ) / 16))) (8.4811596405656777713550712 : ℝ) (8.4811596405656777713550744 : ℝ) := h2.weak (by norm_num) (by norm_num)
  exact h3

/-- **The helion `B(3, 2) = B_d [3 + τ₃] − α m_p/9`** in MeV. -/
noncomputable def qBh : ℝ :=
  ((qBd * ((61 : ℝ) / 16)) - qCoul)

theorem qBh_bnd : Bnd qBh (7.7203927252583117668911312 : ℝ) (7.7203927252583117668911416 : ℝ) := by
  unfold qBh
  have h1 : Bnd ((61 : ℝ) / 16) ((61 : ℝ) / 16) ((61 : ℝ) / 16) := Bnd.const _
  have h2 := Bnd.mul qBd_bnd h1 (by norm_num) (by norm_num)
  have h3 : Bnd ((qBd * ((61 : ℝ) / 16))) (8.4811596405656777713550712 : ℝ) (8.4811596405656777713550744 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.sub h3 qCoul_bnd
  have h5 : Bnd (((qBd * ((61 : ℝ) / 16)) - qCoul)) (7.7203927252583117668911312 : ℝ) (7.7203927252583117668911416 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- **The alpha `B(4, 2) = B_d [6 + 4τ₃ + (3 + τ₃)] − α m_p/9`** in MeV. -/
noncomputable def qBa : ℝ :=
  ((qBd * ((209 : ℝ) / 16)) - qCoul)

theorem qBa_bnd : Bnd qBa (2.8297632508925857835096877e1 : ℝ) (2.8297632508925857835096897e1 : ℝ) := by
  unfold qBa
  have h1 : Bnd ((209 : ℝ) / 16) ((209 : ℝ) / 16) ((209 : ℝ) / 16) := Bnd.const _
  have h2 := Bnd.mul qBd_bnd h1 (by norm_num) (by norm_num)
  have h3 : Bnd ((qBd * ((209 : ℝ) / 16))) (2.9058399424233223839560817e1 : ℝ) (2.9058399424233223839560829e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.sub h3 qCoul_bnd
  have h5 : Bnd (((qBd * ((209 : ℝ) / 16)) - qCoul)) (2.8297632508925857835096877e1 : ℝ) (2.8297632508925857835096897e1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- The Thomas–Fermi coefficient `3·1.588071/(3.5 (3π/4)^{2/3})`. -/
noncomputable def qCTF : ℝ :=
  (((4764213 : ℝ) / 3500000) / ((((3 : ℝ) / 4) * π) ^ (2 / 3 : ℝ)))

theorem qCTF_bnd : Bnd qCTF (7.6874511326806523737431051e-1 : ℝ) (7.6874511326806523737594189e-1 : ℝ) := by
  unfold qCTF
  have h1 : Bnd ((4764213 : ℝ) / 3500000) ((4764213 : ℝ) / 3500000) ((4764213 : ℝ) / 3500000) := Bnd.const _
  have h2 : Bnd ((3 : ℝ) / 4) ((3 : ℝ) / 4) ((3 : ℝ) / 4) := Bnd.const _
  have h3 := Bnd.mul h2 bnd_pi (by norm_num) (by norm_num)
  have h4 : Bnd ((((3 : ℝ) / 4) * π)) (2.356194490192344928845 : ℝ) (2.3561944901923449288525 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 : Bnd (((((3 : ℝ) / 4) * π) ^ (2 / 3 : ℝ))) (1.7706827540002271116170703 : ℝ) (1.7706827540002271116208279 : ℝ) := Bnd.rpow' (p := 2) (q := 3) h4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h6 := Bnd.div h1 h5 (by norm_num) (by norm_num)
  have h7 : Bnd ((((4764213 : ℝ) / 3500000) / ((((3 : ℝ) / 4) * π) ^ (2 / 3 : ℝ)))) (7.6874511326806523737431051e-1 : ℝ) (7.6874511326806523737594189e-1 : ℝ) := h6.weak (by norm_num) (by norm_num)
  exact h7

/-- Row G01, proton charge radius [fm]. -/
noncomputable def rowG01 : ℝ :=
  ((4 : ℝ) * qLp)

theorem rowG01_bnd : Bnd rowG01 (8.4123564021280974374813356e-1 : ℝ) (8.4123564021280974375081152e-1 : ℝ) := by
  unfold rowG01
  have h1 : Bnd (4 : ℝ) (4 : ℝ) (4 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qLp_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((4 : ℝ) * qLp)) (8.4123564021280974374813356e-1 : ℝ) (8.4123564021280974375081152e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  exact h3

/-- **Row G01 to its printed digits, `0.841235640213`.** -/
theorem rowG01_digits : (8.412356402125e-1 : ℝ) < rowG01 ∧ rowG01 < (8.412356402135e-1 : ℝ) :=
  rowG01_bnd.strict (by norm_num) (by norm_num)

/-- Row G02, `Delta` mass [MeV]. -/
noncomputable def rowG02 : ℝ :=
  (((21 : ℝ) / 16) * qMp)

theorem rowG02_bnd : Bnd rowG02 (1.2314821173640082011957149e3 : ℝ) (1.2314821173640082011957152e3 : ℝ) := by
  unfold rowG02
  have h1 : Bnd ((21 : ℝ) / 16) ((21 : ℝ) / 16) ((21 : ℝ) / 16) := Bnd.const _
  have h2 := Bnd.mul h1 qMp_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((((21 : ℝ) / 16) * qMp)) (1.2314821173640082011957149e3 : ℝ) (1.2314821173640082011957152e3 : ℝ) := h2.weak (by norm_num) (by norm_num)
  exact h3

/-- **Row G02 to its printed digits, `1231.48211736`.** -/
theorem rowG02_digits : (1.231482117355e3 : ℝ) < rowG02 ∧ rowG02 < (1.231482117365e3 : ℝ) :=
  rowG02_bnd.strict (by norm_num) (by norm_num)

/-- Row G03, proton moment `mu_p` [`mu_N`]. -/
noncomputable def rowG03 : ℝ :=
  qMup

theorem rowG03_bnd : Bnd rowG03 (2.7928473452961647834347469 : ℝ) (2.7928473452961647834347471 : ℝ) := by
  unfold rowG03
  exact qMup_bnd

/-- **Row G03 to its printed digits, `2.7928473453`.** -/
theorem rowG03_digits : (2.79284734525 : ℝ) < rowG03 ∧ rowG03 < (2.79284734535 : ℝ) :=
  rowG03_bnd.strict (by norm_num) (by norm_num)

/-- Row G04, neutron moment `mu_n` [`mu_N`]. -/
noncomputable def rowG04 : ℝ :=
  qMun

theorem rowG04_bnd : Bnd rowG04 (-1.9130430238060350499434417 : ℝ) (-1.9130430238060350499434416 : ℝ) := by
  unfold rowG04
  exact qMun_bnd

/-- **Row G04 to its printed digits, `-1.91304302381`.** -/
theorem rowG04_digits : (-1.913043023815 : ℝ) < rowG04 ∧ rowG04 < (-1.913043023805 : ℝ) :=
  rowG04_bnd.strict (by norm_num) (by norm_num)

/-- Row G05, moment ratio `mu_n/mu_p`. -/
noncomputable def rowG05 : ℝ :=
  (qMun / qMup)

theorem rowG05_bnd : Bnd rowG05 (-6.8497944473337058135439545e-1 : ℝ) (-6.8497944473337058135439535e-1 : ℝ) := by
  unfold rowG05
  have h1 := Bnd.div_negnum qMun_bnd qMup_bnd (by norm_num) (by norm_num)
  have h2 : Bnd ((qMun / qMup)) (-6.8497944473337058135439545e-1 : ℝ) (-6.8497944473337058135439535e-1 : ℝ) := h1.weak (by norm_num) (by norm_num)
  exact h2

/-- **Row G05 to its printed digits, `-0.684979444733`.** -/
theorem rowG05_digits : (-6.849794447335e-1 : ℝ) < rowG05 ∧ rowG05 < (-6.849794447325e-1 : ℝ) :=
  rowG05_bnd.strict (by norm_num) (by norm_num)

/-- Row G06, neutral pion mass [MeV]. -/
noncomputable def rowG06 : ℝ :=
  qPi0

theorem rowG06_bnd : Bnd rowG06 (1.349770445597686281871865e2 : ℝ) (1.3497704455976862818718656e2 : ℝ) := by
  unfold rowG06
  exact qPi0_bnd

/-- **Row G06 to its printed digits, `134.97704456`.** -/
theorem rowG06_digits : (1.34977044555e2 : ℝ) < rowG06 ∧ rowG06 < (1.34977044565e2 : ℝ) :=
  rowG06_bnd.strict (by norm_num) (by norm_num)

/-- Row G07, charged pion mass [MeV]. -/
noncomputable def rowG07 : ℝ :=
  qPip

theorem rowG07_bnd : Bnd rowG07 (1.3957038661380855965663077e2 : ℝ) (1.3957038661380855965664527e2 : ℝ) := by
  unfold rowG07
  exact qPip_bnd

/-- **Row G07 to its printed digits, `139.570386614`.** -/
theorem rowG07_digits : (1.395703866135e2 : ℝ) < rowG07 ∧ rowG07 < (1.395703866145e2 : ℝ) :=
  rowG07_bnd.strict (by norm_num) (by norm_num)

/-- Row G08, pion decay constant `f_pi` [MeV]. -/
noncomputable def rowG08 : ℝ :=
  qFpi

theorem rowG08_bnd : Bnd rowG08 (1.3052919547815715965795752e2 : ℝ) (1.3052919547815715965837307e2 : ℝ) := by
  unfold rowG08
  exact qFpi_bnd

/-- **Row G08 to its printed digits, `130.529195478`.** -/
theorem rowG08_digits : (1.305291954775e2 : ℝ) < rowG08 ∧ rowG08 < (1.305291954785e2 : ℝ) :=
  rowG08_bnd.strict (by norm_num) (by norm_num)

/-- Row G10, deuteron binding `m_p+m_n-m_d` [MeV]. -/
noncomputable def rowG10 : ℝ :=
  qBd

theorem rowG10_bnd : Bnd rowG10 (2.2245664630991941695357564 : ℝ) (2.2245664630991941695357572 : ℝ) := by
  unfold rowG10
  exact qBd_bnd

/-- **Row G10 to its printed digits, `2.2245664631`.** -/
theorem rowG10_digits : (2.22456646305 : ℝ) < rowG10 ∧ rowG10 < (2.22456646315 : ℝ) :=
  rowG10_bnd.strict (by norm_num) (by norm_num)

/-- Row G11, deuteron mass [MeV]. -/
noncomputable def rowG11 : ℝ :=
  qMd

theorem rowG11_bnd : Bnd rowG11 (1.8756129449822875338176001e3 : ℝ) (1.8756129449822875338176007e3 : ℝ) := by
  unfold rowG11
  exact qMd_bnd

/-- **Row G11 to its printed digits, `1875.61294498`.** -/
theorem rowG11_digits : (1.875612944975e3 : ℝ) < rowG11 ∧ rowG11 < (1.875612944985e3 : ℝ) :=
  rowG11_bnd.strict (by norm_num) (by norm_num)

/-- Row G12, deuteron/proton `m_d/m_p`. -/
noncomputable def rowG12 : ℝ :=
  (qMd / qMp)

theorem rowG12_bnd : Bnd rowG12 (1.9990075012689747921219219 : ℝ) (1.999007501268974792121923 : ℝ) := by
  unfold rowG12
  have h1 := Bnd.div qMd_bnd qMp_bnd (by norm_num) (by norm_num)
  have h2 : Bnd ((qMd / qMp)) (1.9990075012689747921219219 : ℝ) (1.999007501268974792121923 : ℝ) := h1.weak (by norm_num) (by norm_num)
  exact h2

/-- **Row G12 to its printed digits, `1.99900750127`.** -/
theorem rowG12_digits : (1.999007501265 : ℝ) < rowG12 ∧ rowG12 < (1.999007501275 : ℝ) :=
  rowG12_bnd.strict (by norm_num) (by norm_num)

/-- Row G13, deuteron moment `mu_d` [`mu_N`]. -/
noncomputable def rowG13 : ℝ :=
  qMud

theorem rowG13_bnd : Bnd rowG13 (8.57438233518712951668911e-1 : ℝ) (8.5743823351871295166891143e-1 : ℝ) := by
  unfold rowG13
  exact qMud_bnd

/-- **Row G13 to its printed digits, `0.857438233519`.** -/
theorem rowG13_digits : (8.574382335185e-1 : ℝ) < rowG13 ∧ rowG13 < (8.574382335195e-1 : ℝ) :=
  rowG13_bnd.strict (by norm_num) (by norm_num)

/-- Row J03, `Lambda` [MeV]. -/
noncomputable def rowJ03 : ℝ :=
  (qMn * (((5 : ℝ) / 2) ^ (3 / 16 : ℝ)))

theorem rowJ03_bnd : Bnd rowJ03 (1.1156829009076869889335957e3 : ℝ) (1.1156829009076869889335962e3 : ℝ) := by
  unfold rowJ03
  have h1 : Bnd ((5 : ℝ) / 2) ((5 : ℝ) / 2) ((5 : ℝ) / 2) := Bnd.const _
  have h2 : Bnd ((((5 : ℝ) / 2) ^ (3 / 16 : ℝ))) (1.1874456794108960178297575 : ℝ) (1.1874456794108960178297576 : ℝ) := Bnd.rpow' (p := 3) (q := 16) h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 := Bnd.mul qMn_bnd h2 (by norm_num) (by norm_num)
  have h4 : Bnd ((qMn * (((5 : ℝ) / 2) ^ (3 / 16 : ℝ)))) (1.1156829009076869889335957e3 : ℝ) (1.1156829009076869889335962e3 : ℝ) := h3.weak (by norm_num) (by norm_num)
  exact h4

/-- **Row J03 to its printed digits, `1115.68290091`.** -/
theorem rowJ03_digits : (1.115682900905e3 : ℝ) < rowJ03 ∧ rowJ03 < (1.115682900915e3 : ℝ) :=
  rowJ03_bnd.strict (by norm_num) (by norm_num)

/-- Row J04, `Delta`, Breit--Wigner [MeV]. -/
noncomputable def rowJ04 : ℝ :=
  (((21 : ℝ) / 16) * qMp)

theorem rowJ04_bnd : Bnd rowJ04 (1.2314821173640082011957149e3 : ℝ) (1.2314821173640082011957152e3 : ℝ) := by
  unfold rowJ04
  have h1 : Bnd ((21 : ℝ) / 16) ((21 : ℝ) / 16) ((21 : ℝ) / 16) := Bnd.const _
  have h2 := Bnd.mul h1 qMp_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((((21 : ℝ) / 16) * qMp)) (1.2314821173640082011957149e3 : ℝ) (1.2314821173640082011957152e3 : ℝ) := h2.weak (by norm_num) (by norm_num)
  exact h3

/-- **Row J04 to its printed digits, `1231.48211736`.** -/
theorem rowJ04_digits : (1.231482117355e3 : ℝ) < rowJ04 ∧ rowJ04 < (1.231482117365e3 : ℝ) :=
  rowJ04_bnd.strict (by norm_num) (by norm_num)

/-- Row J05, `pi^0` [MeV]. -/
noncomputable def rowJ05 : ℝ :=
  qPi0

theorem rowJ05_bnd : Bnd rowJ05 (1.349770445597686281871865e2 : ℝ) (1.3497704455976862818718656e2 : ℝ) := by
  unfold rowJ05
  exact qPi0_bnd

/-- **Row J05 to its printed digits, `134.97704456`.** -/
theorem rowJ05_digits : (1.34977044555e2 : ℝ) < rowJ05 ∧ rowJ05 < (1.34977044565e2 : ℝ) :=
  rowJ05_bnd.strict (by norm_num) (by norm_num)

/-- Row J06, `pi^pm` [MeV]. -/
noncomputable def rowJ06 : ℝ :=
  qPip

theorem rowJ06_bnd : Bnd rowJ06 (1.3957038661380855965663077e2 : ℝ) (1.3957038661380855965664527e2 : ℝ) := by
  unfold rowJ06
  exact qPip_bnd

/-- **Row J06 to its printed digits, `139.570386614`.** -/
theorem rowJ06_digits : (1.395703866135e2 : ℝ) < rowJ06 ∧ rowJ06 < (1.395703866145e2 : ℝ) :=
  rowJ06_bnd.strict (by norm_num) (by norm_num)

/-- Row J07, `rho` pole, `{rm Re},s` [GeV`^2`]. -/
noncomputable def rowJ07 : ℝ :=
  ((((6 : ℝ) * (qMp ^ 2)) * (Real.log (((√(313 : ℝ)) - (11 : ℝ)) / (6 : ℝ)))) / (1000000 : ℝ))

theorem rowJ07_bnd : Bnd rowJ07 (5.7640855549429342808959105e-1 : ℝ) (5.7640855549429342808959655e-1 : ℝ) := by
  unfold rowJ07
  have h1 : Bnd (6 : ℝ) (6 : ℝ) (6 : ℝ) := Bnd.const _
  have h2 := Bnd.pow qMp_bnd (by norm_num) 2
  have h3 : Bnd ((qMp ^ 2)) (8.803545137849416385655721e5 : ℝ) (8.8035451378494163856557241e5 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.mul h1 h3 (by norm_num) (by norm_num)
  have h5 : Bnd (((6 : ℝ) * (qMp ^ 2))) (5.2821270827096498313934326e6 : ℝ) (5.2821270827096498313934345e6 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 : Bnd (313 : ℝ) (313 : ℝ) (313 : ℝ) := Bnd.const _
  have h7 : Bnd ((√(313 : ℝ))) (1.7691806012954132546790035e1 : ℝ) (1.7691806012954132546790036e1 : ℝ) := Bnd.sqrt h6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h8 : Bnd (11 : ℝ) (11 : ℝ) (11 : ℝ) := Bnd.const _
  have h9 := Bnd.sub h7 h8
  have h10 : Bnd (((√(313 : ℝ)) - (11 : ℝ))) (6.691806012954132546790035 : ℝ) (6.691806012954132546790036 : ℝ) := h9.weak (by norm_num) (by norm_num)
  have h11 : Bnd (6 : ℝ) (6 : ℝ) (6 : ℝ) := Bnd.const _
  have h12 := Bnd.div h10 h11 (by norm_num) (by norm_num)
  have h13 : Bnd ((((√(313 : ℝ)) - (11 : ℝ)) / (6 : ℝ))) (1.1153010021590220911316725 : ℝ) (1.1153010021590220911316727 : ℝ) := h12.weak (by norm_num) (by norm_num)
  have h14 : Bnd ((Real.log (((√(313 : ℝ)) - (11 : ℝ)) / (6 : ℝ)))) (1.09124325573515871885913e-1 : ℝ) (1.09124325573515871885914e-1 : ℝ) := Bnd.log h13 (by norm_num) (le_trans (exp_le' (1.09124325573515871885913e-1 : ℝ) (((109124325573515871885913 : ℝ) / 1000000000000000000000000)) (1.1153010021590220911316721 : ℝ) 17 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (by norm_num)) (le_trans (by norm_num) (exp_ge' (1.09124325573515871885914e-1 : ℝ) (((54562162786757935942957 : ℝ) / 500000000000000000000000)) (1.1153010021590220911316731 : ℝ) 17 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])))
  have h15 := Bnd.mul h5 h14 (by norm_num) (by norm_num)
  have h16 : Bnd ((((6 : ℝ) * (qMp ^ 2)) * (Real.log (((√(313 : ℝ)) - (11 : ℝ)) / (6 : ℝ))))) (5.7640855549429342808959105e5 : ℝ) (5.7640855549429342808959655e5 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 : Bnd (1000000 : ℝ) (1000000 : ℝ) (1000000 : ℝ) := Bnd.const _
  have h18 := Bnd.div h16 h17 (by norm_num) (by norm_num)
  have h19 : Bnd (((((6 : ℝ) * (qMp ^ 2)) * (Real.log (((√(313 : ℝ)) - (11 : ℝ)) / (6 : ℝ)))) / (1000000 : ℝ))) (5.7640855549429342808959105e-1 : ℝ) (5.7640855549429342808959655e-1 : ℝ) := h18.weak (by norm_num) (by norm_num)
  exact h19

/-- **Row J07 to its printed digits, `0.576408555494`.** -/
theorem rowJ07_digits : (5.764085554935e-1 : ℝ) < rowJ07 ∧ rowJ07 < (5.764085554945e-1 : ℝ) :=
  rowJ07_bnd.strict (by norm_num) (by norm_num)

/-- Row J17, `kT_c`, colour stops binding [MeV]. -/
noncomputable def rowJ17 : ℝ :=
  (qMp / (6 : ℝ))

theorem rowJ17_bnd : Bnd rowJ17 (1.5637868157003278745342411e2 : ℝ) (1.5637868157003278745342415e2 : ℝ) := by
  unfold rowJ17
  have h1 : Bnd (6 : ℝ) (6 : ℝ) (6 : ℝ) := Bnd.const _
  have h2 := Bnd.div qMp_bnd h1 (by norm_num) (by norm_num)
  have h3 : Bnd ((qMp / (6 : ℝ))) (1.5637868157003278745342411e2 : ℝ) (1.5637868157003278745342415e2 : ℝ) := h2.weak (by norm_num) (by norm_num)
  exact h3

/-- **Row J17 to its printed digits, `156.37868157`.** -/
theorem rowJ17_digits : (1.56378681565e2 : ℝ) < rowJ17 ∧ rowJ17 < (1.56378681575e2 : ℝ) :=
  rowJ17_bnd.strict (by norm_num) (by norm_num)

/-- Row J18, `Delta`, pole [MeV]. -/
noncomputable def rowJ18 : ℝ :=
  (((21 : ℝ) / 16) * qMp)

theorem rowJ18_bnd : Bnd rowJ18 (1.2314821173640082011957149e3 : ℝ) (1.2314821173640082011957152e3 : ℝ) := by
  unfold rowJ18
  have h1 : Bnd ((21 : ℝ) / 16) ((21 : ℝ) / 16) ((21 : ℝ) / 16) := Bnd.const _
  have h2 := Bnd.mul h1 qMp_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((((21 : ℝ) / 16) * qMp)) (1.2314821173640082011957149e3 : ℝ) (1.2314821173640082011957152e3 : ℝ) := h2.weak (by norm_num) (by norm_num)
  exact h3

/-- **Row J18 to its printed digits, `1231.48211736`.** -/
theorem rowJ18_digits : (1.231482117355e3 : ℝ) < rowJ18 ∧ rowJ18 < (1.231482117365e3 : ℝ) :=
  rowJ18_bnd.strict (by norm_num) (by norm_num)

/-- Row L13, completed deuteron binding [MeV]. -/
noncomputable def rowL13 : ℝ :=
  qBd

theorem rowL13_bnd : Bnd rowL13 (2.2245664630991941695357564 : ℝ) (2.2245664630991941695357572 : ℝ) := by
  unfold rowL13
  exact qBd_bnd

/-- **Row L13 to its printed digits, `2.2245664631`.** -/
theorem rowL13_digits : (2.22456646305 : ℝ) < rowL13 ∧ rowL13 < (2.22456646315 : ℝ) :=
  rowL13_bnd.strict (by norm_num) (by norm_num)

/-- Row M1, proton mass [MeV]. -/
noncomputable def rowM1 : ℝ :=
  qMp

theorem rowM1_bnd : Bnd rowM1 (9.3827208942019672472054469e2 : ℝ) (9.3827208942019672472054485e2 : ℝ) := by
  unfold rowM1
  exact qMp_bnd

/-- **Row M1 to its printed digits, `938.27208942`.** -/
theorem rowM1_digits : (9.38272089415e2 : ℝ) < rowM1 ∧ rowM1 < (9.38272089425e2 : ℝ) :=
  rowM1_bnd.strict (by norm_num) (by norm_num)

/-- Row M2, neutron mass [MeV]. -/
noncomputable def rowM2 : ℝ :=
  qMn

theorem rowM2_bnd : Bnd rowM2 (9.3956542202519000326659123e2 : ℝ) (9.3956542202519000326659149e2 : ℝ) := by
  unfold rowM2
  exact qMn_bnd

/-- **Row M2 to its printed digits, `939.565422025`.** -/
theorem rowM2_digits : (9.395654220245e2 : ℝ) < rowM2 ∧ rowM2 < (9.395654220255e2 : ℝ) :=
  rowM2_bnd.strict (by norm_num) (by norm_num)

/-- Row M3, deuteron nuclear mass [MeV]. -/
noncomputable def rowM3 : ℝ :=
  qMd

theorem rowM3_bnd : Bnd rowM3 (1.8756129449822875338176001e3 : ℝ) (1.8756129449822875338176007e3 : ℝ) := by
  unfold rowM3
  exact qMd_bnd

/-- **Row M3 to its printed digits, `1875.61294498`.** -/
theorem rowM3_digits : (1.875612944975e3 : ℝ) < rowM3 ∧ rowM3 < (1.875612944985e3 : ℝ) :=
  rowM3_bnd.strict (by norm_num) (by norm_num)

/-- Row M4, triton nuclear mass [MeV]. -/
noncomputable def rowM4 : ℝ :=
  ((qMp + ((2 : ℝ) * qMn)) - qBt)

theorem rowM4_bnd : Bnd rowM4 (2.8089217738300110534823719e3 : ℝ) (2.8089217738300110534823729e3 : ℝ) := by
  unfold rowM4
  have h1 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qMn_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((2 : ℝ) * qMn)) (1.8791308440503800065331824e3 : ℝ) (1.879130844050380006533183e3 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.add qMp_bnd h3
  have h5 : Bnd ((qMp + ((2 : ℝ) * qMn))) (2.817402933470576731253727e3 : ℝ) (2.8174029334705767312537279e3 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.sub h5 qBt_bnd
  have h7 : Bnd (((qMp + ((2 : ℝ) * qMn)) - qBt)) (2.8089217738300110534823719e3 : ℝ) (2.8089217738300110534823729e3 : ℝ) := h6.weak (by norm_num) (by norm_num)
  exact h7

/-- **Row M4 to its printed digits, `2808.92177383`.** -/
theorem rowM4_digits : (2.808921773825e3 : ℝ) < rowM4 ∧ rowM4 < (2.808921773835e3 : ℝ) :=
  rowM4_bnd.strict (by norm_num) (by norm_num)

/-- Row M5, helion nuclear mass [MeV]. -/
noncomputable def rowM5 : ℝ :=
  ((((2 : ℝ) * qMp) + qMn) - qBh)

theorem rowM5_bnd : Bnd rowM5 (2.8083892081403251409407893e3 : ℝ) (2.8083892081403251409407901e3 : ℝ) := by
  unfold rowM5
  have h1 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qMp_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((2 : ℝ) * qMp)) (1.8765441788403934494410893e3 : ℝ) (1.8765441788403934494410897e3 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.add h3 qMn_bnd
  have h5 : Bnd ((((2 : ℝ) * qMp) + qMn)) (2.8161096008655834527076805e3 : ℝ) (2.8161096008655834527076812e3 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.sub h5 qBh_bnd
  have h7 : Bnd (((((2 : ℝ) * qMp) + qMn) - qBh)) (2.8083892081403251409407893e3 : ℝ) (2.8083892081403251409407901e3 : ℝ) := h6.weak (by norm_num) (by norm_num)
  exact h7

/-- **Row M5 to its printed digits, `2808.38920814`.** -/
theorem rowM5_digits : (2.808389208135e3 : ℝ) < rowM5 ∧ rowM5 < (2.808389208145e3 : ℝ) :=
  rowM5_bnd.strict (by norm_num) (by norm_num)

/-- Row M6, alpha nuclear mass [MeV]. -/
noncomputable def rowM6 : ℝ :=
  ((((2 : ℝ) * qMp) + ((2 : ℝ) * qMn)) - qBa)

theorem rowM6_bnd : Bnd rowM6 (3.7273773903818475981391748e3 : ℝ) (3.7273773903818475981391759e3 : ℝ) := by
  unfold rowM6
  have h1 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qMp_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((2 : ℝ) * qMp)) (1.8765441788403934494410893e3 : ℝ) (1.8765441788403934494410897e3 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h5 := Bnd.mul h4 qMn_bnd (by norm_num) (by norm_num)
  have h6 : Bnd (((2 : ℝ) * qMn)) (1.8791308440503800065331824e3 : ℝ) (1.879130844050380006533183e3 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.add h3 h6
  have h8 : Bnd ((((2 : ℝ) * qMp) + ((2 : ℝ) * qMn))) (3.7556750228907734559742717e3 : ℝ) (3.7556750228907734559742727e3 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 := Bnd.sub h8 qBa_bnd
  have h10 : Bnd (((((2 : ℝ) * qMp) + ((2 : ℝ) * qMn)) - qBa)) (3.7273773903818475981391748e3 : ℝ) (3.7273773903818475981391759e3 : ℝ) := h9.weak (by norm_num) (by norm_num)
  exact h10

/-- **Row M6 to its printed digits, `3727.37739038`.** -/
theorem rowM6_digits : (3.727377390375e3 : ℝ) < rowM6 ∧ rowM6 < (3.727377390385e3 : ℝ) :=
  rowM6_bnd.strict (by norm_num) (by norm_num)

/-- Row N01, triton binding [MeV]. -/
noncomputable def rowN01 : ℝ :=
  qBt

theorem rowN01_bnd : Bnd rowN01 (8.4811596405656777713550712 : ℝ) (8.4811596405656777713550744 : ℝ) := by
  unfold rowN01
  exact qBt_bnd

/-- **Row N01 to its printed digits, `8.48115964057`.** -/
theorem rowN01_digits : (8.481159640565 : ℝ) < rowN01 ∧ rowN01 < (8.481159640575 : ℝ) :=
  rowN01_bnd.strict (by norm_num) (by norm_num)

/-- Row N02, helion binding [MeV]. -/
noncomputable def rowN02 : ℝ :=
  qBh

theorem rowN02_bnd : Bnd rowN02 (7.7203927252583117668911312 : ℝ) (7.7203927252583117668911416 : ℝ) := by
  unfold rowN02
  exact qBh_bnd

/-- **Row N02 to its printed digits, `7.72039272526`.** -/
theorem rowN02_digits : (7.720392725255 : ℝ) < rowN02 ∧ rowN02 < (7.720392725265 : ℝ) :=
  rowN02_bnd.strict (by norm_num) (by norm_num)

/-- Row N03, helium-4 binding [MeV]. -/
noncomputable def rowN03 : ℝ :=
  qBa

theorem rowN03_bnd : Bnd rowN03 (2.8297632508925857835096877e1 : ℝ) (2.8297632508925857835096897e1 : ℝ) := by
  unfold rowN03
  exact qBa_bnd

/-- **Row N03 to its printed digits, `28.2976325089`.** -/
theorem rowN03_digits : (2.829763250885e1 : ℝ) < rowN03 ∧ rowN03 < (2.829763250895e1 : ℝ) :=
  rowN03_bnd.strict (by norm_num) (by norm_num)

/-- Row N04, beryllium-8 binding, atomic [MeV]. -/
noncomputable def rowN04 : ℝ :=
  ((((2 : ℝ) * qBa) + ((0 : ℝ) * qBd)) + ((((((qCTF * ((4 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((135984345996929 : ℝ) / 2500000000000)) * ((1 : ℝ) / 1000000)))

theorem rowN04_bnd : Bnd rowN04 (5.6595741923948739353673846e1 : ℝ) (5.6595741923948739353673888e1 : ℝ) := by
  unfold rowN04
  have h1 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qBa_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((2 : ℝ) * qBa)) (5.6595265017851715670193754e1 : ℝ) (5.6595265017851715670193794e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (0 : ℝ) (0 : ℝ) (0 : ℝ) := Bnd.const _
  have h5 := Bnd.mul h4 qBd_bnd (by norm_num) (by norm_num)
  have h6 : Bnd (((0 : ℝ) * qBd)) (0 : ℝ) (0 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.add h3 h6
  have h8 : Bnd ((((2 : ℝ) * qBa) + ((0 : ℝ) * qBd))) (5.6595265017851715670193754e1 : ℝ) (5.6595265017851715670193794e1 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 : Bnd (4 : ℝ) (4 : ℝ) (4 : ℝ) := Bnd.const _
  have h10 : Bnd (((4 : ℝ) ^ (7 / 3 : ℝ))) (2.539841683149119159602729e1 : ℝ) (2.5398416831491191596027291e1 : ℝ) := Bnd.rpow' (p := 7) (q := 3) h9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11 := Bnd.mul qCTF_bnd h10 (by norm_num) (by norm_num)
  have h12 : Bnd ((qCTF * ((4 : ℝ) ^ (7 / 3 : ℝ)))) (1.9524908823954230678858019e1 : ℝ) (1.9524908823954230678899455e1 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 := Bnd.mul h12 qMe_bnd (by norm_num) (by norm_num)
  have h14 : Bnd (((qCTF * ((4 : ℝ) ^ (7 / 3 : ℝ))) * qMe)) (9.977207921358533813482654 : ℝ) (9.9772079213585338135038279 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 := Bnd.pow qAlpha_bnd (by norm_num) 2
  have h16 : Bnd ((qAlpha ^ 2)) (5.325135444808003103748339e-5 : ℝ) (5.3251354448080031037484361e-5 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.mul h14 h16 (by norm_num) (by norm_num)
  have h18 : Bnd ((((qCTF * ((4 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2))) (5.3129983542245508009249174e-4 : ℝ) (5.3129983542245508009362898e-4 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 : Bnd (1000000 : ℝ) (1000000 : ℝ) (1000000 : ℝ) := Bnd.const _
  have h20 := Bnd.mul h18 h19 (by norm_num) (by norm_num)
  have h21 : Bnd (((((qCTF * ((4 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ))) (5.3129983542245508009249174e2 : ℝ) (5.3129983542245508009362898e2 : ℝ) := h20.weak (by norm_num) (by norm_num)
  have h22 : Bnd ((135984345996929 : ℝ) / 2500000000000) ((135984345996929 : ℝ) / 2500000000000) ((135984345996929 : ℝ) / 2500000000000) := Bnd.const _
  have h23 := Bnd.sub h21 h22
  have h24 : Bnd ((((((qCTF * ((4 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((135984345996929 : ℝ) / 2500000000000))) (4.7690609702368348009249174e2 : ℝ) (4.7690609702368348009362898e2 : ℝ) := h23.weak (by norm_num) (by norm_num)
  have h25 : Bnd ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) := Bnd.const _
  have h26 := Bnd.mul h24 h25 (by norm_num) (by norm_num)
  have h27 : Bnd (((((((qCTF * ((4 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((135984345996929 : ℝ) / 2500000000000)) * ((1 : ℝ) / 1000000))) (4.7690609702368348009249174e-4 : ℝ) (4.7690609702368348009362898e-4 : ℝ) := h26.weak (by norm_num) (by norm_num)
  have h28 := Bnd.add h8 h27
  have h29 : Bnd (((((2 : ℝ) * qBa) + ((0 : ℝ) * qBd)) + ((((((qCTF * ((4 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((135984345996929 : ℝ) / 2500000000000)) * ((1 : ℝ) / 1000000)))) (5.6595741923948739353673846e1 : ℝ) (5.6595741923948739353673888e1 : ℝ) := h28.weak (by norm_num) (by norm_num)
  exact h29

/-- **Row N04 to its printed digits, `56.5957419239`.** -/
theorem rowN04_digits : (5.659574192385e1 : ℝ) < rowN04 ∧ rowN04 < (5.659574192395e1 : ℝ) :=
  rowN04_bnd.strict (by norm_num) (by norm_num)

/-- Row N05, carbon-12 binding, atomic [MeV]. -/
noncomputable def rowN05 : ℝ :=
  ((((3 : ℝ) * qBa) + (((13 : ℝ) / 4) * qBd)) + ((((((qCTF * ((6 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((407953037990787 : ℝ) / 5000000000000)) * ((1 : ℝ) / 1000000)))

theorem rowN05_bnd : Bnd rowN05 (9.2124025360841873631362785e1 : ℝ) (9.2124025360841873631362852e1 : ℝ) := by
  unfold rowN05
  have h1 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qBa_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((3 : ℝ) * qBa)) (8.4892897526777573505290631e1 : ℝ) (8.4892897526777573505290691e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd ((13 : ℝ) / 4) ((13 : ℝ) / 4) ((13 : ℝ) / 4) := Bnd.const _
  have h5 := Bnd.mul h4 qBd_bnd (by norm_num) (by norm_num)
  have h6 : Bnd ((((13 : ℝ) / 4) * qBd)) (7.2298410050723810509912083 : ℝ) (7.2298410050723810509912109 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.add h3 h6
  have h8 : Bnd ((((3 : ℝ) * qBa) + (((13 : ℝ) / 4) * qBd))) (9.2122738531849954556281839e1 : ℝ) (9.2122738531849954556281902e1 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 : Bnd (6 : ℝ) (6 : ℝ) (6 : ℝ) := Bnd.const _
  have h10 : Bnd (((6 : ℝ) ^ (7 / 3 : ℝ))) (6.5416341341957027720083623e1 : ℝ) (6.5416341341957027720083624e1 : ℝ) := Bnd.rpow' (p := 7) (q := 3) h9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11 := Bnd.mul qCTF_bnd h10 (by norm_num) (by norm_num)
  have h12 : Bnd ((qCTF * ((6 : ℝ) ^ (7 / 3 : ℝ)))) (5.0288492734505173985810449e1 : ℝ) (5.028849273450517398591717e1 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 := Bnd.mul h12 qMe_bnd (by norm_num) (by norm_num)
  have h14 : Bnd (((qCTF * ((6 : ℝ) ^ (7 / 3 : ℝ))) * qMe)) (2.5697367019113832663125024e1 : ℝ) (2.5697367019113832663179559e1 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 := Bnd.pow qAlpha_bnd (by norm_num) 2
  have h16 : Bnd ((qAlpha ^ 2)) (5.325135444808003103748339e-5 : ℝ) (5.3251354448080031037484361e-5 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.mul h14 h16 (by norm_num) (by norm_num)
  have h18 : Bnd ((((qCTF * ((6 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2))) (1.3684195995172324809469615e-3 : ℝ) (1.3684195995172324809498906e-3 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 : Bnd (1000000 : ℝ) (1000000 : ℝ) (1000000 : ℝ) := Bnd.const _
  have h20 := Bnd.mul h18 h19 (by norm_num) (by norm_num)
  have h21 : Bnd (((((qCTF * ((6 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ))) (1.3684195995172324809469615e3 : ℝ) (1.3684195995172324809498906e3 : ℝ) := h20.weak (by norm_num) (by norm_num)
  have h22 : Bnd ((407953037990787 : ℝ) / 5000000000000) ((407953037990787 : ℝ) / 5000000000000) ((407953037990787 : ℝ) / 5000000000000) := Bnd.const _
  have h23 := Bnd.sub h21 h22
  have h24 : Bnd ((((((qCTF * ((6 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((407953037990787 : ℝ) / 5000000000000))) (1.2868289919190750809469615e3 : ℝ) (1.2868289919190750809498906e3 : ℝ) := h23.weak (by norm_num) (by norm_num)
  have h25 : Bnd ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) := Bnd.const _
  have h26 := Bnd.mul h24 h25 (by norm_num) (by norm_num)
  have h27 : Bnd (((((((qCTF * ((6 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((407953037990787 : ℝ) / 5000000000000)) * ((1 : ℝ) / 1000000))) (1.2868289919190750809469615e-3 : ℝ) (1.2868289919190750809498906e-3 : ℝ) := h26.weak (by norm_num) (by norm_num)
  have h28 := Bnd.add h8 h27
  have h29 : Bnd (((((3 : ℝ) * qBa) + (((13 : ℝ) / 4) * qBd)) + ((((((qCTF * ((6 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((407953037990787 : ℝ) / 5000000000000)) * ((1 : ℝ) / 1000000)))) (9.2124025360841873631362785e1 : ℝ) (9.2124025360841873631362852e1 : ℝ) := h28.weak (by norm_num) (by norm_num)
  exact h29

/-- **Row N05 to its printed digits, `92.1240253608`.** -/
theorem rowN05_digits : (9.212402536075e1 : ℝ) < rowN05 ∧ rowN05 < (9.212402536085e1 : ℝ) :=
  rowN05_bnd.strict (by norm_num) (by norm_num)

/-- Row N06, oxygen-16 binding, atomic [MeV]. -/
noncomputable def rowN06 : ℝ :=
  ((((4 : ℝ) * qBa) + (((13 : ℝ) / 2) * qBd)) + ((((((qCTF * ((8 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((135984345996929 : ℝ) / 1250000000000)) * ((1 : ℝ) / 1000000)))

theorem rowN06_bnd : Bnd rowN06 (1.2765278084175721363088123e2 : ℝ) (1.2765278084175721363088135e2 : ℝ) := by
  unfold rowN06
  have h1 : Bnd (4 : ℝ) (4 : ℝ) (4 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qBa_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((4 : ℝ) * qBa)) (1.131905300357034313403875e2 : ℝ) (1.1319053003570343134038759e2 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd ((13 : ℝ) / 2) ((13 : ℝ) / 2) ((13 : ℝ) / 2) := Bnd.const _
  have h5 := Bnd.mul h4 qBd_bnd (by norm_num) (by norm_num)
  have h6 : Bnd ((((13 : ℝ) / 2) * qBd)) (1.4459682010144762101982416e1 : ℝ) (1.4459682010144762101982422e1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.add h3 h6
  have h8 : Bnd ((((4 : ℝ) * qBa) + (((13 : ℝ) / 2) * qBd))) (1.2765021204584819344236991e2 : ℝ) (1.2765021204584819344237002e2 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 : Bnd (8 : ℝ) (8 : ℝ) (8 : ℝ) := Bnd.const _
  have h10 : Bnd (((8 : ℝ) ^ (7 / 3 : ℝ))) (1.28e2 : ℝ) (1.28e2 : ℝ) := Bnd.rpow' (p := 7) (q := 3) h9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11 := Bnd.mul qCTF_bnd h10 (by norm_num) (by norm_num)
  have h12 : Bnd ((qCTF * ((8 : ℝ) ^ (7 / 3 : ℝ)))) (9.8399374498312350383911745e1 : ℝ) (9.8399374498312350384120562e1 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 := Bnd.mul h12 qMe_bnd (by norm_num) (by norm_num)
  have h14 : Bnd (((qCTF * ((8 : ℝ) ^ (7 / 3 : ℝ))) * qMe)) (5.028197711718995622204652e1 : ℝ) (5.0281977117189956222153226e1 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 := Bnd.pow qAlpha_bnd (by norm_num) 2
  have h16 : Bnd ((qAlpha ^ 2)) (5.325135444808003103748339e-5 : ℝ) (5.3251354448080031037484361e-5 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.mul h14 h16 (by norm_num) (by norm_num)
  have h18 : Bnd ((((qCTF * ((8 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2))) (2.677583385817731711321207e-3 : ℝ) (2.6775833858177317113269381e-3 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 : Bnd (1000000 : ℝ) (1000000 : ℝ) (1000000 : ℝ) := Bnd.const _
  have h20 := Bnd.mul h18 h19 (by norm_num) (by norm_num)
  have h21 : Bnd (((((qCTF * ((8 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ))) (2.677583385817731711321207e3 : ℝ) (2.6775833858177317113269381e3 : ℝ) := h20.weak (by norm_num) (by norm_num)
  have h22 : Bnd ((135984345996929 : ℝ) / 1250000000000) ((135984345996929 : ℝ) / 1250000000000) ((135984345996929 : ℝ) / 1250000000000) := Bnd.const _
  have h23 := Bnd.sub h21 h22
  have h24 : Bnd ((((((qCTF * ((8 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((135984345996929 : ℝ) / 1250000000000))) (2.568795909020188511321207e3 : ℝ) (2.5687959090201885113269381e3 : ℝ) := h23.weak (by norm_num) (by norm_num)
  have h25 : Bnd ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) := Bnd.const _
  have h26 := Bnd.mul h24 h25 (by norm_num) (by norm_num)
  have h27 : Bnd (((((((qCTF * ((8 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((135984345996929 : ℝ) / 1250000000000)) * ((1 : ℝ) / 1000000))) (2.568795909020188511321207e-3 : ℝ) (2.5687959090201885113269381e-3 : ℝ) := h26.weak (by norm_num) (by norm_num)
  have h28 := Bnd.add h8 h27
  have h29 : Bnd (((((4 : ℝ) * qBa) + (((13 : ℝ) / 2) * qBd)) + ((((((qCTF * ((8 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((135984345996929 : ℝ) / 1250000000000)) * ((1 : ℝ) / 1000000)))) (1.2765278084175721363088123e2 : ℝ) (1.2765278084175721363088135e2 : ℝ) := h28.weak (by norm_num) (by norm_num)
  exact h29

/-- **Row N06 to its printed digits, `127.652780842`.** -/
theorem rowN06_digits : (1.276527808415e2 : ℝ) < rowN06 ∧ rowN06 < (1.276527808425e2 : ℝ) :=
  rowN06_bnd.strict (by norm_num) (by norm_num)

/-- Row N07, neon-20 binding, atomic [MeV]. -/
noncomputable def rowN07 : ℝ :=
  ((((5 : ℝ) * qBa) + (((26 : ℝ) / 3) * qBd)) + ((((((qCTF * ((10 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((135984345996929 : ℝ) / 1000000000000)) * ((1 : ℝ) / 1000000)))

theorem rowN07_bnd : Bnd rowN07 (1.6077210935391265636152835e2 : ℝ) (1.607721093539126563615285e2 : ℝ) := by
  unfold rowN07
  have h1 : Bnd (5 : ℝ) (5 : ℝ) (5 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qBa_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((5 : ℝ) * qBa)) (1.4148816254462928917548438e2 : ℝ) (1.4148816254462928917548449e2 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd ((26 : ℝ) / 3) ((26 : ℝ) / 3) ((26 : ℝ) / 3) := Bnd.const _
  have h5 := Bnd.mul h4 qBd_bnd (by norm_num) (by norm_num)
  have h6 : Bnd ((((26 : ℝ) / 3) * qBd)) (1.9279576013526349469309888e1 : ℝ) (1.9279576013526349469309896e1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.add h3 h6
  have h8 : Bnd ((((5 : ℝ) * qBa) + (((26 : ℝ) / 3) * qBd))) (1.6076773855815563864479426e2 : ℝ) (1.6076773855815563864479439e2 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 : Bnd (10 : ℝ) (10 : ℝ) (10 : ℝ) := Bnd.const _
  have h10 : Bnd (((10 : ℝ) ^ (7 / 3 : ℝ))) (2.1544346900318837217592935e2 : ℝ) (2.1544346900318837217592936e2 : ℝ) := Bnd.rpow' (p := 7) (q := 3) h9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11 := Bnd.mul qCTF_bnd h10 (by norm_num) (by norm_num)
  have h12 : Bnd ((qCTF * ((10 : ℝ) ^ (7 / 3 : ℝ)))) (1.6562111398172094718775546e2 : ℝ) (1.6562111398172094718810695e2 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 := Bnd.mul h12 qMe_bnd (by norm_num) (by norm_num)
  have h14 : Bnd (((qCTF * ((10 : ℝ) ^ (7 / 3 : ℝ))) * qMe)) (8.4632215456768291853335946e1 : ℝ) (8.4632215456768291853515558e1 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 := Bnd.pow qAlpha_bnd (by norm_num) 2
  have h16 : Bnd ((qAlpha ^ 2)) (5.325135444808003103748339e-5 : ℝ) (5.3251354448080031037484361e-5 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.mul h14 h16 (by norm_num) (by norm_num)
  have h18 : Bnd ((((qCTF * ((10 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2))) (4.5067801030146457340970262e-3 : ℝ) (4.5067801030146457341066731e-3 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 : Bnd (1000000 : ℝ) (1000000 : ℝ) (1000000 : ℝ) := Bnd.const _
  have h20 := Bnd.mul h18 h19 (by norm_num) (by norm_num)
  have h21 : Bnd (((((qCTF * ((10 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ))) (4.5067801030146457340970262e3 : ℝ) (4.5067801030146457341066731e3 : ℝ) := h20.weak (by norm_num) (by norm_num)
  have h22 : Bnd ((135984345996929 : ℝ) / 1000000000000) ((135984345996929 : ℝ) / 1000000000000) ((135984345996929 : ℝ) / 1000000000000) := Bnd.const _
  have h23 := Bnd.sub h21 h22
  have h24 : Bnd ((((((qCTF * ((10 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((135984345996929 : ℝ) / 1000000000000))) (4.3707957570177167340970262e3 : ℝ) (4.3707957570177167341066731e3 : ℝ) := h23.weak (by norm_num) (by norm_num)
  have h25 : Bnd ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) := Bnd.const _
  have h26 := Bnd.mul h24 h25 (by norm_num) (by norm_num)
  have h27 : Bnd (((((((qCTF * ((10 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((135984345996929 : ℝ) / 1000000000000)) * ((1 : ℝ) / 1000000))) (4.3707957570177167340970262e-3 : ℝ) (4.3707957570177167341066731e-3 : ℝ) := h26.weak (by norm_num) (by norm_num)
  have h28 := Bnd.add h8 h27
  have h29 : Bnd (((((5 : ℝ) * qBa) + (((26 : ℝ) / 3) * qBd)) + ((((((qCTF * ((10 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((135984345996929 : ℝ) / 1000000000000)) * ((1 : ℝ) / 1000000)))) (1.6077210935391265636152835e2 : ℝ) (1.607721093539126563615285e2 : ℝ) := h28.weak (by norm_num) (by norm_num)
  exact h29

/-- **Row N07 to its printed digits, `160.772109354`.** -/
theorem rowN07_digits : (1.607721093535e2 : ℝ) < rowN07 ∧ rowN07 < (1.607721093545e2 : ℝ) :=
  rowN07_bnd.strict (by norm_num) (by norm_num)

/-- Row N08, magnesium-24 binding, atomic [MeV]. -/
noncomputable def rowN08 : ℝ :=
  ((((6 : ℝ) * qBa) + ((13 : ℝ) * qBd)) + ((((((qCTF * ((12 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((407953037990787 : ℝ) / 2500000000000)) * ((1 : ℝ) / 1000000)))

theorem rowN08_bnd : Bnd rowN08 (1.9871189229526355679342097e2 : ℝ) (1.9871189229526355679342114e2 : ℝ) := by
  unfold rowN08
  have h1 : Bnd (6 : ℝ) (6 : ℝ) (6 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qBa_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((6 : ℝ) * qBa)) (1.6978579505355514701058126e2 : ℝ) (1.6978579505355514701058139e2 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (13 : ℝ) (13 : ℝ) (13 : ℝ) := Bnd.const _
  have h5 := Bnd.mul h4 qBd_bnd (by norm_num) (by norm_num)
  have h6 : Bnd (((13 : ℝ) * qBd)) (2.8919364020289524203964833e1 : ℝ) (2.8919364020289524203964844e1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.add h3 h6
  have h8 : Bnd ((((6 : ℝ) * qBa) + ((13 : ℝ) * qBd))) (1.9870515907384467121454609e2 : ℝ) (1.9870515907384467121454624e2 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 : Bnd (12 : ℝ) (12 : ℝ) (12 : ℝ) := Bnd.const _
  have h10 : Bnd (((12 : ℝ) ^ (7 / 3 : ℝ))) (3.2967770185535957792871615e2 : ℝ) (3.2967770185535957792871616e2 : ℝ) := Bnd.rpow' (p := 7) (q := 3) h9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11 := Bnd.mul qCTF_bnd h10 (by norm_num) (by norm_num)
  have h12 : Bnd ((qCTF * ((12 : ℝ) ^ (7 / 3 : ℝ)))) (2.5343812225475383979531733e2 : ℝ) (2.5343812225475383979585518e2 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 := Bnd.mul h12 qMe_bnd (by norm_num) (by norm_num)
  have h14 : Bnd (((qCTF * ((12 : ℝ) ^ (7 / 3 : ℝ))) * qMe)) (1.2950661453702314899965552e2 : ℝ) (1.2950661453702314899993037e2 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 := Bnd.pow qAlpha_bnd (by norm_num) 2
  have h16 : Bnd ((qAlpha ^ 2)) (5.325135444808003103748339e-5 : ℝ) (5.3251354448080031037484361e-5 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.mul h14 h16 (by norm_num) (by norm_num)
  have h18 : Bnd ((((qCTF * ((12 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2))) (6.8964026340818936748841321e-3 : ℝ) (6.8964026340818936748988941e-3 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 : Bnd (1000000 : ℝ) (1000000 : ℝ) (1000000 : ℝ) := Bnd.const _
  have h20 := Bnd.mul h18 h19 (by norm_num) (by norm_num)
  have h21 : Bnd (((((qCTF * ((12 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ))) (6.8964026340818936748841321e3 : ℝ) (6.8964026340818936748988941e3 : ℝ) := h20.weak (by norm_num) (by norm_num)
  have h22 : Bnd ((407953037990787 : ℝ) / 2500000000000) ((407953037990787 : ℝ) / 2500000000000) ((407953037990787 : ℝ) / 2500000000000) := Bnd.const _
  have h23 := Bnd.sub h21 h22
  have h24 : Bnd ((((((qCTF * ((12 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((407953037990787 : ℝ) / 2500000000000))) (6.7332214188855788748841321e3 : ℝ) (6.7332214188855788748988941e3 : ℝ) := h23.weak (by norm_num) (by norm_num)
  have h25 : Bnd ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) := Bnd.const _
  have h26 := Bnd.mul h24 h25 (by norm_num) (by norm_num)
  have h27 : Bnd (((((((qCTF * ((12 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((407953037990787 : ℝ) / 2500000000000)) * ((1 : ℝ) / 1000000))) (6.7332214188855788748841321e-3 : ℝ) (6.7332214188855788748988941e-3 : ℝ) := h26.weak (by norm_num) (by norm_num)
  have h28 := Bnd.add h8 h27
  have h29 : Bnd (((((6 : ℝ) * qBa) + ((13 : ℝ) * qBd)) + ((((((qCTF * ((12 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((407953037990787 : ℝ) / 2500000000000)) * ((1 : ℝ) / 1000000)))) (1.9871189229526355679342097e2 : ℝ) (1.9871189229526355679342114e2 : ℝ) := h28.weak (by norm_num) (by norm_num)
  exact h29

/-- **Row N08 to its printed digits, `198.711892295`.** -/
theorem rowN08_digits : (1.987118922945e2 : ℝ) < rowN08 ∧ rowN08 < (1.987118922955e2 : ℝ) :=
  rowN08_bnd.strict (by norm_num) (by norm_num)

/-- Row N09, silicon-28 binding, atomic [MeV]. -/
noncomputable def rowN09 : ℝ :=
  ((((7 : ℝ) * qBa) + (((65 : ℝ) / 4) * qBd)) + ((((((qCTF * ((14 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((951890421978503 : ℝ) / 5000000000000)) * ((1 : ℝ) / 1000000)))

theorem rowN09_bnd : Bnd rowN09 (2.342423239124871588871774e2 : ℝ) (2.342423239124871588871776e2 : ℝ) := by
  unfold rowN09
  have h1 : Bnd (7 : ℝ) (7 : ℝ) (7 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qBa_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((7 : ℝ) * qBa)) (1.9808342756248100484567813e2 : ℝ) (1.9808342756248100484567828e2 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd ((65 : ℝ) / 4) ((65 : ℝ) / 4) ((65 : ℝ) / 4) := Bnd.const _
  have h5 := Bnd.mul h4 qBd_bnd (by norm_num) (by norm_num)
  have h6 : Bnd ((((65 : ℝ) / 4) * qBd)) (3.6149205025361905254956041e1 : ℝ) (3.6149205025361905254956055e1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.add h3 h6
  have h8 : Bnd ((((7 : ℝ) * qBa) + (((65 : ℝ) / 4) * qBd))) (2.3423263258784291010063417e2 : ℝ) (2.3423263258784291010063434e2 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 : Bnd (14 : ℝ) (14 : ℝ) (14 : ℝ) := Bnd.const _
  have h10 : Bnd (((14 : ℝ) ^ (7 / 3 : ℝ))) (4.7238788377834507728116045e2 : ℝ) (4.7238788377834507728116046e2 : ℝ) := Bnd.rpow' (p := 7) (q := 3) h9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11 := Bnd.mul qCTF_bnd h10 (by norm_num) (by norm_num)
  have h12 : Bnd ((qCTF * ((14 : ℝ) ^ (7 / 3 : ℝ)))) (3.631458772216455235852897e2 : ℝ) (3.6314587722164552358606036e2 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 := Bnd.mul h12 qMe_bnd (by norm_num) (by norm_num)
  have h14 : Bnd (((qCTF * ((14 : ℝ) ^ (7 / 3 : ℝ))) * qMe)) (1.8556716220766043510721868e2 : ℝ) (1.8556716220766043510761249e2 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 := Bnd.pow qAlpha_bnd (by norm_num) 2
  have h16 : Bnd ((qAlpha ^ 2)) (5.325135444808003103748339e-5 : ℝ) (5.3251354448080031037484361e-5 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.mul h14 h16 (by norm_num) (by norm_num)
  have h18 : Bnd ((((qCTF * ((14 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2))) (9.8817027286444871432347323e-3 : ℝ) (9.8817027286444871432558835e-3 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 : Bnd (1000000 : ℝ) (1000000 : ℝ) (1000000 : ℝ) := Bnd.const _
  have h20 := Bnd.mul h18 h19 (by norm_num) (by norm_num)
  have h21 : Bnd (((((qCTF * ((14 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ))) (9.8817027286444871432347323e3 : ℝ) (9.8817027286444871432558835e3 : ℝ) := h20.weak (by norm_num) (by norm_num)
  have h22 : Bnd ((951890421978503 : ℝ) / 5000000000000) ((951890421978503 : ℝ) / 5000000000000) ((951890421978503 : ℝ) / 5000000000000) := Bnd.const _
  have h23 := Bnd.sub h21 h22
  have h24 : Bnd ((((((qCTF * ((14 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((951890421978503 : ℝ) / 5000000000000))) (9.6913246442487865432347323e3 : ℝ) (9.6913246442487865432558835e3 : ℝ) := h23.weak (by norm_num) (by norm_num)
  have h25 : Bnd ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) := Bnd.const _
  have h26 := Bnd.mul h24 h25 (by norm_num) (by norm_num)
  have h27 : Bnd (((((((qCTF * ((14 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((951890421978503 : ℝ) / 5000000000000)) * ((1 : ℝ) / 1000000))) (9.6913246442487865432347323e-3 : ℝ) (9.6913246442487865432558835e-3 : ℝ) := h26.weak (by norm_num) (by norm_num)
  have h28 := Bnd.add h8 h27
  have h29 : Bnd (((((7 : ℝ) * qBa) + (((65 : ℝ) / 4) * qBd)) + ((((((qCTF * ((14 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((951890421978503 : ℝ) / 5000000000000)) * ((1 : ℝ) / 1000000)))) (2.342423239124871588871774e2 : ℝ) (2.342423239124871588871776e2 : ℝ) := h28.weak (by norm_num) (by norm_num)
  exact h29

/-- **Row N09 to its printed digits, `234.242323912`.** -/
theorem rowN09_digits : (2.342423239115e2 : ℝ) < rowN09 ∧ rowN09 < (2.342423239125e2 : ℝ) :=
  rowN09_bnd.strict (by norm_num) (by norm_num)

/-- Row N10, sulfur-32 binding, atomic [MeV]. -/
noncomputable def rowN10 : ℝ :=
  ((((8 : ℝ) * qBa) + (((39 : ℝ) / 2) * qBd)) + ((((((qCTF * ((16 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((135984345996929 : ℝ) / 625000000000)) * ((1 : ℝ) / 1000000)))

theorem rowN10_bnd : Bnd rowN10 (2.6977338270157011608343794e2 : ℝ) (2.6977338270157011608343818e2 : ℝ) := by
  unfold rowN10
  have h1 : Bnd (8 : ℝ) (8 : ℝ) (8 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qBa_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((8 : ℝ) * qBa)) (2.2638106007140686268077501e2 : ℝ) (2.2638106007140686268077518e2 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd ((39 : ℝ) / 2) ((39 : ℝ) / 2) ((39 : ℝ) / 2) := Bnd.const _
  have h5 := Bnd.mul h4 qBd_bnd (by norm_num) (by norm_num)
  have h6 : Bnd ((((39 : ℝ) / 2) * qBd)) (4.3379046030434286305947249e1 : ℝ) (4.3379046030434286305947266e1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.add h3 h6
  have h8 : Bnd ((((8 : ℝ) * qBa) + (((39 : ℝ) / 2) * qBd))) (2.6976010610184114898672225e2 : ℝ) (2.6976010610184114898672245e2 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 : Bnd (16 : ℝ) (16 : ℝ) (16 : ℝ) := Bnd.const _
  have h10 : Bnd (((16 : ℝ) ^ (7 / 3 : ℝ))) (6.4507957754617506036081183e2 : ℝ) (6.4507957754617506036081184e2 : ℝ) := Bnd.rpow' (p := 7) (q := 3) h9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11 := Bnd.mul qCTF_bnd h10 (by norm_num) (by norm_num)
  have h12 : Bnd ((qCTF * ((16 : ℝ) ^ (7 / 3 : ℝ)))) (4.9590177290765001957508947e2 : ℝ) (4.9590177290765001957614186e2 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 := Bnd.mul h12 qMe_bnd (by norm_num) (by norm_num)
  have h14 : Bnd (((qCTF * ((16 : ℝ) ^ (7 / 3 : ℝ))) * qMe)) (2.5340528560111983027662867e2 : ℝ) (2.5340528560111983027716645e2 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 := Bnd.pow qAlpha_bnd (by norm_num) 2
  have h16 : Bnd ((qAlpha ^ 2)) (5.325135444808003103748339e-5 : ℝ) (5.3251354448080031037484361e-5 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.mul h14 h16 (by norm_num) (by norm_num)
  have h18 : Bnd ((((qCTF * ((16 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2))) (1.3494174682562183115692787e-2 : ℝ) (1.3494174682562183115721672e-2 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 : Bnd (1000000 : ℝ) (1000000 : ℝ) (1000000 : ℝ) := Bnd.const _
  have h20 := Bnd.mul h18 h19 (by norm_num) (by norm_num)
  have h21 : Bnd (((((qCTF * ((16 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ))) (1.3494174682562183115692787e4 : ℝ) (1.3494174682562183115721672e4 : ℝ) := h20.weak (by norm_num) (by norm_num)
  have h22 : Bnd ((135984345996929 : ℝ) / 625000000000) ((135984345996929 : ℝ) / 625000000000) ((135984345996929 : ℝ) / 625000000000) := Bnd.const _
  have h23 := Bnd.sub h21 h22
  have h24 : Bnd ((((((qCTF * ((16 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((135984345996929 : ℝ) / 625000000000))) (1.3276599728967096715692787e4 : ℝ) (1.3276599728967096715721672e4 : ℝ) := h23.weak (by norm_num) (by norm_num)
  have h25 : Bnd ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) := Bnd.const _
  have h26 := Bnd.mul h24 h25 (by norm_num) (by norm_num)
  have h27 : Bnd (((((((qCTF * ((16 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((135984345996929 : ℝ) / 625000000000)) * ((1 : ℝ) / 1000000))) (1.3276599728967096715692787e-2 : ℝ) (1.3276599728967096715721672e-2 : ℝ) := h26.weak (by norm_num) (by norm_num)
  have h28 := Bnd.add h8 h27
  have h29 : Bnd (((((8 : ℝ) * qBa) + (((39 : ℝ) / 2) * qBd)) + ((((((qCTF * ((16 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((135984345996929 : ℝ) / 625000000000)) * ((1 : ℝ) / 1000000)))) (2.6977338270157011608343794e2 : ℝ) (2.6977338270157011608343818e2 : ℝ) := h28.weak (by norm_num) (by norm_num)
  exact h29

/-- **Row N10 to its printed digits, `269.773382702`.** -/
theorem rowN10_digits : (2.697733827015e2 : ℝ) < rowN10 ∧ rowN10 < (2.697733827025e2 : ℝ) :=
  rowN10_bnd.strict (by norm_num) (by norm_num)

/-- Row N11, argon-36 binding, atomic [MeV]. -/
noncomputable def rowN11 : ℝ :=
  ((((9 : ℝ) * qBa) + (((91 : ℝ) / 4) * qBd)) + ((((((qCTF * ((18 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((1223859113972361 : ℝ) / 5000000000000)) * ((1 : ℝ) / 1000000)))

theorem rowN11_bnd : Bnd rowN11 (3.0530509726723122908028828e2 : ℝ) (3.0530509726723122908028855e2 : ℝ) := by
  unfold rowN11
  have h1 : Bnd (9 : ℝ) (9 : ℝ) (9 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qBa_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((9 : ℝ) * qBa)) (2.5467869258033272051587189e2 : ℝ) (2.5467869258033272051587208e2 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd ((91 : ℝ) / 4) ((91 : ℝ) / 4) ((91 : ℝ) / 4) := Bnd.const _
  have h5 := Bnd.mul h4 qBd_bnd (by norm_num) (by norm_num)
  have h6 : Bnd ((((91 : ℝ) / 4) * qBd)) (5.0608887035506667356938458e1 : ℝ) (5.0608887035506667356938477e1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.add h3 h6
  have h8 : Bnd ((((9 : ℝ) * qBa) + (((91 : ℝ) / 4) * qBd))) (3.0528757961583938787281034e2 : ℝ) (3.0528757961583938787281056e2 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 : Bnd (18 : ℝ) (18 : ℝ) (18 : ℝ) := Bnd.const _
  have h10 : Bnd (((18 : ℝ) ^ (7 / 3 : ℝ))) (8.4912021172368250071389825e2 : ℝ) (8.4912021172368250071389826e2 : ℝ) := Bnd.rpow' (p := 7) (q := 3) h9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11 := Bnd.mul qCTF_bnd h10 (by norm_num) (by norm_num)
  have h12 : Bnd ((qCTF * ((18 : ℝ) ^ (7 / 3 : ℝ)))) (6.5275701333972583990246203e2 : ℝ) (6.5275701333972583990384729e2 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 := Bnd.mul h12 qMe_bnd (by norm_num) (by norm_num)
  have h14 : Bnd (((qCTF * ((18 : ℝ) ^ (7 / 3 : ℝ))) * qMe)) (3.3355814887213823668243702e2 : ℝ) (3.335581488721382366831449e2 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 := Bnd.pow qAlpha_bnd (by norm_num) 2
  have h16 : Bnd ((qAlpha ^ 2)) (5.325135444808003103748339e-5 : ℝ) (5.3251354448080031037484361e-5 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.mul h14 h16 (by norm_num) (by norm_num)
  have h18 : Bnd ((((qCTF * ((18 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2))) (1.7762423214635679677945445e-2 : ℝ) (1.7762423214635679677983466e-2 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 : Bnd (1000000 : ℝ) (1000000 : ℝ) (1000000 : ℝ) := Bnd.const _
  have h20 := Bnd.mul h18 h19 (by norm_num) (by norm_num)
  have h21 : Bnd (((((qCTF * ((18 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ))) (1.7762423214635679677945445e4 : ℝ) (1.7762423214635679677983466e4 : ℝ) := h20.weak (by norm_num) (by norm_num)
  have h22 : Bnd ((1223859113972361 : ℝ) / 5000000000000) ((1223859113972361 : ℝ) / 5000000000000) ((1223859113972361 : ℝ) / 5000000000000) := Bnd.const _
  have h23 := Bnd.sub h21 h22
  have h24 : Bnd ((((((qCTF * ((18 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((1223859113972361 : ℝ) / 5000000000000))) (1.7517651391841207477945445e4 : ℝ) (1.7517651391841207477983466e4 : ℝ) := h23.weak (by norm_num) (by norm_num)
  have h25 : Bnd ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) := Bnd.const _
  have h26 := Bnd.mul h24 h25 (by norm_num) (by norm_num)
  have h27 : Bnd (((((((qCTF * ((18 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((1223859113972361 : ℝ) / 5000000000000)) * ((1 : ℝ) / 1000000))) (1.7517651391841207477945445e-2 : ℝ) (1.7517651391841207477983466e-2 : ℝ) := h26.weak (by norm_num) (by norm_num)
  have h28 := Bnd.add h8 h27
  have h29 : Bnd (((((9 : ℝ) * qBa) + (((91 : ℝ) / 4) * qBd)) + ((((((qCTF * ((18 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((1223859113972361 : ℝ) / 5000000000000)) * ((1 : ℝ) / 1000000)))) (3.0530509726723122908028828e2 : ℝ) (3.0530509726723122908028855e2 : ℝ) := h28.weak (by norm_num) (by norm_num)
  exact h29

/-- **Row N11 to its printed digits, `305.305097267`.** -/
theorem rowN11_digits : (3.053050972665e2 : ℝ) < rowN11 ∧ rowN11 < (3.053050972675e2 : ℝ) :=
  rowN11_bnd.strict (by norm_num) (by norm_num)

/-- Row N12, calcium-40 binding, atomic [MeV]. -/
noncomputable def rowN12 : ℝ :=
  ((((10 : ℝ) * qBa) + ((26 : ℝ) * qBd)) + ((((((qCTF * ((20 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((135984345996929 : ℝ) / 500000000000)) * ((1 : ℝ) / 1000000)))

theorem rowN12_bnd : Bnd rowN12 (3.4083749390962177504925587e2 : ℝ) (3.4083749390962177504925616e2 : ℝ) := by
  unfold rowN12
  have h1 : Bnd (10 : ℝ) (10 : ℝ) (10 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qBa_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((10 : ℝ) * qBa)) (2.8297632508925857835096877e2 : ℝ) (2.8297632508925857835096897e2 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (26 : ℝ) (26 : ℝ) (26 : ℝ) := Bnd.const _
  have h5 := Bnd.mul h4 qBd_bnd (by norm_num) (by norm_num)
  have h6 : Bnd (((26 : ℝ) * qBd)) (5.7838728040579048407929666e1 : ℝ) (5.7838728040579048407929688e1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.add h3 h6
  have h8 : Bnd ((((10 : ℝ) * qBa) + ((26 : ℝ) * qBd))) (3.4081505312983762675889843e2 : ℝ) (3.4081505312983762675889866e2 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 : Bnd (20 : ℝ) (20 : ℝ) (20 : ℝ) := Bnd.const _
  have h10 : Bnd (((20 : ℝ) ^ (7 / 3 : ℝ))) (1.0857670466379626286072357e3 : ℝ) (1.0857670466379626286072358e3 : ℝ) := Bnd.rpow' (p := 7) (q := 3) h9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11 := Bnd.mul qCTF_bnd h10 (by norm_num) (by norm_num)
  have h12 : Bnd ((qCTF * ((20 : ℝ) ^ (7 / 3 : ℝ)))) (8.3467811125043325210865596e2 : ℝ) (8.3467811125043325211042734e2 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 := Bnd.mul h12 qMe_bnd (by norm_num) (by norm_num)
  have h14 : Bnd (((qCTF * ((20 : ℝ) ^ (7 / 3 : ℝ))) * qMe)) (4.2651963901288247563540742e2 : ℝ) (4.265196390128824756363126e2 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 := Bnd.pow qAlpha_bnd (by norm_num) 2
  have h16 : Bnd ((qAlpha ^ 2)) (5.325135444808003103748339e-5 : ℝ) (5.3251354448080031037484361e-5 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.mul h14 h16 (by norm_num) (by norm_num)
  have h18 : Bnd ((((qCTF * ((20 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2))) (2.2712748476142148357446046e-2 : ℝ) (2.2712748476142148357494663e-2 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 : Bnd (1000000 : ℝ) (1000000 : ℝ) (1000000 : ℝ) := Bnd.const _
  have h20 := Bnd.mul h18 h19 (by norm_num) (by norm_num)
  have h21 : Bnd (((((qCTF * ((20 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ))) (2.2712748476142148357446046e4 : ℝ) (2.2712748476142148357494663e4 : ℝ) := h20.weak (by norm_num) (by norm_num)
  have h22 : Bnd ((135984345996929 : ℝ) / 500000000000) ((135984345996929 : ℝ) / 500000000000) ((135984345996929 : ℝ) / 500000000000) := Bnd.const _
  have h23 := Bnd.sub h21 h22
  have h24 : Bnd ((((((qCTF * ((20 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((135984345996929 : ℝ) / 500000000000))) (2.2440779784148290357446046e4 : ℝ) (2.2440779784148290357494663e4 : ℝ) := h23.weak (by norm_num) (by norm_num)
  have h25 : Bnd ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) := Bnd.const _
  have h26 := Bnd.mul h24 h25 (by norm_num) (by norm_num)
  have h27 : Bnd (((((((qCTF * ((20 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((135984345996929 : ℝ) / 500000000000)) * ((1 : ℝ) / 1000000))) (2.2440779784148290357446046e-2 : ℝ) (2.2440779784148290357494663e-2 : ℝ) := h26.weak (by norm_num) (by norm_num)
  have h28 := Bnd.add h8 h27
  have h29 : Bnd (((((10 : ℝ) * qBa) + ((26 : ℝ) * qBd)) + ((((((qCTF * ((20 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((135984345996929 : ℝ) / 500000000000)) * ((1 : ℝ) / 1000000)))) (3.4083749390962177504925587e2 : ℝ) (3.4083749390962177504925616e2 : ℝ) := h28.weak (by norm_num) (by norm_num)
  exact h29

/-- **Row N12 to its printed digits, `340.83749391`.** -/
theorem rowN12_digits : (3.40837493905e2 : ℝ) < rowN12 ∧ rowN12 < (3.40837493915e2 : ℝ) :=
  rowN12_bnd.strict (by norm_num) (by norm_num)

/-- Row N13, titanium-44 binding, atomic [MeV]. -/
noncomputable def rowN13 : ℝ :=
  ((((11 : ℝ) * qBa) + (((117 : ℝ) / 4) * qBd)) + ((((((qCTF * ((22 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((1495827805966219 : ℝ) / 5000000000000)) * ((1 : ℝ) / 1000000)))

theorem rowN13_bnd : Bnd rowN13 (3.7637059703980400536862345e2 : ℝ) (3.7637059703980400536862378e2 : ℝ) := by
  unfold rowN13
  have h1 : Bnd (11 : ℝ) (11 : ℝ) (11 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qBa_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((11 : ℝ) * qBa)) (3.1127395759818443618606564e2 : ℝ) (3.1127395759818443618606587e2 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd ((117 : ℝ) / 4) ((117 : ℝ) / 4) ((117 : ℝ) / 4) := Bnd.const _
  have h5 := Bnd.mul h4 qBd_bnd (by norm_num) (by norm_num)
  have h6 : Bnd ((((117 : ℝ) / 4) * qBd)) (6.5068569045651429458920874e1 : ℝ) (6.5068569045651429458920899e1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.add h3 h6
  have h8 : Bnd ((((11 : ℝ) * qBa) + (((117 : ℝ) / 4) * qBd))) (3.7634252664383586564498651e2 : ℝ) (3.7634252664383586564498677e2 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 : Bnd (22 : ℝ) (22 : ℝ) (22 : ℝ) := Bnd.const _
  have h10 : Bnd (((22 : ℝ) ^ (7 / 3 : ℝ))) (1.3561870360372073664021878e3 : ℝ) (1.3561870360372073664021879e3 : ℝ) := Bnd.rpow' (p := 7) (q := 3) h9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11 := Bnd.mul qCTF_bnd h10 (by norm_num) (by norm_num)
  have h12 : Bnd ((qCTF * ((22 : ℝ) ^ (7 / 3 : ℝ)))) (1.0425621566311046488285588e3 : ℝ) (1.0425621566311046488307714e3 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 := Bnd.mul h12 qMe_bnd (by norm_num) (by norm_num)
  have h14 : Bnd (((qCTF * ((22 : ℝ) ^ (7 / 3 : ℝ))) * qMe)) (5.3274816806759790096697448e2 : ℝ) (5.3274816806759790096810513e2 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 := Bnd.pow qAlpha_bnd (by norm_num) 2
  have h16 : Bnd ((qAlpha ^ 2)) (5.325135444808003103748339e-5 : ℝ) (5.3251354448080031037484361e-5 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.mul h14 h16 (by norm_num) (by norm_num)
  have h18 : Bnd ((((qCTF * ((22 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2))) (2.8369561529332967436940985e-2 : ℝ) (2.8369561529332967437001712e-2 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 : Bnd (1000000 : ℝ) (1000000 : ℝ) (1000000 : ℝ) := Bnd.const _
  have h20 := Bnd.mul h18 h19 (by norm_num) (by norm_num)
  have h21 : Bnd (((((qCTF * ((22 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ))) (2.8369561529332967436940985e4 : ℝ) (2.8369561529332967437001712e4 : ℝ) := h20.weak (by norm_num) (by norm_num)
  have h22 : Bnd ((1495827805966219 : ℝ) / 5000000000000) ((1495827805966219 : ℝ) / 5000000000000) ((1495827805966219 : ℝ) / 5000000000000) := Bnd.const _
  have h23 := Bnd.sub h21 h22
  have h24 : Bnd ((((((qCTF * ((22 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((1495827805966219 : ℝ) / 5000000000000))) (2.8070395968139723636940985e4 : ℝ) (2.8070395968139723637001712e4 : ℝ) := h23.weak (by norm_num) (by norm_num)
  have h25 : Bnd ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) := Bnd.const _
  have h26 := Bnd.mul h24 h25 (by norm_num) (by norm_num)
  have h27 : Bnd (((((((qCTF * ((22 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((1495827805966219 : ℝ) / 5000000000000)) * ((1 : ℝ) / 1000000))) (2.8070395968139723636940985e-2 : ℝ) (2.8070395968139723637001712e-2 : ℝ) := h26.weak (by norm_num) (by norm_num)
  have h28 := Bnd.add h8 h27
  have h29 : Bnd (((((11 : ℝ) * qBa) + (((117 : ℝ) / 4) * qBd)) + ((((((qCTF * ((22 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((1495827805966219 : ℝ) / 5000000000000)) * ((1 : ℝ) / 1000000)))) (3.7637059703980400536862345e2 : ℝ) (3.7637059703980400536862378e2 : ℝ) := h28.weak (by norm_num) (by norm_num)
  exact h29

/-- **Row N13 to its printed digits, `376.37059704`.** -/
theorem rowN13_digits : (3.76370597035e2 : ℝ) < rowN13 ∧ rowN13 < (3.76370597045e2 : ℝ) :=
  rowN13_bnd.strict (by norm_num) (by norm_num)

/-- Row N14, chromium-48 binding, atomic [MeV]. -/
noncomputable def rowN14 : ℝ :=
  ((((12 : ℝ) * qBa) + (((65 : ℝ) / 2) * qBd)) + ((((((qCTF * ((24 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((407953037990787 : ℝ) / 1250000000000)) * ((1 : ℝ) / 1000000)))

theorem rowN14_bnd : Bnd rowN14 (4.1190442948679263281460034e2 : ℝ) (4.119044294867926328146007e2 : ℝ) := by
  unfold rowN14
  have h1 : Bnd (12 : ℝ) (12 : ℝ) (12 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qBa_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((12 : ℝ) * qBa)) (3.3957159010711029402116252e2 : ℝ) (3.3957159010711029402116277e2 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd ((65 : ℝ) / 2) ((65 : ℝ) / 2) ((65 : ℝ) / 2) := Bnd.const _
  have h5 := Bnd.mul h4 qBd_bnd (by norm_num) (by norm_num)
  have h6 : Bnd ((((65 : ℝ) / 2) * qBd)) (7.2298410050723810509912083e1 : ℝ) (7.2298410050723810509912109e1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.add h3 h6
  have h8 : Bnd ((((12 : ℝ) * qBa) + (((65 : ℝ) / 2) * qBd))) (4.118700001578341045310746e2 : ℝ) (4.1187000015783410453107488e2 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 : Bnd (24 : ℝ) (24 : ℝ) (24 : ℝ) := Bnd.const _
  have h10 : Bnd (((24 : ℝ) ^ (7 / 3 : ℝ))) (1.6614715049941344564345273e3 : ℝ) (1.6614715049941344564345274e3 : ℝ) := Bnd.rpow' (p := 7) (q := 3) h9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11 := Bnd.mul qCTF_bnd h10 (by norm_num) (by norm_num)
  have h12 : Bnd ((qCTF * ((24 : ℝ) ^ (7 / 3 : ℝ)))) (1.2772481002983787104258598e3 : ℝ) (1.2772481002983787104285705e3 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 := Bnd.mul h12 qMe_bnd (by norm_num) (by norm_num)
  have h14 : Bnd (((qCTF * ((24 : ℝ) ^ (7 / 3 : ℝ))) * qMe)) (6.5267243902326739693584972e2 : ℝ) (6.5267243902326739693723489e2 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 := Bnd.pow qAlpha_bnd (by norm_num) 2
  have h16 : Bnd ((qAlpha ^ 2)) (5.325135444808003103748339e-5 : ℝ) (5.3251354448080031037484361e-5 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.mul h14 h16 (by norm_num) (by norm_num)
  have h18 : Bnd ((((qCTF * ((24 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2))) (3.4755691388920913125745089e-2 : ℝ) (3.4755691388920913125819486e-2 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 : Bnd (1000000 : ℝ) (1000000 : ℝ) (1000000 : ℝ) := Bnd.const _
  have h20 := Bnd.mul h18 h19 (by norm_num) (by norm_num)
  have h21 : Bnd (((((qCTF * ((24 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ))) (3.4755691388920913125745089e4 : ℝ) (3.4755691388920913125819486e4 : ℝ) := h20.weak (by norm_num) (by norm_num)
  have h22 : Bnd ((407953037990787 : ℝ) / 1250000000000) ((407953037990787 : ℝ) / 1250000000000) ((407953037990787 : ℝ) / 1250000000000) := Bnd.const _
  have h23 := Bnd.sub h21 h22
  have h24 : Bnd ((((((qCTF * ((24 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((407953037990787 : ℝ) / 1250000000000))) (3.4429328958528283525745089e4 : ℝ) (3.4429328958528283525819486e4 : ℝ) := h23.weak (by norm_num) (by norm_num)
  have h25 : Bnd ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) := Bnd.const _
  have h26 := Bnd.mul h24 h25 (by norm_num) (by norm_num)
  have h27 : Bnd (((((((qCTF * ((24 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((407953037990787 : ℝ) / 1250000000000)) * ((1 : ℝ) / 1000000))) (3.4429328958528283525745089e-2 : ℝ) (3.4429328958528283525819486e-2 : ℝ) := h26.weak (by norm_num) (by norm_num)
  have h28 := Bnd.add h8 h27
  have h29 : Bnd (((((12 : ℝ) * qBa) + (((65 : ℝ) / 2) * qBd)) + ((((((qCTF * ((24 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((407953037990787 : ℝ) / 1250000000000)) * ((1 : ℝ) / 1000000)))) (4.1190442948679263281460034e2 : ℝ) (4.119044294867926328146007e2 : ℝ) := h28.weak (by norm_num) (by norm_num)
  exact h29

/-- **Row N14 to its printed digits, `411.904429487`.** -/
theorem rowN14_digits : (4.119044294865e2 : ℝ) < rowN14 ∧ rowN14 < (4.119044294875e2 : ℝ) :=
  rowN14_bnd.strict (by norm_num) (by norm_num)

/-- Row N15, iron-52 binding, atomic [MeV]. -/
noncomputable def rowN15 : ℝ :=
  ((((13 : ℝ) * qBa) + (((143 : ℝ) / 4) * qBd)) + ((((((qCTF * ((26 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((1767796497960077 : ℝ) / 5000000000000)) * ((1 : ℝ) / 1000000)))

theorem rowN15_bnd : Bnd rowN15 (4.4743901273168308669668288e2 : ℝ) (4.4743901273168308669668328e2 : ℝ) := by
  unfold rowN15
  have h1 : Bnd (13 : ℝ) (13 : ℝ) (13 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qBa_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((13 : ℝ) * qBa)) (3.678692226160361518562594e2 : ℝ) (3.6786922261603615185625967e2 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd ((143 : ℝ) / 4) ((143 : ℝ) / 4) ((143 : ℝ) / 4) := Bnd.const _
  have h5 := Bnd.mul h4 qBd_bnd (by norm_num) (by norm_num)
  have h6 : Bnd ((((143 : ℝ) / 4) * qBd)) (7.9528251055796191560903291e1 : ℝ) (7.952825105579619156090332e1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.add h3 h6
  have h8 : Bnd ((((13 : ℝ) * qBa) + (((143 : ℝ) / 4) * qBd))) (4.4739747367183234341716269e2 : ℝ) (4.4739747367183234341716299e2 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 : Bnd (26 : ℝ) (26 : ℝ) (26 : ℝ) := Bnd.const _
  have h10 : Bnd (((26 : ℝ) ^ (7 / 3 : ℝ))) (2.00264734224338246386299e3 : ℝ) (2.0026473422433824638629901e3 : ℝ) := Bnd.rpow' (p := 7) (q := 3) h9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11 := Bnd.mul qCTF_bnd h10 (by norm_num) (by norm_num)
  have h12 : Bnd ((qCTF * ((26 : ℝ) ^ (7 / 3 : ℝ)))) (1.539525357948878860860077e3 : ℝ) (1.5395253579488788608633442e3 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 := Bnd.mul h12 qMe_bnd (by norm_num) (by norm_num)
  have h14 : Bnd (((qCTF * ((26 : ℝ) ^ (7 / 3 : ℝ))) * qMe)) (7.8669584247252374856142185e2 : ℝ) (7.866958424725237485630914e2 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 := Bnd.pow qAlpha_bnd (by norm_num) 2
  have h16 : Bnd ((qAlpha ^ 2)) (5.325135444808003103748339e-5 : ℝ) (5.3251354448080031037484361e-5 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.mul h14 h16 (by norm_num) (by norm_num)
  have h18 : Bnd ((((qCTF * ((26 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2))) (4.189261915033529492019885e-2 : ℝ) (4.1892619150335294920288521e-2 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 : Bnd (1000000 : ℝ) (1000000 : ℝ) (1000000 : ℝ) := Bnd.const _
  have h20 := Bnd.mul h18 h19 (by norm_num) (by norm_num)
  have h21 : Bnd (((((qCTF * ((26 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ))) (4.189261915033529492019885e4 : ℝ) (4.1892619150335294920288521e4 : ℝ) := h20.weak (by norm_num) (by norm_num)
  have h22 : Bnd ((1767796497960077 : ℝ) / 5000000000000) ((1767796497960077 : ℝ) / 5000000000000) ((1767796497960077 : ℝ) / 5000000000000) := Bnd.const _
  have h23 := Bnd.sub h21 h22
  have h24 : Bnd ((((((qCTF * ((26 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((1767796497960077 : ℝ) / 5000000000000))) (4.153905985074327952019885e4 : ℝ) (4.1539059850743279520288521e4 : ℝ) := h23.weak (by norm_num) (by norm_num)
  have h25 : Bnd ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) := Bnd.const _
  have h26 := Bnd.mul h24 h25 (by norm_num) (by norm_num)
  have h27 : Bnd (((((((qCTF * ((26 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((1767796497960077 : ℝ) / 5000000000000)) * ((1 : ℝ) / 1000000))) (4.153905985074327952019885e-2 : ℝ) (4.1539059850743279520288521e-2 : ℝ) := h26.weak (by norm_num) (by norm_num)
  have h28 := Bnd.add h8 h27
  have h29 : Bnd (((((13 : ℝ) * qBa) + (((143 : ℝ) / 4) * qBd)) + ((((((qCTF * ((26 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((1767796497960077 : ℝ) / 5000000000000)) * ((1 : ℝ) / 1000000)))) (4.4743901273168308669668288e2 : ℝ) (4.4743901273168308669668328e2 : ℝ) := h28.weak (by norm_num) (by norm_num)
  exact h29

/-- **Row N15 to its printed digits, `447.439012732`.** -/
theorem rowN15_digits : (4.474390127315e2 : ℝ) < rowN15 ∧ rowN15 < (4.474390127325e2 : ℝ) :=
  rowN15_bnd.strict (by norm_num) (by norm_num)

/-- Row N16, nickel-56 binding, atomic [MeV]. -/
noncomputable def rowN16 : ℝ :=
  ((((14 : ℝ) * qBa) + ((39 : ℝ) * qBd)) + ((((((qCTF * ((28 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((951890421978503 : ℝ) / 2500000000000)) * ((1 : ℝ) / 1000000)))

theorem rowN16_bnd : Bnd rowN16 (4.8297436709076828208278532e2 : ℝ) (4.8297436709076828208278578e2 : ℝ) := by
  unfold rowN16
  have h1 : Bnd (14 : ℝ) (14 : ℝ) (14 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qBa_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((14 : ℝ) * qBa)) (3.9616685512496200969135627e2 : ℝ) (3.9616685512496200969135656e2 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (39 : ℝ) (39 : ℝ) (39 : ℝ) := Bnd.const _
  have h5 := Bnd.mul h4 qBd_bnd (by norm_num) (by norm_num)
  have h6 : Bnd (((39 : ℝ) * qBd)) (8.6758092060868572611894499e1 : ℝ) (8.6758092060868572611894531e1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.add h3 h6
  have h8 : Bnd ((((14 : ℝ) * qBa) + ((39 : ℝ) * qBd))) (4.8292494718583058230325076e2 : ℝ) (4.829249471858305823032511e2 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 : Bnd (28 : ℝ) (28 : ℝ) (28 : ℝ) := Bnd.const _
  have h10 : Bnd (((28 : ℝ) ^ (7 / 3 : ℝ))) (2.3806857539505194152259147e3 : ℝ) (2.3806857539505194152259148e3 : ℝ) := Bnd.rpow' (p := 7) (q := 3) h9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11 := Bnd.mul qCTF_bnd h10 (by norm_num) (by norm_num)
  have h12 : Bnd ((qCTF * ((28 : ℝ) ^ (7 / 3 : ℝ)))) (1.830140539576361336012925e3 : ℝ) (1.830140539576361336016809e3 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 := Bnd.mul h12 qMe_bnd (by norm_num) (by norm_num)
  have h14 : Bnd (((qCTF * ((28 : ℝ) ^ (7 / 3 : ℝ))) * qMe)) (9.3519989533875105983089118e2 : ℝ) (9.3519989533875105983287591e2 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 := Bnd.pow qAlpha_bnd (by norm_num) 2
  have h16 : Bnd ((qAlpha ^ 2)) (5.325135444808003103748339e-5 : ℝ) (5.3251354448080031037484361e-5 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.mul h14 h16 (by norm_num) (by norm_num)
  have h18 : Bnd ((((qCTF * ((28 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2))) (4.9800661106491180734568759e-2 : ℝ) (4.9800661106491180734675357e-2 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 : Bnd (1000000 : ℝ) (1000000 : ℝ) (1000000 : ℝ) := Bnd.const _
  have h20 := Bnd.mul h18 h19 (by norm_num) (by norm_num)
  have h21 : Bnd (((((qCTF * ((28 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ))) (4.9800661106491180734568759e4 : ℝ) (4.9800661106491180734675357e4 : ℝ) := h20.weak (by norm_num) (by norm_num)
  have h22 : Bnd ((951890421978503 : ℝ) / 2500000000000) ((951890421978503 : ℝ) / 2500000000000) ((951890421978503 : ℝ) / 2500000000000) := Bnd.const _
  have h23 := Bnd.sub h21 h22
  have h24 : Bnd ((((((qCTF * ((28 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((951890421978503 : ℝ) / 2500000000000))) (4.9419904937699779534568759e4 : ℝ) (4.9419904937699779534675357e4 : ℝ) := h23.weak (by norm_num) (by norm_num)
  have h25 : Bnd ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) := Bnd.const _
  have h26 := Bnd.mul h24 h25 (by norm_num) (by norm_num)
  have h27 : Bnd (((((((qCTF * ((28 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((951890421978503 : ℝ) / 2500000000000)) * ((1 : ℝ) / 1000000))) (4.9419904937699779534568759e-2 : ℝ) (4.9419904937699779534675357e-2 : ℝ) := h26.weak (by norm_num) (by norm_num)
  have h28 := Bnd.add h8 h27
  have h29 : Bnd (((((14 : ℝ) * qBa) + ((39 : ℝ) * qBd)) + ((((((qCTF * ((28 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((951890421978503 : ℝ) / 2500000000000)) * ((1 : ℝ) / 1000000)))) (4.8297436709076828208278532e2 : ℝ) (4.8297436709076828208278578e2 : ℝ) := h28.weak (by norm_num) (by norm_num)
  exact h29

/-- **Row N16 to its printed digits, `482.974367091`.** -/
theorem rowN16_digits : (4.829743670905e2 : ℝ) < rowN16 ∧ rowN16 < (4.829743670915e2 : ℝ) :=
  rowN16_bnd.strict (by norm_num) (by norm_num)

/-- Row S13, neon-20, eight-bond construction [MeV]. -/
noncomputable def rowS13 : ℝ :=
  rowN07

theorem rowS13_bnd : Bnd rowS13 (1.6077210935391265636152835e2 : ℝ) (1.607721093539126563615285e2 : ℝ) := by
  unfold rowS13
  exact rowN07_bnd

/-- **Row S13 to its printed digits, `160.772109354`.** -/
theorem rowS13_digits : (1.607721093535e2 : ℝ) < rowS13 ∧ rowS13 < (1.607721093545e2 : ℝ) :=
  rowS13_bnd.strict (by norm_num) (by norm_num)

/-- Row S01, axial coupling `g_A`. -/
noncomputable def rowS01 : ℝ :=
  qGA

theorem rowS01_bnd : Bnd rowS01 (1.2758009281154655816747105 : ℝ) (1.2758009281154655816747106 : ℝ) := by
  unfold rowS01
  exact qGA_bnd

/-- **Row S01 to its printed digits, `1.27580092812`.** -/
theorem rowS01_digits : (1.275800928115 : ℝ) < rowS01 ∧ rowS01 < (1.275800928125 : ℝ) :=
  rowS01_bnd.strict (by norm_num) (by norm_num)

/-- Row S02, axial radius squared [fm`^2`]. -/
noncomputable def rowS02 : ℝ :=
  (((9 : ℝ) * qLp) * qLp)

theorem rowS02_bnd : Bnd rowS02 (3.9806853882989393362819626e-1 : ℝ) (3.9806853882989393363073069e-1 : ℝ) := by
  unfold rowS02
  have h1 : Bnd (9 : ℝ) (9 : ℝ) (9 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qLp_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((9 : ℝ) * qLp)) (1.8927801904788219234333005 : ℝ) (1.892780190478821923439326 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.mul h3 qLp_bnd (by norm_num) (by norm_num)
  have h5 : Bnd ((((9 : ℝ) * qLp) * qLp)) (3.9806853882989393362819626e-1 : ℝ) (3.9806853882989393363073069e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- **Row S02 to its printed digits, `0.39806853883`.** -/
theorem rowS02_digits : (3.98068538825e-1 : ℝ) < rowS02 ∧ rowS02 < (3.98068538835e-1 : ℝ) :=
  rowS02_bnd.strict (by norm_num) (by norm_num)

/-- Row S03, axial radius [fm]. -/
noncomputable def rowS03 : ℝ :=
  ((3 : ℝ) * qLp)

theorem rowS03_bnd : Bnd rowS03 (6.3092673015960730781110017e-1 : ℝ) (6.3092673015960730781310864e-1 : ℝ) := by
  unfold rowS03
  have h1 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qLp_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((3 : ℝ) * qLp)) (6.3092673015960730781110017e-1 : ℝ) (6.3092673015960730781310864e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  exact h3

/-- **Row S03 to its printed digits, `0.63092673016`.** -/
theorem rowS03_digits : (6.30926730155e-1 : ℝ) < rowS03 ∧ rowS03 < (6.30926730165e-1 : ℝ) :=
  rowS03_bnd.strict (by norm_num) (by norm_num)

/-- Row S04, pion charge radius [fm]. -/
noncomputable def rowS04 : ℝ :=
  ((√(10 : ℝ)) * qLp)

theorem rowS04_bnd : Bnd rowS04 (6.6505516799560314840943545e-1 : ℝ) (6.650551679956031484115526e-1 : ℝ) := by
  unfold rowS04
  have h1 : Bnd (10 : ℝ) (10 : ℝ) (10 : ℝ) := Bnd.const _
  have h2 : Bnd ((√(10 : ℝ))) (3.1622776601683793319988935 : ℝ) (3.1622776601683793319988936 : ℝ) := Bnd.sqrt h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 := Bnd.mul h2 qLp_bnd (by norm_num) (by norm_num)
  have h4 : Bnd (((√(10 : ℝ)) * qLp)) (6.6505516799560314840943545e-1 : ℝ) (6.650551679956031484115526e-1 : ℝ) := h3.weak (by norm_num) (by norm_num)
  exact h4

/-- **Row S04 to its printed digits, `0.665055167996`.** -/
theorem rowS04_digits : (6.650551679955e-1 : ℝ) < rowS04 ∧ rowS04 < (6.650551679965e-1 : ℝ) :=
  rowS04_bnd.strict (by norm_num) (by norm_num)

/-- Row A002, pion decay constant, second construction `5m_p/36` [MeV]. -/
noncomputable def rowA002 : ℝ :=
  (((5 : ℝ) * qMp) / (36 : ℝ))

theorem rowA002_bnd : Bnd rowA002 (1.3031556797502732287785342e2 : ℝ) (1.3031556797502732287785346e2 : ℝ) := by
  unfold rowA002
  have h1 : Bnd (5 : ℝ) (5 : ℝ) (5 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qMp_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((5 : ℝ) * qMp)) (4.6913604471009836236027234e3 : ℝ) (4.6913604471009836236027243e3 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (36 : ℝ) (36 : ℝ) (36 : ℝ) := Bnd.const _
  have h5 := Bnd.div h3 h4 (by norm_num) (by norm_num)
  have h6 : Bnd ((((5 : ℝ) * qMp) / (36 : ℝ))) (1.3031556797502732287785342e2 : ℝ) (1.3031556797502732287785346e2 : ℝ) := h5.weak (by norm_num) (by norm_num)
  exact h6

/-- **Row A002 to its printed digits, `130.315567975`.** -/
theorem rowA002_digits : (1.303155679745e2 : ℝ) < rowA002 ∧ rowA002 < (1.303155679755e2 : ℝ) :=
  rowA002_bnd.strict (by norm_num) (by norm_num)

/-- `m_p a²`, the bulk's unit, in MeV. -/
noncomputable def qMa2 : ℝ :=
  (qMp * ((25 : ℝ) / 1444))

theorem qMa2_bnd : Bnd qMa2 (1.6244322877773489001394471e1 : ℝ) (1.6244322877773489001394475e1 : ℝ) := by
  unfold qMa2
  have h1 : Bnd ((25 : ℝ) / 1444) ((25 : ℝ) / 1444) ((25 : ℝ) / 1444) := Bnd.const _
  have h2 := Bnd.mul qMp_bnd h1 (by norm_num) (by norm_num)
  have h3 : Bnd ((qMp * ((25 : ℝ) / 1444))) (1.6244322877773489001394471e1 : ℝ) (1.6244322877773489001394475e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  exact h3

/-- The Coulomb coefficient `a_C = m_p a² · 4α/(5a)`. -/
noncomputable def qAC : ℝ :=
  ((((152 : ℝ) / 25) * qAlpha) * qMa2)

theorem qAC_bnd : Bnd qAC (7.207265513438204252816206e-1 : ℝ) (7.2072655134382042528162736e-1 : ℝ) := by
  unfold qAC
  have h1 : Bnd ((152 : ℝ) / 25) ((152 : ℝ) / 25) ((152 : ℝ) / 25) := Bnd.const _
  have h2 := Bnd.mul h1 qAlpha_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((((152 : ℝ) / 25) * qAlpha)) (4.436790359110407257629464e-2 : ℝ) (4.4367903591104072576295045e-2 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.mul h3 qMa2_bnd (by norm_num) (by norm_num)
  have h5 : Bnd (((((152 : ℝ) / 25) * qAlpha) * qMa2)) (7.207265513438204252816206e-1 : ℝ) (7.2072655134382042528162736e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- Row N17, iron-56 binding, atomic [MeV]. -/
noncomputable def rowN17 : ℝ :=
  (((((((((39 : ℝ) / 40) * qMa2) * (56 : ℝ)) - ((((13 : ℝ) / 12) * qMa2) * ((56 : ℝ) ^ (2 / 3 : ℝ)))) - ((((3 : ℝ) / 2) * qMa2) * ((2 : ℝ) / 7))) + ((((3 : ℝ) / 4) * qMa2) / (√(56 : ℝ)))) - ((qAC * (650 : ℝ)) / ((56 : ℝ) ^ (1 / 3 : ℝ)))) + ((((((qCTF * ((26 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((1767796497960077 : ℝ) / 5000000000000)) * ((1 : ℝ) / 1000000)))

theorem rowN17_bnd : Bnd rowN17 (5.0161288068541701164136988e2 : ℝ) (5.0161288068541701164137157e2 : ℝ) := by
  unfold rowN17
  have h1 : Bnd ((39 : ℝ) / 40) ((39 : ℝ) / 40) ((39 : ℝ) / 40) := Bnd.const _
  have h2 := Bnd.mul h1 qMa2_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((((39 : ℝ) / 40) * qMa2)) (1.5838214805829151776359609e1 : ℝ) (1.5838214805829151776359614e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (56 : ℝ) (56 : ℝ) (56 : ℝ) := Bnd.const _
  have h5 := Bnd.mul h3 h4 (by norm_num) (by norm_num)
  have h6 : Bnd (((((39 : ℝ) / 40) * qMa2) * (56 : ℝ))) (8.869400291264324994761381e2 : ℝ) (8.8694002912643249947613839e2 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 : Bnd ((13 : ℝ) / 12) ((13 : ℝ) / 12) ((13 : ℝ) / 12) := Bnd.const _
  have h8 := Bnd.mul h7 qMa2_bnd (by norm_num) (by norm_num)
  have h9 : Bnd ((((13 : ℝ) / 12) * qMa2)) (1.7598016450921279751510676e1 : ℝ) (1.7598016450921279751510682e1 : ℝ) := h8.weak (by norm_num) (by norm_num)
  have h10 : Bnd (56 : ℝ) (56 : ℝ) (56 : ℝ) := Bnd.const _
  have h11 : Bnd (((56 : ℝ) ^ (2 / 3 : ℝ))) (1.4637222840091886068952293e1 : ℝ) (1.4637222840091886068952294e1 : ℝ) := Bnd.rpow' (p := 2) (q := 3) h10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h12 := Bnd.mul h9 h11 (by norm_num) (by norm_num)
  have h13 : Bnd (((((13 : ℝ) / 12) * qMa2) * ((56 : ℝ) ^ (2 / 3 : ℝ)))) (2.5758608833573770757387453e2 : ℝ) (2.5758608833573770757387464e2 : ℝ) := h12.weak (by norm_num) (by norm_num)
  have h14 := Bnd.sub h6 h13
  have h15 : Bnd ((((((39 : ℝ) / 40) * qMa2) * (56 : ℝ)) - ((((13 : ℝ) / 12) * qMa2) * ((56 : ℝ) ^ (2 / 3 : ℝ))))) (6.2935394079069479190226346e2 : ℝ) (6.2935394079069479190226386e2 : ℝ) := h14.weak (by norm_num) (by norm_num)
  have h16 : Bnd ((3 : ℝ) / 2) ((3 : ℝ) / 2) ((3 : ℝ) / 2) := Bnd.const _
  have h17 := Bnd.mul h16 qMa2_bnd (by norm_num) (by norm_num)
  have h18 : Bnd ((((3 : ℝ) / 2) * qMa2)) (2.4366484316660233502091706e1 : ℝ) (2.4366484316660233502091713e1 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 : Bnd ((2 : ℝ) / 7) ((2 : ℝ) / 7) ((2 : ℝ) / 7) := Bnd.const _
  have h20 := Bnd.mul h18 h19 (by norm_num) (by norm_num)
  have h21 : Bnd (((((3 : ℝ) / 2) * qMa2) * ((2 : ℝ) / 7))) (6.9618526619029238577404874 : ℝ) (6.9618526619029238577404895 : ℝ) := h20.weak (by norm_num) (by norm_num)
  have h22 := Bnd.sub h15 h21
  have h23 : Bnd (((((((39 : ℝ) / 40) * qMa2) * (56 : ℝ)) - ((((13 : ℝ) / 12) * qMa2) * ((56 : ℝ) ^ (2 / 3 : ℝ)))) - ((((3 : ℝ) / 2) * qMa2) * ((2 : ℝ) / 7)))) (6.2239208812879186804452297e2 : ℝ) (6.2239208812879186804452338e2 : ℝ) := h22.weak (by norm_num) (by norm_num)
  have h24 : Bnd ((3 : ℝ) / 4) ((3 : ℝ) / 4) ((3 : ℝ) / 4) := Bnd.const _
  have h25 := Bnd.mul h24 qMa2_bnd (by norm_num) (by norm_num)
  have h26 : Bnd ((((3 : ℝ) / 4) * qMa2)) (1.2183242158330116751045853e1 : ℝ) (1.2183242158330116751045857e1 : ℝ) := h25.weak (by norm_num) (by norm_num)
  have h27 : Bnd (56 : ℝ) (56 : ℝ) (56 : ℝ) := Bnd.const _
  have h28 : Bnd ((√(56 : ℝ))) (7.4833147735478827711674974 : ℝ) (7.4833147735478827711674975 : ℝ) := Bnd.sqrt h27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h29 := Bnd.div h26 h28 (by norm_num) (by norm_num)
  have h30 : Bnd (((((3 : ℝ) / 4) * qMa2) / (√(56 : ℝ)))) (1.6280542148775563601683353 : ℝ) (1.628054214877556360168336 : ℝ) := h29.weak (by norm_num) (by norm_num)
  have h31 := Bnd.add h23 h30
  have h32 : Bnd ((((((((39 : ℝ) / 40) * qMa2) * (56 : ℝ)) - ((((13 : ℝ) / 12) * qMa2) * ((56 : ℝ) ^ (2 / 3 : ℝ)))) - ((((3 : ℝ) / 2) * qMa2) * ((2 : ℝ) / 7))) + ((((3 : ℝ) / 4) * qMa2) / (√(56 : ℝ))))) (6.240201423436694244046913e2 : ℝ) (6.2402014234366942440469172e2 : ℝ) := h31.weak (by norm_num) (by norm_num)
  have h33 : Bnd (650 : ℝ) (650 : ℝ) (650 : ℝ) := Bnd.const _
  have h34 := Bnd.mul qAC_bnd h33 (by norm_num) (by norm_num)
  have h35 : Bnd ((qAC * (650 : ℝ))) (4.6847225837348327643305339e2 : ℝ) (4.6847225837348327643305779e2 : ℝ) := h34.weak (by norm_num) (by norm_num)
  have h36 : Bnd (56 : ℝ) (56 : ℝ) (56 : ℝ) := Bnd.const _
  have h37 : Bnd (((56 : ℝ) ^ (1 / 3 : ℝ))) (3.8258623655447782023982336 : ℝ) (3.8258623655447782023982337 : ℝ) := Bnd.rpow' (p := 1) (q := 3) h36 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h38 := Bnd.div h35 h37 (by norm_num) (by norm_num)
  have h39 : Bnd (((qAC * (650 : ℝ)) / ((56 : ℝ) ^ (1 / 3 : ℝ)))) (1.2244880071810315604284044e2 : ℝ) (1.2244880071810315604284161e2 : ℝ) := h38.weak (by norm_num) (by norm_num)
  have h40 := Bnd.sub h32 h39
  have h41 : Bnd (((((((((39 : ℝ) / 40) * qMa2) * (56 : ℝ)) - ((((13 : ℝ) / 12) * qMa2) * ((56 : ℝ) ^ (2 / 3 : ℝ)))) - ((((3 : ℝ) / 2) * qMa2) * ((2 : ℝ) / 7))) + ((((3 : ℝ) / 4) * qMa2) / (√(56 : ℝ)))) - ((qAC * (650 : ℝ)) / ((56 : ℝ) ^ (1 / 3 : ℝ))))) (5.0157134162556626836184969e2 : ℝ) (5.0157134162556626836185128e2 : ℝ) := h40.weak (by norm_num) (by norm_num)
  have h42 : Bnd (26 : ℝ) (26 : ℝ) (26 : ℝ) := Bnd.const _
  have h43 : Bnd (((26 : ℝ) ^ (7 / 3 : ℝ))) (2.00264734224338246386299e3 : ℝ) (2.0026473422433824638629901e3 : ℝ) := Bnd.rpow' (p := 7) (q := 3) h42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h44 := Bnd.mul qCTF_bnd h43 (by norm_num) (by norm_num)
  have h45 : Bnd ((qCTF * ((26 : ℝ) ^ (7 / 3 : ℝ)))) (1.539525357948878860860077e3 : ℝ) (1.5395253579488788608633442e3 : ℝ) := h44.weak (by norm_num) (by norm_num)
  have h46 := Bnd.mul h45 qMe_bnd (by norm_num) (by norm_num)
  have h47 : Bnd (((qCTF * ((26 : ℝ) ^ (7 / 3 : ℝ))) * qMe)) (7.8669584247252374856142185e2 : ℝ) (7.866958424725237485630914e2 : ℝ) := h46.weak (by norm_num) (by norm_num)
  have h48 := Bnd.pow qAlpha_bnd (by norm_num) 2
  have h49 : Bnd ((qAlpha ^ 2)) (5.325135444808003103748339e-5 : ℝ) (5.3251354448080031037484361e-5 : ℝ) := h48.weak (by norm_num) (by norm_num)
  have h50 := Bnd.mul h47 h49 (by norm_num) (by norm_num)
  have h51 : Bnd ((((qCTF * ((26 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2))) (4.189261915033529492019885e-2 : ℝ) (4.1892619150335294920288521e-2 : ℝ) := h50.weak (by norm_num) (by norm_num)
  have h52 : Bnd (1000000 : ℝ) (1000000 : ℝ) (1000000 : ℝ) := Bnd.const _
  have h53 := Bnd.mul h51 h52 (by norm_num) (by norm_num)
  have h54 : Bnd (((((qCTF * ((26 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ))) (4.189261915033529492019885e4 : ℝ) (4.1892619150335294920288521e4 : ℝ) := h53.weak (by norm_num) (by norm_num)
  have h55 : Bnd ((1767796497960077 : ℝ) / 5000000000000) ((1767796497960077 : ℝ) / 5000000000000) ((1767796497960077 : ℝ) / 5000000000000) := Bnd.const _
  have h56 := Bnd.sub h54 h55
  have h57 : Bnd ((((((qCTF * ((26 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((1767796497960077 : ℝ) / 5000000000000))) (4.153905985074327952019885e4 : ℝ) (4.1539059850743279520288521e4 : ℝ) := h56.weak (by norm_num) (by norm_num)
  have h58 : Bnd ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) := Bnd.const _
  have h59 := Bnd.mul h57 h58 (by norm_num) (by norm_num)
  have h60 : Bnd (((((((qCTF * ((26 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((1767796497960077 : ℝ) / 5000000000000)) * ((1 : ℝ) / 1000000))) (4.153905985074327952019885e-2 : ℝ) (4.1539059850743279520288521e-2 : ℝ) := h59.weak (by norm_num) (by norm_num)
  have h61 := Bnd.add h41 h60
  have h62 : Bnd ((((((((((39 : ℝ) / 40) * qMa2) * (56 : ℝ)) - ((((13 : ℝ) / 12) * qMa2) * ((56 : ℝ) ^ (2 / 3 : ℝ)))) - ((((3 : ℝ) / 2) * qMa2) * ((2 : ℝ) / 7))) + ((((3 : ℝ) / 4) * qMa2) / (√(56 : ℝ)))) - ((qAC * (650 : ℝ)) / ((56 : ℝ) ^ (1 / 3 : ℝ)))) + ((((((qCTF * ((26 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((1767796497960077 : ℝ) / 5000000000000)) * ((1 : ℝ) / 1000000)))) (5.0161288068541701164136988e2 : ℝ) (5.0161288068541701164137157e2 : ℝ) := h61.weak (by norm_num) (by norm_num)
  exact h62

/-- **Row N17 to its printed digits, `501.612880685`.** -/
theorem rowN17_digits : (5.016128806845e2 : ℝ) < rowN17 ∧ rowN17 < (5.016128806855e2 : ℝ) :=
  rowN17_bnd.strict (by norm_num) (by norm_num)

/-- Row N18, nickel-62 binding, atomic [MeV]. -/
noncomputable def rowN18 : ℝ :=
  (((((((((39 : ℝ) / 40) * qMa2) * (62 : ℝ)) - ((((13 : ℝ) / 12) * qMa2) * ((62 : ℝ) ^ (2 / 3 : ℝ)))) - ((((3 : ℝ) / 2) * qMa2) * ((18 : ℝ) / 31))) + ((((3 : ℝ) / 4) * qMa2) / (√(62 : ℝ)))) - ((qAC * (756 : ℝ)) / ((62 : ℝ) ^ (1 / 3 : ℝ)))) + ((((((qCTF * ((28 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((951890421978503 : ℝ) / 2500000000000)) * ((1 : ℝ) / 1000000)))

theorem rowN18_bnd : Bnd rowN18 (5.5607990918567434753984346e2 : ℝ) (5.5607990918567434753984535e2 : ℝ) := by
  unfold rowN18
  have h1 : Bnd ((39 : ℝ) / 40) ((39 : ℝ) / 40) ((39 : ℝ) / 40) := Bnd.const _
  have h2 := Bnd.mul h1 qMa2_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((((39 : ℝ) / 40) * qMa2)) (1.5838214805829151776359609e1 : ℝ) (1.5838214805829151776359614e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (62 : ℝ) (62 : ℝ) (62 : ℝ) := Bnd.const _
  have h5 := Bnd.mul h3 h4 (by norm_num) (by norm_num)
  have h6 : Bnd (((((39 : ℝ) / 40) * qMa2) * (62 : ℝ))) (9.8196931796140741013429575e2 : ℝ) (9.8196931796140741013429607e2 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 : Bnd ((13 : ℝ) / 12) ((13 : ℝ) / 12) ((13 : ℝ) / 12) := Bnd.const _
  have h8 := Bnd.mul h7 qMa2_bnd (by norm_num) (by norm_num)
  have h9 : Bnd ((((13 : ℝ) / 12) * qMa2)) (1.7598016450921279751510676e1 : ℝ) (1.7598016450921279751510682e1 : ℝ) := h8.weak (by norm_num) (by norm_num)
  have h10 : Bnd (62 : ℝ) (62 : ℝ) (62 : ℝ) := Bnd.const _
  have h11 : Bnd (((62 : ℝ) ^ (2 / 3 : ℝ))) (1.5664905993978551153060968e1 : ℝ) (1.5664905993978551153060969e1 : ℝ) := Bnd.rpow' (p := 2) (q := 3) h10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h12 := Bnd.mul h9 h11 (by norm_num) (by norm_num)
  have h13 : Bnd (((((13 : ℝ) / 12) * qMa2) * ((62 : ℝ) ^ (2 / 3 : ℝ)))) (2.7567127338416990484030404e2 : ℝ) (2.7567127338416990484030416e2 : ℝ) := h12.weak (by norm_num) (by norm_num)
  have h14 := Bnd.sub h6 h13
  have h15 : Bnd ((((((39 : ℝ) / 40) * qMa2) * (62 : ℝ)) - ((((13 : ℝ) / 12) * qMa2) * ((62 : ℝ) ^ (2 / 3 : ℝ))))) (7.0629804457723750529399159e2 : ℝ) (7.0629804457723750529399203e2 : ℝ) := h14.weak (by norm_num) (by norm_num)
  have h16 : Bnd ((3 : ℝ) / 2) ((3 : ℝ) / 2) ((3 : ℝ) / 2) := Bnd.const _
  have h17 := Bnd.mul h16 qMa2_bnd (by norm_num) (by norm_num)
  have h18 : Bnd ((((3 : ℝ) / 2) * qMa2)) (2.4366484316660233502091706e1 : ℝ) (2.4366484316660233502091713e1 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 : Bnd ((18 : ℝ) / 31) ((18 : ℝ) / 31) ((18 : ℝ) / 31) := Bnd.const _
  have h20 := Bnd.mul h18 h19 (by norm_num) (by norm_num)
  have h21 : Bnd (((((3 : ℝ) / 2) * qMa2) * ((18 : ℝ) / 31))) (1.414828121612529687218228e1 : ℝ) (1.4148281216125296872182285e1 : ℝ) := h20.weak (by norm_num) (by norm_num)
  have h22 := Bnd.sub h15 h21
  have h23 : Bnd (((((((39 : ℝ) / 40) * qMa2) * (62 : ℝ)) - ((((13 : ℝ) / 12) * qMa2) * ((62 : ℝ) ^ (2 / 3 : ℝ)))) - ((((3 : ℝ) / 2) * qMa2) * ((18 : ℝ) / 31)))) (6.921497633611122084218093e2 : ℝ) (6.9214976336111220842180975e2 : ℝ) := h22.weak (by norm_num) (by norm_num)
  have h24 : Bnd ((3 : ℝ) / 4) ((3 : ℝ) / 4) ((3 : ℝ) / 4) := Bnd.const _
  have h25 := Bnd.mul h24 qMa2_bnd (by norm_num) (by norm_num)
  have h26 : Bnd ((((3 : ℝ) / 4) * qMa2)) (1.2183242158330116751045853e1 : ℝ) (1.2183242158330116751045857e1 : ℝ) := h25.weak (by norm_num) (by norm_num)
  have h27 : Bnd (62 : ℝ) (62 : ℝ) (62 : ℝ) := Bnd.const _
  have h28 : Bnd ((√(62 : ℝ))) (7.8740078740118110196850344 : ℝ) (7.8740078740118110196850345 : ℝ) := Bnd.sqrt h27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h29 := Bnd.div h26 h28 (by norm_num) (by norm_num)
  have h30 : Bnd (((((3 : ℝ) / 4) * qMa2) / (√(62 : ℝ)))) (1.5472733013819998468069987 : ℝ) (1.5472733013819998468069993 : ℝ) := h29.weak (by norm_num) (by norm_num)
  have h31 := Bnd.add h23 h30
  have h32 : Bnd ((((((((39 : ℝ) / 40) * qMa2) * (62 : ℝ)) - ((((13 : ℝ) / 12) * qMa2) * ((62 : ℝ) ^ (2 / 3 : ℝ)))) - ((((3 : ℝ) / 2) * qMa2) * ((18 : ℝ) / 31))) + ((((3 : ℝ) / 4) * qMa2) / (√(62 : ℝ))))) (6.9369703666249420826861629e2 : ℝ) (6.9369703666249420826861675e2 : ℝ) := h31.weak (by norm_num) (by norm_num)
  have h33 : Bnd (756 : ℝ) (756 : ℝ) (756 : ℝ) := Bnd.const _
  have h34 := Bnd.mul qAC_bnd h33 (by norm_num) (by norm_num)
  have h35 : Bnd ((qAC * (756 : ℝ))) (5.4486927281592824151290517e2 : ℝ) (5.4486927281592824151291029e2 : ℝ) := h34.weak (by norm_num) (by norm_num)
  have h36 : Bnd (62 : ℝ) (62 : ℝ) (62 : ℝ) := Bnd.const _
  have h37 : Bnd (((62 : ℝ) ^ (1 / 3 : ℝ))) (3.9578916096804054789361484 : ℝ) (3.9578916096804054789361485 : ℝ) := Bnd.rpow' (p := 1) (q := 3) h36 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h38 := Bnd.div h35 h37 (by norm_num) (by norm_num)
  have h39 : Bnd (((qAC * (756 : ℝ)) / ((62 : ℝ) ^ (1 / 3 : ℝ)))) (1.3766654738175756050830608e2 : ℝ) (1.3766654738175756050830739e2 : ℝ) := h38.weak (by norm_num) (by norm_num)
  have h40 := Bnd.sub h32 h39
  have h41 : Bnd (((((((((39 : ℝ) / 40) * qMa2) * (62 : ℝ)) - ((((13 : ℝ) / 12) * qMa2) * ((62 : ℝ) ^ (2 / 3 : ℝ)))) - ((((3 : ℝ) / 2) * qMa2) * ((18 : ℝ) / 31))) + ((((3 : ℝ) / 4) * qMa2) / (√(62 : ℝ)))) - ((qAC * (756 : ℝ)) / ((62 : ℝ) ^ (1 / 3 : ℝ))))) (5.560304892807366477603089e2 : ℝ) (5.5603048928073664776031067e2 : ℝ) := h40.weak (by norm_num) (by norm_num)
  have h42 : Bnd (28 : ℝ) (28 : ℝ) (28 : ℝ) := Bnd.const _
  have h43 : Bnd (((28 : ℝ) ^ (7 / 3 : ℝ))) (2.3806857539505194152259147e3 : ℝ) (2.3806857539505194152259148e3 : ℝ) := Bnd.rpow' (p := 7) (q := 3) h42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h44 := Bnd.mul qCTF_bnd h43 (by norm_num) (by norm_num)
  have h45 : Bnd ((qCTF * ((28 : ℝ) ^ (7 / 3 : ℝ)))) (1.830140539576361336012925e3 : ℝ) (1.830140539576361336016809e3 : ℝ) := h44.weak (by norm_num) (by norm_num)
  have h46 := Bnd.mul h45 qMe_bnd (by norm_num) (by norm_num)
  have h47 : Bnd (((qCTF * ((28 : ℝ) ^ (7 / 3 : ℝ))) * qMe)) (9.3519989533875105983089118e2 : ℝ) (9.3519989533875105983287591e2 : ℝ) := h46.weak (by norm_num) (by norm_num)
  have h48 := Bnd.pow qAlpha_bnd (by norm_num) 2
  have h49 : Bnd ((qAlpha ^ 2)) (5.325135444808003103748339e-5 : ℝ) (5.3251354448080031037484361e-5 : ℝ) := h48.weak (by norm_num) (by norm_num)
  have h50 := Bnd.mul h47 h49 (by norm_num) (by norm_num)
  have h51 : Bnd ((((qCTF * ((28 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2))) (4.9800661106491180734568759e-2 : ℝ) (4.9800661106491180734675357e-2 : ℝ) := h50.weak (by norm_num) (by norm_num)
  have h52 : Bnd (1000000 : ℝ) (1000000 : ℝ) (1000000 : ℝ) := Bnd.const _
  have h53 := Bnd.mul h51 h52 (by norm_num) (by norm_num)
  have h54 : Bnd (((((qCTF * ((28 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ))) (4.9800661106491180734568759e4 : ℝ) (4.9800661106491180734675357e4 : ℝ) := h53.weak (by norm_num) (by norm_num)
  have h55 : Bnd ((951890421978503 : ℝ) / 2500000000000) ((951890421978503 : ℝ) / 2500000000000) ((951890421978503 : ℝ) / 2500000000000) := Bnd.const _
  have h56 := Bnd.sub h54 h55
  have h57 : Bnd ((((((qCTF * ((28 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((951890421978503 : ℝ) / 2500000000000))) (4.9419904937699779534568759e4 : ℝ) (4.9419904937699779534675357e4 : ℝ) := h56.weak (by norm_num) (by norm_num)
  have h58 : Bnd ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) := Bnd.const _
  have h59 := Bnd.mul h57 h58 (by norm_num) (by norm_num)
  have h60 : Bnd (((((((qCTF * ((28 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((951890421978503 : ℝ) / 2500000000000)) * ((1 : ℝ) / 1000000))) (4.9419904937699779534568759e-2 : ℝ) (4.9419904937699779534675357e-2 : ℝ) := h59.weak (by norm_num) (by norm_num)
  have h61 := Bnd.add h41 h60
  have h62 : Bnd ((((((((((39 : ℝ) / 40) * qMa2) * (62 : ℝ)) - ((((13 : ℝ) / 12) * qMa2) * ((62 : ℝ) ^ (2 / 3 : ℝ)))) - ((((3 : ℝ) / 2) * qMa2) * ((18 : ℝ) / 31))) + ((((3 : ℝ) / 4) * qMa2) / (√(62 : ℝ)))) - ((qAC * (756 : ℝ)) / ((62 : ℝ) ^ (1 / 3 : ℝ)))) + ((((((qCTF * ((28 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((951890421978503 : ℝ) / 2500000000000)) * ((1 : ℝ) / 1000000)))) (5.5607990918567434753984346e2 : ℝ) (5.5607990918567434753984535e2 : ℝ) := h61.weak (by norm_num) (by norm_num)
  exact h62

/-- **Row N18 to its printed digits, `556.079909186`.** -/
theorem rowN18_digits : (5.560799091855e2 : ℝ) < rowN18 ∧ rowN18 < (5.560799091865e2 : ℝ) :=
  rowN18_bnd.strict (by norm_num) (by norm_num)

/-- Row N19, lead-208 binding, atomic [MeV]. -/
noncomputable def rowN19 : ℝ :=
  (((((((((39 : ℝ) / 40) * qMa2) * (208 : ℝ)) - ((((13 : ℝ) / 12) * qMa2) * ((208 : ℝ) ^ (2 / 3 : ℝ)))) - ((((3 : ℝ) / 2) * qMa2) * ((121 : ℝ) / 13))) + ((((3 : ℝ) / 4) * qMa2) / (√(208 : ℝ)))) - ((qAC * (6642 : ℝ)) / ((208 : ℝ) ^ (1 / 3 : ℝ)))) + ((((((qCTF * ((82 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((5575358185874089 : ℝ) / 5000000000000)) * ((1 : ℝ) / 1000000)))

theorem rowN19_bnd : Bnd rowN19 (1.6432752766996815107687659e3 : ℝ) (1.6432752766996815107687768e3 : ℝ) := by
  unfold rowN19
  have h1 : Bnd ((39 : ℝ) / 40) ((39 : ℝ) / 40) ((39 : ℝ) / 40) := Bnd.const _
  have h2 := Bnd.mul h1 qMa2_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((((39 : ℝ) / 40) * qMa2)) (1.5838214805829151776359609e1 : ℝ) (1.5838214805829151776359614e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (208 : ℝ) (208 : ℝ) (208 : ℝ) := Bnd.const _
  have h5 := Bnd.mul h3 h4 (by norm_num) (by norm_num)
  have h6 : Bnd (((((39 : ℝ) / 40) * qMa2) * (208 : ℝ))) (3.2943486796124635694827986e3 : ℝ) (3.2943486796124635694827998e3 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 : Bnd ((13 : ℝ) / 12) ((13 : ℝ) / 12) ((13 : ℝ) / 12) := Bnd.const _
  have h8 := Bnd.mul h7 qMa2_bnd (by norm_num) (by norm_num)
  have h9 : Bnd ((((13 : ℝ) / 12) * qMa2)) (1.7598016450921279751510676e1 : ℝ) (1.7598016450921279751510682e1 : ℝ) := h8.weak (by norm_num) (by norm_num)
  have h10 : Bnd (208 : ℝ) (208 : ℝ) (208 : ℝ) := Bnd.const _
  have h11 : Bnd (((208 : ℝ) ^ (2 / 3 : ℝ))) (3.5105531821316510737968655e1 : ℝ) (3.5105531821316510737968656e1 : ℝ) := Bnd.rpow' (p := 2) (q := 3) h10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h12 := Bnd.mul h9 h11 (by norm_num) (by norm_num)
  have h13 : Bnd (((((13 : ℝ) / 12) * qMa2) * ((208 : ℝ) ^ (2 / 3 : ℝ)))) (6.1778772650986843225636663e2 : ℝ) (6.1778772650986843225636687e2 : ℝ) := h12.weak (by norm_num) (by norm_num)
  have h14 := Bnd.sub h6 h13
  have h15 : Bnd ((((((39 : ℝ) / 40) * qMa2) * (208 : ℝ)) - ((((13 : ℝ) / 12) * qMa2) * ((208 : ℝ) ^ (2 / 3 : ℝ))))) (2.6765609531025951372264317e3 : ℝ) (2.6765609531025951372264332e3 : ℝ) := h14.weak (by norm_num) (by norm_num)
  have h16 : Bnd ((3 : ℝ) / 2) ((3 : ℝ) / 2) ((3 : ℝ) / 2) := Bnd.const _
  have h17 := Bnd.mul h16 qMa2_bnd (by norm_num) (by norm_num)
  have h18 : Bnd ((((3 : ℝ) / 2) * qMa2)) (2.4366484316660233502091706e1 : ℝ) (2.4366484316660233502091713e1 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 : Bnd ((121 : ℝ) / 13) ((121 : ℝ) / 13) ((121 : ℝ) / 13) := Bnd.const _
  have h20 := Bnd.mul h18 h19 (by norm_num) (by norm_num)
  have h21 : Bnd (((((3 : ℝ) / 2) * qMa2) * ((121 : ℝ) / 13))) (2.2679573863968371182716126e2 : ℝ) (2.2679573863968371182716133e2 : ℝ) := h20.weak (by norm_num) (by norm_num)
  have h22 := Bnd.sub h15 h21
  have h23 : Bnd (((((((39 : ℝ) / 40) * qMa2) * (208 : ℝ)) - ((((13 : ℝ) / 12) * qMa2) * ((208 : ℝ) ^ (2 / 3 : ℝ)))) - ((((3 : ℝ) / 2) * qMa2) * ((121 : ℝ) / 13)))) (2.4497652144629114253992703e3 : ℝ) (2.449765214462911425399272e3 : ℝ) := h22.weak (by norm_num) (by norm_num)
  have h24 : Bnd ((3 : ℝ) / 4) ((3 : ℝ) / 4) ((3 : ℝ) / 4) := Bnd.const _
  have h25 := Bnd.mul h24 qMa2_bnd (by norm_num) (by norm_num)
  have h26 : Bnd ((((3 : ℝ) / 4) * qMa2)) (1.2183242158330116751045853e1 : ℝ) (1.2183242158330116751045857e1 : ℝ) := h25.weak (by norm_num) (by norm_num)
  have h27 : Bnd (208 : ℝ) (208 : ℝ) (208 : ℝ) := Bnd.const _
  have h28 : Bnd ((√(208 : ℝ))) (1.4422205101855957172476885e1 : ℝ) (1.4422205101855957172476886e1 : ℝ) := Bnd.sqrt h27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h29 := Bnd.div h26 h28 (by norm_num) (by norm_num)
  have h30 : Bnd (((((3 : ℝ) / 4) * qMa2) / (√(208 : ℝ)))) (8.4475585198564996614569454e-1 : ℝ) (8.4475585198564996614569489e-1 : ℝ) := h29.weak (by norm_num) (by norm_num)
  have h31 := Bnd.add h23 h30
  have h32 : Bnd ((((((((39 : ℝ) / 40) * qMa2) * (208 : ℝ)) - ((((13 : ℝ) / 12) * qMa2) * ((208 : ℝ) ^ (2 / 3 : ℝ)))) - ((((3 : ℝ) / 2) * qMa2) * ((121 : ℝ) / 13))) + ((((3 : ℝ) / 4) * qMa2) / (√(208 : ℝ))))) (2.4506099703148970753654159e3 : ℝ) (2.4506099703148970753654177e3 : ℝ) := h31.weak (by norm_num) (by norm_num)
  have h33 : Bnd (6642 : ℝ) (6642 : ℝ) (6642 : ℝ) := Bnd.const _
  have h34 := Bnd.mul qAC_bnd h33 (by norm_num) (by norm_num)
  have h35 : Bnd ((qAC * (6642 : ℝ))) (4.787065754025655264720524e3 : ℝ) (4.787065754025655264720569e3 : ℝ) := h34.weak (by norm_num) (by norm_num)
  have h36 : Bnd (208 : ℝ) (208 : ℝ) (208 : ℝ) := Bnd.const _
  have h37 : Bnd (((208 : ℝ) ^ (1 / 3 : ℝ))) (5.9249921368147410173461243 : ℝ) (5.9249921368147410173461244 : ℝ) := Bnd.rpow' (p := 1) (q := 3) h36 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h38 := Bnd.div h35 h37 (by norm_num) (by norm_num)
  have h39 : Bnd (((qAC * (6642 : ℝ)) / ((208 : ℝ) ^ (1 / 3 : ℝ)))) (8.0794465941674114163718112e2 : ℝ) (8.0794465941674114163718874e2 : ℝ) := h38.weak (by norm_num) (by norm_num)
  have h40 := Bnd.sub h32 h39
  have h41 : Bnd (((((((((39 : ℝ) / 40) * qMa2) * (208 : ℝ)) - ((((13 : ℝ) / 12) * qMa2) * ((208 : ℝ) ^ (2 / 3 : ℝ)))) - ((((3 : ℝ) / 2) * qMa2) * ((121 : ℝ) / 13))) + ((((3 : ℝ) / 4) * qMa2) / (√(208 : ℝ)))) - ((qAC * (6642 : ℝ)) / ((208 : ℝ) ^ (1 / 3 : ℝ))))) (1.6426653108981559337282271e3 : ℝ) (1.6426653108981559337282366e3 : ℝ) := h40.weak (by norm_num) (by norm_num)
  have h42 : Bnd (82 : ℝ) (82 : ℝ) (82 : ℝ) := Bnd.const _
  have h43 : Bnd (((82 : ℝ) ^ (7 / 3 : ℝ))) (2.9212293510308146427181085e4 : ℝ) (2.9212293510308146427181086e4 : ℝ) := Bnd.rpow' (p := 7) (q := 3) h42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h44 := Bnd.mul qCTF_bnd h43 (by norm_num) (by norm_num)
  have h45 : Bnd ((qCTF * ((82 : ℝ) ^ (7 / 3 : ℝ)))) (2.2456807883401803084072653e4 : ℝ) (2.2456807883401803084120311e4 : ℝ) := h44.weak (by norm_num) (by norm_num)
  have h46 := Bnd.mul h45 qMe_bnd (by norm_num) (by norm_num)
  have h47 : Bnd (((qCTF * ((82 : ℝ) ^ (7 / 3 : ℝ))) * qMe)) (1.1475405264265241243615131e4 : ℝ) (1.1475405264265241243639485e4 : ℝ) := h46.weak (by norm_num) (by norm_num)
  have h48 := Bnd.pow qAlpha_bnd (by norm_num) 2
  have h49 : Bnd ((qAlpha ^ 2)) (5.325135444808003103748339e-5 : ℝ) (5.3251354448080031037484361e-5 : ℝ) := h48.weak (by norm_num) (by norm_num)
  have h50 := Bnd.mul h47 h49 (by norm_num) (by norm_num)
  have h51 : Bnd ((((qCTF * ((82 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2))) (6.1108087316275185833881916e-1 : ℝ) (6.1108087316275185834012719e-1 : ℝ) := h50.weak (by norm_num) (by norm_num)
  have h52 : Bnd (1000000 : ℝ) (1000000 : ℝ) (1000000 : ℝ) := Bnd.const _
  have h53 := Bnd.mul h51 h52 (by norm_num) (by norm_num)
  have h54 : Bnd (((((qCTF * ((82 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ))) (6.1108087316275185833881916e5 : ℝ) (6.1108087316275185834012719e5 : ℝ) := h53.weak (by norm_num) (by norm_num)
  have h55 : Bnd ((5575358185874089 : ℝ) / 5000000000000) ((5575358185874089 : ℝ) / 5000000000000) ((5575358185874089 : ℝ) / 5000000000000) := Bnd.const _
  have h56 := Bnd.sub h54 h55
  have h57 : Bnd ((((((qCTF * ((82 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((5575358185874089 : ℝ) / 5000000000000))) (6.0996580152557704053881916e5 : ℝ) (6.0996580152557704054012719e5 : ℝ) := h56.weak (by norm_num) (by norm_num)
  have h58 : Bnd ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) := Bnd.const _
  have h59 := Bnd.mul h57 h58 (by norm_num) (by norm_num)
  have h60 : Bnd (((((((qCTF * ((82 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((5575358185874089 : ℝ) / 5000000000000)) * ((1 : ℝ) / 1000000))) (6.0996580152557704053881916e-1 : ℝ) (6.0996580152557704054012719e-1 : ℝ) := h59.weak (by norm_num) (by norm_num)
  have h61 := Bnd.add h41 h60
  have h62 : Bnd ((((((((((39 : ℝ) / 40) * qMa2) * (208 : ℝ)) - ((((13 : ℝ) / 12) * qMa2) * ((208 : ℝ) ^ (2 / 3 : ℝ)))) - ((((3 : ℝ) / 2) * qMa2) * ((121 : ℝ) / 13))) + ((((3 : ℝ) / 4) * qMa2) / (√(208 : ℝ)))) - ((qAC * (6642 : ℝ)) / ((208 : ℝ) ^ (1 / 3 : ℝ)))) + ((((((qCTF * ((82 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((5575358185874089 : ℝ) / 5000000000000)) * ((1 : ℝ) / 1000000)))) (1.6432752766996815107687659e3 : ℝ) (1.6432752766996815107687768e3 : ℝ) := h61.weak (by norm_num) (by norm_num)
  exact h62

/-- **Row N19 to its printed digits, `1643.2752767`.** -/
theorem rowN19_digits : (1.64327527665e3 : ℝ) < rowN19 ∧ rowN19 < (1.64327527675e3 : ℝ) :=
  rowN19_bnd.strict (by norm_num) (by norm_num)

/-- Row N20, uranium-238 binding, atomic [MeV]. -/
noncomputable def rowN20 : ℝ :=
  (((((((((39 : ℝ) / 40) * qMa2) * (238 : ℝ)) - ((((13 : ℝ) / 12) * qMa2) * ((238 : ℝ) ^ (2 / 3 : ℝ)))) - ((((3 : ℝ) / 2) * qMa2) * ((1458 : ℝ) / 119))) + ((((3 : ℝ) / 4) * qMa2) / (√(238 : ℝ)))) - ((qAC * (8372 : ℝ)) / ((238 : ℝ) ^ (1 / 3 : ℝ)))) + ((((((qCTF * ((92 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((3127639957929367 : ℝ) / 2500000000000)) * ((1 : ℝ) / 1000000)))

theorem rowN20_bnd : Bnd rowN20 (1.8230351038987562217304646e3 : ℝ) (1.8230351038987562217304775e3 : ℝ) := by
  unfold rowN20
  have h1 : Bnd ((39 : ℝ) / 40) ((39 : ℝ) / 40) ((39 : ℝ) / 40) := Bnd.const _
  have h2 := Bnd.mul h1 qMa2_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((((39 : ℝ) / 40) * qMa2)) (1.5838214805829151776359609e1 : ℝ) (1.5838214805829151776359614e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (238 : ℝ) (238 : ℝ) (238 : ℝ) := Bnd.const _
  have h5 := Bnd.mul h3 h4 (by norm_num) (by norm_num)
  have h6 : Bnd (((((39 : ℝ) / 40) * qMa2) * (238 : ℝ))) (3.7694951237873381227735869e3 : ℝ) (3.7694951237873381227735882e3 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 : Bnd ((13 : ℝ) / 12) ((13 : ℝ) / 12) ((13 : ℝ) / 12) := Bnd.const _
  have h8 := Bnd.mul h7 qMa2_bnd (by norm_num) (by norm_num)
  have h9 : Bnd ((((13 : ℝ) / 12) * qMa2)) (1.7598016450921279751510676e1 : ℝ) (1.7598016450921279751510682e1 : ℝ) := h8.weak (by norm_num) (by norm_num)
  have h10 : Bnd (238 : ℝ) (238 : ℝ) (238 : ℝ) := Bnd.const _
  have h11 : Bnd (((238 : ℝ) ^ (2 / 3 : ℝ))) (3.8404723088031607975766775e1 : ℝ) (3.8404723088031607975766776e1 : ℝ) := Bnd.rpow' (p := 2) (q := 3) h10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h12 := Bnd.mul h9 h11 (by norm_num) (by norm_num)
  have h13 : Bnd (((((13 : ℝ) / 12) * qMa2) * ((238 : ℝ) ^ (2 / 3 : ℝ)))) (6.7584694869625652902087298e2 : ℝ) (6.7584694869625652902087324e2 : ℝ) := h12.weak (by norm_num) (by norm_num)
  have h14 := Bnd.sub h6 h13
  have h15 : Bnd ((((((39 : ℝ) / 40) * qMa2) * (238 : ℝ)) - ((((13 : ℝ) / 12) * qMa2) * ((238 : ℝ) ^ (2 / 3 : ℝ))))) (3.0936481750910815937527136e3 : ℝ) (3.0936481750910815937527153e3 : ℝ) := h14.weak (by norm_num) (by norm_num)
  have h16 : Bnd ((3 : ℝ) / 2) ((3 : ℝ) / 2) ((3 : ℝ) / 2) := Bnd.const _
  have h17 := Bnd.mul h16 qMa2_bnd (by norm_num) (by norm_num)
  have h18 : Bnd ((((3 : ℝ) / 2) * qMa2)) (2.4366484316660233502091706e1 : ℝ) (2.4366484316660233502091713e1 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 : Bnd ((1458 : ℝ) / 119) ((1458 : ℝ) / 119) ((1458 : ℝ) / 119) := Bnd.const _
  have h20 := Bnd.mul h18 h19 (by norm_num) (by norm_num)
  have h21 : Bnd (((((3 : ℝ) / 2) * qMa2) * ((1458 : ℝ) / 119))) (2.9854062297219008778193031e2 : ℝ) (2.985406229721900877819304e2 : ℝ) := h20.weak (by norm_num) (by norm_num)
  have h22 := Bnd.sub h15 h21
  have h23 : Bnd (((((((39 : ℝ) / 40) * qMa2) * (238 : ℝ)) - ((((13 : ℝ) / 12) * qMa2) * ((238 : ℝ) ^ (2 / 3 : ℝ)))) - ((((3 : ℝ) / 2) * qMa2) * ((1458 : ℝ) / 119)))) (2.7951075521188915059707832e3 : ℝ) (2.795107552118891505970785e3 : ℝ) := h22.weak (by norm_num) (by norm_num)
  have h24 : Bnd ((3 : ℝ) / 4) ((3 : ℝ) / 4) ((3 : ℝ) / 4) := Bnd.const _
  have h25 := Bnd.mul h24 qMa2_bnd (by norm_num) (by norm_num)
  have h26 : Bnd ((((3 : ℝ) / 4) * qMa2)) (1.2183242158330116751045853e1 : ℝ) (1.2183242158330116751045857e1 : ℝ) := h25.weak (by norm_num) (by norm_num)
  have h27 : Bnd (238 : ℝ) (238 : ℝ) (238 : ℝ) := Bnd.const _
  have h28 : Bnd ((√(238 : ℝ))) (1.542724862054151248907878e1 : ℝ) (1.5427248620541512489078781e1 : ℝ) := Bnd.sqrt h27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h29 := Bnd.div h26 h28 (by norm_num) (by norm_num)
  have h30 : Bnd (((((3 : ℝ) / 4) * qMa2) / (√(238 : ℝ)))) (7.8972229319672896192528525e-1 : ℝ) (7.8972229319672896192528557e-1 : ℝ) := h29.weak (by norm_num) (by norm_num)
  have h31 := Bnd.add h23 h30
  have h32 : Bnd ((((((((39 : ℝ) / 40) * qMa2) * (238 : ℝ)) - ((((13 : ℝ) / 12) * qMa2) * ((238 : ℝ) ^ (2 / 3 : ℝ)))) - ((((3 : ℝ) / 2) * qMa2) * ((1458 : ℝ) / 119))) + ((((3 : ℝ) / 4) * qMa2) / (√(238 : ℝ))))) (2.7958972744120882349327084e3 : ℝ) (2.7958972744120882349327103e3 : ℝ) := h31.weak (by norm_num) (by norm_num)
  have h33 : Bnd (8372 : ℝ) (8372 : ℝ) (8372 : ℝ) := Bnd.const _
  have h34 := Bnd.mul qAC_bnd h33 (by norm_num) (by norm_num)
  have h35 : Bnd ((qAC * (8372 : ℝ))) (6.0339226878504646004577276e3 : ℝ) (6.0339226878504646004577843e3 : ℝ) := h34.weak (by norm_num) (by norm_num)
  have h36 : Bnd (238 : ℝ) (238 : ℝ) (238 : ℝ) := Bnd.const _
  have h37 : Bnd (((238 : ℝ) ^ (1 / 3 : ℝ))) (6.1971544347411262472999642 : ℝ) (6.1971544347411262472999643 : ℝ) := Bnd.rpow' (p := 1) (q := 3) h36 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h38 := Bnd.div h35 h37 (by norm_num) (by norm_num)
  have h39 : Bnd (((qAC * (8372 : ℝ)) / ((238 : ℝ) ^ (1 / 3 : ℝ)))) (9.7366020992222048325555361e2 : ℝ) (9.7366020992222048325556279e2 : ℝ) := h38.weak (by norm_num) (by norm_num)
  have h40 := Bnd.sub h32 h39
  have h41 : Bnd (((((((((39 : ℝ) / 40) * qMa2) * (238 : ℝ)) - ((((13 : ℝ) / 12) * qMa2) * ((238 : ℝ) ^ (2 / 3 : ℝ)))) - ((((3 : ℝ) / 2) * qMa2) * ((1458 : ℝ) / 119))) + ((((3 : ℝ) / 4) * qMa2) / (√(238 : ℝ)))) - ((qAC * (8372 : ℝ)) / ((238 : ℝ) ^ (1 / 3 : ℝ))))) (1.8222370644898677516771456e3 : ℝ) (1.8222370644898677516771567e3 : ℝ) := h40.weak (by norm_num) (by norm_num)
  have h42 : Bnd (92 : ℝ) (92 : ℝ) (92 : ℝ) := Bnd.const _
  have h43 : Bnd (((92 : ℝ) ^ (7 / 3 : ℝ))) (3.820952133385194767562301e4 : ℝ) (3.8209521333851947675623011e4 : ℝ) := Bnd.rpow' (p := 7) (q := 3) h42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h44 := Bnd.mul qCTF_bnd h43 (by norm_num) (by norm_num)
  have h45 : Bnd ((qCTF * ((92 : ℝ) ^ (7 / 3 : ℝ)))) (2.9373382805710570647484702e4 : ℝ) (2.9373382805710570647547038e4 : ℝ) := h44.weak (by norm_num) (by norm_num)
  have h46 := Bnd.mul h45 qMe_bnd (by norm_num) (by norm_num)
  have h47 : Bnd (((qCTF * ((92 : ℝ) ^ (7 / 3 : ℝ))) * qMe)) (1.5009767791933789740705796e4 : ℝ) (1.5009767791933789740737651e4 : ℝ) := h46.weak (by norm_num) (by norm_num)
  have h48 := Bnd.pow qAlpha_bnd (by norm_num) 2
  have h49 : Bnd ((qAlpha ^ 2)) (5.325135444808003103748339e-5 : ℝ) (5.3251354448080031037484361e-5 : ℝ) := h48.weak (by norm_num) (by norm_num)
  have h50 := Bnd.mul h47 h49 (by norm_num) (by norm_num)
  have h51 : Bnd ((((qCTF * ((92 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2))) (7.9929046487164180011900358e-1 : ℝ) (7.9929046487164180012071449e-1 : ℝ) := h50.weak (by norm_num) (by norm_num)
  have h52 : Bnd (1000000 : ℝ) (1000000 : ℝ) (1000000 : ℝ) := Bnd.const _
  have h53 := Bnd.mul h51 h52 (by norm_num) (by norm_num)
  have h54 : Bnd (((((qCTF * ((92 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ))) (7.9929046487164180011900358e5 : ℝ) (7.9929046487164180012071449e5 : ℝ) := h53.weak (by norm_num) (by norm_num)
  have h55 : Bnd ((3127639957929367 : ℝ) / 2500000000000) ((3127639957929367 : ℝ) / 2500000000000) ((3127639957929367 : ℝ) / 2500000000000) := Bnd.const _
  have h56 := Bnd.sub h54 h55
  have h57 : Bnd ((((((qCTF * ((92 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((3127639957929367 : ℝ) / 2500000000000))) (7.9803940888847005331900358e5 : ℝ) (7.9803940888847005332071449e5 : ℝ) := h56.weak (by norm_num) (by norm_num)
  have h58 : Bnd ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000000) := Bnd.const _
  have h59 := Bnd.mul h57 h58 (by norm_num) (by norm_num)
  have h60 : Bnd (((((((qCTF * ((92 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((3127639957929367 : ℝ) / 2500000000000)) * ((1 : ℝ) / 1000000))) (7.9803940888847005331900358e-1 : ℝ) (7.9803940888847005332071449e-1 : ℝ) := h59.weak (by norm_num) (by norm_num)
  have h61 := Bnd.add h41 h60
  have h62 : Bnd ((((((((((39 : ℝ) / 40) * qMa2) * (238 : ℝ)) - ((((13 : ℝ) / 12) * qMa2) * ((238 : ℝ) ^ (2 / 3 : ℝ)))) - ((((3 : ℝ) / 2) * qMa2) * ((1458 : ℝ) / 119))) + ((((3 : ℝ) / 4) * qMa2) / (√(238 : ℝ)))) - ((qAC * (8372 : ℝ)) / ((238 : ℝ) ^ (1 / 3 : ℝ)))) + ((((((qCTF * ((92 : ℝ) ^ (7 / 3 : ℝ))) * qMe) * (qAlpha ^ 2)) * (1000000 : ℝ)) - ((3127639957929367 : ℝ) / 2500000000000)) * ((1 : ℝ) / 1000000)))) (1.8230351038987562217304646e3 : ℝ) (1.8230351038987562217304775e3 : ℝ) := h61.weak (by norm_num) (by norm_num)
  exact h62

/-- **Row N20 to its printed digits, `1823.0351039`.** -/
theorem rowN20_digits : (1.82303510385e3 : ℝ) < rowN20 ∧ rowN20 < (1.82303510395e3 : ℝ) :=
  rowN20_bnd.strict (by norm_num) (by norm_num)

/-- `r₀ = k_C |u| λ_p/a` in fm. -/
noncomputable def qR0 : ℝ :=
  ((((3 : ℝ) / 4) * qLp) / ((5 : ℝ) / 38))

theorem qR0_bnd : Bnd qR0 (1.1987607873032538848410903 : ℝ) (1.1987607873032538848449065 : ℝ) := by
  unfold qR0
  have h1 : Bnd ((3 : ℝ) / 4) ((3 : ℝ) / 4) ((3 : ℝ) / 4) := Bnd.const _
  have h2 := Bnd.mul h1 qLp_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((((3 : ℝ) / 4) * qLp)) (1.5773168253990182695277504e-1 : ℝ) (1.5773168253990182695327716e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd ((5 : ℝ) / 38) ((5 : ℝ) / 38) ((5 : ℝ) / 38) := Bnd.const _
  have h5 := Bnd.div h3 h4 (by norm_num) (by norm_num)
  have h6 : Bnd (((((3 : ℝ) / 4) * qLp) / ((5 : ℝ) / 38))) (1.1987607873032538848410903 : ℝ) (1.1987607873032538848449065 : ℝ) := h5.weak (by norm_num) (by norm_num)
  exact h6

/-- Row N21, saturation density `n_0` [fm`^{-3}`]. -/
noncomputable def rowN21 : ℝ :=
  ((3 : ℝ) / (((4 : ℝ) * π) * (qR0 ^ 3)))

theorem rowN21_bnd : Bnd rowN21 (1.3858422766596652819749225e-1 : ℝ) (1.3858422766596652819925693e-1 : ℝ) := by
  unfold rowN21
  have h1 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h2 : Bnd (4 : ℝ) (4 : ℝ) (4 : ℝ) := Bnd.const _
  have h3 := Bnd.mul h2 bnd_pi (by norm_num) (by norm_num)
  have h4 : Bnd (((4 : ℝ) * π)) (1.256637061435917295384e1 : ℝ) (1.256637061435917295388e1 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 := Bnd.pow qR0_bnd (by norm_num) 3
  have h6 : Bnd ((qR0 ^ 3)) (1.7226521275802501460273969 : ℝ) (1.722652127580250146043849 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.mul h4 h6 (by norm_num) (by norm_num)
  have h8 : Bnd ((((4 : ℝ) * π) * (qR0 ^ 3))) (2.1647485074787764414909648e1 : ℝ) (2.1647485074787764415185298e1 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 := Bnd.div h1 h8 (by norm_num) (by norm_num)
  have h10 : Bnd (((3 : ℝ) / (((4 : ℝ) * π) * (qR0 ^ 3)))) (1.3858422766596652819749225e-1 : ℝ) (1.3858422766596652819925693e-1 : ℝ) := h9.weak (by norm_num) (by norm_num)
  exact h10

/-- **Row N21 to its printed digits, `0.138584227666`.** -/
theorem rowN21_digits : (1.385842276655e-1 : ℝ) < rowN21 ∧ rowN21 < (1.385842276665e-1 : ℝ) :=
  rowN21_bnd.strict (by norm_num) (by norm_num)

/-- Row N22, saturation energy `e_0` [MeV]. -/
noncomputable def rowN22 : ℝ :=
  (-(((39 : ℝ) / 40) * qMa2))

theorem rowN22_bnd : Bnd rowN22 (-1.5838214805829151776359614e1 : ℝ) (-1.5838214805829151776359609e1 : ℝ) := by
  unfold rowN22
  have h1 : Bnd ((39 : ℝ) / 40) ((39 : ℝ) / 40) ((39 : ℝ) / 40) := Bnd.const _
  have h2 := Bnd.mul h1 qMa2_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((((39 : ℝ) / 40) * qMa2)) (1.5838214805829151776359609e1 : ℝ) (1.5838214805829151776359614e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.neg h3
  have h5 : Bnd ((-(((39 : ℝ) / 40) * qMa2))) (-1.5838214805829151776359614e1 : ℝ) (-1.5838214805829151776359609e1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- **Row N22 to its printed digits, `-15.8382148058`.** -/
theorem rowN22_digits : (-1.583821480585e1 : ℝ) < rowN22 ∧ rowN22 < (-1.583821480575e1 : ℝ) :=
  rowN22_bnd.strict (by norm_num) (by norm_num)

end Comparison.Article
