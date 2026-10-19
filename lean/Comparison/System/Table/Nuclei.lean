import Comparison.System.Table.Hadrons

set_option linter.style.longLine false

/-!
# The proof system, the table, part 7: the nuclei

Rows M1 to M6, N01 to N22, S13 of Table X (Prop. 125, Eq. (50)).

The light nuclei follow the incidence polynomial
`B(A, Z) = B_d[C(A, 2) + τ₃C(A, 3) + (k_C + τ₃)C(A, 4)] − (αm_p/V_C)C(Z, 2)`, `τ₃ = χ_A Var Q/Eℓ = 13/16`,
`V_C = Var P − Cov²/Var Q = 9`; the alpha-cluster nuclei of `n` clusters carry `χ_AB_d` on each edge of their
rigid frame, `B(4n, 2n) = nB_α + β_nχ_AB_d + Δ_at`; the heavy nuclei the bulk coefficients
`m_pa²(1 − t/Eℓ, χ_A, e/t, k_C/4, 4α/(5a))` of volume, surface, symmetry, pairing and Coulomb energy; the saturation
point `n₀ = 3/(4πr₀³)`, `r₀ = k_C|u|λ_p/a`, and `e₀ = −m_pa²(1 − t/Eℓ)`.

Recognitions: M1 to M6 the proton, neutron, deuteron, triton, helion and alpha nuclear masses [MeV], N01 to N03 the
triton, helion and helium-4 bindings [MeV], N04 to N20 the atomic bindings of the nuclei they name [MeV], N21 the
saturation density [fm⁻³], N22 the saturation energy [MeV], S13 neon-20's eight-bond construction. The incidence
expansion, the cluster bonds `β_n` (a table here; the rigid frame's rank `3n − 6`, or the contacts where fewer, on
the A₃ lattice, completes Prop. 125) and the bulk expansion are the theory's compositions (C); the atomic term
`Δ_at(Z) = E_TF(Z) − Z I_H` carries the classical Thomas–Fermi constant `1.588071` and the hydrogen binding
`I_H = 13.5984345996929 eV` (outside inputs).
-/

namespace Comparison.System.Table

open Real Complex Matrix Comparison Comparison.Law Comparison.System.Completion

namespace Row

/-- `τ₃ = χ_A Var Q/Eℓ` and `V_C = Var P − Cov²/Var Q`. -/
noncomputable def tau3 : ℝ := Num.chiA * Num.VarQ / Num.El
noncomputable def VC : ℝ := Num.VarP - Num.Cov ^ 2 / Num.VarQ

/-- **The incidence polynomial** `B(A, Z)` [MeV] (Eq. (50)). -/
noncomputable def Binc (A Z : ℕ) : ℝ :=
  G10 * ((A.choose 2 : ℝ) + tau3 * (A.choose 3 : ℝ) + ((Num.kC : ℝ) + tau3) * (A.choose 4 : ℝ)) -
    Num.alpha * Num.mp / VC * (Z.choose 2 : ℝ)

/-- `I_H = 13.5984345996929 eV`, the hydrogen binding, and the Thomas–Fermi constant `3·1.588071/(3.5(3π/4)^{2/3})`.
Outside inputs. -/
noncomputable def IH : ℝ := 135984345996929 / 10000000000000
noncomputable def TF : ℝ := (4764213 / 3500000) / ((3 / 4 * π) ^ (2 / 3 : ℝ))

/-- **The atomic term** `Δ_at(Z) = E_TF(Z) − Z I_H` [MeV], `E_TF(Z) = TF·Z^{7/3}m_eα²`. -/
noncomputable def atomic (Z : ℝ) : ℝ :=
  (TF * Z ^ (7 / 3 : ℝ) * Num.me * Num.alpha ^ 2 * 1000000 - Z * IH) * (1 / 1000000)

/-- **The alpha-cluster nuclei** `B(4n, 2n) = nB_α + β_nχ_AB_d + Δ_at(2n)` [MeV]. -/
noncomputable def cluster (n : ℕ) : ℝ :=
  (n : ℝ) * Binc 4 2 + Article.betaC n * Num.chiA * G10 + atomic (2 * n)

/-- **The bulk coefficients** `(a_V, a_S, a_A, a_P, a_C) = m_pa²(1 − t/Eℓ, χ_A, e/t, k_C/4, 4α/(5a))` and the bulk
binding at even `A`, even `Z` [MeV]. -/
noncomputable def ma2 : ℝ := Num.mp * Num.a ^ 2
noncomputable def bulk (A Z : ℝ) : ℝ :=
  (1 - Num.t / Num.El) * ma2 * A - Num.chiA * ma2 * A ^ (2 / 3 : ℝ) -
    Num.e / Num.t * ma2 * ((A - 2 * Z) ^ 2 / A) + (Num.kC : ℝ) / 4 * ma2 / √A -
    4 * Num.alpha / (5 * Num.a) * ma2 * (Z * (Z - 1)) / A ^ (1 / 3 : ℝ)

/-- M1, M2, M3 [MeV]. -/
noncomputable def M1 : ℝ := Num.mp
noncomputable def M2 : ℝ := mn
noncomputable def M3 : ℝ := G11
/-- M4, M5, M6: `m_p + 2m_n − B(3, 1)`, `2m_p + m_n − B(3, 2)`, `2m_p + 2m_n − B(4, 2)` [MeV]. -/
noncomputable def M4 : ℝ := Num.mp + 2 * mn - Binc 3 1
noncomputable def M5 : ℝ := 2 * Num.mp + mn - Binc 3 2
noncomputable def M6 : ℝ := 2 * Num.mp + 2 * mn - Binc 4 2
/-- N01, N02, N03: `B(3, 1)`, `B(3, 2)`, `B(4, 2)` [MeV]. -/
noncomputable def N01 : ℝ := Binc 3 1
noncomputable def N02 : ℝ := Binc 3 2
noncomputable def N03 : ℝ := Binc 4 2
/-- N17 to N20: `B_bulk(A, Z) + Δ_at(Z)` [MeV]. -/
noncomputable def N17 : ℝ := bulk 56 26 + atomic 26
noncomputable def N18 : ℝ := bulk 62 28 + atomic 28
noncomputable def N19 : ℝ := bulk 208 82 + atomic 82
noncomputable def N20 : ℝ := bulk 238 92 + atomic 92
/-- N21, `n₀ = 3/(4πr₀³)`, `r₀ = k_C|u@{}|λ_p/a` [fm⁻³]; N22, `e₀ = −m_pa²(1 − t/Eℓ)` [MeV]. -/
noncomputable def r0 : ℝ := (Num.kC : ℝ) * ‖uS sHere‖ * Num.lp / Num.a
noncomputable def N21 : ℝ := 3 / (4 * π * r0 ^ 3)
noncomputable def N22 : ℝ := -((1 - Num.t / Num.El) * ma2)

/-- N04, `B(4n, 2n)` at n = 2 [MeV]. -/
noncomputable def N04 : ℝ := cluster 2
/-- N05, `B(4n, 2n)` at n = 3 [MeV]. -/
noncomputable def N05 : ℝ := cluster 3
/-- N06, `B(4n, 2n)` at n = 4 [MeV]. -/
noncomputable def N06 : ℝ := cluster 4
/-- N07, `B(4n, 2n)` at n = 5 [MeV]. -/
noncomputable def N07 : ℝ := cluster 5
/-- N08, `B(4n, 2n)` at n = 6 [MeV]. -/
noncomputable def N08 : ℝ := cluster 6
/-- N09, `B(4n, 2n)` at n = 7 [MeV]. -/
noncomputable def N09 : ℝ := cluster 7
/-- N10, `B(4n, 2n)` at n = 8 [MeV]. -/
noncomputable def N10 : ℝ := cluster 8
/-- N11, `B(4n, 2n)` at n = 9 [MeV]. -/
noncomputable def N11 : ℝ := cluster 9
/-- N12, `B(4n, 2n)` at n = 10 [MeV]. -/
noncomputable def N12 : ℝ := cluster 10
/-- N13, `B(4n, 2n)` at n = 11 [MeV]. -/
noncomputable def N13 : ℝ := cluster 11
/-- N14, `B(4n, 2n)` at n = 12 [MeV]. -/
noncomputable def N14 : ℝ := cluster 12
/-- N15, `B(4n, 2n)` at n = 13 [MeV]. -/
noncomputable def N15 : ℝ := cluster 13
/-- N16, `B(4n, 2n)` at n = 14 [MeV]. -/
noncomputable def N16 : ℝ := cluster 14
/-- S13, neon-20's eight-bond construction (as N07). -/
noncomputable def S13 : ℝ := N07

end Row

theorem VC_eq : Row.VC = 9 := by rw [Row.VC, Num.VarP_eq, Num.Cov_eq, Num.VarQ_eq]; norm_num

theorem tau3_eq : Row.tau3 = 13 / 16 := by
  rw [Row.tau3, Num.chiA_eq, Num.VarQ_eq, Num.El_eq]; norm_num

theorem coul_eq_q : Num.alpha * Num.mp / Row.VC = Article.qCoul := by
  rw [Num.alpha_eq_q, Num.mp_eq_q, VC_eq, Article.qCoul]

theorem Binc_eq (A Z : ℕ) : Row.Binc A Z = Article.incPoly Article.qBd Article.qCoul A Z := by
  rw [Row.Binc, G10_eq_q, tau3_eq, Num.kC_eq, coul_eq_q, Article.incPoly]; norm_num

theorem N01_eq_q : Row.N01 = Article.qBt := by
  rw [Row.N01, Binc_eq]; exact (Article.incidence_light).2.1

theorem N02_eq_q : Row.N02 = Article.qBh := by
  rw [Row.N02, Binc_eq]; exact (Article.incidence_light).2.2.1

theorem N03_eq_q : Row.N03 = Article.qBa := by
  rw [Row.N03, Binc_eq]; exact (Article.incidence_light).2.2.2.1

theorem TF_eq_q : Row.TF = Article.qCTF := by rw [Row.TF, Article.qCTF]

theorem atomic_eq (Z : ℝ) : Row.atomic Z = Article.atomicCorr Z (Z * Row.IH) := by
  rw [Row.atomic, TF_eq_q, Num.me_eq_q, Num.alpha_eq_q, Article.atomicCorr]

theorem cluster_eq (n : ℕ) : Row.cluster n =
    (n : ℝ) * Article.qBa + Article.betaC n * (13 / 12) * Article.qBd +
      Article.atomicCorr (2 * n) ((2 * n : ℝ) * Row.IH) := by
  rw [Row.cluster, show Row.Binc 4 2 = Row.N03 from rfl, N03_eq_q, Num.chiA_eq, G10_eq_q, atomic_eq]

theorem ma2_eq_q : Row.ma2 = Article.qMa2 := by
  rw [Row.ma2, Num.mp_eq_q, Num.a_eq, Article.qMa2]; norm_num

theorem r0_eq_q : Row.r0 = Article.qR0 := by
  rw [Row.r0, Num.kC_eq, table_here.2.2.2.1, Num.lp_eq_q, Num.a_eq, Article.qR0]; norm_num

end Comparison.System.Table

namespace Comparison.System

open Real Complex Matrix Comparison Comparison.Law Comparison.System.Completion Comparison.System.Table

/-- **Row M1.** `m_e(m_p/m_e) = 938.27208942 MeV`. Recognition: the proton mass. -/
theorem row_M1 : (938.272089415 : ℝ) < Table.Row.M1 ∧ Table.Row.M1 < 938.272089425 := by
  rw [Table.Row.M1, Num.mp_eq_q]; exact Article.rowM1_digits

/-- **Row M2.** `m_p(m_n/m_p) = 939.565422025 MeV`. Recognition: the neutron mass. -/
theorem row_M2 : (939.5654220245 : ℝ) < Table.Row.M2 ∧ Table.Row.M2 < 939.5654220255 := by
  rw [Table.Row.M2, mn_eq_q]; exact Article.rowM2_digits

/-- **Row M3.** As G11. Recognition: the deuteron nuclear mass. -/
theorem row_M3 : (1875.612944975 : ℝ) < Table.Row.M3 ∧ Table.Row.M3 < 1875.612944985 := by
  rw [Table.Row.M3, G11_eq_q]; exact Article.rowM3_digits

/-- **Row M4.** `m_p + 2m_n − B(3, 1) = 2808.92177383 MeV`. Recognition: the triton nuclear mass. -/
theorem row_M4 : (2808.921773825 : ℝ) < Table.Row.M4 ∧ Table.Row.M4 < 2808.921773835 := by
  rw [Table.Row.M4, Num.mp_eq_q, mn_eq_q, show Table.Row.Binc 3 1 = Table.Row.N01 from rfl, N01_eq_q]
  exact Article.rowM4_digits

/-- **Row M5.** `2m_p + m_n − B(3, 2) = 2808.38920814 MeV`. Recognition: the helion nuclear mass. -/
theorem row_M5 : (2808.389208135 : ℝ) < Table.Row.M5 ∧ Table.Row.M5 < 2808.389208145 := by
  rw [Table.Row.M5, Num.mp_eq_q, mn_eq_q, show Table.Row.Binc 3 2 = Table.Row.N02 from rfl, N02_eq_q]
  exact Article.rowM5_digits

/-- **Row M6.** `2m_p + 2m_n − B(4, 2) = 3727.37739038 MeV`. Recognition: the alpha nuclear mass. -/
theorem row_M6 : (3727.377390375 : ℝ) < Table.Row.M6 ∧ Table.Row.M6 < 3727.377390385 := by
  rw [Table.Row.M6, Num.mp_eq_q, mn_eq_q, show Table.Row.Binc 4 2 = Table.Row.N03 from rfl, N03_eq_q]
  exact Article.rowM6_digits

/-- **Row N01.** `B(3, 1) = (61/16)B_d = 8.48115964057 MeV`. Recognition: the triton binding. -/
theorem row_N01 : (8.481159640565 : ℝ) < Table.Row.N01 ∧ Table.Row.N01 < 8.481159640575 := by
  rw [N01_eq_q]; exact (Article.incidence_light).2.2.2.2.2.1

/-- **Row N02.** `B(3, 2) = (61/16)B_d − αm_p/9 = 7.72039272526 MeV`. Recognition: the helion binding. -/
theorem row_N02 : (7.720392725255 : ℝ) < Table.Row.N02 ∧ Table.Row.N02 < 7.720392725265 := by
  rw [N02_eq_q]; exact (Article.incidence_light).2.2.2.2.2.2.1

/-- **Row N03.** `B(4, 2) = (209/16)B_d − αm_p/9 = 28.2976325089 MeV`. Recognition: the helium-4 binding. -/
theorem row_N03 : (28.29763250885 : ℝ) < Table.Row.N03 ∧ Table.Row.N03 < 28.29763250895 := by
  rw [N03_eq_q]; exact (Article.incidence_light).2.2.2.2.2.2.2

/-- **Row N04.** `2B_α + β_2χ_AB_d + Δ_at(4) = 56.5957419239 MeV`. Recognition: the beryllium-8 atomic binding. -/
theorem row_N04 : Table.Row.N04 = Table.Row.cluster 2 ∧
    (5.659574192385e1 : ℝ) < Table.Row.N04 ∧ Table.Row.N04 < 5.659574192395e1 := by
  refine ⟨rfl, ?_⟩
  have e : Table.Row.N04 = Article.rowN04 := by
    rw [Table.Row.N04, cluster_eq, (Article.cluster_bonds.1)]
    norm_num [Table.Row.IH]
  rw [e]; exact Article.rowN04_digits

/-- **Row N05.** `3B_α + β_3χ_AB_d + Δ_at(6) = 92.1240253608 MeV`. Recognition: the carbon-12 atomic binding. -/
theorem row_N05 : Table.Row.N05 = Table.Row.cluster 3 ∧
    (9.212402536075e1 : ℝ) < Table.Row.N05 ∧ Table.Row.N05 < 9.212402536085e1 := by
  refine ⟨rfl, ?_⟩
  have e : Table.Row.N05 = Article.rowN05 := by
    rw [Table.Row.N05, cluster_eq, (Article.cluster_bonds.2.1)]
    norm_num [Table.Row.IH]
  rw [e]; exact Article.rowN05_digits

/-- **Row N06.** `4B_α + β_4χ_AB_d + Δ_at(8) = 127.652780842 MeV`. Recognition: the oxygen-16 atomic binding. -/
theorem row_N06 : Table.Row.N06 = Table.Row.cluster 4 ∧
    (1.276527808415e2 : ℝ) < Table.Row.N06 ∧ Table.Row.N06 < 1.276527808425e2 := by
  refine ⟨rfl, ?_⟩
  have e : Table.Row.N06 = Article.rowN06 := by
    rw [Table.Row.N06, cluster_eq, (Article.cluster_bonds.2.2.1)]
    norm_num [Table.Row.IH]
  rw [e]; exact Article.rowN06_digits

/-- **Row N07.** `5B_α + β_5χ_AB_d + Δ_at(10) = 160.772109354 MeV`. Recognition: the neon-20 atomic binding. -/
theorem row_N07 : Table.Row.N07 = Table.Row.cluster 5 ∧
    (1.607721093535e2 : ℝ) < Table.Row.N07 ∧ Table.Row.N07 < 1.607721093545e2 := by
  refine ⟨rfl, ?_⟩
  have e : Table.Row.N07 = Article.rowN07 := by
    rw [Table.Row.N07, cluster_eq, (Article.cluster_bonds.2.2.2.1)]
    norm_num [Table.Row.IH]
  rw [e]; exact Article.rowN07_digits

/-- **Row N08.** `6B_α + β_6χ_AB_d + Δ_at(12) = 198.711892295 MeV`. Recognition: the magnesium-24 atomic binding. -/
theorem row_N08 : Table.Row.N08 = Table.Row.cluster 6 ∧
    (1.987118922945e2 : ℝ) < Table.Row.N08 ∧ Table.Row.N08 < 1.987118922955e2 := by
  refine ⟨rfl, ?_⟩
  have e : Table.Row.N08 = Article.rowN08 := by
    rw [Table.Row.N08, cluster_eq, (Article.cluster_bonds.2.2.2.2.1)]
    norm_num [Table.Row.IH]
  rw [e]; exact Article.rowN08_digits

/-- **Row N09.** `7B_α + β_7χ_AB_d + Δ_at(14) = 234.242323912 MeV`. Recognition: the silicon-28 atomic binding. -/
theorem row_N09 : Table.Row.N09 = Table.Row.cluster 7 ∧
    (2.342423239115e2 : ℝ) < Table.Row.N09 ∧ Table.Row.N09 < 2.342423239125e2 := by
  refine ⟨rfl, ?_⟩
  have e : Table.Row.N09 = Article.rowN09 := by
    rw [Table.Row.N09, cluster_eq, (Article.cluster_bonds.2.2.2.2.2.1)]
    norm_num [Table.Row.IH]
  rw [e]; exact Article.rowN09_digits

/-- **Row N10.** `8B_α + β_8χ_AB_d + Δ_at(16) = 269.773382702 MeV`. Recognition: the sulfur-32 atomic binding. -/
theorem row_N10 : Table.Row.N10 = Table.Row.cluster 8 ∧
    (2.697733827015e2 : ℝ) < Table.Row.N10 ∧ Table.Row.N10 < 2.697733827025e2 := by
  refine ⟨rfl, ?_⟩
  have e : Table.Row.N10 = Article.rowN10 := by
    rw [Table.Row.N10, cluster_eq, (Article.cluster_bonds.2.2.2.2.2.2.1)]
    norm_num [Table.Row.IH]
  rw [e]; exact Article.rowN10_digits

/-- **Row N11.** `9B_α + β_9χ_AB_d + Δ_at(18) = 305.305097267 MeV`. Recognition: the argon-36 atomic binding. -/
theorem row_N11 : Table.Row.N11 = Table.Row.cluster 9 ∧
    (3.053050972665e2 : ℝ) < Table.Row.N11 ∧ Table.Row.N11 < 3.053050972675e2 := by
  refine ⟨rfl, ?_⟩
  have e : Table.Row.N11 = Article.rowN11 := by
    rw [Table.Row.N11, cluster_eq, (Article.cluster_bonds.2.2.2.2.2.2.2.1)]
    norm_num [Table.Row.IH]
  rw [e]; exact Article.rowN11_digits

/-- **Row N12.** `10B_α + β_10χ_AB_d + Δ_at(20) = 340.83749391 MeV`. Recognition: the calcium-40 atomic binding. -/
theorem row_N12 : Table.Row.N12 = Table.Row.cluster 10 ∧
    (3.40837493905e2 : ℝ) < Table.Row.N12 ∧ Table.Row.N12 < 3.40837493915e2 := by
  refine ⟨rfl, ?_⟩
  have e : Table.Row.N12 = Article.rowN12 := by
    rw [Table.Row.N12, cluster_eq, (Article.cluster_bonds.2.2.2.2.2.2.2.2.1)]
    norm_num [Table.Row.IH]
  rw [e]; exact Article.rowN12_digits

/-- **Row N13.** `11B_α + β_11χ_AB_d + Δ_at(22) = 376.37059704 MeV`. Recognition: the titanium-44 atomic binding. -/
theorem row_N13 : Table.Row.N13 = Table.Row.cluster 11 ∧
    (3.76370597035e2 : ℝ) < Table.Row.N13 ∧ Table.Row.N13 < 3.76370597045e2 := by
  refine ⟨rfl, ?_⟩
  have e : Table.Row.N13 = Article.rowN13 := by
    rw [Table.Row.N13, cluster_eq, (Article.cluster_bonds.2.2.2.2.2.2.2.2.2.1)]
    norm_num [Table.Row.IH]
  rw [e]; exact Article.rowN13_digits

/-- **Row N14.** `12B_α + β_12χ_AB_d + Δ_at(24) = 411.904429487 MeV`. Recognition: the chromium-48 atomic binding. -/
theorem row_N14 : Table.Row.N14 = Table.Row.cluster 12 ∧
    (4.119044294865e2 : ℝ) < Table.Row.N14 ∧ Table.Row.N14 < 4.119044294875e2 := by
  refine ⟨rfl, ?_⟩
  have e : Table.Row.N14 = Article.rowN14 := by
    rw [Table.Row.N14, cluster_eq, (Article.cluster_bonds.2.2.2.2.2.2.2.2.2.2.1)]
    norm_num [Table.Row.IH]
  rw [e]; exact Article.rowN14_digits

/-- **Row N15.** `13B_α + β_13χ_AB_d + Δ_at(26) = 447.439012732 MeV`. Recognition: the iron-52 atomic binding. -/
theorem row_N15 : Table.Row.N15 = Table.Row.cluster 13 ∧
    (4.474390127315e2 : ℝ) < Table.Row.N15 ∧ Table.Row.N15 < 4.474390127325e2 := by
  refine ⟨rfl, ?_⟩
  have e : Table.Row.N15 = Article.rowN15 := by
    rw [Table.Row.N15, cluster_eq, (Article.cluster_bonds.2.2.2.2.2.2.2.2.2.2.2.1)]
    norm_num [Table.Row.IH]
  rw [e]; exact Article.rowN15_digits

/-- **Row N16.** `14B_α + β_14χ_AB_d + Δ_at(28) = 482.974367091 MeV`. Recognition: the nickel-56 atomic binding. -/
theorem row_N16 : Table.Row.N16 = Table.Row.cluster 14 ∧
    (4.829743670905e2 : ℝ) < Table.Row.N16 ∧ Table.Row.N16 < 4.829743670915e2 := by
  refine ⟨rfl, ?_⟩
  have e : Table.Row.N16 = Article.rowN16 := by
    rw [Table.Row.N16, cluster_eq, (Article.cluster_bonds.2.2.2.2.2.2.2.2.2.2.2.2)]
    norm_num [Table.Row.IH]
  rw [e]; exact Article.rowN16_digits

/-- **Row N17.** `B_bulk(56, 26) + Δ_at(26)`. Recognition: the iron-56 atomic binding. -/
theorem row_N17 : Table.Row.N17 = Table.Row.bulk 56 26 + Table.Row.atomic 26 ∧
    (5.016128806845e2 : ℝ) < Table.Row.N17 ∧ Table.Row.N17 < 5.016128806855e2 := by
  refine ⟨rfl, ?_⟩
  have e : Table.Row.N17 = Article.rowN17 := by
    rw [Table.Row.N17, Table.Row.bulk, atomic_eq, ma2_eq_q, Num.t_eq, Num.El_eq, Num.chiA_eq, Num.e_eq,
      Num.kC_eq, Num.alpha_eq_q, Num.a_eq, Article.rowN17, Article.qAC, Article.atomicCorr]
    norm_num [Table.Row.IH]
    ring_nf
    all_goals simp
  rw [e]; exact Article.rowN17_digits

/-- **Row N18.** `B_bulk(62, 28) + Δ_at(28)`. Recognition: the nickel-62 atomic binding. -/
theorem row_N18 : Table.Row.N18 = Table.Row.bulk 62 28 + Table.Row.atomic 28 ∧
    (5.560799091855e2 : ℝ) < Table.Row.N18 ∧ Table.Row.N18 < 5.560799091865e2 := by
  refine ⟨rfl, ?_⟩
  have e : Table.Row.N18 = Article.rowN18 := by
    rw [Table.Row.N18, Table.Row.bulk, atomic_eq, ma2_eq_q, Num.t_eq, Num.El_eq, Num.chiA_eq, Num.e_eq,
      Num.kC_eq, Num.alpha_eq_q, Num.a_eq, Article.rowN18, Article.qAC, Article.atomicCorr]
    norm_num [Table.Row.IH]
    ring_nf
    all_goals simp
  rw [e]; exact Article.rowN18_digits

/-- **Row N19.** `B_bulk(208, 82) + Δ_at(82)`. Recognition: the lead-208 atomic binding. -/
theorem row_N19 : Table.Row.N19 = Table.Row.bulk 208 82 + Table.Row.atomic 82 ∧
    (1.64327527665e3 : ℝ) < Table.Row.N19 ∧ Table.Row.N19 < 1.64327527675e3 := by
  refine ⟨rfl, ?_⟩
  have e : Table.Row.N19 = Article.rowN19 := by
    rw [Table.Row.N19, Table.Row.bulk, atomic_eq, ma2_eq_q, Num.t_eq, Num.El_eq, Num.chiA_eq, Num.e_eq,
      Num.kC_eq, Num.alpha_eq_q, Num.a_eq, Article.rowN19, Article.qAC, Article.atomicCorr]
    norm_num [Table.Row.IH]
    ring_nf
    all_goals simp
  rw [e]; exact Article.rowN19_digits

/-- **Row N20.** `B_bulk(238, 92) + Δ_at(92)`. Recognition: the uranium-238 atomic binding. -/
theorem row_N20 : Table.Row.N20 = Table.Row.bulk 238 92 + Table.Row.atomic 92 ∧
    (1.82303510385e3 : ℝ) < Table.Row.N20 ∧ Table.Row.N20 < 1.82303510395e3 := by
  refine ⟨rfl, ?_⟩
  have e : Table.Row.N20 = Article.rowN20 := by
    rw [Table.Row.N20, Table.Row.bulk, atomic_eq, ma2_eq_q, Num.t_eq, Num.El_eq, Num.chiA_eq, Num.e_eq,
      Num.kC_eq, Num.alpha_eq_q, Num.a_eq, Article.rowN20, Article.qAC, Article.atomicCorr]
    norm_num [Table.Row.IH]
    ring_nf
    all_goals simp
  rw [e]; exact Article.rowN20_digits

/-- **Row N21.** `n₀ = 3/(4πr₀³)`, `r₀ = k_C|u@{}|λ_p/a = 3λ_p/(4a)`: `0.138584227666 fm⁻³`. Recognition: the
saturation density. -/
theorem row_N21 : Table.Row.N21 = 3 / (4 * π * Table.Row.r0 ^ 3) ∧
    (0.1385842276655 : ℝ) < Table.Row.N21 ∧ Table.Row.N21 < 0.1385842276665 := by
  refine ⟨rfl, ?_⟩
  rw [Table.Row.N21, r0_eq_q]; exact Article.rowN21_digits

/-- **Row N22.** `e₀ = −m_pa²(1 − t/Eℓ) = −(39/40)m_pa² = −15.8382148058 MeV`. Recognition: the saturation
energy. -/
theorem row_N22 : Table.Row.N22 = -(39 / 40 * Table.Row.ma2) ∧
    (-15.83821480585 : ℝ) < Table.Row.N22 ∧ Table.Row.N22 < -15.83821480575 := by
  have e : Table.Row.N22 = -(39 / 40 * Table.Row.ma2) := by
    rw [Table.Row.N22, Num.t_eq, Num.El_eq]; norm_num
  refine ⟨e, ?_⟩
  rw [e, ma2_eq_q]; exact Article.rowN22_digits

/-- **Row S13.** As N07. Recognition: neon-20, eight-bond construction. -/
theorem row_S13 : Table.Row.S13 = Table.Row.N07 ∧
    (160.7721093535 : ℝ) < Table.Row.S13 ∧ Table.Row.S13 < 160.7721093545 := ⟨rfl, row_N07.2⟩

end Comparison.System
