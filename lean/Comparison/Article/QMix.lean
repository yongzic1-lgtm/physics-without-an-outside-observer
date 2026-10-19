import Comparison.Article.QCosmos

/-!
# The closed forms of the mixing rows

The cosines and sines of the quark and lepton frames, and every mixing row's real and imaginary parts as
polynomials in them (expanded from the entries `ckmV_eq`, `pmnsU_eq` of `Mixing.lean`), each with a closed
interval; the rows' closed forms with their printed digits.
-/

namespace Comparison.Article

open Real

/-- `c₁₂ = (1 − s₁₂²)^{1/2}`. -/
noncomputable def qc12 : ℝ :=
  (√((1 : ℝ) - (((9 : ℝ) / 40) ^ 2)))

theorem qc12_bnd : Bnd qc12 (9.7435876349525383637090747e-1 : ℝ) (9.7435876349525383637090748e-1 : ℝ) := by
  unfold qc12
  have h1 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h2 : Bnd ((9 : ℝ) / 40) ((9 : ℝ) / 40) ((9 : ℝ) / 40) := Bnd.const _
  have h3 := Bnd.pow h2 (by norm_num) 2
  have h4 : Bnd ((((9 : ℝ) / 40) ^ 2)) (5.0625e-2 : ℝ) (5.0625e-2 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 := Bnd.sub h1 h4
  have h6 : Bnd (((1 : ℝ) - (((9 : ℝ) / 40) ^ 2))) (9.49375e-1 : ℝ) (9.49375e-1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 : Bnd ((√((1 : ℝ) - (((9 : ℝ) / 40) ^ 2)))) (9.7435876349525383637090747e-1 : ℝ) (9.7435876349525383637090748e-1 : ℝ) := Bnd.sqrt h6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h7

/-- `c₂₃`. -/
noncomputable def qc23 : ℝ :=
  (√((1 : ℝ) - (((1 : ℝ) / 24) ^ 2)))

theorem qc23_bnd : Bnd qc23 (9.9913156735681657116613292e-1 : ℝ) (9.9913156735681657116613294e-1 : ℝ) := by
  unfold qc23
  have h1 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h2 : Bnd ((1 : ℝ) / 24) ((1 : ℝ) / 24) ((1 : ℝ) / 24) := Bnd.const _
  have h3 := Bnd.pow h2 (by norm_num) 2
  have h4 : Bnd ((((1 : ℝ) / 24) ^ 2)) (1.7361111111111111111111111e-3 : ℝ) (1.7361111111111111111111112e-3 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 := Bnd.sub h1 h4
  have h6 : Bnd (((1 : ℝ) - (((1 : ℝ) / 24) ^ 2))) (9.9826388888888888888888888e-1 : ℝ) (9.9826388888888888888888889e-1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 : Bnd ((√((1 : ℝ) - (((1 : ℝ) / 24) ^ 2)))) (9.9913156735681657116613292e-1 : ℝ) (9.9913156735681657116613294e-1 : ℝ) := Bnd.sqrt h6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h7

/-- `c₁₃`. -/
noncomputable def qc13 : ℝ :=
  (√((1 : ℝ) - (((3 : ℝ) / 800) ^ 2)))

theorem qc13_bnd : Bnd qc13 (9.9999296872528058791007821e-1 : ℝ) (9.9999296872528058791007822e-1 : ℝ) := by
  unfold qc13
  have h1 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h2 : Bnd ((3 : ℝ) / 800) ((3 : ℝ) / 800) ((3 : ℝ) / 800) := Bnd.const _
  have h3 := Bnd.pow h2 (by norm_num) 2
  have h4 : Bnd ((((3 : ℝ) / 800) ^ 2)) (1.40625e-5 : ℝ) (1.40625e-5 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 := Bnd.sub h1 h4
  have h6 : Bnd (((1 : ℝ) - (((3 : ℝ) / 800) ^ 2))) (9.999859375e-1 : ℝ) (9.999859375e-1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 : Bnd ((√((1 : ℝ) - (((3 : ℝ) / 800) ^ 2)))) (9.9999296872528058791007821e-1 : ℝ) (9.9999296872528058791007822e-1 : ℝ) := Bnd.sqrt h6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h7

/-- `cos δ_q = 7/√305`. -/
noncomputable def qcdq : ℝ :=
  ((7 : ℝ) / (√(305 : ℝ)))

theorem qcdq_bnd : Bnd qcdq (4.0081883401970775253851574e-1 : ℝ) (4.0081883401970775253851577e-1 : ℝ) := by
  unfold qcdq
  have h1 : Bnd (7 : ℝ) (7 : ℝ) (7 : ℝ) := Bnd.const _
  have h2 : Bnd (305 : ℝ) (305 : ℝ) (305 : ℝ) := Bnd.const _
  have h3 : Bnd ((√(305 : ℝ))) (1.7464249196572980646321043e1 : ℝ) (1.7464249196572980646321044e1 : ℝ) := Bnd.sqrt h2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h4 := Bnd.div h1 h3 (by norm_num) (by norm_num)
  have h5 : Bnd (((7 : ℝ) / (√(305 : ℝ)))) (4.0081883401970775253851574e-1 : ℝ) (4.0081883401970775253851577e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- `sin δ_q = 16/√305`. -/
noncomputable def qsdq : ℝ :=
  ((16 : ℝ) / (√(305 : ℝ)))

theorem qsdq_bnd : Bnd qsdq (9.1615733490218914865946456e-1 : ℝ) (9.1615733490218914865946462e-1 : ℝ) := by
  unfold qsdq
  have h1 : Bnd (16 : ℝ) (16 : ℝ) (16 : ℝ) := Bnd.const _
  have h2 : Bnd (305 : ℝ) (305 : ℝ) (305 : ℝ) := Bnd.const _
  have h3 : Bnd ((√(305 : ℝ))) (1.7464249196572980646321043e1 : ℝ) (1.7464249196572980646321044e1 : ℝ) := Bnd.sqrt h2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h4 := Bnd.div h1 h3 (by norm_num) (by norm_num)
  have h5 : Bnd (((16 : ℝ) / (√(305 : ℝ)))) (9.1615733490218914865946456e-1 : ℝ) (9.1615733490218914865946462e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- `s' = √(2b) s₁₂`. -/
noncomputable def qsP : ℝ :=
  ((√((7 : ℝ) / 8)) * ((9 : ℝ) / 40))

theorem qsP_bnd : Bnd qsP (2.1046822800603420293908586e-1 : ℝ) (2.1046822800603420293908587e-1 : ℝ) := by
  unfold qsP
  have h1 : Bnd ((7 : ℝ) / 8) ((7 : ℝ) / 8) ((7 : ℝ) / 8) := Bnd.const _
  have h2 : Bnd ((√((7 : ℝ) / 8))) (9.3541434669348534639593718e-1 : ℝ) (9.3541434669348534639593719e-1 : ℝ) := Bnd.sqrt h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 : Bnd ((9 : ℝ) / 40) ((9 : ℝ) / 40) ((9 : ℝ) / 40) := Bnd.const _
  have h4 := Bnd.mul h2 h3 (by norm_num) (by norm_num)
  have h5 : Bnd (((√((7 : ℝ) / 8)) * ((9 : ℝ) / 40))) (2.1046822800603420293908586e-1 : ℝ) (2.1046822800603420293908587e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- `c' = (1 − s'²)^{1/2}`. -/
noncomputable def qcP : ℝ :=
  (√((1 : ℝ) - (qsP ^ 2)))

theorem qcP_bnd : Bnd qcP (9.7760069813804859004966799e-1 : ℝ) (9.7760069813804859004966801e-1 : ℝ) := by
  unfold qcP
  have h1 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h2 := Bnd.pow qsP_bnd (by norm_num) 2
  have h3 : Bnd ((qsP ^ 2)) (4.4296874999999999999999997e-2 : ℝ) (4.4296875000000000000000002e-2 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.sub h1 h3
  have h5 : Bnd (((1 : ℝ) - (qsP ^ 2))) (9.5570312499999999999999999e-1 : ℝ) (9.5570312500000000000000001e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 : Bnd ((√((1 : ℝ) - (qsP ^ 2)))) (9.7760069813804859004966799e-1 : ℝ) (9.7760069813804859004966801e-1 : ℝ) := Bnd.sqrt h5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h6

/-- `s_b = b^{1/2}`. -/
noncomputable def qsB : ℝ :=
  (√((7 : ℝ) / 16))

theorem qsB_bnd : Bnd qsB (6.6143782776614764762540393e-1 : ℝ) (6.6143782776614764762540394e-1 : ℝ) := by
  unfold qsB
  have h1 : Bnd ((7 : ℝ) / 16) ((7 : ℝ) / 16) ((7 : ℝ) / 16) := Bnd.const _
  have h2 : Bnd ((√((7 : ℝ) / 16))) (6.6143782776614764762540393e-1 : ℝ) (6.6143782776614764762540394e-1 : ℝ) := Bnd.sqrt h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h2

/-- `c₂ = s₂ = 2^{-1/2}`. -/
noncomputable def qc2 : ℝ :=
  ((1 : ℝ) / (√(2 : ℝ)))

theorem qc2_bnd : Bnd qc2 (7.0710678118654752440084432e-1 : ℝ) (7.0710678118654752440084438e-1 : ℝ) := by
  unfold qc2
  have h1 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h2 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h3 : Bnd ((√(2 : ℝ))) (1.4142135623730950488016887 : ℝ) (1.4142135623730950488016888 : ℝ) := Bnd.sqrt h2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h4 := Bnd.div h1 h3 (by norm_num) (by norm_num)
  have h5 : Bnd (((1 : ℝ) / (√(2 : ℝ)))) (7.0710678118654752440084432e-1 : ℝ) (7.0710678118654752440084438e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- `|V_ud| = c₁₂ c₁₃`. -/
noncomputable def qAbsVud : ℝ :=
  (qc12 * qc13)

theorem qAbsVud_bnd : Bnd qAbsVud (9.7435191251111243456910466e-1 : ℝ) (9.7435191251111243456910469e-1 : ℝ) := by
  unfold qAbsVud
  have h1 := Bnd.mul qc12_bnd qc13_bnd (by norm_num) (by norm_num)
  have h2 : Bnd ((qc12 * qc13)) (9.7435191251111243456910466e-1 : ℝ) (9.7435191251111243456910469e-1 : ℝ) := h1.weak (by norm_num) (by norm_num)
  exact h2

/-- `Σ_{i = u, c} Σ_j |V_ij|²`, expanded. -/
noncomputable def qTwoRows : ℝ :=
  ((((((((((81 : ℝ) / 1600) * (qc23 ^ 2)) + (((377 : ℝ) / 7200) * (qc13 ^ 2))) + (((921681 : ℝ) / 65536000000) * (qcdq ^ 2))) + (((921681 : ℝ) / 65536000000) * (qsdq ^ 2))) + ((qc12 ^ 2) * (qc13 ^ 2))) + ((qc12 ^ 2) * (qc23 ^ 2))) + (((1 : ℝ) / 40960000) * ((qc12 ^ 2) * (qcdq ^ 2)))) + (((1 : ℝ) / 40960000) * ((qc12 ^ 2) * (qsdq ^ 2))))

theorem qTwoRows_bnd : Bnd qTwoRows (1.9999999999999999999999997 : ℝ) (2.0000000000000000000000003 : ℝ) := by
  unfold qTwoRows
  have h1 : Bnd ((81 : ℝ) / 1600) ((81 : ℝ) / 1600) ((81 : ℝ) / 1600) := Bnd.const _
  have h2 := Bnd.pow qc23_bnd (by norm_num) 2
  have h3 : Bnd ((qc23 ^ 2)) (9.9826388888888888888888886e-1 : ℝ) (9.9826388888888888888888891e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.mul h1 h3 (by norm_num) (by norm_num)
  have h5 : Bnd ((((81 : ℝ) / 1600) * (qc23 ^ 2))) (5.0537109374999999999999998e-2 : ℝ) (5.0537109375000000000000002e-2 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 : Bnd ((377 : ℝ) / 7200) ((377 : ℝ) / 7200) ((377 : ℝ) / 7200) := Bnd.const _
  have h7 := Bnd.pow qc13_bnd (by norm_num) 2
  have h8 : Bnd ((qc13 ^ 2)) (9.9998593749999999999999998e-1 : ℝ) (9.9998593750000000000000001e-1 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 := Bnd.mul h6 h8 (by norm_num) (by norm_num)
  have h10 : Bnd ((((377 : ℝ) / 7200) * (qc13 ^ 2))) (5.236037478298611111111111e-2 : ℝ) (5.2360374782986111111111112e-2 : ℝ) := h9.weak (by norm_num) (by norm_num)
  have h11 := Bnd.add h5 h10
  have h12 : Bnd (((((81 : ℝ) / 1600) * (qc23 ^ 2)) + (((377 : ℝ) / 7200) * (qc13 ^ 2)))) (1.028974841579861111111111e-1 : ℝ) (1.0289748415798611111111112e-1 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 : Bnd ((921681 : ℝ) / 65536000000) ((921681 : ℝ) / 65536000000) ((921681 : ℝ) / 65536000000) := Bnd.const _
  have h14 := Bnd.pow qcdq_bnd (by norm_num) 2
  have h15 : Bnd ((qcdq ^ 2)) (1.6065573770491803278688523e-1 : ℝ) (1.6065573770491803278688526e-1 : ℝ) := h14.weak (by norm_num) (by norm_num)
  have h16 := Bnd.mul h13 h15 (by norm_num) (by norm_num)
  have h17 : Bnd ((((921681 : ℝ) / 65536000000) * (qcdq ^ 2))) (2.2594198758484887295081964e-6 : ℝ) (2.259419875848488729508197e-6 : ℝ) := h16.weak (by norm_num) (by norm_num)
  have h18 := Bnd.add h12 h17
  have h19 : Bnd ((((((81 : ℝ) / 1600) * (qc23 ^ 2)) + (((377 : ℝ) / 7200) * (qc13 ^ 2))) + (((921681 : ℝ) / 65536000000) * (qcdq ^ 2)))) (1.028997435778619595998406e-1 : ℝ) (1.0289974357786195959984063e-1 : ℝ) := h18.weak (by norm_num) (by norm_num)
  have h20 : Bnd ((921681 : ℝ) / 65536000000) ((921681 : ℝ) / 65536000000) ((921681 : ℝ) / 65536000000) := Bnd.const _
  have h21 := Bnd.pow qsdq_bnd (by norm_num) 2
  have h22 : Bnd ((qsdq ^ 2)) (8.3934426229508196721311471e-1 : ℝ) (8.3934426229508196721311483e-1 : ℝ) := h21.weak (by norm_num) (by norm_num)
  have h23 := Bnd.mul h20 h22 (by norm_num) (by norm_num)
  have h24 : Bnd ((((921681 : ℝ) / 65536000000) * (qsdq ^ 2))) (1.1804316086065573770491802e-5 : ℝ) (1.1804316086065573770491805e-5 : ℝ) := h23.weak (by norm_num) (by norm_num)
  have h25 := Bnd.add h19 h24
  have h26 : Bnd (((((((81 : ℝ) / 1600) * (qc23 ^ 2)) + (((377 : ℝ) / 7200) * (qc13 ^ 2))) + (((921681 : ℝ) / 65536000000) * (qcdq ^ 2))) + (((921681 : ℝ) / 65536000000) * (qsdq ^ 2)))) (1.0291154789394802517361109e-1 : ℝ) (1.0291154789394802517361113e-1 : ℝ) := h25.weak (by norm_num) (by norm_num)
  have h27 := Bnd.pow qc12_bnd (by norm_num) 2
  have h28 : Bnd ((qc12 ^ 2)) (9.4937499999999999999999998e-1 : ℝ) (9.4937500000000000000000001e-1 : ℝ) := h27.weak (by norm_num) (by norm_num)
  have h29 := Bnd.pow qc13_bnd (by norm_num) 2
  have h30 : Bnd ((qc13 ^ 2)) (9.9998593749999999999999998e-1 : ℝ) (9.9998593750000000000000001e-1 : ℝ) := h29.weak (by norm_num) (by norm_num)
  have h31 := Bnd.mul h28 h30 (by norm_num) (by norm_num)
  have h32 : Bnd (((qc12 ^ 2) * (qc13 ^ 2))) (9.4936164941406249999999996e-1 : ℝ) (9.4936164941406250000000002e-1 : ℝ) := h31.weak (by norm_num) (by norm_num)
  have h33 := Bnd.add h26 h32
  have h34 : Bnd ((((((((81 : ℝ) / 1600) * (qc23 ^ 2)) + (((377 : ℝ) / 7200) * (qc13 ^ 2))) + (((921681 : ℝ) / 65536000000) * (qcdq ^ 2))) + (((921681 : ℝ) / 65536000000) * (qsdq ^ 2))) + ((qc12 ^ 2) * (qc13 ^ 2)))) (1.052273197308010525173611 : ℝ) (1.0522731973080105251736112 : ℝ) := h33.weak (by norm_num) (by norm_num)
  have h35 := Bnd.pow qc12_bnd (by norm_num) 2
  have h36 : Bnd ((qc12 ^ 2)) (9.4937499999999999999999998e-1 : ℝ) (9.4937500000000000000000001e-1 : ℝ) := h35.weak (by norm_num) (by norm_num)
  have h37 := Bnd.pow qc23_bnd (by norm_num) 2
  have h38 : Bnd ((qc23 ^ 2)) (9.9826388888888888888888886e-1 : ℝ) (9.9826388888888888888888891e-1 : ℝ) := h37.weak (by norm_num) (by norm_num)
  have h39 := Bnd.mul h36 h38 (by norm_num) (by norm_num)
  have h40 : Bnd (((qc12 ^ 2) * (qc23 ^ 2))) (9.4772677951388888888888884e-1 : ℝ) (9.4772677951388888888888892e-1 : ℝ) := h39.weak (by norm_num) (by norm_num)
  have h41 := Bnd.add h34 h40
  have h42 : Bnd (((((((((81 : ℝ) / 1600) * (qc23 ^ 2)) + (((377 : ℝ) / 7200) * (qc13 ^ 2))) + (((921681 : ℝ) / 65536000000) * (qcdq ^ 2))) + (((921681 : ℝ) / 65536000000) * (qsdq ^ 2))) + ((qc12 ^ 2) * (qc13 ^ 2))) + ((qc12 ^ 2) * (qc23 ^ 2)))) (1.9999999768218994140624998 : ℝ) (1.9999999768218994140625002 : ℝ) := h41.weak (by norm_num) (by norm_num)
  have h43 : Bnd ((1 : ℝ) / 40960000) ((1 : ℝ) / 40960000) ((1 : ℝ) / 40960000) := Bnd.const _
  have h44 := Bnd.pow qc12_bnd (by norm_num) 2
  have h45 : Bnd ((qc12 ^ 2)) (9.4937499999999999999999998e-1 : ℝ) (9.4937500000000000000000001e-1 : ℝ) := h44.weak (by norm_num) (by norm_num)
  have h46 := Bnd.pow qcdq_bnd (by norm_num) 2
  have h47 : Bnd ((qcdq ^ 2)) (1.6065573770491803278688523e-1 : ℝ) (1.6065573770491803278688526e-1 : ℝ) := h46.weak (by norm_num) (by norm_num)
  have h48 := Bnd.mul h45 h47 (by norm_num) (by norm_num)
  have h49 : Bnd (((qc12 ^ 2) * (qcdq ^ 2))) (1.5252254098360655737704916e-1 : ℝ) (1.525225409836065573770492e-1 : ℝ) := h48.weak (by norm_num) (by norm_num)
  have h50 := Bnd.mul h43 h49 (by norm_num) (by norm_num)
  have h51 : Bnd ((((1 : ℝ) / 40960000) * ((qc12 ^ 2) * (qcdq ^ 2)))) (3.7236948482325819672131142e-9 : ℝ) (3.7236948482325819672131153e-9 : ℝ) := h50.weak (by norm_num) (by norm_num)
  have h52 := Bnd.add h42 h51
  have h53 : Bnd ((((((((((81 : ℝ) / 1600) * (qc23 ^ 2)) + (((377 : ℝ) / 7200) * (qc13 ^ 2))) + (((921681 : ℝ) / 65536000000) * (qcdq ^ 2))) + (((921681 : ℝ) / 65536000000) * (qsdq ^ 2))) + ((qc12 ^ 2) * (qc13 ^ 2))) + ((qc12 ^ 2) * (qc23 ^ 2))) + (((1 : ℝ) / 40960000) * ((qc12 ^ 2) * (qcdq ^ 2))))) (1.9999999805455942622950817 : ℝ) (1.9999999805455942622950822 : ℝ) := h52.weak (by norm_num) (by norm_num)
  have h54 : Bnd ((1 : ℝ) / 40960000) ((1 : ℝ) / 40960000) ((1 : ℝ) / 40960000) := Bnd.const _
  have h55 := Bnd.pow qc12_bnd (by norm_num) 2
  have h56 : Bnd ((qc12 ^ 2)) (9.4937499999999999999999998e-1 : ℝ) (9.4937500000000000000000001e-1 : ℝ) := h55.weak (by norm_num) (by norm_num)
  have h57 := Bnd.pow qsdq_bnd (by norm_num) 2
  have h58 : Bnd ((qsdq ^ 2)) (8.3934426229508196721311471e-1 : ℝ) (8.3934426229508196721311483e-1 : ℝ) := h57.weak (by norm_num) (by norm_num)
  have h59 := Bnd.mul h56 h58 (by norm_num) (by norm_num)
  have h60 : Bnd (((qc12 ^ 2) * (qsdq ^ 2))) (7.9685245901639344262295076e-1 : ℝ) (7.9685245901639344262295091e-1 : ℝ) := h59.weak (by norm_num) (by norm_num)
  have h61 := Bnd.mul h54 h60 (by norm_num) (by norm_num)
  have h62 : Bnd ((((1 : ℝ) / 40960000) * ((qc12 ^ 2) * (qsdq ^ 2)))) (1.9454405737704918032786883e-8 : ℝ) (1.9454405737704918032786888e-8 : ℝ) := h61.weak (by norm_num) (by norm_num)
  have h63 := Bnd.add h53 h62
  have h64 : Bnd (((((((((((81 : ℝ) / 1600) * (qc23 ^ 2)) + (((377 : ℝ) / 7200) * (qc13 ^ 2))) + (((921681 : ℝ) / 65536000000) * (qcdq ^ 2))) + (((921681 : ℝ) / 65536000000) * (qsdq ^ 2))) + ((qc12 ^ 2) * (qc13 ^ 2))) + ((qc12 ^ 2) * (qc23 ^ 2))) + (((1 : ℝ) / 40960000) * ((qc12 ^ 2) * (qcdq ^ 2)))) + (((1 : ℝ) / 40960000) * ((qc12 ^ 2) * (qsdq ^ 2))))) (1.9999999999999999999999997 : ℝ) (2.0000000000000000000000003 : ℝ) := h63.weak (by norm_num) (by norm_num)
  exact h64

/-- `Σ_i |V_ii|²`, expanded. -/
noncomputable def qDiagSum : ℝ :=
  ((((((((81 : ℝ) / 65536000000) * (qcdq ^ 2)) + (((81 : ℝ) / 65536000000) * (qsdq ^ 2))) + ((qc12 ^ 2) * (qc13 ^ 2))) + ((qc12 ^ 2) * (qc23 ^ 2))) + ((qc13 ^ 2) * (qc23 ^ 2))) - (((9 : ℝ) / 128000) * ((qc12 * qc23) * qcdq)))

theorem qDiagSum_bnd : Bnd qDiagSum (2.8953108448757564997682079 : ℝ) (2.8953108448757564997682085 : ℝ) := by
  unfold qDiagSum
  have h1 : Bnd ((81 : ℝ) / 65536000000) ((81 : ℝ) / 65536000000) ((81 : ℝ) / 65536000000) := Bnd.const _
  have h2 := Bnd.pow qcdq_bnd (by norm_num) 2
  have h3 : Bnd ((qcdq ^ 2)) (1.6065573770491803278688523e-1 : ℝ) (1.6065573770491803278688526e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.mul h1 h3 (by norm_num) (by norm_num)
  have h5 : Bnd ((((81 : ℝ) / 65536000000) * (qcdq ^ 2))) (1.985643730788934426229508e-10 : ℝ) (1.9856437307889344262295084e-10 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 : Bnd ((81 : ℝ) / 65536000000) ((81 : ℝ) / 65536000000) ((81 : ℝ) / 65536000000) := Bnd.const _
  have h7 := Bnd.pow qsdq_bnd (by norm_num) 2
  have h8 : Bnd ((qsdq ^ 2)) (8.3934426229508196721311471e-1 : ℝ) (8.3934426229508196721311483e-1 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 := Bnd.mul h6 h8 (by norm_num) (by norm_num)
  have h10 : Bnd ((((81 : ℝ) / 65536000000) * (qsdq ^ 2))) (1.0373975409836065573770491e-9 : ℝ) (1.0373975409836065573770493e-9 : ℝ) := h9.weak (by norm_num) (by norm_num)
  have h11 := Bnd.add h5 h10
  have h12 : Bnd (((((81 : ℝ) / 65536000000) * (qcdq ^ 2)) + (((81 : ℝ) / 65536000000) * (qsdq ^ 2)))) (1.2359619140624999999999999e-9 : ℝ) (1.2359619140625000000000002e-9 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 := Bnd.pow qc12_bnd (by norm_num) 2
  have h14 : Bnd ((qc12 ^ 2)) (9.4937499999999999999999998e-1 : ℝ) (9.4937500000000000000000001e-1 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 := Bnd.pow qc13_bnd (by norm_num) 2
  have h16 : Bnd ((qc13 ^ 2)) (9.9998593749999999999999998e-1 : ℝ) (9.9998593750000000000000001e-1 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.mul h14 h16 (by norm_num) (by norm_num)
  have h18 : Bnd (((qc12 ^ 2) * (qc13 ^ 2))) (9.4936164941406249999999996e-1 : ℝ) (9.4936164941406250000000002e-1 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 := Bnd.add h12 h18
  have h20 : Bnd ((((((81 : ℝ) / 65536000000) * (qcdq ^ 2)) + (((81 : ℝ) / 65536000000) * (qsdq ^ 2))) + ((qc12 ^ 2) * (qc13 ^ 2)))) (9.4936165065002441406249995e-1 : ℝ) (9.4936165065002441406250003e-1 : ℝ) := h19.weak (by norm_num) (by norm_num)
  have h21 := Bnd.pow qc12_bnd (by norm_num) 2
  have h22 : Bnd ((qc12 ^ 2)) (9.4937499999999999999999998e-1 : ℝ) (9.4937500000000000000000001e-1 : ℝ) := h21.weak (by norm_num) (by norm_num)
  have h23 := Bnd.pow qc23_bnd (by norm_num) 2
  have h24 : Bnd ((qc23 ^ 2)) (9.9826388888888888888888886e-1 : ℝ) (9.9826388888888888888888891e-1 : ℝ) := h23.weak (by norm_num) (by norm_num)
  have h25 := Bnd.mul h22 h24 (by norm_num) (by norm_num)
  have h26 : Bnd (((qc12 ^ 2) * (qc23 ^ 2))) (9.4772677951388888888888884e-1 : ℝ) (9.4772677951388888888888892e-1 : ℝ) := h25.weak (by norm_num) (by norm_num)
  have h27 := Bnd.add h20 h26
  have h28 : Bnd (((((((81 : ℝ) / 65536000000) * (qcdq ^ 2)) + (((81 : ℝ) / 65536000000) * (qsdq ^ 2))) + ((qc12 ^ 2) * (qc13 ^ 2))) + ((qc12 ^ 2) * (qc23 ^ 2)))) (1.8970884301639133029513887 : ℝ) (1.897088430163913302951389 : ℝ) := h27.weak (by norm_num) (by norm_num)
  have h29 := Bnd.pow qc13_bnd (by norm_num) 2
  have h30 : Bnd ((qc13 ^ 2)) (9.9998593749999999999999998e-1 : ℝ) (9.9998593750000000000000001e-1 : ℝ) := h29.weak (by norm_num) (by norm_num)
  have h31 := Bnd.pow qc23_bnd (by norm_num) 2
  have h32 : Bnd ((qc23 ^ 2)) (9.9826388888888888888888886e-1 : ℝ) (9.9826388888888888888888891e-1 : ℝ) := h31.weak (by norm_num) (by norm_num)
  have h33 := Bnd.mul h30 h32 (by norm_num) (by norm_num)
  have h34 : Bnd (((qc13 ^ 2) * (qc23 ^ 2))) (9.9824985080295138888888884e-1 : ℝ) (9.9824985080295138888888892e-1 : ℝ) := h33.weak (by norm_num) (by norm_num)
  have h35 := Bnd.add h28 h34
  have h36 : Bnd ((((((((81 : ℝ) / 65536000000) * (qcdq ^ 2)) + (((81 : ℝ) / 65536000000) * (qsdq ^ 2))) + ((qc12 ^ 2) * (qc13 ^ 2))) + ((qc12 ^ 2) * (qc23 ^ 2))) + ((qc13 ^ 2) * (qc23 ^ 2)))) (2.8953382809668646918402775 : ℝ) (2.895338280966864691840278 : ℝ) := h35.weak (by norm_num) (by norm_num)
  have h37 : Bnd ((9 : ℝ) / 128000) ((9 : ℝ) / 128000) ((9 : ℝ) / 128000) := Bnd.const _
  have h38 := Bnd.mul qc12_bnd qc23_bnd (by norm_num) (by norm_num)
  have h39 : Bnd ((qc12 * qc23)) (9.7351259853886271567207588e-1 : ℝ) (9.7351259853886271567207592e-1 : ℝ) := h38.weak (by norm_num) (by norm_num)
  have h40 := Bnd.mul h39 qcdq_bnd (by norm_num) (by norm_num)
  have h41 : Bnd (((qc12 * qc23) * qcdq)) (3.902021846498428027668863e-1 : ℝ) (3.9020218464984280276688636e-1 : ℝ) := h40.weak (by norm_num) (by norm_num)
  have h42 := Bnd.mul h37 h41 (by norm_num) (by norm_num)
  have h43 : Bnd ((((9 : ℝ) / 128000) * ((qc12 * qc23) * qcdq))) (2.7436091108192072069546692e-5 : ℝ) (2.7436091108192072069546698e-5 : ℝ) := h42.weak (by norm_num) (by norm_num)
  have h44 := Bnd.sub h36 h43
  have h45 : Bnd (((((((((81 : ℝ) / 65536000000) * (qcdq ^ 2)) + (((81 : ℝ) / 65536000000) * (qsdq ^ 2))) + ((qc12 ^ 2) * (qc13 ^ 2))) + ((qc12 ^ 2) * (qc23 ^ 2))) + ((qc13 ^ 2) * (qc23 ^ 2))) - (((9 : ℝ) / 128000) * ((qc12 * qc23) * qcdq)))) (2.8953108448757564997682079 : ℝ) (2.8953108448757564997682085 : ℝ) := h44.weak (by norm_num) (by norm_num)
  exact h45

/-- `Im(V_us V_cb V_ub* V_cs*)`, expanded. -/
noncomputable def qJq : ℝ :=
  (((9 : ℝ) / 256000) * (((qc12 * qc23) * qsdq) * (qc13 ^ 2)))

theorem qJq_bnd : Bnd qJq (3.1355091757898129278323674e-5 : ℝ) (3.135509175789812927832368e-5 : ℝ) := by
  unfold qJq
  have h1 : Bnd ((9 : ℝ) / 256000) ((9 : ℝ) / 256000) ((9 : ℝ) / 256000) := Bnd.const _
  have h2 := Bnd.mul qc12_bnd qc23_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((qc12 * qc23)) (9.7351259853886271567207588e-1 : ℝ) (9.7351259853886271567207592e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.mul h3 qsdq_bnd (by norm_num) (by norm_num)
  have h5 : Bnd (((qc12 * qc23) * qsdq)) (8.9189070777106926346716871e-1 : ℝ) (8.9189070777106926346716881e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.pow qc13_bnd (by norm_num) 2
  have h7 : Bnd ((qc13 ^ 2)) (9.9998593749999999999999998e-1 : ℝ) (9.9998593750000000000000001e-1 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 := Bnd.mul h5 h7 (by norm_num) (by norm_num)
  have h9 : Bnd ((((qc12 * qc23) * qsdq) * (qc13 ^ 2))) (8.9187816555799123280565118e-1 : ℝ) (8.9187816555799123280565132e-1 : ℝ) := h8.weak (by norm_num) (by norm_num)
  have h10 := Bnd.mul h1 h9 (by norm_num) (by norm_num)
  have h11 : Bnd ((((9 : ℝ) / 256000) * (((qc12 * qc23) * qsdq) * (qc13 ^ 2)))) (3.1355091757898129278323674e-5 : ℝ) (3.135509175789812927832368e-5 : ℝ) := h10.weak (by norm_num) (by norm_num)
  exact h11

/-- `Re` of the triangle's `Alpha` numerator times its conjugate denominator. -/
noncomputable def qReAlpha : ℝ :=
  (((((9 : ℝ) / 640000) * ((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2)) * (qcdq ^ 2))) + (((9 : ℝ) / 640000) * ((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2)) * (qsdq ^ 2)))) - (((9 : ℝ) / 256000) * (((qc12 * qc23) * qcdq) * (qc13 ^ 2))))

theorem qReAlpha_bnd : Bnd qReAlpha (-3.90632223839075663270519e-7 : ℝ) (-3.90632223839075663270511e-7 : ℝ) := by
  unfold qReAlpha
  have h1 : Bnd ((9 : ℝ) / 640000) ((9 : ℝ) / 640000) ((9 : ℝ) / 640000) := Bnd.const _
  have h2 := Bnd.pow qc12_bnd (by norm_num) 2
  have h3 : Bnd ((qc12 ^ 2)) (9.4937499999999999999999998e-1 : ℝ) (9.4937500000000000000000001e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.pow qc13_bnd (by norm_num) 2
  have h5 : Bnd ((qc13 ^ 2)) (9.9998593749999999999999998e-1 : ℝ) (9.9998593750000000000000001e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.mul h3 h5 (by norm_num) (by norm_num)
  have h7 : Bnd (((qc12 ^ 2) * (qc13 ^ 2))) (9.4936164941406249999999996e-1 : ℝ) (9.4936164941406250000000002e-1 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 := Bnd.pow qc23_bnd (by norm_num) 2
  have h9 : Bnd ((qc23 ^ 2)) (9.9826388888888888888888886e-1 : ℝ) (9.9826388888888888888888891e-1 : ℝ) := h8.weak (by norm_num) (by norm_num)
  have h10 := Bnd.mul h7 h9 (by norm_num) (by norm_num)
  have h11 : Bnd ((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2))) (9.4771345210605197482638882e-1 : ℝ) (9.4771345210605197482638893e-1 : ℝ) := h10.weak (by norm_num) (by norm_num)
  have h12 := Bnd.pow qcdq_bnd (by norm_num) 2
  have h13 : Bnd ((qcdq ^ 2)) (1.6065573770491803278688523e-1 : ℝ) (1.6065573770491803278688526e-1 : ℝ) := h12.weak (by norm_num) (by norm_num)
  have h14 := Bnd.mul h11 h13 (by norm_num) (by norm_num)
  have h15 : Bnd (((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2)) * (qcdq ^ 2))) (1.5225560378097228448030507e-1 : ℝ) (1.5225560378097228448030513e-1 : ℝ) := h14.weak (by norm_num) (by norm_num)
  have h16 := Bnd.mul h1 h15 (by norm_num) (by norm_num)
  have h17 : Bnd ((((9 : ℝ) / 640000) * ((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2)) * (qcdq ^ 2)))) (2.14109442816992275050429e-6 : ℝ) (2.1410944281699227505042909e-6 : ℝ) := h16.weak (by norm_num) (by norm_num)
  have h18 : Bnd ((9 : ℝ) / 640000) ((9 : ℝ) / 640000) ((9 : ℝ) / 640000) := Bnd.const _
  have h19 := Bnd.pow qc12_bnd (by norm_num) 2
  have h20 : Bnd ((qc12 ^ 2)) (9.4937499999999999999999998e-1 : ℝ) (9.4937500000000000000000001e-1 : ℝ) := h19.weak (by norm_num) (by norm_num)
  have h21 := Bnd.pow qc13_bnd (by norm_num) 2
  have h22 : Bnd ((qc13 ^ 2)) (9.9998593749999999999999998e-1 : ℝ) (9.9998593750000000000000001e-1 : ℝ) := h21.weak (by norm_num) (by norm_num)
  have h23 := Bnd.mul h20 h22 (by norm_num) (by norm_num)
  have h24 : Bnd (((qc12 ^ 2) * (qc13 ^ 2))) (9.4936164941406249999999996e-1 : ℝ) (9.4936164941406250000000002e-1 : ℝ) := h23.weak (by norm_num) (by norm_num)
  have h25 := Bnd.pow qc23_bnd (by norm_num) 2
  have h26 : Bnd ((qc23 ^ 2)) (9.9826388888888888888888886e-1 : ℝ) (9.9826388888888888888888891e-1 : ℝ) := h25.weak (by norm_num) (by norm_num)
  have h27 := Bnd.mul h24 h26 (by norm_num) (by norm_num)
  have h28 : Bnd ((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2))) (9.4771345210605197482638882e-1 : ℝ) (9.4771345210605197482638893e-1 : ℝ) := h27.weak (by norm_num) (by norm_num)
  have h29 := Bnd.pow qsdq_bnd (by norm_num) 2
  have h30 : Bnd ((qsdq ^ 2)) (8.3934426229508196721311471e-1 : ℝ) (8.3934426229508196721311483e-1 : ℝ) := h29.weak (by norm_num) (by norm_num)
  have h31 := Bnd.mul h28 h30 (by norm_num) (by norm_num)
  have h32 : Bnd (((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2)) * (qsdq ^ 2))) (7.9545784832507969034608368e-1 : ℝ) (7.954578483250796903460839e-1 : ℝ) := h31.weak (by norm_num) (by norm_num)
  have h33 := Bnd.mul h18 h32 (by norm_num) (by norm_num)
  have h34 : Bnd ((((9 : ℝ) / 640000) * ((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2)) * (qsdq ^ 2)))) (1.1186125992071433145491801e-5 : ℝ) (1.1186125992071433145491805e-5 : ℝ) := h33.weak (by norm_num) (by norm_num)
  have h35 := Bnd.add h17 h34
  have h36 : Bnd (((((9 : ℝ) / 640000) * ((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2)) * (qcdq ^ 2))) + (((9 : ℝ) / 640000) * ((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2)) * (qsdq ^ 2))))) (1.3327220420241355895996091e-5 : ℝ) (1.3327220420241355895996096e-5 : ℝ) := h35.weak (by norm_num) (by norm_num)
  have h37 : Bnd ((9 : ℝ) / 256000) ((9 : ℝ) / 256000) ((9 : ℝ) / 256000) := Bnd.const _
  have h38 := Bnd.mul qc12_bnd qc23_bnd (by norm_num) (by norm_num)
  have h39 : Bnd ((qc12 * qc23)) (9.7351259853886271567207588e-1 : ℝ) (9.7351259853886271567207592e-1 : ℝ) := h38.weak (by norm_num) (by norm_num)
  have h40 := Bnd.mul h39 qcdq_bnd (by norm_num) (by norm_num)
  have h41 : Bnd (((qc12 * qc23) * qcdq)) (3.902021846498428027668863e-1 : ℝ) (3.9020218464984280276688636e-1 : ℝ) := h40.weak (by norm_num) (by norm_num)
  have h42 := Bnd.pow qc13_bnd (by norm_num) 2
  have h43 : Bnd ((qc13 ^ 2)) (9.9998593749999999999999998e-1 : ℝ) (9.9998593750000000000000001e-1 : ℝ) := h42.weak (by norm_num) (by norm_num)
  have h44 := Bnd.mul h41 h43 (by norm_num) (by norm_num)
  have h45 : Bnd ((((qc12 * qc23) * qcdq) * (qc13 ^ 2))) (3.9019669743162116435247238e-1 : ℝ) (3.9019669743162116435247246e-1 : ℝ) := h44.weak (by norm_num) (by norm_num)
  have h46 := Bnd.mul h37 h45 (by norm_num) (by norm_num)
  have h47 : Bnd ((((9 : ℝ) / 256000) * (((qc12 * qc23) * qcdq) * (qc13 ^ 2)))) (1.3717852644080431559266607e-5 : ℝ) (1.371785264408043155926661e-5 : ℝ) := h46.weak (by norm_num) (by norm_num)
  have h48 := Bnd.sub h36 h47
  have h49 : Bnd ((((((9 : ℝ) / 640000) * ((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2)) * (qcdq ^ 2))) + (((9 : ℝ) / 640000) * ((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2)) * (qsdq ^ 2)))) - (((9 : ℝ) / 256000) * (((qc12 * qc23) * qcdq) * (qc13 ^ 2))))) (-3.90632223839075663270519e-7 : ℝ) (-3.90632223839075663270511e-7 : ℝ) := h48.weak (by norm_num) (by norm_num)
  exact h49

/-- `Im` of the same. -/
noncomputable def qImAlpha : ℝ :=
  (((9 : ℝ) / 256000) * (((qc12 * qc23) * qsdq) * (qc13 ^ 2)))

theorem qImAlpha_bnd : Bnd qImAlpha (3.1355091757898129278323674e-5 : ℝ) (3.135509175789812927832368e-5 : ℝ) := by
  unfold qImAlpha
  have h1 : Bnd ((9 : ℝ) / 256000) ((9 : ℝ) / 256000) ((9 : ℝ) / 256000) := Bnd.const _
  have h2 := Bnd.mul qc12_bnd qc23_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((qc12 * qc23)) (9.7351259853886271567207588e-1 : ℝ) (9.7351259853886271567207592e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.mul h3 qsdq_bnd (by norm_num) (by norm_num)
  have h5 : Bnd (((qc12 * qc23) * qsdq)) (8.9189070777106926346716871e-1 : ℝ) (8.9189070777106926346716881e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.pow qc13_bnd (by norm_num) 2
  have h7 : Bnd ((qc13 ^ 2)) (9.9998593749999999999999998e-1 : ℝ) (9.9998593750000000000000001e-1 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 := Bnd.mul h5 h7 (by norm_num) (by norm_num)
  have h9 : Bnd ((((qc12 * qc23) * qsdq) * (qc13 ^ 2))) (8.9187816555799123280565118e-1 : ℝ) (8.9187816555799123280565132e-1 : ℝ) := h8.weak (by norm_num) (by norm_num)
  have h10 := Bnd.mul h1 h9 (by norm_num) (by norm_num)
  have h11 : Bnd ((((9 : ℝ) / 256000) * (((qc12 * qc23) * qsdq) * (qc13 ^ 2)))) (3.1355091757898129278323674e-5 : ℝ) (3.135509175789812927832368e-5 : ℝ) := h10.weak (by norm_num) (by norm_num)
  exact h11

/-- `Re` of the triangle's `Beta` numerator times its conjugate denominator. -/
noncomputable def qReBeta : ℝ :=
  (((((9 : ℝ) / 102400) * ((qc13 ^ 2) * (qc23 ^ 2))) + (((1 : ℝ) / 16384000) * (((qc12 * qc23) * qcdq) * (qc13 ^ 2)))) - (((((9 : ℝ) / 256000) * (((qc12 * qcdq) * (qc13 ^ 2)) * (qc23 ^ 3))) + (((1 : ℝ) / 40960000) * ((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2)) * (qcdq ^ 2)))) + (((1 : ℝ) / 40960000) * ((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2)) * (qsdq ^ 2)))))

theorem qReBeta_bnd : Bnd qReBeta (7.4043444546487855888168344e-5 : ℝ) (7.404344454648785588816836e-5 : ℝ) := by
  unfold qReBeta
  have h1 : Bnd ((9 : ℝ) / 102400) ((9 : ℝ) / 102400) ((9 : ℝ) / 102400) := Bnd.const _
  have h2 := Bnd.pow qc13_bnd (by norm_num) 2
  have h3 : Bnd ((qc13 ^ 2)) (9.9998593749999999999999998e-1 : ℝ) (9.9998593750000000000000001e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.pow qc23_bnd (by norm_num) 2
  have h5 : Bnd ((qc23 ^ 2)) (9.9826388888888888888888886e-1 : ℝ) (9.9826388888888888888888891e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.mul h3 h5 (by norm_num) (by norm_num)
  have h7 : Bnd (((qc13 ^ 2) * (qc23 ^ 2))) (9.9824985080295138888888884e-1 : ℝ) (9.9824985080295138888888892e-1 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 := Bnd.mul h1 h7 (by norm_num) (by norm_num)
  have h9 : Bnd ((((9 : ℝ) / 102400) * ((qc13 ^ 2) * (qc23 ^ 2)))) (8.7736803293228149414062495e-5 : ℝ) (8.7736803293228149414062503e-5 : ℝ) := h8.weak (by norm_num) (by norm_num)
  have h10 : Bnd ((1 : ℝ) / 16384000) ((1 : ℝ) / 16384000) ((1 : ℝ) / 16384000) := Bnd.const _
  have h11 := Bnd.mul qc12_bnd qc23_bnd (by norm_num) (by norm_num)
  have h12 : Bnd ((qc12 * qc23)) (9.7351259853886271567207588e-1 : ℝ) (9.7351259853886271567207592e-1 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 := Bnd.mul h12 qcdq_bnd (by norm_num) (by norm_num)
  have h14 : Bnd (((qc12 * qc23) * qcdq)) (3.902021846498428027668863e-1 : ℝ) (3.9020218464984280276688636e-1 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 := Bnd.pow qc13_bnd (by norm_num) 2
  have h16 : Bnd ((qc13 ^ 2)) (9.9998593749999999999999998e-1 : ℝ) (9.9998593750000000000000001e-1 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.mul h14 h16 (by norm_num) (by norm_num)
  have h18 : Bnd ((((qc12 * qc23) * qcdq) * (qc13 ^ 2))) (3.9019669743162116435247238e-1 : ℝ) (3.9019669743162116435247246e-1 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 := Bnd.mul h10 h18 (by norm_num) (by norm_num)
  have h20 : Bnd ((((1 : ℝ) / 16384000) * (((qc12 * qc23) * qcdq) * (qc13 ^ 2)))) (2.3815716395972971457060081e-8 : ℝ) (2.3815716395972971457060087e-8 : ℝ) := h19.weak (by norm_num) (by norm_num)
  have h21 := Bnd.add h9 h20
  have h22 : Bnd (((((9 : ℝ) / 102400) * ((qc13 ^ 2) * (qc23 ^ 2))) + (((1 : ℝ) / 16384000) * (((qc12 * qc23) * qcdq) * (qc13 ^ 2))))) (8.7760619009624122385519555e-5 : ℝ) (8.7760619009624122385519564e-5 : ℝ) := h21.weak (by norm_num) (by norm_num)
  have h23 : Bnd ((9 : ℝ) / 256000) ((9 : ℝ) / 256000) ((9 : ℝ) / 256000) := Bnd.const _
  have h24 := Bnd.mul qc12_bnd qcdq_bnd (by norm_num) (by norm_num)
  have h25 : Bnd ((qc12 * qcdq)) (3.9054134350105182862291256e-1 : ℝ) (3.9054134350105182862291261e-1 : ℝ) := h24.weak (by norm_num) (by norm_num)
  have h26 := Bnd.pow qc13_bnd (by norm_num) 2
  have h27 : Bnd ((qc13 ^ 2)) (9.9998593749999999999999998e-1 : ℝ) (9.9998593750000000000000001e-1 : ℝ) := h26.weak (by norm_num) (by norm_num)
  have h28 := Bnd.mul h25 h27 (by norm_num) (by norm_num)
  have h29 : Bnd (((qc12 * qcdq) * (qc13 ^ 2))) (3.9053585151340884508157254e-1 : ℝ) (3.9053585151340884508157261e-1 : ℝ) := h28.weak (by norm_num) (by norm_num)
  have h30 := Bnd.pow qc23_bnd (by norm_num) 3
  have h31 : Bnd ((qc23 ^ 3)) (9.9739696394126654239674725e-1 : ℝ) (9.9739696394126654239674732e-1 : ℝ) := h30.weak (by norm_num) (by norm_num)
  have h32 := Bnd.mul h29 h31 (by norm_num) (by norm_num)
  have h33 : Bnd ((((qc12 * qcdq) * (qc13 ^ 2)) * (qc23 ^ 3))) (3.8951927260969126649769377e-1 : ℝ) (3.8951927260969126649769388e-1 : ℝ) := h32.weak (by norm_num) (by norm_num)
  have h34 := Bnd.mul h23 h33 (by norm_num) (by norm_num)
  have h35 : Bnd ((((9 : ℝ) / 256000) * (((qc12 * qcdq) * (qc13 ^ 2)) * (qc23 ^ 3)))) (1.3694036927684458587809546e-5 : ℝ) (1.3694036927684458587809551e-5 : ℝ) := h34.weak (by norm_num) (by norm_num)
  have h36 : Bnd ((1 : ℝ) / 40960000) ((1 : ℝ) / 40960000) ((1 : ℝ) / 40960000) := Bnd.const _
  have h37 := Bnd.pow qc12_bnd (by norm_num) 2
  have h38 : Bnd ((qc12 ^ 2)) (9.4937499999999999999999998e-1 : ℝ) (9.4937500000000000000000001e-1 : ℝ) := h37.weak (by norm_num) (by norm_num)
  have h39 := Bnd.pow qc13_bnd (by norm_num) 2
  have h40 : Bnd ((qc13 ^ 2)) (9.9998593749999999999999998e-1 : ℝ) (9.9998593750000000000000001e-1 : ℝ) := h39.weak (by norm_num) (by norm_num)
  have h41 := Bnd.mul h38 h40 (by norm_num) (by norm_num)
  have h42 : Bnd (((qc12 ^ 2) * (qc13 ^ 2))) (9.4936164941406249999999996e-1 : ℝ) (9.4936164941406250000000002e-1 : ℝ) := h41.weak (by norm_num) (by norm_num)
  have h43 := Bnd.pow qc23_bnd (by norm_num) 2
  have h44 : Bnd ((qc23 ^ 2)) (9.9826388888888888888888886e-1 : ℝ) (9.9826388888888888888888891e-1 : ℝ) := h43.weak (by norm_num) (by norm_num)
  have h45 := Bnd.mul h42 h44 (by norm_num) (by norm_num)
  have h46 : Bnd ((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2))) (9.4771345210605197482638882e-1 : ℝ) (9.4771345210605197482638893e-1 : ℝ) := h45.weak (by norm_num) (by norm_num)
  have h47 := Bnd.pow qcdq_bnd (by norm_num) 2
  have h48 : Bnd ((qcdq ^ 2)) (1.6065573770491803278688523e-1 : ℝ) (1.6065573770491803278688526e-1 : ℝ) := h47.weak (by norm_num) (by norm_num)
  have h49 := Bnd.mul h46 h48 (by norm_num) (by norm_num)
  have h50 : Bnd (((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2)) * (qcdq ^ 2))) (1.5225560378097228448030507e-1 : ℝ) (1.5225560378097228448030513e-1 : ℝ) := h49.weak (by norm_num) (by norm_num)
  have h51 := Bnd.mul h36 h50 (by norm_num) (by norm_num)
  have h52 : Bnd ((((1 : ℝ) / 40960000) * ((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2)) * (qcdq ^ 2)))) (3.7171778266838936640699479e-9 : ℝ) (3.7171778266838936640699495e-9 : ℝ) := h51.weak (by norm_num) (by norm_num)
  have h53 := Bnd.add h35 h52
  have h54 : Bnd (((((9 : ℝ) / 256000) * (((qc12 * qcdq) * (qc13 ^ 2)) * (qc23 ^ 3))) + (((1 : ℝ) / 40960000) * ((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2)) * (qcdq ^ 2))))) (1.3697754105511142481473615e-5 : ℝ) (1.3697754105511142481473621e-5 : ℝ) := h53.weak (by norm_num) (by norm_num)
  have h55 : Bnd ((1 : ℝ) / 40960000) ((1 : ℝ) / 40960000) ((1 : ℝ) / 40960000) := Bnd.const _
  have h56 := Bnd.pow qc12_bnd (by norm_num) 2
  have h57 : Bnd ((qc12 ^ 2)) (9.4937499999999999999999998e-1 : ℝ) (9.4937500000000000000000001e-1 : ℝ) := h56.weak (by norm_num) (by norm_num)
  have h58 := Bnd.pow qc13_bnd (by norm_num) 2
  have h59 : Bnd ((qc13 ^ 2)) (9.9998593749999999999999998e-1 : ℝ) (9.9998593750000000000000001e-1 : ℝ) := h58.weak (by norm_num) (by norm_num)
  have h60 := Bnd.mul h57 h59 (by norm_num) (by norm_num)
  have h61 : Bnd (((qc12 ^ 2) * (qc13 ^ 2))) (9.4936164941406249999999996e-1 : ℝ) (9.4936164941406250000000002e-1 : ℝ) := h60.weak (by norm_num) (by norm_num)
  have h62 := Bnd.pow qc23_bnd (by norm_num) 2
  have h63 : Bnd ((qc23 ^ 2)) (9.9826388888888888888888886e-1 : ℝ) (9.9826388888888888888888891e-1 : ℝ) := h62.weak (by norm_num) (by norm_num)
  have h64 := Bnd.mul h61 h63 (by norm_num) (by norm_num)
  have h65 : Bnd ((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2))) (9.4771345210605197482638882e-1 : ℝ) (9.4771345210605197482638893e-1 : ℝ) := h64.weak (by norm_num) (by norm_num)
  have h66 := Bnd.pow qsdq_bnd (by norm_num) 2
  have h67 : Bnd ((qsdq ^ 2)) (8.3934426229508196721311471e-1 : ℝ) (8.3934426229508196721311483e-1 : ℝ) := h66.weak (by norm_num) (by norm_num)
  have h68 := Bnd.mul h65 h67 (by norm_num) (by norm_num)
  have h69 : Bnd (((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2)) * (qsdq ^ 2))) (7.9545784832507969034608368e-1 : ℝ) (7.954578483250796903460839e-1 : ℝ) := h68.weak (by norm_num) (by norm_num)
  have h70 := Bnd.mul h55 h69 (by norm_num) (by norm_num)
  have h71 : Bnd ((((1 : ℝ) / 40960000) * ((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2)) * (qsdq ^ 2)))) (1.9420357625124015877589933e-8 : ℝ) (1.9420357625124015877589939e-8 : ℝ) := h70.weak (by norm_num) (by norm_num)
  have h72 := Bnd.add h54 h71
  have h73 : Bnd ((((((9 : ℝ) / 256000) * (((qc12 * qcdq) * (qc13 ^ 2)) * (qc23 ^ 3))) + (((1 : ℝ) / 40960000) * ((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2)) * (qcdq ^ 2)))) + (((1 : ℝ) / 40960000) * ((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2)) * (qsdq ^ 2))))) (1.3717174463136266497351204e-5 : ℝ) (1.3717174463136266497351211e-5 : ℝ) := h72.weak (by norm_num) (by norm_num)
  have h74 := Bnd.sub h22 h73
  have h75 : Bnd ((((((9 : ℝ) / 102400) * ((qc13 ^ 2) * (qc23 ^ 2))) + (((1 : ℝ) / 16384000) * (((qc12 * qc23) * qcdq) * (qc13 ^ 2)))) - (((((9 : ℝ) / 256000) * (((qc12 * qcdq) * (qc13 ^ 2)) * (qc23 ^ 3))) + (((1 : ℝ) / 40960000) * ((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2)) * (qcdq ^ 2)))) + (((1 : ℝ) / 40960000) * ((((qc12 ^ 2) * (qc13 ^ 2)) * (qc23 ^ 2)) * (qsdq ^ 2)))))) (7.4043444546487855888168344e-5 : ℝ) (7.404344454648785588816836e-5 : ℝ) := h74.weak (by norm_num) (by norm_num)
  exact h75

/-- `Im` of the same. -/
noncomputable def qImBeta : ℝ :=
  ((((1 : ℝ) / 16384000) * (((qc12 * qc23) * qsdq) * (qc13 ^ 2))) + (((9 : ℝ) / 256000) * (((qc12 * qsdq) * (qc13 ^ 2)) * (qc23 ^ 3))))

theorem qImBeta_bnd : Bnd qImBeta (3.1355091757898129278323673e-5 : ℝ) (3.1355091757898129278323682e-5 : ℝ) := by
  unfold qImBeta
  have h1 : Bnd ((1 : ℝ) / 16384000) ((1 : ℝ) / 16384000) ((1 : ℝ) / 16384000) := Bnd.const _
  have h2 := Bnd.mul qc12_bnd qc23_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((qc12 * qc23)) (9.7351259853886271567207588e-1 : ℝ) (9.7351259853886271567207592e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.mul h3 qsdq_bnd (by norm_num) (by norm_num)
  have h5 : Bnd (((qc12 * qc23) * qsdq)) (8.9189070777106926346716871e-1 : ℝ) (8.9189070777106926346716881e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.pow qc13_bnd (by norm_num) 2
  have h7 : Bnd ((qc13 ^ 2)) (9.9998593749999999999999998e-1 : ℝ) (9.9998593750000000000000001e-1 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 := Bnd.mul h5 h7 (by norm_num) (by norm_num)
  have h9 : Bnd ((((qc12 * qc23) * qsdq) * (qc13 ^ 2))) (8.9187816555799123280565118e-1 : ℝ) (8.9187816555799123280565132e-1 : ℝ) := h8.weak (by norm_num) (by norm_num)
  have h10 := Bnd.mul h1 h9 (by norm_num) (by norm_num)
  have h11 : Bnd ((((1 : ℝ) / 16384000) * (((qc12 * qc23) * qsdq) * (qc13 ^ 2)))) (5.4435923190795363330423045e-8 : ℝ) (5.4435923190795363330423055e-8 : ℝ) := h10.weak (by norm_num) (by norm_num)
  have h12 : Bnd ((9 : ℝ) / 256000) ((9 : ℝ) / 256000) ((9 : ℝ) / 256000) := Bnd.const _
  have h13 := Bnd.mul qc12_bnd qsdq_bnd (by norm_num) (by norm_num)
  have h14 : Bnd ((qc12 * qsdq)) (8.9266592800240417970951445e-1 : ℝ) (8.9266592800240417970951453e-1 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 := Bnd.pow qc13_bnd (by norm_num) 2
  have h16 : Bnd ((qc13 ^ 2)) (9.9998593749999999999999998e-1 : ℝ) (9.9998593750000000000000001e-1 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.mul h14 h16 (by norm_num) (by norm_num)
  have h18 : Bnd (((qc12 * qsdq) * (qc13 ^ 2))) (8.9265337488779164590073726e-1 : ℝ) (8.9265337488779164590073738e-1 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 := Bnd.pow qc23_bnd (by norm_num) 3
  have h20 : Bnd ((qc23 ^ 3)) (9.9739696394126654239674725e-1 : ℝ) (9.9739696394126654239674732e-1 : ℝ) := h19.weak (by norm_num) (by norm_num)
  have h21 := Bnd.mul h18 h20 (by norm_num) (by norm_num)
  have h22 : Bnd ((((qc12 * qsdq) * (qc13 ^ 2)) * (qc23 ^ 3))) (8.9032976596500860913758579e-1 : ℝ) (8.9032976596500860913758598e-1 : ℝ) := h21.weak (by norm_num) (by norm_num)
  have h23 := Bnd.mul h12 h22 (by norm_num) (by norm_num)
  have h24 : Bnd ((((9 : ℝ) / 256000) * (((qc12 * qsdq) * (qc13 ^ 2)) * (qc23 ^ 3)))) (3.130065583470733391499325e-5 : ℝ) (3.1300655834707333914993258e-5 : ℝ) := h23.weak (by norm_num) (by norm_num)
  have h25 := Bnd.add h11 h24
  have h26 : Bnd (((((1 : ℝ) / 16384000) * (((qc12 * qc23) * qsdq) * (qc13 ^ 2))) + (((9 : ℝ) / 256000) * (((qc12 * qsdq) * (qc13 ^ 2)) * (qc23 ^ 3))))) (3.1355091757898129278323673e-5 : ℝ) (3.1355091757898129278323682e-5 : ℝ) := h25.weak (by norm_num) (by norm_num)
  exact h26

/-- `Re` of the triangle's `Gamma` numerator times its conjugate denominator. -/
noncomputable def qReGamma : ℝ :=
  (((((1 : ℝ) / 40960000) * (((qc12 ^ 2) * (qc13 ^ 2)) * (qcdq ^ 2))) + (((1 : ℝ) / 40960000) * (((qc12 ^ 2) * (qc13 ^ 2)) * (qsdq ^ 2)))) + (((9 : ℝ) / 256000) * (((qc12 * qc23) * qcdq) * (qc13 ^ 2))))

theorem qReGamma_bnd : Bnd qReGamma (1.3741030418724329569520513e-5 : ℝ) (1.3741030418724329569520517e-5 : ℝ) := by
  unfold qReGamma
  have h1 : Bnd ((1 : ℝ) / 40960000) ((1 : ℝ) / 40960000) ((1 : ℝ) / 40960000) := Bnd.const _
  have h2 := Bnd.pow qc12_bnd (by norm_num) 2
  have h3 : Bnd ((qc12 ^ 2)) (9.4937499999999999999999998e-1 : ℝ) (9.4937500000000000000000001e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.pow qc13_bnd (by norm_num) 2
  have h5 : Bnd ((qc13 ^ 2)) (9.9998593749999999999999998e-1 : ℝ) (9.9998593750000000000000001e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.mul h3 h5 (by norm_num) (by norm_num)
  have h7 : Bnd (((qc12 ^ 2) * (qc13 ^ 2))) (9.4936164941406249999999996e-1 : ℝ) (9.4936164941406250000000002e-1 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 := Bnd.pow qcdq_bnd (by norm_num) 2
  have h9 : Bnd ((qcdq ^ 2)) (1.6065573770491803278688523e-1 : ℝ) (1.6065573770491803278688526e-1 : ℝ) := h8.weak (by norm_num) (by norm_num)
  have h10 := Bnd.mul h7 h9 (by norm_num) (by norm_num)
  have h11 : Bnd ((((qc12 ^ 2) * (qc13 ^ 2)) * (qcdq ^ 2))) (1.5252039613537397540983604e-1 : ℝ) (1.5252039613537397540983609e-1 : ℝ) := h10.weak (by norm_num) (by norm_num)
  have h12 := Bnd.mul h1 h11 (by norm_num) (by norm_num)
  have h13 : Bnd ((((1 : ℝ) / 40960000) * (((qc12 ^ 2) * (qc13 ^ 2)) * (qcdq ^ 2)))) (3.7236424837737786965292001e-9 : ℝ) (3.7236424837737786965292015e-9 : ℝ) := h12.weak (by norm_num) (by norm_num)
  have h14 : Bnd ((1 : ℝ) / 40960000) ((1 : ℝ) / 40960000) ((1 : ℝ) / 40960000) := Bnd.const _
  have h15 := Bnd.pow qc12_bnd (by norm_num) 2
  have h16 : Bnd ((qc12 ^ 2)) (9.4937499999999999999999998e-1 : ℝ) (9.4937500000000000000000001e-1 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.pow qc13_bnd (by norm_num) 2
  have h18 : Bnd ((qc13 ^ 2)) (9.9998593749999999999999998e-1 : ℝ) (9.9998593750000000000000001e-1 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 := Bnd.mul h16 h18 (by norm_num) (by norm_num)
  have h20 : Bnd (((qc12 ^ 2) * (qc13 ^ 2))) (9.4936164941406249999999996e-1 : ℝ) (9.4936164941406250000000002e-1 : ℝ) := h19.weak (by norm_num) (by norm_num)
  have h21 := Bnd.pow qsdq_bnd (by norm_num) 2
  have h22 : Bnd ((qsdq ^ 2)) (8.3934426229508196721311471e-1 : ℝ) (8.3934426229508196721311483e-1 : ℝ) := h21.weak (by norm_num) (by norm_num)
  have h23 := Bnd.mul h20 h22 (by norm_num) (by norm_num)
  have h24 : Bnd ((((qc12 ^ 2) * (qc13 ^ 2)) * (qsdq ^ 2))) (7.9684125327868852459016385e-1 : ℝ) (7.9684125327868852459016403e-1 : ℝ) := h23.weak (by norm_num) (by norm_num)
  have h25 := Bnd.mul h14 h24 (by norm_num) (by norm_num)
  have h26 : Bnd ((((1 : ℝ) / 40960000) * (((qc12 ^ 2) * (qc13 ^ 2)) * (qsdq ^ 2)))) (1.9454132160124231557377047e-8 : ℝ) (1.9454132160124231557377052e-8 : ℝ) := h25.weak (by norm_num) (by norm_num)
  have h27 := Bnd.add h13 h26
  have h28 : Bnd (((((1 : ℝ) / 40960000) * (((qc12 ^ 2) * (qc13 ^ 2)) * (qcdq ^ 2))) + (((1 : ℝ) / 40960000) * (((qc12 ^ 2) * (qc13 ^ 2)) * (qsdq ^ 2))))) (2.3177774643898010253906247e-8 : ℝ) (2.3177774643898010253906254e-8 : ℝ) := h27.weak (by norm_num) (by norm_num)
  have h29 : Bnd ((9 : ℝ) / 256000) ((9 : ℝ) / 256000) ((9 : ℝ) / 256000) := Bnd.const _
  have h30 := Bnd.mul qc12_bnd qc23_bnd (by norm_num) (by norm_num)
  have h31 : Bnd ((qc12 * qc23)) (9.7351259853886271567207588e-1 : ℝ) (9.7351259853886271567207592e-1 : ℝ) := h30.weak (by norm_num) (by norm_num)
  have h32 := Bnd.mul h31 qcdq_bnd (by norm_num) (by norm_num)
  have h33 : Bnd (((qc12 * qc23) * qcdq)) (3.902021846498428027668863e-1 : ℝ) (3.9020218464984280276688636e-1 : ℝ) := h32.weak (by norm_num) (by norm_num)
  have h34 := Bnd.pow qc13_bnd (by norm_num) 2
  have h35 : Bnd ((qc13 ^ 2)) (9.9998593749999999999999998e-1 : ℝ) (9.9998593750000000000000001e-1 : ℝ) := h34.weak (by norm_num) (by norm_num)
  have h36 := Bnd.mul h33 h35 (by norm_num) (by norm_num)
  have h37 : Bnd ((((qc12 * qc23) * qcdq) * (qc13 ^ 2))) (3.9019669743162116435247238e-1 : ℝ) (3.9019669743162116435247246e-1 : ℝ) := h36.weak (by norm_num) (by norm_num)
  have h38 := Bnd.mul h29 h37 (by norm_num) (by norm_num)
  have h39 : Bnd ((((9 : ℝ) / 256000) * (((qc12 * qc23) * qcdq) * (qc13 ^ 2)))) (1.3717852644080431559266607e-5 : ℝ) (1.371785264408043155926661e-5 : ℝ) := h38.weak (by norm_num) (by norm_num)
  have h40 := Bnd.add h28 h39
  have h41 : Bnd ((((((1 : ℝ) / 40960000) * (((qc12 ^ 2) * (qc13 ^ 2)) * (qcdq ^ 2))) + (((1 : ℝ) / 40960000) * (((qc12 ^ 2) * (qc13 ^ 2)) * (qsdq ^ 2)))) + (((9 : ℝ) / 256000) * (((qc12 * qc23) * qcdq) * (qc13 ^ 2))))) (1.3741030418724329569520513e-5 : ℝ) (1.3741030418724329569520517e-5 : ℝ) := h40.weak (by norm_num) (by norm_num)
  exact h41

/-- `Im` of the same. -/
noncomputable def qImGamma : ℝ :=
  (((9 : ℝ) / 256000) * (((qc12 * qc23) * qsdq) * (qc13 ^ 2)))

theorem qImGamma_bnd : Bnd qImGamma (3.1355091757898129278323674e-5 : ℝ) (3.135509175789812927832368e-5 : ℝ) := by
  unfold qImGamma
  have h1 : Bnd ((9 : ℝ) / 256000) ((9 : ℝ) / 256000) ((9 : ℝ) / 256000) := Bnd.const _
  have h2 := Bnd.mul qc12_bnd qc23_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((qc12 * qc23)) (9.7351259853886271567207588e-1 : ℝ) (9.7351259853886271567207592e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.mul h3 qsdq_bnd (by norm_num) (by norm_num)
  have h5 : Bnd (((qc12 * qc23) * qsdq)) (8.9189070777106926346716871e-1 : ℝ) (8.9189070777106926346716881e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.pow qc13_bnd (by norm_num) 2
  have h7 : Bnd ((qc13 ^ 2)) (9.9998593749999999999999998e-1 : ℝ) (9.9998593750000000000000001e-1 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 := Bnd.mul h5 h7 (by norm_num) (by norm_num)
  have h9 : Bnd ((((qc12 * qc23) * qsdq) * (qc13 ^ 2))) (8.9187816555799123280565118e-1 : ℝ) (8.9187816555799123280565132e-1 : ℝ) := h8.weak (by norm_num) (by norm_num)
  have h10 := Bnd.mul h1 h9 (by norm_num) (by norm_num)
  have h11 : Bnd ((((9 : ℝ) / 256000) * (((qc12 * qc23) * qsdq) * (qc13 ^ 2)))) (3.1355091757898129278323674e-5 : ℝ) (3.135509175789812927832368e-5 : ℝ) := h10.weak (by norm_num) (by norm_num)
  exact h11

/-- `|U_e3|²`, expanded. -/
noncomputable def qU02sq : ℝ :=
  ((((qc2 ^ 2) * (qcdq ^ 2)) * (qsP ^ 2)) + (((qc2 ^ 2) * (qsP ^ 2)) * (qsdq ^ 2)))

theorem qU02sq_bnd : Bnd qU02sq (2.2148437499999999999999993e-2 : ℝ) (2.2148437500000000000000006e-2 : ℝ) := by
  unfold qU02sq
  have h1 := Bnd.pow qc2_bnd (by norm_num) 2
  have h2 : Bnd ((qc2 ^ 2)) (4.9999999999999999999999994e-1 : ℝ) (5.0000000000000000000000003e-1 : ℝ) := h1.weak (by norm_num) (by norm_num)
  have h3 := Bnd.pow qcdq_bnd (by norm_num) 2
  have h4 : Bnd ((qcdq ^ 2)) (1.6065573770491803278688523e-1 : ℝ) (1.6065573770491803278688526e-1 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 := Bnd.mul h2 h4 (by norm_num) (by norm_num)
  have h6 : Bnd (((qc2 ^ 2) * (qcdq ^ 2))) (8.0327868852459016393442605e-2 : ℝ) (8.0327868852459016393442635e-2 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.pow qsP_bnd (by norm_num) 2
  have h8 : Bnd ((qsP ^ 2)) (4.4296874999999999999999997e-2 : ℝ) (4.4296875000000000000000002e-2 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 := Bnd.mul h6 h8 (by norm_num) (by norm_num)
  have h10 : Bnd ((((qc2 ^ 2) * (qcdq ^ 2)) * (qsP ^ 2))) (3.5582735655737704918032776e-3 : ℝ) (3.5582735655737704918032794e-3 : ℝ) := h9.weak (by norm_num) (by norm_num)
  have h11 := Bnd.pow qc2_bnd (by norm_num) 2
  have h12 : Bnd ((qc2 ^ 2)) (4.9999999999999999999999994e-1 : ℝ) (5.0000000000000000000000003e-1 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 := Bnd.pow qsP_bnd (by norm_num) 2
  have h14 : Bnd ((qsP ^ 2)) (4.4296874999999999999999997e-2 : ℝ) (4.4296875000000000000000002e-2 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 := Bnd.mul h12 h14 (by norm_num) (by norm_num)
  have h16 : Bnd (((qc2 ^ 2) * (qsP ^ 2))) (2.2148437499999999999999995e-2 : ℝ) (2.2148437500000000000000003e-2 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.pow qsdq_bnd (by norm_num) 2
  have h18 : Bnd ((qsdq ^ 2)) (8.3934426229508196721311471e-1 : ℝ) (8.3934426229508196721311483e-1 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 := Bnd.mul h16 h18 (by norm_num) (by norm_num)
  have h20 : Bnd ((((qc2 ^ 2) * (qsP ^ 2)) * (qsdq ^ 2))) (1.8590163934426229508196716e-2 : ℝ) (1.8590163934426229508196726e-2 : ℝ) := h19.weak (by norm_num) (by norm_num)
  have h21 := Bnd.add h10 h20
  have h22 : Bnd (((((qc2 ^ 2) * (qcdq ^ 2)) * (qsP ^ 2)) + (((qc2 ^ 2) * (qsP ^ 2)) * (qsdq ^ 2)))) (2.2148437499999999999999993e-2 : ℝ) (2.2148437500000000000000006e-2 : ℝ) := h21.weak (by norm_num) (by norm_num)
  exact h22

/-- `|U_e2|²`, expanded. -/
noncomputable def qU01sq : ℝ :=
  (((((qcP ^ 2) * (qsB ^ 2)) + (((9 : ℝ) / 16) * (((qc2 ^ 2) * (qcdq ^ 2)) * (qsP ^ 2)))) + (((9 : ℝ) / 16) * (((qc2 ^ 2) * (qsP ^ 2)) * (qsdq ^ 2)))) - (((3 : ℝ) / 2) * ((((qc2 * qcP) * qsB) * qsP) * qsdq)))

theorem qU01sq_bnd : Bnd qU01sq (2.9833235274321608965544e-1 : ℝ) (2.9833235274321608965544013e-1 : ℝ) := by
  unfold qU01sq
  have h1 := Bnd.pow qcP_bnd (by norm_num) 2
  have h2 : Bnd ((qcP ^ 2)) (9.5570312499999999999999997e-1 : ℝ) (9.5570312500000000000000002e-1 : ℝ) := h1.weak (by norm_num) (by norm_num)
  have h3 := Bnd.pow qsB_bnd (by norm_num) 2
  have h4 : Bnd ((qsB ^ 2)) (4.3749999999999999999999998e-1 : ℝ) (4.3750000000000000000000001e-1 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 := Bnd.mul h2 h4 (by norm_num) (by norm_num)
  have h6 : Bnd (((qcP ^ 2) * (qsB ^ 2))) (4.1812011718749999999999996e-1 : ℝ) (4.1812011718750000000000002e-1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 : Bnd ((9 : ℝ) / 16) ((9 : ℝ) / 16) ((9 : ℝ) / 16) := Bnd.const _
  have h8 := Bnd.pow qc2_bnd (by norm_num) 2
  have h9 : Bnd ((qc2 ^ 2)) (4.9999999999999999999999994e-1 : ℝ) (5.0000000000000000000000003e-1 : ℝ) := h8.weak (by norm_num) (by norm_num)
  have h10 := Bnd.pow qcdq_bnd (by norm_num) 2
  have h11 : Bnd ((qcdq ^ 2)) (1.6065573770491803278688523e-1 : ℝ) (1.6065573770491803278688526e-1 : ℝ) := h10.weak (by norm_num) (by norm_num)
  have h12 := Bnd.mul h9 h11 (by norm_num) (by norm_num)
  have h13 : Bnd (((qc2 ^ 2) * (qcdq ^ 2))) (8.0327868852459016393442605e-2 : ℝ) (8.0327868852459016393442635e-2 : ℝ) := h12.weak (by norm_num) (by norm_num)
  have h14 := Bnd.pow qsP_bnd (by norm_num) 2
  have h15 : Bnd ((qsP ^ 2)) (4.4296874999999999999999997e-2 : ℝ) (4.4296875000000000000000002e-2 : ℝ) := h14.weak (by norm_num) (by norm_num)
  have h16 := Bnd.mul h13 h15 (by norm_num) (by norm_num)
  have h17 : Bnd ((((qc2 ^ 2) * (qcdq ^ 2)) * (qsP ^ 2))) (3.5582735655737704918032776e-3 : ℝ) (3.5582735655737704918032794e-3 : ℝ) := h16.weak (by norm_num) (by norm_num)
  have h18 := Bnd.mul h7 h17 (by norm_num) (by norm_num)
  have h19 : Bnd ((((9 : ℝ) / 16) * (((qc2 ^ 2) * (qcdq ^ 2)) * (qsP ^ 2)))) (2.0015288806352459016393436e-3 : ℝ) (2.0015288806352459016393447e-3 : ℝ) := h18.weak (by norm_num) (by norm_num)
  have h20 := Bnd.add h6 h19
  have h21 : Bnd ((((qcP ^ 2) * (qsB ^ 2)) + (((9 : ℝ) / 16) * (((qc2 ^ 2) * (qcdq ^ 2)) * (qsP ^ 2))))) (4.201216460681352459016393e-1 : ℝ) (4.2012164606813524590163937e-1 : ℝ) := h20.weak (by norm_num) (by norm_num)
  have h22 : Bnd ((9 : ℝ) / 16) ((9 : ℝ) / 16) ((9 : ℝ) / 16) := Bnd.const _
  have h23 := Bnd.pow qc2_bnd (by norm_num) 2
  have h24 : Bnd ((qc2 ^ 2)) (4.9999999999999999999999994e-1 : ℝ) (5.0000000000000000000000003e-1 : ℝ) := h23.weak (by norm_num) (by norm_num)
  have h25 := Bnd.pow qsP_bnd (by norm_num) 2
  have h26 : Bnd ((qsP ^ 2)) (4.4296874999999999999999997e-2 : ℝ) (4.4296875000000000000000002e-2 : ℝ) := h25.weak (by norm_num) (by norm_num)
  have h27 := Bnd.mul h24 h26 (by norm_num) (by norm_num)
  have h28 : Bnd (((qc2 ^ 2) * (qsP ^ 2))) (2.2148437499999999999999995e-2 : ℝ) (2.2148437500000000000000003e-2 : ℝ) := h27.weak (by norm_num) (by norm_num)
  have h29 := Bnd.pow qsdq_bnd (by norm_num) 2
  have h30 : Bnd ((qsdq ^ 2)) (8.3934426229508196721311471e-1 : ℝ) (8.3934426229508196721311483e-1 : ℝ) := h29.weak (by norm_num) (by norm_num)
  have h31 := Bnd.mul h28 h30 (by norm_num) (by norm_num)
  have h32 : Bnd ((((qc2 ^ 2) * (qsP ^ 2)) * (qsdq ^ 2))) (1.8590163934426229508196716e-2 : ℝ) (1.8590163934426229508196726e-2 : ℝ) := h31.weak (by norm_num) (by norm_num)
  have h33 := Bnd.mul h22 h32 (by norm_num) (by norm_num)
  have h34 : Bnd ((((9 : ℝ) / 16) * (((qc2 ^ 2) * (qsP ^ 2)) * (qsdq ^ 2)))) (1.0456967213114754098360652e-2 : ℝ) (1.0456967213114754098360659e-2 : ℝ) := h33.weak (by norm_num) (by norm_num)
  have h35 := Bnd.add h21 h34
  have h36 : Bnd (((((qcP ^ 2) * (qsB ^ 2)) + (((9 : ℝ) / 16) * (((qc2 ^ 2) * (qcdq ^ 2)) * (qsP ^ 2)))) + (((9 : ℝ) / 16) * (((qc2 ^ 2) * (qsP ^ 2)) * (qsdq ^ 2))))) (4.3057861328124999999999995e-1 : ℝ) (4.3057861328125000000000003e-1 : ℝ) := h35.weak (by norm_num) (by norm_num)
  have h37 : Bnd ((3 : ℝ) / 2) ((3 : ℝ) / 2) ((3 : ℝ) / 2) := Bnd.const _
  have h38 := Bnd.mul qc2_bnd qcP_bnd (by norm_num) (by norm_num)
  have h39 : Bnd ((qc2 * qcP)) (6.9126808294611722222179942e-1 : ℝ) (6.912680829461172222217995e-1 : ℝ) := h38.weak (by norm_num) (by norm_num)
  have h40 := Bnd.mul h39 qsB_bnd (by norm_num) (by norm_num)
  have h41 : Bnd (((qc2 * qcP) * qsB)) (4.5723085918794894918135343e-1 : ℝ) (4.572308591879489491813535e-1 : ℝ) := h40.weak (by norm_num) (by norm_num)
  have h42 := Bnd.mul h41 qsP_bnd (by norm_num) (by norm_num)
  have h43 : Bnd ((((qc2 * qcP) * qsB) * qsP)) (9.6232568722964158083014181e-2 : ℝ) (9.6232568722964158083014201e-2 : ℝ) := h42.weak (by norm_num) (by norm_num)
  have h44 := Bnd.mul h43 qsdq_bnd (by norm_num) (by norm_num)
  have h45 : Bnd (((((qc2 * qcP) * qsB) * qsP) * qsdq)) (8.8164173692022606896373273e-2 : ℝ) (8.8164173692022606896373298e-2 : ℝ) := h44.weak (by norm_num) (by norm_num)
  have h46 := Bnd.mul h37 h45 (by norm_num) (by norm_num)
  have h47 : Bnd ((((3 : ℝ) / 2) * ((((qc2 * qcP) * qsB) * qsP) * qsdq))) (1.322462605380339103445599e-1 : ℝ) (1.3224626053803391034455995e-1 : ℝ) := h46.weak (by norm_num) (by norm_num)
  have h48 := Bnd.sub h36 h47
  have h49 : Bnd ((((((qcP ^ 2) * (qsB ^ 2)) + (((9 : ℝ) / 16) * (((qc2 ^ 2) * (qcdq ^ 2)) * (qsP ^ 2)))) + (((9 : ℝ) / 16) * (((qc2 ^ 2) * (qsP ^ 2)) * (qsdq ^ 2)))) - (((3 : ℝ) / 2) * ((((qc2 * qcP) * qsB) * qsP) * qsdq)))) (2.9833235274321608965544e-1 : ℝ) (2.9833235274321608965544013e-1 : ℝ) := h48.weak (by norm_num) (by norm_num)
  exact h49

/-- `|U_μ3|²`, expanded. -/
noncomputable def qU12sq : ℝ :=
  ((qc2 ^ 2) * (qcP ^ 2))

theorem qU12sq_bnd : Bnd qU12sq (4.7785156249999999999999992e-1 : ℝ) (4.7785156250000000000000004e-1 : ℝ) := by
  unfold qU12sq
  have h1 := Bnd.pow qc2_bnd (by norm_num) 2
  have h2 : Bnd ((qc2 ^ 2)) (4.9999999999999999999999994e-1 : ℝ) (5.0000000000000000000000003e-1 : ℝ) := h1.weak (by norm_num) (by norm_num)
  have h3 := Bnd.pow qcP_bnd (by norm_num) 2
  have h4 : Bnd ((qcP ^ 2)) (9.5570312499999999999999997e-1 : ℝ) (9.5570312500000000000000002e-1 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 := Bnd.mul h2 h4 (by norm_num) (by norm_num)
  have h6 : Bnd (((qc2 ^ 2) * (qcP ^ 2))) (4.7785156249999999999999992e-1 : ℝ) (4.7785156250000000000000004e-1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  exact h6

/-- `|U_μ1|²`, expanded. -/
noncomputable def qU10sq : ℝ :=
  ((((((9 : ℝ) / 16) * ((qcdq ^ 2) * (qsP ^ 2))) + (((9 : ℝ) / 16) * ((qsP ^ 2) * (qsdq ^ 2)))) + (((qc2 ^ 2) * (qcP ^ 2)) * (qsB ^ 2))) - (((3 : ℝ) / 2) * ((((qc2 * qcP) * qsB) * qsP) * qsdq)))

theorem qU10sq_bnd : Bnd qU10sq (1.0173079024321608965543999e-1 : ℝ) (1.0173079024321608965544014e-1 : ℝ) := by
  unfold qU10sq
  have h1 : Bnd ((9 : ℝ) / 16) ((9 : ℝ) / 16) ((9 : ℝ) / 16) := Bnd.const _
  have h2 := Bnd.pow qcdq_bnd (by norm_num) 2
  have h3 : Bnd ((qcdq ^ 2)) (1.6065573770491803278688523e-1 : ℝ) (1.6065573770491803278688526e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.pow qsP_bnd (by norm_num) 2
  have h5 : Bnd ((qsP ^ 2)) (4.4296874999999999999999997e-2 : ℝ) (4.4296875000000000000000002e-2 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.mul h3 h5 (by norm_num) (by norm_num)
  have h7 : Bnd (((qcdq ^ 2) * (qsP ^ 2))) (7.1165471311475409836065561e-3 : ℝ) (7.1165471311475409836065584e-3 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 := Bnd.mul h1 h7 (by norm_num) (by norm_num)
  have h9 : Bnd ((((9 : ℝ) / 16) * ((qcdq ^ 2) * (qsP ^ 2)))) (4.0030577612704918032786878e-3 : ℝ) (4.0030577612704918032786891e-3 : ℝ) := h8.weak (by norm_num) (by norm_num)
  have h10 : Bnd ((9 : ℝ) / 16) ((9 : ℝ) / 16) ((9 : ℝ) / 16) := Bnd.const _
  have h11 := Bnd.pow qsP_bnd (by norm_num) 2
  have h12 : Bnd ((qsP ^ 2)) (4.4296874999999999999999997e-2 : ℝ) (4.4296875000000000000000002e-2 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 := Bnd.pow qsdq_bnd (by norm_num) 2
  have h14 : Bnd ((qsdq ^ 2)) (8.3934426229508196721311471e-1 : ℝ) (8.3934426229508196721311483e-1 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 := Bnd.mul h12 h14 (by norm_num) (by norm_num)
  have h16 : Bnd (((qsP ^ 2) * (qsdq ^ 2))) (3.7180327868852459016393438e-2 : ℝ) (3.7180327868852459016393448e-2 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.mul h10 h16 (by norm_num) (by norm_num)
  have h18 : Bnd ((((9 : ℝ) / 16) * ((qsP ^ 2) * (qsdq ^ 2)))) (2.0913934426229508196721308e-2 : ℝ) (2.0913934426229508196721315e-2 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 := Bnd.add h9 h18
  have h20 : Bnd (((((9 : ℝ) / 16) * ((qcdq ^ 2) * (qsP ^ 2))) + (((9 : ℝ) / 16) * ((qsP ^ 2) * (qsdq ^ 2))))) (2.4916992187499999999999995e-2 : ℝ) (2.4916992187500000000000005e-2 : ℝ) := h19.weak (by norm_num) (by norm_num)
  have h21 := Bnd.pow qc2_bnd (by norm_num) 2
  have h22 : Bnd ((qc2 ^ 2)) (4.9999999999999999999999994e-1 : ℝ) (5.0000000000000000000000003e-1 : ℝ) := h21.weak (by norm_num) (by norm_num)
  have h23 := Bnd.pow qcP_bnd (by norm_num) 2
  have h24 : Bnd ((qcP ^ 2)) (9.5570312499999999999999997e-1 : ℝ) (9.5570312500000000000000002e-1 : ℝ) := h23.weak (by norm_num) (by norm_num)
  have h25 := Bnd.mul h22 h24 (by norm_num) (by norm_num)
  have h26 : Bnd (((qc2 ^ 2) * (qcP ^ 2))) (4.7785156249999999999999992e-1 : ℝ) (4.7785156250000000000000004e-1 : ℝ) := h25.weak (by norm_num) (by norm_num)
  have h27 := Bnd.pow qsB_bnd (by norm_num) 2
  have h28 : Bnd ((qsB ^ 2)) (4.3749999999999999999999998e-1 : ℝ) (4.3750000000000000000000001e-1 : ℝ) := h27.weak (by norm_num) (by norm_num)
  have h29 := Bnd.mul h26 h28 (by norm_num) (by norm_num)
  have h30 : Bnd ((((qc2 ^ 2) * (qcP ^ 2)) * (qsB ^ 2))) (2.0906005859374999999999995e-1 : ℝ) (2.0906005859375000000000003e-1 : ℝ) := h29.weak (by norm_num) (by norm_num)
  have h31 := Bnd.add h20 h30
  have h32 : Bnd ((((((9 : ℝ) / 16) * ((qcdq ^ 2) * (qsP ^ 2))) + (((9 : ℝ) / 16) * ((qsP ^ 2) * (qsdq ^ 2)))) + (((qc2 ^ 2) * (qcP ^ 2)) * (qsB ^ 2)))) (2.3397705078124999999999994e-1 : ℝ) (2.3397705078125000000000004e-1 : ℝ) := h31.weak (by norm_num) (by norm_num)
  have h33 : Bnd ((3 : ℝ) / 2) ((3 : ℝ) / 2) ((3 : ℝ) / 2) := Bnd.const _
  have h34 := Bnd.mul qc2_bnd qcP_bnd (by norm_num) (by norm_num)
  have h35 : Bnd ((qc2 * qcP)) (6.9126808294611722222179942e-1 : ℝ) (6.912680829461172222217995e-1 : ℝ) := h34.weak (by norm_num) (by norm_num)
  have h36 := Bnd.mul h35 qsB_bnd (by norm_num) (by norm_num)
  have h37 : Bnd (((qc2 * qcP) * qsB)) (4.5723085918794894918135343e-1 : ℝ) (4.572308591879489491813535e-1 : ℝ) := h36.weak (by norm_num) (by norm_num)
  have h38 := Bnd.mul h37 qsP_bnd (by norm_num) (by norm_num)
  have h39 : Bnd ((((qc2 * qcP) * qsB) * qsP)) (9.6232568722964158083014181e-2 : ℝ) (9.6232568722964158083014201e-2 : ℝ) := h38.weak (by norm_num) (by norm_num)
  have h40 := Bnd.mul h39 qsdq_bnd (by norm_num) (by norm_num)
  have h41 : Bnd (((((qc2 * qcP) * qsB) * qsP) * qsdq)) (8.8164173692022606896373273e-2 : ℝ) (8.8164173692022606896373298e-2 : ℝ) := h40.weak (by norm_num) (by norm_num)
  have h42 := Bnd.mul h33 h41 (by norm_num) (by norm_num)
  have h43 : Bnd ((((3 : ℝ) / 2) * ((((qc2 * qcP) * qsB) * qsP) * qsdq))) (1.322462605380339103445599e-1 : ℝ) (1.3224626053803391034455995e-1 : ℝ) := h42.weak (by norm_num) (by norm_num)
  have h44 := Bnd.sub h32 h43
  have h45 : Bnd (((((((9 : ℝ) / 16) * ((qcdq ^ 2) * (qsP ^ 2))) + (((9 : ℝ) / 16) * ((qsP ^ 2) * (qsdq ^ 2)))) + (((qc2 ^ 2) * (qcP ^ 2)) * (qsB ^ 2))) - (((3 : ℝ) / 2) * ((((qc2 * qcP) * qsB) * qsP) * qsdq)))) (1.0173079024321608965543999e-1 : ℝ) (1.0173079024321608965544014e-1 : ℝ) := h44.weak (by norm_num) (by norm_num)
  exact h45

/-- `Im(U_e1 U_μ2 U_e2* U_μ1*)`, expanded. -/
noncomputable def qJl : ℝ :=
  (((((((((3 : ℝ) / 4) * ((((qcP * (qc2 ^ 3)) * (qcdq ^ 3)) * (qsB ^ 3)) * (qsP ^ 3))) + (((3 : ℝ) / 4) * ((((qcdq * qsP) * (qc2 ^ 3)) * (qcP ^ 3)) * (qsB ^ 3)))) + (((27 : ℝ) / 64) * ((((qcP * qsB) * (qc2 ^ 3)) * (qcdq ^ 3)) * (qsP ^ 3)))) + (((27 : ℝ) / 64) * ((((qcdq * qsB) * qsP) * (qc2 ^ 3)) * (qcP ^ 3)))) + (((3 : ℝ) / 4) * (((((qcP * qcdq) * (qc2 ^ 3)) * (qsB ^ 3)) * (qsP ^ 3)) * (qsdq ^ 2)))) + (((27 : ℝ) / 64) * (((((qcP * qcdq) * qsB) * (qc2 ^ 3)) * (qsP ^ 3)) * (qsdq ^ 2)))) - ((((((((27 : ℝ) / 64) * ((((qc2 * qcP) * qsB) * (qcdq ^ 3)) * (qsP ^ 3))) + (((27 : ℝ) / 64) * ((((qc2 * qcdq) * qsB) * qsP) * (qcP ^ 3)))) + (((3 : ℝ) / 4) * ((((qc2 * qcP) * (qcdq ^ 3)) * (qsB ^ 3)) * (qsP ^ 3)))) + (((3 : ℝ) / 4) * ((((qc2 * qcdq) * qsP) * (qcP ^ 3)) * (qsB ^ 3)))) + (((27 : ℝ) / 64) * (((((qc2 * qcP) * qcdq) * qsB) * (qsP ^ 3)) * (qsdq ^ 2)))) + (((3 : ℝ) / 4) * (((((qc2 * qcP) * qcdq) * (qsB ^ 3)) * (qsP ^ 3)) * (qsdq ^ 2)))))

theorem qJl_bnd : Bnd qJl (-1.4464434746347458943936259e-2 : ℝ) (-1.4464434746347458943936225e-2 : ℝ) := by
  unfold qJl
  have h1 : Bnd ((3 : ℝ) / 4) ((3 : ℝ) / 4) ((3 : ℝ) / 4) := Bnd.const _
  have h2 := Bnd.pow qc2_bnd (by norm_num) 3
  have h3 : Bnd ((qc2 ^ 3)) (3.5355339059327376220042211e-1 : ℝ) (3.5355339059327376220042221e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.mul qcP_bnd h3 (by norm_num) (by norm_num)
  have h5 : Bnd ((qcP * (qc2 ^ 3))) (3.4563404147305861111089966e-1 : ℝ) (3.4563404147305861111089977e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.pow qcdq_bnd (by norm_num) 3
  have h7 : Bnd ((qcdq ^ 3)) (6.4393845465461245489794327e-2 : ℝ) (6.4393845465461245489794342e-2 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 := Bnd.mul h5 h7 (by norm_num) (by norm_num)
  have h9 : Bnd (((qcP * (qc2 ^ 3)) * (qcdq ^ 3))) (2.2256705054218959307511638e-2 : ℝ) (2.2256705054218959307511651e-2 : ℝ) := h8.weak (by norm_num) (by norm_num)
  have h10 := Bnd.pow qsB_bnd (by norm_num) 3
  have h11 : Bnd ((qsB ^ 3)) (2.8937904964768959583611421e-1 : ℝ) (2.8937904964768959583611423e-1 : ℝ) := h10.weak (by norm_num) (by norm_num)
  have h12 := Bnd.mul h9 h11 (by norm_num) (by norm_num)
  have h13 : Bnd ((((qcP * (qc2 ^ 3)) * (qcdq ^ 3)) * (qsB ^ 3))) (6.4406241568788121833880945e-3 : ℝ) (6.4406241568788121833880988e-3 : ℝ) := h12.weak (by norm_num) (by norm_num)
  have h14 := Bnd.pow qsP_bnd (by norm_num) 3
  have h15 : Bnd ((qsP ^ 3)) (9.3230847874547963333173184e-3 : ℝ) (9.3230847874547963333173198e-3 : ℝ) := h14.weak (by norm_num) (by norm_num)
  have h16 := Bnd.mul h13 h15 (by norm_num) (by norm_num)
  have h17 : Bnd (((((qcP * (qc2 ^ 3)) * (qcdq ^ 3)) * (qsB ^ 3)) * (qsP ^ 3))) (6.0046485098710727520399227e-5 : ℝ) (6.0046485098710727520399277e-5 : ℝ) := h16.weak (by norm_num) (by norm_num)
  have h18 := Bnd.mul h1 h17 (by norm_num) (by norm_num)
  have h19 : Bnd ((((3 : ℝ) / 4) * ((((qcP * (qc2 ^ 3)) * (qcdq ^ 3)) * (qsB ^ 3)) * (qsP ^ 3)))) (4.503486382403304564029942e-5 : ℝ) (4.5034863824033045640299458e-5 : ℝ) := h18.weak (by norm_num) (by norm_num)
  have h20 : Bnd ((3 : ℝ) / 4) ((3 : ℝ) / 4) ((3 : ℝ) / 4) := Bnd.const _
  have h21 := Bnd.mul qcdq_bnd qsP_bnd (by norm_num) (by norm_num)
  have h22 : Bnd ((qcdq * qsP)) (8.4359629747572629940926597e-2 : ℝ) (8.4359629747572629940926608e-2 : ℝ) := h21.weak (by norm_num) (by norm_num)
  have h23 := Bnd.pow qc2_bnd (by norm_num) 3
  have h24 : Bnd ((qc2 ^ 3)) (3.5355339059327376220042211e-1 : ℝ) (3.5355339059327376220042221e-1 : ℝ) := h23.weak (by norm_num) (by norm_num)
  have h25 := Bnd.mul h22 h24 (by norm_num) (by norm_num)
  have h26 : Bnd (((qcdq * qsP) * (qc2 ^ 3))) (2.9825633126447502505007157e-2 : ℝ) (2.982563312644750250500717e-2 : ℝ) := h25.weak (by norm_num) (by norm_num)
  have h27 := Bnd.pow qcP_bnd (by norm_num) 3
  have h28 : Bnd ((qcP ^ 3)) (9.3429604221271471891231158e-1 : ℝ) (9.3429604221271471891231164e-1 : ℝ) := h27.weak (by norm_num) (by norm_num)
  have h29 := Bnd.mul h26 h28 (by norm_num) (by norm_num)
  have h30 : Bnd ((((qcdq * qsP) * (qc2 ^ 3)) * (qcP ^ 3))) (2.7865970986528338278087281e-2 : ℝ) (2.7865970986528338278087296e-2 : ℝ) := h29.weak (by norm_num) (by norm_num)
  have h31 := Bnd.pow qsB_bnd (by norm_num) 3
  have h32 : Bnd ((qsB ^ 3)) (2.8937904964768959583611421e-1 : ℝ) (2.8937904964768959583611423e-1 : ℝ) := h31.weak (by norm_num) (by norm_num)
  have h33 := Bnd.mul h30 h32 (by norm_num) (by norm_num)
  have h34 : Bnd (((((qcdq * qsP) * (qc2 ^ 3)) * (qcP ^ 3)) * (qsB ^ 3))) (8.0638282015916618283086191e-3 : ℝ) (8.0638282015916618283086241e-3 : ℝ) := h33.weak (by norm_num) (by norm_num)
  have h35 := Bnd.mul h20 h34 (by norm_num) (by norm_num)
  have h36 : Bnd ((((3 : ℝ) / 4) * ((((qcdq * qsP) * (qc2 ^ 3)) * (qcP ^ 3)) * (qsB ^ 3)))) (6.0478711511937463712314643e-3 : ℝ) (6.0478711511937463712314681e-3 : ℝ) := h35.weak (by norm_num) (by norm_num)
  have h37 := Bnd.add h19 h36
  have h38 : Bnd (((((3 : ℝ) / 4) * ((((qcP * (qc2 ^ 3)) * (qcdq ^ 3)) * (qsB ^ 3)) * (qsP ^ 3))) + (((3 : ℝ) / 4) * ((((qcdq * qsP) * (qc2 ^ 3)) * (qcP ^ 3)) * (qsB ^ 3))))) (6.0929060150177794168717637e-3 : ℝ) (6.0929060150177794168717676e-3 : ℝ) := h37.weak (by norm_num) (by norm_num)
  have h39 : Bnd ((27 : ℝ) / 64) ((27 : ℝ) / 64) ((27 : ℝ) / 64) := Bnd.const _
  have h40 := Bnd.mul qcP_bnd qsB_bnd (by norm_num) (by norm_num)
  have h41 : Bnd ((qcP * qsB)) (6.4662208219910028061828474e-1 : ℝ) (6.4662208219910028061828477e-1 : ℝ) := h40.weak (by norm_num) (by norm_num)
  have h42 := Bnd.pow qc2_bnd (by norm_num) 3
  have h43 : Bnd ((qc2 ^ 3)) (3.5355339059327376220042211e-1 : ℝ) (3.5355339059327376220042221e-1 : ℝ) := h42.weak (by norm_num) (by norm_num)
  have h44 := Bnd.mul h41 h43 (by norm_num) (by norm_num)
  have h45 : Bnd (((qcP * qsB) * (qc2 ^ 3))) (2.2861542959397447459067668e-1 : ℝ) (2.2861542959397447459067676e-1 : ℝ) := h44.weak (by norm_num) (by norm_num)
  have h46 := Bnd.pow qcdq_bnd (by norm_num) 3
  have h47 : Bnd ((qcdq ^ 3)) (6.4393845465461245489794327e-2 : ℝ) (6.4393845465461245489794342e-2 : ℝ) := h46.weak (by norm_num) (by norm_num)
  have h48 := Bnd.mul h45 h47 (by norm_num) (by norm_num)
  have h49 : Bnd ((((qcP * qsB) * (qc2 ^ 3)) * (qcdq ^ 3))) (1.4721426644294427847744216e-2 : ℝ) (1.4721426644294427847744226e-2 : ℝ) := h48.weak (by norm_num) (by norm_num)
  have h50 := Bnd.pow qsP_bnd (by norm_num) 3
  have h51 : Bnd ((qsP ^ 3)) (9.3230847874547963333173184e-3 : ℝ) (9.3230847874547963333173198e-3 : ℝ) := h50.weak (by norm_num) (by norm_num)
  have h52 := Bnd.mul h49 h51 (by norm_num) (by norm_num)
  have h53 : Bnd (((((qcP * qsB) * (qc2 ^ 3)) * (qcdq ^ 3)) * (qsP ^ 3))) (1.3724910879705309147519823e-4 : ℝ) (1.3724910879705309147519835e-4 : ℝ) := h52.weak (by norm_num) (by norm_num)
  have h54 := Bnd.mul h39 h53 (by norm_num) (by norm_num)
  have h55 : Bnd ((((27 : ℝ) / 64) * ((((qcP * qsB) * (qc2 ^ 3)) * (qcdq ^ 3)) * (qsP ^ 3)))) (5.7901967773756772966099253e-5 : ℝ) (5.7901967773756772966099304e-5 : ℝ) := h54.weak (by norm_num) (by norm_num)
  have h56 := Bnd.add h38 h55
  have h57 : Bnd ((((((3 : ℝ) / 4) * ((((qcP * (qc2 ^ 3)) * (qcdq ^ 3)) * (qsB ^ 3)) * (qsP ^ 3))) + (((3 : ℝ) / 4) * ((((qcdq * qsP) * (qc2 ^ 3)) * (qcP ^ 3)) * (qsB ^ 3)))) + (((27 : ℝ) / 64) * ((((qcP * qsB) * (qc2 ^ 3)) * (qcdq ^ 3)) * (qsP ^ 3))))) (6.1508079827915361898378629e-3 : ℝ) (6.150807982791536189837867e-3 : ℝ) := h56.weak (by norm_num) (by norm_num)
  have h58 : Bnd ((27 : ℝ) / 64) ((27 : ℝ) / 64) ((27 : ℝ) / 64) := Bnd.const _
  have h59 := Bnd.mul qcdq_bnd qsB_bnd (by norm_num) (by norm_num)
  have h60 : Bnd ((qcdq * qsB)) (2.651167389017555778222859e-1 : ℝ) (2.6511673890175557782228593e-1 : ℝ) := h59.weak (by norm_num) (by norm_num)
  have h61 := Bnd.mul h60 qsP_bnd (by norm_num) (by norm_num)
  have h62 : Bnd (((qcdq * qsB) * qsP)) (5.5798650251390930758454444e-2 : ℝ) (5.5798650251390930758454454e-2 : ℝ) := h61.weak (by norm_num) (by norm_num)
  have h63 := Bnd.pow qc2_bnd (by norm_num) 3
  have h64 : Bnd ((qc2 ^ 3)) (3.5355339059327376220042211e-1 : ℝ) (3.5355339059327376220042221e-1 : ℝ) := h63.weak (by norm_num) (by norm_num)
  have h65 := Bnd.mul h62 h64 (by norm_num) (by norm_num)
  have h66 : Bnd ((((qcdq * qsB) * qsP) * (qc2 ^ 3))) (1.9727801986907490945255066e-2 : ℝ) (1.9727801986907490945255076e-2 : ℝ) := h65.weak (by norm_num) (by norm_num)
  have h67 := Bnd.pow qcP_bnd (by norm_num) 3
  have h68 : Bnd ((qcP ^ 3)) (9.3429604221271471891231158e-1 : ℝ) (9.3429604221271471891231164e-1 : ℝ) := h67.weak (by norm_num) (by norm_num)
  have h69 := Bnd.mul h66 h68 (by norm_num) (by norm_num)
  have h70 : Bnd (((((qcdq * qsB) * qsP) * (qc2 ^ 3)) * (qcP ^ 3))) (1.8431607317923798464705415e-2 : ℝ) (1.8431607317923798464705427e-2 : ℝ) := h69.weak (by norm_num) (by norm_num)
  have h71 := Bnd.mul h58 h70 (by norm_num) (by norm_num)
  have h72 : Bnd ((((27 : ℝ) / 64) * ((((qcdq * qsB) * qsP) * (qc2 ^ 3)) * (qcP ^ 3)))) (7.7758343372491024772975969e-3 : ℝ) (7.7758343372491024772976021e-3 : ℝ) := h71.weak (by norm_num) (by norm_num)
  have h73 := Bnd.add h57 h72
  have h74 : Bnd (((((((3 : ℝ) / 4) * ((((qcP * (qc2 ^ 3)) * (qcdq ^ 3)) * (qsB ^ 3)) * (qsP ^ 3))) + (((3 : ℝ) / 4) * ((((qcdq * qsP) * (qc2 ^ 3)) * (qcP ^ 3)) * (qsB ^ 3)))) + (((27 : ℝ) / 64) * ((((qcP * qsB) * (qc2 ^ 3)) * (qcdq ^ 3)) * (qsP ^ 3)))) + (((27 : ℝ) / 64) * ((((qcdq * qsB) * qsP) * (qc2 ^ 3)) * (qcP ^ 3))))) (1.3926642320040638667135459e-2 : ℝ) (1.392664232004063866713547e-2 : ℝ) := h73.weak (by norm_num) (by norm_num)
  have h75 : Bnd ((3 : ℝ) / 4) ((3 : ℝ) / 4) ((3 : ℝ) / 4) := Bnd.const _
  have h76 := Bnd.mul qcP_bnd qcdq_bnd (by norm_num) (by norm_num)
  have h77 : Bnd ((qcP * qcdq)) (3.9184077196454491953943681e-1 : ℝ) (3.9184077196454491953943685e-1 : ℝ) := h76.weak (by norm_num) (by norm_num)
  have h78 := Bnd.pow qc2_bnd (by norm_num) 3
  have h79 : Bnd ((qc2 ^ 3)) (3.5355339059327376220042211e-1 : ℝ) (3.5355339059327376220042221e-1 : ℝ) := h78.weak (by norm_num) (by norm_num)
  have h80 := Bnd.mul h77 h79 (by norm_num) (by norm_num)
  have h81 : Bnd (((qcP * qcdq) * (qc2 ^ 3))) (1.3853663350075066507736837e-1 : ℝ) (1.3853663350075066507736843e-1 : ℝ) := h80.weak (by norm_num) (by norm_num)
  have h82 := Bnd.pow qsB_bnd (by norm_num) 3
  have h83 : Bnd ((qsB ^ 3)) (2.8937904964768959583611421e-1 : ℝ) (2.8937904964768959583611423e-1 : ℝ) := h82.weak (by norm_num) (by norm_num)
  have h84 := Bnd.mul h81 h83 (by norm_num) (by norm_num)
  have h85 : Bnd ((((qcP * qcdq) * (qc2 ^ 3)) * (qsB ^ 3))) (4.0089599343837504406803448e-2 : ℝ) (4.0089599343837504406803469e-2 : ℝ) := h84.weak (by norm_num) (by norm_num)
  have h86 := Bnd.pow qsP_bnd (by norm_num) 3
  have h87 : Bnd ((qsP ^ 3)) (9.3230847874547963333173184e-3 : ℝ) (9.3230847874547963333173198e-3 : ℝ) := h86.weak (by norm_num) (by norm_num)
  have h88 := Bnd.mul h85 h87 (by norm_num) (by norm_num)
  have h89 : Bnd (((((qcP * qcdq) * (qc2 ^ 3)) * (qsB ^ 3)) * (qsP ^ 3))) (3.7375873377768922232085235e-4 : ℝ) (3.7375873377768922232085261e-4 : ℝ) := h88.weak (by norm_num) (by norm_num)
  have h90 := Bnd.pow qsdq_bnd (by norm_num) 2
  have h91 : Bnd ((qsdq ^ 2)) (8.3934426229508196721311471e-1 : ℝ) (8.3934426229508196721311483e-1 : ℝ) := h90.weak (by norm_num) (by norm_num)
  have h92 := Bnd.mul h89 h91 (by norm_num) (by norm_num)
  have h93 : Bnd ((((((qcP * qcdq) * (qc2 ^ 3)) * (qsB ^ 3)) * (qsP ^ 3)) * (qsdq ^ 2))) (3.137122486789784948004531e-4 : ℝ) (3.1371224867897849480045337e-4 : ℝ) := h92.weak (by norm_num) (by norm_num)
  have h94 := Bnd.mul h75 h93 (by norm_num) (by norm_num)
  have h95 : Bnd ((((3 : ℝ) / 4) * (((((qcP * qcdq) * (qc2 ^ 3)) * (qsB ^ 3)) * (qsP ^ 3)) * (qsdq ^ 2)))) (2.3528418650923387110033982e-4 : ℝ) (2.3528418650923387110034003e-4 : ℝ) := h94.weak (by norm_num) (by norm_num)
  have h96 := Bnd.add h74 h95
  have h97 : Bnd ((((((((3 : ℝ) / 4) * ((((qcP * (qc2 ^ 3)) * (qcdq ^ 3)) * (qsB ^ 3)) * (qsP ^ 3))) + (((3 : ℝ) / 4) * ((((qcdq * qsP) * (qc2 ^ 3)) * (qcP ^ 3)) * (qsB ^ 3)))) + (((27 : ℝ) / 64) * ((((qcP * qsB) * (qc2 ^ 3)) * (qcdq ^ 3)) * (qsP ^ 3)))) + (((27 : ℝ) / 64) * ((((qcdq * qsB) * qsP) * (qc2 ^ 3)) * (qcP ^ 3)))) + (((3 : ℝ) / 4) * (((((qcP * qcdq) * (qc2 ^ 3)) * (qsB ^ 3)) * (qsP ^ 3)) * (qsdq ^ 2))))) (1.4161926506549872538235798e-2 : ℝ) (1.4161926506549872538235811e-2 : ℝ) := h96.weak (by norm_num) (by norm_num)
  have h98 : Bnd ((27 : ℝ) / 64) ((27 : ℝ) / 64) ((27 : ℝ) / 64) := Bnd.const _
  have h99 := Bnd.mul qcP_bnd qcdq_bnd (by norm_num) (by norm_num)
  have h100 : Bnd ((qcP * qcdq)) (3.9184077196454491953943681e-1 : ℝ) (3.9184077196454491953943685e-1 : ℝ) := h99.weak (by norm_num) (by norm_num)
  have h101 := Bnd.mul h100 qsB_bnd (by norm_num) (by norm_num)
  have h102 : Bnd (((qcP * qcdq) * qsB)) (2.5917830903843899830841334e-1 : ℝ) (2.5917830903843899830841338e-1 : ℝ) := h101.weak (by norm_num) (by norm_num)
  have h103 := Bnd.pow qc2_bnd (by norm_num) 3
  have h104 : Bnd ((qc2 ^ 3)) (3.5355339059327376220042211e-1 : ℝ) (3.5355339059327376220042221e-1 : ℝ) := h103.weak (by norm_num) (by norm_num)
  have h105 := Bnd.mul h102 h104 (by norm_num) (by norm_num)
  have h106 : Bnd ((((qcP * qcdq) * qsB) * (qc2 ^ 3))) (9.1633369928771438644122172e-2 : ℝ) (9.1633369928771438644122213e-2 : ℝ) := h105.weak (by norm_num) (by norm_num)
  have h107 := Bnd.pow qsP_bnd (by norm_num) 3
  have h108 : Bnd ((qsP ^ 3)) (9.3230847874547963333173184e-3 : ℝ) (9.3230847874547963333173198e-3 : ℝ) := h107.weak (by norm_num) (by norm_num)
  have h109 := Bnd.mul h106 h108 (by norm_num) (by norm_num)
  have h110 : Bnd (((((qcP * qcdq) * qsB) * (qc2 ^ 3)) * (qsP ^ 3))) (8.54305677206146793876234e-4 : ℝ) (8.5430567720614679387623452e-4 : ℝ) := h109.weak (by norm_num) (by norm_num)
  have h111 := Bnd.pow qsdq_bnd (by norm_num) 2
  have h112 : Bnd ((qsdq ^ 2)) (8.3934426229508196721311471e-1 : ℝ) (8.3934426229508196721311483e-1 : ℝ) := h111.weak (by norm_num) (by norm_num)
  have h113 := Bnd.mul h110 h112 (by norm_num) (by norm_num)
  have h114 : Bnd ((((((qcP * qcdq) * qsB) * (qc2 ^ 3)) * (qsP ^ 3)) * (qsdq ^ 2))) (7.1705656840909370240103571e-4 : ℝ) (7.1705656840909370240103626e-4 : ℝ) := h113.weak (by norm_num) (by norm_num)
  have h115 := Bnd.mul h98 h114 (by norm_num) (by norm_num)
  have h116 : Bnd ((((27 : ℝ) / 64) * (((((qcP * qcdq) * qsB) * (qc2 ^ 3)) * (qsP ^ 3)) * (qsdq ^ 2)))) (3.0250823979758640570043694e-4 : ℝ) (3.0250823979758640570043718e-4 : ℝ) := h115.weak (by norm_num) (by norm_num)
  have h117 := Bnd.add h97 h116
  have h118 : Bnd (((((((((3 : ℝ) / 4) * ((((qcP * (qc2 ^ 3)) * (qcdq ^ 3)) * (qsB ^ 3)) * (qsP ^ 3))) + (((3 : ℝ) / 4) * ((((qcdq * qsP) * (qc2 ^ 3)) * (qcP ^ 3)) * (qsB ^ 3)))) + (((27 : ℝ) / 64) * ((((qcP * qsB) * (qc2 ^ 3)) * (qcdq ^ 3)) * (qsP ^ 3)))) + (((27 : ℝ) / 64) * ((((qcdq * qsB) * qsP) * (qc2 ^ 3)) * (qcP ^ 3)))) + (((3 : ℝ) / 4) * (((((qcP * qcdq) * (qc2 ^ 3)) * (qsB ^ 3)) * (qsP ^ 3)) * (qsdq ^ 2)))) + (((27 : ℝ) / 64) * (((((qcP * qcdq) * qsB) * (qc2 ^ 3)) * (qsP ^ 3)) * (qsdq ^ 2))))) (1.4464434746347458943936234e-2 : ℝ) (1.4464434746347458943936249e-2 : ℝ) := h117.weak (by norm_num) (by norm_num)
  have h119 : Bnd ((27 : ℝ) / 64) ((27 : ℝ) / 64) ((27 : ℝ) / 64) := Bnd.const _
  have h120 := Bnd.mul qc2_bnd qcP_bnd (by norm_num) (by norm_num)
  have h121 : Bnd ((qc2 * qcP)) (6.9126808294611722222179942e-1 : ℝ) (6.912680829461172222217995e-1 : ℝ) := h120.weak (by norm_num) (by norm_num)
  have h122 := Bnd.mul h121 qsB_bnd (by norm_num) (by norm_num)
  have h123 : Bnd (((qc2 * qcP) * qsB)) (4.5723085918794894918135343e-1 : ℝ) (4.572308591879489491813535e-1 : ℝ) := h122.weak (by norm_num) (by norm_num)
  have h124 := Bnd.pow qcdq_bnd (by norm_num) 3
  have h125 : Bnd ((qcdq ^ 3)) (6.4393845465461245489794327e-2 : ℝ) (6.4393845465461245489794342e-2 : ℝ) := h124.weak (by norm_num) (by norm_num)
  have h126 := Bnd.mul h123 h125 (by norm_num) (by norm_num)
  have h127 : Bnd ((((qc2 * qcP) * qsB) * (qcdq ^ 3))) (2.9442853288588855695488437e-2 : ℝ) (2.9442853288588855695488449e-2 : ℝ) := h126.weak (by norm_num) (by norm_num)
  have h128 := Bnd.pow qsP_bnd (by norm_num) 3
  have h129 : Bnd ((qsP ^ 3)) (9.3230847874547963333173184e-3 : ℝ) (9.3230847874547963333173198e-3 : ℝ) := h128.weak (by norm_num) (by norm_num)
  have h130 := Bnd.mul h127 h129 (by norm_num) (by norm_num)
  have h131 : Bnd (((((qc2 * qcP) * qsB) * (qcdq ^ 3)) * (qsP ^ 3))) (2.7449821759410618295039651e-4 : ℝ) (2.7449821759410618295039667e-4 : ℝ) := h130.weak (by norm_num) (by norm_num)
  have h132 := Bnd.mul h119 h131 (by norm_num) (by norm_num)
  have h133 : Bnd ((((27 : ℝ) / 64) * ((((qc2 * qcP) * qsB) * (qcdq ^ 3)) * (qsP ^ 3)))) (1.1580393554751354593219852e-4 : ℝ) (1.158039355475135459321986e-4 : ℝ) := h132.weak (by norm_num) (by norm_num)
  have h134 : Bnd ((27 : ℝ) / 64) ((27 : ℝ) / 64) ((27 : ℝ) / 64) := Bnd.const _
  have h135 := Bnd.mul qc2_bnd qcdq_bnd (by norm_num) (by norm_num)
  have h136 : Bnd ((qc2 * qcdq)) (2.8342171556262060067786384e-1 : ℝ) (2.834217155626206006778639e-1 : ℝ) := h135.weak (by norm_num) (by norm_num)
  have h137 := Bnd.mul h136 qsB_bnd (by norm_num) (by norm_num)
  have h138 : Bnd (((qc2 * qcdq) * qsB)) (1.8746584388349473320205909e-1 : ℝ) (1.8746584388349473320205914e-1 : ℝ) := h137.weak (by norm_num) (by norm_num)
  have h139 := Bnd.mul h138 qsP_bnd (by norm_num) (by norm_num)
  have h140 : Bnd ((((qc2 * qcdq) * qsB) * qsP)) (3.9455603973814981890510137e-2 : ℝ) (3.945560397381498189051015e-2 : ℝ) := h139.weak (by norm_num) (by norm_num)
  have h141 := Bnd.pow qcP_bnd (by norm_num) 3
  have h142 : Bnd ((qcP ^ 3)) (9.3429604221271471891231158e-1 : ℝ) (9.3429604221271471891231164e-1 : ℝ) := h141.weak (by norm_num) (by norm_num)
  have h143 := Bnd.mul h140 h142 (by norm_num) (by norm_num)
  have h144 : Bnd (((((qc2 * qcdq) * qsB) * qsP) * (qcP ^ 3))) (3.6863214635847596929410836e-2 : ℝ) (3.6863214635847596929410851e-2 : ℝ) := h143.weak (by norm_num) (by norm_num)
  have h145 := Bnd.mul h134 h144 (by norm_num) (by norm_num)
  have h146 : Bnd ((((27 : ℝ) / 64) * ((((qc2 * qcdq) * qsB) * qsP) * (qcP ^ 3)))) (1.5551668674498204954595196e-2 : ℝ) (1.5551668674498204954595203e-2 : ℝ) := h145.weak (by norm_num) (by norm_num)
  have h147 := Bnd.add h133 h146
  have h148 : Bnd (((((27 : ℝ) / 64) * ((((qc2 * qcP) * qsB) * (qcdq ^ 3)) * (qsP ^ 3))) + (((27 : ℝ) / 64) * ((((qc2 * qcdq) * qsB) * qsP) * (qcP ^ 3))))) (1.5667472610045718500527394e-2 : ℝ) (1.5667472610045718500527402e-2 : ℝ) := h147.weak (by norm_num) (by norm_num)
  have h149 : Bnd ((3 : ℝ) / 4) ((3 : ℝ) / 4) ((3 : ℝ) / 4) := Bnd.const _
  have h150 := Bnd.mul qc2_bnd qcP_bnd (by norm_num) (by norm_num)
  have h151 : Bnd ((qc2 * qcP)) (6.9126808294611722222179942e-1 : ℝ) (6.912680829461172222217995e-1 : ℝ) := h150.weak (by norm_num) (by norm_num)
  have h152 := Bnd.pow qcdq_bnd (by norm_num) 3
  have h153 : Bnd ((qcdq ^ 3)) (6.4393845465461245489794327e-2 : ℝ) (6.4393845465461245489794342e-2 : ℝ) := h152.weak (by norm_num) (by norm_num)
  have h154 := Bnd.mul h151 h153 (by norm_num) (by norm_num)
  have h155 : Bnd (((qc2 * qcP) * (qcdq ^ 3))) (4.4513410108437918615023283e-2 : ℝ) (4.4513410108437918615023299e-2 : ℝ) := h154.weak (by norm_num) (by norm_num)
  have h156 := Bnd.pow qsB_bnd (by norm_num) 3
  have h157 : Bnd ((qsB ^ 3)) (2.8937904964768959583611421e-1 : ℝ) (2.8937904964768959583611423e-1 : ℝ) := h156.weak (by norm_num) (by norm_num)
  have h158 := Bnd.mul h155 h157 (by norm_num) (by norm_num)
  have h159 : Bnd ((((qc2 * qcP) * (qcdq ^ 3)) * (qsB ^ 3))) (1.2881248313757624366776191e-2 : ℝ) (1.2881248313757624366776197e-2 : ℝ) := h158.weak (by norm_num) (by norm_num)
  have h160 := Bnd.pow qsP_bnd (by norm_num) 3
  have h161 : Bnd ((qsP ^ 3)) (9.3230847874547963333173184e-3 : ℝ) (9.3230847874547963333173198e-3 : ℝ) := h160.weak (by norm_num) (by norm_num)
  have h162 := Bnd.mul h159 h161 (by norm_num) (by norm_num)
  have h163 : Bnd (((((qc2 * qcP) * (qcdq ^ 3)) * (qsB ^ 3)) * (qsP ^ 3))) (1.2009297019742145504079847e-4 : ℝ) (1.2009297019742145504079855e-4 : ℝ) := h162.weak (by norm_num) (by norm_num)
  have h164 := Bnd.mul h149 h163 (by norm_num) (by norm_num)
  have h165 : Bnd ((((3 : ℝ) / 4) * ((((qc2 * qcP) * (qcdq ^ 3)) * (qsB ^ 3)) * (qsP ^ 3)))) (9.0069727648066091280598852e-5 : ℝ) (9.0069727648066091280598913e-5 : ℝ) := h164.weak (by norm_num) (by norm_num)
  have h166 := Bnd.add h148 h165
  have h167 : Bnd ((((((27 : ℝ) / 64) * ((((qc2 * qcP) * qsB) * (qcdq ^ 3)) * (qsP ^ 3))) + (((27 : ℝ) / 64) * ((((qc2 * qcdq) * qsB) * qsP) * (qcP ^ 3)))) + (((3 : ℝ) / 4) * ((((qc2 * qcP) * (qcdq ^ 3)) * (qsB ^ 3)) * (qsP ^ 3))))) (1.5757542337693784591807992e-2 : ℝ) (1.5757542337693784591808001e-2 : ℝ) := h166.weak (by norm_num) (by norm_num)
  have h168 : Bnd ((3 : ℝ) / 4) ((3 : ℝ) / 4) ((3 : ℝ) / 4) := Bnd.const _
  have h169 := Bnd.mul qc2_bnd qcdq_bnd (by norm_num) (by norm_num)
  have h170 : Bnd ((qc2 * qcdq)) (2.8342171556262060067786384e-1 : ℝ) (2.834217155626206006778639e-1 : ℝ) := h169.weak (by norm_num) (by norm_num)
  have h171 := Bnd.mul h170 qsP_bnd (by norm_num) (by norm_num)
  have h172 : Bnd (((qc2 * qcdq) * qsP)) (5.9651266252895005010014323e-2 : ℝ) (5.9651266252895005010014339e-2 : ℝ) := h171.weak (by norm_num) (by norm_num)
  have h173 := Bnd.pow qcP_bnd (by norm_num) 3
  have h174 : Bnd ((qcP ^ 3)) (9.3429604221271471891231158e-1 : ℝ) (9.3429604221271471891231164e-1 : ℝ) := h173.weak (by norm_num) (by norm_num)
  have h175 := Bnd.mul h172 h174 (by norm_num) (by norm_num)
  have h176 : Bnd ((((qc2 * qcdq) * qsP) * (qcP ^ 3))) (5.573194197305667655617457e-2 : ℝ) (5.573194197305667655617459e-2 : ℝ) := h175.weak (by norm_num) (by norm_num)
  have h177 := Bnd.pow qsB_bnd (by norm_num) 3
  have h178 : Bnd ((qsB ^ 3)) (2.8937904964768959583611421e-1 : ℝ) (2.8937904964768959583611423e-1 : ℝ) := h177.weak (by norm_num) (by norm_num)
  have h179 := Bnd.mul h176 h178 (by norm_num) (by norm_num)
  have h180 : Bnd (((((qc2 * qcdq) * qsP) * (qcP ^ 3)) * (qsB ^ 3))) (1.612765640318332365661724e-2 : ℝ) (1.6127656403183323656617248e-2 : ℝ) := h179.weak (by norm_num) (by norm_num)
  have h181 := Bnd.mul h168 h180 (by norm_num) (by norm_num)
  have h182 : Bnd ((((3 : ℝ) / 4) * ((((qc2 * qcdq) * qsP) * (qcP ^ 3)) * (qsB ^ 3)))) (1.209574230238749274246293e-2 : ℝ) (1.2095742302387492742462936e-2 : ℝ) := h181.weak (by norm_num) (by norm_num)
  have h183 := Bnd.add h167 h182
  have h184 : Bnd (((((((27 : ℝ) / 64) * ((((qc2 * qcP) * qsB) * (qcdq ^ 3)) * (qsP ^ 3))) + (((27 : ℝ) / 64) * ((((qc2 * qcdq) * qsB) * qsP) * (qcP ^ 3)))) + (((3 : ℝ) / 4) * ((((qc2 * qcP) * (qcdq ^ 3)) * (qsB ^ 3)) * (qsP ^ 3)))) + (((3 : ℝ) / 4) * ((((qc2 * qcdq) * qsP) * (qcP ^ 3)) * (qsB ^ 3))))) (2.7853284640081277334270922e-2 : ℝ) (2.7853284640081277334270937e-2 : ℝ) := h183.weak (by norm_num) (by norm_num)
  have h185 : Bnd ((27 : ℝ) / 64) ((27 : ℝ) / 64) ((27 : ℝ) / 64) := Bnd.const _
  have h186 := Bnd.mul qc2_bnd qcP_bnd (by norm_num) (by norm_num)
  have h187 : Bnd ((qc2 * qcP)) (6.9126808294611722222179942e-1 : ℝ) (6.912680829461172222217995e-1 : ℝ) := h186.weak (by norm_num) (by norm_num)
  have h188 := Bnd.mul h187 qcdq_bnd (by norm_num) (by norm_num)
  have h189 : Bnd (((qc2 * qcP) * qcdq)) (2.7707326700150133015473678e-1 : ℝ) (2.7707326700150133015473684e-1 : ℝ) := h188.weak (by norm_num) (by norm_num)
  have h190 := Bnd.mul h189 qsB_bnd (by norm_num) (by norm_num)
  have h191 : Bnd ((((qc2 * qcP) * qcdq) * qsB)) (1.8326673985754287728824436e-1 : ℝ) (1.8326673985754287728824442e-1 : ℝ) := h190.weak (by norm_num) (by norm_num)
  have h192 := Bnd.pow qsP_bnd (by norm_num) 3
  have h193 : Bnd ((qsP ^ 3)) (9.3230847874547963333173184e-3 : ℝ) (9.3230847874547963333173198e-3 : ℝ) := h192.weak (by norm_num) (by norm_num)
  have h194 := Bnd.mul h191 h193 (by norm_num) (by norm_num)
  have h195 : Bnd (((((qc2 * qcP) * qcdq) * qsB) * (qsP ^ 3))) (1.7086113544122935877524681e-3 : ℝ) (1.708611354412293587752469e-3 : ℝ) := h194.weak (by norm_num) (by norm_num)
  have h196 := Bnd.pow qsdq_bnd (by norm_num) 2
  have h197 : Bnd ((qsdq ^ 2)) (8.3934426229508196721311471e-1 : ℝ) (8.3934426229508196721311483e-1 : ℝ) := h196.weak (by norm_num) (by norm_num)
  have h198 := Bnd.mul h195 h197 (by norm_num) (by norm_num)
  have h199 : Bnd ((((((qc2 * qcP) * qcdq) * qsB) * (qsP ^ 3)) * (qsdq ^ 2))) (1.4341131368181874048020715e-3 : ℝ) (1.4341131368181874048020725e-3 : ℝ) := h198.weak (by norm_num) (by norm_num)
  have h200 := Bnd.mul h185 h199 (by norm_num) (by norm_num)
  have h201 : Bnd ((((27 : ℝ) / 64) * (((((qc2 * qcP) * qcdq) * qsB) * (qsP ^ 3)) * (qsdq ^ 2)))) (6.0501647959517281140087391e-4 : ℝ) (6.0501647959517281140087434e-4 : ℝ) := h200.weak (by norm_num) (by norm_num)
  have h202 := Bnd.add h184 h201
  have h203 : Bnd ((((((((27 : ℝ) / 64) * ((((qc2 * qcP) * qsB) * (qcdq ^ 3)) * (qsP ^ 3))) + (((27 : ℝ) / 64) * ((((qc2 * qcdq) * qsB) * qsP) * (qcP ^ 3)))) + (((3 : ℝ) / 4) * ((((qc2 * qcP) * (qcdq ^ 3)) * (qsB ^ 3)) * (qsP ^ 3)))) + (((3 : ℝ) / 4) * ((((qc2 * qcdq) * qsP) * (qcP ^ 3)) * (qsB ^ 3)))) + (((27 : ℝ) / 64) * (((((qc2 * qcP) * qcdq) * qsB) * (qsP ^ 3)) * (qsdq ^ 2))))) (2.8458301119676450145671795e-2 : ℝ) (2.8458301119676450145671812e-2 : ℝ) := h202.weak (by norm_num) (by norm_num)
  have h204 : Bnd ((3 : ℝ) / 4) ((3 : ℝ) / 4) ((3 : ℝ) / 4) := Bnd.const _
  have h205 := Bnd.mul qc2_bnd qcP_bnd (by norm_num) (by norm_num)
  have h206 : Bnd ((qc2 * qcP)) (6.9126808294611722222179942e-1 : ℝ) (6.912680829461172222217995e-1 : ℝ) := h205.weak (by norm_num) (by norm_num)
  have h207 := Bnd.mul h206 qcdq_bnd (by norm_num) (by norm_num)
  have h208 : Bnd (((qc2 * qcP) * qcdq)) (2.7707326700150133015473678e-1 : ℝ) (2.7707326700150133015473684e-1 : ℝ) := h207.weak (by norm_num) (by norm_num)
  have h209 := Bnd.pow qsB_bnd (by norm_num) 3
  have h210 : Bnd ((qsB ^ 3)) (2.8937904964768959583611421e-1 : ℝ) (2.8937904964768959583611423e-1 : ℝ) := h209.weak (by norm_num) (by norm_num)
  have h211 := Bnd.mul h208 h210 (by norm_num) (by norm_num)
  have h212 : Bnd ((((qc2 * qcP) * qcdq) * (qsB ^ 3))) (8.0179198687675008813606908e-2 : ℝ) (8.0179198687675008813606932e-2 : ℝ) := h211.weak (by norm_num) (by norm_num)
  have h213 := Bnd.pow qsP_bnd (by norm_num) 3
  have h214 : Bnd ((qsP ^ 3)) (9.3230847874547963333173184e-3 : ℝ) (9.3230847874547963333173198e-3 : ℝ) := h213.weak (by norm_num) (by norm_num)
  have h215 := Bnd.mul h212 h214 (by norm_num) (by norm_num)
  have h216 : Bnd (((((qc2 * qcP) * qcdq) * (qsB ^ 3)) * (qsP ^ 3))) (7.4751746755537844464170482e-4 : ℝ) (7.4751746755537844464170516e-4 : ℝ) := h215.weak (by norm_num) (by norm_num)
  have h217 := Bnd.pow qsdq_bnd (by norm_num) 2
  have h218 : Bnd ((qsdq ^ 2)) (8.3934426229508196721311471e-1 : ℝ) (8.3934426229508196721311483e-1 : ℝ) := h217.weak (by norm_num) (by norm_num)
  have h219 := Bnd.mul h216 h218 (by norm_num) (by norm_num)
  have h220 : Bnd ((((((qc2 * qcP) * qcdq) * (qsB ^ 3)) * (qsP ^ 3)) * (qsdq ^ 2))) (6.274244973579569896009063e-4 : ℝ) (6.2742449735795698960090669e-4 : ℝ) := h219.weak (by norm_num) (by norm_num)
  have h221 := Bnd.mul h204 h220 (by norm_num) (by norm_num)
  have h222 : Bnd ((((3 : ℝ) / 4) * (((((qc2 * qcP) * qcdq) * (qsB ^ 3)) * (qsP ^ 3)) * (qsdq ^ 2)))) (4.7056837301846774220067972e-4 : ℝ) (4.7056837301846774220068002e-4 : ℝ) := h221.weak (by norm_num) (by norm_num)
  have h223 := Bnd.add h203 h222
  have h224 : Bnd (((((((((27 : ℝ) / 64) * ((((qc2 * qcP) * qsB) * (qcdq ^ 3)) * (qsP ^ 3))) + (((27 : ℝ) / 64) * ((((qc2 * qcdq) * qsB) * qsP) * (qcP ^ 3)))) + (((3 : ℝ) / 4) * ((((qc2 * qcP) * (qcdq ^ 3)) * (qsB ^ 3)) * (qsP ^ 3)))) + (((3 : ℝ) / 4) * ((((qc2 * qcdq) * qsP) * (qcP ^ 3)) * (qsB ^ 3)))) + (((27 : ℝ) / 64) * (((((qc2 * qcP) * qcdq) * qsB) * (qsP ^ 3)) * (qsdq ^ 2)))) + (((3 : ℝ) / 4) * (((((qc2 * qcP) * qcdq) * (qsB ^ 3)) * (qsP ^ 3)) * (qsdq ^ 2))))) (2.8928869492694917887872474e-2 : ℝ) (2.8928869492694917887872493e-2 : ℝ) := h223.weak (by norm_num) (by norm_num)
  have h225 := Bnd.sub h118 h224
  have h226 : Bnd ((((((((((3 : ℝ) / 4) * ((((qcP * (qc2 ^ 3)) * (qcdq ^ 3)) * (qsB ^ 3)) * (qsP ^ 3))) + (((3 : ℝ) / 4) * ((((qcdq * qsP) * (qc2 ^ 3)) * (qcP ^ 3)) * (qsB ^ 3)))) + (((27 : ℝ) / 64) * ((((qcP * qsB) * (qc2 ^ 3)) * (qcdq ^ 3)) * (qsP ^ 3)))) + (((27 : ℝ) / 64) * ((((qcdq * qsB) * qsP) * (qc2 ^ 3)) * (qcP ^ 3)))) + (((3 : ℝ) / 4) * (((((qcP * qcdq) * (qc2 ^ 3)) * (qsB ^ 3)) * (qsP ^ 3)) * (qsdq ^ 2)))) + (((27 : ℝ) / 64) * (((((qcP * qcdq) * qsB) * (qc2 ^ 3)) * (qsP ^ 3)) * (qsdq ^ 2)))) - ((((((((27 : ℝ) / 64) * ((((qc2 * qcP) * qsB) * (qcdq ^ 3)) * (qsP ^ 3))) + (((27 : ℝ) / 64) * ((((qc2 * qcdq) * qsB) * qsP) * (qcP ^ 3)))) + (((3 : ℝ) / 4) * ((((qc2 * qcP) * (qcdq ^ 3)) * (qsB ^ 3)) * (qsP ^ 3)))) + (((3 : ℝ) / 4) * ((((qc2 * qcdq) * qsP) * (qcP ^ 3)) * (qsB ^ 3)))) + (((27 : ℝ) / 64) * (((((qc2 * qcP) * qcdq) * qsB) * (qsP ^ 3)) * (qsdq ^ 2)))) + (((3 : ℝ) / 4) * (((((qc2 * qcP) * qcdq) * (qsB ^ 3)) * (qsP ^ 3)) * (qsdq ^ 2)))))) (-1.4464434746347458943936259e-2 : ℝ) (-1.4464434746347458943936225e-2 : ℝ) := h225.weak (by norm_num) (by norm_num)
  exact h226

/-- The closed form of row A003, pion current product, second construction `5m_p/36` [MeV]. -/
noncomputable def qRowA003 : ℝ :=
  ((((5 : ℝ) * qMp) / (36 : ℝ)) * qAbsVud)

theorem qRowA003_bnd : Bnd qRowA003 (1.2697322288643974750824968e2 : ℝ) (1.2697322288643974750824973e2 : ℝ) := by
  unfold qRowA003
  have h1 : Bnd (5 : ℝ) (5 : ℝ) (5 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qMp_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((5 : ℝ) * qMp)) (4.6913604471009836236027234e3 : ℝ) (4.6913604471009836236027243e3 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (36 : ℝ) (36 : ℝ) (36 : ℝ) := Bnd.const _
  have h5 := Bnd.div h3 h4 (by norm_num) (by norm_num)
  have h6 : Bnd ((((5 : ℝ) * qMp) / (36 : ℝ))) (1.3031556797502732287785342e2 : ℝ) (1.3031556797502732287785346e2 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.mul h6 qAbsVud_bnd (by norm_num) (by norm_num)
  have h8 : Bnd (((((5 : ℝ) * qMp) / (36 : ℝ)) * qAbsVud)) (1.2697322288643974750824968e2 : ℝ) (1.2697322288643974750824973e2 : ℝ) := h7.weak (by norm_num) (by norm_num)
  exact h8

/-- **The closed form of row A003 to its printed digits, `126.973222886`.** -/
theorem qRowA003_digits : (1.269732228855e2 : ℝ) < qRowA003 ∧ qRowA003 < (1.269732228865e2 : ℝ) :=
  qRowA003_bnd.strict (by norm_num) (by norm_num)

/-- The closed form of row G09, pion constant times `V_{ud}` [MeV]. -/
noncomputable def qRowG09 : ℝ :=
  (qFpi * qAbsVud)

theorem qRowG09_bnd : Bnd qRowG09 (1.2718137125267927763240764e2 : ℝ) (1.2718137125267927763281255e2 : ℝ) := by
  unfold qRowG09
  have h1 := Bnd.mul qFpi_bnd qAbsVud_bnd (by norm_num) (by norm_num)
  have h2 : Bnd ((qFpi * qAbsVud)) (1.2718137125267927763240764e2 : ℝ) (1.2718137125267927763281255e2 : ℝ) := h1.weak (by norm_num) (by norm_num)
  exact h2

/-- **The closed form of row G09 to its printed digits, `127.181371253`.** -/
theorem qRowG09_digits : (1.271813712525e2 : ℝ) < qRowG09 ∧ qRowG09 < (1.271813712535e2 : ℝ) :=
  qRowG09_bnd.strict (by norm_num) (by norm_num)

/-- The closed form of row S05, neutron lifetime [s]. -/
noncomputable def qRowS05 : ℝ :=
  (((509933 : ℝ) / 100) / ((((103983 : ℝ) / 100000) * (qAbsVud ^ 2)) * ((1 : ℝ) + ((3 : ℝ) * (qGA ^ 2)))))

theorem qRowS05_bnd : Bnd qRowS05 (8.7805141182657826832346114e2 : ℝ) (8.7805141182657826832346138e2 : ℝ) := by
  unfold qRowS05
  have h1 : Bnd ((509933 : ℝ) / 100) ((509933 : ℝ) / 100) ((509933 : ℝ) / 100) := Bnd.const _
  have h2 : Bnd ((103983 : ℝ) / 100000) ((103983 : ℝ) / 100000) ((103983 : ℝ) / 100000) := Bnd.const _
  have h3 := Bnd.pow qAbsVud_bnd (by norm_num) 2
  have h4 : Bnd ((qAbsVud ^ 2)) (9.4936164941406249999999996e-1 : ℝ) (9.4936164941406250000000003e-1 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 := Bnd.mul h2 h4 (by norm_num) (by norm_num)
  have h6 : Bnd ((((103983 : ℝ) / 100000) * (qAbsVud ^ 2))) (9.8717472391022460937499995e-1 : ℝ) (9.8717472391022460937500004e-1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h8 : Bnd (3 : ℝ) (3 : ℝ) (3 : ℝ) := Bnd.const _
  have h9 := Bnd.pow qGA_bnd (by norm_num) 2
  have h10 : Bnd ((qGA ^ 2)) (1.6276680081802833765186432 : ℝ) (1.6276680081802833765186435 : ℝ) := h9.weak (by norm_num) (by norm_num)
  have h11 := Bnd.mul h8 h10 (by norm_num) (by norm_num)
  have h12 : Bnd (((3 : ℝ) * (qGA ^ 2))) (4.8830040245408501295559296 : ℝ) (4.8830040245408501295559305 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 := Bnd.add h7 h12
  have h14 : Bnd (((1 : ℝ) + ((3 : ℝ) * (qGA ^ 2)))) (5.8830040245408501295559296 : ℝ) (5.8830040245408501295559305 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 := Bnd.mul h6 h14 (by norm_num) (by norm_num)
  have h16 : Bnd (((((103983 : ℝ) / 100000) * (qAbsVud ^ 2)) * ((1 : ℝ) + ((3 : ℝ) * (qGA ^ 2))))) (5.8075528736888539690181368 : ℝ) (5.8075528736888539690181383 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.div h1 h16 (by norm_num) (by norm_num)
  have h18 : Bnd ((((509933 : ℝ) / 100) / ((((103983 : ℝ) / 100000) * (qAbsVud ^ 2)) * ((1 : ℝ) + ((3 : ℝ) * (qGA ^ 2)))))) (8.7805141182657826832346114e2 : ℝ) (8.7805141182657826832346138e2 : ℝ) := h17.weak (by norm_num) (by norm_num)
  exact h18

/-- **The closed form of row S05 to its printed digits, `878.051411827`.** -/
theorem qRowS05_digits : (8.780514118265e2 : ℝ) < qRowS05 ∧ qRowS05 < (8.780514118275e2 : ℝ) :=
  qRowS05_bnd.strict (by norm_num) (by norm_num)

/-- The closed form of row K05, diagonal quark current. -/
noncomputable def qRowK05 : ℝ :=
  qDiagSum

theorem qRowK05_bnd : Bnd qRowK05 (2.8953108448757564997682079 : ℝ) (2.8953108448757564997682085 : ℝ) := by
  unfold qRowK05
  exact qDiagSum_bnd

/-- **The closed form of row K05 to its printed digits, `2.89531084488`.** -/
theorem qRowK05_digits : (2.895310844875 : ℝ) < qRowK05 ∧ qRowK05 < (2.895310844885 : ℝ) :=
  qRowK05_bnd.strict (by norm_num) (by norm_num)

/-- The closed form of row C05, quark quartet `J_q` [`10^{-5}`]. -/
noncomputable def qRowC05 : ℝ :=
  ((100000 : ℝ) * qJq)

theorem qRowC05_bnd : Bnd qRowC05 (3.1355091757898129278323674 : ℝ) (3.135509175789812927832368 : ℝ) := by
  unfold qRowC05
  have h1 : Bnd (100000 : ℝ) (100000 : ℝ) (100000 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qJq_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((100000 : ℝ) * qJq)) (3.1355091757898129278323674 : ℝ) (3.135509175789812927832368 : ℝ) := h2.weak (by norm_num) (by norm_num)
  exact h3

/-- **The closed form of row C05 to its printed digits, `3.13550917579`.** -/
theorem qRowC05_digits : (3.135509175785 : ℝ) < qRowC05 ∧ qRowC05 < (3.135509175795 : ℝ) :=
  qRowC05_bnd.strict (by norm_num) (by norm_num)

/-- The closed form of row C04, quark phase `delta_q` [rad]. -/
noncomputable def qRowC04 : ℝ :=
  ((π / (2 : ℝ)) - (Real.arctan ((7 : ℝ) / 16)))

theorem qRowC04_bnd : Bnd qRowC04 (1.1583858851975093123302086 : ℝ) (1.1583858851975093123352088 : ℝ) := by
  unfold qRowC04
  have h1 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h2 := Bnd.div bnd_pi h1 (by norm_num) (by norm_num)
  have h3 : Bnd ((π / (2 : ℝ))) (1.57079632679489661923 : ℝ) (1.570796326794896619235 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd ((7 : ℝ) / 16) ((7 : ℝ) / 16) ((7 : ℝ) / 16) := Bnd.const _
  have h5 : Bnd ((Real.arctan ((7 : ℝ) / 16))) (4.1241044159738730689979122e-1 : ℝ) (4.1241044159738730689979131e-1 : ℝ) := Bnd.arctan h4 (atan_ge ((7 : ℝ) / 16) (4.1241044159738730689979122e-1 : ℝ) (by norm_num) (by norm_num) 16 (by norm_num [atanPoly, Finset.sum_range_succ])) (atan_le ((7 : ℝ) / 16) (4.1241044159738730689979131e-1 : ℝ) (by norm_num) (by norm_num) 16 (by norm_num [atanPoly, Finset.sum_range_succ]))
  have h6 := Bnd.sub h3 h5
  have h7 : Bnd (((π / (2 : ℝ)) - (Real.arctan ((7 : ℝ) / 16)))) (1.1583858851975093123302086 : ℝ) (1.1583858851975093123352088 : ℝ) := h6.weak (by norm_num) (by norm_num)
  exact h7

/-- **The closed form of row C04 to its printed digits, `1.1583858852`.** -/
theorem qRowC04_digits : (1.15838588515 : ℝ) < qRowC04 ∧ qRowC04 < (1.15838588525 : ℝ) :=
  qRowC04_bnd.strict (by norm_num) (by norm_num)

/-- The closed form of row C06, triangle angle `alpha` [deg]. -/
noncomputable def qRowC06 : ℝ :=
  ((90 : ℝ) + (((180 : ℝ) * (Real.arctan ((-qReAlpha) / qImAlpha))) / π))

theorem qRowC06_bnd : Bnd qRowC06 (9.0713773064337999148282423e1 : ℝ) (9.0713773064337999148284712e1 : ℝ) := by
  unfold qRowC06
  have h1 : Bnd (90 : ℝ) (90 : ℝ) (90 : ℝ) := Bnd.const _
  have h2 : Bnd (180 : ℝ) (180 : ℝ) (180 : ℝ) := Bnd.const _
  have h3 := Bnd.neg qReAlpha_bnd
  have h4 : Bnd ((-qReAlpha)) (3.90632223839075663270511e-7 : ℝ) (3.90632223839075663270519e-7 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 := Bnd.div h4 qImAlpha_bnd (by norm_num) (by norm_num)
  have h6 : Bnd (((-qReAlpha) / qImAlpha)) (1.2458334577849804128927263e-2 : ℝ) (1.2458334577849804128927522e-2 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 : Bnd ((Real.arctan ((-qReAlpha) / qImAlpha))) (1.2457690084747405333960469e-2 : ℝ) (1.2457690084747405333960742e-2 : ℝ) := Bnd.arctan h6 (atan_ge (1.2458334577849804128927263e-2 : ℝ) (1.2457690084747405333960469e-2 : ℝ) (by norm_num) (by norm_num) 3 (by norm_num [atanPoly, Finset.sum_range_succ])) (atan_le (1.2458334577849804128927522e-2 : ℝ) (1.2457690084747405333960742e-2 : ℝ) (by norm_num) (by norm_num) 3 (by norm_num [atanPoly, Finset.sum_range_succ]))
  have h8 := Bnd.mul h2 h7 (by norm_num) (by norm_num)
  have h9 : Bnd (((180 : ℝ) * (Real.arctan ((-qReAlpha) / qImAlpha)))) (2.2423842152545329601128844 : ℝ) (2.2423842152545329601129336 : ℝ) := h8.weak (by norm_num) (by norm_num)
  have h10 := Bnd.div h9 bnd_pi (by norm_num) (by norm_num)
  have h11 : Bnd ((((180 : ℝ) * (Real.arctan ((-qReAlpha) / qImAlpha))) / π)) (7.1377306433799914828242381e-1 : ℝ) (7.1377306433799914828471149e-1 : ℝ) := h10.weak (by norm_num) (by norm_num)
  have h12 := Bnd.add h1 h11
  have h13 : Bnd (((90 : ℝ) + (((180 : ℝ) * (Real.arctan ((-qReAlpha) / qImAlpha))) / π))) (9.0713773064337999148282423e1 : ℝ) (9.0713773064337999148284712e1 : ℝ) := h12.weak (by norm_num) (by norm_num)
  exact h13

/-- **The closed form of row C06 to its printed digits, `90.7137730643`.** -/
theorem qRowC06_digits : (9.071377306425e1 : ℝ) < qRowC06 ∧ qRowC06 < (9.071377306435e1 : ℝ) :=
  qRowC06_bnd.strict (by norm_num) (by norm_num)

/-- The closed form of row C07, triangle angle `beta` [deg]. -/
noncomputable def qRowC07 : ℝ :=
  (((180 : ℝ) * (Real.arctan (qImBeta / qReBeta))) / π)

theorem qRowC07_bnd : Bnd qRowC07 (2.2951143935388809481950208e1 : ℝ) (2.2951143935388809482023292e1 : ℝ) := by
  unfold qRowC07
  have h1 : Bnd (180 : ℝ) (180 : ℝ) (180 : ℝ) := Bnd.const _
  have h2 := Bnd.div qImBeta_bnd qReBeta_bnd (by norm_num) (by norm_num)
  have h3 : Bnd ((qImBeta / qReBeta)) (4.2346884251463977684578999e-1 : ℝ) (4.2346884251463977684579021e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd ((Real.arctan (qImBeta / qReBeta))) (4.0057302877166344486197543e-1 : ℝ) (4.0057302877166344486197591e-1 : ℝ) := Bnd.arctan h3 (atan_ge (4.2346884251463977684578999e-1 : ℝ) (4.0057302877166344486197543e-1 : ℝ) (by norm_num) (by norm_num) 15 (by norm_num [atanPoly, Finset.sum_range_succ])) (atan_le (4.2346884251463977684579021e-1 : ℝ) (4.0057302877166344486197591e-1 : ℝ) (by norm_num) (by norm_num) 15 (by norm_num [atanPoly, Finset.sum_range_succ]))
  have h5 := Bnd.mul h1 h4 (by norm_num) (by norm_num)
  have h6 : Bnd (((180 : ℝ) * (Real.arctan (qImBeta / qReBeta)))) (7.2103145178899420075155577e1 : ℝ) (7.2103145178899420075155664e1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.div h6 bnd_pi (by norm_num) (by norm_num)
  have h8 : Bnd ((((180 : ℝ) * (Real.arctan (qImBeta / qReBeta))) / π)) (2.2951143935388809481950208e1 : ℝ) (2.2951143935388809482023292e1 : ℝ) := h7.weak (by norm_num) (by norm_num)
  exact h8

/-- **The closed form of row C07 to its printed digits, `22.9511439354`.** -/
theorem qRowC07_digits : (2.295114393535e1 : ℝ) < qRowC07 ∧ qRowC07 < (2.295114393545e1 : ℝ) :=
  qRowC07_bnd.strict (by norm_num) (by norm_num)

/-- The closed form of row C08, triangle angle `gamma` [deg]. -/
noncomputable def qRowC08 : ℝ :=
  ((90 : ℝ) - (((180 : ℝ) * (Real.arctan (qReGamma / qImGamma))) / π))

theorem qRowC08_bnd : Bnd qRowC08 (6.6335083000273191369692006e1 : ℝ) (6.6335083000273191369767351e1 : ℝ) := by
  unfold qRowC08
  have h1 : Bnd (90 : ℝ) (90 : ℝ) (90 : ℝ) := Bnd.const _
  have h2 : Bnd (180 : ℝ) (180 : ℝ) (180 : ℝ) := Bnd.const _
  have h3 := Bnd.div qReGamma_bnd qImGamma_bnd (by norm_num) (by norm_num)
  have h4 : Bnd ((qReGamma / qImGamma)) (4.3823920289638634816673219e-1 : ℝ) (4.3823920289638634816673241e-1 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 : Bnd ((Real.arctan (qReGamma / qImGamma))) (4.1303071885641085019593621e-1 : ℝ) (4.1303071885641085019593648e-1 : ℝ) := Bnd.arctan h4 (atan_ge (4.3823920289638634816673219e-1 : ℝ) (4.1303071885641085019593621e-1 : ℝ) (by norm_num) (by norm_num) 16 (by norm_num [atanPoly, Finset.sum_range_succ])) (atan_le (4.3823920289638634816673241e-1 : ℝ) (4.1303071885641085019593648e-1 : ℝ) (by norm_num) (by norm_num) 16 (by norm_num [atanPoly, Finset.sum_range_succ]))
  have h6 := Bnd.mul h2 h5 (by norm_num) (by norm_num)
  have h7 : Bnd (((180 : ℝ) * (Real.arctan (qReGamma / qImGamma)))) (7.4345529394153953035268517e1 : ℝ) (7.4345529394153953035268567e1 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 := Bnd.div h7 bnd_pi (by norm_num) (by norm_num)
  have h9 : Bnd ((((180 : ℝ) * (Real.arctan (qReGamma / qImGamma))) / π)) (2.3664916999726808630232649e1 : ℝ) (2.3664916999726808630307994e1 : ℝ) := h8.weak (by norm_num) (by norm_num)
  have h10 := Bnd.sub h1 h9
  have h11 : Bnd (((90 : ℝ) - (((180 : ℝ) * (Real.arctan (qReGamma / qImGamma))) / π))) (6.6335083000273191369692006e1 : ℝ) (6.6335083000273191369767351e1 : ℝ) := h10.weak (by norm_num) (by norm_num)
  exact h11

/-- **The closed form of row C08 to its printed digits, `66.3350830003`.** -/
theorem qRowC08_digits : (6.633508300025e1 : ℝ) < qRowC08 ∧ qRowC08 < (6.633508300035e1 : ℝ) :=
  qRowC08_bnd.strict (by norm_num) (by norm_num)

/-- The closed form of row C10, solar lepton angle `s^2_{12}`. -/
noncomputable def qRowC10 : ℝ :=
  (qU01sq / ((1 : ℝ) - qU02sq))

theorem qRowC10_bnd : Bnd qRowC10 (3.0508961092263539708302096e-1 : ℝ) (3.0508961092263539708302111e-1 : ℝ) := by
  unfold qRowC10
  have h1 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h2 := Bnd.sub h1 qU02sq_bnd
  have h3 : Bnd (((1 : ℝ) - qU02sq)) (9.7785156249999999999999999e-1 : ℝ) (9.7785156250000000000000001e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.div qU01sq_bnd h3 (by norm_num) (by norm_num)
  have h5 : Bnd ((qU01sq / ((1 : ℝ) - qU02sq))) (3.0508961092263539708302096e-1 : ℝ) (3.0508961092263539708302111e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- **The closed form of row C10 to its printed digits, `0.305089610923`.** -/
theorem qRowC10_digits : (3.050896109225e-1 : ℝ) < qRowC10 ∧ qRowC10 < (3.050896109235e-1 : ℝ) :=
  qRowC10_bnd.strict (by norm_num) (by norm_num)

/-- The closed form of row C11, reactor angle `s^2_{13}`. -/
noncomputable def qRowC11 : ℝ :=
  qU02sq

theorem qRowC11_bnd : Bnd qRowC11 (2.2148437499999999999999993e-2 : ℝ) (2.2148437500000000000000006e-2 : ℝ) := by
  unfold qRowC11
  exact qU02sq_bnd

/-- **The closed form of row C11 to its printed digits, `0.0221484375`.** -/
theorem qRowC11_digits : (2.214843745e-2 : ℝ) < qRowC11 ∧ qRowC11 < (2.214843755e-2 : ℝ) :=
  qRowC11_bnd.strict (by norm_num) (by norm_num)

/-- The closed form of row C12, reactor angle `sin^22theta_{13}`. -/
noncomputable def qRowC12 : ℝ :=
  (((4 : ℝ) * qU02sq) * ((1 : ℝ) - qU02sq))

theorem qRowC12_bnd : Bnd qRowC12 (8.6631536865234374999999971e-2 : ℝ) (8.6631536865234375000000025e-2 : ℝ) := by
  unfold qRowC12
  have h1 : Bnd (4 : ℝ) (4 : ℝ) (4 : ℝ) := Bnd.const _
  have h2 := Bnd.mul h1 qU02sq_bnd (by norm_num) (by norm_num)
  have h3 : Bnd (((4 : ℝ) * qU02sq)) (8.8593749999999999999999972e-2 : ℝ) (8.8593750000000000000000024e-2 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h5 := Bnd.sub h4 qU02sq_bnd
  have h6 : Bnd (((1 : ℝ) - qU02sq)) (9.7785156249999999999999999e-1 : ℝ) (9.7785156250000000000000001e-1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.mul h3 h6 (by norm_num) (by norm_num)
  have h8 : Bnd ((((4 : ℝ) * qU02sq) * ((1 : ℝ) - qU02sq))) (8.6631536865234374999999971e-2 : ℝ) (8.6631536865234375000000025e-2 : ℝ) := h7.weak (by norm_num) (by norm_num)
  exact h8

/-- **The closed form of row C12 to its printed digits, `0.0866315368652`.** -/
theorem qRowC12_digits : (8.663153686515e-2 : ℝ) < qRowC12 ∧ qRowC12 < (8.663153686525e-2 : ℝ) :=
  qRowC12_bnd.strict (by norm_num) (by norm_num)

/-- The closed form of row C13, atmospheric angle `s^2_{23}`. -/
noncomputable def qRowC13 : ℝ :=
  (qU12sq / ((1 : ℝ) - qU02sq))

theorem qRowC13_bnd : Bnd qRowC13 (4.8867494906723125474373817e-1 : ℝ) (4.8867494906723125474373832e-1 : ℝ) := by
  unfold qRowC13
  have h1 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h2 := Bnd.sub h1 qU02sq_bnd
  have h3 : Bnd (((1 : ℝ) - qU02sq)) (9.7785156249999999999999999e-1 : ℝ) (9.7785156250000000000000001e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.div qU12sq_bnd h3 (by norm_num) (by norm_num)
  have h5 : Bnd ((qU12sq / ((1 : ℝ) - qU02sq))) (4.8867494906723125474373817e-1 : ℝ) (4.8867494906723125474373832e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- **The closed form of row C13 to its printed digits, `0.488674949067`.** -/
theorem qRowC13_digits : (4.886749490665e-1 : ℝ) < qRowC13 ∧ qRowC13 < (4.886749490675e-1 : ℝ) :=
  qRowC13_bnd.strict (by norm_num) (by norm_num)

/-- The closed form of row T06, lepton quartet `J_l`. -/
noncomputable def qRowT06 : ℝ :=
  qJl

theorem qRowT06_bnd : Bnd qRowT06 (-1.4464434746347458943936259e-2 : ℝ) (-1.4464434746347458943936225e-2 : ℝ) := by
  unfold qRowT06
  exact qJl_bnd

/-- **The closed form of row T06 to its printed digits, `-0.0144644347463`.** -/
theorem qRowT06_digits : (-1.446443474635e-2 : ℝ) < qRowT06 ∧ qRowT06 < (-1.446443474625e-2 : ℝ) :=
  qRowT06_bnd.strict (by norm_num) (by norm_num)

/-- `s₁₂² = |U_e2|²/(1 − |U_e3|²)`. -/
noncomputable def qS12 : ℝ :=
  (qU01sq / ((1 : ℝ) - qU02sq))

theorem qS12_bnd : Bnd qS12 (3.0508961092263539708302096e-1 : ℝ) (3.0508961092263539708302111e-1 : ℝ) := by
  unfold qS12
  have h1 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h2 := Bnd.sub h1 qU02sq_bnd
  have h3 : Bnd (((1 : ℝ) - qU02sq)) (9.7785156249999999999999999e-1 : ℝ) (9.7785156250000000000000001e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.div qU01sq_bnd h3 (by norm_num) (by norm_num)
  have h5 : Bnd ((qU01sq / ((1 : ℝ) - qU02sq))) (3.0508961092263539708302096e-1 : ℝ) (3.0508961092263539708302111e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- `s₂₃² = |U_μ3|²/(1 − |U_e3|²)`. -/
noncomputable def qS23 : ℝ :=
  (qU12sq / ((1 : ℝ) - qU02sq))

theorem qS23_bnd : Bnd qS23 (4.8867494906723125474373817e-1 : ℝ) (4.8867494906723125474373832e-1 : ℝ) := by
  unfold qS23
  have h1 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h2 := Bnd.sub h1 qU02sq_bnd
  have h3 : Bnd (((1 : ℝ) - qU02sq)) (9.7785156249999999999999999e-1 : ℝ) (9.7785156250000000000000001e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.div qU12sq_bnd h3 (by norm_num) (by norm_num)
  have h5 : Bnd ((qU12sq / ((1 : ℝ) - qU02sq))) (4.8867494906723125474373817e-1 : ℝ) (4.8867494906723125474373832e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  exact h5

/-- `(s₁₂²c₁₂²s₂₃²c₂₃²s₁₃²)^{1/2}`. -/
noncomputable def qScale : ℝ :=
  (√((((qS12 * ((1 : ℝ) - qS12)) * qS23) * ((1 : ℝ) - qS23)) * qU02sq))

theorem qScale_bnd : Bnd qScale (3.4253758534006208393659025e-2 : ℝ) (3.4253758534006208393659063e-2 : ℝ) := by
  unfold qScale
  have h1 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h2 := Bnd.sub h1 qS12_bnd
  have h3 : Bnd (((1 : ℝ) - qS12)) (6.9491038907736460291697889e-1 : ℝ) (6.9491038907736460291697904e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.mul qS12_bnd h3 (by norm_num) (by norm_num)
  have h5 : Bnd ((qS12 * ((1 : ℝ) - qS12))) (2.1200994022971034929525683e-1 : ℝ) (2.1200994022971034929525699e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.mul h5 qS23_bnd (by norm_num) (by norm_num)
  have h7 : Bnd (((qS12 * ((1 : ℝ) - qS12)) * qS23)) (1.0360394674350044752642017e-1 : ℝ) (1.0360394674350044752642029e-1 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h9 := Bnd.sub h8 qS23_bnd
  have h10 : Bnd (((1 : ℝ) - qS23)) (5.1132505093276874525626168e-1 : ℝ) (5.1132505093276874525626183e-1 : ℝ) := h9.weak (by norm_num) (by norm_num)
  have h11 := Bnd.mul h7 h10 (by norm_num) (by norm_num)
  have h12 : Bnd ((((qS12 * ((1 : ℝ) - qS12)) * qS23) * ((1 : ℝ) - qS23))) (5.297529334545622691400064e-2 : ℝ) (5.2975293345456226914000718e-2 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 := Bnd.mul h12 qU02sq_bnd (by norm_num) (by norm_num)
  have h14 : Bnd (((((qS12 * ((1 : ℝ) - qS12)) * qS23) * ((1 : ℝ) - qS23)) * qU02sq)) (1.1733199737060031507905606e-3 : ℝ) (1.1733199737060031507905631e-3 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 : Bnd ((√((((qS12 * ((1 : ℝ) - qS12)) * qS23) * ((1 : ℝ) - qS23)) * qU02sq))) (3.4253758534006208393659025e-2 : ℝ) (3.4253758534006208393659063e-2 : ℝ) := Bnd.sqrt h14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h15

/-- `J_l/(scale (1 − s₁₃²))`, the sine side. -/
noncomputable def qYL : ℝ :=
  (-((-qJl) / (qScale * ((1 : ℝ) - qU02sq))))

theorem qYL_bnd : Bnd qYL (-4.3183744791376673529721041e-1 : ℝ) (-4.3183744791376673529720889e-1 : ℝ) := by
  unfold qYL
  have h1 := Bnd.neg qJl_bnd
  have h2 : Bnd ((-qJl)) (1.4464434746347458943936225e-2 : ℝ) (1.4464434746347458943936259e-2 : ℝ) := h1.weak (by norm_num) (by norm_num)
  have h3 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h4 := Bnd.sub h3 qU02sq_bnd
  have h5 : Bnd (((1 : ℝ) - qU02sq)) (9.7785156249999999999999999e-1 : ℝ) (9.7785156250000000000000001e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 := Bnd.mul qScale_bnd h5 (by norm_num) (by norm_num)
  have h7 : Bnd ((qScale * ((1 : ℝ) - qU02sq))) (3.3495091303975680262440092e-2 : ℝ) (3.3495091303975680262440131e-2 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 := Bnd.div h2 h7 (by norm_num) (by norm_num)
  have h9 : Bnd (((-qJl) / (qScale * ((1 : ℝ) - qU02sq)))) (4.3183744791376673529720889e-1 : ℝ) (4.3183744791376673529721041e-1 : ℝ) := h8.weak (by norm_num) (by norm_num)
  have h10 := Bnd.neg h9
  have h11 : Bnd ((-((-qJl) / (qScale * ((1 : ℝ) - qU02sq))))) (-4.3183744791376673529721041e-1 : ℝ) (-4.3183744791376673529720889e-1 : ℝ) := h10.weak (by norm_num) (by norm_num)
  exact h11

/-- `(|U_μ1|² − s₁₂²c₂₃² − c₁₂²s₂₃²s₁₃²)/(2 scale)`, the cosine side. -/
noncomputable def qXL : ℝ :=
  (-((((qS12 * ((1 : ℝ) - qS23)) + ((((1 : ℝ) - qS12) * qS23) * qU02sq)) - qU10sq) / ((2 : ℝ) * qScale)))

theorem qXL_bnd : Bnd qXL (-9.0195145023406043743358218e-1 : ℝ) (-9.0195145023406043743357679e-1 : ℝ) := by
  unfold qXL
  have h1 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h2 := Bnd.sub h1 qS23_bnd
  have h3 : Bnd (((1 : ℝ) - qS23)) (5.1132505093276874525626168e-1 : ℝ) (5.1132505093276874525626183e-1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 := Bnd.mul qS12_bnd h3 (by norm_num) (by norm_num)
  have h5 : Bnd ((qS12 * ((1 : ℝ) - qS23))) (1.5599996084407514411627323e-1 : ℝ) (1.5599996084407514411627336e-1 : ℝ) := h4.weak (by norm_num) (by norm_num)
  have h6 : Bnd (1 : ℝ) (1 : ℝ) (1 : ℝ) := Bnd.const _
  have h7 := Bnd.sub h6 qS12_bnd
  have h8 : Bnd (((1 : ℝ) - qS12)) (6.9491038907736460291697889e-1 : ℝ) (6.9491038907736460291697904e-1 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 := Bnd.mul h8 qS23_bnd (by norm_num) (by norm_num)
  have h10 : Bnd ((((1 : ℝ) - qS12) * qS23)) (3.3958529898867100177699041e-1 : ℝ) (3.395852989886710017769906e-1 : ℝ) := h9.weak (by norm_num) (by norm_num)
  have h11 := Bnd.mul h10 qU02sq_bnd (by norm_num) (by norm_num)
  have h12 : Bnd (((((1 : ℝ) - qS12) * qS23) * qU02sq)) (7.5212837705693928909200586e-3 : ℝ) (7.5212837705693928909200673e-3 : ℝ) := h11.weak (by norm_num) (by norm_num)
  have h13 := Bnd.add h5 h12
  have h14 : Bnd (((qS12 * ((1 : ℝ) - qS23)) + ((((1 : ℝ) - qS12) * qS23) * qU02sq))) (1.6352124461464453700719328e-1 : ℝ) (1.6352124461464453700719343e-1 : ℝ) := h13.weak (by norm_num) (by norm_num)
  have h15 := Bnd.sub h14 qU10sq_bnd
  have h16 : Bnd ((((qS12 * ((1 : ℝ) - qS23)) + ((((1 : ℝ) - qS12) * qS23) * qU02sq)) - qU10sq)) (6.179045437142844735175314e-2 : ℝ) (6.179045437142844735175344e-2 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h18 := Bnd.mul h17 qScale_bnd (by norm_num) (by norm_num)
  have h19 : Bnd (((2 : ℝ) * qScale)) (6.850751706801241678731805e-2 : ℝ) (6.8507517068012416787318126e-2 : ℝ) := h18.weak (by norm_num) (by norm_num)
  have h20 := Bnd.div h16 h19 (by norm_num) (by norm_num)
  have h21 : Bnd (((((qS12 * ((1 : ℝ) - qS23)) + ((((1 : ℝ) - qS12) * qS23) * qU02sq)) - qU10sq) / ((2 : ℝ) * qScale))) (9.0195145023406043743357679e-1 : ℝ) (9.0195145023406043743358218e-1 : ℝ) := h20.weak (by norm_num) (by norm_num)
  have h22 := Bnd.neg h21
  have h23 : Bnd ((-((((qS12 * ((1 : ℝ) - qS23)) + ((((1 : ℝ) - qS12) * qS23) * qU02sq)) - qU10sq) / ((2 : ℝ) * qScale)))) (-9.0195145023406043743358218e-1 : ℝ) (-9.0195145023406043743357679e-1 : ℝ) := h22.weak (by norm_num) (by norm_num)
  exact h23

/-- The closed form of row C14, lepton phase `delta_l` [deg]. -/
noncomputable def qRowC14 : ℝ :=
  ((180 : ℝ) + (((180 : ℝ) * (Real.arctan ((-qYL) / (-qXL)))) / π))

theorem qRowC14_bnd : Bnd qRowC14 (2.0558422583520145415686116e2 : ℝ) (2.0558422583520145415694283e2 : ℝ) := by
  unfold qRowC14
  have h1 : Bnd (180 : ℝ) (180 : ℝ) (180 : ℝ) := Bnd.const _
  have h2 : Bnd (180 : ℝ) (180 : ℝ) (180 : ℝ) := Bnd.const _
  have h3 := Bnd.neg qYL_bnd
  have h4 : Bnd ((-qYL)) (4.3183744791376673529720889e-1 : ℝ) (4.3183744791376673529721041e-1 : ℝ) := h3.weak (by norm_num) (by norm_num)
  have h5 := Bnd.neg qXL_bnd
  have h6 : Bnd ((-qXL)) (9.0195145023406043743357679e-1 : ℝ) (9.0195145023406043743358218e-1 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.div h4 h6 (by norm_num) (by norm_num)
  have h8 : Bnd (((-qYL) / (-qXL))) (4.7878125568920919762986447e-1 : ℝ) (4.7878125568920919762986903e-1 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 : Bnd ((Real.arctan ((-qYL) / (-qXL)))) (4.4652897739806155868445925e-1 : ℝ) (4.4652897739806155868446303e-1 : ℝ) := Bnd.arctan h8 (atan_ge (4.7878125568920919762986447e-1 : ℝ) (4.4652897739806155868445925e-1 : ℝ) (by norm_num) (by norm_num) 18 (by norm_num [atanPoly, Finset.sum_range_succ])) (atan_le (4.7878125568920919762986903e-1 : ℝ) (4.4652897739806155868446303e-1 : ℝ) (by norm_num) (by norm_num) 18 (by norm_num [atanPoly, Finset.sum_range_succ]))
  have h10 := Bnd.mul h2 h9 (by norm_num) (by norm_num)
  have h11 : Bnd (((180 : ℝ) * (Real.arctan ((-qYL) / (-qXL))))) (8.0375215931651080563202665e1 : ℝ) (8.0375215931651080563203346e1 : ℝ) := h10.weak (by norm_num) (by norm_num)
  have h12 := Bnd.div h11 bnd_pi (by norm_num) (by norm_num)
  have h13 : Bnd ((((180 : ℝ) * (Real.arctan ((-qYL) / (-qXL)))) / π)) (2.5584225835201454156861169e1 : ℝ) (2.5584225835201454156942824e1 : ℝ) := h12.weak (by norm_num) (by norm_num)
  have h14 := Bnd.add h1 h13
  have h15 : Bnd (((180 : ℝ) + (((180 : ℝ) * (Real.arctan ((-qYL) / (-qXL)))) / π))) (2.0558422583520145415686116e2 : ℝ) (2.0558422583520145415694283e2 : ℝ) := h14.weak (by norm_num) (by norm_num)
  exact h15

/-- **The closed form of row C14 to its printed digits, `205.584225835`.** -/
theorem qRowC14_digits : (2.055842258345e2 : ℝ) < qRowC14 ∧ qRowC14 < (2.055842258355e2 : ℝ) :=
  qRowC14_bnd.strict (by norm_num) (by norm_num)

end Comparison.Article
