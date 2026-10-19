import Comparison.Article.QCosmos

/-!
# Numbers of single propositions

Proposition 187: the neutrino masses in meV, their sum, the least sum the measured splittings allow and its
width, and the distance of the newest bound below it. Proposition 50: `arg(7 + 16i)` to five decimals.
-/

namespace Comparison.Article

open Real

/-- `m₂` in meV. -/
noncomputable def qM2meV : ℝ :=
  (qM2 * (1000 : ℝ))

theorem qM2meV_bnd : Bnd qM2meV (8.6126719736524727057604685 : ℝ) (8.6126719736524727057606099 : ℝ) := by
  unfold qM2meV
  have h1 : Bnd (1000 : ℝ) (1000 : ℝ) (1000 : ℝ) := Bnd.const _
  have h2 := Bnd.mul qM2_bnd h1 (by norm_num) (by norm_num)
  have h3 : Bnd ((qM2 * (1000 : ℝ))) (8.6126719736524727057604685 : ℝ) (8.6126719736524727057606099 : ℝ) := h2.weak (by norm_num) (by norm_num)
  exact h3

/-- **`qM2meV` to its stated digits `8.6126720`.** -/
theorem qM2meV_digits : (8.61267195 : ℝ) < qM2meV ∧ qM2meV < (8.61267205 : ℝ) :=
  qM2meV_bnd.strict (by norm_num) (by norm_num)

/-- `m₃` in meV. -/
noncomputable def qM3meV : ℝ :=
  (qM3 * (1000 : ℝ))

theorem qM3meV_bnd : Bnd qM3meV (5.0198330947777375808569645e1 : ℝ) (5.0198330947777375808570397e1 : ℝ) := by
  unfold qM3meV
  have h1 : Bnd (1000 : ℝ) (1000 : ℝ) (1000 : ℝ) := Bnd.const _
  have h2 := Bnd.mul qM3_bnd h1 (by norm_num) (by norm_num)
  have h3 : Bnd ((qM3 * (1000 : ℝ))) (5.0198330947777375808569645e1 : ℝ) (5.0198330947777375808570397e1 : ℝ) := h2.weak (by norm_num) (by norm_num)
  exact h3

/-- **`qM3meV` to its stated digits `50.198331`.** -/
theorem qM3meV_digits : (5.01983305e1 : ℝ) < qM3meV ∧ qM3meV < (5.01983315e1 : ℝ) :=
  qM3meV_bnd.strict (by norm_num) (by norm_num)

/-- `Σ m_ν = m₁ + m₂ + m₃` with `m₁ = 0`, in eV. -/
noncomputable def qSumNu : ℝ :=
  (qM2 + qM3)

theorem qSumNu_bnd : Bnd qSumNu (5.8811002921429848514330113e-2 : ℝ) (5.8811002921429848514331007e-2 : ℝ) := by
  unfold qSumNu
  have h1 := Bnd.add qM2_bnd qM3_bnd
  have h2 : Bnd ((qM2 + qM3)) (5.8811002921429848514330113e-2 : ℝ) (5.8811002921429848514331007e-2 : ℝ) := h1.weak (by norm_num) (by norm_num)
  exact h2

/-- **`qSumNu` to its stated digits `0.0588110`.** -/
theorem qSumNu_digits : (5.881095e-2 : ℝ) < qSumNu ∧ qSumNu < (5.881105e-2 : ℝ) :=
  qSumNu_bnd.strict (by norm_num) (by norm_num)

/-- **The least sum the measured splittings allow**, `(Δm²₂₁)^{1/2} + (Δm²₃₁)^{1/2}` with JUNO 2026's `7.388·10⁻⁵` and `2.509·10⁻³` eV², `m₁ = 0`. -/
noncomputable def qLeastSum : ℝ :=
  ((√((1847 : ℝ) / 25000000)) + (√((2509 : ℝ) / 1000000)))

theorem qLeastSum_bnd : Bnd qLeastSum (5.8685266724250493673693611e-2 : ℝ) (5.8685266724250493673693613e-2 : ℝ) := by
  unfold qLeastSum
  have h1 : Bnd ((1847 : ℝ) / 25000000) ((1847 : ℝ) / 25000000) ((1847 : ℝ) / 25000000) := Bnd.const _
  have h2 : Bnd ((√((1847 : ℝ) / 25000000))) (8.5953475787777192134507043e-3 : ℝ) (8.5953475787777192134507044e-3 : ℝ) := Bnd.sqrt h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 : Bnd ((2509 : ℝ) / 1000000) ((2509 : ℝ) / 1000000) ((2509 : ℝ) / 1000000) := Bnd.const _
  have h4 : Bnd ((√((2509 : ℝ) / 1000000))) (5.0089919145472774460242907e-2 : ℝ) (5.0089919145472774460242908e-2 : ℝ) := Bnd.sqrt h3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h5 := Bnd.add h2 h4
  have h6 : Bnd (((√((1847 : ℝ) / 25000000)) + (√((2509 : ℝ) / 1000000)))) (5.8685266724250493673693611e-2 : ℝ) (5.8685266724250493673693613e-2 : ℝ) := h5.weak (by norm_num) (by norm_num)
  exact h6

/-- **`qLeastSum` to its stated digits `0.05869`.** -/
theorem qLeastSum_digits : (5.8685e-2 : ℝ) < qLeastSum ∧ qLeastSum < (5.8695e-2 : ℝ) :=
  qLeastSum_bnd.strict (by norm_num) (by norm_num)

/-- The least sum's width, the two standard deviations `0.078·10⁻⁵` and `0.026·10⁻³` eV² (the mean of `+0.027` and `−0.025`) carried at first order and combined in quadrature. -/
noncomputable def qLeastWidth : ℝ :=
  (√(((((39 : ℝ) / 50000000) / ((2 : ℝ) * (√((1847 : ℝ) / 25000000)))) ^ 2) + ((((13 : ℝ) / 500000) / ((2 : ℝ) * (√((2509 : ℝ) / 1000000)))) ^ 2)))

theorem qLeastWidth_bnd : Bnd qLeastWidth (2.6346965074256572687221478e-4 : ℝ) (2.6346965074256572687221483e-4 : ℝ) := by
  unfold qLeastWidth
  have h1 : Bnd ((39 : ℝ) / 50000000) ((39 : ℝ) / 50000000) ((39 : ℝ) / 50000000) := Bnd.const _
  have h2 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h3 : Bnd ((1847 : ℝ) / 25000000) ((1847 : ℝ) / 25000000) ((1847 : ℝ) / 25000000) := Bnd.const _
  have h4 : Bnd ((√((1847 : ℝ) / 25000000))) (8.5953475787777192134507043e-3 : ℝ) (8.5953475787777192134507044e-3 : ℝ) := Bnd.sqrt h3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h5 := Bnd.mul h2 h4 (by norm_num) (by norm_num)
  have h6 : Bnd (((2 : ℝ) * (√((1847 : ℝ) / 25000000)))) (1.7190695157555438426901408e-2 : ℝ) (1.7190695157555438426901409e-2 : ℝ) := h5.weak (by norm_num) (by norm_num)
  have h7 := Bnd.div h1 h6 (by norm_num) (by norm_num)
  have h8 : Bnd ((((39 : ℝ) / 50000000) / ((2 : ℝ) * (√((1847 : ℝ) / 25000000))))) (4.537338326642271918307762e-5 : ℝ) (4.5373383266422719183077624e-5 : ℝ) := h7.weak (by norm_num) (by norm_num)
  have h9 := Bnd.pow h8 (by norm_num) 2
  have h10 : Bnd (((((39 : ℝ) / 50000000) / ((2 : ℝ) * (√((1847 : ℝ) / 25000000)))) ^ 2)) (2.0587439090416892257715212e-9 : ℝ) (2.0587439090416892257715217e-9 : ℝ) := h9.weak (by norm_num) (by norm_num)
  have h11 : Bnd ((13 : ℝ) / 500000) ((13 : ℝ) / 500000) ((13 : ℝ) / 500000) := Bnd.const _
  have h12 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h13 : Bnd ((2509 : ℝ) / 1000000) ((2509 : ℝ) / 1000000) ((2509 : ℝ) / 1000000) := Bnd.const _
  have h14 : Bnd ((√((2509 : ℝ) / 1000000))) (5.0089919145472774460242907e-2 : ℝ) (5.0089919145472774460242908e-2 : ℝ) := Bnd.sqrt h13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h15 := Bnd.mul h12 h14 (by norm_num) (by norm_num)
  have h16 : Bnd (((2 : ℝ) * (√((2509 : ℝ) / 1000000)))) (1.0017983829094554892048581e-1 : ℝ) (1.0017983829094554892048582e-1 : ℝ) := h15.weak (by norm_num) (by norm_num)
  have h17 := Bnd.div h11 h16 (by norm_num) (by norm_num)
  have h18 : Bnd ((((13 : ℝ) / 500000) / ((2 : ℝ) * (√((2509 : ℝ) / 1000000))))) (2.5953325982110245834322748e-4 : ℝ) (2.5953325982110245834322752e-4 : ℝ) := h17.weak (by norm_num) (by norm_num)
  have h19 := Bnd.pow h18 (by norm_num) 2
  have h20 : Bnd (((((13 : ℝ) / 500000) / ((2 : ℝ) * (√((2509 : ℝ) / 1000000)))) ^ 2)) (6.7357512953367875647668384e-8 : ℝ) (6.7357512953367875647668405e-8 : ℝ) := h19.weak (by norm_num) (by norm_num)
  have h21 := Bnd.add h10 h20
  have h22 : Bnd ((((((39 : ℝ) / 50000000) / ((2 : ℝ) * (√((1847 : ℝ) / 25000000)))) ^ 2) + ((((13 : ℝ) / 500000) / ((2 : ℝ) * (√((2509 : ℝ) / 1000000)))) ^ 2))) (6.9416256862409564873439905e-8 : ℝ) (6.9416256862409564873439927e-8 : ℝ) := h21.weak (by norm_num) (by norm_num)
  have h23 : Bnd ((√(((((39 : ℝ) / 50000000) / ((2 : ℝ) * (√((1847 : ℝ) / 25000000)))) ^ 2) + ((((13 : ℝ) / 500000) / ((2 : ℝ) * (√((2509 : ℝ) / 1000000)))) ^ 2)))) (2.6346965074256572687221478e-4 : ℝ) (2.6346965074256572687221483e-4 : ℝ) := Bnd.sqrt h22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h23

/-- **`qLeastWidth` to its stated digits `0.00026`.** -/
theorem qLeastWidth_digits : (2.55e-4 : ℝ) < qLeastWidth ∧ qLeastWidth < (2.65e-4 : ℝ) :=
  qLeastWidth_bnd.strict (by norm_num) (by norm_num)

/-- How far the bound `0.055` eV lies below the least sum. -/
noncomputable def qBelowLeast : ℝ :=
  (qLeastSum - ((11 : ℝ) / 200))

theorem qBelowLeast_bnd : Bnd qBelowLeast (3.685266724250493673693611e-3 : ℝ) (3.685266724250493673693613e-3 : ℝ) := by
  unfold qBelowLeast
  have h1 : Bnd ((11 : ℝ) / 200) ((11 : ℝ) / 200) ((11 : ℝ) / 200) := Bnd.const _
  have h2 := Bnd.sub qLeastSum_bnd h1
  have h3 : Bnd ((qLeastSum - ((11 : ℝ) / 200))) (3.685266724250493673693611e-3 : ℝ) (3.685266724250493673693613e-3 : ℝ) := h2.weak (by norm_num) (by norm_num)
  exact h3

/-- **`qBelowLeast` to its stated digits `0.0037`.** -/
theorem qBelowLeast_digits : (3.65e-3 : ℝ) < qBelowLeast ∧ qBelowLeast < (3.75e-3 : ℝ) :=
  qBelowLeast_bnd.strict (by norm_num) (by norm_num)

/-- `arg(7 + 16i) = π/2 − arctan(7/16)`. -/
noncomputable def qDeltaQ5 : ℝ :=
  ((π / (2 : ℝ)) - (Real.arctan ((7 : ℝ) / 16)))

theorem qDeltaQ5_bnd : Bnd qDeltaQ5 (1.1583858851975093123301993 : ℝ) (1.1583858851975093123352596 : ℝ) := by
  unfold qDeltaQ5
  have h1 : Bnd (2 : ℝ) (2 : ℝ) (2 : ℝ) := Bnd.const _
  have h2 := Bnd.div bnd_pi h1 (by norm_num) (by norm_num)
  have h3 : Bnd ((π / (2 : ℝ))) (1.57079632679489661923 : ℝ) (1.570796326794896619235 : ℝ) := h2.weak (by norm_num) (by norm_num)
  have h4 : Bnd ((7 : ℝ) / 16) ((7 : ℝ) / 16) ((7 : ℝ) / 16) := Bnd.const _
  have h5 : Bnd ((Real.arctan ((7 : ℝ) / 16))) (4.1241044159738730689974045e-1 : ℝ) (4.1241044159738730689980069e-1 : ℝ) := Bnd.arctan h4 (atan_ge ((7 : ℝ) / 16) (4.1241044159738730689974045e-1 : ℝ) (by norm_num) (by norm_num) 14 (by norm_num [atanPoly, Finset.sum_range_succ])) (atan_le ((7 : ℝ) / 16) (4.1241044159738730689980069e-1 : ℝ) (by norm_num) (by norm_num) 14 (by norm_num [atanPoly, Finset.sum_range_succ]))
  have h6 := Bnd.sub h3 h5
  have h7 : Bnd (((π / (2 : ℝ)) - (Real.arctan ((7 : ℝ) / 16)))) (1.1583858851975093123301993 : ℝ) (1.1583858851975093123352596 : ℝ) := h6.weak (by norm_num) (by norm_num)
  exact h7

/-- **`qDeltaQ5` to its stated digits `1.15839`.** -/
theorem qDeltaQ5_digits : (1.158385 : ℝ) < qDeltaQ5 ∧ qDeltaQ5 < (1.158395 : ℝ) :=
  qDeltaQ5_bnd.strict (by norm_num) (by norm_num)

end Comparison.Article
