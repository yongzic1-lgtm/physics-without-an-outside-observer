import Comparison.Formulas.Clocks
import Comparison.Formulas.Kernel
import Comparison.Formulas.OwnChart
import Comparison.Formulas.Sweep
import Comparison.Formulas.Nucleon
import Comparison.Formulas.Lapse
import Comparison.Formulas.MainLine
import Comparison.Formulas.SuThree
import Comparison.Formulas.Rules

/-!
# The main line in formulas

The finite formulas for clocks, the determinant, the chart of the law, the
crossing moment, the nucleon projector and the common lapse.

* `Clocks` (Prop. S41a; formulas (4), (5)): `H_k(iγ_h)H_k† = γ_hγ_k`, the quaternion triple
  `iγ_h, γ_hγ_k, iγ_k`, the square-root step on the six, and a central kept rotation exactly at type `2¦4`.
* `Kernel` (Prop. S54a; formulas (10) to (13), (17)): `T = HWᵀ` unitary with `T†(6I − L)T = 5I − A`,
  `det(I − uB) = (1 − u²)²⁴u¹⁶det[(6I − L) + χ(u)I]`, `k_N = u(2N + χ)`, the gap at the four points `u = i^d/4`,
  `κ = 2/[(χ + 5)² − 5]²` and the law's own transformation as a shift of the gap.
* `OwnChart` (Prop. S59a; formula (16)): the Bass identity on the law's own chart, the hop sum
  `25 − |F|² = Σ_{s≠t}(1 − cos k·(v_s − v_t))`, the projection along `v_h` with Gram `δ − 1/4` and cell
  `V₃ = 1/2`, the two-sheet Schur symbol and the continuation along the last-step direction.
* `Sweep` (Prop. S64a; formula (27)): `Cov(N, H_DH_E) = (C_W/72)(|D||E| − 5 tr P_DP_E)` for all
  coordinate divided sets and two positive nonsinglet grade weights; `1/72`, `1/18 = −Φ(1)/(1 + Φ(1))`,
  `1/12 = −Φ(i)/(1 + Φ(i))`.
* `Nucleon` (Prop. S120a; formula (54)): `P_N = P_sym(15/4 − S²)/3` a projector of rank 4 in the
  symmetric twenty, `S²P_N = I²P_N = (3/4)P_N`, `P_{p↑}` of rank one with unit charge and
  `⟨p↑|Σ_r σ_zτ_z|p↑⟩ = 5/3`.
* `Lapse` (Prop. S166a; formula (20)): `K(E, N) = K(E/N, 1)` gives `N∂_N K = −E∂_E K`,
  `E_X(N) = NE_X(1)` and the displacement `E` at a simple zero.
* `MainLine` (formulas (3), (14), (29)): `L(Ω) = 6`, `χ(1/4 − δ) = 12δ + 16δ²/(1/4 − δ)`, and the
  one-arc identity with the law written out.
* `SuThree` (formula (59)): the traceless rotations of three lines have real dimension eight.
* `Rules` (formulas (67) to (73), section 15): `Ψ_S = −Φ(4w_S)/(16w_S²)` at every divided set, `√3 = e@{t}^{−1/2}`,
  the clock's spread `61/16` as the excursion's, `−log h(ν)/ν² → (3/2)Var D`, `det F₀ = t@{}`, and `W` as the
  minor on `C`.

`Audit.lean` (not imported here) prints the axioms of every declaration of these files.
-/
