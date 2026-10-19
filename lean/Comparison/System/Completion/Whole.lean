import Comparison.System.Completion.Bass
import Comparison.System.Completion.Kaon
import Comparison.System.Completion.Clock
import Comparison.System.Completion.Remainders
import Comparison.System.Completion.Constants
import Comparison.System.Completion.DividedSet

set_option linter.style.longLine false

/-!
# The proof system, the completions, part 13: the numbered statements whose clauses come from two files

Each `prop_N` here is the whole SI Proposition N: the conjunction of the clauses
proved in the proposition's home file and those proved in a later file (the Higgs quartic for Prop. 68, the product
walk for Prop. 167, the light levels' digits for Prop. 197, the refits at every coupling for Prop. 198, the fourth order
for Prop. 206). Each conjunct is written with the namespaces of the file that proves it.
-/

namespace Comparison.System

/-- **Proposition 68 (the weak, the Higgs and the top).** `G_Fm_p² = (1 − 1/N₂)W_W/M²` with
`W_W = F(h)h⁻⁴(1 − 2b + 2bh)` and `2b = Var P/(Var P + Var Q) = 7/8`; `ŝ² = 3N_h`, `N_h = Σ_k hᵏp_k`,
`p₁ = −Φ(i) = 1/13`, `3p₁ = w_h`; `m_H² = 2παv²/χ_h`, `χ_h = w_h(1 − w_h) = 30/169`; `y_t² = η/σ = C_j/C_h = 59/60`,
`M_t = v(η/2σ)^{1/2}`; the values `G_F = 1.16637886·10⁻⁵ GeV⁻²`, `ŝ² = 0.231258`, `m_H = 125.135 GeV`,
`M_t = 172.647 GeV`; and the Higgs quartic `λ_H = πα/χ_h = 0.129145909`, `χ_h = (4χ_A − 1)/(4χ_A)²`.

Recognition: `G_F` Fermi's constant, `ŝ²` the weak angle, `m_H` the Higgs mass, `y_t` the top's Yukawa coupling,
`λ_H` the Higgs self-coupling. The weak contact, the retained excursion `W_W` and the quartic `πα/χ_h` are the theory's
compositions. -/
theorem prop_68 :
    (open Real Complex Matrix Comparison Comparison.Law Comparison.System.Completion in
      Num.GFmp2 = (1 - 1 / (Num.N2 : ℝ)) * Num.WW / (Num.M : ℝ) ^ 2 ∧
      Num.WW = Num.Fr Num.h / Num.h ^ 4 * (1 - 2 * Num.b + 2 * Num.b * Num.h) ∧
      2 * Num.b = Num.VarP / (Num.VarP + Num.VarQ) ∧ 2 * Num.b = 7 / 8 ∧
      Num.sw2 = 3 * Num.Nh ∧ Num.Nh = ∑' k : ℕ, Num.h ^ (k + 1) * repR (k + 1) ∧
      repR 1 = 1 / 13 ∧ -(Num.Phi I) = 1 / 13 ∧ 3 * repR 1 = Num.wh ∧
      Num.chih = Num.wh * (1 - Num.wh) ∧ Num.chih = 30 / 169 ∧
      Table.Row.D16 ^ 2 = 2 * π * Num.alpha * Num.v ^ 2 / Num.chih ∧
      Num.eta / Num.sigma = (Num.Cj : ℝ) / Num.Ch ∧ Num.eta / Num.sigma = 59 / 60 ∧
      Table.Row.D17 = Num.v * √(Num.eta / (2 * Num.sigma)) ∧
      ((1.166378858705 : ℝ) < Table.Row.D03 ∧ Table.Row.D03 < 1.166378858715) ∧
      ((0.2312575216885 : ℝ) < Num.sw2 ∧ Num.sw2 < 0.2312575216895) ∧
      ((125.1347715925 : ℝ) < Table.Row.D16 ∧ Table.Row.D16 < 125.1347715935) ∧
      ((172.6466136135 : ℝ) < Table.Row.D17 ∧ Table.Row.D17 < 172.6466136145)) ∧
    (open Real Comparison Comparison.Law Comparison.System.Completion in
      Num.chih = 30 / 169 ∧ (30 / 169 : ℝ) = (4 * (13 / 12) - 1) / (4 * (13 / 12)) ^ 2 ∧
      ((0.1291459085 : ℝ) < π * Num.alpha / Num.chih ∧ π * Num.alpha / Num.chih < 0.1291459095)) :=
  ⟨Completion.Comp.weak_higgs_top, Completion.Comp.higgs_quartic⟩

/-- **Proposition 167 (a bound state of several world lines on the line side: their zero shifts add).** On the line side
(`G = I`) the law on the direct sum factors over the lines, `det(I − D ⊗ M) = det(I − S₁M)det(I − S₂M)` for every
square `M`; a level `e^{−S}` on the steps along `h` has `δ(S) = −log((3 + (9 + 16e^{−S})^{1/2})/8) =
S/5 − (6/125)S² + O(S³)`; the product walk of any number of levels has the Perron root `ρ = Π_iρ(w_i)`, so the shifts
add, `δ = Σ_iδ(S_i)`; and the same level on the eighty states has the Perron root `λ(S)/4`. -/
theorem prop_167 :
    (open Real Complex Matrix Kronecker Comparison Comparison.Law Comparison.System.Completion Comparison.Article Filter Topology Asymptotics in
      (∀ {n : Type} [Fintype n] [DecidableEq n] (S₁ S₂ : ℝ) (M : Matrix n n ℝ),
        (1 - levelOp S₁ S₂ 0 ⊗ₖ M).det = (1 - S₁ • M).det * (1 - S₂ • M).det) ∧
      (∀ S : ℝ, deltaLevel S = -Real.log ((3 + Real.sqrt (9 + 16 * Real.exp (-S))) / 8)) ∧
      (fun S : ℝ => deltaLevel S - (S / 5 - 6 / 125 * S ^ 2)) =O[𝓝 0] (fun S : ℝ => S ^ 3)) ∧
    (open Real Comparison Comparison.Law Comparison.System.Completion.Comp in
      ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (h : Fin 5) (lam : κ → ℝ),
        IsPerron (kronPi fun j => lastDirectionWalk h (-lam j)) (∏ j, lamLevel (lam j) / 4) ∧
          -Real.log (∏ j, lamLevel (lam j) / 4) = ∑ j, deltaLevel (lam j)) ∧
    (open Real Comparison Comparison.Law in
      ∀ (h : Fin 5) (S : ℝ), IsPerron (lastDirectionWalk h (-S)) (lamLevel S / 4)) :=
  ⟨Completion.Comp.line_side_level, fun h lam => Completion.Comp.composite_walk h lam,
    fun h S => Comparison.Law.level_perron h S⟩

/-- **Proposition 197 (the light level, from the charged pion through the composition).**
`6m_p²Tr δ₁(R(R_udS_d, S_d; 8/15)) = m_π⁰²` has exactly one nonnegative root `S_d`, in `[sdLo, sdHi]` (relative width
`2·10⁻¹⁷`): `S_d = 0.011855816`, `S_u = R_udS_d = 0.005447267` (`R_ud = 17/37`), `S_s = pS_d = 0.236661685`. -/
theorem prop_197 :
    (open Real Matrix Kronecker Filter Topology Asymptotics Comparison Comparison.Law Comparison.System.Completion in
      (∃ S ∈ Set.Icc Article.sdLo Article.sdHi, light_level_equation S Num.mp (Table.Row.G06 ^ 2)) ∧
      (∀ S T : ℝ, 0 ≤ S → 0 ≤ T → light_level_equation S Num.mp (Table.Row.G06 ^ 2) →
        light_level_equation T Num.mp (Table.Row.G06 ^ 2) → S = T) ∧
      (∀ S : ℝ, 0 ≤ S → light_level_equation S Num.mp (Table.Row.G06 ^ 2) → Article.Bnd S Article.sdLo Article.sdHi) ∧
      ((0.0118558155 : ℝ) < Article.sdLo ∧ Article.sdHi < 0.0118558165)) ∧
    (open Real Comparison Comparison.Law Comparison.System.Completion in
      ((0.0118558155 : ℝ) < Table.Row.Sd ∧ Table.Row.Sd < 0.0118558165) ∧
      ((0.0054472665 : ℝ) < Num.Rud * Table.Row.Sd ∧ Num.Rud * Table.Row.Sd < 0.0054472675) ∧
      ((0.2366616845 : ℝ) < massOp .symmetric sPlaneSinglet * Table.Row.Sd ∧
        massOp .symmetric sPlaneSinglet * Table.Row.Sd < 0.2366616855)) :=
  ⟨Completion.Comp.light_level, Completion.Comp.light_level_digits⟩

/-- **Proposition 198 (`K⁰`).** `K⁰ = d s̄` at the singlet: `m² = 6m_p²Tr δ₁(R(S_d, S_s; 8/15))` with the light level
`S_d` (Prop. 197) and `S_s = pS_d`, `p = m_s/m_d` the plane-and-singlet mass operator; the law on the direct sum factors
over the two modes; at `c = 0` the composition is the line side and at `c = 1` the meeting side; `m = 497.6135845 MeV`,
against `497.611(13)` (PDG, outside input), `+0.20` standard deviations. With the light level refitted at each coupling `c`
(`6m_p²Tr δ₁(R(R_udS, S; c)) = m_π⁰²`, a nonnegative root in a stated interval of relative width `2·10⁻¹⁷`): the line
side alone `498.1434 MeV` (`+40.95` standard deviations), the meeting side alone `497.1479 MeV` (`−35.62`); the measured `K⁰` asks
`c = 0.5359` between `0.5229` (`+1.00`) and `0.5490` (`−1.00`); at `c = 8/15` it asks `p = 19.961420` between
`19.960252` and `19.962588`, `0.1709` standard deviations per `10⁻⁵` of `p`; the shift is
`Tr δ₁(R) = δ₁(S_s) + S_d[(1 − c)/5 + cδ₁′(S_s)] − (6/125)S_d² + 6.6·10⁻⁸`, `δ₁′(S_s) = 0.177461`. All in the law's
`m_p`, the row `m_π⁰` (G06), `p` (B04) and `R_ud`. -/
theorem prop_198 :
    (open Real Matrix Kronecker Filter Topology Asymptotics Comparison Comparison.Law Comparison.System.Completion in
      Table.Row.J08 = Article.rowJ08Of Table.Row.Sd ∧ light_level_equation Table.Row.Sd Num.mp (Table.Row.G06 ^ 2) ∧
      Article.rowJ08Of Table.Row.Sd =
        Num.mp * √(6 * (deltaLevel (Table.Row.Sd * Article.qNuP) + deltaLevel (Table.Row.Sd * Article.qNuM))) ∧
      (6 * Num.mp ^ 2 * compositeDelta Table.Row.Sd (massOp .symmetric sPlaneSinglet * Table.Row.Sd) 0 =
          6 * Num.mp ^ 2 * (deltaLevel Table.Row.Sd + deltaLevel (massOp .symmetric sPlaneSinglet * Table.Row.Sd)) ∧
        6 * Num.mp ^ 2 * compositeDelta Table.Row.Sd (massOp .symmetric sPlaneSinglet * Table.Row.Sd) 1 =
          6 * Num.mp ^ 2 * deltaLevel (Table.Row.Sd + massOp .symmetric sPlaneSinglet * Table.Row.Sd) ∧
        eigenPlus Table.Row.Sd (massOp .symmetric sPlaneSinglet * Table.Row.Sd) (8 / 15) +
            eigenMinus Table.Row.Sd (massOp .symmetric sPlaneSinglet * Table.Row.Sd) (8 / 15) =
          Table.Row.Sd + massOp .symmetric sPlaneSinglet * Table.Row.Sd ∧
        massOp .symmetric sPlaneSinglet =
          3 ^ (5 : ℝ) * Real.exp (-(5 / 2)) * clockMQ sLastDirectionSinglet (-(9 / 4000)) ^ (1 / 6 : ℝ)) ∧
      (∀ {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ), 0 < Table.Row.Sd →
        (1 - levelOp Table.Row.Sd (massOp .symmetric sPlaneSinglet * Table.Row.Sd) (Real.sqrt (8 / 15)) ⊗ₖ M).det =
          (1 - eigenPlus Table.Row.Sd (massOp .symmetric sPlaneSinglet * Table.Row.Sd) (8 / 15) • M).det *
            (1 - eigenMinus Table.Row.Sd (massOp .symmetric sPlaneSinglet * Table.Row.Sd) (8 / 15) • M).det) ∧
      ((497.6135844505 : ℝ) < Table.Row.J08 ∧ Table.Row.J08 < 497.6135844515) ∧
      ((0.195 : ℝ) < (Table.Row.J08 - 497.611) / 0.013 ∧ (Table.Row.J08 - 497.611) / 0.013 < 0.205)) ∧
    (open Real Comparison Comparison.Law Comparison.Article Comparison.System.Completion in
      ((∃ S ∈ Set.Icc QK.sdLo_0 QK.sdHi_0, 6 * Num.mp ^ 2 * compositeDelta (Num.Rud * S) S 0 = Table.Row.G06 ^ 2) ∧
        ∀ S, 0 ≤ S → 6 * Num.mp ^ 2 * compositeDelta (Num.Rud * S) S 0 = Table.Row.G06 ^ 2 →
          ((498.14335 : ℝ) < Num.mp * √(6 * compositeDelta S (Table.Row.B04 * S) 0) ∧ Num.mp * √(6 * compositeDelta S (Table.Row.B04 * S) 0) < 498.14345) ∧
          ((40.945 : ℝ) < (Num.mp * √(6 * compositeDelta S (Table.Row.B04 * S) 0) - 497.611) / 0.013 ∧
            (Num.mp * √(6 * compositeDelta S (Table.Row.B04 * S) 0) - 497.611) / 0.013 < 40.955)) ∧
      ((∃ S ∈ Set.Icc QK.sdLo_1 QK.sdHi_1, 6 * Num.mp ^ 2 * compositeDelta (Num.Rud * S) S 1 = Table.Row.G06 ^ 2) ∧
        ∀ S, 0 ≤ S → 6 * Num.mp ^ 2 * compositeDelta (Num.Rud * S) S 1 = Table.Row.G06 ^ 2 →
          ((497.14785 : ℝ) < Num.mp * √(6 * compositeDelta S (Table.Row.B04 * S) 1) ∧ Num.mp * √(6 * compositeDelta S (Table.Row.B04 * S) 1) < 497.14795) ∧
          ((-35.625 : ℝ) < (Num.mp * √(6 * compositeDelta S (Table.Row.B04 * S) 1) - 497.611) / 0.013 ∧
            (Num.mp * √(6 * compositeDelta S (Table.Row.B04 * S) 1) - 497.611) / 0.013 < -35.615)) ∧
      ((∃ S ∈ Set.Icc QK.sdLo_b QK.sdHi_b, 6 * Num.mp ^ 2 * compositeDelta (Num.Rud * S) S (5359 / 10000) = Table.Row.G06 ^ 2) ∧
        ∀ S, 0 ≤ S → 6 * Num.mp ^ 2 * compositeDelta (Num.Rud * S) S (5359 / 10000) = Table.Row.G06 ^ 2 →
          (-0.005 : ℝ) < (Num.mp * √(6 * compositeDelta S (Table.Row.B04 * S) (5359 / 10000)) - 497.611) / 0.013 ∧
            (Num.mp * √(6 * compositeDelta S (Table.Row.B04 * S) (5359 / 10000)) - 497.611) / 0.013 < 0.005) ∧
      ((∃ S ∈ Set.Icc QK.sdLo_a QK.sdHi_a, 6 * Num.mp ^ 2 * compositeDelta (Num.Rud * S) S (5229 / 10000) = Table.Row.G06 ^ 2) ∧
        ∀ S, 0 ≤ S → 6 * Num.mp ^ 2 * compositeDelta (Num.Rud * S) S (5229 / 10000) = Table.Row.G06 ^ 2 →
          (0.995 : ℝ) < (Num.mp * √(6 * compositeDelta S (Table.Row.B04 * S) (5229 / 10000)) - 497.611) / 0.013 ∧
            (Num.mp * √(6 * compositeDelta S (Table.Row.B04 * S) (5229 / 10000)) - 497.611) / 0.013 < 1.005) ∧
      ((∃ S ∈ Set.Icc QK.sdLo_d QK.sdHi_d, 6 * Num.mp ^ 2 * compositeDelta (Num.Rud * S) S (549 / 1000) = Table.Row.G06 ^ 2) ∧
        ∀ S, 0 ≤ S → 6 * Num.mp ^ 2 * compositeDelta (Num.Rud * S) S (549 / 1000) = Table.Row.G06 ^ 2 →
          (-1.005 : ℝ) < (Num.mp * √(6 * compositeDelta S (Table.Row.B04 * S) (549 / 1000)) - 497.611) / 0.013 ∧
            (Num.mp * √(6 * compositeDelta S (Table.Row.B04 * S) (549 / 1000)) - 497.611) / 0.013 < -0.995) ∧
      ((-0.005 : ℝ) < (Num.mp * √(6 * compositeDelta Table.Row.Sd (19961420 / 1000000 * Table.Row.Sd) (8 / 15)) - 497.611) / 0.013 ∧
        (Num.mp * √(6 * compositeDelta Table.Row.Sd (19961420 / 1000000 * Table.Row.Sd) (8 / 15)) - 497.611) / 0.013 < 0.005) ∧
      ((-1.005 : ℝ) < (Num.mp * √(6 * compositeDelta Table.Row.Sd (19960252 / 1000000 * Table.Row.Sd) (8 / 15)) - 497.611) / 0.013 ∧
        (Num.mp * √(6 * compositeDelta Table.Row.Sd (19960252 / 1000000 * Table.Row.Sd) (8 / 15)) - 497.611) / 0.013 < -0.995) ∧
      ((0.995 : ℝ) < (Num.mp * √(6 * compositeDelta Table.Row.Sd (19962588 / 1000000 * Table.Row.Sd) (8 / 15)) - 497.611) / 0.013 ∧
        (Num.mp * √(6 * compositeDelta Table.Row.Sd (19962588 / 1000000 * Table.Row.Sd) (8 / 15)) - 497.611) / 0.013 < 1.005) ∧
      ((0.1705 : ℝ) < (Num.mp * √(6 * compositeDelta Table.Row.Sd (Table.Row.B04 * (100001 / 100000) * Table.Row.Sd) (8 / 15)) -
          Num.mp * √(6 * compositeDelta Table.Row.Sd (Table.Row.B04 * Table.Row.Sd) (8 / 15))) / 0.013 ∧
        (Num.mp * √(6 * compositeDelta Table.Row.Sd (Table.Row.B04 * (100001 / 100000) * Table.Row.Sd) (8 / 15)) -
          Num.mp * √(6 * compositeDelta Table.Row.Sd (Table.Row.B04 * Table.Row.Sd) (8 / 15))) / 0.013 < 0.1715) ∧
      ((0.1774605 : ℝ) < f1 (yR (Table.Row.Sd * Table.Row.B04)) ∧ f1 (yR (Table.Row.Sd * Table.Row.B04)) < 0.1774615) ∧
      HasDerivAt deltaLevel (f1 (yR (Table.Row.Sd * Table.Row.B04))) (Table.Row.Sd * Table.Row.B04) ∧
      ((6.55e-8 : ℝ) < compositeDelta Table.Row.Sd (Table.Row.B04 * Table.Row.Sd) (8 / 15) -
          (deltaLevel (Table.Row.Sd * Table.Row.B04) + Table.Row.Sd * ((1 - 8 / 15) / 5 + 8 / 15 * f1 (yR (Table.Row.Sd * Table.Row.B04))) -
            6 / 125 * Table.Row.Sd ^ 2) ∧
        compositeDelta Table.Row.Sd (Table.Row.B04 * Table.Row.Sd) (8 / 15) -
            (deltaLevel (Table.Row.Sd * Table.Row.B04) + Table.Row.Sd * ((1 - 8 / 15) / 5 + 8 / 15 * f1 (yR (Table.Row.Sd * Table.Row.B04))) -
              6 / 125 * Table.Row.Sd ^ 2) < 6.65e-8)) := by
  refine ⟨Completion.Comp.kaon_book, ?_⟩
  rw [Completion.Num.mp_eq_q, Table.G06_eq_q, Table.B04_eq_q, Completion.Num.Rud_eq]
  exact Completion.Comp.kaon_every_coupling

/-- **Proposition 206 (the clock's overlap and its exponent `−3/2`).** The clock at `{h, n}` has the five marks
`(0, 1, 2, 3, 19)/4`, the last `1/(4|Φ@{h,n}|)`, ten gaps `D` with `E_D = 2` and `Var D = 61/16`, and the rate
`ν = e@{h,n}²/(E_PEℓ) = 9/4000`; the gap law tilted at `x` is `p_x(D) = e^{−xD}/(10M_Q(x))`;
`Σ_D(p_ν(D)p_{−ν}(D))^{1/2} = [M_Q(ν)M_Q(−ν)]^{−1/2}`, and
`h = (Σ_D(p_νp_{−ν})^{1/2})^{k_C} = [M_Q(ν)M_Q(−ν)]^{−k_Cs@{h}} = [M_Q(ν)M_Q(−ν)]^{−3/2} = 0.9999710493297`;
`−log h = k_C·(1/2)[c_Q(ν) + c_Q(−ν)] = (3/2)Var D ν² + O(ν⁴)`: `|M_Q(ν)M_Q(−ν) − 1 − (61/16)ν²| ≤ 27ν⁴` for
`|ν| ≤ 1/5`, and `−log h/ν² → (3/2)Var D`. -/
theorem prop_206 :
    (open Real Complex Matrix Kronecker Filter Topology Comparison Comparison.Law Comparison.System.Completion in
      clockMarks sLastDirectionSinglet = ![0, 1 / 4, 2 / 4, 3 / 4, longMark sLastDirectionSinglet / 4] ∧ longMark sLastDirectionSinglet = 19 ∧
      longMark sLastDirectionSinglet = 1 / ‖PhiS sLastDirectionSinglet‖ ∧
      ((1 / 10) * ∑ i, clockGap sLastDirectionSinglet i = 2 ∧ (1 / 10) * ∑ i, clockGap sLastDirectionSinglet i ^ 2 - 2 ^ 2 = 61 / 16) ∧
      nuS sLastDirectionSinglet = eS sLastDirectionSinglet ^ 2 / (Num.EP * Num.El) ∧ Num.nu = 9 / 4000 ∧
      (∀ x : ℝ, ∀ i, RuleAndLaw.tiltLaw x i = Real.exp (-(x * clockGap sLastDirectionSinglet i)) / (10 * clockMQ sLastDirectionSinglet x)) ∧
      (∀ x : ℝ, ∑ i, Real.sqrt (RuleAndLaw.tiltLaw x i * RuleAndLaw.tiltLaw (-x) i) =
        (clockMQ sLastDirectionSinglet x * clockMQ sLastDirectionSinglet (-x)) ^ (-(1 / 2 : ℝ))) ∧
      (hOv sLastDirectionSinglet = (∑ i, Real.sqrt (RuleAndLaw.tiltLaw (9 / 4000) i * RuleAndLaw.tiltLaw (-(9 / 4000)) i)) ^ 3 ∧
        hOv sLastDirectionSinglet = (clockMQ sLastDirectionSinglet (9 / 4000) * clockMQ sLastDirectionSinglet (-(9 / 4000))) ^
          (-(((((LZ sHere - LZ sC) / 2 : ℤ) : ℝ)) * powS sLastDirection))) ∧
      hOv sLastDirectionSinglet = (clockMQ sLastDirectionSinglet (9 / 4000) * clockMQ sLastDirectionSinglet (-(9 / 4000))) ^ (-(3 / 2 : ℝ)) ∧
      ((0.99997104932965 : ℝ) < hOv sLastDirectionSinglet ∧ hOv sLastDirectionSinglet < 0.99997104932975) ∧
      Tendsto (fun ν : ℝ => -Real.log (Formulas.clockTilt ν) / ν ^ 2) (𝓝[≠] 0) (𝓝 (3 / 2 * (61 / 16))) ∧
      hOv sLastDirectionSinglet = Formulas.clockTilt (9 / 4000)) ∧
    (open Real Filter Topology Asymptotics Comparison Comparison.Law in
      (∀ ν : ℝ, -Real.log (Formulas.clockTilt ν) =
        3 / 2 * (Real.log (clockMQ sLastDirectionSinglet ν) + Real.log (clockMQ sLastDirectionSinglet (-ν)))) ∧
      (∀ ν : ℝ, |ν| ≤ 1 / 5 → |Formulas.clockPair ν - 1 - 61 / 16 * ν ^ 2| ≤ 27 * ν ^ 4) ∧
      (fun ν : ℝ => -Real.log (Formulas.clockTilt ν) - 3 / 2 * (61 / 16) * ν ^ 2) =O[𝓝 0] (fun ν : ℝ => ν ^ 4)) :=
  ⟨Completion.Comp.clock_overlap, Completion.Comp.clock_fourth_order⟩

end Comparison.System
