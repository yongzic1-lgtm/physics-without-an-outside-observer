import Comparison.System.Existence.Six
import Comparison.System.Existence.Excursion
import Comparison.Existence.Matter
import Comparison.Existence.Pair
import Comparison.WholePicture.Geometry
import Comparison.Article.Geometry3
import Comparison.Article.Side

/-!
# The proof system, the existence layer: matter (Propositions 45, 48 to 51, 99)

Book IX, seen from the plane `F = {h, k}` of a line and the three
lines `C` outside it; every statement holds for every plane (`h ≠ k`). Props. 46 and 47 are in
`System/Existence/PairModel.lean` and `System/Existence/LastDirection.lean`.
-/

namespace Comparison.System.Existence

open Matrix Complex Kronecker

/-! ## Proposition 45 -/

/-- The count each line carries: `½` on the two lines of the plane, `−⅓` on the three outside. -/
def lineY (h k x : Fin 5) : ℚ := if x ∈ ({h, k} : Finset (Fin 5)) then 1 / 2 else -1 / 3

/-- `Y` is the sum of the counts of the lines a two-spinor state disagrees on. -/
theorem hyper_eq_sum (h k : Fin 5) (r : Fin 16) : hyper h k r = ∑ x ∈ disagreeSet r, lineY h k x := by
  rw [hyper, nPlane, nOut]
  simp only [lineY]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, Finset.filter_mem_eq_inter, nsmul_eq_mul,
    nsmul_eq_mul]
  have e : (disagreeSet r).filter (fun x => x ∉ ({h, k} : Finset (Fin 5))) = disagreeSet r \ {h, k} := by
    ext x
    simp [Finset.mem_sdiff]
  rw [e]
  ring

theorem lineY_sum : ∀ h k : Fin 5, h ≠ k → ∑ x, lineY h k x = 0 := by
  decide +kernel

theorem plane_out_card : ∀ (h k : Fin 5) (r : Fin 16), nPlane h k r + nOut h k r = (disagreeSet r).card := by
  decide +kernel

theorem classes_plane_out : ∀ h k : Fin 5, h ≠ k →
    (Finset.univ.filter fun r => nPlane h k r = 0 ∧ nOut h k r = 0).card = 1 ∧
    (Finset.univ.filter fun r => nPlane h k r = 2 ∧ nOut h k r = 0).card = 1 ∧
    (Finset.univ.filter fun r => nPlane h k r = 1 ∧ nOut h k r = 1).card = 6 ∧
    (Finset.univ.filter fun r => nPlane h k r = 0 ∧ nOut h k r = 2).card = 3 ∧
    (Finset.univ.filter fun r => nPlane h k r = 1 ∧ nOut h k r = 3).card = 2 ∧
    (Finset.univ.filter fun r => nPlane h k r = 2 ∧ nOut h k r = 2).card = 3 := by
  decide +kernel

theorem class_hyper (h k : Fin 5) (r : Fin 16) :
    (nPlane h k r = 0 ∧ nOut h k r = 0 → hyper h k r = 0) ∧
    (nPlane h k r = 2 ∧ nOut h k r = 0 → hyper h k r = 1) ∧
    (nPlane h k r = 1 ∧ nOut h k r = 1 → hyper h k r = 1 / 6) ∧
    (nPlane h k r = 0 ∧ nOut h k r = 2 → hyper h k r = -2 / 3) ∧
    (nPlane h k r = 1 ∧ nOut h k r = 3 → hyper h k r = -1 / 2) ∧
    (nPlane h k r = 2 ∧ nOut h k r = 2 → hyper h k r = 1 / 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro ⟨h1, h2⟩ <;> rw [hyper, h1, h2] <;> norm_num

/-- **Proposition 45 (one generation, seen from the plane).** For every plane `F = {h, k}`: each two-spinor state `e_S`
meets the plane in `N_F = |S ∩ F|` lines and the outside in `N_C = |S ∩ C|`, `N_F + N_C = |S| ∈ {0, 2, 4}`; the
classes `(N_F, N_C) = (0,0), (2,0), (1,1), (0,2), (1,3), (2,2)` hold `1, 1, 6, 3, 2, 3` two-spinor states, with
`Y = N_F/2 − N_C/3 = 0, 1, 1/6, −2/3, −1/2, 1/3`; `Y = Σ_{x ∈ S} y_x` with `y = ½` on the plane and `−⅓` outside,
`Σ_x y_x = 0`; the values of `Y` occur `1, 6, 3, 1, 3, 2` times; `Σ Y = Σ Y³ = 0`, the colour and the doublet sums of
`Y` vanish, as many two-spinor states in triplets as in antitriplets, eight in doublets; `Σ Y⁵ = 5/9`;
`Q = N_k − N_C/3 = T₃ + Y`, `T₃ = (N_k − N_h)/2`, with the charges `0` twice, `2/3, −1/3, −2/3, 1/3` three times,
`±1` once; the last-step direction's vector state is neutral; the ten symmetric states meet `F` in two lines once, in one line six times, in
none three times.

Recognition: with the line charges `(0, 1, −⅓, −⅓, −⅓)` the sixteen two-spinor states are `ν^c` (`Y = 0`), `e^c` (`1`),
`u^c` (`−2/3`, three), `Q` (`1/6`, six), `d^c` (`1/3`, three) and `L` (`−1/2`, two): one generation with its
right-handed neutrino; the vanishing sums are the absence of anomalies; the eight two-spinor states meeting the plane in one
line are the weak doublets, parity broken at the plane. Uses Props. 10, 25. -/
theorem prop_45 (h k : Fin 5) (hk : h ≠ k) :
    (∀ r : Fin 16, nPlane h k r + nOut h k r = (disagreeSet r).card ∧
      ((disagreeSet r).card = 0 ∨ (disagreeSet r).card = 2 ∨ (disagreeSet r).card = 4)) ∧
    ((Finset.univ.filter fun r => nPlane h k r = 0 ∧ nOut h k r = 0).card = 1 ∧
     (Finset.univ.filter fun r => nPlane h k r = 2 ∧ nOut h k r = 0).card = 1 ∧
     (Finset.univ.filter fun r => nPlane h k r = 1 ∧ nOut h k r = 1).card = 6 ∧
     (Finset.univ.filter fun r => nPlane h k r = 0 ∧ nOut h k r = 2).card = 3 ∧
     (Finset.univ.filter fun r => nPlane h k r = 1 ∧ nOut h k r = 3).card = 2 ∧
     (Finset.univ.filter fun r => nPlane h k r = 2 ∧ nOut h k r = 2).card = 3) ∧
    (∀ r : Fin 16,
      (nPlane h k r = 0 ∧ nOut h k r = 0 → hyper h k r = 0) ∧
      (nPlane h k r = 2 ∧ nOut h k r = 0 → hyper h k r = 1) ∧
      (nPlane h k r = 1 ∧ nOut h k r = 1 → hyper h k r = 1 / 6) ∧
      (nPlane h k r = 0 ∧ nOut h k r = 2 → hyper h k r = -2 / 3) ∧
      (nPlane h k r = 1 ∧ nOut h k r = 3 → hyper h k r = -1 / 2) ∧
      (nPlane h k r = 2 ∧ nOut h k r = 2 → hyper h k r = 1 / 3)) ∧
    (∀ r : Fin 16, hyper h k r = ∑ x ∈ disagreeSet r, lineY h k x) ∧ ∑ x, lineY h k x = 0 ∧
    ((Finset.univ.filter fun r => hyper h k r = 0).card = 1 ∧
     (Finset.univ.filter fun r => hyper h k r = 1 / 6).card = 6 ∧
     (Finset.univ.filter fun r => hyper h k r = -2 / 3).card = 3 ∧
     (Finset.univ.filter fun r => hyper h k r = 1).card = 1 ∧
     (Finset.univ.filter fun r => hyper h k r = 1 / 3).card = 3 ∧
     (Finset.univ.filter fun r => hyper h k r = -1 / 2).card = 2) ∧
    (∑ r, hyper h k r = 0 ∧ ∑ r, hyper h k r ^ 3 = 0 ∧
     ∑ r ∈ Finset.univ.filter (fun r => nOut h k r = 1 ∨ nOut h k r = 2), hyper h k r = 0 ∧
     ∑ r ∈ Finset.univ.filter (fun r => nPlane h k r = 1), hyper h k r = 0 ∧
     (Finset.univ.filter fun r => nOut h k r = 1).card = (Finset.univ.filter fun r => nOut h k r = 2).card ∧
     (Finset.univ.filter fun r => nPlane h k r = 1).card = 8) ∧
    ∑ r, hyper h k r ^ 5 = 5 / 9 ∧
    (∀ r : Fin 16, charge h k r = isospin h k r + hyper h k r) ∧
    (∀ r : Fin 16, isospin h k r =
      ((if k ∈ disagreeSet r then 1 else 0) - (if h ∈ disagreeSet r then 1 else 0)) / 2) ∧
    ((Finset.univ.filter fun r => charge h k r = 0).card = 2 ∧
     (Finset.univ.filter fun r => charge h k r = 2 / 3).card = 3 ∧
     (Finset.univ.filter fun r => charge h k r = -1 / 3).card = 3 ∧
     (Finset.univ.filter fun r => charge h k r = -2 / 3).card = 3 ∧
     (Finset.univ.filter fun r => charge h k r = 1 / 3).card = 3 ∧
     (Finset.univ.filter fun r => charge h k r = 1).card = 1 ∧
     (Finset.univ.filter fun r => charge h k r = -1).card = 1) ∧
    (charge h k (transition h 0) = 0 ∧ charge h k (transition k 0) = -1) ∧
    ((Finset.univ.filter fun r => (disagreeSet r).card = 2 ∧ nPlane h k r = 2).card = 1 ∧
     (Finset.univ.filter fun r => (disagreeSet r).card = 2 ∧ nPlane h k r = 1).card = 6 ∧
     (Finset.univ.filter fun r => (disagreeSet r).card = 2 ∧ nPlane h k r = 0).card = 3) :=
  ⟨fun r => ⟨plane_out_card h k r, irreps.1 r⟩, classes_plane_out h k hk, fun r => class_hyper h k r,
    hyper_eq_sum h k, lineY_sum h k hk, hyper_values h k hk, no_anomaly h k hk,
    WholePicture.hyper_fifth h k hk, charge_eq h k hk, fun r => rfl, charge_values h k hk,
    lastDirection_line_neutral h k hk, plane_meets h k hk⟩

/-! ## Proposition 48 -/

/-- Proposition 48, the singlet, symmetric and vector states and their projectors (`IrrepsWhole.lean`: `prop_48`). A two-spinor state disagrees on `N = 0`, `2` or `4` lines, `1 + 10 + 5` two-spinor states,
and none on six (an even set of five lines has at most four); the comparison is `L = 6 − 2N = 6, 2, −2` on them;
`Π₀ = E/4`, `Π_F = (1 + P)/2`, `Π_L = (1 − P)/2 − E/4` are one on the singlet, the symmetric states and the vector states
respectively and zero on the others.

Recognition: three families and no fourth, the electron at no distinction, the muon reaching the symmetric states, the tau
reaching the vector states. Uses Props. 10, 11, 13. -/
theorem prop_48_irreps :
    (∀ k : Fin 16, (disagreeSet k).card = 0 ∨ (disagreeSet k).card = 2 ∨ (disagreeSet k).card = 4) ∧
    (Finset.univ.filter fun k : Fin 16 => (disagreeSet k).card = 0).card = 1 ∧
    (Finset.univ.filter fun k : Fin 16 => (disagreeSet k).card = 2).card = 10 ∧
    (Finset.univ.filter fun k : Fin 16 => (disagreeSet k).card = 4).card = 5 ∧
    (∀ k : Fin 16, (disagreeSet k).card ≠ 6) ∧
    (∀ k : Fin 16, L *ᵥ rel k = ((Lvalue k : ℤ) : ℂ) • rel k ∧ Lvalue k = 6 - 2 * (disagreeSet k).card) ∧
    (∀ k : Fin 16,
      ((1 / 4 : ℂ) • Eop) *ᵥ rel k = (if (disagreeSet k).card = 0 then 1 else 0 : ℂ) • rel k ∧
      ((1 / 2 : ℂ) • (1 + swap)) *ᵥ rel k = (if (disagreeSet k).card = 2 then 1 else 0 : ℂ) • rel k ∧
      ((1 / 2 : ℂ) • (1 - swap) - (1 / 4 : ℂ) • Eop) *ᵥ rel k =
        (if (disagreeSet k).card = 4 then 1 else 0 : ℂ) • rel k) := by
  obtain ⟨l1, l2, l3, l4⟩ := irreps
  refine ⟨l1, l2, l3, l4, fun k => ?_, fun k => ⟨L_rel' k, rfl⟩, irrep_projectors⟩
  rcases l1 k with h | h | h <;> omega

/-! ## Proposition 49 -/

/-- **`Φ(z) = −z²Ψ(z²/16)`** for every `z`. -/
theorem Phi_eq_Psi (z : ℂ) : Law.Phi z = -z ^ 2 * Law.Psi (z ^ 2 / 16) := by
  unfold Law.Phi Law.Psi
  by_cases h : (16 + 3 * z ^ 2 : ℂ) = 0
  · have h' : (1 + 3 * (z ^ 2 / 16) : ℂ) = 0 := by linear_combination h / 16
    rw [h, h', div_zero, div_zero]
    ring
  · have h' : (1 + 3 * (z ^ 2 / 16) : ℂ) ≠ 0 := by
      intro e
      apply h
      linear_combination 16 * e
    field_simp

theorem plane_card : ∀ a b : Fin 5, a ≠ b → ({a.succ, b.succ} : Finset (Fin 6)).card = 2 := by
  decide +kernel

/-- **Proposition 49 (one plane at its two signs).** For every plane `{a, b}`: at the plane itself (even, a count)
`z = −1`, `L = 5`, `w = −1/5`, `w² = 1/25`; at its counterpart `{a, b}'`, the three lines outside it (odd, an amplitude),
`z = −i`, `L = −1`, `w = i`, `w² = −1`; `Φ(z) = −z²Ψ(z²/16)` with `Ψ(v) = v/(1 + 3v)`; `Ψ(w²) = 1/28` at the plane and
`1/2` at its counterpart with `n` added; the sign `z²` each puts on the clock is `+1`, `−1`; on both signs each two-spinor state of the singlet, the symmetric or the vector states weighs
`|L/6|^{−1/2} = √3`.

Recognition: the charged leptons sit at the plane and the quarks at its counterpart with `n` added, one mass operator for both. Uses
Props. 10, 30, 44. -/
theorem prop_49 (a b : Fin 5) (hab : a ≠ b) :
    zS {a.succ, b.succ} = -1 ∧ Law.LS {a.succ, b.succ} = 5 ∧ Law.wS {a.succ, b.succ} = -1 / 5 ∧
    Law.wS {a.succ, b.succ} ^ 2 = 1 / 25 ∧
    zS (outside a b) = -I ∧ Law.LS (outside a b) = -1 ∧ Law.wS (outside a b) = I ∧
    Law.wS (outside a b) ^ 2 = -1 ∧
    (∀ z : ℂ, Law.Phi z = -z ^ 2 * Law.Psi (z ^ 2 / 16)) ∧ (∀ v : ℂ, Law.Psi v = v / (1 + 3 * v)) ∧
    Law.PsiS {a.succ, b.succ} = 1 / 28 ∧ Law.PsiS (outside a b) = 1 / 2 ∧
    zS {a.succ, b.succ} ^ 2 = 1 ∧ zS (outside a b) ^ 2 = -1 ∧
    (∀ k : Fin 16, k ≠ 0 → |(Lvalue k : ℝ) / 6| = 1 / 3 ∧ Real.sqrt (|(Lvalue k : ℝ) / 6|)⁻¹ = Real.sqrt 3) := by
  have hc := plane_card a b hab
  have he : Even ({a.succ, b.succ} : Finset (Fin 6)).card := by rw [hc]; decide
  obtain ⟨hL1, hw1, -, -, hw1sq, -⟩ := twin_step hab
  have hz : zS {a.succ, b.succ} = -1 := by
    simp only [zS, Law.zS, hc, I_sq]
  have hz' : zS (outside a b) = -I := by
    have hc3 : ∀ a b : Fin 5, a ≠ b → (outside a b).card = 3 := by decide +kernel
    simp only [zS, Law.zS, hc3 a b hab]
    exact I_pow_three
  have hL : Law.LS {a.succ, b.succ} = 5 := Law.LS_even he
  have hw : Law.wS {a.succ, b.succ} = -1 / 5 := by
    rw [wS_eq, hz, hL]
  have hLv : ∀ k : Fin 16, k ≠ 0 → (Lvalue k = 2 ∨ Lvalue k = -2) := by decide
  refine ⟨hz, hL, hw, by rw [hw]; norm_num, hz', hL1, hw1, hw1sq, Phi_eq_Psi, fun v => rfl, ?_, ?_,
    by rw [hz]; norm_num, by rw [hz', neg_sq, I_sq], fun k hk => ?_⟩
  · rw [Law.PsiS, hw, Law.Psi]
    norm_num
  · rw [Law.PsiS, hw1sq, Law.Psi]
    norm_num
  · have h3 : |(Lvalue k : ℝ) / 6| = 1 / 3 := by
      rcases hLv k hk with e | e <;> rw [e] <;> norm_num [abs_div]
    refine ⟨h3, ?_⟩
    rw [h3]
    norm_num

/-! ## Proposition 50 -/

theorem b_value : varP / (2 * (varP + varQ)) = 7 / 16 := by
  rw [varP_eq, varQ_eq]
  norm_num

/-- **Proposition 50 (the complex weight).** For every plane `{a, b}`: the plane whose one end counts an excursion at `{}`,
`b = Var P/(2(Var P + Var Q)) = 7/16` (Prop. 30), and whose other end carries the three outside lines,
`w_C = i` (Prop. 44), has `b + w_C = 7/16 + i`, of angle `arg(7 + 16i) = arctan(16/7) = 1.15839…`; with the other
orientation of the square root of the sign (`C` named `{n, a, b}`, `w = −i`), `b + w = 7/16 − i`, of angle `−arg(7 + 16i)`.

Recognition: the phase of quark mixing and its sign; the orientation `q` is the one that calls matter matter. Uses
Props. 30, 44. -/
theorem prop_50 (a b : Fin 5) (hab : a ≠ b) :
    ((varP / (2 * (varP + varQ)) : ℝ) : ℂ) + Law.wS (outside a b) = 7 / 16 + I ∧
    ((varP / (2 * (varP + varQ)) : ℝ) : ℂ) + Law.wS {0, a.succ, b.succ} = 7 / 16 - I ∧
    Complex.arg (7 / 16 + I) = Complex.arg (7 + 16 * I) ∧
    Complex.arg (7 + 16 * I) = Real.arctan (16 / 7) ∧
    ((1.158385 : ℝ) < Complex.arg (7 + 16 * I) ∧ Complex.arg (7 + 16 * I) < 1.158395) ∧
    Complex.arg (7 / 16 - I) = -Complex.arg (7 + 16 * I) := by
  obtain ⟨-, hw1, -, hw2, -, -⟩ := twin_step hab
  obtain ⟨-, hbw, hd1, hd2, -, hbounds, hconj⟩ := Article.crossed_plane
  have hb : ((varP / (2 * (varP + varQ)) : ℝ) : ℂ) = 7 / 16 := by
    rw [b_value]
    push_cast
    ring
  have harg : Complex.arg (7 / 16 + I) = Article.deltaQ := by
    rw [Article.deltaQ, hbw]
  refine ⟨by rw [hb, hw1], by rw [hb, hw2]; ring, by rw [harg, hd1], by rw [← hd1, hd2], ?_, ?_⟩
  · rw [← hd1]
    exact hbounds
  · rw [hconj, hd1]

/-! ## Proposition 51 -/

/-- **Proposition 51 (the line factor at the last-step direction's phase).** The factor of the law on the vector states,
`1 + 3u + 4u²` at `u = z/4`: `2` at `z = 1` (`u_∅ = 1/4`) and `(3/4)(1 + i)` at the last-step direction's phase `z = i`
(`u_{\{t\}} = i/4`), of phase `π/4`, half phase `π/8`; `tan²(π/8) = 3 − 2√2 = 0.171573…`; at every even divided set
the factor is real and positive.

Recognition: the ratio of the two light neutral masses `ρ_ν = tan²(π/8)`. Uses Props. 35, 44. -/
theorem prop_51 :
    Article.lineFactor (1 / 4) = 2 ∧ Article.lineFactor (I / 4) = 3 / 4 * (1 + I) ∧
    Complex.arg (Article.lineFactor (I / 4)) = Real.pi / 4 ∧
    Real.tan (Real.pi / 8) ^ 2 = 3 - 2 * Real.sqrt 2 ∧
    ((0.1715725 : ℝ) < 3 - 2 * Real.sqrt 2 ∧ 3 - 2 * Real.sqrt 2 < 0.1715735) ∧
    (∀ S : Finset (Fin 6), Even S.card →
      (Article.lineFactor (Law.uS S)).im = 0 ∧ 0 < (Article.lineFactor (Law.uS S)).re) ∧
    (∀ t : Fin 5, Law.uS {t.succ} = I / 4) ∧ Law.uS ∅ = 1 / 4 := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := Article.line_factor
  refine ⟨f1, f2, f3, f4, f5, fun S hS => ?_, fun t => ?_, ?_⟩
  · obtain ⟨m, hm⟩ := hS
    have hu : Law.uS S = I ^ (2 * m) / 4 := by
      rw [Law.uS, Law.zS, hm, two_mul]
    rw [hu]
    exact f6 m
  · simp [Law.uS, Law.zS]
  · simp [Law.uS, Law.zS]

/-! ## Proposition 99 -/

/-- The sign vector of a pairing of the four lines beside the last-step direction: `+1` on the pair `{k, c}`, `−1` on the other
pair. -/
def pairVec (k c x : Fin 5) : ℤ := if x = k ∨ x = c then 1 else -1

theorem pairVec_facts : ∀ h k : Fin 5, h ≠ k →
    (∀ x : Fin 5, x ≠ h →
      ∑ c ∈ Finset.univ.filter (fun c => c ≠ h ∧ c ≠ k), pairVec k c x = if x = k then 3 else -1) ∧
    (∀ c c' : Fin 5, c ≠ h → c ≠ k → c' ≠ h → c' ≠ k →
      ∑ x ∈ Finset.univ.filter (fun x => x ≠ h), pairVec k c x * pairVec k c' x = if c = c' then 4 else 0) := by
  decide +kernel

theorem gammaZ_pairings : ∀ h a b c d : Fin 5, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    a ≠ h → b ≠ h → c ≠ h → d ≠ h →
    (γZ a * γZ b) * (γZ c * γZ d) = γZ h ∨ (γZ a * γZ b) * (γZ c * γZ d) = -γZ h := by
  decide +kernel

theorem gamma_pairings (h a b c d : Fin 5) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (ha : a ≠ h) (hb : b ≠ h) (hc : c ≠ h) (hd : d ≠ h) :
    (γ a * γ b) * (γ c * γ d) = γ h ∨ (γ a * γ b) * (γ c * γ d) = -γ h := by
  have hmap : ∀ M : Matrix Four Four GaussianInt, (-M).map GaussianInt.toComplex = -(M.map GaussianInt.toComplex) := by
    intro M
    ext i j
    simp
  rcases gammaZ_pairings h a b c d hab hac had hbc hbd hcd ha hb hc hd with e | e
  · left
    have := congrArg (fun M => M.map GaussianInt.toComplex) e
    simpa only [Matrix.map_mul, γZ_map] using this
  · right
    have := congrArg (fun M => M.map GaussianInt.toComplex) e
    simpa only [Matrix.map_mul, γZ_map, hmap] using this

/-- The projection on the last-step direction's side `Q(h) = (1 + γ_h)/2`. -/
noncomputable def sideQ (h : Fin 5) : Matrix Four Four ℂ := (1 / 2 : ℂ) • (1 + γ h)

/-- `K_c = γ_kγ_c`, a rotation beside the last-step direction. -/
noncomputable def Kc (k c : Fin 5) : Matrix Four Four ℂ := γ k * γ c

theorem Kc_sq {k c : Fin 5} (hkc : k ≠ c) : Kc k c * Kc k c = -1 := by
  simp only [Kc]
  rw [show γ k * γ c * (γ k * γ c) = γ k * (γ c * γ k) * γ c by simp only [Matrix.mul_assoc],
    γ_anticomm (Ne.symm hkc), Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, γ_mul_self, Matrix.one_mul,
    γ_mul_self]

theorem Kc_anticomm {k c d : Fin 5} (hkc : k ≠ c) (hkd : k ≠ d) (hcd : c ≠ d) :
    Kc k c * Kc k d = -(Kc k d * Kc k c) := by
  simp only [Kc]
  have e1 : γ k * γ c * (γ k * γ d) = -(γ c * γ d) := by
    rw [show γ k * γ c * (γ k * γ d) = γ k * (γ c * γ k) * γ d by simp only [Matrix.mul_assoc],
      γ_anticomm (Ne.symm hkc), Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, γ_mul_self, Matrix.one_mul]
  have e2 : γ k * γ d * (γ k * γ c) = -(γ d * γ c) := by
    rw [show γ k * γ d * (γ k * γ c) = γ k * (γ d * γ k) * γ c by simp only [Matrix.mul_assoc],
      γ_anticomm (Ne.symm hkd), Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, γ_mul_self, Matrix.one_mul]
  rw [e1, e2, γ_anticomm hcd, neg_neg]

theorem Kc_comm_lastDirection {h k c : Fin 5} (hkh : k ≠ h) (hch : c ≠ h) : Kc k c * γ h = γ h * Kc k c := by
  simp only [Kc]
  rw [Matrix.mul_assoc, γ_anticomm hch, Matrix.mul_neg, ← Matrix.mul_assoc, γ_anticomm hkh, Matrix.neg_mul,
    neg_neg, Matrix.mul_assoc]

/-! ### The operators of the last-step direction's side -/

/-- `2Q(h)` over the Gaussian integers. -/
def sideQ2Z (h : Fin 5) : Matrix Four Four GaussianInt := 1 + γZ h

/-- The outside lines of the plane `{h, k}`. -/
def outLines (h k : Fin 5) : Finset (Fin 5) := Finset.univ.filter fun c => c ≠ h ∧ c ≠ k

/-- On every `Y_ab = (2Q) E_ab (2Q)`: `4Y = tr(Y) 2Q − Σ_c tr(K_cY) K_c 2Q`, over the Gaussian integers. -/
theorem side_span_Z : ∀ h k : Fin 5, h ≠ k → ∀ a b : Four,
    (4 : GaussianInt) • (sideQ2Z h * Matrix.single a b 1 * sideQ2Z h) =
      (sideQ2Z h * Matrix.single a b 1 * sideQ2Z h).trace • sideQ2Z h -
        ∑ c ∈ outLines h k, ((γZ k * γZ c) * (sideQ2Z h * Matrix.single a b 1 * sideQ2Z h)).trace •
          ((γZ k * γZ c) * sideQ2Z h) := by
  decide +kernel

theorem mapC_mul (A B : Matrix Four Four GaussianInt) :
    (A * B).map GaussianInt.toComplex = A.map GaussianInt.toComplex * B.map GaussianInt.toComplex :=
  Matrix.map_mul

theorem mapC_add (A B : Matrix Four Four GaussianInt) :
    (A + B).map GaussianInt.toComplex = A.map GaussianInt.toComplex + B.map GaussianInt.toComplex := by
  ext i j
  simp

theorem mapC_sub (A B : Matrix Four Four GaussianInt) :
    (A - B).map GaussianInt.toComplex = A.map GaussianInt.toComplex - B.map GaussianInt.toComplex := by
  ext i j
  simp

theorem mapC_one : (1 : Matrix Four Four GaussianInt).map GaussianInt.toComplex = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem mapC_single (a b : Four) :
    (Matrix.single a b (1 : GaussianInt)).map GaussianInt.toComplex = Matrix.single a b 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem mapC_smul (c : GaussianInt) (A : Matrix Four Four GaussianInt) :
    (c • A).map GaussianInt.toComplex = GaussianInt.toComplex c • A.map GaussianInt.toComplex := by
  ext i j
  simp

theorem mapC_sum {ι : Type*} (s : Finset ι) (M : ι → Matrix Four Four GaussianInt) :
    (∑ i ∈ s, M i).map GaussianInt.toComplex = ∑ i ∈ s, (M i).map GaussianInt.toComplex := by
  ext i j
  simp [Matrix.sum_apply]

theorem toC_trace (A : Matrix Four Four GaussianInt) :
    GaussianInt.toComplex A.trace = (A.map GaussianInt.toComplex).trace := by
  simp [Matrix.trace, map_sum]

/-- On every `Y_ab = (2Q) E_ab (2Q)`: `4Y = tr(Y) 2Q − Σ_c tr(K_cY) K_c 2Q`. -/
theorem side_span_C (h k : Fin 5) (hk : h ≠ k) (a b : Four) :
    (4 : ℂ) • ((1 + γ h) * Matrix.single a b 1 * (1 + γ h)) =
      ((1 + γ h) * Matrix.single a b 1 * (1 + γ h)).trace • (1 + γ h) -
        ∑ c ∈ outLines h k, (Kc k c * ((1 + γ h) * Matrix.single a b 1 * (1 + γ h))).trace •
          (Kc k c * (1 + γ h)) := by
  have e := congrArg (fun M => M.map GaussianInt.toComplex) (side_span_Z h k hk a b)
  simp only [mapC_smul, mapC_sub, mapC_sum, toC_trace, mapC_mul, mapC_add, mapC_one, mapC_single, γZ_map,
    sideQ2Z] at e
  have h4 : GaussianInt.toComplex 4 = 4 := map_ofNat _ 4
  rw [h4] at e
  exact e

/-- The coordinates of an operator of the side: `Φ(X) = ½ tr(X) Q − ½ Σ_c tr(K_c X) K_c Q`. -/
noncomputable def sideCoord (h k : Fin 5) (X : Matrix Four Four ℂ) : Matrix Four Four ℂ :=
  (1 / 2 * X.trace) • sideQ h - ∑ c ∈ outLines h k, (1 / 2 * (Kc k c * X).trace) • (Kc k c * sideQ h)

theorem sideCoord_add (h k : Fin 5) (X Y : Matrix Four Four ℂ) :
    sideCoord h k (X + Y) = sideCoord h k X + sideCoord h k Y := by
  simp only [sideCoord, Matrix.trace_add, Matrix.mul_add, mul_add, add_smul, Finset.sum_add_distrib]
  abel

theorem sideCoord_smul (h k : Fin 5) (r : ℂ) (X : Matrix Four Four ℂ) :
    sideCoord h k (r • X) = r • sideCoord h k X := by
  simp only [sideCoord, Matrix.trace_smul, Matrix.mul_smul, smul_eq_mul, smul_sub, Finset.smul_sum, smul_smul]
  congr 1
  · congr 1
    ring
  · refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    ring

theorem sideCoord_sum (h k : Fin 5) {ι : Type*} (s : Finset ι) (X : ι → Matrix Four Four ℂ) :
    sideCoord h k (∑ i ∈ s, X i) = ∑ i ∈ s, sideCoord h k (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [sideCoord]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, sideCoord_add, ih]

theorem sideCoord_basis (h k : Fin 5) (hk : h ≠ k) (a b : Four) :
    sideCoord h k (sideQ h * Matrix.single a b 1 * sideQ h) = sideQ h * Matrix.single a b 1 * sideQ h := by
  have e := side_span_C h k hk a b
  set Y := (1 + γ h) * Matrix.single a b 1 * (1 + γ h) with hYdef
  have hQ : sideQ h = (1 / 2 : ℂ) • (1 + γ h) := rfl
  have hY : sideQ h * Matrix.single a b 1 * sideQ h = (1 / 4 : ℂ) • Y := by
    rw [hQ, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hYdef]
    norm_num
  rw [hY, sideCoord_smul]
  congr 1
  have hY4 : Y = (1 / 4 : ℂ) • ((4 : ℂ) • Y) := by
    rw [smul_smul]
    norm_num
  rw [sideCoord, hQ]
  conv_rhs => rw [hY4, e]
  simp only [Matrix.mul_smul, smul_sub, Finset.smul_sum, smul_smul]
  congr 1
  · congr 1
    ring
  · refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    ring

/-- **The operators of the last-step direction's side:** every `X` with `Q X Q = X` is
`½ tr(X) Q − ½ Σ_c tr(K_c X) K_c Q`, a combination of `Q` and the three `K_c Q`. -/
theorem side_span_general (h k : Fin 5) (hk : h ≠ k) (X : Matrix Four Four ℂ)
    (hX : sideQ h * X * sideQ h = X) : X = sideCoord h k X := by
  have hexp : X = ∑ a, ∑ b, X a b • (sideQ h * Matrix.single a b 1 * sideQ h) := by
    conv_lhs => rw [← hX]
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have hs : Matrix.single a b (X a b) = X a b • Matrix.single a b (1 : ℂ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hs, Matrix.mul_smul, Matrix.smul_mul]
  conv_rhs => rw [hexp]
  rw [sideCoord_sum]
  conv_lhs => rw [hexp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sideCoord_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sideCoord_smul, sideCoord_basis h k hk a b]

theorem sideQ_comm (h k c : Fin 5) (hkh : k ≠ h) (hch : c ≠ h) : Kc k c * sideQ h = sideQ h * Kc k c := by
  rw [sideQ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Kc_comm_lastDirection hkh hch]

/-- **Proposition 99 (the three pairings of the four lines beside the last-step direction).** For every last-step direction `h`: the four lines
beside it pair in exactly three ways; for every plane `{h, k}` and the three lines `c` outside it, with
`K_c = γ_kγ_c` on the last-step direction's side `Q(h)H` (`Q(h) = (1 + γ_h)/2`): `K_c² = −1`, `K_cK_d = −K_dK_c`, each `K_c` keeps
the side (it commutes with `γ_h`), and every operator of the side is `½ tr(X) Q − ½ Σ_c tr(K_cX) K_cQ`, a
combination of `Q` and the three `K_cQ`; for each pairing `{a, b | c, d}` of the four lines,
`(γ_aγ_b)(γ_cγ_d) = ±γ_h`, so on the side `γ_aγ_b = ∓γ_cγ_d`; the pairing vectors, `+1` on the pair of `k` and `−1`
on the other, are orthogonal on the four lines (`Σ_x χ_cχ_{c'} = 4δ`) and sum to `3` at `k` and `−1` at each
outside line, `(3, −1, −1, −1)`; `G_Θ = (5I − 𝖩₃)/4` on `1, −P, −E` has `B₃ᵀG_ΘB₃ = diag(1, 10, 5)`;
`3(1 + 10 + 5) = 48`.

Recognition: the three families, each one of the three ways the four lines beside the last-step direction split into two symmetric states; on
the last-step direction's doublet the same three are the three rotations of spin. Uses Props. 4, 5, 13, 48. -/
theorem prop_99 :
    (∀ h : Fin 5, (WholePicture.pairingsBeside h).card = 3) ∧
    (∀ h k : Fin 5, h ≠ k → ∀ c ∈ outLines h k,
      Kc k c * Kc k c = -1 ∧ Kc k c * γ h = γ h * Kc k c ∧ Kc k c * sideQ h = sideQ h * Kc k c) ∧
    (∀ h k : Fin 5, h ≠ k → ∀ c ∈ outLines h k, ∀ d ∈ outLines h k, c ≠ d →
      Kc k c * Kc k d = -(Kc k d * Kc k c)) ∧
    (∀ h k : Fin 5, h ≠ k → ∀ X : Matrix Four Four ℂ, sideQ h * X * sideQ h = X →
      X = (1 / 2 * X.trace) • sideQ h - ∑ c ∈ outLines h k, (1 / 2 * (Kc k c * X).trace) • (Kc k c * sideQ h)) ∧
    (∀ h a b c d : Fin 5, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → a ≠ h → b ≠ h → c ≠ h → d ≠ h →
      (γ a * γ b) * (γ c * γ d) = γ h ∨ (γ a * γ b) * (γ c * γ d) = -γ h) ∧
    (∀ h k : Fin 5, h ≠ k →
      (∀ x : Fin 5, x ≠ h → ∑ c ∈ outLines h k, pairVec k c x = if x = k then 3 else -1) ∧
      (∀ c ∈ outLines h k, ∀ c' ∈ outLines h k,
        ∑ x ∈ Finset.univ.filter (fun x => x ≠ h), pairVec k c x * pairVec k c' x = if c = c' then 4 else 0)) ∧
    Article.gramTheta = !![1, -1 / 4, -1 / 4; -1 / 4, 1, -1 / 4; -1 / 4, -1 / 4, 1] ∧
    Article.B3ᵀ * Article.gramTheta * Article.B3 = Matrix.diagonal ![1, 10, 5] ∧ (3 : ℕ) * (1 + 10 + 5) = 48 := by
  have hout : ∀ h k c : Fin 5, c ∈ outLines h k ↔ c ≠ h ∧ c ≠ k := fun h k c => by
    simp [outLines]
  refine ⟨WholePicture.three_pairings, fun h k hk c hc => ?_, fun h k hk c hc d hd hcd => ?_,
    fun h k hk X hX => side_span_general h k hk X hX, fun h a b c d => gamma_pairings h a b c d,
    fun h k hk => ?_, Article.gramTheta_eq, Article.pairing_gram_diag.1, by norm_num⟩
  · obtain ⟨h1, h2⟩ := (hout h k c).mp hc
    exact ⟨Kc_sq (Ne.symm h2), Kc_comm_lastDirection (Ne.symm hk) h1, sideQ_comm h k c (Ne.symm hk) h1⟩
  · obtain ⟨_, h2⟩ := (hout h k c).mp hc
    obtain ⟨_, h4⟩ := (hout h k d).mp hd
    exact Kc_anticomm (Ne.symm h2) (Ne.symm h4) hcd
  · obtain ⟨p1, p2⟩ := pairVec_facts h k hk
    refine ⟨fun x hx => p1 x hx, fun c hc c' hc' => ?_⟩
    obtain ⟨c1, c2⟩ := (hout h k c).mp hc
    obtain ⟨c3, c4⟩ := (hout h k c').mp hc'
    exact p2 c c' c1 c2 c3 c4

end Comparison.System.Existence
