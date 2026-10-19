import Comparison.System.Completion.Numbers
import Comparison.System.Table.Neutrinos
import Comparison.Law.Bass
import Comparison.GroupsContinuumLaw.Coupling
import Comparison.Elements.OwnPast

set_option linter.style.longLine false

/-!
# The proof system, the completions, part 4: the masses from both pairings (SI Props. 161 to 169, 187; Eqs. (37), (38))

In the first pairing a line holds the division, in the second a meeting of two systems; a
level is a real weight `e^{−S}` on the steps along one line and `δ(S) = log 4u_c(S)` the long-range zero's shift.
-/

namespace Comparison.System

open Real Complex Matrix Kronecker Comparison Comparison.Law Comparison.System.Completion Comparison.Article

/-- **The level `e^{−0.3}` on `h`:** `u_c(0.3) = 2/(3 + (9 + 16e^{−0.3})^{1/2}) = 0.264322355220`. -/
theorem uLevel_point_three : (0.2643223552195 : ℝ) < uLevel (3 / 10) ∧ uLevel (3 / 10) < 0.2643223552205 := by
  have he : Bnd (Real.exp (-(3 / 10))) 0.7408182206817178 0.7408182206817179 :=
    bnd_exp (-(3 / 10)) _ _ 16 (by norm_num) (by norm_num [abs_of_neg])
      (by norm_num [expPoly, expErr, Finset.sum_range_succ, Nat.factorial, abs_of_neg])
      (by norm_num [expPoly, expErr, Finset.sum_range_succ, Nat.factorial, abs_of_neg])
  have ha : Bnd (9 + 16 * Real.exp (-(3 / 10))) (9 + 16 * 0.7408182206817178) (9 + 16 * 0.7408182206817179) :=
    Bnd.add (Bnd.const 9) (he.smul_const (by norm_num))
  have hs : Bnd (√(9 + 16 * Real.exp (-(3 / 10)))) 4.566518535044775 4.566518535044776 :=
    Bnd.sqrt ha (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 := Bnd.add (Bnd.const (3 : ℝ)) hs
  have hd := Bnd.div (Bnd.const (2 : ℝ)) h3 (by norm_num) (by norm_num)
  rw [uLevel]
  exact hd.strict (by norm_num) (by norm_num)

/-- **Proposition 161 (one line, one operator).** With weights `w_t > 0` on the steps along each line: if `λ > 0`
solves the singlet meeting's secular equation `Σ_t w_t/(λ + w_t) = 1`, then `λ/4` is the Perron root of the weighted
walk (positive eigenvectors) and `u = 1/λ` is the root of `Σ_t 1/(1 + uw_t) − 4`; the singlet meeting's factor is
`det(I − uW(𝐉 − I)) = Π_t(1 + uw_t)[Σ_t 1/(1 + uw_t) − 4]`; for every weight `M` on the steps of the eighty states,
`det(λ − (𝒳 ⊗ 1)M(𝒳 ⊗ 1)) = det(λ − M)`; with weights per line, `det(I − uB_w) = Π_t(1 − u²w_t²)⁸ det(I − Â + D̂)`
on the sixteen vertices, and with five operators `Γ_t` of scalar squares the same Bass identity; with `w_h = e^{−S}`,
`Σ_t 1/(1 + uw_t) − 4 = (1 − 3u − 4u²e^{−S})/((1 + u)(1 + ue^{−S}))`, whose root `u_c(S)` is the eighty-state
walk's (`λ(S)/4` its Perron root), and `u_c(0.3) = 0.264322355220`.

The vertex form with a weight `W_e` on each step and any connection is `Comp.place_form_steps` (`Bass.lean`), and the
whole proposition is `prop_161` there. -/
theorem Completion.Comp.one_line_one_operator :
    (∀ (w : Fin 5 → ℝ), (∀ t, 0 < w t) → ∀ lam : ℝ, 0 < lam → ∑ t, w t / (lam + w t) = 1 →
      IsPerron (lineWalk w) (lam / 4) ∧ ∑ t, 1 / (1 + (1 / lam) * w t) - 4 = 0) ∧
    (∀ (u : ℝ) (w : Fin 5 → ℝ), (∀ t, 1 + u * w t ≠ 0) →
      (1 - u • (diagonal w * (Matrix.of fun i j : Fin 5 => if i = j then (0 : ℝ) else 1))).det =
        (∏ t, (1 + u * w t)) * (∑ t, 1 / (1 + u * w t) - 4)) ∧
    (∀ (K : Type) [Field K] [CharZero K] (M : Matrix State State K) (l : K),
      (l • (1 : Matrix State State K) - charX80 K * M * charX80 K).det = (l • (1 : Matrix State State K) - M).det) ∧
    (∀ (w : Fin 5 → ℂ) (u : ℂ), (∀ t, 1 - u ^ 2 * w t ^ 2 ≠ 0) →
      (1 - u • stepOp (fun t => w t • transitionMat t)).det =
        (∏ t, (1 - u ^ 2 * w t ^ 2) ^ 8) *
          (1 - ∑ t, (u / (1 - u ^ 2 * w t ^ 2) * w t) • transitionMat t +
            (∑ t, u ^ 2 / (1 - u ^ 2 * w t ^ 2) * w t ^ 2) • (1 : Matrix (Fin 16) (Fin 16) ℂ)).det) ∧
    (∀ (h : Fin 5) (S u : ℝ), 1 + u ≠ 0 → 1 + u * Real.exp (-S) ≠ 0 →
      ∑ t, 1 / (1 + u * levelW h S t) - 4 = (1 - 3 * u - 4 * u ^ 2 * Real.exp (-S)) / ((1 + u) * (1 + u * Real.exp (-S)))) ∧
    (∀ S : ℝ, 1 - 3 * uLevel S - 4 * uLevel S ^ 2 * Real.exp (-S) = 0) ∧
    (∀ (h : Fin 5) (S : ℝ), IsPerron (lastDirectionWalk h (-S)) (lamLevel S / 4)) ∧
    ((0.2643223552195 : ℝ) < uLevel (3 / 10) ∧ uLevel (3 / 10) < 0.2643223552205) :=
  ⟨fun w hw lam hl hs => ⟨lineWalk_isPerron w hw lam hl hs, singlet_root_of_secular w hw lam hl hs⟩,
    fun u w hw => singlet_weighted_factor u w hw, fun K _ _ M l => conj_spectrum M l,
    fun w u hc => bass_line_weights w u hc, fun h S u h1 h2 => level_factor h S u h1 h2, uLevel_root,
    fun h S => level_perron h S, uLevel_point_three⟩

open Filter Topology in
/-- **Proposition 162 (the bridge in both bases).** A phase on the steps turns the long-range zero at the mean of
the weight per step: on the eighty states the weight on the steps along one line has the rate `1/5`, and the phase
`e^{−iθ}` on them turns the zero by `θ/5` at first order; the available transitions weight `X = L(Ω) + [along h]` on the transitions turns
it at `1836/320` per step, the weight on the `60` transitions along `h` at
`60/320 = 3/16`, one transition at `1/320`; the ratio of the two angles is `1836`; per transition of the watched available transitions the rate
is `1836/296`; and the meetings' basis `𝒳 ⊗ 1` keeps the spectrum of every weighted step, so the zero and its rotation
are the same at the meetings. -/
theorem prop_162 (a₀ s₀ : State) (h₀ : Continues a₀ s₀) :
    (∀ t : Fin 5, piU ⬝ᵥ (hadPow ((1 / 4 : ℝ) • B ℝ) (alongX t) 1 *ᵥ 1) = 1 / 5) ∧
    (∀ t : Fin 5, ∃ ψ : ℂ → ℂ, ψ 0 = 1 ∧ (∀ᶠ s in 𝓝 0, charF ((1 / 4 : ℝ) • B ℝ) (alongX t) s (ψ s) = 0) ∧
      HasDerivAt (fun θ : ℝ => Complex.arg (ψ (-I * θ))) (-(1 / 5 : ℝ)) 0) ∧
    (∀ h : Fin 5, piU ⬝ᵥ (hadPow ((1 / 4 : ℝ) • B ℝ) (availableTransitionsLawX h (transitionX h)) 1 *ᵥ 1) = 1836 / 320) ∧
    (∀ h : Fin 5, piU ⬝ᵥ (hadPow ((1 / 4 : ℝ) • B ℝ) (availableTransitionsAlongX h) 1 *ᵥ 1) = 3 / 16) ∧
    piU ⬝ᵥ (hadPow ((1 / 4 : ℝ) • B ℝ) (oneTransitionX a₀ s₀) 1 *ᵥ 1) = 1 / 320 ∧
    (∀ h : Fin 5,
      (∃ ψ : ℂ → ℂ, ψ 0 = 1 ∧
        (∀ᶠ s in 𝓝 0, charF ((1 / 4 : ℝ) • B ℝ) (availableTransitionsLawX h (transitionX h)) s (ψ s) = 0) ∧
        HasDerivAt (fun θ : ℝ => Complex.arg (ψ (-I * θ))) (-(1836 / 320 : ℝ)) 0) ∧
      (∃ ψ : ℂ → ℂ, ψ 0 = 1 ∧ (∀ᶠ s in 𝓝 0, charF ((1 / 4 : ℝ) • B ℝ) (oneTransitionX a₀ s₀) s (ψ s) = 0) ∧
        HasDerivAt (fun θ : ℝ => Complex.arg (ψ (-I * θ))) (-(1 / 320 : ℝ)) 0) ∧
      (1836 / 320 : ℝ) / (1 / 320) = 1836) ∧
    (∀ h : Fin 5, HasDerivAt (fun s => Real.log (perronRoot (watchedS h) s)) (1836 / 296) 0) ∧
    (∀ (M : Matrix State State ℝ) (l : ℝ),
      (l • (1 : Matrix State State ℝ) - charX80 ℝ * M * charX80 ℝ).det = (l • (1 : Matrix State State ℝ) - M).det) :=
  ⟨one_line_rate, one_line_angle, fun h => availableTransitions_angle_rate h, availableTransitions_along_rate, one_transition_angle_rate a₀ s₀ h₀,
    fun h => proton_availableTransitions_ratio h a₀ s₀ h₀, fun h => (inventory_velocity h).2.1, fun M l => conj_spectrum M l⟩

/-- **Proposition 163 (mass in both pairings: where it sits and how much).** A unit rotation the held division moves
has the mass form `2`, a kept one `0` (for every division, of any size); the line's own clock is moved at `{t}` and
kept at `{t, n}`; with the phase
`e^{−iμ}` on every step `det(1 − ue^{−iμ}B) = D₊(ue^{−iμ})`, which vanishes at `u = e^{iμ}/4`, and on the closed disc
`|v| ≤ 1/4` `D₊(v)` vanishes only at `v = 1/4`.

Recognition: the rest energy `E = mc²` with `μ = mc²τ/ħ`; `W`, `Z` and the fermions take their masses by one rule,
the moved rotation. -/
theorem prop_163 :
    (∀ (n : ℕ) (D : Finset (Fin n)) (a b : Fin n), a ∈ D → b ∉ D →
      massForm D (unitTurn a b) (unitTurn a b) = 2) ∧
    (∀ (n : ℕ) (D : Finset (Fin n)) (a b : Fin n), (a ∈ D ↔ b ∈ D) →
      massForm D (unitTurn a b) (unitTurn a b) = 0) ∧
    (∀ h : Fin 5, Moved {h.succ} (Sum.inl h)) ∧ (∀ h : Fin 5, Kept {0, h.succ} (Sum.inl h)) ∧
    (∀ (μ : ℝ) (u : ℂ),
      (1 - (u * Complex.exp (-(μ : ℂ) * I)) • B ℂ).det =
        (1 - (u * Complex.exp (-(μ : ℂ) * I)) ^ 2) ^ 24 * (1 - u * Complex.exp (-(μ : ℂ) * I)) *
          (1 - 4 * (u * Complex.exp (-(μ : ℂ) * I))) *
          (1 - u * Complex.exp (-(μ : ℂ) * I) + 4 * (u * Complex.exp (-(μ : ℂ) * I)) ^ 2) ^ 10 *
          (1 + 3 * (u * Complex.exp (-(μ : ℂ) * I)) + 4 * (u * Complex.exp (-(μ : ℂ) * I)) ^ 2) ^ 5 ∧
      (1 - (Complex.exp ((μ : ℂ) * I) / 4 * Complex.exp (-(μ : ℂ) * I)) • B ℂ).det = 0) ∧
    (∀ v : ℂ, ‖v‖ ≤ 1 / 4 → ((1 - v ^ 2) ^ 24 * (1 - v) * (1 - 4 * v) * (1 - v + 4 * v ^ 2) ^ 10 *
      (1 + 3 * v + 4 * v ^ 2) ^ 5 = 0 ↔ v = 1 / 4)) :=
  ⟨fun _ D _ _ ha hb => massForm_unit_moved D ha hb, fun _ D _ _ h => massForm_unit_kept D h, clock_line_moved,
    by decide, fun μ u => by rw [← stepOp_transitionMat_eq]; exact uniform_phase_zero μ u, D_plus_disc⟩

/-- **Proposition 164 (a massive line is a null line of the six).** `det(t₀ + Σ_s t_sγ_s) = (t₀² − |t|²)²`; for every
real direction `n`, `ω` is an eigenvalue of `γ(n)` exactly when `ω² = |n|²`; a step that holds `h` and moves along
`j ≠ h`, `H = μγ_h + kγ_j`, has `H² = (μ² + k²)1` and the energy `ω` exactly when `ω² = μ² + k²`; in the chart,
`(Σ x_μΓ_μ)² = |x|²1`. Recognition: `E² = p² + m²`, a massive particle in four dimensions a massless one in six. -/
theorem prop_164 :
    (∀ (t₀ : ℂ) (t : Fin 5 → ℂ), (t₀ • (1 : Matrix Four Four ℂ) + ∑ s, t s • γ s).det = (t₀ ^ 2 - ∑ s, t s ^ 2) ^ 2) ∧
    (∀ (n : Fin 5 → ℝ) (ω : ℝ), (∃ v : Four → ℂ, v ≠ 0 ∧ γv n *ᵥ v = (ω : ℂ) • v) ↔ ω ^ 2 = ∑ s, n s ^ 2) ∧
    (∀ {h j : Fin 5}, h ≠ j → ∀ μ k ω : ℝ,
      ((μ : ℂ) • γ h + (k : ℂ) • γ j) * ((μ : ℂ) • γ h + (k : ℂ) • γ j) =
        ((μ ^ 2 + k ^ 2 : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) ∧
      ((∃ v : Four → ℂ, v ≠ 0 ∧ ((μ : ℂ) • γ h + (k : ℂ) • γ j) *ᵥ v = (ω : ℂ) • v) ↔ ω ^ 2 = μ ^ 2 + k ^ 2)) ∧
    (∀ (O : Matrix (Fin 5) (Fin 5) ℝ), O * Oᵀ = 1 → ∀ x : Fin 5 → ℂ,
      (∑ μ, x μ • γv (O μ)) * (∑ μ, x μ • γv (O μ)) = (∑ μ, x μ ^ 2) • (1 : Matrix Four Four ℂ)) :=
  ⟨det_cone, eigen_null_cone, fun hj μ k ω => step_energy hj μ k ω, chart_square⟩

/-- **Proposition 165 (the two components on the plane, and the chiral rotation of the mass).** The plane's rotation
`γ₀γ₁` squares to `−1`; a generator of the fifteen rotations is kept by the plane's division `{1, 2}` exactly when it
commutes with `γ₀γ₁` (the clock of `F`); `R(θ)R(−θ) = 1`; `R(θ)` takes `γ_h ↦ cos θ γ_h − sin θ γ_k`,
`γ_k ↦ cos θ γ_k + sin θ γ_h` and fixes the colour lines, so it takes `(m, m₅) ↦ (m cos θ + m₅ sin θ,
m₅ cos θ − m sin θ)` and keeps `p` and `m₀² = m² + m₅²`; `H² = (|p|² + m² + m₅²)1`. Recognition: Dirac's mass term
`ψ̄(m + iγ⁵m₅)ψ` and its axial rotation. -/
theorem prop_165 :
    JointCells.planeTurn * JointCells.planeTurn = -1 ∧
    (∀ x : Fin 5 ⊕ Fin 10, Kept {1, 2} x ↔ gen x * JointCells.planeTurn = JointCells.planeTurn * gen x) ∧
    (∀ θ : ℝ, chiralR θ * chiralR (-θ) = 1) ∧
    (∀ θ m m₅ p₂ p₃ p₄ : ℝ,
      chiralR θ * ((p₂ : ℂ) • γ 2 + (p₃ : ℂ) • γ 3 + (p₄ : ℂ) • γ 4 + (m : ℂ) • γ 0 + (m₅ : ℂ) • γ 1) *
          chiralR (-θ) =
        (p₂ : ℂ) • γ 2 + (p₃ : ℂ) • γ 3 + (p₄ : ℂ) • γ 4 +
          ((m * Real.cos θ + m₅ * Real.sin θ : ℝ) : ℂ) • γ 0 +
          ((m₅ * Real.cos θ - m * Real.sin θ : ℝ) : ℂ) • γ 1 ∧
        (m * Real.cos θ + m₅ * Real.sin θ) ^ 2 + (m₅ * Real.cos θ - m * Real.sin θ) ^ 2 = m ^ 2 + m₅ ^ 2 ∧
        ((p₂ : ℂ) • γ 2 + (p₃ : ℂ) • γ 3 + (p₄ : ℂ) • γ 4 + (m : ℂ) • γ 0 + (m₅ : ℂ) • γ 1) *
          ((p₂ : ℂ) • γ 2 + (p₃ : ℂ) • γ 3 + (p₄ : ℂ) • γ 4 + (m : ℂ) • γ 0 + (m₅ : ℂ) • γ 1) =
          ((p₂ ^ 2 + p₃ ^ 2 + p₄ ^ 2 + m ^ 2 + m₅ ^ 2 : ℝ) : ℂ) • (1 : Matrix Four Four ℂ)) :=
  ⟨JointCells.planeTurn_mul_self, JointCells.kept_F_iff, chiralR_inv, chiral_rotation⟩

/-- **Two sources through a simple zero:** with the residue `M = (ℓK_ζr)⁻¹ rℓ`, `YMX = (Yr)(ℓX)/(ℓK_ζr)`. -/
theorem Completion.Comp.two_sources {n 𝕜 : Type*} [Fintype n] [Field 𝕜] (r ℓ Y X : n → 𝕜) (c : 𝕜) :
    Y ⬝ᵥ ((c⁻¹ • vecMulVec r ℓ) *ᵥ X) = (Y ⬝ᵥ r) * (ℓ ⬝ᵥ X) / c := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_smul, Matrix.vecMul_vecMulVec, smul_smul, smul_dotProduct,
    smul_eq_mul]
  ring

open Filter Topology in
/-- **Proposition 166 (mass and strength, one meeting).** At the law's critical zero every state has four
continuations in and out, `B𝟏 = 4𝟏`, `𝟏ᵀB = 4𝟏ᵀ`, so `r = l = 𝟏/√80` with `lK_ur = −4`, the same at the singlet meeting
(`(𝒳 ⊗ 1)𝟏 = 4e_∅ ⊗ 𝟏`); the level `e^{−j}` on the steps along `h` has `lK_jr = 1/5` and moves the zero at
`du_c/dj = 1/20`; on the sixteen at the critical step `(1 + 4u²) − uA = (5 − A)/4`, and the residue
`(ζ − 5)𝒳 diag(1/(ζ − χ_U))𝒳 → 𝐉/16`, so the plane source `−1` on each of the ten symmetric states reads `−10/16 = −5/8`; for
every pencil the zero moves at `dζ/dj = −ℓK_jr/(ℓK_ζr)` and at a simple zero the residue is `rℓ/(ℓK_ζr)` (Eq. (37)),
so two sources through the zero carry `(ζ − ζ₀)YK⁻¹X → (Yr)(ℓX)/(ℓK_ζr)`; the quaternionic structure on one system exchanges
`P` and `E` and keeps `L`.
Recognition (with Prop. 57): one denominator for the zero's shift (the mass) and the residue (the strength). -/
theorem prop_166 :
    B ℚ *ᵥ (fun _ => (1 : ℚ)) = (4 : ℚ) • (fun _ => 1) ∧ (fun _ => (1 : ℚ)) ᵥ* B ℚ = (4 : ℚ) • (fun _ => 1) ∧
    -((fun _ => (1 : ℚ)) ⬝ᵥ (B ℚ *ᵥ fun _ => 1)) / 80 = -4 ∧
    charX80 ℚ *ᵥ (fun _ => 1) = (fun p => if p.1 = 0 then 4 else 0) ∧
    -((fun p : State => if p.1 = 0 then (1 : ℚ) else 0) ⬝ᵥ
        (meetBlocks ℚ (lastDirectionK ℚ) *ᵥ fun p => if p.1 = 0 then 1 else 0)) / 5 = -4 ∧
    (∀ h : Fin 5, (1 / 4 : ℝ) * ((1 : State → ℝ) ⬝ᵥ (lastDirectionSteps h *ᵥ 1)) / 80 = 1 / 5) ∧
    (∀ h : Fin 5, ∃ ζ : ℝ → ℝ, ζ 0 = 1 / 4 ∧ (∀ᶠ J in 𝓝 0, lawSrc (-(1 / 4 : ℝ) • lastDirectionSteps h) J (ζ J) = 0) ∧
      HasDerivAt ζ (1 / 20) 0) ∧
    (1 + 4 * (1 / 4 : ℝ) ^ 2) • (1 : Matrix (Fin 16) (Fin 16) ℝ) - (1 / 4 : ℝ) • A ℝ =
      (1 / 4 : ℝ) • ((5 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) - A ℝ) ∧
    Tendsto (fun ζ : ℝ => (ζ - 5) • (charX ℝ * diagonal (fun U => 1 / (ζ - (charValue U : ℝ))) * charX ℝ))
      (𝓝[≠] 5) (𝓝 (Matrix.of fun _ _ => 1 / 16)) ∧
    (∀ y : Fin 16, ((Matrix.of fun _ _ => (1 / 16 : ℝ)) *ᵥ
      (fun x => if (disagreeSet x).card = 2 then (-1 : ℝ) else 0)) y = -5 / 8) ∧
    (∀ {n 𝕜 : Type} [Fintype n] [DecidableEq n] [Field 𝕜] (S₀ Sζ Sa : Matrix n n 𝕜) (ℓ v : n → 𝕜) (ζ J : 𝕜),
      ℓ ᵥ* S₀ = 0 → (S₀ + ζ • Sζ + J • Sa) *ᵥ v = 0 → ζ * (ℓ ⬝ᵥ (Sζ *ᵥ v)) = -(J * (ℓ ⬝ᵥ (Sa *ᵥ v)))) ∧
    (∀ {n 𝕜 : Type} [Fintype n] [DecidableEq n] [Field 𝕜] (S₀ Sζ M N : Matrix n n 𝕜) (r ℓ : n → 𝕜),
      r ≠ 0 → ℓ ≠ 0 → (∀ v, S₀ *ᵥ v = 0 → ∃ c : 𝕜, v = c • r) → (∀ w, w ᵥ* S₀ = 0 → ∃ c : 𝕜, w = c • ℓ) →
      ℓ ᵥ* S₀ = 0 → S₀ * M = 0 → M * S₀ = 0 → S₀ * N + Sζ * M = 1 →
      ℓ ⬝ᵥ (Sζ *ᵥ r) ≠ 0 ∧ M = (ℓ ⬝ᵥ (Sζ *ᵥ r))⁻¹ • vecMulVec r ℓ) ∧
    (∀ {n 𝕜 : Type} [Fintype n] [Field 𝕜] (r ℓ Y X : n → 𝕜) (c : 𝕜),
      Y ⬝ᵥ ((c⁻¹ • vecMulVec r ℓ) *ᵥ X) = (Y ⬝ᵥ r) * (ℓ ⬝ᵥ X) / c) ∧
    (partnerTwo swap = Eop ∧ partnerTwo Eop = swap ∧ partnerTwo L = L) := by
  refine ⟨uniform_null.1, uniform_null.2, lKr_u, charX80_ones, lKr_u_meeting, level_source, level_shift,
    by rw [← law_adj16_eq]; exact critical_sixteen, residue_sixteen, fun y => ?_,
    fun S₀ Sζ Sa ℓ v ζ J hℓ hv => zero_shift S₀ Sζ Sa ℓ v ζ J hℓ hv,
    fun S₀ Sζ M N r ℓ hr hℓ hkR hkL hℓS h1 h2 h3 => residue_simple_zero S₀ Sζ M N r ℓ hr hℓ hkR hkL hℓS h1 h2 h3,
    fun r ℓ Y X c => Completion.Comp.two_sources r ℓ Y X c, ⟨partnerTwo_swap, partnerTwo_Eop, partnerTwo_L⟩⟩
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, mul_ite, mul_neg, mul_one, mul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have h10 : (Finset.univ.filter fun x : Fin 16 => (disagreeSet x).card = 2).card = 10 := Num.N2_eq
  rw [h10]
  norm_num

open Filter Topology Asymptotics in
/-- **Proposition 167 (a bound state of several world lines on the line side: their zero shifts add).** On the line side
(`G = I`) the law on the direct sum factors over the lines, `det(I − D ⊗ M) = det(I − S₁M)det(I − S₂M)` for every
square `M`; a level `e^{−S}` on the steps along `h` has `δ(S) = −log((3 + (9 + 16e^{−S})^{1/2})/8) =
S/5 − (6/125)S² + O(S³)`. The product walk and the eighty states are in `prop_167` (`Whole.lean`). -/
theorem Completion.Comp.line_side_level :
    (∀ {n : Type} [Fintype n] [DecidableEq n] (S₁ S₂ : ℝ) (M : Matrix n n ℝ),
      (1 - levelOp S₁ S₂ 0 ⊗ₖ M).det = (1 - S₁ • M).det * (1 - S₂ • M).det) ∧
    (∀ S : ℝ, deltaLevel S = -Real.log ((3 + Real.sqrt (9 + 16 * Real.exp (-S))) / 8)) ∧
    (fun S : ℝ => deltaLevel S - (S / 5 - 6 / 125 * S ^ 2)) =O[𝓝 0] (fun S : ℝ => S ^ 3) :=
  ⟨fun S₁ S₂ M => line_side_det S₁ S₂ M, level_value, delta_expansion⟩

/-- **Proposition 168 (a bound state of several world lines on the meeting side: their levels add inside one shift).** At the
singlet a step of either system is the same step, `(γ_t ⊗ 1)Ω = (1 ⊗ γ_t)Ω`, and `γ_t ⊗ γ_t` keeps every meeting,
`(γ_t ⊗ γ_t)e_S = ±e_S`; on the meeting side (`G = 𝟏𝟏ᵀ`)
`det(I − (𝟏𝟏ᵀD) ⊗ M) = det(I − (S₁ + S₂)M)`, and the composite shift is `δ(S₁ + S₂)` while the line side's is
`δ(S₁) + δ(S₂)`. -/
theorem prop_168 :
    (∀ c : Fin 5, (γ c ⊗ₖ 1) *ᵥ Ω = (1 ⊗ₖ γ c) *ᵥ Ω) ∧
    (∀ (u : Fin 5) (k : Fin 16), (γ u ⊗ₖ γ u) *ᵥ rel k = (if u ∈ disagreeSet k then -1 else 1 : ℂ) • rel k) ∧
    (∀ {n : Type} [Fintype n] [DecidableEq n] (S₁ S₂ : ℝ), S₂ ≠ 0 → S₁ + S₂ ≠ 0 → ∀ M : Matrix n n ℝ,
      (1 - levelOp S₁ S₂ 1 ⊗ₖ M).det = (1 - (S₁ + S₂) • M).det) ∧
    (∀ S₁ S₂ : ℝ, 0 ≤ S₁ → 0 ≤ S₂ → compositeDelta S₁ S₂ 0 = deltaLevel S₁ + deltaLevel S₂ ∧
      compositeDelta S₁ S₂ 1 = deltaLevel (S₁ + S₂)) :=
  ⟨meson_either_end, GroupsContinuumLaw.coupling_R1.1, fun S₁ S₂ hS hT M => meeting_side_det S₁ S₂ hS hT M,
    fun S₁ S₂ h₁ h₂ => composite_ends S₁ S₂ h₁ h₂⟩

open Filter Topology Asymptotics in
/-- **Proposition 169 (the two limits agree at first order and differ at second by the cross covariance of the
lines' transitions).** The last-step direction's walk `(𝐉 − I)/4` has `Cov(X^i₀, X^j_k) = (1/5)(−1/4)^k(δ_ij − 1/5)` and the long-run
covariance `σ_ij = (3/25)(δ_ij − 1/5)`: `12/125` on one line, `−3/125` across two; at first order both limits are
`(S₁ + S₂)/5`; at second order the composition carries `−(12/125)cS₁S₂` (Prop. 189), the line side `c = 0` and the
meeting side `c = 1`.

The second-order difference `δ_L − δ_M = σ_hhS₁S₂ + O(‖S‖³)` is in `prop_169` (`Remainders.lean`). -/
theorem Completion.Comp.two_limits :
    (∀ (i j : Fin 5) (k : ℕ), (1 / 5 : ℚ) * (lastDirectionStep ^ k) i j - (1 / 5) ^ 2 =
      (1 / 5) * (-1 / 4) ^ k * ((if i = j then 1 else 0) - 1 / 5)) ∧
    (∀ i j : Fin 5, HasSum (fun k : ℕ => (if k = 0 then (1 : ℝ) else 2) *
        ((1 / 5) * (-1 / 4) ^ k * ((if i = j then 1 else 0) - 1 / 5)))
      ((3 / 25) * ((if i = j then 1 else 0) - 1 / 5))) ∧
    ((3 / 25 : ℝ) * (1 - 1 / 5) = 12 / 125 ∧ (3 / 25 : ℝ) * (0 - 1 / 5) = -3 / 125) ∧
    ((fun p : ℝ × ℝ => deltaLevel p.1 + deltaLevel p.2 - (p.1 + p.2) / 5) =O[𝓝 0]
        (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) ∧
      (fun p : ℝ × ℝ => deltaLevel (p.1 + p.2) - (p.1 + p.2) / 5) =O[𝓝 0]
        (fun p : ℝ × ℝ => (p.1 + p.2) ^ 2)) ∧
    (∀ S₁ S₂ c : ℝ, 0 ≤ (S₁ - S₂) ^ 2 + 4 * c * S₁ * S₂ →
      (eigenPlus S₁ S₂ c / 5 - 6 / 125 * eigenPlus S₁ S₂ c ^ 2) +
          (eigenMinus S₁ S₂ c / 5 - 6 / 125 * eigenMinus S₁ S₂ c ^ 2) =
        (S₁ + S₂) / 5 - 6 / 125 * (S₁ ^ 2 + S₂ ^ 2) - 12 / 125 * c * S₁ * S₂) :=
  ⟨lastDirection_cross_cov, cross_spread, cross_values, two_limits_first_order,
    fun S₁ S₂ c hd => second_order_composite S₁ S₂ c hd⟩

/-- **Proposition 187 (the neutrino mass sum beside the newest cosmic bound).** With `m₁ = 0`, the splittings
`m₂² = 7.4178·10⁻⁵ eV²` and `m₃² = 2.5199·10⁻³ eV²` stand at `+0.38` and `+0.40` standard deviations of JUNO 2026; the least sum the
measured splittings allow is `(7.388·10⁻⁵)^{1/2} + (2.509·10⁻³)^{1/2} = 0.05869(26) eV`; the bound `0.081 eV` stands
above `Σm_ν`, and the bound `0.055 eV` lies `0.0037 eV` below the least sum. -/
theorem prop_187 :
    ((7.41775e-5 : ℝ) < Num.mnu2 ^ 2 ∧ Num.mnu2 ^ 2 < 7.41785e-5) ∧
    ((2.51985e-3 : ℝ) < Num.mnu3 ^ 2 ∧ Num.mnu3 ^ 2 < 2.51995e-3) ∧
    ((0.375 : ℝ) < (Num.mnu2 ^ 2 - 7.388e-5) / 0.078e-5 ∧ (Num.mnu2 ^ 2 - 7.388e-5) / 0.078e-5 < 0.385) ∧
    ((0.395 : ℝ) < (Num.mnu3 ^ 2 - 2.509e-3) / 0.027e-3 ∧ (Num.mnu3 ^ 2 - 2.509e-3) / 0.027e-3 < 0.405) ∧
    qLeastSum = √7.388e-5 + √2.509e-3 ∧ ((0.058685 : ℝ) < qLeastSum ∧ qLeastSum < 0.058695) ∧
    ((0.000255 : ℝ) < qLeastWidth ∧ qLeastWidth < 0.000265) ∧
    Num.mnu2 + Num.mnu3 < 0.081 ∧ qBelowLeast = qLeastSum - 0.055 ∧
    ((0.00365 : ℝ) < qBelowLeast ∧ qBelowLeast < 0.00375) := by
  rw [Num.mnu2_eq_q, Num.mnu3_eq_q]
  have h := neutrino_sum_beside_bounds
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, ?_,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩
  have := h.2.2.2.2.2.2.2.1
  rw [qSumNu] at this
  exact this

/-- **Equation (37).** For a pencil `S₀ + ζS_ζ + JS_a` with `ℓS₀ = 0`, a null vector `v` gives
`ζ(ℓS_ζv) = −J(ℓS_av)`: the zero moves at `dζ/dj = −ℓK_jr/(ℓK_ζr)`; and at a simple zero the residue is
`rℓ/(ℓS_ζr)` (Prop. 57, with the law's own zero shift `du_c/dj = 1/20` for the level on `h`, Prop. 166). -/
theorem eq_37 :
    (∀ {n 𝕜 : Type} [Fintype n] [DecidableEq n] [Field 𝕜] (S₀ Sζ Sa : Matrix n n 𝕜) (ℓ v : n → 𝕜) (ζ J : 𝕜),
      ℓ ᵥ* S₀ = 0 → (S₀ + ζ • Sζ + J • Sa) *ᵥ v = 0 → ζ * (ℓ ⬝ᵥ (Sζ *ᵥ v)) = -(J * (ℓ ⬝ᵥ (Sa *ᵥ v)))) ∧
    (∀ {n 𝕜 : Type} [Fintype n] [DecidableEq n] [Field 𝕜] (S₀ Sζ M N : Matrix n n 𝕜) (r ℓ : n → 𝕜),
      r ≠ 0 → ℓ ≠ 0 → (∀ v, S₀ *ᵥ v = 0 → ∃ c : 𝕜, v = c • r) → (∀ w, w ᵥ* S₀ = 0 → ∃ c : 𝕜, w = c • ℓ) →
      ℓ ᵥ* S₀ = 0 → S₀ * M = 0 → M * S₀ = 0 → S₀ * N + Sζ * M = 1 →
      ℓ ⬝ᵥ (Sζ *ᵥ r) ≠ 0 ∧ M = (ℓ ⬝ᵥ (Sζ *ᵥ r))⁻¹ • vecMulVec r ℓ) :=
  ⟨fun S₀ Sζ Sa ℓ v ζ J hℓ hv => zero_shift S₀ Sζ Sa ℓ v ζ J hℓ hv,
    fun S₀ Sζ M N r ℓ hr hℓ hkR hkL hℓS h1 h2 h3 => residue_simple_zero S₀ Sζ M N r ℓ hr hℓ hkR hkL hℓS h1 h2 h3⟩

/-- **Equation (38), the pencil.** `K_X(ζ) = [[ζC_L, −A], [−B, ζC_R]]` has `det K_X(ζ) = ζ²C_LC_R − AB`, so its zeros
are `ζ² = Ω_X² = AB/(C_LC_R)`; a change of either end's description multiplies `AB` and `C_LC_R` by one factor and
keeps `Ω_X²`; `m_X/m_e = Ω_X/Ω_e`. The rest pencil of the law for an integral mark `X` on the arcs,
`K_X(z) = z − ν(X)β` (`β` the plane's clock), has its zero at `ν(X) = Σ_arcs X/320`; among the nonnegative integral
marks the least positive `ν` is `1/320`, attained exactly by one arc carrying one unit (the electron).

The entries `A, B, C_L, C_R` of the pencil of each mass other than the integral counts, read from the law, are the
statement that completes Eq. (38). -/
theorem eq_38 :
    (∀ ζ CL CR A B : ℝ, (pencil ζ CL CR A B).det = ζ ^ 2 * (CL * CR) - A * B) ∧
    (∀ ζ CL CR A B : ℝ, CL * CR ≠ 0 → ((pencil ζ CL CR A B).det = 0 ↔ ζ ^ 2 = A * B / (CL * CR))) ∧
    (∀ CL CR A B c : ℝ, c ≠ 0 → CL * CR ≠ 0 → (c * (A * B)) / (c * (CL * CR)) = A * B / (CL * CR)) ∧
    (∀ ΩX Ωe : ℝ, 0 < ΩX → 0 < Ωe → ΩX / Ωe = √(ΩX ^ 2 / Ωe ^ 2)) ∧
    (∀ ν z : ℂ, (GroupsContinuumLaw.restK ν z).det = 0 ↔ z = ν ∨ z = -ν) ∧
    (∀ X : State → State → ℕ, 0 < GroupsContinuumLaw.natTotal X →
      (1 : ℚ) / 320 ≤ GroupsContinuumLaw.rate (fun p q => (X p q : ℚ)) ∧
      (GroupsContinuumLaw.rate (fun p q => (X p q : ℚ)) = 1 / 320 ↔
        ∃ e ∈ Comparison.arcs, X e.2 e.1 = 1 ∧ ∀ f ∈ Comparison.arcs, f ≠ e → X f.2 f.1 = 0)) :=
  ⟨pencil_det, pencil_zero, pencil_rescale, pencil_ratio, GroupsContinuumLaw.rest_poles_iff,
    fun X hX => ⟨(GroupsContinuumLaw.least_positive_pole X hX).2.1, (GroupsContinuumLaw.least_positive_pole X hX).2.2⟩⟩

end Comparison.System
