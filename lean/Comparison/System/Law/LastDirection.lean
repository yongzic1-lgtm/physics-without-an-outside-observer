import Comparison.System.Postulates
import Comparison.Existence.LastDirectionSplit
import Comparison.WholePicture.Curvature
import Comparison.System.Law.LastDirectionJet

/-!
# The proof system, the law: Proposition 61 and equation (29), the ten rotations split at the last-step direction

`prop_61`: the split of the ten rotations at the last-step direction with its three
brackets and its directness, the curvature of `𝒜 = ¼ω^{ab}γ_aγ_b + (1/2ℓ)e^aγ_hγ_a` from its first jet, the trace
of five lines, the trace `tr(γ_h𝓕∧𝓕)` with the form indices and its MacDowell–Mansouri expansion, `ε_{habcd} =
(−1)^hε_{abcd}` on the four directions that move the last-step direction, and `Λ = 3/ℓ²` (`Law/LastDirectionJet.lean`,
`Existence/LastDirectionSplit.lean`, `WholePicture/Curvature.lean`). `eq_29`: equation (29) in the pairing of curvature
two-forms on the four directions, with the form indices kept; the identification of that pairing with
`lastDirectionWedge`, `(−1)^h·4` times the wedge of the curvature module, gives (29) in the orthonormal frame and
completes Eq. (29).
-/

open Matrix Complex Comparison Finset

namespace Comparison.System

/-- **Proposition 61, the ten rotations split at the last-step direction.** The ten rotations `γ_aγ_b` are the six `a, b ≠ h` and the
four `γ_hγ_a`; the six close, `[Σ Xγγ, Σ Yγγ] = 4Σ(XY − YX)γγ`, they move the four into the four,
`[Σ Xγγ, Σ yγ_hγ] = 4Σ(Xy)γ_hγ`, and `[ℝ⁴, ℝ⁴] ⊆ so(4)`, `[Σ xγ_hγ, Σ yγ_hγ] = −Σ(x∧y)γγ`; the sum is direct.
With `𝒜_μ = ¼ω_μ^{ab}γ_aγ_b + (1/2ℓ)e_μ^aγ_hγ_a` and its first jet, `𝓕_μν = ∂_μ𝒜_ν − ∂_ν𝒜_μ + [𝒜_μ, 𝒜_ν]` is
`¼𝓕^{ab}γ_aγ_b + ½𝓕^{ah}γ_hγ_a` with `𝓕^{ab} = R^{ab} − e^a∧e^b/ℓ²` and `𝓕^{ah} = T^a/ℓ`;
`tr(γ_aγ_bγ_cγ_dγ_e) = 4ε_{abcde}`; with the form indices, `ε^{μνρσ}tr(γ_h𝓕_μν𝓕_ρσ) = ¼ε_{habcd}𝓕^{ab}∧𝓕^{cd}`
and `(R − E/ℓ²)∧(R − E/ℓ²) = R∧R − (2/ℓ²)R∧E + (1/ℓ⁴)E∧E`, where on the four directions that move the last-step direction
`ε_{habcd} = (−1)^hε_{abcd}` (so `c = (−1)^h/4 ≠ 0`); the ratio of the last two coefficients gives `Λ = 3/ℓ²`.
Recognition: the Einstein–Cartan equations in the form of MacDowell and Mansouri; `Λ` the cosmological constant. -/
theorem prop_61 :
    ((Finset.univ.filter fun p : Fin 5 × Fin 5 => p.1 < p.2).card = 10 ∧
      (Finset.univ.filter fun p : Fin 5 × Fin 5 => p.1 < p.2 ∧ p.1 ≠ 0 ∧ p.2 ≠ 0).card = 6 ∧
      (Finset.univ.filter fun p : Fin 5 × Fin 5 => p.1 < p.2 ∧ (p.1 = 0 ∨ p.2 = 0)).card = 4) ∧
    (∀ (h : Fin 5) (X Y : Fin 5 → Fin 5 → ℂ), (∀ a b, Y b a = -Y a b) →
      Law.six (univ.erase h) X * Law.six (univ.erase h) Y -
          Law.six (univ.erase h) Y * Law.six (univ.erase h) X =
        (4 : ℂ) • Law.six (univ.erase h)
          (fun a b => ∑ c ∈ univ.erase h, (X a c * Y c b - Y a c * X c b))) ∧
    (∀ (h : Fin 5) (X : Fin 5 → Fin 5 → ℂ), (∀ a b, X b a = -X a b) → ∀ y : Fin 5 → ℂ,
      Law.six (univ.erase h) X * Law.four h (univ.erase h) y -
          Law.four h (univ.erase h) y * Law.six (univ.erase h) X =
        (4 : ℂ) • Law.four h (univ.erase h) (fun a => ∑ b ∈ univ.erase h, X a b * y b)) ∧
    (∀ (h : Fin 5) (x y : Fin 5 → ℂ),
      Law.four h (univ.erase h) x * Law.four h (univ.erase h) y -
          Law.four h (univ.erase h) y * Law.four h (univ.erase h) x =
        -Law.six (univ.erase h) (fun a b => x a * y b - y a * x b)) ∧
    (∀ (h : Fin 5) (X : Fin 5 → Fin 5 → ℂ) (y : Fin 5 → ℂ),
      Law.six (univ.erase h) X = Law.four h (univ.erase h) y →
        Law.four h (univ.erase h) y = 0 ∧ Law.six (univ.erase h) X = 0) ∧
    (∀ (h : Fin 5) (ℓ : ℂ), ℓ ≠ 0 → ∀ (ωμ ων dωμν dωνμ : Fin 5 → Fin 5 → ℂ) (eμ eν deμν deνμ : Fin 5 → ℂ),
      (∀ a b, ωμ b a = -ωμ a b) → (∀ a b, ων b a = -ων a b) →
      Law.lastDirectionConn h ℓ dωμν deμν - Law.lastDirectionConn h ℓ dωνμ deνμ +
          (Law.lastDirectionConn h ℓ ωμ eμ * Law.lastDirectionConn h ℓ ων eν -
            Law.lastDirectionConn h ℓ ων eν * Law.lastDirectionConn h ℓ ωμ eμ) =
        lastDirectionCurv h (fun a b =>
            dωμν a b - dωνμ a b + ∑ c ∈ univ.erase h, (ωμ a c * ων c b - ων a c * ωμ c b) -
              (1 / ℓ ^ 2) * (eμ a * eν b - eν a * eμ b))
          (fun a => (1 / ℓ) * (deμν a - deνμ a +
            (∑ b ∈ univ.erase h, ωμ a b * eν b - ∑ b ∈ univ.erase h, ων a b * eμ b)))) ∧
    (∀ a b c d e : Fin 5, (γ a * γ b * γ c * γ d * γ e).trace = 4 * (lc5 a b c d e : ℂ)) ∧
    (∀ (h : Fin 5) (a b c d : Fin 4),
      lc5 h (h.succAbove a) (h.succAbove b) (h.succAbove c) (h.succAbove d) =
        (-1) ^ (h : ℕ) * WholePicture.eps4 a b c d) ∧
    (∀ (h : Fin 5) (F : Fin 4 → Fin 4 → Fin 5 → Fin 5 → ℂ) (T : Fin 4 → Fin 4 → Fin 5 → ℂ),
      ∑ μ, ∑ ν, ∑ ρ, ∑ σ, (WholePicture.eps4 μ ν ρ σ : ℂ) *
          (γ h * lastDirectionCurv h (F μ ν) (T μ ν) * lastDirectionCurv h (F ρ σ) (T ρ σ)).trace =
        (1 / 4 : ℂ) * Law.lastDirectionWedge h F F) ∧
    (∀ (h : Fin 5) (R E : Fin 4 → Fin 4 → Fin 5 → Fin 5 → ℂ) (ℓ : ℂ),
      Law.lastDirectionWedge h (fun μ ν a b => R μ ν a b - E μ ν a b / ℓ ^ 2)
          (fun μ ν a b => R μ ν a b - E μ ν a b / ℓ ^ 2) =
        Law.lastDirectionWedge h R R - 2 / ℓ ^ 2 * Law.lastDirectionWedge h R E + 1 / ℓ ^ 4 * Law.lastDirectionWedge h E E) ∧
    (∀ ℓ Λ : ℝ, ℓ ≠ 0 → ((1 / ℓ ^ 4) / (-(2 / ℓ ^ 2)) = -(Λ / 6) ↔ Λ = 3 / ℓ ^ 2)) :=
  ⟨ten_split, fun h X Y hY => Law.bracket_six_six _ X Y hY,
    fun h X hX y => Law.bracket_six_four h X hX y, fun h x y => Law.bracket_four_four h x y,
    fun h X y hXy => Law.split_direct h X y hXy,
    fun h ℓ hℓ ωμ ων dωμν dωνμ eμ eν deμν deνμ hμ hν =>
      Law.curvature_jet_lastDirectionCurv h ℓ hℓ ωμ ων dωμν dωνμ eμ eν deμν deνμ hμ hν,
    trace_five, Law.lc5_restrict, Law.trace_four_form, Law.lastDirectionWedge_mm, lambda_from_ratio⟩

/-- **Equation (29), the curvature at the last-step direction** (as proved): `tr(γ_h𝓕∧𝓕) − tr(γ_hR∧R) = −(4/ℓ²)(R − 6/ℓ²)` in the
pairing of curvature two-forms with the form indices kept, and `Λ = 3/ℓ²`. -/
theorem eq_29 (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (hR : ∀ a b e f, R a b f e = -R a b e f)
    (ℓ : ℝ) (hℓ : ℓ ≠ 0) :
    WholePicture.wedge (fun p q => WholePicture.onPairs R p q - WholePicture.frameP p q / ℓ ^ 2)
          (fun p q => WholePicture.onPairs R p q - WholePicture.frameP p q / ℓ ^ 2) -
        WholePicture.wedge (WholePicture.onPairs R) (WholePicture.onPairs R) =
      -(4 / ℓ ^ 2) * (WholePicture.scalarR R - 6 / ℓ ^ 2) ∧
    ((24 / ℓ ^ 4 = (4 / ℓ ^ 2) * (2 * (3 / ℓ ^ 2)))) :=
  ⟨WholePicture.curvature_identity R hR ℓ, (WholePicture.lambda_three ℓ hℓ (3 / ℓ ^ 2)).2 rfl⟩

end Comparison.System
