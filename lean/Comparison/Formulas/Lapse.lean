import Mathlib

/-!
# The lapse (Prop. S166a; formula (20))

Proposition S166a. A lapse `N` rescales the duration of a step, so it enters
every kernel through `E/N` alone: `K(E, N) = K(E/N, 1) = k(E/N)`, with values in any real normed space
(the matrices of a block, for instance).

* `lapse_partials`: **`∂_N K = −(E/N²) k′(E/N)`, `∂_E K = (1/N) k′(E/N)`, hence `N ∂_N K = −E ∂_E K`.**
* `lapse_zero_scales`: `E` is a zero of `K(·, N)` exactly when `E = N E₁` with `E₁` a zero of
  `K(·, 1)`: **`E_X(N) = N E_X(1)`**; `lapse_rate`: `dE_X/dN = E_X(1)`.
* `lapse_displacement`: at a simple zero (`λ(k′(E)) ≠ 0` for the pairing `λ = ℓ†(·)r` of Prop. S57,
  any real-linear map), **the displacement `−λ(∂_N K)/λ(∂_E K)` at `N = 1` is `E`**: the lapse couples
  to the rest energy, the same share for every line.
-/

namespace Comparison.Formulas

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `d/dN (E/N) = −E/N²`. -/
theorem hasDerivAt_div_lapse (E N : ℝ) (hN : N ≠ 0) :
    HasDerivAt (fun N' : ℝ => E / N') (-(E / N ^ 2)) N := by
  have h := (hasDerivAt_inv hN).const_mul E
  have e : (fun N' : ℝ => E / N') = fun N' => E * N'⁻¹ := by
    funext N'
    rw [div_eq_mul_inv]
  rw [e]
  convert h using 1
  field_simp

/-- **The lapse's two partial derivatives:** for `K(E, N) = k(E/N)`,
`∂_N K = −(E/N²) k′(E/N)`, `∂_E K = (1/N) k′(E/N)`, and `N ∂_N K = −E ∂_E K`. -/
theorem lapse_partials (k : ℝ → F) (k' : F) (E N : ℝ) (hN : N ≠ 0)
    (hk : HasDerivAt k k' (E / N)) :
    HasDerivAt (fun N' => k (E / N')) (-(E / N ^ 2) • k') N ∧
      HasDerivAt (fun E' => k (E' / N)) ((1 / N) • k') E ∧
      N • (-(E / N ^ 2) • k') = -(E • ((1 / N) • k')) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hk.scomp N (hasDerivAt_div_lapse E N hN)
  · have h1 : HasDerivAt (fun E' : ℝ => E' / N) (1 / N) E := by
      simpa using (hasDerivAt_id E).div_const N
    exact hk.scomp E h1
  · rw [smul_smul, smul_smul, ← neg_smul]
    congr 1
    field_simp

/-- **The zeros move in proportion:** `E` is a zero of `K(·, N)` exactly when `E = N E₁` for a zero
`E₁` of `K(·, 1)`; any property of the kernel (singular, a given null vector) is read at `E/N`. -/
theorem lapse_zero_scales {M : Type*} (k : ℝ → M) (P : M → Prop) (N : ℝ) (hN : N ≠ 0) (E : ℝ) :
    P (k (E / N)) ↔ ∃ E₁, P (k (E₁ / 1)) ∧ E = N * E₁ := by
  constructor
  · intro h
    refine ⟨E / N, by rwa [div_one], ?_⟩
    field_simp
  · rintro ⟨E₁, h, rfl⟩
    rwa [mul_div_cancel_left₀ _ hN, ← div_one E₁]

/-- `E_X(N) = N E_X(1)` gives `dE_X/dN = E_X(1)`. -/
theorem lapse_rate (E₁ : ℝ) : HasDerivAt (fun N : ℝ => N * E₁) E₁ 1 := by
  simpa using (hasDerivAt_id (1 : ℝ)).mul_const E₁

/-- **The lapse couples to the rest energy:** at a simple zero, the displacement of the zero by the
lapse, `−λ(∂_N K)/λ(∂_E K)` at `N = 1` (Prop. S57 with the source `N`), is `E` itself. -/
theorem lapse_displacement (k : ℝ → F) (k' : F) (E : ℝ) (hk : HasDerivAt k k' E)
    (pair : F →ₗ[ℝ] ℂ) (hs : pair k' ≠ 0) :
    HasDerivAt (fun N' : ℝ => k (E / N')) (-E • k') 1 ∧
      HasDerivAt (fun E' : ℝ => k (E' / 1)) k' E ∧
      -(pair (-E • k')) / pair k' = E := by
  have hk1 : HasDerivAt k k' (E / 1) := by rwa [div_one]
  obtain ⟨h1, h2, -⟩ := lapse_partials k k' E 1 one_ne_zero hk1
  refine ⟨?_, ?_, ?_⟩
  · simpa using h1
  · simpa using h2
  · rw [map_smul, Complex.real_smul]
    field_simp
    push_cast
    ring

end Comparison.Formulas
