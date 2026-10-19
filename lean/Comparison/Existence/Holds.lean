module

public import Comparison.Elements.Turns
public import Comparison.Existence.Coin

/-!
# Book VI. What a line holds; the coin from relabelling (Propositions 27 and 28)

P1's real six in the basis
`f₀ = J` (the singlet) and `f_{t+1} = i γ_t J` (`sixP1`); a rotation `W` of one system acts on both systems of
a two-spinor state by `M ↦ W M Wᵀ`.

* `line_on_six`: `γ_h ⊗ γ_h` is `+1` on the singlet and on `f_h`, `−1` on the four other lines: the
  division `θ_{T_h}` (the four lines other than `h` divided), which is the division `{h, n}`.
* `plane_on_six`: `γ_hγ_k ⊗ γ_hγ_k` is `−1` exactly on `f_h` and `f_k`: the division `{h, k}`.
* `one_of_each`: the divided sets `{}`, `{h, n}`, `{h, k}` and their counterparts `{n}`, `{h}`, `{n, h, k}`
  divide `0, 4, 2, 5, 1, 3` lines with the singlet undivided: each of Proposition 22's six once.
* `commutant_perm`: a matrix that no relabelling of the five directions changes is `a·1 + b·𝟙𝟙ᵀ`
  (Proposition 28's first step).
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex Kronecker

/-- **A line held on the six:** `γ_h (f_c) γ_hᵀ = +f_c` for the singlet and `f_h`, `−f_c` for the four
other lines. -/
theorem line_on_six (h : Fin 5) (c : Fin 6) :
    γ h * sixP1 c * (γ h)ᵀ = (if c = 0 ∨ c = h.succ then 1 else -1 : ℂ) • sixP1 c := by
  rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨u, rfl⟩
  · rw [sixP1_zero, Matrix.mul_assoc, J_mul_γ_transpose, ← Matrix.mul_assoc, γ_mul_self,
      Matrix.one_mul]
    simp
  · have e : γ h * sixP1 u.succ * (γ h)ᵀ = I • ((γ h * γ u * γ h) * J) := by
      rw [sixP1_succ, Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      rw [Matrix.mul_assoc, Matrix.mul_assoc, J_mul_γ_transpose]
      simp only [Matrix.mul_assoc]
    rw [e, sixP1_succ]
    by_cases hu : u = h
    · subst hu
      rw [γ_mul_self, Matrix.one_mul]
      simp
    · rw [γ_conj_line_ne (Ne.symm hu)]
      have : ¬(u.succ = 0 ∨ u.succ = h.succ) := by
        simp [Fin.succ_ne_zero, hu]
      rw [ite_eq_right this, Matrix.neg_mul, smul_neg, neg_smul, one_smul]

/-- **A plane held on the six:** `(γ_hγ_k) f_c (γ_hγ_k)ᵀ = −f_c` exactly on `f_h` and `f_k`. -/
theorem plane_on_six (h k : Fin 5) (hk : h ≠ k) (c : Fin 6) :
    (γ h * γ k) * sixP1 c * (γ h * γ k)ᵀ =
      (if c = h.succ ∨ c = k.succ then -1 else 1 : ℂ) • sixP1 c := by
  rw [Matrix.transpose_mul, show γ h * γ k * sixP1 c * ((γ k)ᵀ * (γ h)ᵀ) =
    γ h * (γ k * sixP1 c * (γ k)ᵀ) * (γ h)ᵀ by simp only [Matrix.mul_assoc],
    line_on_six, Matrix.mul_smul, Matrix.smul_mul, line_on_six, smul_smul]
  congr 1
  rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨u, rfl⟩
  · simp [(Fin.succ_ne_zero h).symm, (Fin.succ_ne_zero k).symm]
  · simp only [Fin.succ_ne_zero, false_or, Fin.succ_inj]
    by_cases h1 : u = h
    · subst h1
      simp [Ne.symm hk, hk]
    · by_cases h2 : u = k
      · subst h2
        simp [h1]
      · simp [h1, h2]

/-- The number of lines a division divides with the singlet undivided: the lines of `D` if the singlet is
not in `D`, the lines outside `D` if it is (Definition 13: calling the other part divided). -/
def linesDivided (D : Finset (Fin 6)) : ℕ :=
  if (0 : Fin 6) ∈ D then 5 - (D.erase 0).card else D.card

/-- **The six held by a line, one of each:** `{}`, `{h, n}`, `{h, k}`, `{n}`, `{h}`, `{n, h, k}`
divide `0, 4, 2, 5, 1, 3` lines with the singlet undivided. -/
theorem one_of_each : ∀ h k : Fin 5, h ≠ k →
    [linesDivided ∅, linesDivided {0, h.succ}, linesDivided {h.succ, k.succ}, linesDivided {0},
      linesDivided {h.succ}, linesDivided {0, h.succ, k.succ}] = [0, 4, 2, 5, 1, 3] := by
  decide

/-- **The commutant of the relabellings:** a matrix that every relabelling of the five directions leaves
unchanged is `a·1 + b·𝟙𝟙ᵀ`. -/
theorem commutant_perm {R : Type*} [CommRing R] (X : Matrix (Fin 5) (Fin 5) R)
    (hX : ∀ σ : Equiv.Perm (Fin 5), X.submatrix σ σ = X) :
    ∃ a b : R, X = a • (1 : Matrix (Fin 5) (Fin 5) R) + b • Matrix.of fun _ _ => 1 := by
  have hdiag : ∀ i, X i i = X 0 0 := by
    intro i
    have := congrFun (congrFun (hX (Equiv.swap 0 i)) i) i
    simp only [Matrix.submatrix_apply, Equiv.swap_apply_right] at this
    exact this.symm
  have hoff : ∀ i j, i ≠ j → X i j = X 0 1 := by
    intro i j hij
    -- a relabelling sending i to 0 and j to 1
    obtain ⟨σ, h1, h2⟩ : ∃ σ : Equiv.Perm (Fin 5), σ i = 0 ∧ σ j = 1 := by
      let σ₁ := Equiv.swap i 0
      have hj : σ₁ j ≠ 0 := by
        intro h
        apply hij
        have := congrArg σ₁ h
        simp only [σ₁, Equiv.swap_apply_self] at this
        rw [Equiv.swap_apply_right] at this
        exact this.symm
      refine ⟨(Equiv.swap (σ₁ j) 1) * σ₁, ?_, ?_⟩
      · simp only [Equiv.Perm.mul_apply, σ₁, Equiv.swap_apply_left]
        rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hj) (by decide)]
      · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    have := congrFun (congrFun (hX σ⁻¹) 0) 1
    simp only [Matrix.submatrix_apply] at this
    have hi : σ⁻¹ 0 = i := by rw [← h1]; simp
    have hj : σ⁻¹ 1 = j := by rw [← h2]; simp
    rw [hi, hj] at this
    exact this
  refine ⟨X 0 0 - X 0 1, X 0 1, ?_⟩
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h
    rw [hdiag]
    simp
  · rw [hoff i j h]
    simp [h]

end Comparison

end
