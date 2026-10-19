import Mathlib

/-!
# The eight traceless rotations of three lines (formula (59))

`su3`: the antihermitian traceless `3 × 3` complex matrices, a real subspace of the rotations of the three
lines outside the plane; `finrank_su3`: **its real dimension is eight**, the components `k_C² − 1` of the
colour term (row L14, `rowL14_digits`).
-/

namespace Comparison.Formulas

open Matrix Complex

/-- The traceless rotations of three lines. -/
def su3 : Submodule ℝ (Matrix (Fin 3) (Fin 3) ℂ) where
  carrier := {X | Xᴴ = -X ∧ X.trace = 0}
  add_mem' := by
    rintro X Y ⟨hX1, hX2⟩ ⟨hY1, hY2⟩
    exact ⟨by rw [conjTranspose_add, hX1, hY1, neg_add], by rw [trace_add, hX2, hY2, add_zero]⟩
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' := by
    rintro c X ⟨hX1, hX2⟩
    refine ⟨?_, ?_⟩
    · rw [conjTranspose_smul, hX1, smul_neg]
      simp
    · rw [trace_smul, hX2, smul_zero]

/-- The eight real coordinates as a matrix of `su(3)`. -/
noncomputable def su3Of (c : Fin 8 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(c 0 : ℂ) * I, (c 2 : ℂ) + (c 3 : ℂ) * I, (c 4 : ℂ) + (c 5 : ℂ) * I;
     -(c 2 : ℂ) + (c 3 : ℂ) * I, (c 1 : ℂ) * I, (c 6 : ℂ) + (c 7 : ℂ) * I;
     -(c 4 : ℂ) + (c 5 : ℂ) * I, -(c 6 : ℂ) + (c 7 : ℂ) * I, -((c 0 : ℂ) + (c 1 : ℂ)) * I]

/-- The coordinates, as a real-linear map. -/
noncomputable def su3Lin : (Fin 8 → ℝ) →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℂ where
  toFun := su3Of
  map_add' c d := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [su3Of] <;> ring
  map_smul' a c := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [su3Of, Complex.real_smul] <;> ring

theorem su3Lin_apply (c : Fin 8 → ℝ) : su3Lin c = su3Of c := rfl

theorem su3Lin_injective : Function.Injective su3Lin := by
  intro c d h
  rw [su3Lin_apply, su3Lin_apply] at h
  have e : ∀ i j : Fin 3, su3Of c i j = su3Of d i j := fun i j => by rw [h]
  have h00 := congrArg Complex.im (e 0 0)
  have h11 := congrArg Complex.im (e 1 1)
  have h01r := congrArg Complex.re (e 0 1)
  have h01i := congrArg Complex.im (e 0 1)
  have h02r := congrArg Complex.re (e 0 2)
  have h02i := congrArg Complex.im (e 0 2)
  have h12r := congrArg Complex.re (e 1 2)
  have h12i := congrArg Complex.im (e 1 2)
  simp [su3Of] at h00 h11 h01r h01i h02r h02i h12r h12i
  funext k
  fin_cases k
  · exact h00
  · exact h11
  · exact h01r
  · exact h01i
  · exact h02r
  · exact h02i
  · exact h12r
  · exact h12i

theorem su3Of_mem (c : Fin 8 → ℝ) : su3Of c ∈ su3 := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [su3Of, conjTranspose_apply] <;> ring
  · simp [su3Of, Matrix.trace, Fin.sum_univ_three]
    ring

theorem mem_su3_eq (X : Matrix (Fin 3) (Fin 3) ℂ) (hX : X ∈ su3) :
    su3Of ![(X 0 0).im, (X 1 1).im, (X 0 1).re, (X 0 1).im, (X 0 2).re, (X 0 2).im, (X 1 2).re,
      (X 1 2).im] = X := by
  obtain ⟨h1, h2⟩ := hX
  have hs : ∀ i j, star (X j i) = -X i j := fun i j => by
    have := congrFun (congrFun h1 i) j
    simpa [conjTranspose_apply] using this
  have hre : ∀ i j, (X j i).re = -(X i j).re := fun i j => by
    have := congrArg Complex.re (hs i j)
    simpa using this
  have him : ∀ i j, (X j i).im = (X i j).im := fun i j => by
    have := congrArg Complex.im (hs i j)
    simp at this
    linarith
  have hd : ∀ i, (X i i).re = 0 := fun i => by
    have := hre i i
    linarith
  have htr : X 0 0 + X 1 1 + X 2 2 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_three] using h2
  have htr_re := congrArg Complex.re htr
  have htr_im := congrArg Complex.im htr
  simp at htr_re htr_im
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [su3Of]
  all_goals first
    | linarith [hd 0, hd 1, hd 2, hre 0 1, hre 0 2, hre 1 2, him 0 1, him 0 2, him 1 2]
    | (rw [hd 0]) | (rw [hd 1])

theorem range_su3Lin : LinearMap.range su3Lin = su3 := by
  ext X
  constructor
  · rintro ⟨c, rfl⟩
    exact su3Of_mem c
  · intro hX
    exact ⟨_, mem_su3_eq X hX⟩

/-- **The traceless rotations of three lines are eight.** -/
theorem finrank_su3 : Module.finrank ℝ su3 = 8 := by
  rw [← range_su3Lin, LinearMap.finrank_range_of_inj su3Lin_injective, Module.finrank_fin_fun]

end Comparison.Formulas
