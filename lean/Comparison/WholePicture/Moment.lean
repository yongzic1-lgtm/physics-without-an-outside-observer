module

public import Mathlib

/-!
# The whole picture, statement 12: the mixed moment for every central weight

On the fifteen two-spinor states other than the singlet (the ten symmetric
states, two lines, and the five vector states, four lines), a source on a set `D` of `r` lines is
`S_D = (5P_D − r)/4`; its clock on the two-spinor state `S` is `H_D(S) = (5|S ∩ D| − r|S|)/4`
(`clock4 = 4H`). A central weight `W` weighs the symmetric states by `w₂` and the vector states by `w₄`. With
`μ = Σ W|S|/Σ W`, the mixed moment `𝒥_DE = Σ W (|S| − μ) H_D H_E/Σ W` and the clock
`𝒞_W = (9/8) Var_W |S|`:

* `plane_clock_sum`, `line_clock_sum`: **the grade-resolved sums** `Σ_planes H_DH_E = 3 Tr(S_DS_E)`
  and `Σ_lines H_DH_E = Tr(S_DS_E)`, `16 Tr(S_DS_E) = 25|D ∩ E| − 5rs`, for all `D, E` (kernel
  check).
* `mixed_moment_central`: **`𝒥_DE = 𝒞_W (rs − 5 Tr P_DP_E)/72` for every central weight** with
  `10w₂ + 5w₄ ≠ 0`, `Tr P_DP_E = |D ∩ E|`.
* `clock_uniform`: at the uniform weight the clock is `1`; `crossing_pair_quarter`: with the weights
  `1/k₂(¼) = 1`, `1/k₄(¼) = 1/2` one pair of directions on opposite sides is `1/100` against the clock `18/25`, the same
  `1/72`.

For general symmetric projectors `P_D`, `P_E` and the uniform weight the same formula is
`ArticleStatements/MixedMoment.lean`'s `mixed_moment_subspaces`.
-/

@[expose] public section

namespace Comparison.WholePicture

/-- The ten symmetric states: the sets of two of the five directions. -/
def planesOf : Finset (Finset (Fin 5)) := Finset.univ.filter fun S => S.card = 2

/-- The five vector states: the sets of four of the five directions. -/
def lineRelsOf : Finset (Finset (Fin 5)) := Finset.univ.filter fun S => S.card = 4

/-- The fifteen two-spinor states other than the singlet. -/
def fifteen : Finset (Finset (Fin 5)) := Finset.univ.filter fun S => S.card = 2 ∨ S.card = 4

/-- Four times the clock of the source `S_D = (5P_D − r)/4` on the two-spinor state `S`. -/
def clock4 (D S : Finset (Fin 5)) : ℤ := 5 * (S ∩ D).card - D.card * S.card

/-- **On the symmetric states:** `Σ (4H_D)(4H_E) = 3(25|D ∩ E| − 5rs)`. -/
theorem plane_clock_sum : ∀ D E : Finset (Fin 5),
    ∑ S ∈ planesOf, clock4 D S * clock4 E S = 3 * (25 * (D ∩ E).card - 5 * D.card * E.card) := by
  decide +kernel

/-- **On the vector states:** `Σ (4H_D)(4H_E) = 25|D ∩ E| − 5rs`. -/
theorem line_clock_sum : ∀ D E : Finset (Fin 5),
    ∑ S ∈ lineRelsOf, clock4 D S * clock4 E S = 25 * (D ∩ E).card - 5 * D.card * E.card := by
  decide +kernel

theorem card_planesOf : planesOf.card = 10 := by decide

theorem card_lineRelsOf : lineRelsOf.card = 5 := by decide

theorem fifteen_eq : fifteen = planesOf ∪ lineRelsOf := by
  ext S
  simp [fifteen, planesOf, lineRelsOf]

theorem planes_lines_disjoint : Disjoint planesOf lineRelsOf := by
  rw [planesOf, lineRelsOf, Finset.disjoint_filter]
  intro S _ h
  omega

theorem sum_fifteen (f : Finset (Fin 5) → ℝ) :
    ∑ S ∈ fifteen, f S = ∑ S ∈ planesOf, f S + ∑ S ∈ lineRelsOf, f S := by
  rw [fifteen_eq, Finset.sum_union planes_lines_disjoint]

/-- **A central weight:** `w₂` on the symmetric states, `w₄` on the vector states. -/
def cw (w2 w4 : ℝ) (S : Finset (Fin 5)) : ℝ := if S.card = 2 then w2 else w4

theorem sum_planes_cw (w2 w4 : ℝ) (g : ℝ → ℝ → Finset (Fin 5) → ℝ) :
    ∑ S ∈ planesOf, g (cw w2 w4 S) (S.card : ℝ) S = ∑ S ∈ planesOf, g w2 2 S := by
  refine Finset.sum_congr rfl fun S hS => ?_
  have h : S.card = 2 := (Finset.mem_filter.mp hS).2
  simp [cw, h]

theorem sum_lines_cw (w2 w4 : ℝ) (g : ℝ → ℝ → Finset (Fin 5) → ℝ) :
    ∑ S ∈ lineRelsOf, g (cw w2 w4 S) (S.card : ℝ) S = ∑ S ∈ lineRelsOf, g w4 4 S := by
  refine Finset.sum_congr rfl fun S hS => ?_
  have h : S.card = 4 := (Finset.mem_filter.mp hS).2
  simp [cw, h]

/-- The total weight `Z = Σ W`. -/
noncomputable def Zc (w2 w4 : ℝ) : ℝ := ∑ S ∈ fifteen, cw w2 w4 S

/-- The mean grade `μ = Σ W|S|/Z`. -/
noncomputable def meanGrade (w2 w4 : ℝ) : ℝ := (∑ S ∈ fifteen, cw w2 w4 S * S.card) / Zc w2 w4

/-- **The mixed moment** `𝒥_DE = Σ W (|S| − μ) H_D H_E / Z`. -/
noncomputable def mixedJ (D E : Finset (Fin 5)) (w2 w4 : ℝ) : ℝ :=
  (∑ S ∈ fifteen, cw w2 w4 S * ((S.card : ℝ) - meanGrade w2 w4) *
    ((clock4 D S : ℝ) / 4) * ((clock4 E S : ℝ) / 4)) / Zc w2 w4

/-- **The clock** `𝒞_W = (9/8) Var_W |S|`. -/
noncomputable def clockW (w2 w4 : ℝ) : ℝ :=
  9 / 8 * ((∑ S ∈ fifteen, cw w2 w4 S * ((S.card : ℝ) - meanGrade w2 w4) ^ 2) / Zc w2 w4)

theorem Zc_eq (w2 w4 : ℝ) : Zc w2 w4 = 10 * w2 + 5 * w4 := by
  rw [Zc, sum_fifteen]
  rw [sum_planes_cw w2 w4 (fun c _ _ => c), sum_lines_cw w2 w4 (fun c _ _ => c)]
  simp [card_planesOf, card_lineRelsOf]

theorem meanGrade_eq (w2 w4 : ℝ) :
    meanGrade w2 w4 = (20 * w2 + 20 * w4) / (10 * w2 + 5 * w4) := by
  rw [meanGrade, Zc_eq, sum_fifteen]
  rw [sum_planes_cw w2 w4 (fun c n _ => c * n), sum_lines_cw w2 w4 (fun c n _ => c * n)]
  simp [card_planesOf, card_lineRelsOf]
  ring

theorem cast_plane_sum (D E : Finset (Fin 5)) :
    ∑ S ∈ planesOf, (clock4 D S : ℝ) * (clock4 E S : ℝ) =
      3 * (25 * (D ∩ E).card - 5 * D.card * E.card) := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (plane_clock_sum D E)
  push_cast at h
  exact h

theorem cast_line_sum (D E : Finset (Fin 5)) :
    ∑ S ∈ lineRelsOf, (clock4 D S : ℝ) * (clock4 E S : ℝ) =
      25 * (D ∩ E).card - 5 * D.card * E.card := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (line_clock_sum D E)
  push_cast at h
  exact h

/-- **The mixed moment for every central weight:**
`𝒥_DE = 𝒞_W (rs − 5 Tr P_DP_E)/72` with `r = |D|`, `s = |E|`, `Tr P_DP_E = |D ∩ E|`. -/
theorem mixed_moment_central (D E : Finset (Fin 5)) (w2 w4 : ℝ) (hZ : 10 * w2 + 5 * w4 ≠ 0) :
    mixedJ D E w2 w4 =
      clockW w2 w4 * ((D.card : ℝ) * E.card - 5 * (D ∩ E).card) / 72 := by
  have hJ : mixedJ D E w2 w4 =
      (w2 * (2 - meanGrade w2 w4) / 16 * (3 * (25 * (D ∩ E).card - 5 * D.card * E.card)) +
        w4 * (4 - meanGrade w2 w4) / 16 * (25 * (D ∩ E).card - 5 * D.card * E.card)) /
        (10 * w2 + 5 * w4) := by
    rw [mixedJ, Zc_eq, sum_fifteen]
    rw [sum_planes_cw w2 w4 (fun c n S => c * (n - meanGrade w2 w4) *
        ((clock4 D S : ℝ) / 4) * ((clock4 E S : ℝ) / 4)),
      sum_lines_cw w2 w4 (fun c n S => c * (n - meanGrade w2 w4) *
        ((clock4 D S : ℝ) / 4) * ((clock4 E S : ℝ) / 4))]
    rw [← cast_plane_sum, ← cast_line_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1
    congr 1 <;> refine Finset.sum_congr rfl fun S _ => ?_ <;> ring
  have hC : clockW w2 w4 =
      9 / 8 * ((10 * w2 * (2 - meanGrade w2 w4) ^ 2 + 5 * w4 * (4 - meanGrade w2 w4) ^ 2) /
        (10 * w2 + 5 * w4)) := by
    rw [clockW, Zc_eq, sum_fifteen]
    rw [sum_planes_cw w2 w4 (fun c n _ => c * (n - meanGrade w2 w4) ^ 2),
      sum_lines_cw w2 w4 (fun c n _ => c * (n - meanGrade w2 w4) ^ 2)]
    simp [card_planesOf, card_lineRelsOf]
    ring
  rw [hJ, hC, meanGrade_eq]
  have hZ' : w2 * 10 + w4 * 5 ≠ 0 := by
    intro h
    apply hZ
    linarith
  field_simp
  ring

/-- **At the uniform weight the clock is one** (`Var |S| = 8/9`). -/
theorem clock_uniform : clockW 1 1 = 1 := by
  rw [clockW, Zc_eq, sum_fifteen]
  rw [sum_planes_cw 1 1 (fun c n _ => c * (n - meanGrade 1 1) ^ 2),
    sum_lines_cw 1 1 (fun c n _ => c * (n - meanGrade 1 1) ^ 2), meanGrade_eq]
  simp [card_planesOf, card_lineRelsOf]
  norm_num

/-- **One pair of directions on opposite sides:** `1/72` against the clock `1` at `u = 0`, and `1/100` against `18/25` with
the weights `1/k₂(¼) = 1`, `1/k₄(¼) = 1/2` at `u = ¼`: the ratio `1/72` stays. -/
theorem crossing_pair_quarter :
    mixedJ {0} {1} 1 1 = 1 / 72 ∧ clockW 1 (1 / 2) = 18 / 25 ∧
      mixedJ {0} {1} 1 (1 / 2) = 1 / 100 := by
  have hc : clockW 1 (1 / 2) = 18 / 25 := by
    rw [clockW, Zc_eq, sum_fifteen]
    rw [sum_planes_cw 1 (1 / 2) (fun c n _ => c * (n - meanGrade 1 (1 / 2)) ^ 2),
      sum_lines_cw 1 (1 / 2) (fun c n _ => c * (n - meanGrade 1 (1 / 2)) ^ 2), meanGrade_eq]
    simp [card_planesOf, card_lineRelsOf]
    norm_num
  refine ⟨?_, hc, ?_⟩
  · rw [mixed_moment_central _ _ _ _ (by norm_num), clock_uniform]
    simp
  · rw [mixed_moment_central _ _ _ _ (by norm_num), hc]
    simp
    norm_num

end Comparison.WholePicture

end
