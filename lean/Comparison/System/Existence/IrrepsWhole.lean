import Comparison.System.Existence.Irreps

/-!
# The proof system, the existence layer: Proposition 48 whole

The singlet, the symmetric and the vector states of the comparison (`Matter.lean`: `prop_48_irreps`), their projectors
spanning the operators the ten keep (`Irreps.lean`: `ten_commutant`), `Π₀ + Π_F + Π_L = 1`, and the cumulative projectors
`Q₁ = 0`, `Q₂ = Π_F`, `Q₃ = Π_F + Π_L`: `Q_n` is one on the two-spinor states that disagree on `0 < N ≤ 2(n − 1)` lines and
zero on the others (`cumQ_rel`).
-/

namespace Comparison.System.Existence

open Matrix Complex

/-- The cumulative projectors of the comparison: `Q₁ = 0`, `Q₂ = Π_F`, `Q₃ = Π_F + Π_L`. -/
noncomputable def cumQ (n : ℕ) : Matrix Two Two ℂ :=
  (if 2 ≤ n then (1 : ℂ) else 0) • ((1 / 2 : ℂ) • (1 + swap)) +
    (if 3 ≤ n then (1 : ℂ) else 0) • ((1 / 2 : ℂ) • (1 - swap) - (1 / 4 : ℂ) • Eop)

theorem cumQ_values : cumQ 1 = 0 ∧ cumQ 2 = (1 / 2 : ℂ) • (1 + swap) ∧
    cumQ 3 = (1 / 2 : ℂ) • (1 + swap) + ((1 / 2 : ℂ) • (1 - swap) - (1 / 4 : ℂ) • Eop) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [cumQ]

/-- **`Π₀ + Π_F + Π_L = 1`.** -/
theorem irreps_sum :
    (1 / 4 : ℂ) • Eop + (1 / 2 : ℂ) • (1 + swap) + ((1 / 2 : ℂ) • (1 - swap) - (1 / 4 : ℂ) • Eop) =
      (1 : Matrix Two Two ℂ) := by
  module

/-- **The cumulative projectors:** `Q_n` is one on the two-spinor states that disagree on `0 < N ≤ 2(n − 1)` lines and zero on
the others. -/
theorem cumQ_rel (n : ℕ) (k : Fin 16) :
    cumQ n *ᵥ rel k =
      (if 0 < (disagreeSet k).card ∧ (disagreeSet k).card + 2 ≤ 2 * n then 1 else 0 : ℂ) • rel k := by
  obtain ⟨-, pF, pL⟩ := irrep_projectors k
  rw [cumQ, Matrix.add_mulVec,
    Matrix.smul_mulVec (if 2 ≤ n then (1 : ℂ) else 0) ((1 / 2 : ℂ) • (1 + swap)),
    Matrix.smul_mulVec (if 3 ≤ n then (1 : ℂ) else 0) ((1 / 2 : ℂ) • (1 - swap) - (1 / 4 : ℂ) • Eop), pF, pL,
    smul_smul, smul_smul, ← add_smul]
  congr 1
  have e2 : (2 ≤ n) ↔ (0 < 2 ∧ 2 + 2 ≤ 2 * n) := by omega
  have e3 : (3 ≤ n) ↔ (0 < 4 ∧ 4 + 2 ≤ 2 * n) := by omega
  rcases irreps.1 k with h | h | h <;> rw [h]
  · simp
  · by_cases hn : 2 ≤ n
    · rw [if_pos hn, if_pos (e2.mp hn)]
      norm_num
    · rw [if_neg hn, if_neg (fun h' => hn (e2.mpr h'))]
      norm_num
  · by_cases hn : 3 ≤ n
    · rw [if_pos hn, if_pos (e3.mp hn)]
      norm_num
    · rw [if_neg hn, if_neg (fun h' => hn (e3.mpr h'))]
      norm_num

/-! ## Proposition 48 -/

/-- **Proposition 48 (singlet, symmetric and vector states).** A two-spinor state disagrees on `N = 0`, `2` or `4` lines, `1 + 10 + 5` two-spinor states,
and none on six (an even set of five lines has at most four); the comparison is `L = 6 − 2N = 6, 2, −2` on them;
`Π₀ = E/4`, `Π_F = (1 + P)/2`, `Π_L = (1 − P)/2 − E/4` are one on the singlet, the symmetric states and the vector states
respectively and zero on the others, `Π₀ + Π_F + Π_L = 1`, and they span the operators the ten keep: an operator on
two systems commutes with the ten rotations `γ_aγ_b ⊗ 1 + 1 ⊗ γ_aγ_b` exactly when it is `c₀Π₀ + c₁Π_F + c₂Π_L`;
cumulatively `Q₁ = 0`, `Q₂ = Π_F`, `Q₃ = Π_F + Π_L`, `Q_n` one on the two-spinor states with `0 < N ≤ 2(n − 1)`.

Recognition: three families and no fourth, the electron at no distinction, the muon reaching the symmetric states, the tau
reaching the vector states. Uses Props. 10, 11, 13. -/
theorem prop_48 :
    ((∀ k : Fin 16, (disagreeSet k).card = 0 ∨ (disagreeSet k).card = 2 ∨ (disagreeSet k).card = 4) ∧
    (Finset.univ.filter fun k : Fin 16 => (disagreeSet k).card = 0).card = 1 ∧
    (Finset.univ.filter fun k : Fin 16 => (disagreeSet k).card = 2).card = 10 ∧
    (Finset.univ.filter fun k : Fin 16 => (disagreeSet k).card = 4).card = 5 ∧
    (∀ k : Fin 16, (disagreeSet k).card ≠ 6) ∧
    (∀ k : Fin 16, L *ᵥ rel k = ((Lvalue k : ℤ) : ℂ) • rel k ∧ Lvalue k = 6 - 2 * (disagreeSet k).card) ∧
    (∀ k : Fin 16,
      ((1 / 4 : ℂ) • Eop) *ᵥ rel k = (if (disagreeSet k).card = 0 then 1 else 0 : ℂ) • rel k ∧
      ((1 / 2 : ℂ) • (1 + swap)) *ᵥ rel k = (if (disagreeSet k).card = 2 then 1 else 0 : ℂ) • rel k ∧
      ((1 / 2 : ℂ) • (1 - swap) - (1 / 4 : ℂ) • Eop) *ᵥ rel k =
        (if (disagreeSet k).card = 4 then 1 else 0 : ℂ) • rel k)) ∧
    (1 / 4 : ℂ) • Eop + (1 / 2 : ℂ) • (1 + swap) + ((1 / 2 : ℂ) • (1 - swap) - (1 / 4 : ℂ) • Eop) =
      (1 : Matrix Two Two ℂ) ∧
    (∀ X : Matrix Two Two ℂ, (∀ f : Fin 10, X * tenAct f = tenAct f * X) ↔
      ∃ c₀ c₁ c₂ : ℂ, X = c₀ • ((1 / 4 : ℂ) • Eop) + c₁ • ((1 / 2 : ℂ) • (1 + swap)) +
        c₂ • ((1 / 2 : ℂ) • (1 - swap) - (1 / 4 : ℂ) • Eop)) ∧
    (cumQ 1 = 0 ∧ cumQ 2 = (1 / 2 : ℂ) • (1 + swap) ∧
      cumQ 3 = (1 / 2 : ℂ) • (1 + swap) + ((1 / 2 : ℂ) • (1 - swap) - (1 / 4 : ℂ) • Eop)) ∧
    (∀ (n : ℕ) (k : Fin 16), cumQ n *ᵥ rel k =
      (if 0 < (disagreeSet k).card ∧ (disagreeSet k).card + 2 ≤ 2 * n then 1 else 0 : ℂ) • rel k) :=
  ⟨prop_48_irreps, irreps_sum, prop_48_kept, cumQ_values, cumQ_rel⟩

end Comparison.System.Existence
