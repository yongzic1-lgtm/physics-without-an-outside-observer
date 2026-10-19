import Comparison.System.Existence.Matter

/-!
# The proof system, the existence layer: Proposition 99 whole

The singlet, the symmetric and the vector states `Π₀ = E/4`, `Π_F = (1 + P)/2`, `Π_L = (1 − P)/2 − E/4`
are `(1/4) Σ_i (B₃)_{ij} X_i` in the basis `X = (1, −P, −E)` (`irreps_from_pairings`): `B₃` is the change of basis
between two bases of one space, so `B₃ᵀG_ΘB₃ = diag(1, 10, 5)` is the Gram matrix of the three projectors.
-/

namespace Comparison.System.Existence

open Matrix Complex

/-- **The three projectors in the basis `1, −P, −E`:** `Π_j = (1/4) Σ_i (B₃)_{ij} X_i`. -/
theorem irreps_from_pairings : ∀ j : Fin 3,
    ![(1 / 4 : ℂ) • Comparison.Eop, (1 / 2 : ℂ) • (1 + Comparison.swap),
      (1 / 2 : ℂ) • (1 - Comparison.swap) - (1 / 4 : ℂ) • Comparison.Eop] j =
      (1 / 4 : ℂ) • ∑ i, Article.B3 i j • Article.XTheta i := by
  obtain ⟨e0, e1, e2⟩ := Article.pairing_irreps
  intro j
  fin_cases j
  · exact e0.symm
  · exact e1.symm
  · exact e2.symm

/-- **Proposition 99 (the three pairings of the four lines beside the last-step direction).** For every last-step direction `h`: the four lines
beside it pair in exactly three ways; for every plane `{h, k}` and the three lines `c` outside it, with
`K_c = γ_kγ_c` on the last-step direction's side `Q(h)H` (`Q(h) = (1 + γ_h)/2`): `K_c² = −1`, `K_cK_d = −K_dK_c`, each `K_c` keeps
the side (it commutes with `γ_h`), and every operator of the side is `½ tr(X) Q − ½ Σ_c tr(K_cX) K_cQ`, a
combination of `Q` and the three `K_cQ`; for each pairing `{a, b | c, d}` of the four lines,
`(γ_aγ_b)(γ_cγ_d) = ±γ_h`, so on the side `γ_aγ_b = ∓γ_cγ_d`; the pairing vectors, `+1` on the pair of `k` and `−1`
on the other, are orthogonal on the four lines (`Σ_x χ_cχ_{c'} = 4δ`) and sum to `3` at `k` and `−1` at each
outside line, `(3, −1, −1, −1)`; `G_Θ = (5I − 𝖩₃)/4` on `X = (1, −P, −E)`; the singlet, the symmetric and the vector states `Π₀ = E/4`,
`Π_F = (1 + P)/2`, `Π_L = (1 − P)/2 − E/4` are `(1/4) Σ_i (B₃)_{ij} X_i`, so `B₃` changes one basis of the space
into the other and `B₃ᵀG_ΘB₃ = diag(1, 10, 5)` is the Gram matrix of the three projectors; `3(1 + 10 + 5) = 48`.

Recognition: the three families, each one of the three ways the four lines beside the last-step direction split into two symmetric states; on
the last-step direction's doublet the same three are the three rotations of spin. Uses Props. 4, 5, 13, 48. -/
theorem prop_99_full :
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
    (∀ j : Fin 3,
      ![(1 / 4 : ℂ) • Comparison.Eop, (1 / 2 : ℂ) • (1 + Comparison.swap),
        (1 / 2 : ℂ) • (1 - Comparison.swap) - (1 / 4 : ℂ) • Comparison.Eop] j =
        (1 / 4 : ℂ) • ∑ i, Article.B3 i j • Article.XTheta i) ∧
    Article.B3ᵀ * Article.gramTheta * Article.B3 = Matrix.diagonal ![1, 10, 5] ∧ (3 : ℕ) * (1 + 10 + 5) = 48 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := prop_99
  exact ⟨p1, p2, p3, p4, p5, p6, p7, irreps_from_pairings, p8, p9⟩

end Comparison.System.Existence
