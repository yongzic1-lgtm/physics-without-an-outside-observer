import Comparison.Existence.IharaBass

/-!
# The critical germ and the resistance `b`
# (Propositions 114 and 109)

At the critical step `u = 1/4` the law's operator `(1 + 4u²) − uA` is
`(5 − A)/4`, the Laplacian of the sixteen vertices (`A` the Clebsch graph of the transitions, `adjacencyZ`). Its Green function and the resistances of the network of vertices:

* `green_identity`: with `128 G = 4(7 + A) − 3𝐉`, **`(5 − A) G = 1 − 𝐉/16` and `G𝐉 = 0`**: `G` is
  `(5 − A)⁺ = (7 + A)/32 − 3𝐉/128`, the inverse on the functions of mean zero (Proposition 114);
* `green_symm`: `G` is symmetric;
* `laplacian_spectrum`, `det_prime`: `5 − A` is `0, 4, 8` on the characters (`1, 10, 5` times), and
  the product of its nonzero eigenvalues is `4¹⁰8⁵ = 2³⁵`;
* `resistance_values`, `resistance_real`: **the resistance of the network of vertices from here to a
  plane is `R = G_xx + G_yy − 2G_xy = 7/16 = b`, and to a vector state `3/8`**, and
  `(7/16 − 3/8)/(7/16 + 3/8) = 1/13 = |Φ(i)|` (Proposition 109). This is the reading by which
  Proposition 205 lets each aligned last-step direction carry `b` from its own singlet to the bound state's plane: the
  Δ's factor `k_C b = 21/16` is three such resistances.
-/

open Comparison Matrix

namespace Comparison.RuleAndLaw

/-- The matrix of ones on the sixteen vertices. -/
def J16 : Matrix (Fin 16) (Fin 16) ℤ := Matrix.of fun _ _ => 1

/-- `128 G = 4(7 + A) − 3𝐉`. -/
def green128 : Matrix (Fin 16) (Fin 16) ℤ :=
  (4 : ℤ) • ((7 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) + adjacencyZ) - (3 : ℤ) • J16

/-- **The Green function of the critical germ:** `(5 − A)·128G = 128 − 8𝐉` and `128G·𝐉 = 0`. -/
theorem green_identity :
    ((5 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) - adjacencyZ) * green128 =
        (128 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) - (8 : ℤ) • J16 ∧
      green128 * J16 = 0 := by
  decide +kernel

theorem green_symm : green128ᵀ = green128 := by
  decide +kernel

/-- **The Laplacian of the sixteen vertices on the characters:** `5 − A` is `5 − (L_l − 1)`. -/
theorem laplacian_spectrum :
    ((5 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) - adjacencyZ) * charTable =
      charTable * Matrix.diagonal (fun l => 5 - charValue l) := by
  decide +kernel

/-- **`det′(5 − A) = 4¹⁰8⁵ = 2³⁵`**, with the eigenvalues `0` once, `4` ten times, `8` five times. -/
theorem det_prime :
    (∏ l ∈ Finset.univ.filter (fun l : Fin 16 => l ≠ 0), (5 - charValue l)) = 2 ^ 35 ∧
      (5 - charValue 0) = 0 ∧
      (Finset.univ.filter (fun l : Fin 16 => 5 - charValue l = 4)).card = 10 ∧
      (Finset.univ.filter (fun l : Fin 16 => 5 - charValue l = 8)).card = 5 := by
  decide +kernel

/-- `128 R(x, y) = 128(G_xx + G_yy − 2G_xy)`. -/
def res128 (x y : Fin 16) : ℤ := green128 x x + green128 y y - 2 * green128 x y

/-- **`128 R(here, plane) = 56`, `128 R(here, line) = 48`**, for every plane and every vector state. -/
theorem resistance_values :
    disagreeSet 0 = ∅ ∧
      (∀ f : Fin 16, (disagreeSet f).card = 2 → res128 0 f = 56) ∧
      (∀ l : Fin 16, (disagreeSet l).card = 4 → res128 0 l = 48) := by
  decide +kernel

/-- **`b = R(here, plane) = 7/16`, `R(here, line) = 3/8`, and their contrast is `1/13`.** -/
theorem resistance_real :
    (56 : ℝ) / 128 = 7 / 16 ∧ (48 : ℝ) / 128 = 3 / 8 ∧
      ((7 : ℝ) / 16 - 3 / 8) / (7 / 16 + 3 / 8) = 1 / 13 ∧ (3 : ℝ) * (7 / 16) = 21 / 16 := by
  norm_num

end Comparison.RuleAndLaw

#print axioms Comparison.RuleAndLaw.green_identity
#print axioms Comparison.RuleAndLaw.green_symm
#print axioms Comparison.RuleAndLaw.laplacian_spectrum
#print axioms Comparison.RuleAndLaw.det_prime
#print axioms Comparison.RuleAndLaw.resistance_values
#print axioms Comparison.RuleAndLaw.resistance_real
