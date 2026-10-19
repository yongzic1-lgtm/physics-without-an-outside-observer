import Comparison.System.Postulates
import Comparison.WholePicture.Cells
import Comparison.WholePicture.SecondVariation
import Comparison.System.Law.Phases

/-!
# The proof system, the law: Proposition 116, the plane flux closes on the cells

The cells of `RP⁴`, the symmetric states of the five-cube with the
whole flip (`WholePicture/Cells.lean`, `Existence/PlaquetteData.lean`): sixteen vertices, forty links, forty
squares, twenty cubes, five four-cells. Here the boundaries are given their orientations over `ℤ`:

* `gradZ'` (links × vertices, head less tail), `cMat` (squares × links, the circulation `C`), `cubeBdZ`
  (cubes × squares, the six squares of a cube with their signs), `fourBdZ` (four-cells × cubes, the eight
  cubes of a four-cell with their signs);
* `bd_bd_int`: **`C·grad = 0`, `D·C = 0`, `E·D = 0` over `ℤ`**: the boundary of a boundary is nothing, with
  orientations; `gradZ'_mod_two`, `cMat_mod_two`, `cubeBdZ_mod_two`, `fourBdZ_mod_two`: mod 2 they are the
  unoriented boundaries `bd1`, ..., `bd4`;
* `step_on_cube`: a step changes one line and then flips them all, `T_{transition t k} = (T_k △ {t}) △ [5]`;
* `prop_116`: Proposition 116 as one statement.
-/

open Matrix Comparison Comparison.WholePicture

namespace Comparison.System

namespace Law

/-- **The oriented boundary of a link:** `+1` at its head, `−1` at its tail (links × vertices). -/
def gradZ' : Matrix (Fin 40) (Fin 16) ℤ :=
  Matrix.of fun l x => (if linkV l = x then 1 else 0) - (if linkU l = x then 1 else 0)

/-- **The oriented boundary of a cube:** its six squares with their signs (cubes × squares). -/
def cubeBdZ : Matrix (Fin 20) (Fin 40) ℤ :=
  !![1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, -1, 1, 0, -1, 0, 0;
    1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, -1, 0;
    1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, -1;
    0, 1, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 1, 0, -1, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, -1;
    0, 0, 0, 0, 1, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, -1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, 0, 0, 0, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- **The oriented boundary of a four-cell:** its eight cubes with their signs (four-cells × cubes). -/
def fourBdZ : Matrix (Fin 5) (Fin 20) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, -1, -1, 1, 1, -1, -1;
    0, 0, 0, 0, 0, 0, 1, 1, -1, -1, 1, 1, 0, 0, 0, 0, 0, 0, -1, 1;
    0, 0, 1, 1, -1, -1, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, -1, 1, 0, 0;
    1, 1, 0, 0, -1, 1, 0, 0, 1, -1, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0;
    1, -1, -1, 1, 0, 0, 1, -1, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0]


/-- **The boundary of a boundary is nothing, with orientations, over `ℤ`:** `C·grad = 0`, `D·C = 0`,
`E·D = 0`. -/
theorem bd_bd_int : cMat * gradZ' = 0 ∧ cubeBdZ * cMat = 0 ∧ fourBdZ * cubeBdZ = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · ext q x
    simp only [Matrix.mul_apply, cMat, gradZ', Matrix.of_apply, Matrix.zero_apply]
    exact cZ_div q x
  · decide +kernel
  · decide +kernel

/-- Mod 2 the oriented boundaries are the unoriented ones. -/
theorem gradZ'_mod_two : gradZ'.map (Int.castRingHom (ZMod 2)) = bd1ᵀ := by
  decide +kernel

theorem cMat_mod_two : cMat.map (Int.castRingHom (ZMod 2)) = bd2ᵀ := by
  decide +kernel

theorem cubeBdZ_mod_two : cubeBdZ.map (Int.castRingHom (ZMod 2)) = bd3ᵀ := by
  decide +kernel

theorem fourBdZ_mod_two : fourBdZ.map (Int.castRingHom (ZMod 2)) = bd4ᵀ := by
  decide +kernel

/-- Moving along every line of `T` (the transitions commute). -/
def transitionSet (T : Finset (Fin 5)) (x : Fin 16) : Fin 16 :=
  (if (4 : Fin 5) ∈ T then transition 4 else id) ((if (3 : Fin 5) ∈ T then transition 3 else id)
    ((if (2 : Fin 5) ∈ T then transition 2 else id) ((if (1 : Fin 5) ∈ T then transition 1 else id)
      ((if (0 : Fin 5) ∈ T then transition 0 else id) x))))

/-- The vertices of the four-dimensional plane through `x` along the four lines other than `j`. -/
def fourOf (x : Fin 16) (j : Fin 5) : Finset (Fin 16) :=
  ((Finset.univ : Finset (Finset (Fin 5))).filter fun T => j ∉ T).image fun T => transitionSet T x

/-- **The four-cell left out by `j` covers every vertex:** from any vertex the four lines other than `j` reach all
sixteen (a four-plane of the five-cube and its flip are one cell). -/
theorem four_cells_places : ∀ (x : Fin 16) (j : Fin 5), fourOf x j = Finset.univ := by
  decide +kernel

/-- **The cubes of the four-cell `j` are those whose three lines avoid `j`:** eight of them, and every cube lies on
two four-cells. -/
theorem four_cells_cubes :
    (∀ (j : Fin 5) (c : Fin 20), fourBdZ j c ≠ 0 ↔ cubeLines c ⊆ Finset.univ.erase j) ∧
    (∀ j : Fin 5, (Finset.univ.filter fun c : Fin 20 => fourBdZ j c ≠ 0).card = 8) ∧
    (∀ c : Fin 20, (Finset.univ.filter fun j : Fin 5 => fourBdZ j c ≠ 0).card = 2) := by
  have h : ∀ (j : Fin 5) (c : Fin 20),
      decide (fourBdZ j c ≠ 0) = decide (cubeLines c ⊆ Finset.univ.erase j) := by
    decide +kernel
  refine ⟨fun j c => decide_eq_decide.mp (h j c), ?_, ?_⟩ <;> decide +kernel

/-- **A step changes one line and then flips them all:** `T_{transition t k} = (T_k △ {t}) △ [5]`. -/
theorem step_on_cube : ∀ (t : Fin 5) (k : Fin 16),
    disagreeSet (transition t k) = symmDiff (symmDiff (disagreeSet k) {t}) Finset.univ := by
  decide

end Law

open Comparison.System.Law

/-- **Proposition 116, the plane flux closes on the cells.** The cells of `RP⁴` (a step changes one line and
then flips them all): sixteen vertices, forty links, forty squares, twenty cubes, five four-cells, every link,
square and cube of the five-cube with the flip listed once, and the five four-cells the four-symmetric states left out by one
line `j` (each reaches all sixteen vertices; its boundary is the eight cubes whose three lines avoid `j`, and every
cube lies on two four-cells); the boundary of a boundary is nothing, with
orientations over `ℤ` (`C·grad = 0`, `D·C = 0`, `E·D = 0`) and mod 2; the Euler number is `1`; mod 2 there
is one class in each dimension (`dim H_k(RP⁴; ℤ/2) = 1`, `k = 0, …, 4`); `rank C = 25` and
`spec CᵀC = 0¹⁵ ⊕ 4¹⁰ ⊕ 8¹⁵`; the second variation of `log det(I − wA₋[θ])` is `−κ(w)CᵀC`,
`κ(w) = 2w⁴/(1 − 5w²)²` (the Hessian matrix entry by entry, and the second derivative of `det(I − wA₋[e^{itθ}])`
at `t = 0` along every direction `θ`, `Law/Phases.lean`), which is `1/200` at `w = ±1/5` and `1/98` at
`w = ±i/3`. -/
theorem prop_116 :
    (∀ (t : Fin 5) (k : Fin 16),
      disagreeSet (transition t k) = symmDiff (symmDiff (disagreeSet k) {t}) Finset.univ) ∧
    (∀ x y : Fin 16, x < y → sadjF x y ≠ 0 → ∃ l : Fin 40, linkU l = x ∧ linkV l = y) ∧
    (∀ l m : Fin 40, linkU l = linkU m → linkV l = linkV m → l = m) ∧
    (∀ (x : Fin 16) (s t : Fin 5), s ≠ t →
      ∃ q : Fin 40, square x s t = square (sqX q) (sqS q) (sqT q)) ∧
    (∀ q q' : Fin 40, square (sqX q) (sqS q) (sqT q) = square (sqX q') (sqS q') (sqT q') → q = q') ∧
    (∀ (x : Fin 16) (a b d : Fin 5), a < b → b < d →
      ∃ c : Fin 20, cubeSet c = cubeOf x a b d ∧ cubeA c = a ∧ cubeB c = b ∧ cubeD c = d) ∧
    (∀ c c' : Fin 20, cubeSet c = cubeSet c' → cubeA c = cubeA c' → cubeB c = cubeB c' →
      cubeD c = cubeD c' → c = c') ∧
    (∀ (x : Fin 16) (j : Fin 5), Law.fourOf x j = Finset.univ) ∧
    (∀ (j : Fin 5) (c : Fin 20), fourBdZ j c ≠ 0 ↔ cubeLines c ⊆ Finset.univ.erase j) ∧
    (∀ j : Fin 5, (Finset.univ.filter fun c : Fin 20 => fourBdZ j c ≠ 0).card = 8) ∧
    (∀ c : Fin 20, (Finset.univ.filter fun j : Fin 5 => fourBdZ j c ≠ 0).card = 2) ∧
    (cMat * gradZ' = 0 ∧ cubeBdZ * cMat = 0 ∧ fourBdZ * cubeBdZ = 0) ∧
    (bd1 * bd2 = 0 ∧ bd2 * bd3 = 0 ∧ bd3 * bd4 = 0) ∧
    (Module.finrank (ZMod 2) (LinearMap.ker (0 : Matrix (Fin 0) (Fin 16) (ZMod 2)).mulVecLin ⧸
      (LinearMap.range bd1.mulVecLin).comap
        (LinearMap.ker (0 : Matrix (Fin 0) (Fin 16) (ZMod 2)).mulVecLin).subtype) = 1 ∧
    Module.finrank (ZMod 2) (LinearMap.ker bd1.mulVecLin ⧸
      (LinearMap.range bd2.mulVecLin).comap (LinearMap.ker bd1.mulVecLin).subtype) = 1 ∧
    Module.finrank (ZMod 2) (LinearMap.ker bd2.mulVecLin ⧸
      (LinearMap.range bd3.mulVecLin).comap (LinearMap.ker bd2.mulVecLin).subtype) = 1 ∧
    Module.finrank (ZMod 2) (LinearMap.ker bd3.mulVecLin ⧸
      (LinearMap.range bd4.mulVecLin).comap (LinearMap.ker bd3.mulVecLin).subtype) = 1 ∧
    Module.finrank (ZMod 2) (LinearMap.ker bd4.mulVecLin ⧸
      (LinearMap.range (0 : Matrix (Fin 5) (Fin 0) (ZMod 2)).mulVecLin).comap
        (LinearMap.ker bd4.mulVecLin).subtype) = 1) ∧
    ((Fintype.card (Fin 16) : ℤ) - Fintype.card (Fin 40) + Fintype.card (Fin 40) -
      Fintype.card (Fin 20) + Fintype.card (Fin 5) = 1) ∧
    cReal.rank = 25 ∧
    (cRealᵀ * cReal).charpoly =
      Polynomial.X ^ 15 * (Polynomial.X - Polynomial.C (4 : ℝ)) ^ 10 *
        (Polynomial.X - Polynomial.C (8 : ℝ)) ^ 15 ∧
    (∀ (w : ℂ), 1 - 5 * w ^ 2 ≠ 0 → ∀ j k : Fin 40,
      hessLaw w j k = -(2 * w ^ 4 / (1 - 5 * w ^ 2) ^ 2) * (GZ j k : ℂ)) ∧
    (∀ (w : ℂ), 1 - 5 * w ^ 2 ≠ 0 → ∀ θ : Fin 40 → ℝ,
      HasDerivAt (fun s => (Kph w θ s).det) 0 0 ∧
      HasDerivAt (deriv (fun s => (Kph w θ s).det))
        (-(2 * w ^ 4 / (1 - 5 * w ^ 2) ^ 2) * (plaqSq θ : ℂ) * (Kph w θ 0).det) 0) ∧
    (2 * (1 / 5 : ℂ) ^ 4 / (1 - 5 * (1 / 5) ^ 2) ^ 2 = 1 / 200 ∧
      2 * (-1 / 5 : ℂ) ^ 4 / (1 - 5 * (-1 / 5) ^ 2) ^ 2 = 1 / 200 ∧
      2 * (Complex.I / 3) ^ 4 / (1 - 5 * (Complex.I / 3) ^ 2) ^ 2 = 1 / 98 ∧
      2 * (-Complex.I / 3) ^ 4 / (1 - 5 * (-Complex.I / 3) ^ 2) ^ 2 = 1 / 98) := by
  refine ⟨step_on_cube, links_complete, links_distinct, squares_complete, squares_distinct,
    cubes_complete, cubes_distinct, four_cells_places, four_cells_cubes.1, four_cells_cubes.2.1,
    four_cells_cubes.2.2, bd_bd_int, bd_bd, homology_mod_two, by simp, rank_cReal,
    cReal_gram_charpoly, fun w hw j k => hessLaw_eq w hw j k, fun w hw θ => ?_, ?_⟩
  · obtain ⟨-, -, -, -, h5, h6, -⟩ := law_small_phases w hw θ
    exact ⟨h5, h6⟩
  · obtain ⟨-, -, -, -, h1, h2, h3, h4⟩ := kappa_quarters
    exact ⟨h1, h2, h3, h4⟩

end Comparison.System
